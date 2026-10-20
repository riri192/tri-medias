import os
import sys
import shutil
import subprocess
import hashlib
import re
import tempfile
from pathlib import Path
from datetime import datetime

from PySide6.QtCore import Qt, QSize, QUrl, QEvent, QDateTime
from PySide6.QtGui import QPixmap, QShortcut, QKeySequence
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QLabel, QPushButton,
    QFileDialog, QMessageBox, QVBoxLayout, QHBoxLayout, QGridLayout,
    QSlider, QScrollArea, QSplitter, QStackedWidget, QDateTimeEdit, QComboBox
)
from PySide6.QtMultimedia import QMediaPlayer, QAudioOutput
from PySide6.QtMultimediaWidgets import QVideoWidget

try:
    import cv2
except Exception:
    cv2 = None

try:
    from PIL import Image
except Exception:
    Image = None

try:
    from send2trash import send2trash
except Exception:
    send2trash = None


EXT_IMAGES = (".jpg", ".jpeg", ".png", ".bmp", ".webp")
EXT_VIDEOS = (".mp4", ".mov", ".avi", ".mkv", ".wmv", ".m4v")
EXT_MEDIAS = EXT_IMAGES + EXT_VIDEOS

MOIS = {
    1: "01_janvier", 2: "02_février", 3: "03_mars", 4: "04_avril",
    5: "05_mai", 6: "06_juin", 7: "07_juillet", 8: "08_août",
    9: "09_septembre", 10: "10_octobre", 11: "11_novembre", 12: "12_décembre"
}


class Vignette(QLabel):
    def __init__(self, chemin, taille, parent):
        super().__init__()
        self.chemin = chemin
        self.parent = parent
        self.taille = taille

        self.setFixedSize(taille, taille)
        self.setAlignment(Qt.AlignCenter)
        self.setStyleSheet("border: 1px solid #999; background-color: #eeeeee;")

        self.charger_image()
        self.installEventFilter(parent)

    def charger_image(self):
        pixmap = self.parent.obtenir_miniature(self.chemin, self.taille)

        if pixmap and not pixmap.isNull():
            self.setPixmap(pixmap)
        else:
            self.setText("🎬" if self.chemin.lower().endswith(EXT_VIDEOS) else "🖼")

    def creer_miniature_video(self, chemin):
        if cv2 is None:
            return None

        try:
            cap = cv2.VideoCapture(chemin)
            success, frame = cap.read()
            cap.release()

            if not success:
                return None

            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            hauteur, largeur, canaux = frame.shape
            bytes_ligne = canaux * largeur

            from PySide6.QtGui import QImage
            image = QImage(frame.data, largeur, hauteur, bytes_ligne, QImage.Format_RGB888)
            return QPixmap.fromImage(image.copy())

        except Exception:
            return None

    def appliquer_selection(self, selectionne):
        est_doublon = self.chemin in getattr(self.parent, "doublons_a_signaler", set())

        if est_doublon:
            self.setStyleSheet("border: 5px solid #d00000; background-color: #ffe6e6;")
        elif selectionne:
            self.setStyleSheet("border: 4px solid #0078d7; background-color: #dceeff;")
        else:
            self.setStyleSheet("border: 1px solid #999; background-color: #eeeeee;")

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.parent.clic_vignette(self.chemin, event.modifiers())

    def mouseDoubleClickEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.parent.ouvrir_depuis_miniature(self.chemin)


class FenetrePrincipale(QMainWindow):
    def __init__(self):
        super().__init__()

        self.setWindowTitle("Tri de médias")
        self.resize(1550, 900)

        self.dossier_source = ""
        self.dossier_destination = ""

        self.fichiers_tous = []
        self.fichiers = []
        self.index = 0
        self.filtre_type = "Tous"
        self.dates_classement_modifiees = {}
        self._bloquer_changement_date = False
        self.doublons_a_signaler = set()
        self.nb_groupes_doublons = 0

        self.mode = "unique"
        self.mode_retour = None

        self.page = 0
        self.selection = set()
        self.ancre_selection = None

        self.zoom = 100
        self.grille_n = 3
        self.nb_par_page = 9

        self.vignettes = {}
        self.vignettes_studio = {}
        self.cache_miniatures = {}
        self.historique_actions = []

        self.creer_interface()
        self.creer_raccourcis()

    def creer_interface(self):
        central = QWidget()
        central.installEventFilter(self)
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)

        barre_haut = QHBoxLayout()

        self.btn_source = QPushButton("📁 Dossier source")
        self.btn_source.clicked.connect(self.choisir_source)

        self.btn_destination = QPushButton("📁 Dossier destination")
        self.btn_destination.clicked.connect(self.choisir_destination)

        self.btn_mode = QPushButton("Mode : vue unique")
        self.btn_mode.clicked.connect(self.basculer_mode)

        self.combo_filtre = QComboBox()
        self.combo_filtre.addItems(["Tous", "Photos", "Vidéos"])
        self.combo_filtre.currentTextChanged.connect(self.changer_filtre)

        barre_haut.addWidget(self.btn_source)
        barre_haut.addWidget(self.btn_destination)
        barre_haut.addWidget(self.btn_mode)
        barre_haut.addWidget(QLabel("Filtre"))
        barre_haut.addWidget(self.combo_filtre)

        layout.addLayout(barre_haut)

        self.splitter = QSplitter(Qt.Horizontal)

        self.zone_studio_scroll = QScrollArea()
        self.zone_studio_scroll.setWidgetResizable(True)
        self.zone_studio_scroll.setFixedWidth(170)
        self.zone_studio_scroll.viewport().installEventFilter(self)

        self.zone_studio_widget = QWidget()
        self.zone_studio_layout = QVBoxLayout(self.zone_studio_widget)
        self.zone_studio_layout.setSpacing(10)
        self.zone_studio_scroll.setWidget(self.zone_studio_widget)
        self.zone_studio_scroll.hide()

        self.stack_unique = QStackedWidget()
        self.stack_unique.installEventFilter(self)

        self.zone_image = QLabel("Aucun média chargé")
        self.zone_image.setAlignment(Qt.AlignCenter)
        self.zone_image.installEventFilter(self)

        self.video_widget = QVideoWidget()
        self.video_widget.installEventFilter(self)

        self.stack_unique.addWidget(self.zone_image)
        self.stack_unique.addWidget(self.video_widget)

        self.player = QMediaPlayer()
        self.audio = QAudioOutput()
        self.player.setAudioOutput(self.audio)
        self.player.setVideoOutput(self.video_widget)
        self.player.positionChanged.connect(self.position_video_changee)
        self.player.durationChanged.connect(self.duree_video_changee)

        self.zone_grille_scroll = QScrollArea()
        self.zone_grille_scroll.setWidgetResizable(True)
        self.zone_grille_scroll.viewport().installEventFilter(self)

        self.zone_grille_widget = QWidget()
        self.zone_grille_layout = QGridLayout(self.zone_grille_widget)
        self.zone_grille_layout.setSpacing(12)
        self.zone_grille_scroll.setWidget(self.zone_grille_widget)
        self.zone_grille_scroll.hide()

        self.panneau_infos = QWidget()
        self.panneau_infos.setMinimumWidth(320)
        self.panneau_infos.setMaximumWidth(380)

        layout_infos = QVBoxLayout(self.panneau_infos)

        self.label_infos = QLabel("Informations")
        self.label_infos.setAlignment(Qt.AlignTop)
        self.label_infos.setWordWrap(True)

        layout_infos.addWidget(self.label_infos)

        layout_infos.addWidget(QLabel("Date utilisée pour le classement :"))

        self.edit_date_classement = QDateTimeEdit()
        self.edit_date_classement.setDisplayFormat("dd/MM/yyyy HH:mm")
        self.edit_date_classement.setCalendarPopup(True)
        self.edit_date_classement.dateTimeChanged.connect(self.date_classement_changee)

        layout_infos.addWidget(self.edit_date_classement)
        layout_infos.addStretch()

        self.splitter.addWidget(self.zone_studio_scroll)
        self.splitter.addWidget(self.stack_unique)
        self.splitter.addWidget(self.zone_grille_scroll)
        self.splitter.addWidget(self.panneau_infos)
        self.splitter.setSizes([0, 1050, 0, 340])

        layout.addWidget(self.splitter, stretch=1)

        barre_outils = QHBoxLayout()
        barre_outils.addStretch()

        self.btn_annuler = QPushButton("↩")
        self.btn_annuler.setFixedWidth(42)
        self.btn_annuler.setToolTip("Annuler la dernière action (Ctrl+Z)")
        self.btn_annuler.clicked.connect(self.annuler_derniere_action)

        self.btn_rotation_gauche = QPushButton("↶")
        self.btn_rotation_gauche.setFixedWidth(42)
        self.btn_rotation_gauche.setToolTip("Rotation gauche (Ctrl+L)")
        self.btn_rotation_gauche.clicked.connect(lambda: self.faire_rotation_selection(-90))

        self.btn_rotation_droite = QPushButton("↷")
        self.btn_rotation_droite.setFixedWidth(42)
        self.btn_rotation_droite.setToolTip("Rotation droite (Ctrl+R)")
        self.btn_rotation_droite.clicked.connect(lambda: self.faire_rotation_selection(90))

        barre_outils.addWidget(self.btn_annuler)
        barre_outils.addWidget(self.btn_rotation_gauche)
        barre_outils.addWidget(self.btn_rotation_droite)

        layout.addLayout(barre_outils)

        barre_zoom = QHBoxLayout()
        barre_zoom.addWidget(QLabel("Zoom"))

        self.slider_zoom = QSlider(Qt.Horizontal)
        self.slider_zoom.setMinimum(25)
        self.slider_zoom.setMaximum(100)
        self.slider_zoom.setValue(100)
        self.slider_zoom.valueChanged.connect(self.changer_zoom)

        barre_zoom.addWidget(self.slider_zoom)
        layout.addLayout(barre_zoom)

        barre_video = QHBoxLayout()

        self.slider_video = QSlider(Qt.Horizontal)
        self.slider_video.setMinimum(0)
        self.slider_video.setMaximum(0)
        self.slider_video.sliderMoved.connect(self.deplacer_video)

        self.label_temps_video = QLabel("00:00 / 00:00")

        barre_video.addWidget(QLabel("Vidéo"))
        barre_video.addWidget(self.slider_video)
        barre_video.addWidget(self.label_temps_video)

        layout.addLayout(barre_video)

        barre_navigation = QHBoxLayout()

        self.btn_precedent = QPushButton("◀ Précédent")
        self.btn_precedent.clicked.connect(self.precedent)

        self.btn_suivant = QPushButton("Suivant ▶")
        self.btn_suivant.clicked.connect(self.suivant)

        self.btn_page_precedente = QPushButton("◀ Page précédente")
        self.btn_page_precedente.clicked.connect(self.page_precedente)

        self.btn_page_suivante = QPushButton("Page suivante ▶")
        self.btn_page_suivante.clicked.connect(self.page_suivante)

        self.btn_lecture = QPushButton("▶ Lecture / Pause")
        self.btn_lecture.clicked.connect(self.lecture_pause)

        self.btn_supprimer = QPushButton("🗑 Supprimer définitivement")
        self.btn_supprimer.clicked.connect(self.supprimer_selection)

        self.btn_corbeille = QPushButton("♻ Corbeille")
        self.btn_corbeille.clicked.connect(self.envoyer_corbeille)

        self.btn_ouvrir_dossier = QPushButton("📂 Ouvrir le dossier")
        self.btn_ouvrir_dossier.clicked.connect(self.ouvrir_dossier_fichier)

        self.btn_doublons = QPushButton("🔍 Doublons")
        self.btn_doublons.clicked.connect(self.scanner_doublons)

        self.btn_classer = QPushButton("📦 Classer")
        self.btn_classer.clicked.connect(self.classer_selection)

        self.btn_classer_manuel = QPushButton("📂 Classer manuellement")
        self.btn_classer_manuel.clicked.connect(self.classer_manuellement)

        barre_navigation.addWidget(self.btn_precedent)
        barre_navigation.addWidget(self.btn_suivant)
        barre_navigation.addWidget(self.btn_page_precedente)
        barre_navigation.addWidget(self.btn_page_suivante)
        barre_navigation.addWidget(self.btn_lecture)
        barre_navigation.addWidget(self.btn_supprimer)
        barre_navigation.addWidget(self.btn_corbeille)
        barre_navigation.addWidget(self.btn_ouvrir_dossier)
        barre_navigation.addWidget(self.btn_doublons)
        barre_navigation.addWidget(self.btn_classer)
        barre_navigation.addWidget(self.btn_classer_manuel)

        layout.addLayout(barre_navigation)

        self.actualiser_boutons_mode()

    def creer_raccourcis(self):
        QShortcut(QKeySequence("G"), self, self.basculer_mode)
        QShortcut(QKeySequence("C"), self, self.classer_selection)
        QShortcut(QKeySequence("D"), self, self.scanner_doublons)
        QShortcut(QKeySequence("Ctrl+Z"), self, self.annuler_derniere_action)
        QShortcut(QKeySequence("Ctrl+L"), self, lambda: self.faire_rotation_selection(-90))
        QShortcut(QKeySequence("Ctrl+R"), self, lambda: self.faire_rotation_selection(90))
        QShortcut(QKeySequence(Qt.Key_Delete), self, self.supprimer_selection)
        QShortcut(QKeySequence(Qt.Key_Space), self, self.lecture_pause)
        QShortcut(QKeySequence(Qt.Key_Escape), self, self.retour_mode_precedent)

        QShortcut(QKeySequence(Qt.Key_Left), self, self.raccourci_gauche)
        QShortcut(QKeySequence(Qt.Key_Right), self, self.raccourci_droite)

    def eventFilter(self, obj, event):
        if event.type() == QEvent.Wheel:
            modifiers = event.modifiers()
            delta = event.angleDelta().y()

            if modifiers & Qt.ControlModifier:
                if delta > 0:
                    self.slider_zoom.setValue(min(100, self.slider_zoom.value() + 5))
                else:
                    self.slider_zoom.setValue(max(25, self.slider_zoom.value() - 5))
                return True

            if self.mode == "studio" and self.zone_studio_scroll.underMouse():
                return False

            if delta > 0:
                self.navigation_molette_arriere()
            else:
                self.navigation_molette_avant()

            return True

        return super().eventFilter(obj, event)

    def navigation_molette_avant(self):
        if self.mode == "grille":
            self.page_suivante()
        else:
            self.suivant()

    def navigation_molette_arriere(self):
        if self.mode == "grille":
            self.page_precedente()
        else:
            self.precedent()

    def raccourci_gauche(self):
        if self.mode == "grille":
            self.page_precedente()
        else:
            self.precedent()

    def raccourci_droite(self):
        if self.mode == "grille":
            self.page_suivante()
        else:
            self.suivant()

    def obtenir_miniature(self, chemin, taille):
        try:
            mtime = os.path.getmtime(chemin)
        except Exception:
            mtime = 0

        cle = (chemin, mtime, taille)

        if cle in self.cache_miniatures:
            return self.cache_miniatures[cle]

        pixmap = None

        if chemin.lower().endswith(EXT_IMAGES):
            pixmap = QPixmap(chemin)

        elif chemin.lower().endswith(EXT_VIDEOS):
            pixmap = self.creer_pixmap_video(chemin)

        if pixmap and not pixmap.isNull():
            pixmap = pixmap.scaled(
                taille - 8,
                taille - 8,
                Qt.KeepAspectRatio,
                Qt.SmoothTransformation
            )
            self.cache_miniatures[cle] = pixmap
            return pixmap

        return None

    def creer_pixmap_video(self, chemin):
        if cv2 is None:
            return None

        try:
            cap = cv2.VideoCapture(chemin)
            success, frame = cap.read()
            cap.release()

            if not success:
                return None

            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            hauteur, largeur, canaux = frame.shape
            bytes_ligne = canaux * largeur

            from PySide6.QtGui import QImage
            image = QImage(frame.data, largeur, hauteur, bytes_ligne, QImage.Format_RGB888)
            return QPixmap.fromImage(image.copy())

        except Exception:
            return None

    def vider_cache_media(self, chemin=None):
        if chemin is None:
            self.cache_miniatures.clear()
            return

        for cle in list(self.cache_miniatures.keys()):
            if cle[0] == chemin:
                del self.cache_miniatures[cle]

    def choisir_source(self):
        dossier = QFileDialog.getExistingDirectory(self, "Choisir le dossier source")
        if not dossier:
            return

        self.dossier_source = dossier
        self.charger_medias()

    def choisir_destination(self):
        dossier = QFileDialog.getExistingDirectory(self, "Choisir le dossier destination")
        if dossier:
            self.dossier_destination = dossier
            self.mettre_a_jour_infos()

    def charger_medias(self):
        self.stop_video()

        self.fichiers_tous = []

        for nom in os.listdir(self.dossier_source):
            chemin = os.path.join(self.dossier_source, nom)

            if os.path.isfile(chemin) and nom.lower().endswith(EXT_MEDIAS):
                self.fichiers_tous.append(chemin)

        self.fichiers_tous.sort()
        self.doublons_a_signaler.clear()
        self.nb_groupes_doublons = 0
        self.appliquer_filtre(reset_position=True)

    def changer_filtre(self, filtre):
        self.filtre_type = filtre
        self.doublons_a_signaler.clear()
        self.nb_groupes_doublons = 0
        self.appliquer_filtre(reset_position=True)

    def appliquer_filtre(self, reset_position=False):
        if self.filtre_type == "Photos":
            self.fichiers = [f for f in self.fichiers_tous if f.lower().endswith(EXT_IMAGES)]
        elif self.filtre_type == "Vidéos":
            self.fichiers = [f for f in self.fichiers_tous if f.lower().endswith(EXT_VIDEOS)]
        else:
            self.fichiers = list(self.fichiers_tous)

        if reset_position:
            self.index = 0
            self.page = 0
            self.selection.clear()
            self.ancre_selection = None
            self.mode_retour = None
        else:
            self.index = min(self.index, max(0, len(self.fichiers) - 1))
            self.page = min(self.page, self.page_max())

        self.afficher_mode_courant()

    def basculer_mode(self):
        self.stop_video()
        self.mode_retour = None

        if self.mode == "unique":
            self.mode = "grille"
        elif self.mode == "grille":
            self.mode = "studio"
        else:
            self.mode = "unique"

        self.afficher_mode_courant()

    def afficher_mode_courant(self):
        if self.mode == "unique":
            self.afficher_mode_unique()
        elif self.mode == "grille":
            self.afficher_mode_grille()
        else:
            self.afficher_mode_studio()

        self.actualiser_boutons_mode()

    def afficher_mode_unique(self):
        self.zone_studio_scroll.hide()
        self.zone_grille_scroll.hide()
        self.stack_unique.show()

        self.splitter.setSizes([0, 1050, 0, 340])
        self.btn_mode.setText("Mode : vue unique")

        self.afficher_media_central()

    def afficher_mode_grille(self):
        self.zone_studio_scroll.hide()
        self.stack_unique.hide()
        self.zone_grille_scroll.show()

        self.splitter.setSizes([0, 0, 1050, 340])
        self.btn_mode.setText("Mode : vue paginée")

        self.afficher_grille()

    def afficher_mode_studio(self):
        self.zone_studio_scroll.show()
        self.zone_grille_scroll.hide()
        self.stack_unique.show()

        self.splitter.setSizes([170, 900, 0, 340])
        self.btn_mode.setText("Mode : studio")

        self.afficher_colonne_studio()
        self.afficher_media_central()

    def retour_mode_precedent(self):
        if not self.mode_retour:
            return

        self.stop_video()
        self.mode = self.mode_retour
        self.mode_retour = None
        self.afficher_mode_courant()

    def actualiser_boutons_mode(self):
        mode_grille = self.mode == "grille"

        self.btn_precedent.setVisible(self.mode != "grille")
        self.btn_suivant.setVisible(self.mode != "grille")

        self.btn_page_precedente.setVisible(mode_grille)
        self.btn_page_suivante.setVisible(mode_grille)

    def changer_zoom(self, valeur):
        self.zoom = valeur

        if valeur >= 90:
            self.grille_n = 3
        elif valeur >= 70:
            self.grille_n = 4
        elif valeur >= 50:
            self.grille_n = 5
        else:
            self.grille_n = 8

        self.nb_par_page = self.grille_n * self.grille_n

        if self.mode == "grille":
            self.page = min(self.page, self.page_max())
            self.afficher_grille()
        elif self.mode == "studio":
            self.afficher_colonne_studio()
            self.afficher_media_central()
        else:
            self.afficher_media_central()

    def afficher_media_central(self):
        self.stop_video()

        if not self.fichiers:
            self.zone_image.clear()
            self.zone_image.setText("Aucun média trouvé")
            self.stack_unique.setCurrentWidget(self.zone_image)
            self.mettre_a_jour_infos()
            return

        chemin = self.fichiers[self.index]

        if chemin.lower().endswith(EXT_IMAGES):
            self.stack_unique.setCurrentWidget(self.zone_image)

            pixmap = QPixmap(chemin)

            if pixmap.isNull():
                self.zone_image.clear()
                self.zone_image.setText("Image impossible à afficher")
                return

            largeur = int(self.stack_unique.width() * self.zoom / 100)
            hauteur = int(self.stack_unique.height() * self.zoom / 100)

            pixmap = pixmap.scaled(
                largeur,
                hauteur,
                Qt.KeepAspectRatio,
                Qt.SmoothTransformation
            )

            self.zone_image.setPixmap(pixmap)

        else:
            self.stack_unique.setCurrentWidget(self.video_widget)
            self.player.setSource(QUrl.fromLocalFile(chemin))
            self.audio.setVolume(0.8)
            self.player.pause()
            self.slider_video.setValue(0)

        self.mettre_a_jour_infos()

        if self.mode == "studio":
            self.actualiser_selection_studio()

    def vider_layout(self, layout):
        while layout.count():
            item = layout.takeAt(0)
            widget = item.widget()

            if widget:
                widget.deleteLater()

    def afficher_colonne_studio(self):
        self.vider_layout(self.zone_studio_layout)
        self.vignettes_studio.clear()

        if not self.fichiers:
            return

        debut = self.index
        fin = min(len(self.fichiers), debut + 5)

        taille = 135

        for chemin in self.fichiers[debut:fin]:
            vignette = Vignette(chemin, taille, self)
            vignette.appliquer_selection(chemin == self.fichiers[self.index])

            self.zone_studio_layout.addWidget(vignette)
            self.vignettes_studio[chemin] = vignette

        self.zone_studio_layout.addStretch()

    def actualiser_selection_studio(self):
        for chemin, vignette in self.vignettes_studio.items():
            vignette.appliquer_selection(chemin == self.fichiers[self.index])

    def vider_grille(self):
        self.vider_layout(self.zone_grille_layout)
        self.vignettes.clear()

    def afficher_grille(self):
        self.stop_video()
        self.vider_grille()

        if not self.fichiers:
            self.mettre_a_jour_infos()
            return

        debut = self.page * self.nb_par_page
        fin = min(debut + self.nb_par_page, len(self.fichiers))
        fichiers_page = self.fichiers[debut:fin]

        largeur_dispo = max(300, self.zone_grille_scroll.width() - 40)
        hauteur_dispo = max(300, self.zone_grille_scroll.height() - 40)

        taille_largeur = int(largeur_dispo / self.grille_n) - 20
        taille_hauteur = int(hauteur_dispo / self.grille_n) - 20

        taille = max(80, min(taille_largeur, taille_hauteur))

        for i, chemin in enumerate(fichiers_page):
            ligne = i // self.grille_n
            colonne = i % self.grille_n

            vignette = Vignette(chemin, taille, self)
            vignette.appliquer_selection(chemin in self.selection)

            self.zone_grille_layout.addWidget(vignette, ligne, colonne)
            self.vignettes[chemin] = vignette

        self.mettre_a_jour_infos()

    def clic_vignette(self, chemin, modifiers):
        if chemin not in self.fichiers:
            return

        index_clique = self.fichiers.index(chemin)

        if self.mode == "studio":
            self.index = index_clique
            self.selection = {chemin}
            self.afficher_colonne_studio()
            self.afficher_media_central()
            return

        if modifiers & Qt.ShiftModifier:
            if self.ancre_selection is None:
                self.ancre_selection = index_clique

            debut = min(self.ancre_selection, index_clique)
            fin = max(self.ancre_selection, index_clique)

            self.selection = set(self.fichiers[debut:fin + 1])

        elif modifiers & Qt.ControlModifier:
            if chemin in self.selection:
                self.selection.remove(chemin)
            else:
                self.selection.add(chemin)

            self.ancre_selection = index_clique

        else:
            self.selection = {chemin}
            self.ancre_selection = index_clique

        self.index = index_clique
        self.actualiser_selection_vignettes()
        self.mettre_a_jour_infos()

    def actualiser_selection_vignettes(self):
        for chemin, vignette in self.vignettes.items():
            vignette.appliquer_selection(chemin in self.selection)

    def ouvrir_depuis_miniature(self, chemin):
        if chemin in self.fichiers:
            self.index = self.fichiers.index(chemin)

        self.mode_retour = self.mode
        self.mode = "unique"
        self.afficher_mode_courant()

    def page_max(self):
        if not self.fichiers:
            return 0

        return (len(self.fichiers) - 1) // self.nb_par_page

    def page_precedente(self):
        if self.page > 0:
            self.page -= 1
            self.afficher_grille()

    def page_suivante(self):
        if self.page < self.page_max():
            self.page += 1
            self.afficher_grille()

    def precedent(self):
        if self.fichiers and self.index > 0:
            self.index -= 1
            self.afficher_media_central()

            if self.mode == "studio":
                self.afficher_colonne_studio()

    def suivant(self):
        if self.fichiers and self.index < len(self.fichiers) - 1:
            self.index += 1
            self.afficher_media_central()

            if self.mode == "studio":
                self.afficher_colonne_studio()

    def lecture_pause(self):
        if not self.fichiers:
            return

        if self.mode == "grille":
            if self.selection:
                chemin = list(self.selection)[-1]
            else:
                chemin = self.fichiers[self.index]

            if chemin in self.fichiers:
                self.index = self.fichiers.index(chemin)

            self.mode_retour = "grille"
            self.mode = "unique"
            self.afficher_mode_courant()

        chemin = self.fichiers[self.index]

        if not chemin.lower().endswith(EXT_VIDEOS):
            return

        if self.player.playbackState() == QMediaPlayer.PlayingState:
            self.player.pause()
        else:
            self.player.play()

    def stop_video(self):
        try:
            self.player.stop()
        except Exception:
            pass

    def format_temps(self, millisecondes):
        secondes = millisecondes // 1000
        minutes = secondes // 60
        secondes = secondes % 60
        return f"{minutes:02d}:{secondes:02d}"

    def duree_video_changee(self, duree):
        self.slider_video.setMaximum(duree)
        self.label_temps_video.setText(f"00:00 / {self.format_temps(duree)}")

    def position_video_changee(self, position):
        if not self.slider_video.isSliderDown():
            self.slider_video.setValue(position)

        duree = self.player.duration()
        self.label_temps_video.setText(
            f"{self.format_temps(position)} / {self.format_temps(duree)}"
        )

    def deplacer_video(self, position):
        self.player.setPosition(position)

    def obtenir_date_modification(self, chemin):
        try:
            return datetime.fromtimestamp(os.path.getmtime(chemin))
        except Exception:
            return datetime.now()

    def obtenir_date_exif(self, chemin):
        if Image is None or not chemin.lower().endswith(EXT_IMAGES):
            return None

        try:
            with Image.open(chemin) as image:
                exif = image.getexif()

                if not exif:
                    return None

                for tag in (36867, 36868, 306):
                    valeur = exif.get(tag)

                    if valeur:
                        try:
                            return datetime.strptime(str(valeur), "%Y:%m:%d %H:%M:%S")
                        except Exception:
                            pass

        except Exception:
            return None

        return None

    def obtenir_date_classement_auto(self, chemin):
        date_exif = self.obtenir_date_exif(chemin)

        if date_exif:
            return date_exif

        return self.obtenir_date_modification(chemin)

    def obtenir_date_classement(self, chemin):
        if chemin in self.dates_classement_modifiees:
            return self.dates_classement_modifiees[chemin]

        return self.obtenir_date_classement_auto(chemin)

    def obtenir_date_media(self, chemin):
        return self.obtenir_date_classement(chemin)

    def date_classement_changee(self, qdatetime):
        if self._bloquer_changement_date or not self.fichiers:
            return

        chemin = self.fichiers[self.index]
        self.dates_classement_modifiees[chemin] = qdatetime.toPython()

        self.mettre_a_jour_infos()

    def mettre_a_jour_infos(self):
        if not self.fichiers:
            self.label_infos.setText(
                f"Source :\n{self.dossier_source or 'Non défini'}\n\n"
                f"Destination :\n{self.dossier_destination or 'Non défini'}"
            )
            self._bloquer_changement_date = True
            self.edit_date_classement.setEnabled(False)
            self._bloquer_changement_date = False
            return

        chemin = self.fichiers[self.index]
        date_exif = self.obtenir_date_exif(chemin)
        date_modif = self.obtenir_date_modification(chemin)
        date_classement = self.obtenir_date_classement(chemin)

        self._bloquer_changement_date = True
        self.edit_date_classement.setEnabled(True)
        self.edit_date_classement.setDateTime(QDateTime.fromSecsSinceEpoch(int(date_classement.timestamp())))
        self._bloquer_changement_date = False

        if self.mode == "grille":
            debut = self.page * self.nb_par_page + 1
            fin = min((self.page + 1) * self.nb_par_page, len(self.fichiers))
            position = f"Page {self.page + 1}/{self.page_max() + 1}\n{debut} à {fin}"
        else:
            position = f"{self.index + 1}/{len(self.fichiers)}"

        date_exif_txt = date_exif.strftime("%d/%m/%Y %H:%M") if date_exif else "Non trouvée"
        date_modif_txt = date_modif.strftime("%d/%m/%Y %H:%M")
        date_classement_txt = date_classement.strftime("%d/%m/%Y %H:%M")

        texte = (
            f"Fichier :\n{os.path.basename(chemin)}\n\n"
            f"Position : {position}\n\n"
            f"Mode : {self.mode}\n"
            f"Filtre : {self.filtre_type}\n"
            f"Grille : {self.grille_n}×{self.grille_n}\n"
            f"Sélection : {len(self.selection)}\n"
            f"Doublons signalés : {len(self.doublons_a_signaler)}\n\n"
            f"Date EXIF réelle :\n{date_exif_txt}\n\n"
            f"Date modification :\n{date_modif_txt}\n\n"
            f"Date classement :\n{date_classement_txt}\n\n"
            f"Source :\n{self.dossier_source or 'Non défini'}\n\n"
            f"Destination :\n{self.dossier_destination or 'Non défini'}\n\n"
            f"Raccourcis :\n"
            f"G : changer de mode\n"
            f"Échap : retour\n"
            f"Ctrl + molette : zoom\n"
            f"Molette : défiler\n"
            f"Espace : vidéo\n"
            f"C : classer\n"
            f"Suppr : supprimer\n"
            f"D : scanner doublons"
        )

        self.label_infos.setText(texte)

    def fichiers_a_traiter(self):
        if self.mode == "grille" and self.selection:
            return list(self.selection)

        if self.mode == "studio" and self.selection:
            return list(self.selection)

        if self.fichiers:
            return [self.fichiers[self.index]]

        return []

    def supprimer_selection(self):
        chemins = self.fichiers_a_traiter()

        if not chemins:
            return

        reponse = QMessageBox.warning(
            self,
            "Suppression",
            f"Supprimer définitivement {len(chemins)} fichier(s) ?",
            QMessageBox.Yes | QMessageBox.No
        )

        if reponse != QMessageBox.Yes:
            return

        self.stop_video()

        for chemin in chemins:
            try:
                os.remove(chemin)
                self.selection.discard(chemin)
                self.doublons_a_signaler.discard(chemin)
            except Exception as e:
                QMessageBox.critical(
                    self,
                    "Erreur",
                    f"Impossible de supprimer :\n{chemin}\n\n{e}"
                )

        self.charger_medias()

    def envoyer_corbeille(self):
        chemins = self.fichiers_a_traiter()

        if not chemins:
            return

        if send2trash is None:
            QMessageBox.warning(
                self,
                "Module manquant",
                "Pour utiliser la corbeille Windows, installe le module avec :\n\npip install send2trash"
            )
            return

        reponse = QMessageBox.question(
            self,
            "Envoyer à la corbeille",
            f"Envoyer {len(chemins)} fichier(s) à la corbeille ?",
            QMessageBox.Yes | QMessageBox.No
        )

        if reponse != QMessageBox.Yes:
            return

        self.stop_video()

        for chemin in chemins:
            try:
                send2trash(chemin)
                self.selection.discard(chemin)
                self.doublons_a_signaler.discard(chemin)
            except Exception as e:
                QMessageBox.critical(
                    self,
                    "Erreur",
                    f"Impossible d'envoyer à la corbeille :\n{chemin}\n\n{e}"
                )

        self.charger_medias()

    def calculer_sha256(self, chemin):
        h = hashlib.sha256()

        with open(chemin, "rb") as fichier:
            for bloc in iter(lambda: fichier.read(1024 * 1024), b""):
                h.update(bloc)

        return h.hexdigest()

    def score_nom_doublon(self, chemin):
        nom = os.path.basename(chemin).lower()
        racine = Path(nom).stem
        score = 0

        indices_copie = [
            "copie", "copy", "duplicate", "duplicat", "doublon",
            "copie de", "copy of"
        ]

        for indice in indices_copie:
            if indice in nom:
                score += 100

        # Les suffixes de copie Windows du type "photo (1).jpg" sont aussi suspects.
        if re.search(r"\(\s*\d+\s*\)$", racine):
            score += 50

        return score

    def choisir_fichiers_a_signaler_dans_groupe(self, groupe):
        if len(groupe) <= 1:
            return []

        groupe_tries = sorted(
            groupe,
            key=lambda chemin: (
                self.score_nom_doublon(chemin),
                os.path.getmtime(chemin) if os.path.exists(chemin) else 0,
                os.path.basename(chemin).lower()
            )
        )

        fichier_a_conserver = groupe_tries[0]
        return [chemin for chemin in groupe if chemin != fichier_a_conserver]

    def scanner_doublons(self):
        if not self.fichiers:
            return

        reponse = QMessageBox.question(
            self,
            "Scanner les doublons",
            (
                f"Scanner les doublons SHA-256 sur le filtre actuel : {self.filtre_type} ?\n\n"
                "Seuls les fichiers exactement identiques seront détectés.\n"
                "Le fichier à supprimer le plus probable sera encadré en rouge."
            ),
            QMessageBox.Yes | QMessageBox.No
        )

        if reponse != QMessageBox.Yes:
            return

        self.stop_video()
        self.doublons_a_signaler.clear()
        self.nb_groupes_doublons = 0

        empreintes = {}
        erreurs = 0

        total = len(self.fichiers)

        for i, chemin in enumerate(self.fichiers, start=1):
            try:
                empreinte = self.calculer_sha256(chemin)
                empreintes.setdefault(empreinte, []).append(chemin)
            except Exception:
                erreurs += 1

            if i % 25 == 0:
                self.statusBar().showMessage(f"Scan doublons : {i}/{total} fichier(s)...")
                QApplication.processEvents()

        groupes = [groupe for groupe in empreintes.values() if len(groupe) > 1]
        self.nb_groupes_doublons = len(groupes)

        for groupe in groupes:
            for chemin in self.choisir_fichiers_a_signaler_dans_groupe(groupe):
                self.doublons_a_signaler.add(chemin)

        self.selection = set(self.doublons_a_signaler)

        self.statusBar().clearMessage()

        if self.mode == "grille":
            self.afficher_grille()
        elif self.mode == "studio":
            self.afficher_colonne_studio()
            self.afficher_media_central()
        else:
            self.afficher_media_central()

        QMessageBox.information(
            self,
            "Scan terminé",
            (
                f"Groupes de doublons trouvés : {self.nb_groupes_doublons}\n"
                f"Fichiers signalés en rouge : {len(self.doublons_a_signaler)}\n"
                f"Erreurs de lecture : {erreurs}\n\n"
                "Le scan a été effectué uniquement sur le filtre actuellement sélectionné."
            )
        )

    def ouvrir_dossier_fichier(self):
        if not self.fichiers:
            return

        chemin = self.fichiers[self.index]

        try:
            if sys.platform.startswith("win"):
                subprocess.Popen(f'explorer /select,"{os.path.normpath(chemin)}"')
            else:
                dossier = os.path.dirname(chemin)
                subprocess.Popen(["xdg-open", dossier])
        except Exception as e:
            QMessageBox.critical(
                self,
                "Erreur",
                f"Impossible d'ouvrir le dossier :\n{e}"
            )

    def classer_selection(self):
        if not self.dossier_destination:
            QMessageBox.warning(
                self,
                "Destination manquante",
                "Choisis d'abord un dossier destination."
            )
            return

        chemins = self.fichiers_a_traiter()

        if not chemins:
            return

        self.stop_video()
        mouvements = []

        for chemin in chemins:
            try:
                date = self.obtenir_date_classement(chemin)

                dossier_final = os.path.join(
                    self.dossier_destination,
                    str(date.year),
                    MOIS[date.month]
                )

                os.makedirs(dossier_final, exist_ok=True)

                destination = os.path.join(dossier_final, os.path.basename(chemin))
                destination = self.chemin_unique(destination)

                source_originale = chemin
                shutil.move(chemin, destination)
                mouvements.append((source_originale, destination))
                self.selection.discard(chemin)
                self.doublons_a_signaler.discard(chemin)

            except Exception as e:
                QMessageBox.critical(
                    self,
                    "Erreur",
                    f"Impossible de classer :\n{chemin}\n\n{e}"
                )

        if mouvements:
            self.historique_actions.append({
                "type": "move",
                "moves": mouvements
            })

        self.charger_medias()

    def classer_manuellement(self):
        chemins = self.fichiers_a_traiter()

        if not chemins:
            return

        dossier_depart = self.dossier_destination if self.dossier_destination else self.dossier_source

        dossier_choisi = QFileDialog.getExistingDirectory(
            self,
            "Choisir le dossier où déplacer les médias sélectionnés",
            dossier_depart
        )

        if not dossier_choisi:
            return

        self.stop_video()
        mouvements = []

        for chemin in chemins:
            try:
                destination = os.path.join(dossier_choisi, os.path.basename(chemin))
                destination = self.chemin_unique(destination)

                source_originale = chemin
                shutil.move(chemin, destination)
                mouvements.append((source_originale, destination))
                self.selection.discard(chemin)
                self.doublons_a_signaler.discard(chemin)

            except Exception as e:
                QMessageBox.critical(
                    self,
                    "Erreur",
                    f"Impossible de déplacer :\n{chemin}\n\n{e}"
                )

        self.charger_medias()

    def faire_rotation_selection(self, angle):
        if Image is None:
            QMessageBox.warning(
                self,
                "Module manquant",
                "Pour faire pivoter les images, installe Pillow avec :\n\npip install pillow"
            )
            return

        chemins = [c for c in self.fichiers_a_traiter() if c.lower().endswith(EXT_IMAGES)]

        if not chemins:
            QMessageBox.information(self, "Rotation", "Aucune image à faire pivoter dans la sélection.")
            return

        self.stop_video()

        rotations = []

        for chemin in chemins:
            try:
                suffixe = Path(chemin).suffix
                sauvegarde = tempfile.NamedTemporaryFile(delete=False, suffix=suffixe)
                sauvegarde.close()
                shutil.copy2(chemin, sauvegarde.name)

                with Image.open(chemin) as image:
                    exif = image.info.get("exif")
                    image = image.rotate(angle, expand=True)

                    options = {}
                    if exif and chemin.lower().endswith((".jpg", ".jpeg")):
                        options["exif"] = exif

                    image.save(chemin, **options)

                rotations.append((chemin, sauvegarde.name))
                self.vider_cache_media(chemin)

            except Exception as e:
                QMessageBox.critical(
                    self,
                    "Erreur",
                    f"Impossible de faire pivoter :\n{chemin}\n\n{e}"
                )

        if rotations:
            self.historique_actions.append({
                "type": "rotation",
                "rotations": rotations
            })

        self.afficher_mode_courant()

    def annuler_derniere_action(self):
        if not self.historique_actions:
            QMessageBox.information(self, "Annuler", "Aucune action à annuler.")
            return

        action = self.historique_actions.pop()
        type_action = action.get("type")

        self.stop_video()

        if type_action == "move":
            erreurs = 0

            for source, destination in reversed(action.get("moves", [])):
                try:
                    if os.path.exists(destination):
                        os.makedirs(os.path.dirname(source), exist_ok=True)
                        shutil.move(destination, self.chemin_unique(source) if os.path.exists(source) else source)
                except Exception:
                    erreurs += 1

            if erreurs:
                QMessageBox.warning(self, "Annuler", f"{erreurs} déplacement(s) n'ont pas pu être annulé(s).")

        elif type_action == "rotation":
            erreurs = 0

            for chemin, sauvegarde in action.get("rotations", []):
                try:
                    if os.path.exists(sauvegarde):
                        shutil.copy2(sauvegarde, chemin)
                        os.remove(sauvegarde)
                        self.vider_cache_media(chemin)
                except Exception:
                    erreurs += 1

            if erreurs:
                QMessageBox.warning(self, "Annuler", f"{erreurs} rotation(s) n'ont pas pu être annulée(s).")

        else:
            QMessageBox.warning(self, "Annuler", "Cette action ne peut pas être annulée.")

        self.charger_medias()

    def chemin_unique(self, chemin):
        if not os.path.exists(chemin):
            return chemin

        base = Path(chemin)
        dossier = base.parent
        nom = base.stem
        ext = base.suffix
        i = 1

        while True:
            nouveau = dossier / f"{nom}_{i}{ext}"

            if not nouveau.exists():
                return str(nouveau)

            i += 1

    def resizeEvent(self, event):
        super().resizeEvent(event)

        if self.mode == "unique":
            self.afficher_media_central()
        elif self.mode == "grille":
            self.afficher_grille()
        else:
            self.afficher_colonne_studio()
            self.afficher_media_central()


app = QApplication(sys.argv)

fenetre = FenetrePrincipale()
fenetre.show()

sys.exit(app.exec())