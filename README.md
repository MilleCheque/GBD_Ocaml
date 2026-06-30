# GBD_Ocaml
Fonctions OCaml permettant de créer, modifier et étudier des bases de données

## 📌 Description

Ce projet est un outil développé en **OCaml** permettant de créer, manipuler et analyser des bases de données relationnelles.

Il permet notamment de :
- créer des bases de données
- ajouter des lignes
- analyser leur normalisation
- vérifier si une base est en **1NF, 2NF ou 3NF**

## ⚙️ Fonctionnalités

### 🏗️ Gestion des bases de données
- Création de bases de données relationnelles
- Ajout de lignes
- Produit cartésiens entre tables
- Recherche des dépendances fonctionnelles

### 🔧 Manipulation
- Définition des clés primaires et étrangères
- Gestion des dépendances fonctionnelles

### 📊 Analyse de normalisation
- Vérification de la **Première Forme Normale (1NF)**
- Vérification de la **Deuxième Forme Normale (2NF)**
- Vérification de la **Troisième Forme Normale (3NF)**

## 🧠 Objectif du projet

Ce projet a pour objectif de :
- comprendre les concepts de normalisation des bases de données
- implémenter des structures relationnelles en OCaml
- automatiser l’analyse des formes normales

## 🚀 Installation

### Prérequis
- OCaml (version 4.14 ou supérieure recommandée)
- ocamlc

### Compilation
```termial linux
ocamlc daouda.ml -o exec
./exec
