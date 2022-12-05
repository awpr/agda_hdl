#! /bin/bash

sed -i '/mArKeR/q' index.agda
echo >> index.agda
git ls-files | sed -e '/index\.agda/d' -e '/\.agda$/!d' -e 's/.agda$//' -e 's:/:.:g' -e 's/^/import /' >> index.agda

git diff index.agda
