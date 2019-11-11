#!/bin/sh
echo "creating $2.pdf"
mkdir -p tmp
pdflatex -interaction=batchmode -output-directory=tmp $1.tex > /dev/null
pdflatex -interaction=batchmode -output-directory=tmp $1.tex > /dev/null
mkdir -p pdfs
mv tmp/$1.pdf pdfs/$2.pdf

