#!/bin/sh
echo "creating $2.pdf"
mkdir -p tmp
pdflatex -interaction=batchmode -output-directory=tmp "\PassOptionsToClass{handout}{beamer}\def\ttbwflag{}\input{$1.tex}" > /dev/null
pdflatex -interaction=batchmode -output-directory=tmp "\PassOptionsToClass{handout}{beamer}\def\ttbwflag{}\input{$1.tex}" > /dev/null
cd tmp
pdfjam --landscape --a4paper --nup 2x2 --scale 0.9 $1.pdf -o $1-4.pdf -q 
cd ..
mkdir -p pdfs
mv tmp/$1-4.pdf pdfs/$2.pdf
