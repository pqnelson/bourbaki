LHS2TEX=~/.local/bin/lhs2TeX
FILE=bourbaki
TEX=pdflatex

all:
	$(LHS2TEX) $(FILE).lhs > $(FILE).tex
	$(TEX) $(FILE).tex
	$(TEX) $(FILE).tex

code:
	$(LHS2TEX) --newcode $(FILE).lhs > $(FILE).hs
