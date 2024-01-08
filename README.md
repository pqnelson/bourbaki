This is a literate program describing Bourbaki's formal language as they
laid it out in the English translation _Theory of Sets_.

It's probably not wise to use it as a foundations for mathematics, or as
the engine for a proof assistant, because...well, it's horribly bloated
as a foundations. Famously, the number 1 requires something like 273,385
symbols (if the ordered pair is a primitive --- otherwise, it requires
about 20 times as many symbols). 

# How to Compile

Assuming you have cabal installed locally, be sure to have cabal install
lhs2tex:

```
~/bourbaki/$ cabal install lhs2tex
```

Then you can run `make code` to extract the Haskell code, `make` to
have pdflatex compile the literate commentary.
