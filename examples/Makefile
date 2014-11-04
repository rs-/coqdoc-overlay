COQDOCFLAGS?=--no-index --with-header header.html
-include Makefile.coq

Makefile.coq:
	coq_makefile Even.v > $@

doc: Even.html
	perl -i ../alignment.pl $<
	sed -i'.bk' -f ../proofs-toggle.sed $<
	rm $<.bk
