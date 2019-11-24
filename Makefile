default: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: stlc.v
	coq_makefile -f _CoqProject -o Makefile.coq

stlc.v: stlc.ott
	ott -o stlc.v -coq_expand_list_types false stlc.ott

stlcScript.sml: stlc.ott
	ott -o stlcScript.sml stlc.ott

hol: stlcMetaScript.sml stlcScript.sml ottScript.sml ottLib.sig ottLib.sml
	Holmake

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf stlc.v stlcScript.sml

.PHONY: default clean
