OCAML=ocaml
OCAMLC=ocamlc 
OCAMLOPT=ocamlopt 
OCAMLDEP=ocamldep 
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
INCLUDES=
OCAMLFLAGS=$(INCLUDES) -dtypes
OCAMLOPTFLAGS=$(INCLUDES) 

OBJS = misc.cmo

binary: $(OBJS) core run.ml
	$(OCAMLC) -o ../lollimon $(OBJS) main.cmo run.ml

ocaml: $(OBJS) core
	$(OCAML) $(OBJS) main.cmo

core: $(OBJS)
	$(OCAMLC) -pp camlp4r -c main.ml

# Common rules 
.SUFFIXES: .ml .mli .cmo .cmi .cmx 

.ml.cmo: 
	$(OCAMLC) $(OCAMLFLAGS) -c $< 

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $< 

.ml.cmx: 
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $< 

clean:
	rm -f *.cm[iox]

depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

include .depend