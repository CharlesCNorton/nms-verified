COQMAKEFILE := Makefile.coq

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) cleanall
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all clean
