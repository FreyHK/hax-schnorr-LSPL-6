all:
	cd generated-core && \
	coq_makefile -f _CoqProject -o CoqMakefile && \
	make -f CoqMakefile && \
	make -f CoqMakefile install