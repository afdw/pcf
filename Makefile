ROCQ ?= "$(ROCQBIN)rocq"

RocqMakefile:
	rocq makefile -f _CoqProject -o RocqMakefile

invoke-rocqmakefile: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile $(filter-out RocqMakefile,$(MAKECMDGOALS))

build: invoke-rocqmakefile

clean: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile cleanall
	rm RocqMakefile
	rm RocqMakefile.conf

.PHONY: invoke-rocqmakefile build clean
.DEFAULT_GOAL := build

%: invoke-rocqmakefile
