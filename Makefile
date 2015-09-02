.PHONY: all agda idris
all: agda idris

.PHONY: clean agda-clean idris-clean
clean: agda-clean idris-clean


agda := $(shell find src -name '*.agda')
agdai := $(patsubst %.agda,%.agdai,$(agda))

agda: $(agdai)

%.agdai: %.agda
	agda --safe -i src $<

agda-clean:
	rm -f $(agdai)


idr := $(shell find src -name '*.idr')
ibc := $(patsubst %.idr,%.ibc,$(idr))

idris: $(ibc)

%.ibc: %.idr
	idris --check --noprelude --total -i src $<

idris-clean:
	rm -f $(ibc)
