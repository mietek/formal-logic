.PHONY: all agda idris
all: agda idris

.PHONY: clean agda-clean idris-clean
clean: agda-clean idris-clean


agda := $(wildcard src/*.agda)
agdai := $(patsubst %.agda,%.agdai,$(agda))

agda: $(agdai)

%.agdai: %.agda
	agda --safe -i $(@D) $<

agda-clean:
	rm -f $(agdai)


idr := $(wildcard src/*.idr)
ibc := $(patsubst %.idr,%.ibc,$(idr))

idris: $(ibc)

%.ibc: %.idr
	idris --check --noprelude --total $<

idris-clean:
	rm -f $(ibc)
