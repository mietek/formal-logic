.PHONY: all agda haskell idris
all: agda haskell idris

.PHONY: clean agda-clean haskell-clean idris-clean
clean: agda-clean haskell-clean idris-clean


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


hs := $(shell find src -name '*.hs')
hi := $(patsubst %.hs,%.hi,$(hs))
o := $(patsubst %.hs,%.o,$(hs))

haskell: $(hi) $(o)

%.hi %.o: %.hs
	ghc -c -Wall $<

haskell-clean:
	rm -f $(hi) $(o)
