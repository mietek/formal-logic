.PHONY: all agda haskell idris
all: agda haskell idris

.PHONY: clean agda-clean haskell-clean idris-clean
clean: agda-clean haskell-clean idris-clean


agda  := $(shell find src -type f -name '*.agda')
agdai := $(patsubst %.agda,%.agdai,$(agda))

agda: $(agdai)

%.agdai: %.agda
	agda --safe -i src $<

agda-clean:
	rm -f $(agdai)


idr := $(shell find src -type f -name '*.idr')
ibc := $(patsubst %.idr,%.ibc,$(idr))

idris: $(ibc)

%.ibc: %.idr
	idris --check -i src $<

idris-clean:
	rm -f $(ibc)


hs := $(shell find src -type f -name '*.hs')
hi := $(patsubst %.hs,%.hi,$(hs))
o  := $(patsubst %.hs,%.o,$(hs))

haskell: $(hi) $(o)

%.hi %.o: %.hs
	ghc --make -Wall -isrc $<

haskell-clean:
	rm -f $(hi) $(o)
