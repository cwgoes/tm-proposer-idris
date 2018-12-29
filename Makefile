PKG=tm-proposer-idris.ipkg
IDRIS=idris --noprelude
MAIN=Main.idr
FILES=Main Types

all: repl

repl:
	cd src && ${IDRIS} ${FILES}

check:
	cd src && ${IDRIS} --check ${MAIN}
	@echo "All OK!"

clean:
	${IDRIS} --clean ${PKG}

.PHONY: all repl check clean
