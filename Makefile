.PHONY: default
default: build

.PHONY: build
build: 
	dune build @install

.PHONY: test
test:
	dune runtest

.PHONY: clean
clean:
	dune clean

.PHONY: doc
doc:
	dune build @doc
