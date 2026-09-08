.PHONY: setup sync build check clean distclean

## setup — fetch Mathlib, pin the toolchain it wants, pull its prebuilt oleans
setup:
	lake update
	$(MAKE) sync
	lake exe cache get
	@echo "==> ready. run 'make build'"

## sync — copy Mathlib's exact toolchain into ./lean-toolchain
## Mathlib only builds against one Lean version; this makes that version
## explicit and committable instead of leaving it as 'stable'.
sync:
	@if [ -f .lake/packages/mathlib/lean-toolchain ]; then \
		cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain; \
		echo "==> pinned toolchain: $$(cat lean-toolchain)"; \
	else \
		echo "!! Mathlib not fetched yet; run 'lake update' first"; exit 1; \
	fi

## build — elaborate every file; this is what "the proofs check" means
build:
	lake build

check: build

clean:
	lake clean

distclean:
	rm -rf .lake lake-manifest.json
