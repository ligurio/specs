SHELL := /bin/sh

ALLOY_BIN ?= $(shell command -v alloy6 2>/dev/null)
PYTHON ?= python3

MODELS := ibuf.als
MODELS += lsregion.als
MODELS += matras.als
MODELS += mempool.als
MODELS += obuf.als
MODELS += quota.als
MODELS += quota_lessor.als
MODELS += common.als
MODELS += region.als
MODELS += slab_arena.als
MODELS += slab_cache.als
MODELS += small.als

# quota.als -> quota.json
RECEIPTS = $(MODELS:.als=.json)

.PHONY: check clean FORCE

check: $(RECEIPTS)
	@$(PYTHON) check.py $^
	@echo "ALL OK"

%.json: %.als FORCE
	@tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	"$(ALLOY_BIN)" exec -f -o "$$tmp" -t none "$<" && \
	mv "$$tmp/receipt.json" "$@"

clean:
	rm -f $(RECEIPTS)
	rm -rf $(MODELS:.als=)
	rm -rf __pycache__
