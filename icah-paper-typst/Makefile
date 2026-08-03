OUT_DIR := build
MAIN := main.typ
PDF := $(OUT_DIR)/icah-paper.pdf
TYPST_VERSION := 0.14.2
SOURCE_DATE_EPOCH ?= 1785715200

.PHONY: build check-version watch clean

check-version:
	@command -v typst >/dev/null || { echo "Typst $(TYPST_VERSION) is required"; exit 1; }
	@actual="$$(typst --version | awk '{print $$2}')"; \
	  test "$$actual" = "$(TYPST_VERSION)" || { \
	    echo "Typst $(TYPST_VERSION) is required; found $$actual"; exit 1; \
	  }

build: check-version
	mkdir -p $(OUT_DIR)
	typst compile --creation-timestamp $(SOURCE_DATE_EPOCH) $(MAIN) $(PDF)

watch: check-version
	mkdir -p $(OUT_DIR)
	typst watch --creation-timestamp $(SOURCE_DATE_EPOCH) $(MAIN) $(PDF)

clean:
	rm -rf $(OUT_DIR)
