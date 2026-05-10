OUT_DIR := build
MAIN := main.typ
PDF := $(OUT_DIR)/icah-paper.pdf

.PHONY: build watch clean

build:
	mkdir -p $(OUT_DIR)
	typst compile $(MAIN) $(PDF)

watch:
	mkdir -p $(OUT_DIR)
	typst watch $(MAIN) $(PDF)

clean:
	rm -rf $(OUT_DIR)
