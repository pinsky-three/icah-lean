LAKE := $(HOME)/.elan/bin/lake
LEAN := $(HOME)/.elan/bin/lean

.PHONY: build check sorry-count axiom-count clean cache

## Download Mathlib cache (run once after cloning)
cache:
	$(LAKE) exe cache get

## Build the full project
build:
	$(LAKE) build

## Type-check the umbrella file (faster than a full build when oleans are fresh)
check:
	$(LAKE) env $(LEAN) ICAH.lean

## Count lines containing `sorry` in proof position (excludes comments)
sorry-count:
	@echo "=== sorry count ==="
	@grep -rn "^\s*sorry\s*$$" ICAH/ --include="*.lean" | wc -l

## Count named axioms introduced by the project (excludes Lean kernel axioms)
axiom-count:
	@echo "=== project axiom count ==="
	@grep -rn "^axiom " ICAH/ --include="*.lean" | wc -l
	@echo "=== axiom names ==="
	@grep -rn "^axiom " ICAH/ --include="*.lean" | sed 's/.*axiom //' | sed 's/ .*//'

## Remove build artifacts
clean:
	$(LAKE) clean
