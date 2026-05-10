# Template selection notes

## Recommended baseline: `unequivocal-ams`

Use this for the first draft because it is AMS-style, single-column, and aimed at mathematicians.

```bash
typst init @preview/unequivocal-ams:0.1.2
```

## Alternatives

### `clean-math-paper`

Good if the document should look cleaner and more modern while keeping math-paper features such as theorem-like environments, keywords, and AMS classifications.

```bash
typst init @preview/clean-math-paper:0.2.6
```

### `theorion`

Use if theorem environment management becomes complex: restated theorems, appendix numbering, theorem lists, multilingual labels, or custom theorem styles.

```typst
#import "@preview/theorion:0.6.0": *
```

## Current choice

The project uses `unequivocal-ams` for the overall paper shell and local minimal theorem blocks in `src/macros.typ` for stability.
