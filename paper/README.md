# Paper workspace

## Working title

**Conservation of Quantitative Information under Change of Representation**

This directory contains the publication-facing layer of the Lean-verified foundational capstone.

## Files

- [`CONSERVATION_OF_QUANTITATIVE_INFORMATION.md`](CONSERVATION_OF_QUANTITATIVE_INFORMATION.md) — theorem-bounded working manuscript in Markdown.
- [`CONSERVATION_OF_QUANTITATIVE_INFORMATION.tex`](CONSERVATION_OF_QUANTITATIVE_INFORMATION.tex) — publication-oriented LaTeX manuscript.
- [`LITERATURE_REVIEW.md`](LITERATURE_REVIEW.md) — scoped literature/novelty review comparing the capstone with automata-based numeration, abstract numeration systems, canonical number systems, odometers, carry propagation, information-lossless finite-state coding, and periodic enumeration approaches.
- [`references.bib`](references.bib) — bibliography used by the LaTeX manuscript.

Primary formal source:

- [`../QuantityRepresentationFoundations/FoundationalCapstone.lean`](../QuantityRepresentationFoundations/FoundationalCapstone.lean)

Detailed theorem-level source note:

- [`../FOUNDATIONAL_CAPSTONE.md`](../FOUNDATIONAL_CAPSTONE.md)

## Logical discipline

The paper distinguishes four layers:

1. Lean-proved cardinal/depth results;
2. explicit operational hypotheses (`UnitTrajectory`, faithful split encoding, autonomous injective local dynamics, first-step nontriviality);
3. intrinsic construction of emergent capacity, cycle coordinates, carry transport, finite expansion, and canonical digits;
4. downstream identifications with `Nat.div`, `Nat.mod`, `Nat.digits`, Carry Geometry, and external literature.

The manuscript does **not** claim that faithfulness alone forces positional notation, nor that the literature search establishes unconditional historical priority.

## LaTeX build

From this directory, a local TeX Live installation can build the paper with:

```bash
latexmk -pdf -file-line-error -halt-on-error -interaction=nonstopmode CONSERVATION_OF_QUANTITATIVE_INFORMATION.tex
```

GitHub Actions also compiles the manuscript on paper-related pull requests via `.github/workflows/paper-latex.yml` and uploads the generated PDF as a workflow artifact.

## Editorial next steps

After the current LaTeX/literature pass is stable, the main remaining editorial tasks are citation chaining for a broader literature review, journal/template selection, tightening of theorem exposition for the target venue, and preparation of a frozen release/archival version linked to the exact Lean commit.
