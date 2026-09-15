# Paper workspace

## Title

**Conservation of Quantitative Information under Change of Representation**

### Subtitle

**Universal Carry Rigidity of Optimal Lossless Finite Quantity Codes**

This directory contains the publication-facing layer of the Lean-verified universal carry-collapse theorem.

## Files

- [`CONSERVATION_OF_QUANTITATIVE_INFORMATION.md`](CONSERVATION_OF_QUANTITATIVE_INFORMATION.md) — GitHub-renderable theorem-backed manuscript in Markdown.
- [`CONSERVATION_OF_QUANTITATIVE_INFORMATION.tex`](CONSERVATION_OF_QUANTITATIVE_INFORMATION.tex) — publication-oriented LaTeX manuscript compiled by CI.
- [`LITERATURE_REVIEW.md`](LITERATURE_REVIEW.md) — scoped related-work and novelty review updated for the universal rigidity theorem.
- [`references.bib`](references.bib) — bibliography used by the LaTeX manuscript.

Primary formal source:

- [`../QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean`](../QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean)

Supporting universal-rigidity modules:

- [`../QuantityRepresentationFoundations/UniversalLosslessCompression.lean`](../QuantityRepresentationFoundations/UniversalLosslessCompression.lean)
- [`../QuantityRepresentationFoundations/UniversalLosslessCompressionTower.lean`](../QuantityRepresentationFoundations/UniversalLosslessCompressionTower.lean)
- [`../QuantityRepresentationFoundations/UniversalCrossDepthCarryCoherence.lean`](../QuantityRepresentationFoundations/UniversalCrossDepthCarryCoherence.lean)
- [`../QuantityRepresentationFoundations/UniversalProjectiveCarryTower.lean`](../QuantityRepresentationFoundations/UniversalProjectiveCarryTower.lean)

Detailed theorem-level source note:

- [`../FOUNDATIONAL_CAPSTONE.md`](../FOUNDATIONAL_CAPSTONE.md)

## Main theorem

```lean
theorem universal_optimal_lossless_representation_collapses_to_carry
    {b : ℕ}
    (tower : LosslessCompressedTower b)
    (hb : 1 < b) :
    UniversalCarryCollapseCertificate tower (lt_trans Nat.zero_lt_one hb)
```

The paper's main conclusion is representation-invariant rather than syntactic:

> Every arbitrary optimal lossless finite quantity tower is projectively equivalent, as an exact successor dynamical system, to the canonical residual/carry tower.

## Manuscript structure

The rewritten paper follows this logical order:

1. arbitrary optimal lossless finite window;
2. cardinality and bijectivity rigidity;
3. unique exact successor by conjugacy;
4. wrap event = carry-through-depth;
5. simultaneous all-depth rigidity;
6. unique residual projection between depths;
7. projective identity and composition laws;
8. universal carry-collapse certificate;
9. projective equivalence of any two optimal towers;
10. finite-local specialization with `b = Fintype.card Local`;
11. complementary emergent-construction route;
12. related work, formal audit, scope, and discussion.

## GitHub Markdown

The Markdown manuscript and foundational note use GitHub Flavored Markdown math syntax:

- inline math: `$...$`
- display math: `$$...$$`

This replaces the old `\[ ... \]` blocks that did not render reliably in GitHub Markdown views.

## LaTeX build

From this directory:

```bash
latexmk -pdf -file-line-error -halt-on-error -interaction=nonstopmode CONSERVATION_OF_QUANTITATIVE_INFORMATION.tex
```

GitHub Actions compiles the manuscript on paper-related pull requests via `.github/workflows/paper-latex.yml` and uploads the generated PDF as a workflow artifact.

## Audit discipline

The manuscript distinguishes:

- what is literally proved by the universal Lean theorem;
- the precise definition of “optimal lossless finite compression” used by the theorem;
- the canonical carry predicate imported from the pinned Carry Geometry dependency;
- related mathematical structures already present in the literature, especially odometers, carry propagation, numeration systems, and information-lossless coding;
- scoped novelty claims versus historical priority claims.

The earlier operational capstone remains in the repository as a complementary constructive route, but it is no longer presented as the strongest theorem.