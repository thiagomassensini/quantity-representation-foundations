# v1.0.0 — Universal Carry Rigidity of Optimal Lossless Finite Quantity Codes

This is the first citable research release of **Quantity Representation Foundations**.

The release packages the Lean 4 formalization, kernel audit surface, foundational capstone, and accompanying preprint for the universal carry-rigidity theorem.

## Main result

The central theorem is:

```lean
universal_optimal_lossless_representation_collapses_to_carry
```

For an arbitrary optimal lossless compressed quantity tower of capacity `b > 1`, with completely opaque code types at every finite depth, the formalization proves that:

- every depth-`k` code space has exactly `b^k` states;
- every faithful optimal encoder is bijective;
- exact unit successor is uniquely conjugate to the canonical cyclic successor;
- the code-level wrap event is exactly the carry-through-depth event;
- for every `k ≤ m`, the unique zero-preserving successor-equivariant projection from depth `m` to depth `k` is residual reduction after decode/re-encode;
- equal-depth projections are identities;
- projections compose transitively;
- any two optimal lossless towers with the same capacity are projectively equivalent.

In this precise sense, arbitrary optimal lossless finite quantity codes differ only by change of representation: once coordinates are factored out, the successor dynamics and cross-depth hierarchy are the canonical residual/carry tower.

## Included research artifacts

- complete Lean 4 source;
- kernel audit surface (`QuantityRepresentationFoundations/Audit.lean`);
- universal foundational capstone (`FOUNDATIONAL_CAPSTONE.md`);
- publication manuscript in Markdown and LaTeX;
- compiled preprint PDF attached to this release;
- scoped literature review and BibTeX bibliography;
- `CITATION.cff` metadata for GitHub citation support;
- `.zenodo.json` metadata for Zenodo ingestion as a preprint.

## Reproducibility

The repository is pinned to its Lean/mathlib toolchain through `lean-toolchain` and `lake-manifest.json`. The main branch is validated by Lean CI, and the paper source is independently compiled by the Paper LaTeX CI.

## Citation and archival

This tagged release is intended as the archival research version associated with the Zenodo DOI generated from the GitHub–Zenodo integration.

**Paper title:** *Conservation of Quantitative Information under Change of Representation: Universal Carry Rigidity of Optimal Lossless Finite Quantity Codes*

**Author:** Thiago Massensini

**Version:** 1.0.0

**Release date:** 2026-09-15
