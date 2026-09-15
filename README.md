# Quantity Representation Foundations

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22774108.svg)](https://doi.org/10.5281/zenodo.22774108)

Lean 4 formalization of a rigidity principle for exact quantitative representation:

> **Optimal lossless finite representation has no independent quantitative dynamics beyond the residual/carry tower, up to change of representation.**

The repository contains two complementary formal programs:

1. an **emergent construction route**, which builds quotient/remainder-like coordinates, carry transport, and canonical positional expansion from explicit structural hypotheses without postulating those objects;
2. a **universal rigidity route**, which proves that arbitrary optimal lossless finite codes — including opaque recodings — are projectively equivalent to the canonical residual/carry dynamics.

The current main result is the universal carry-collapse capstone.

For the theorem-by-theorem account, see [`FOUNDATIONAL_CAPSTONE.md`](FOUNDATIONAL_CAPSTONE.md).

---

## Main theorem

The capstone is implemented in:

- [`QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean`](QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean)

```lean
theorem universal_optimal_lossless_representation_collapses_to_carry
    {b : ℕ}
    (tower : LosslessCompressedTower b)
    (hb : 1 < b) :
    UniversalCarryCollapseCertificate tower (lt_trans Nat.zero_lt_one hb)
```

At depth `k`, the code type may be completely opaque. The finite-window assumptions are only:

```lean
structure LosslessCompressedWindow
    (b k : ℕ) (Code : Type*) [Fintype Code] where
  encode : Fin (b ^ k) → Code
  faithful : Function.Injective encode
  state_budget : Fintype.card Code ≤ b ^ k
```

No digit syntax, positional order, place value, quotient, remainder, native carry rule, or truncation rule is assumed on `Code`.

From these hypotheses Lean forces:

$$
|Code_k| = b^k,
$$

so every encoder is bijective;

$$
Code_k \simeq \operatorname{Fin}(b^k),
$$

with exact unit successor conjugate to the canonical cyclic quantity successor;

$$
\text{wrap at depth }k
\iff
\operatorname{carryAfterIncrementAtDepth}(b,k,n);
$$

and, for every $k\le m$, a unique coherent projection

$$
\pi_{k,m}:Code_m\to Code_k
$$

which becomes

$$
\pi_{k,m}(n)=n\bmod b^k
$$

after changing coordinates.

The projections satisfy

$$
\pi_{k,k}=\operatorname{id}
$$

and

$$
\pi_{j,k}\circ\pi_{k,m}=\pi_{j,m}.
$$

So the complete finite-depth hierarchy is forced up to representation equivalence.

---

## What “collapse to carry” means

The theorem does **not** say that every valid code must visibly look like ordinary base-$b$ digits.

A Gray-like code, an arbitrary permutation of labels, or another opaque exact code may look completely different.

What Lean proves is that these are changes of coordinates of the same quantitative object.

At each depth:

$$
\boxed{Code_k \simeq \operatorname{Fin}(b^k).}
$$

The exact successor is conjugate to the canonical successor, the wrap event is exactly the carry event, and all cross-depth maps are the canonical residual projections after decoding and re-encoding.

The invariant is therefore the **projective residual/carry dynamical system**, not a particular spelling of numerals.

The direct comparison theorem is:

```lean
theorem any_two_optimal_lossless_towers_are_projectively_equivalent
```

It proves that any two arbitrary optimal lossless towers with the same finite capacity differ only by levelwise changes of representation preserving successor and every forced projection.

---

## Finite local cells

For an arbitrary finite local state type `Local`, define a depth-`k` code as simply

```lean
abbrev LocalWord (Local : Type u) (k : ℕ) := Fin k → Local
```

No positional meaning is built into this type.

Its cardinality is

$$
|\operatorname{LocalWord}(Local,k)| = |Local|^k.
$$

Writing

$$
b=|Local|,
$$

any faithful encoding of the $b^k$ distinguishable quantity states into `k` local cells is automatically bijective.

The specialized capstone is:

```lean
theorem universal_finiteLocal_lossless_representation_collapses_to_carry
    {Local : Type u} [Fintype Local]
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local) :
    UniversalCarryCollapseCertificate tower.toCompressedTower
      (lt_trans Nat.zero_lt_one hLocal)
```

Thus the capacity/radix in this model is not supplied independently:

$$
\boxed{b=|Local|.}
$$

---

## Universal rigidity chain

The current universal theorem was built in four steps.

```text
arbitrary optimal lossless finite window
        ↓
exact cardinality is forced
        ↓
encoder is bijective
        ↓
exact successor is unique up to conjugacy
        ↓
wrap event is exactly carry
        ↓
all finite depths satisfy the same rigidity
        ↓
adjacent-depth projection is uniquely residual
        ↓
all k ≤ m projections are uniquely residual
        ↓
identity + projective composition laws
        ↓
UNIVERSAL CARRY-COLLAPSE CERTIFICATE
```

The corresponding modules are:

- [`UniversalLosslessCompression.lean`](QuantityRepresentationFoundations/UniversalLosslessCompression.lean)
- [`UniversalLosslessCompressionTower.lean`](QuantityRepresentationFoundations/UniversalLosslessCompressionTower.lean)
- [`UniversalCrossDepthCarryCoherence.lean`](QuantityRepresentationFoundations/UniversalCrossDepthCarryCoherence.lean)
- [`UniversalProjectiveCarryTower.lean`](QuantityRepresentationFoundations/UniversalProjectiveCarryTower.lean)
- [`UniversalCarryCollapseCapstone.lean`](QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean)

---

## Earlier emergent construction route

The repository also contains a separate constructive route that begins upstream of quotient, remainder, carry, and digits.

Its chain is:

```text
faithful distinguishability
        ↓
finite-state obstruction
        ↓
information escape
        ↓
unbounded distinguishing depth
        ↓
unit-step dynamics
        ↓
finite local recurrence
        ↓
emergent local capacity
        ↓
unique cycle-count / residual coordinates
        ↓
emergent quotient + remainder
        ↓
boundary reset + transported unit
        ↓
carry
        ↓
weighted hierarchical transport
        ↓
finite positional expansion
        ↓
intrinsic uniqueness of canonical digits
```

Important modules include:

- [`FiniteStateObstruction.lean`](QuantityRepresentationFoundations/FiniteStateObstruction.lean)
- [`InformationEscape.lean`](QuantityRepresentationFoundations/InformationEscape.lean)
- [`UnboundedPrefixDepth.lean`](QuantityRepresentationFoundations/UnboundedPrefixDepth.lean)
- [`FirstDistinguishingDepth.lean`](QuantityRepresentationFoundations/FirstDistinguishingDepth.lean)
- [`FirstLocalReturnCapacity.lean`](QuantityRepresentationFoundations/FirstLocalReturnCapacity.lean)
- [`EmergentCycleDecomposition.lean`](QuantityRepresentationFoundations/EmergentCycleDecomposition.lean)
- [`EmergentQuotientRemainder.lean`](QuantityRepresentationFoundations/EmergentQuotientRemainder.lean)
- [`CarryGeometryNormalizationBridge.lean`](QuantityRepresentationFoundations/CarryGeometryNormalizationBridge.lean)
- [`EmergentWeightedPositionalTransport.lean`](QuantityRepresentationFoundations/EmergentWeightedPositionalTransport.lean)
- [`IteratedEmergentPositionalExpansion.lean`](QuantityRepresentationFoundations/IteratedEmergentPositionalExpansion.lean)
- [`CanonicalEmergentDigits.lean`](QuantityRepresentationFoundations/CanonicalEmergentDigits.lean)
- [`IntrinsicPositionalUniqueness.lean`](QuantityRepresentationFoundations/IntrinsicPositionalUniqueness.lean)
- [`FoundationalCapstone.lean`](QuantityRepresentationFoundations/FoundationalCapstone.lean)

That route remains useful because it explains how familiar arithmetic structure can be constructed rather than assumed. The universal rigidity branch answers the stronger invariance question: arbitrary optimal lossless recodings do not create a different quantitative mechanics.

---

## Connection to Carry Geometry

This repository depends on [`carry-geometry`](https://github.com/thiagomassensini/carry-geometry).

The constructive route proves that its emergent coordinates coincide with Carry Geometry normalization:

```lean
theorem emergentCoordinates_are_carryGeometryNormalization

theorem emergentRemainder_eq_normalizedDigit

theorem emergentQuotient_eq_carryUnits
```

The universal route uses the finite-window bridge:

```lean
theorem windowSuccessor_eq_zero_iff_carry
```

which proves that the canonical cyclic wrap event is exactly

```lean
CarryGeometry.carryAfterIncrementAtDepth
```

and then transports this invariant through arbitrary optimal lossless codes.

---

## Scope

The main universal theorem quantifies over `LosslessCompressedTower b`.

At depth `k`, this means a faithful representation

$$
\operatorname{Fin}(b^k)\hookrightarrow Code_k
$$

with

$$
|Code_k|\le b^k.
$$

This is the formal notion of **optimal lossless finite compression** used by the theorem.

Redundant codes with additional non-quantitative states fall outside that optimal budget. The theorem does not claim that redundant error-correcting structure disappears; it says that once redundant degrees of freedom are excluded, the exact quantitative dynamics and hierarchy are forced up to coordinates.

---

## Audit

The kernel audit surface is:

- [`QuantityRepresentationFoundations/Audit.lean`](QuantityRepresentationFoundations/Audit.lean)

It includes the universal capstone theorems:

```lean
#print axioms QuantityRepresentationFoundations.universal_optimal_lossless_representation_collapses_to_carry
#print axioms QuantityRepresentationFoundations.universal_finiteLocal_lossless_representation_collapses_to_carry
#print axioms QuantityRepresentationFoundations.any_two_optimal_lossless_towers_are_projectively_equivalent
```

---

## Paper and archival release

The `paper/` directory contains the current manuscript built around the universal carry-rigidity theorem:

- [`paper/CONSERVATION_OF_QUANTITATIVE_INFORMATION.md`](paper/CONSERVATION_OF_QUANTITATIVE_INFORMATION.md)
- [`paper/CONSERVATION_OF_QUANTITATIVE_INFORMATION.tex`](paper/CONSERVATION_OF_QUANTITATIVE_INFORMATION.tex)
- [`paper/LITERATURE_REVIEW.md`](paper/LITERATURE_REVIEW.md)
- [`paper/README.md`](paper/README.md)

The archival research release is **v1.0.0**, deposited on Zenodo with DOI:

**[10.5281/zenodo.22774108](https://doi.org/10.5281/zenodo.22774108)**

Suggested citation:

> Massensini, Thiago (2026). *Conservation of Quantitative Information under Change of Representation: Universal Carry Rigidity of Optimal Lossless Finite Quantity Codes* (Version 1.0.0). Zenodo. https://doi.org/10.5281/zenodo.22774108
