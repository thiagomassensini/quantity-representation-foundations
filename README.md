# Quantity Representation Foundations

**Goal:** formalize how quotient–remainder, positional normalization, and carry can emerge from minimal requirements on faithful representations of quantity, rather than being postulated as primitive rules.

## Guiding question

> What must remain invariant when the representation of a quantity changes?

The project studies the boundary between a physical/operational notion of distinguishable multiplicity and a mathematical representation of that multiplicity.

The intended direction is deliberately **pre-positional**. We do **not** begin by assuming a base, quotient, remainder, digits, carry, or a positional numeral system.

Instead, we ask which structures are forced by requirements such as:

- **distinguishability:** different quantities must remain distinguishable;
- **faithfulness:** a representation must not create, erase, or identify quantitative information;
- **finite local capacity:** a local representational component has only finitely many states;
- **unbounded extensibility:** arbitrarily large quantities must remain representable;
- **operational persistence:** admissible transformations of the representation must preserve the represented quantity.

## First obstruction

A first theorem should require no quotient–remainder machinery at all:

> A finite state space cannot faithfully encode an unbounded family of pairwise distinguishable quantities.

This is a cardinality/pigeonhole obstruction. It is intended to be the first formal step from finite local capacity toward the necessity of additional representational structure.

The planned chain is:

```text
distinguishable multiplicity
        ↓
faithful representation
        ↓
finite local capacity + unbounded quantities
        ↓
finite-state obstruction
        ↓
necessity of additional level / scale / extension
        ↓
local saturation + information-preserving transport
        ↓
quotient–remainder structure
        ↓
positional normalization
        ↓
carry
        ↓
Carry Geometry
```

The arrows after the finite-state obstruction are **research targets**, not assumptions and not yet claimed as theorems in this repository.

## Non-circularity rule

The central methodological constraint is:

> A theorem claiming that quotient–remainder or carry is necessary must not place quotient, remainder, division, modulo, positional weights, or carry into the definition of the primitive representation from which the theorem is derived.

Those objects may appear only after they have been constructed or characterized by earlier results.

Using `ℕ` as a metatheoretic index for quantities in an initial Lean model is acceptable only when the theorem under study does not obtain its conclusion from pre-existing `Nat.div`, `Nat.mod`, or positional numeral machinery. Later stages should abstract the carrier further where useful.

## Relation to Carry Geometry

This repository is conceptually upstream of [`carry-geometry`](https://github.com/thiagomassensini/carry-geometry).

`carry-geometry` already proves, once a finite positional alphabet and exact value preservation are present, that positional normalization is forced and unique. In particular, its `CarryGeometry/Normalization.lean` contains results such as:

- `coefficient_normalization_unique`;
- `weighted_coefficient_normalization`;
- `finiteDigitAlphabet_not_closed_under_raw_addition`;
- `normalizeCoefficients_preserves_value`;
- `finiteAlphabetNormalization_forced`.

The purpose here is to descend one logical level further: explain why a faithful, finite, scalable representation of quantity is driven toward the kind of capacity/transport structure on which those theorems act.

## Epistemic layers

We will keep four layers explicit.

1. **Operational motivation** — distinguishable multiplicity and conservation of quantitative information.
2. **Definitions** — the weakest mathematical structures sufficient to state representation and faithfulness.
3. **Theorems** — consequences proved from those definitions in Lean.
4. **Interpretation** — claims about emergence, discovery, or physical meaning, clearly separated from the formal theorem statements.

## Immediate formal milestones

1. Define a minimal notion of faithful representation without QR/carry.
2. Prove the finite-state obstruction.
3. Separate literal/extensive realization from compressed representation without defining the distinction in terms of QR.
4. Formalize a notion of finite local capacity plus extensibility.
5. Determine the weakest additional compositional assumptions under which saturation forces information to leave the local state.
6. Characterize the resulting transport law.
7. Only then derive/identify quotient–remainder and connect it to `CarryGeometry.finiteAlphabetNormalization_forced`.

## Status

**Research foundation / formalization in progress.**

The repository intentionally starts with a weaker statement than the desired final theorem. Each strengthening should be accompanied by an explicit dependency audit so that quotient–remainder is shown to emerge rather than being smuggled into the hypotheses.
