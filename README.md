# Quantity Representation Foundations

Formal Lean 4 study of how quotient–remainder coordinates, carry, and canonical positional representation can arise from explicit structural requirements on faithful finite-local representations, instead of being postulated as primitive rules.

> **Guiding principle:** conserve quantitative distinguishability first; identify familiar arithmetic representations only downstream.

The current repository has reached a **formalized foundational capstone**.

For the full theorem-by-theorem account, see [`FOUNDATIONAL_CAPSTONE.md`](FOUNDATIONAL_CAPSTONE.md).

---

## Main theorem

The capstone is implemented in [`FoundationalCapstone.lean`](QuantityRepresentationFoundations/FoundationalCapstone.lean).

```lean
theorem existsUnique_foundationalCapstone
    {Q LocalState Extension : Type*}
    [Finite LocalState]
    (system : FoundationalOperationalRepresentation Q LocalState Extension) :
    ∃! b : ℕ, FoundationalCapstoneAt system b
```

The theorem deliberately does **not** say that arbitrary faithfulness alone forces positional notation.

Instead, `FoundationalOperationalRepresentation` records the operational assumptions explicitly:

- an injective unit-step trajectory `ℕ → Q`;
- a globally faithful split representation `Q → LocalState × Extension`;
- finite local state;
- autonomous local dynamics intertwined with the global unit step;
- an injective local step, so local information is not erased;
- agreement between the autonomous local observation and the local component of the faithful encoding;
- a nontrivial first local step.

No radix, quotient, remainder, division, modulo, digit list, positional normalization, or carry is part of this primitive system.

From these hypotheses Lean proves the existence of a **unique** emergent capacity `b`, and derives `1 < b` rather than assuming it separately.

At that same `b`, the capstone packages:

- arbitrarily late local recurrence with compensating distinction in the extension component;
- periodic local readout;
- residual control of the local observation;
- unique cycle-count/residual coordinates;
- exact identification of those coordinates with Carry Geometry normalization;
- a unique finite canonical positional representation of every external step count.

---

## Formal chain

The repository separates construction from later identification.

```text
faithful distinguishability
        ↓
finite-state obstruction
        ↓
information must escape finite local state
        ↓
no fixed finite tower of finite layers is enough
        ↓
arbitrarily deep distinguishing information
        ↓
canonical first distinguishing depth

[explicit operational dynamics]
        ↓
finite local recurrence
        ↓
least positive local return
        ↓
unique nontrivial capacity b > 1
        ↓
unique cycle count + residual position
        ↓
recursive emergent quotient Q_b and remainder R_b
        ↓
boundary reset + one transported unit
        ↓
carry
        ↓
weighted transport between successive levels
        ↓
iterated transport
        ↓
finite positional expansion
        ↓
canonical emergent digit list
        ↓
intrinsic uniqueness of canonical positional representation
```

Only **after** those objects are constructed do the classical crosswalks appear:

\[
Q_b(n)=n/b,
\qquad
R_b(n)=n\bmod b,
\]

and

\[
\operatorname{emergentDigits}_b(n)=\operatorname{Nat.digits}_b(n).
\]

This ordering is the main non-circularity invariant of the project.

---

## The pre-positional obstruction layer

The first theorem assumes no arithmetic structure at all:

```lean
def FaithfulRepresentation {Q S : Type*} (encode : Q → S) : Prop :=
  Function.Injective encode
```

Then:

```lean
theorem finiteState_obstructs_faithfulRepresentation
```

proves that an infinite family of distinguishable states cannot be faithfully encoded into a finite state space.

The next modules establish:

- [`InformationEscape.lean`](QuantityRepresentationFoundations/InformationEscape.lean): finite local collisions force distinguishing information into an extension component;
- [`UnboundedExtension.lean`](QuantityRepresentationFoundations/UnboundedExtension.lean): the extension cannot remain finite, and fixed finite depth cannot suffice;
- [`UnboundedPrefixDepth.lean`](QuantityRepresentationFoundations/UnboundedPrefixDepth.lean): distinguishing information exists beyond every finite prefix;
- [`FirstDistinguishingDepth.lean`](QuantityRepresentationFoundations/FirstDistinguishingDepth.lean): every distinct faithfully represented layered pair has a unique first distinguishing depth, and such depths are unbounded.

These are genuine pre-positional theorems: no base, quotient, remainder, digit, positional weight, or carry is used.

### Important boundary

The capstone does **not** currently derive `UnitTrajectory` or `AutonomousLocalDynamics` from the layered-depth theorems above.

Those dynamic objects are explicit operational assumptions in the capstone system. This distinction is intentional and is documented in detail in [`FOUNDATIONAL_CAPSTONE.md`](FOUNDATIONAL_CAPSTONE.md).

---

## Emergent local capacity

The dynamic branch begins with an abstract injective unit-step trajectory:

```lean
structure UnitTrajectory (Q : Type*) where
  state : ℕ → Q
  transition : Q → Q
  evolves : ∀ n, state (n + 1) = transition (state n)
  state_injective : Function.Injective state
```

Here `ℕ` is an **external clock**. The abstract source type `Q` is not given natural-number arithmetic.

Finite local observation forces recurrence. Adding autonomous, injective local dynamics yields a unique least positive return:

```lean
def EmergentLocalCapacity ...

theorem existsUnique_emergentLocalCapacity
```

The capstone additionally requires that the first local step actually changes the local observation and proves:

```lean
theorem emergentLocalCapacity_gt_one_of_first_step_changes
```

so the resulting capacity is genuinely

\[
\boxed{1<b.}
\]

---

## Quotient and remainder are constructed before `/` and `%`

For positive `b`, define a bounded cycle decomposition:

```lean
def IsCycleDecomposition (b n q r : ℕ) : Prop :=
  n = q * b + r ∧ r < b
```

Existence and uniqueness are proved without using division or modulo.

Then the project defines a recursive cycle machine:

```lean
def cycleCoordinatesRec ...
def emergentQuotient ...
def emergentRemainder ...
```

with

\[
\boxed{
n=Q_b(n)b+R_b(n),
\qquad R_b(n)<b.
}
\]

The successor dynamics has exactly two regimes:

- inside a cycle: the residual advances and the cycle count stays fixed;
- at the boundary: the residual resets to zero and the cycle count increases by one.

Only later does [`ClassicalQRCrosswalk.lean`](QuantityRepresentationFoundations/ClassicalQRCrosswalk.lean) prove

\[
Q_b(n)=n/b,
\qquad
R_b(n)=n\bmod b.
\]

---

## Carry emerges at the boundary

The repository depends on [`carry-geometry`](https://github.com/thiagomassensini/carry-geometry) only after the emergent coordinates have already been constructed.

[`CarryGeometryNormalizationBridge.lean`](QuantityRepresentationFoundations/CarryGeometryNormalizationBridge.lean) proves that the emergent coordinates satisfy Carry Geometry's bounded value-preserving normalization predicate. By uniqueness:

\[
\boxed{
R_b(n)=\operatorname{normalizedDigit}(b,n)
}
\]

and

\[
\boxed{
Q_b(n)=\operatorname{carryUnits}(b,n).
}
\]

At local saturation, one unit step gives exactly

\[
\boxed{
R\mapsto0,
\qquad
Q\mapsto Q+1.
}
\]

So, within the formal framework:

> **carry is the positional manifestation of the dynamically forced local boundary transition.**

---

## Hierarchical transport and finite positional expansion

The weighted transport theorem is

\[
\boxed{
a b^j=R_b(a)b^j+Q_b(a)b^{j+1}.}
\]

The current residual remains at level `j`; the completed-cycle count is transported to `j+1`.

Iterating this gives an exact finite-depth identity with an explicit unresolved tail:

\[
\boxed{
n=
\sum_{i<k}r_i b^i
+Q_b^{(k)}(n)b^k.
}
\]

For `b > 1`, the project proves intrinsically that positive emergent quotients strictly decrease. Therefore the tail eventually reaches zero and a finite expansion exists:

\[
\boxed{
n=\sum_{i<k}r_i b^i,
\qquad r_i<b.
}
\]

See:

- [`EmergentWeightedPositionalTransport.lean`](QuantityRepresentationFoundations/EmergentWeightedPositionalTransport.lean)
- [`IteratedEmergentPositionalExpansion.lean`](QuantityRepresentationFoundations/IteratedEmergentPositionalExpansion.lean)

---

## Canonical emergent digits and intrinsic uniqueness

The project defines its own finite little-endian digit list:

```lean
def emergentDigits (b : ℕ) (hb : 1 < b) (n : ℕ) : List ℕ := ...
```

Before comparing it with `Nat.digits`, Lean proves:

- exact reconstruction of `n`;
- every digit is `< b`;
- no nonempty representation has a zero most-significant digit.

The strongest intrinsic uniqueness theorem is:

```lean
theorem intrinsicCanonicalExpansion_eq_emergentDigits_of_value
```

Any admissible finite coefficient list with no leading zero is the emergent digit list of its own represented value.

Consequently:

```lean
theorem existsUnique_intrinsicCanonicalExpansion
```

gives a unique canonical positional representation for every `n`.

Only after that theorem does the repository identify it with the standard representation:

\[
\boxed{
\operatorname{emergentDigits}_b(n)
=
\operatorname{Nat.digits}_b(n).
}
\]

See:

- [`CanonicalEmergentDigits.lean`](QuantityRepresentationFoundations/CanonicalEmergentDigits.lean)
- [`IntrinsicPositionalUniqueness.lean`](QuantityRepresentationFoundations/IntrinsicPositionalUniqueness.lean)

---

## What the capstone supports

Under the explicit operational hypotheses, the formal development supports the statement:

> A faithful nonrepeating unit-step representation with finite, autonomous, information-preserving local state is forced to have a unique nontrivial local capacity. Relative to that capacity, the external unit-step clock has unique cycle/residual coordinates; boundary saturation is carry normalization; iterated transport yields a finite positional expansion; and the canonical expansion is intrinsically unique.

A compact slogan is:

\[
\boxed{
\text{finite local capacity}
+\text{faithful persistence}
+\text{autonomous unit dynamics}
\Longrightarrow
\text{canonical positional structure}.
}
\]

The hypotheses on the left are essential parts of the theorem statement.

---

## What is not claimed

The repository does **not** currently prove that:

- every arbitrary injective coding is positional;
- faithfulness alone implies positional notation;
- the layered-depth theorems alone generate the dynamic hypotheses;
- every finite local dynamics has capacity `> 1` without a nontriviality condition;
- the abstract source type `Q` itself carries the arithmetic of `ℕ`.

The current positional construction lives on the **external natural-number unit-step clock** of an injective trajectory in `Q`.

These boundaries are part of the result, not caveats to be hidden.

---

## Repository map

The constructive path is organized as:

1. `FiniteStateObstruction.lean`
2. `InformationEscape.lean`
3. `UnboundedExtension.lean`
4. `UnboundedPrefixDepth.lean`
5. `FirstDistinguishingDepth.lean`
6. `UnitDynamicsLocalRecurrence.lean`
7. `FirstLocalReturnCapacity.lean`
8. `EmergentCycleDecomposition.lean`
9. `EmergentQuotientRemainder.lean`
10. `ClassicalQRCrosswalk.lean`
11. `CarryGeometryNormalizationBridge.lean`
12. `EmergentWeightedPositionalTransport.lean`
13. `IteratedEmergentPositionalExpansion.lean`
14. `CanonicalEmergentDigits.lean`
15. `IntrinsicPositionalUniqueness.lean`
16. `FoundationalCapstone.lean`

The full kernel-facing theorem/axiom audit is in:

- [`QuantityRepresentationFoundations/Audit.lean`](QuantityRepresentationFoundations/Audit.lean)

The detailed mathematical narrative, exact theorem map, scope, and suggested article architecture are in:

- [`FOUNDATIONAL_CAPSTONE.md`](FOUNDATIONAL_CAPSTONE.md)

---

## Status

**Foundational capstone formalized in Lean 4.**

The principal strengthening questions are now:

1. Can the operational dynamic hypotheses be derived from weaker principles of representation and admissible change of representation?
2. Can the construction be internalized on a quantity carrier more abstract than the external `ℕ` clock?
3. Which capstone hypotheses can be weakened without losing the forced positional structure?
4. How broadly does conservation of distinguishable quantitative information generalize beyond ordinary positional representation?
