# Foundational Capstone — theorem-level note

## Conservation of quantitative information under change of representation

This note records the current formal state of **Quantity Representation Foundations** after the foundational capstone was closed in Lean 4.

The guiding question is:

> **What structural features are forced when distinguishable quantitative information must be represented faithfully through finite local states and persistent unit-step dynamics?**

The project is deliberately upstream of positional arithmetic. Its constructive direction does **not** begin by postulating a radix, quotient, remainder, digits, division, modulo, positional weights, normalization, or carry. Those objects are introduced only after earlier structures have been constructed and characterized.

The central methodological principle is therefore:

> **Conserve quantitative distinguishability first; identify familiar arithmetic representations only downstream.**

This is also the intended meaning of the working article title:

> **Conservation of Quantitative Information under Change of Representation**

---

## 1. What is formally proved — and what is not

The repository now proves a complete capstone theorem for an **explicit operational system**. It does **not** prove the unrestricted statement

> “every faithful representation of quantity must be positional.”

That would be too strong.

Instead, the capstone makes every additional operational hypothesis visible. Under those hypotheses, finite local state forces recurrence, recurrence yields a unique nontrivial local capacity, and that capacity supports unique cycle/residual coordinates, carry normalization, and a unique finite canonical positional representation.

The direct capstone theorem is:

```lean
theorem existsUnique_foundationalCapstone
    {Q LocalState Extension : Type*}
    [Finite LocalState]
    (system : FoundationalOperationalRepresentation Q LocalState Extension) :
    ∃! b : ℕ, FoundationalCapstoneAt system b
```

The theorem is implemented in:

- [`QuantityRepresentationFoundations/FoundationalCapstone.lean`](QuantityRepresentationFoundations/FoundationalCapstone.lean)

### Important logical boundary

The repository also proves earlier cardinal/depth results showing that finite local state cannot contain all distinguishing information and that finite layered representations must carry information arbitrarily deep.

However, **the capstone theorem does not derive `UnitTrajectory` or `AutonomousLocalDynamics` from those depth theorems**. The dynamic structure is an explicit hypothesis of `FoundationalOperationalRepresentation`.

Therefore the rigorous picture is:

1. **Cardinal/depth branch:** finite local representation forces information escape and unbounded distinguishing depth.
2. **Operational/dynamic branch:** once an injective unit-step trajectory and autonomous information-preserving local dynamics are given, finite local state forces recurrence and a canonical capacity.
3. **Constructive positional branch:** that capacity generates quotient/remainder-like coordinates, carry, hierarchical transport, finite digits, and intrinsic positional uniqueness.
4. **Crosswalk branch:** only after construction do the familiar `Nat.div`, `Nat.mod`, `Nat.digits`, and Carry Geometry normalization appear as identifications.

Any future theorem that derives the dynamic hypotheses themselves from more primitive representational principles would strengthen the chain further, but that theorem is **not** silently assumed here.

---

# 2. Primitive representational principle: faithfulness

The first definition is intentionally minimal:

```lean
def FaithfulRepresentation {Q S : Type*} (encode : Q → S) : Prop :=
  Function.Injective encode
```

A representation is faithful exactly when distinct source states remain distinguishable.

No arithmetic structure is assumed on `Q` or `S`.

Source:

- [`FiniteStateObstruction.lean`](QuantityRepresentationFoundations/FiniteStateObstruction.lean)

The first theorem is the finite-state obstruction:

```lean
theorem finiteState_obstructs_faithfulRepresentation
    {Q S : Type*} [Infinite Q] [Finite S] (encode : Q → S) :
    ¬ FaithfulRepresentation encode
```

Equivalently, every map from an infinite source into a finite state space collides:

```lean
theorem finiteState_forces_collision ... :
    ∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ encode q₁ = encode q₂
```

Thus:

\[
\boxed{
\text{infinite distinguishable source}
+\text{finite state}
\Longrightarrow
\text{faithful encoding impossible}
}
\]

This stage contains no QR, radix, carry, or positional notation.

---

# 3. Information escape from finite local state

A global representation is next split abstractly into

\[
E:Q\to L\times X,
\]

where `L` is a local component and `X` is an arbitrary extension component.

The theorem

```lean
theorem sameLocal_forces_extension_difference
```

says that if two distinct source states collide in `L`, global faithfulness forces their `X` components to differ.

With infinite source and finite local state:

```lean
theorem finiteLocal_forces_information_into_extension
```

gives

\[
\boxed{
q_1\neq q_2,
\quad L(q_1)=L(q_2)
\Longrightarrow
X(q_1)\neq X(q_2).
}
\]

Source:

- [`InformationEscape.lean`](QuantityRepresentationFoundations/InformationEscape.lean)

This is the first exact theorem behind the phrase **information must leave the finite local state**.

It still does not claim that `X` is a next digit, a scale, a quotient, or a carry channel.

---

# 4. No bounded auxiliary state and no fixed finite depth

The extension cannot itself remain finite:

```lean
theorem faithfulFiniteLocal_forces_infiniteExtension
```

and no fixed finite tower of finite layers can faithfully encode an infinite source:

```lean
theorem finiteFixedDepthTower_obstructs_faithfulness
```

Source:

- [`UnboundedExtension.lean`](QuantityRepresentationFoundations/UnboundedExtension.lean)

Thus, under finite layers,

\[
\boxed{
\text{faithfulness}
\Longrightarrow
\text{no fixed finite representational depth suffices}.
}
\]

Again, this is a cardinal theorem, not yet a positional theorem.

---

# 5. Information beyond every finite prefix

For a countably layered encoding

\[
E:Q\to\prod_{k\in\mathbb N}L_k
\]

with every layer finite, the project defines agreement below a cutoff:

```lean
def AgreeBelow ...
```

and proves:

```lean
theorem faithfulLayeredEncoding_has_arbitrarily_late_information
```

For every finite depth `d`, there are distinct states that agree on every layer below `d` and differ somewhere at or beyond `d`.

Source:

- [`UnboundedPrefixDepth.lean`](QuantityRepresentationFoundations/UnboundedPrefixDepth.lean)

Formally:

\[
\boxed{
\forall d\;\exists q_1\neq q_2:
E(q_1)|_{<d}=E(q_2)|_{<d},
\quad
\exists k\ge d,\ E(q_1)_k\neq E(q_2)_k.
}
\]

This is the exact sense in which finite-layer faithfulness forces **arbitrarily deep distinguishing information**.

---

# 6. Canonical first distinguishing depth

For two distinct faithfully encoded layered states, define:

```lean
def FirstDifferenceAt ...
```

meaning that they agree at every level below `k` and differ at `k`.

The repository proves existence and uniqueness:

```lean
theorem existsUnique_firstDistinguishingDepth
```

and then proves those first distinguishing depths are unbounded over a faithful encoding by finite layers:

```lean
theorem faithfulFiniteLayerEncoding_has_unbounded_firstDistinguishingDepth
```

Source:

- [`FirstDistinguishingDepth.lean`](QuantityRepresentationFoundations/FirstDistinguishingDepth.lean)

So a canonical notion of **depth of first distinction** exists before any radix or positional weight is introduced.

---

# 7. Unit-step dynamics: the operational branch

The dynamic branch introduces:

```lean
structure UnitTrajectory (Q : Type*) where
  state : ℕ → Q
  transition : Q → Q
  evolves : ∀ n, state (n + 1) = transition (state n)
  state_injective : Function.Injective state
```

Source:

- [`UnitDynamicsLocalRecurrence.lean`](QuantityRepresentationFoundations/UnitDynamicsLocalRecurrence.lean)

Here `ℕ` is an **external unit-step clock**. No addition, quotient, remainder, base, or positional structure is imposed on the abstract source type `Q`.

Because the trajectory is injective, different step counts represent distinct quantity states.

For any finite local observation, the theorem

```lean
theorem unitTrajectory_forces_localRecurrence
```

forces two different clock times to have the same local observation.

With a faithful split representation `Q → Local × Extension`, the theorem

```lean
theorem unitTrajectory_has_arbitrarily_late_extensionDifference
```

strengthens this to arbitrarily late times:

\[
\boxed{
\forall N\;\exists m<n,\ N\le m,
\quad L(q_m)=L(q_n),
\quad X(q_m)\neq X(q_n).
}
\]

This is the dynamic form of information escape.

---

# 8. Autonomous local dynamics and emergent capacity

Local recurrence somewhere does **not** by itself imply return to the initial state: a finite dynamical system may contain a transient tail before entering a cycle.

The project therefore isolates the additional hypothesis explicitly:

```lean
structure AutonomousLocalDynamics
    {Q : Type*}
    (trajectory : UnitTrajectory Q)
    (LocalState : Type*) where
  observe : Q → LocalState
  step : LocalState → LocalState
  intertwines : ∀ q,
    observe (trajectory.transition q) = step (observe q)
  step_injective : Function.Injective step
```

Source:

- [`FirstLocalReturnCapacity.lean`](QuantityRepresentationFoundations/FirstLocalReturnCapacity.lean)

The local state evolves autonomously, and its step map is injective, so local information is not erased.

Finite local state then forces a positive return to the initial local observation:

```lean
theorem autonomousLocalDynamics_has_positiveReturn
```

The least positive return is defined as:

```lean
def EmergentLocalCapacity ... (b : ℕ) : Prop := ...
```

and is unique:

```lean
theorem existsUnique_emergentLocalCapacity
```

Thus a canonical local cycle length emerges before any radix interpretation:

\[
\boxed{
\exists! b>0:\quad
L(q_b)=L(q_0),
\quad b\text{ least positive return}.
}
\]

Every such return is a period of the whole local readout:

```lean
theorem emergentLocalCapacity_periodic_readout
```

---

# 9. Why the capstone capacity is genuinely greater than one

A trivial local observation could have period `1`. The capstone therefore records one more explicit operational condition:

```lean
first_local_step_changes :
  localDynamics.observe (trajectory.state 1) ≠
    localDynamics.observe (trajectory.state 0)
```

The theorem

```lean
theorem emergentLocalCapacity_gt_one_of_first_step_changes
```

then derives

\[
\boxed{1<b.}
\]

This is important: the capstone does **not** simply assume a radix-like `b > 1` after deriving a positive cycle. It derives nontrivial capacity from the first-step nontriviality hypothesis.

---

# 10. Cycle count and residual position without division or modulo

For positive `b`, the project defines a bounded cycle decomposition:

```lean
def IsCycleDecomposition (b n q r : ℕ) : Prop :=
  n = q * b + r ∧ r < b
```

The existence proof is constructive by unit-step induction and does not call `Nat.div` or `Nat.mod`:

```lean
theorem exists_cycleDecomposition
```

Uniqueness is also proved without division or modulo:

```lean
theorem cycleDecomposition_unique
```

Therefore:

```lean
theorem existsUnique_cycleCoordinates
```

gives

\[
\boxed{
\forall n\;\exists!(q,r):
\quad n=qb+r,
\quad r<b.
}
\]

Source:

- [`EmergentCycleDecomposition.lean`](QuantityRepresentationFoundations/EmergentCycleDecomposition.lean)

The residual is operationally meaningful. If the local readout has period `b`, then

```lean
theorem periodicReadout_depends_only_on_residual
```

proves

\[
\boxed{L(q_n)=L(q_r).}
\]

So `r` is not merely an algebraic leftover: it is the observable position inside the local cycle.

---

# 11. Emergent quotient and remainder as recursive operations

The project does not stop at existential witnesses. It defines its own recursive state machine:

```lean
def nextCycleCoordinates ...
def cycleCoordinatesRec ...
def emergentQuotient ...
def emergentRemainder ...
```

Source:

- [`EmergentQuotientRemainder.lean`](QuantityRepresentationFoundations/EmergentQuotientRemainder.lean)

These functions are constructed without classical quotient or modulo.

They satisfy:

```lean
theorem emergentQuotientRemainder_spec
```

hence

\[
\boxed{
n=Q_b(n)b+R_b(n),
\qquad R_b(n)<b.
}
\]

The recursive update has exactly two regimes.

### Inside the cycle

If

\[
R_b(n)+1<b,
\]

then

\[
Q_b(n+1)=Q_b(n),
\qquad
R_b(n+1)=R_b(n)+1.
\]

Lean theorem:

```lean
theorem emergent_step_inside_cycle
```

### At the boundary

If

\[
R_b(n)+1=b,
\]

then

\[
Q_b(n+1)=Q_b(n)+1,
\qquad
R_b(n+1)=0.
\]

Lean theorem:

```lean
theorem emergent_step_at_boundary
```

This is the primitive dynamic event later identified as carry.

---

# 12. Classical quotient and remainder are downstream crosswalks

Only after `Q_b` and `R_b` have been independently defined and characterized does the repository compare them with the standard natural-number operations.

Source:

- [`ClassicalQRCrosswalk.lean`](QuantityRepresentationFoundations/ClassicalQRCrosswalk.lean)

The final identification is:

\[
\boxed{Q_b(n)=n/b}
\]

and

\[
\boxed{R_b(n)=n\bmod b.}
\]

Lean theorems:

```lean
theorem emergentQuotient_eq_div
theorem emergentRemainder_eq_mod
```

The logical direction is therefore:

\[
\text{constructed cycle dynamics}
\Longrightarrow(Q_b,R_b)
\Longrightarrow
\text{unique bounded decomposition}
\Longrightarrow
(Q_b,R_b)=(/,\%).
\]

Division and modulo identify the already-constructed coordinates; they do not generate them.

---

# 13. Carry as the positional reading of the boundary transition

The repository is linked explicitly to [`carry-geometry`](https://github.com/thiagomassensini/carry-geometry).

Source:

- [`CarryGeometryNormalizationBridge.lean`](QuantityRepresentationFoundations/CarryGeometryNormalizationBridge.lean)

The emergent pair already satisfies Carry Geometry's coefficient-normalization predicate:

```lean
theorem emergentCoordinates_are_carryGeometryNormalization
```

Uniqueness of normalization then gives:

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

At the boundary, the emergent transition becomes exactly:

\[
\boxed{
\text{digit reset to }0
\quad+\quad
\text{one transported carry unit}.
}
\]

Lean theorem:

```lean
theorem emergent_step_at_boundary_is_oneCarry
```

This justifies the precise interpretive statement:

> **Carry is the positional manifestation of the dynamically forced local boundary transition.**

---

# 14. Weighted transport between hierarchical levels

At positional level `j`, the project proves:

\[
\boxed{
a b^j
=R_b(a)b^j+Q_b(a)b^{j+1}.
}
\]

Source:

- [`EmergentWeightedPositionalTransport.lean`](QuantityRepresentationFoundations/EmergentWeightedPositionalTransport.lean)

Lean theorem:

```lean
theorem emergent_weighted_positional_transport
```

Interpretation:

- `R_b(a)b^j` is the information retained at the current level;
- `Q_b(a)b^(j+1)` is the information transported to the next level.

A full local cycle at level `j` becomes one unit at level `j+1`.

Thus hierarchical place-value transport is not introduced as a primitive representation rule; it is the weighted form of the already-derived cycle split.

---

# 15. Iteration produces finite positional expansion

Define the repeatedly transported quantity:

```lean
def iteratedEmergentQuotient (b n : ℕ) : ℕ → ℕ
```

and the residual extracted at depth `k`:

```lean
def emergentPositionalDigit (b n k : ℕ) : ℕ
```

Source:

- [`IteratedEmergentPositionalExpansion.lean`](QuantityRepresentationFoundations/IteratedEmergentPositionalExpansion.lean)

At every finite depth `k`:

```lean
theorem emergent_positional_expansion_with_tail
```

proves

\[
\boxed{
n=
\sum_{i<k}r_i b^i
+Q_b^{(k)}(n)b^k.
}
\]

Nothing is discarded: resolved information is in the finite prefix; unresolved information is the explicit transported tail.

For `b>1`, the descent theorem

```lean
theorem emergentQuotient_lt_self
```

is proved **intrinsically** from

\[
n=Q_b(n)b+R_b(n)
\]

and no longer uses classical division.

Hence repeated transport eventually reaches zero:

```lean
theorem exists_iteratedEmergentQuotient_eq_zero
```

and therefore:

```lean
theorem exists_finite_emergent_positional_expansion
```

proves the existence of a finite expansion

\[
\boxed{
n=\sum_{i<k}r_i b^i,
\qquad r_i<b.
}
\]

---

# 16. Canonical emergent digit list

The finite expansion is packaged into a recursively defined digit list:

```lean
def emergentDigits (b : ℕ) (hb : 1 < b) (n : ℕ) : List ℕ :=
  if n = 0 then []
  else
    emergentRemainder b n ::
      emergentDigits b hb (emergentQuotient b n)
```

Source:

- [`CanonicalEmergentDigits.lean`](QuantityRepresentationFoundations/CanonicalEmergentDigits.lean)

The repository proves before using `Nat.digits` that:

1. the list reconstructs the value exactly;
2. every digit is `< b`;
3. a nonempty list has a nonzero most significant digit.

Lean theorems:

```lean
theorem rawExpansionValue_emergentDigits
theorem emergentDigits_digits_admissible
theorem emergentDigits_no_leading_zero
```

---

# 17. Intrinsic uniqueness of positional representation

Source:

- [`IntrinsicPositionalUniqueness.lean`](QuantityRepresentationFoundations/IntrinsicPositionalUniqueness.lean)

The strongest index-free theorem is:

```lean
theorem intrinsicCanonicalExpansion_eq_emergentDigits_of_value
```

It states that any finite list `L` satisfying

\[
\forall d\in L,\quad d<b
\]

and having no leading zero is exactly the emergent digit list of its own raw value:

\[
\boxed{
L=\operatorname{emergentDigits}_b(\operatorname{value}_b(L)).
}
\]

The proof is structural induction on the list itself. It does not use:

- `Nat.div`;
- `Nat.mod`;
- `Nat.digits`;
- `normalizeCoefficients`;
- even the quotient-descent theorem as an induction principle.

For a prescribed quantity `n`, the canonical existence-and-uniqueness theorem is:

```lean
theorem existsUnique_intrinsicCanonicalExpansion
```

which gives

\[
\boxed{
\exists!L:
\operatorname{value}_b(L)=n,
\quad
\forall d\in L\;d<b,
\quad
L\neq[]\Rightarrow\operatorname{last}(L)\neq0.
}
\]

Only after this uniqueness theorem is available does `Nat.digits` enter as a known representation satisfying the same characterization:

```lean
theorem natDigits_eq_emergentDigits_by_intrinsic_uniqueness
```

Thus `Nat.digits` is a **downstream identification of the unique emergent representation**, not a construction primitive.

---

# 18. The explicit operational system used by the capstone

The capstone bundles its assumptions in:

```lean
structure FoundationalOperationalRepresentation
    (Q LocalState Extension : Type*) where
  trajectory : UnitTrajectory Q
  encode : Q → LocalState × Extension
  faithful : FaithfulRepresentation encode
  localDynamics : AutonomousLocalDynamics trajectory LocalState
  local_agrees_with_encoding :
    ∀ q : Q, localDynamics.observe q = (encode q).1
  first_local_step_changes :
    localDynamics.observe (trajectory.state 1) ≠
      localDynamics.observe (trajectory.state 0)
```

This says exactly what is assumed:

1. an injective unit-step trajectory of quantity states;
2. a globally faithful split representation;
3. a finite local channel (`[Finite LocalState]` is required by the capstone theorem);
4. autonomous local dynamics;
5. an injective local step, through `AutonomousLocalDynamics.step_injective`;
6. agreement between the autonomous observation and the local component of the faithful encoding;
7. a genuinely nontrivial first local step.

It does **not** put quotient, remainder, division, modulo, digits, carry, or a radix expansion into the primitive system.

---

# 19. The capstone certificate

For a candidate `b`, the structure

```lean
structure FoundationalCapstoneAt ... (b : ℕ) : Prop
```

packages all of the following:

### 19.1 Dynamical capacity

\[
\operatorname{EmergentLocalCapacity}(b)
\]

with

\[
\boxed{1<b.}
\]

### 19.2 Arbitrarily late information escape

For every cutoff there are later distinct trajectory states with equal local encoding but different extension encoding.

### 19.3 Periodicity

\[
\boxed{L(q_{n+b})=L(q_n).}
\]

### 19.4 Residual control

\[
\boxed{L(q_n)=L(q_{R_b(n)}).}
\]

### 19.5 Unique cycle coordinates

\[
\boxed{
\forall n\;\exists!(q,r):
\quad n=qb+r,
\quad r<b.
}
\]

### 19.6 Carry Geometry normalization

\[
\boxed{
Q_b(n)=\operatorname{carryUnits}(b,n),
\qquad
R_b(n)=\operatorname{normalizedDigit}(b,n).
}
\]

### 19.7 Unique canonical finite positional representation

\[
\boxed{
\forall n\;\exists!L:
\operatorname{value}_b(L)=n,
\quad d<b,
\quad\text{no leading zero}.
}
\]

The main theorem then states:

\[
\boxed{
\exists!b\in\mathbb N:\quad
\operatorname{FoundationalCapstoneAt}(system,b).
}
\]

This is the current formal capstone of the project.

---

# 20. Constructive layer versus classical crosswalk layer

The repository deliberately distinguishes the two layers below.

## Constructive / intrinsic layer

Constructed before classical QR/digits are needed as primitives:

- faithfulness obstruction;
- information escape;
- unbounded finite-layer depth;
- first distinguishing depth;
- local recurrence on an injective unit trajectory;
- emergent least positive local return;
- cycle decomposition by induction;
- recursive `emergentQuotient` and `emergentRemainder`;
- boundary transition;
- weighted transport;
- intrinsic quotient descent;
- finite positional expansion;
- `emergentDigits`;
- intrinsic canonical uniqueness.

## Downstream identifications

Only afterward:

\[
Q_b(n)=n/b,
\qquad
R_b(n)=n\bmod b,
\]

\[
(Q_b,R_b)
=(\operatorname{carryUnits},\operatorname{normalizedDigit}),
\]

and

\[
\operatorname{emergentDigits}_b(n)=\operatorname{Nat.digits}_b(n).
\]

This separation is the core non-circularity invariant of the repository.

---

# 21. What the theorem means — and what it does not mean

## Supported interpretation

Within the explicit operational hypotheses, the formal development supports the statement:

> A faithful nonrepeating unit-step representation with finite, autonomous, information-preserving local state is forced to develop a unique nontrivial local capacity. Relative to that capacity, the unit-step clock has unique cycle/residual coordinates; boundary saturation is exactly carry normalization; iterated transport yields a finite positional expansion; and that expansion is intrinsically unique.

A compact mathematical slogan is:

\[
\boxed{
\text{finite local capacity}
+\text{faithful persistence}
+\text{autonomous unit dynamics}
\Longrightarrow
\text{canonical positional structure}.
}
\]

The words in the left-hand side matter: they are not decorative.

## Not proved

The repository does **not** currently prove:

- that every conceivable injective coding of `ℕ` or of an infinite type is positional;
- that arbitrary representation changes must satisfy `FoundationalOperationalRepresentation`;
- that the layered-depth theorems alone imply `UnitTrajectory` or `AutonomousLocalDynamics`;
- that every finite local system has `b>1` without the nontrivial first-step hypothesis;
- that `Q` itself is endowed intrinsically with the arithmetic of `ℕ`.

The current positional construction applies to the **external unit-step clock `ℕ`** associated with an injective trajectory in the abstract quantity-state type `Q`.

This distinction is fundamental.

---

# 22. Exact theorem map

| Stage | Main Lean object/theorem | Module |
|---|---|---|
| Faithfulness | `FaithfulRepresentation` | `FiniteStateObstruction.lean` |
| Finite-state no-go | `finiteState_obstructs_faithfulRepresentation` | `FiniteStateObstruction.lean` |
| Information escape | `finiteLocal_forces_information_into_extension` | `InformationEscape.lean` |
| Extension must be unbounded | `faithfulFiniteLocal_forces_infiniteExtension` | `UnboundedExtension.lean` |
| Fixed-depth no-go | `finiteFixedDepthTower_obstructs_faithfulness` | `UnboundedExtension.lean` |
| Arbitrarily deep information | `faithfulLayeredEncoding_has_arbitrarily_late_information` | `UnboundedPrefixDepth.lean` |
| Canonical first depth | `existsUnique_firstDistinguishingDepth` | `FirstDistinguishingDepth.lean` |
| Unbounded first depths | `faithfulFiniteLayerEncoding_has_unbounded_firstDistinguishingDepth` | `FirstDistinguishingDepth.lean` |
| Unit dynamics | `UnitTrajectory` | `UnitDynamicsLocalRecurrence.lean` |
| Forced recurrence | `unitTrajectory_forces_localRecurrence` | `UnitDynamicsLocalRecurrence.lean` |
| Late extension escape | `unitTrajectory_has_arbitrarily_late_extensionDifference` | `UnitDynamicsLocalRecurrence.lean` |
| Autonomous local dynamics | `AutonomousLocalDynamics` | `FirstLocalReturnCapacity.lean` |
| Positive return | `autonomousLocalDynamics_has_positiveReturn` | `FirstLocalReturnCapacity.lean` |
| Emergent capacity | `existsUnique_emergentLocalCapacity` | `FirstLocalReturnCapacity.lean` |
| Cycle decomposition | `existsUnique_cycleCoordinates` | `EmergentCycleDecomposition.lean` |
| Residual readout | `emergentCycleResidual_controls_localReadout` | `EmergentCycleDecomposition.lean` |
| Recursive QR coordinates | `emergentQuotient`, `emergentRemainder` | `EmergentQuotientRemainder.lean` |
| Step dichotomy | `emergent_step_dichotomy` | `EmergentQuotientRemainder.lean` |
| Classical QR crosswalk | `emergentQuotient_eq_div`, `emergentRemainder_eq_mod` | `ClassicalQRCrosswalk.lean` |
| Carry bridge | `emergentCoordinates_eq_carryGeometryNormalization` | `CarryGeometryNormalizationBridge.lean` |
| Carry boundary | `emergent_step_at_boundary_is_oneCarry` | `CarryGeometryNormalizationBridge.lean` |
| Weighted level transport | `emergent_weighted_positional_transport` | `EmergentWeightedPositionalTransport.lean` |
| Expansion with tail | `emergent_positional_expansion_with_tail` | `IteratedEmergentPositionalExpansion.lean` |
| Intrinsic descent | `emergentQuotient_lt_self` | `IteratedEmergentPositionalExpansion.lean` |
| Finite expansion | `exists_finite_emergent_positional_expansion` | `IteratedEmergentPositionalExpansion.lean` |
| Canonical digit list | `emergentDigits` | `CanonicalEmergentDigits.lean` |
| Exact digit value | `rawExpansionValue_emergentDigits` | `CanonicalEmergentDigits.lean` |
| Intrinsic list uniqueness | `intrinsicCanonicalExpansion_eq_emergentDigits_of_value` | `IntrinsicPositionalUniqueness.lean` |
| Unique positional representation | `existsUnique_intrinsicCanonicalExpansion` | `IntrinsicPositionalUniqueness.lean` |
| Operational capstone system | `FoundationalOperationalRepresentation` | `FoundationalCapstone.lean` |
| Capstone certificate | `FoundationalCapstoneAt` | `FoundationalCapstone.lean` |
| Capacity `> 1` | `emergentLocalCapacity_gt_one_of_first_step_changes` | `FoundationalCapstone.lean` |
| Final capstone | `existsUnique_foundationalCapstone` | `FoundationalCapstone.lean` |
| Final `Nat.digits` crosswalk | `foundationalCapstone_recovers_natDigits` | `FoundationalCapstone.lean` |

The full axiom inspection surface is:

- [`QuantityRepresentationFoundations/Audit.lean`](QuantityRepresentationFoundations/Audit.lean)

---

# 23. Relation to Carry Geometry

This repository is logically upstream of [`carry-geometry`](https://github.com/thiagomassensini/carry-geometry) in the following sense.

Carry Geometry already contains a normalization theorem saying that, once a radix `b`, a bounded digit condition, and exact coefficient-value preservation are given, the normalized digit and carry units are uniquely forced.

Quantity Representation Foundations addresses an earlier question:

> Where can the bounded local coordinate, completed-cycle coordinate, and hierarchical transport structure come from before those objects are named “digit”, “quotient”, “remainder”, or “carry”? 

The bridge theorem shows that the independently constructed cycle coordinates satisfy Carry Geometry's normalization predicate. Normalization uniqueness then identifies them exactly with the carry/digit API.

So the connection is not merely terminological:

\[
\boxed{
\text{emergent cycle dynamics}
\longrightarrow
\text{bounded value-preserving split}
\longrightarrow
\text{Carry Geometry normalization}.
}
\]

---

# 24. Suggested article architecture

The formal development now supports a paper organized approximately as follows.

## Part I — Conservation and obstruction

1. Distinguishable multiplicity and faithful representation.
2. Finite-state obstruction.
3. Information escape from finite local state.
4. Fixed-depth impossibility and unbounded distinguishing depth.

## Part II — Operational recurrence

5. Injective unit-step trajectories.
6. Finite local recurrence.
7. Autonomous injective local dynamics.
8. Least positive local return and emergent capacity.
9. Nontriviality and the derivation of `b > 1`.

## Part III — Emergent arithmetic coordinates

10. Constructive cycle decomposition without division/modulo.
11. Recursive emergent quotient and remainder.
12. Boundary saturation and carry.
13. Weighted transport across levels.

## Part IV — Positional representation

14. Iterated transport and finite expansion.
15. Canonical emergent digits.
16. Intrinsic existence and uniqueness.

## Part V — Identification theorems

17. Crosswalk with Euclidean quotient/remainder.
18. Crosswalk with Carry Geometry.
19. Crosswalk with `Nat.digits`.

## Part VI — Scope and open strengthening

20. Exact operational assumptions of the capstone.
21. What is not yet derived.
22. Possible derivation of the dynamic hypotheses from more primitive compositional/locality axioms.
23. Generalization beyond the external natural-number clock.

---

# 25. Compact theorem-level summary

The formal story can now be compressed to:

\[
\begin{aligned}
&\text{faithful representation}\
&+\text{finite local state}\
&+\text{injective unit-step trajectory}\
&+\text{autonomous injective local dynamics}\
&+\text{nontrivial first local step}\[1mm]
&\Downarrow\\
&\text{forced local recurrence + nonlocal information escape}\
&\Downarrow\\
&\exists!\,b>1\text{, least positive local return}\
&\Downarrow\\
&\forall n\;\exists!(q,r):\ n=qb+r,\ r<b\
&\Downarrow\\
&(Q_b,R_b)\text{ recursively constructed}\
&\Downarrow\\
&\text{boundary saturation}=\text{carry}\
&\Downarrow\\
&\text{hierarchical weighted transport}\
&\Downarrow\\
&\text{finite positional expansion}\
&\Downarrow\\
&\exists!\text{ canonical digit list for every }n.
\end{aligned}
\]

Only afterward:

\[
Q_b(n)=n/b,
\qquad
R_b(n)=n\bmod b,
\]

and

\[
\operatorname{emergentDigits}_b(n)=\operatorname{Nat.digits}_b(n).
\]

That separation — construction first, classical identification later — is the principal formal invariant of the project.

---

## Current status

**Foundational capstone: formalized.**

The next research question is no longer “can the full chain be written down?” It can.

The sharper questions are now:

- Can the operational dynamic hypotheses themselves be derived from weaker principles of representation/change of representation?
- Can the construction be internalized on a quantity carrier more abstract than the external natural-number step clock?
- Which assumptions are logically necessary, and which can be weakened?
- How far does the conservation-of-information viewpoint generalize beyond ordinary positional representation?

Those are strengthening questions downstream of the current capstone, not missing pieces hidden inside its theorem statement.
