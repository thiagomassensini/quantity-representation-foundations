# Conservation of Quantitative Information under Change of Representation

**Working manuscript — theorem-backed draft**

## Abstract

We study a structural question that precedes ordinary positional arithmetic: under which explicit operational conditions does a faithful representation of distinguishable quantity acquire quotient–remainder coordinates, carry transport, and a canonical positional expansion? The development begins without assuming a radix, quotient, remainder, division, modulo, positional weights, normalization, or carry. The primitive representational requirement is faithfulness: distinct source states must remain distinguishable. From this, finite-state obstructions imply that finite local representation cannot contain all distinguishing information and that fixed finite depth is insufficient for an infinite faithfully represented source. A separate operational branch then assumes an injective unit-step trajectory, a finite local observation, autonomous local dynamics, and injectivity of the local step. Finite local state forces recurrence; injective autonomous dynamics yields a unique least positive return, and a nontrivial first local step forces this emergent capacity to satisfy `b > 1`. Relative to this capacity, we construct unique cycle-count/residual coordinates by induction, define recursive emergent quotient and remainder operations without using classical division or modulo, identify local saturation with reset plus one transported unit, derive weighted inter-level transport, and iterate it to obtain finite positional expansions. We then prove intrinsic uniqueness of the resulting finite canonical digit representation before identifying it with the standard natural-number digit expansion. The entire chain is formalized in Lean 4. The main capstone theorem deliberately keeps the operational hypotheses explicit: the result does not claim that arbitrary injective coding is positional. Rather, it isolates a precise sufficient structure under which conservation of quantitative distinguishability through finite local state forces a unique canonical positional organization of the external unit-step clock.

---

## 1. Introduction

Positional notation is usually introduced constructively. One fixes a base `b > 1`, defines digits in the finite alphabet `{0, …, b-1}`, invokes Euclidean quotient and remainder, and obtains an expansion

\[
n = r_0 + r_1 b + r_2 b^2 + \cdots .
\]

Carry then appears as a normalization rule: when a local coefficient reaches the local capacity, the coefficient resets and one unit is transported to the next place. This construction is mathematically standard, but it leaves a prior structural question untouched:

> Why should a faithful finite-local representation of unbounded distinguishable quantity organize itself in this way at all?

The purpose of this work is not to replace classical arithmetic, nor to claim that every possible coding scheme is secretly positional. The goal is narrower and more precise. We ask which representational and dynamical hypotheses are sufficient to force the characteristic architecture of positional representation without placing quotient, remainder, or carry into the primitive definitions.

The guiding methodological principle is:

> **Conserve quantitative distinguishability first; identify familiar arithmetic structures only downstream.**

This principle leads naturally to a non-circularity requirement. If quotient–remainder structure is to be derived, then quotient, remainder, division, modulo, positional weights, and carry cannot be built into the initial notion of representation. Familiar arithmetic operations may be used later only as crosswalks identifying independently constructed objects.

The resulting formal development has four logically distinct layers.

1. **Cardinal and depth obstructions.** Faithfulness through finite state forces information to escape any bounded local representation and, under finite layers, to persist to arbitrarily large depth.
2. **Operational dynamics.** An injective unit-step trajectory observed through finite autonomous information-preserving local dynamics forces recurrence and a unique least positive local return.
3. **Constructive positional structure.** The emergent return capacity generates unique cycle/residual coordinates, recursive quotient/remainder-like operations, carry transport, finite positional expansion, and intrinsic canonicity.
4. **Classical crosswalks.** Only after the intrinsic construction is complete are the emergent coordinates identified with `Nat.div`, `Nat.mod`, `Nat.digits`, and the normalization API of Carry Geometry.

The main formal theorem packages these stages into an explicit capstone system. Crucially, it does not hide the transition between the cardinal/depth branch and the operational/dynamic branch: the unit trajectory and autonomous local dynamics are assumptions of the capstone, not consequences currently derived from the earlier depth theorems.

This distinction is central to the interpretation of the result. The formal claim is not

> “faithfulness alone implies positional notation.”

Instead, the formal claim is that a precise collection of operational requirements has a unique positional capstone.

---

## 2. Formal setting and methodological constraints

### 2.1 Faithful representation

Let `Q` be a type of source states and `S` a type of representation states. The primitive notion is injective encoding:

\[
\operatorname{FaithfulRepresentation}(E)
\quad\Longleftrightarrow\quad
E:Q\to S \text{ is injective}.
\]

No arithmetic structure is assumed on `Q` or `S`. In Lean this is the definition

```lean
def FaithfulRepresentation {Q S : Type*} (encode : Q → S) : Prop :=
  Function.Injective encode
```

from `FiniteStateObstruction.lean`.

The intended meaning is informational rather than syntactic: if two source states are distinguishable, then a faithful change of representation may alter their form but may not identify them.

### 2.2 Non-circularity rule

The constructive branch obeys the following discipline.

- No base is assumed at the level of the primitive source type.
- No quotient or remainder operation is used to define the emergent coordinates.
- No `Nat.div` or `Nat.mod` is used to prove existence or uniqueness of the bounded cycle decomposition.
- No `Nat.digits` is used to construct the emergent digit list.
- Carry is not a primitive operation; it appears as the later positional interpretation of a boundary transition already present in the recursive cycle dynamics.

Classical arithmetic objects are admitted only after an independent specification has been proved, at which point uniqueness permits a posterior identification.

### 2.3 The role of the natural numbers

The abstract source type `Q` is not endowed with natural-number arithmetic. Natural numbers enter as an **external unit-step clock** through an injective trajectory

\[
q_n := \operatorname{state}(n),\qquad n\in\mathbb N.
\]

The positional structure constructed in this paper is therefore, formally, a canonical organization of that external step clock relative to an emergent local capacity. Because the trajectory is injective, different clock values correspond to different source states. A future strengthening may seek to internalize the construction directly on a more abstract quantity carrier, but that is not part of the present theorem.

---

## 3. Finite-state obstruction and information escape

The first results are purely cardinal.

### 3.1 Finite state cannot faithfully encode an infinite source

If `Q` is infinite and `S` is finite, then no map `Q → S` can be injective. The Lean theorem is

```lean
theorem finiteState_obstructs_faithfulRepresentation
```

with the collision form

```lean
theorem finiteState_forces_collision
```

Hence

\[
\boxed{
\text{infinite distinguishable source}
+
\text{finite representation state}
\Longrightarrow
\text{faithfulness is impossible}.
}
\]

This is the first obstruction and contains no positional vocabulary.

### 3.2 Local collision forces nonlocal distinction

Now split a global encoding abstractly as

\[
E:Q\to L\times X,
\]

where `L` is a local state and `X` an arbitrary extension state. If two distinct source states have the same local image, global injectivity forces their extension images to differ. This is formalized by

```lean
theorem sameLocal_forces_extension_difference
```

and, when `Q` is infinite and `L` finite, by

```lean
theorem finiteLocal_forces_information_into_extension.
```

Thus a finite local channel cannot preserve all distinguishing information. If local states repeat, some distinction must survive elsewhere.

### 3.3 The extension cannot remain finitely bounded

Adding only a finite auxiliary component does not solve the obstruction. The theorem

```lean
theorem faithfulFiniteLocal_forces_infiniteExtension
```

shows that, under an infinite source and finite local state, the extension type of a faithful split representation must be infinite.

More generally, no fixed finite tower of finite layers suffices:

```lean
theorem finiteFixedDepthTower_obstructs_faithfulness.
```

This establishes a first structural consequence:

\[
\boxed{
\text{finite local capacity}
+
\text{global faithfulness}
\Longrightarrow
\text{bounded total representational depth is insufficient}.
}
\]

### 3.4 Information beyond every finite prefix

For a countably layered representation with finite layer types

\[
E:Q\to \prod_{k\in\mathbb N} L_k,
\]

the project proves that, after every finite cutoff, there exist distinct source states that agree below the cutoff but differ somewhere at or beyond it. The theorem is

```lean
theorem faithfulLayeredEncoding_has_arbitrarily_late_information.
```

Thus distinguishing information is forced to occur arbitrarily deep.

The next theorem extracts a canonical first depth at which two distinct faithfully encoded layered states differ:

```lean
theorem existsUnique_firstDistinguishingDepth.
```

Moreover, such first distinguishing depths are themselves unbounded across a faithful finite-layer encoding:

```lean
theorem faithfulFiniteLayerEncoding_has_unbounded_firstDistinguishingDepth.
```

These theorems justify the language of representational depth before any base, place value, or carry law is introduced.

### 3.5 Logical boundary

The depth results above do **not** currently derive the dynamic structures used in the capstone. In particular, the present formalization does not prove

\[
\text{unbounded distinguishing depth}
\Longrightarrow
\text{autonomous unit-step local dynamics}.
\]

The next section therefore begins a separate operational branch whose hypotheses are explicit.

---

## 4. Unit-step dynamics and emergent local capacity

### 4.1 Injective unit trajectory

The dynamic branch uses an abstract structure

```lean
structure UnitTrajectory (Q : Type*) where
  state : ℕ → Q
  transition : Q → Q
  evolves : ∀ n, state (n + 1) = transition (state n)
  state_injective : Function.Injective state
```

The trajectory is a repeated unit process. The external clock is natural-number valued, but the source type `Q` remains abstract.

If a finite local state space observes this infinite injective trajectory, recurrence is unavoidable:

```lean
theorem unitTrajectory_forces_localRecurrence.
```

With a globally faithful split encoding `Q → Local × Extension`, arbitrarily late local recurrences force arbitrarily late extension differences:

```lean
theorem unitTrajectory_has_arbitrarily_late_extensionDifference.
```

Formally, for every cutoff `N` there exist `m<n`, with `N≤m`, such that the local components coincide while the extension components differ.

### 4.2 Why recurrence alone is insufficient

A finite dynamical system can have a transient tail before entering a cycle. Therefore an arbitrary repeated local observation need not return to its initial state. This is an important obstruction: a least positive return to the origin cannot be inferred from finiteness alone.

The formal development isolates the additional structure rather than hiding it.

### 4.3 Autonomous, information-preserving local dynamics

The structure

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

imposes two operational principles.

1. **Autonomy:** one global unit step induces one local step through the same local transition map.
2. **No local information erasure:** the local step is injective.

Under finite local state these conditions are enough to cancel the transient ambiguity. The theorem

```lean
theorem autonomousLocalDynamics_has_positiveReturn
```

proves that the initial local state returns after a positive number of unit steps.

### 4.4 Emergent local capacity

Define `b` to be the least positive return time of the local observation. This is the predicate

```lean
def EmergentLocalCapacity ... (b : ℕ) : Prop := ...
```

and Lean proves

```lean
theorem existsUnique_emergentLocalCapacity.
```

Thus a canonical positive local cycle length arises from finite autonomous injective dynamics before any radix interpretation is made.

Any positive return is a period of the entire local readout:

\[
L(q_{n+b}) = L(q_n)
\]

for all `n`.

### 4.5 Nontriviality and the inequality `b > 1`

Period one remains possible for a trivial local observation. The capstone therefore records the explicit nontriviality hypothesis

\[
L(q_1)\neq L(q_0).
\]

From this and the least positive return property, the theorem

```lean
theorem emergentLocalCapacity_gt_one_of_first_step_changes
```

derives

\[
\boxed{1<b.}
\]

The inequality is therefore a consequence of a transparent operational assumption rather than an imported radix axiom.

---

## 5. Cycle-count and residual coordinates without Euclidean division

Once a positive capacity `b` is available, define

\[
\operatorname{IsCycleDecomposition}(b,n,q,r)
\iff
n=qb+r \quad\text{and}\quad r<b.
\]

At this stage `q` and `r` are interpreted as completed-cycle count and residual position inside the current local cycle.

### 5.1 Existence by unit-step induction

The theorem

```lean
theorem exists_cycleDecomposition
```

constructs `q,r` by induction on the external clock `n`.

At a successor step, there are only two possibilities. If the residual can advance while remaining below the capacity, then

\[
(q,r)\mapsto(q,r+1).
\]

If the next residual reaches the capacity boundary, then

\[
(q,r)\mapsto(q+1,0).
\]

No call to `Nat.div` or `Nat.mod` appears in the construction.

### 5.2 Uniqueness without division

The theorem

```lean
theorem cycleDecomposition_unique
```

proves that bounded decompositions do not overlap. If

\[
n=q_1b+r_1=q_2b+r_2,
\qquad
r_1,r_2<b,
\]

then

\[
q_1=q_2,
\qquad
r_1=r_2.
\]

The proof uses only order, addition, multiplication, and the residual bound. Therefore

\[
\boxed{
\forall n\;\exists!(q,r):
\quad n=qb+r,
\quad r<b.
}
\]

has been established independently of classical quotient and remainder.

### 5.3 Residual position is operational

Because the local readout is periodic with period `b`, the theorem

```lean
theorem periodicReadout_depends_only_on_residual
```

shows that if `n=qb+r`, then

\[
L(q_n)=L(q_r).
\]

Hence the residual is not merely an algebraic leftover. It records the local observable position inside the emergent cycle.

---

## 6. Recursive emergent quotient and remainder

Existence and uniqueness of coordinates are next turned into explicit recursive operations.

Define a cycle-coordinate machine starting from `(0,0)` and applying the two successor regimes. Its projections are

\[
Q_b(n):=\operatorname{emergentQuotient}(b,n),
\qquad
R_b(n):=\operatorname{emergentRemainder}(b,n).
\]

These definitions are recursive and do not use classical division or modulo.

The theorem

```lean
theorem emergentQuotientRemainder_spec
```

gives

\[
\boxed{
n=Q_b(n)b+R_b(n),
\qquad
R_b(n)<b.
}
\]

The local successor law is exact.

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

This boundary transition is already present before the word “carry” is introduced.

---

## 7. Carry as boundary transport

The foundations repository is linked downstream to the independent `carry-geometry` development. That repository contains a normalization predicate expressing bounded local digit and exact value preservation.

The theorem

```lean
theorem emergentCoordinates_are_carryGeometryNormalization
```

shows that the independently constructed pair `(R_b(n),Q_b(n))` satisfies this normalization predicate. The uniqueness theorem in Carry Geometry therefore forces

\[
\boxed{R_b(n)=\operatorname{normalizedDigit}(b,n)}
\]

and

\[
\boxed{Q_b(n)=\operatorname{carryUnits}(b,n)}.
\]

The boundary transition consequently becomes

\[
\boxed{
\text{local saturation}
\Longrightarrow
\text{reset local state to }0
+
\text{transport one unit outward}.
}
\]

This yields the precise interpretation used throughout the project:

> **Carry is the positional manifestation of the dynamically forced local boundary transition.**

The interpretation is downstream of the construction, not part of its premise.

---

## 8. Weighted transport between hierarchical levels

Let the positional level be indexed by `j`. The one-level weighted transport identity is

\[
\boxed{
a b^j
=
R_b(a)b^j
+
Q_b(a)b^{j+1}.}
\]

The first term remains at level `j`; the completed-cycle count is re-expressed one level higher.

At the first full saturation, `a=b`, one obtains

\[
R_b(b)=0,
\qquad
Q_b(b)=1,
\]

and therefore

\[
b\,b^j=b^{j+1}.
\]

The equality itself is elementary; what matters here is its structural provenance. A complete local cycle is reinterpreted as exactly one unit at the next hierarchical level.

---

## 9. Iterated transport and finite positional expansion

Define the unresolved transported quantity after `k` successive quotient steps by

\[
Q_b^{(0)}(n)=n,
\qquad
Q_b^{(k+1)}(n)=Q_b(Q_b^{(k)}(n)),
\]

and the residual digit extracted at level `k` by

\[
r_k=R_b(Q_b^{(k)}(n)).
\]

The formal development first proves an exact finite-depth expansion **with tail**:

\[
\boxed{
n=
\sum_{i<k} r_i b^i
+
Q_b^{(k)}(n)b^k.
}
\]

Nothing is discarded. The lower-level residuals plus the unresolved transported tail reconstruct the original clock value exactly.

### 9.1 Intrinsic termination

For `b>1` and `n>0`, the decomposition itself implies

\[
Q_b(n)<n.
\]

This is proved intrinsically in

```lean
theorem emergentQuotient_lt_self
```

without appealing to classical division. Thus the positive transported quantity decreases strictly until it reaches zero. Consequently there exists a finite `k` such that

\[
Q_b^{(k)}(n)=0.
\]

Substituting into the expansion with tail yields

\[
\boxed{
n=
\sum_{i<k} r_i b^i,
\qquad r_i<b.
}
\]

A finite positional expansion has therefore been obtained by iteration of the emergent transport law.

---

## 10. Canonical emergent digits

The finite expansion is packaged as a recursively defined little-endian list

\[
\operatorname{emergentDigits}_b(n).
\]

The definition is

\[
\operatorname{emergentDigits}_b(0)=[],
\]

and, for `n>0`,

\[
\operatorname{emergentDigits}_b(n)
=
R_b(n)::\operatorname{emergentDigits}_b(Q_b(n)).
\]

Before any comparison with the standard digit function, Lean proves three properties.

1. **Exact reconstruction:** the raw positional value of the list equals `n`.
2. **Digit admissibility:** every coefficient is strictly below `b`.
3. **No leading zero:** every nonempty list has nonzero most significant coefficient.

### 10.1 Intrinsic uniqueness

The strongest canonicity statement is index-free:

```lean
theorem intrinsicCanonicalExpansion_eq_emergentDigits_of_value
```

It says that any finite coefficient list whose digits are all `< b` and whose most significant digit is nonzero is exactly the emergent digit list of the value it represents.

Equivalently, for every `n` there exists a unique canonical finite list `L` satisfying

\[
\operatorname{value}_b(L)=n,
\]

all coefficients are `<b`, and a nonempty list has nonzero leading coefficient.

Thus the positional representation is not merely produced by one algorithm. It is characterized intrinsically by the representation conditions themselves.

---

## 11. The foundational capstone theorem

The complete operational hypotheses are packaged in

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

The capstone certificate at a candidate capacity `b` records:

- that `b` is the emergent least positive local return;
- that `1<b`;
- arbitrarily late escape of distinguishing information into the extension component;
- periodic local readout;
- control of local readout by the residual coordinate;
- unique cycle-count/residual coordinates for every external clock value;
- exact bridge to Carry Geometry normalization;
- unique finite canonical positional representation.

The main theorem is

```lean
theorem existsUnique_foundationalCapstone
    {Q LocalState Extension : Type*}
    [Finite LocalState]
    (system : FoundationalOperationalRepresentation Q LocalState Extension) :
    ∃! b : ℕ, FoundationalCapstoneAt system b
```

The uniqueness of the complete capstone is inherited from uniqueness of the least positive local return. All later structure is attached canonically to the same capacity.

A concise mathematical reading is therefore:

\[
\boxed{
\begin{aligned}
&\text{faithful nonrepeating unit-step representation}\\
&+\text{finite local state}\\
&+\text{autonomous injective local dynamics}\\
&+\text{nontrivial first local step}\\[1mm]
&\Longrightarrow\\[1mm]
&\exists!\,b>1\text{ supporting unique cycle/residual coordinates,}\\
&\text{carry transport, and unique finite canonical positional representation.}
\end{aligned}
}
\]

This is the main theorem-level content of the present manuscript.

---

## 12. Downstream identification with classical arithmetic

The formal construction deliberately precedes the familiar natural-number API. Only after the emergent operations satisfy the unique bounded decomposition specification do we prove

\[
\boxed{Q_b(n)=n/b}
\]

and

\[
\boxed{R_b(n)=n\bmod b.}
\]

Likewise, only after construction, finite termination, reconstruction, admissibility, no leading zero, and intrinsic uniqueness do we prove

\[
\boxed{
\operatorname{emergentDigits}_b(n)
=
\operatorname{Nat.digits}_b(n).
}
\]

These equalities are not used as premises for the construction. They are posterior crosswalks showing that the independently obtained objects coincide with the standard arithmetic ones.

The logical direction is therefore

\[
\text{operational dynamics}
\Longrightarrow
(Q_b,R_b)
\Longrightarrow
\text{carry and hierarchical transport}
\Longrightarrow
\text{canonical finite digits}
\Longrightarrow
\text{classical identification}.
\]

---

## 13. What is proved, what is interpreted, and what remains open

A central purpose of the formalization is to keep these categories distinct.

### 13.1 Formally proved

Within the stated hypotheses, Lean verifies:

- finite-state obstruction to faithful encoding of an infinite source;
- forced nonlocal distinction when a finite local component collides;
- impossibility of fixed finite depth for finite layered encodings of an infinite source;
- distinguishing information beyond every finite prefix;
- unique first distinguishing depth;
- local recurrence along an injective unit-step trajectory observed through finite local state;
- positive return under autonomous injective local dynamics;
- unique least positive return;
- derivation of `b>1` from nontrivial first local step;
- existence and uniqueness of bounded cycle/residual coordinates without classical division or modulo;
- recursive emergent quotient and remainder;
- boundary reset plus one transported unit;
- weighted hierarchical transport;
- finite positional expansion via intrinsic descent;
- canonical emergent digit list;
- intrinsic uniqueness of canonical finite positional representation;
- downstream equivalence with classical quotient, remainder, digits, and Carry Geometry normalization.

### 13.2 Interpretive statement

The theorem chain supports the interpretation that, within the explicit operational system, positional structure is not inserted as an arbitrary convention at the final stage. It is the canonical organization compatible with a finite autonomous local cycle, faithful persistence of distinction, and repeated unit transport.

In this precise setting, carry is not an independent rule added to positional notation. It is the positional reading of local saturation followed by information-preserving transport.

### 13.3 Non-claims

The present work does **not** prove that:

- every injective coding of an infinite set is positional;
- faithfulness alone implies quotient–remainder structure;
- the cardinal/depth theorems alone imply `UnitTrajectory` or `AutonomousLocalDynamics`;
- every finite local dynamics has a nontrivial capacity greater than one;
- the abstract source type `Q` itself has been endowed with or forced to carry natural-number arithmetic;
- all possible non-positional finite representations have been excluded under weaker assumptions than those explicitly stated.

These are not technical footnotes. They define the exact scope of the theorem.

---

## 14. Relation to Carry Geometry

The present project is logically upstream of the normalization layer developed in `carry-geometry`.

Carry Geometry starts from a finite positional alphabet and exact value preservation and proves uniqueness of normalization. In particular, its normalization API identifies the unique admissible local digit and carry count satisfying the value equation.

The foundations project descends one level further. It asks where the local capacity, bounded residual, completed-cycle count, and carry event come from before positional normalization is assumed.

The bridge theorem shows that the pair generated dynamically by the foundations project already satisfies the normalization predicate of Carry Geometry. Therefore the two theories meet exactly at the point where an emergent local cycle becomes a positional digit/carry pair.

The relation can be summarized as

\[
\boxed{
\text{finite faithful operational dynamics}
\Longrightarrow
\text{emergent cycle coordinates}
\Longrightarrow
\text{Carry Geometry normalization}.
}
\]

This gives a formal provenance for the normalization variables used downstream by the carry-geometric theory.

---

## 15. Formal verification and reproducibility

All principal statements in this manuscript are formalized in Lean 4 in the repository `quantity-representation-foundations`. The project exposes a dedicated audit surface in

`QuantityRepresentationFoundations/Audit.lean`.

The constructive path is organized through the following modules:

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

The dependency ordering itself reflects the non-circularity policy: the crosswalk modules come after the corresponding emergent structures have already been constructed and characterized.

---

## 16. Discussion

The main conceptual outcome is a separation between **quantity**, **representation**, and **arithmetic coordinates**.

At the beginning, quantity states are only assumed distinguishable and faithfully representable. Finite local capacity then produces an obstruction: local state alone cannot preserve all distinctions. Once repeated unit evolution is required to be locally autonomous and information-preserving, finite local state produces recurrence. The least return period gives a capacity. Relative to that capacity, the external unit clock decomposes canonically into completed cycles and residual position. Local saturation produces the only successor transition compatible with the bounded residual specification: reset locally and transport one unit. Iteration turns that transport into hierarchy. Hierarchy terminates because the transported quantity strictly decreases for a nontrivial capacity. The resulting list of bounded residuals is then characterized uniquely by exact reconstruction and absence of leading zero.

This chain is useful even independently of the final identification with ordinary base-`b` notation. It isolates which aspects of positional arithmetic depend on which structural hypotheses.

It also exposes the main gap toward a stronger foundational claim. The cardinal/depth branch shows that information must occur arbitrarily deeply, while the capstone assumes a unit-step dynamical organization. A future result deriving the latter from more primitive principles of admissible representation change would connect the two branches more tightly. Such a theorem would reduce the number of operational assumptions and strengthen the emergence claim.

A second direction is internalization. At present the canonical positional representation is built on the external natural-number clock indexing an injective trajectory in an abstract state type `Q`. One may ask whether an appropriate abstract notion of quantitative succession, without an a priori natural-number clock, is enough to reconstruct the same structure internally.

A third direction is hypothesis minimization. Injectivity of the local step is sufficient to eliminate transient information loss and obtain a return to the initial local state. It may not be necessary in its current full strength. Determining the weakest local reversibility or cancellativity principle that still yields a canonical capacity is a natural formal problem.

---

## 17. Conclusion

We have formalized a route from conserved distinguishability to canonical positional structure under explicit operational assumptions. The construction does not begin with Euclidean division, remainder, digits, or carry. Instead:

\[
\text{faithfulness}
\to
\text{finite-state obstruction}
\to
\text{information escape}
\to
\text{operational recurrence}
\to
\text{unique local capacity}
\to
\text{cycle/residual coordinates}
\to
\text{boundary transport}
\to
\text{carry}
\to
\text{hierarchical positional expansion}
\to
\text{intrinsic canonicity}.
\]

The familiar identities

\[
Q_b(n)=n/b,
\qquad
R_b(n)=n\bmod b,
\qquad
\operatorname{emergentDigits}_b(n)=\operatorname{Nat.digits}_b(n)
\]

appear only after the corresponding structures have been independently constructed.

The foundational capstone can therefore be stated compactly:

> **Within a faithful, nonrepeating unit-step representation whose local state is finite, autonomous, information-preserving, and nontrivial, there exists a unique emergent capacity `b>1`; relative to that capacity the external unit-step clock admits unique cycle/residual coordinates, carry transport, and a unique finite canonical positional representation.**

The theorem does not collapse representation theory into positional arithmetic. Rather, it identifies a precise operational regime in which positional arithmetic is the forced canonical outcome.

---

## Appendix A. Main Lean theorem map

| Mathematical role | Lean theorem / structure | Module |
|---|---|---|
| Faithfulness | `FaithfulRepresentation` | `FiniteStateObstruction.lean` |
| Finite-state obstruction | `finiteState_obstructs_faithfulRepresentation` | `FiniteStateObstruction.lean` |
| Information escape | `finiteLocal_forces_information_into_extension` | `InformationEscape.lean` |
| Infinite extension | `faithfulFiniteLocal_forces_infiniteExtension` | `UnboundedExtension.lean` |
| No fixed finite depth | `finiteFixedDepthTower_obstructs_faithfulness` | `UnboundedExtension.lean` |
| Late information | `faithfulLayeredEncoding_has_arbitrarily_late_information` | `UnboundedPrefixDepth.lean` |
| First distinguishing depth | `existsUnique_firstDistinguishingDepth` | `FirstDistinguishingDepth.lean` |
| Unit trajectory | `UnitTrajectory` | `UnitDynamicsLocalRecurrence.lean` |
| Forced recurrence | `unitTrajectory_forces_localRecurrence` | `UnitDynamicsLocalRecurrence.lean` |
| Late extension distinction | `unitTrajectory_has_arbitrarily_late_extensionDifference` | `UnitDynamicsLocalRecurrence.lean` |
| Autonomous local dynamics | `AutonomousLocalDynamics` | `FirstLocalReturnCapacity.lean` |
| Positive return | `autonomousLocalDynamics_has_positiveReturn` | `FirstLocalReturnCapacity.lean` |
| Unique emergent capacity | `existsUnique_emergentLocalCapacity` | `FirstLocalReturnCapacity.lean` |
| Genuine capacity | `emergentLocalCapacity_gt_one_of_first_step_changes` | `FoundationalCapstone.lean` |
| Unique cycle coordinates | `existsUnique_cycleCoordinates` | `EmergentCycleDecomposition.lean` |
| Recursive coordinates | `emergentQuotient`, `emergentRemainder` | `EmergentQuotientRemainder.lean` |
| Emergent QR specification | `emergentQuotientRemainder_spec` | `EmergentQuotientRemainder.lean` |
| Carry boundary | `emergent_step_at_boundary` | `EmergentQuotientRemainder.lean` |
| Classical quotient crosswalk | `emergentQuotient_eq_div` | `ClassicalQRCrosswalk.lean` |
| Classical remainder crosswalk | `emergentRemainder_eq_mod` | `ClassicalQRCrosswalk.lean` |
| Carry Geometry bridge | `emergentCoordinates_eq_carryGeometryNormalization` | `CarryGeometryNormalizationBridge.lean` |
| Weighted transport | `emergent_weighted_positional_transport` | `EmergentWeightedPositionalTransport.lean` |
| Expansion with tail | `emergent_positional_expansion_with_tail` | `IteratedEmergentPositionalExpansion.lean` |
| Intrinsic descent | `emergentQuotient_lt_self` | `IteratedEmergentPositionalExpansion.lean` |
| Finite expansion | `exists_finite_emergent_positional_expansion` | `IteratedEmergentPositionalExpansion.lean` |
| Emergent digits | `emergentDigits` | `CanonicalEmergentDigits.lean` |
| Exact reconstruction | `rawExpansionValue_emergentDigits` | `CanonicalEmergentDigits.lean` |
| Intrinsic uniqueness | `intrinsicCanonicalExpansion_eq_emergentDigits_of_value` | `IntrinsicPositionalUniqueness.lean` |
| Unique canonical representation | `existsUnique_intrinsicCanonicalExpansion` | `IntrinsicPositionalUniqueness.lean` |
| Foundational system | `FoundationalOperationalRepresentation` | `FoundationalCapstone.lean` |
| Capstone certificate | `FoundationalCapstoneAt` | `FoundationalCapstone.lean` |
| Main theorem | `existsUnique_foundationalCapstone` | `FoundationalCapstone.lean` |
| Standard digits crosswalk | `foundationalCapstone_recovers_natDigits` | `FoundationalCapstone.lean` |

---

## Appendix B. Current strengthening problems

The present formal development naturally exposes three next foundational questions.

1. **Dynamic derivation problem.** Can `UnitTrajectory` and enough of `AutonomousLocalDynamics` be derived from weaker representation-change principles rather than assumed in the capstone?
2. **Internal quantity problem.** Can the positional construction be internalized on an abstract quantity carrier without using `ℕ` as the external step clock?
3. **Minimal-hypothesis problem.** Which of autonomy, local injectivity, global split faithfulness, and first-step nontriviality can be weakened while retaining a unique nontrivial capacity and canonical positional structure?

These questions mark the boundary between the theorem established here and a stronger general theory of representation-induced arithmetic structure.
