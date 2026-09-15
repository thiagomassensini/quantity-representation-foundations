# Conservation of Quantitative Information under Change of Representation

## Universal carry rigidity of optimal lossless finite quantity codes

**Working manuscript — Lean 4 formalization-backed draft**

**Author:** Thiago Massensini

## Abstract

We prove a representation-rigidity theorem for finite quantitative coding. Fix an integer capacity $b>1$. At depth $k$, consider the complete quantitative window of $b^k$ distinguishable states and let `Codeₖ` be an arbitrary finite code space. No positional syntax, digit alphabet, ordering, quotient, remainder, truncation rule, or carry algorithm is assumed on the code. The only finite-window hypotheses are losslessness—an injective encoding of all $b^k$ quantity states—and an optimal state budget $|Code_k|\le b^k$. Finite cardinality forces equality $|Code_k|=b^k$ and hence bijectivity of the encoding. Therefore every optimal lossless code is a change of coordinates of the canonical cyclic quantity window. Exact unit successor on the code is uniquely determined by conjugation. Its wrap event is equivalent to the carry-through-depth event formalized in Carry Geometry.

We then prove cross-depth rigidity. For every $k\le m$, the unique zero-preserving map from the depth-$m$ canonical cycle to the depth-$k$ cycle that commutes with unit successor is reduction modulo $b^k$. Transporting this result through arbitrary encoders yields a unique code-level projection. These projections are identities at equal depth and compose transitively, so every arbitrary optimal lossless tower is projectively equivalent, as a successor dynamical system, to the canonical residual/carry tower. Any two such towers with the same capacity are therefore projectively equivalent. A specialization to arbitrary finite local cells derives $b$ as the number of available local states. The complete result is formalized and kernel-checked in Lean 4. A complementary constructive branch of the repository independently derives quotient–remainder-like coordinates, carry transport, and canonical digits from explicit operational hypotheses, showing that the rigidity theorem is consistent with a non-circular emergence route.

---

## 1. Introduction

A representation of quantity may change symbols, memory layout, bit patterns, labels, or local coordinates without changing the quantity represented. This elementary observation leads to a structural question:

> **If a complete finite set of distinguishable quantities is represented exactly with no redundant finite states, how much of the quantitative dynamics is actually free to change?**

Ordinary positional notation suggests one answer. In base $b>1$, a depth-$k$ window contains exactly $b^k$ residue states. Unit increment acts cyclically on that window, and the transition from the maximal residue back to zero is the finite shadow of carry through the lowest $k$ places. Between depths, the lower state is obtained by reduction modulo the lower place value.

But these facts are normally presented *inside* a positional system. One begins with digits, powers of a base, quotient and remainder, and then defines carry. The present work asks whether the same dynamics is forced even when the finite code itself has no positional structure at all.

The answer proved here is yes, in a precise optimal-lossless regime.

At depth $k$, let

$$
W_k := \operatorname{Fin}(b^k)
$$

be the complete finite quantity window. Let $C_k$ be any finite code space. Assume only an injective encoding

$$
e_k:W_k\hookrightarrow C_k
$$

and the optimal finite-state budget

$$
|C_k|\le b^k.
$$

Nothing else is assumed about $C_k$.

The first rigidity step is immediate but decisive:

$$
b^k\le |C_k|\le b^k,
$$

hence

$$
|C_k|=b^k
$$

and $e_k$ is bijective. Thus any optimal lossless code is only a coordinate system on the same finite quantity state space.

The rest of the paper asks what this forced bijectivity does to dynamics and hierarchy.

Define canonical unit successor on $W_k$ by

$$
s_k(n)=(n+1)\bmod b^k.
$$

Transporting $s_k$ across $e_k$ gives the only exact successor on $C_k$. Moreover,

$$
s_k(n)=0
\iff
n+1\equiv0\pmod{b^k},
$$

which is exactly the `carryAfterIncrementAtDepth` predicate in the linked Carry Geometry formalization.

The second rigidity step concerns depth. For $k\le m$, consider a map

$$
f:W_m\to W_k
$$

that preserves zero and commutes with unit successor. We prove that necessarily

$$
f(n)=n\bmod b^k.
$$

No alternative zero-preserving successor-equivariant reduction exists. After transport through arbitrary encoders, this forces every coherent code-level map $C_m\to C_k$. The maps satisfy

$$
\pi_{k,k}=\operatorname{id}
$$

and

$$
\pi_{j,k}\circ\pi_{k,m}=\pi_{j,m},
$$

so the entire arbitrary code tower is projectively equivalent to the canonical residual/carry tower.

The main theorem is formalized in Lean as:

```lean
theorem universal_optimal_lossless_representation_collapses_to_carry
    {b : ℕ}
    (tower : LosslessCompressedTower b)
    (hb : 1 < b) :
    UniversalCarryCollapseCertificate tower (lt_trans Nat.zero_lt_one hb)
```

The phrase **collapses to carry** is used in an invariant sense. It does not mean that every code must visibly look like a base-$b$ numeral. It means that after change of coordinates is factored out, no distinct exact finite quantity dynamics or coherent depth hierarchy remains.

### 1.1 Contributions

The paper establishes the following machine-checked results.

1. **Finite-window rigidity.** Any injective encoding of all $b^k$ quantity states into a finite code with at most $b^k$ states is bijective.
2. **Successor rigidity.** Any exact code-level realization of unit increment is uniquely the conjugate of the canonical cyclic successor.
3. **Carry invariance.** The code-level wrap event occurs exactly when increment carries through depth $k$.
4. **All-depth rigidity.** The finite-window result holds simultaneously at every finite depth of an arbitrary opaque code tower.
5. **Cross-depth rigidity.** For $k\le m$, every zero-preserving successor-equivariant map between canonical quantity windows is reduction modulo $b^k$.
6. **Representation-independent projection rigidity.** The same uniqueness holds between arbitrary optimal code spaces after decoding and re-encoding.
7. **Projective laws.** The forced projections are identities at equal depth and compose transitively.
8. **Two-tower equivalence.** Any two optimal lossless towers with the same capacity are equivalent through levelwise coordinate changes preserving successor and all forced projections.
9. **Finite-local specialization.** If a depth-$k$ code consists of $k$ arbitrary cells from a finite local state type `Local`, then $b=|Local|$ and the full theorem follows from faithfulness alone.
10. **Formal verification.** The theorem chain, capstone certificate, and axiom audit are implemented in Lean 4.

A second, complementary formal branch constructs quotient/remainder-like coordinates, carry, hierarchical transport, and canonical digits from explicit operational assumptions without using classical division, modulo, or `Nat.digits` as constructors. We discuss this branch after the universal rigidity theorem.

---

## 2. Formal model of optimal lossless finite representation

### 2.1 Quantity windows

Fix $b>1$. At depth $k$, the complete finite quantity window is

$$
W_k=\operatorname{Fin}(b^k).
$$

We regard $W_k$ only as the set of representatives

$$
0,1,\dots,b^k-1
$$

with the canonical cyclic successor defined later. No digit tuple is required.

### 2.2 Arbitrary code spaces

Let $C_k$ be an arbitrary finite type. The Lean structure is:

```lean
structure LosslessCompressedWindow
    (b k : ℕ) (Code : Type*) [Fintype Code] where
  encode : Fin (b ^ k) → Code
  faithful : Function.Injective encode
  state_budget : Fintype.card Code ≤ b ^ k
```

The word *compressed* is used here in a finite-state cardinal sense: the representation contains no more code states than the number of quantities that must remain distinguishable. This is not a claim about Shannon-optimal variable-length coding.

The assumptions have direct informational meanings.

- `faithful` means no two quantity states are identified;
- `state_budget` means no additional redundant finite states are available.

No operation on `Code` is assumed.

### 2.3 Why arbitrary recodings are included

Suppose an ordinary base-$b$ representation is permuted by an arbitrary bijection, encoded in Gray-like coordinates, renamed by symbols, or stored in a finite data type with no visible arithmetic structure. Such a code still fits the model as long as it is lossless and uses exactly the optimal number of states.

The theorem is designed so that these examples are not counterexamples. They are coordinate changes.

---

## 3. Cardinal rigidity

### Theorem 3.1 — Exact state count

For every `LosslessCompressedWindow`,

$$
|C_k|=b^k.
$$

Lean theorem:

```lean
theorem LosslessCompressedWindow.card_eq_windowSize
```

### Proof

Injectivity of

$$
e_k:W_k\to C_k
$$

implies

$$
|W_k|\le |C_k|.
$$

Since $|W_k|=b^k$,

$$
b^k\le |C_k|.
$$

The state budget gives the reverse inequality. Hence equality holds.

### Corollary 3.2 — Forced bijection

The encoder is bijective:

$$
\boxed{W_k\simeq C_k.}
$$

Lean theorem:

```lean
theorem LosslessCompressedWindow.encode_bijective
```

This is the core information-conservation step. Under optimal losslessness there is no room for either collision or redundant finite state. Every code state carries exactly one quantitative state.

---

## 4. Canonical unit successor and carry

### 4.1 Canonical successor

For $b>0$, define

$$
s_k(n)=(n+1)\bmod b^k.
$$

In Lean:

```lean
def windowSuccessor
    (b k : ℕ) (hb : 0 < b) (n : Fin (b ^ k)) :
    Fin (b ^ k)
```

The distinguished zero state is `windowZero b k hb`.

### 4.2 Carry-through-depth event

The linked Carry Geometry repository defines:

```lean
def carryAfterIncrementAtDepth (b k n : ℕ) : Prop :=
  n + 1 ≡ 0 [MOD placeValue b k]
```

with `placeValue b k = b^k`.

Therefore the finite successor wraps exactly when increment crosses a multiple of $b^k$.

Lean theorem:

```lean
theorem windowSuccessor_eq_zero_iff_carry
```

Mathematically,

$$
\boxed{
s_k(n)=0
\iff
n+1\equiv0\pmod{b^k}
\iff
\operatorname{carryAfterIncrementAtDepth}(b,k,n).
}
$$

Carry is therefore already visible at the level of the canonical finite quantity cycle, without requiring a concrete digit syntax.

---

## 5. Successor rigidity under arbitrary representation

Because $e_k$ is bijective, canonical successor transports to $C_k$:

$$
T_k=e_k\circ s_k\circ e_k^{-1}.
$$

Lean definition:

```lean
noncomputable def LosslessCompressedWindow.codeSuccessor
```

and the intertwining identity is:

```lean
@[simp] theorem LosslessCompressedWindow.codeSuccessor_encode
```

so

$$
T_k(e_k(n))=e_k(s_k(n)).
$$

### Theorem 5.1 — Exact successor is unique

Suppose

$$
U:C_k\to C_k
$$

is any map satisfying

$$
U(e_k(n))=e_k(s_k(n))
$$

for every $n\in W_k$. Then

$$
\boxed{U=T_k.}
$$

Lean theorem:

```lean
theorem LosslessCompressedWindow.codeSuccessor_unique
```

The proof uses surjectivity of $e_k$: every code state is $e_k(n)$ for a unique quantity state.

### Corollary 5.2 — Carry is representation-invariant

For any exact successor implementation,

$$
\boxed{
U(e_k(n))=e_k(0)
\iff
\operatorname{carryAfterIncrementAtDepth}(b,k,n).
}
$$

Lean theorem:

```lean
theorem LosslessCompressedWindow.exact_successor_wrap_iff_carry
```

A recoding may obscure the visual pattern of carry, but it cannot remove or move the quantitative wrap event.

---

## 6. Change of representation

Let $C_k^{(1)}$ and $C_k^{(2)}$ be two arbitrary optimal lossless codes for the same quantity window. Since both encoders are bijective, there is a canonical coordinate change

$$
\Phi_k
=
e_k^{(2)}\circ (e_k^{(1)})^{-1}.
$$

Lean definition:

```lean
noncomputable def LosslessCompressedWindow.changeOfRepresentation
```

It preserves represented quantity:

```lean
@[simp] theorem LosslessCompressedWindow.changeOfRepresentation_encode
```

and conjugates exact successor:

```lean
theorem LosslessCompressedWindow.changeOfRepresentation_conjugates_successor
```

Thus

$$
\boxed{
\Phi_k\circ T_k^{(1)}=T_k^{(2)}\circ\Phi_k.
}
$$

The finite quantitative dynamics is invariant under optimal lossless change of representation.

---

## 7. From one window to all finite depths

An arbitrary optimal lossless tower is:

```lean
structure LosslessCompressedTower (b : ℕ) where
  level : (k : ℕ) → LosslessCompressedLevel b k
```

Each `level k` may use a different opaque code type.

Lean proves at every depth:

```lean
theorem LosslessCompressedTower.level_card_eq

theorem LosslessCompressedTower.level_encode_bijective

theorem LosslessCompressedTower.all_depths_force_carry_conjugacy
```

Hence for all $k$:

$$
|C_k|=b^k,
$$

$$
C_k\simeq W_k,
$$

and exact successor on $C_k$ is conjugate to $s_k$ with wrap exactly on the depth-$k$ carry event.

At this stage every level is rigid, but one question remains: are the maps between levels also forced?

---

## 8. Cross-depth rigidity

### 8.1 Adjacent depths

The canonical projection from depth $k+1$ to depth $k$ is

$$
\rho_{k,k+1}(n)=n\bmod b^k.
$$

Lean definition:

```lean
def canonicalDepthProjection
```

It satisfies:

$$
\rho_{k,k+1}(0)=0
$$

and

$$
\rho_{k,k+1}\circ s_{k+1}=s_k\circ\rho_{k,k+1}.
$$

Lean theorems:

```lean
theorem canonicalDepthProjection_zero

theorem canonicalDepthProjection_commutes_successor
```

### Theorem 8.1 — Adjacent projection uniqueness

Let

$$
f:W_{k+1}\to W_k
$$

satisfy

$$
f(0)=0
$$

and

$$
f(s_{k+1}(n))=s_k(f(n))
$$

for every $n$. Then

$$
\boxed{f=\rho_{k,k+1}.}
$$

Lean theorem:

```lean
theorem canonicalDepthProjection_unique
```

### Proof idea

The depth-$(k+1)$ cycle is generated from zero by repeated successor. Since $f$ fixes zero and commutes with successor, its value at every state is determined inductively. The residual map has the same two properties, hence the two maps agree everywhere.

This argument is structural: no digit truncation rule is assumed.

---

## 9. Arbitrary-depth projective rigidity

For any $k\le m$, define

$$
\rho_{k,m}(n)=n\bmod b^k.
$$

Lean definition:

```lean
def canonicalDepthProjectionLE
```

The same two laws hold:

$$
\rho_{k,m}(0)=0
$$

and

$$
\rho_{k,m}\circ s_m=s_k\circ\rho_{k,m}.
$$

The general rigidity theorem is:

```lean
theorem canonicalDepthProjectionLE_unique
```

which proves:

$$
\boxed{
\text{zero-preserving + successor-equivariant}
\Longrightarrow
f(n)=n\bmod b^k.
}
$$

No alternative quantitative factor map exists between ordered depths.

---

## 10. Projective laws

The canonical depth maps satisfy two laws.

### Identity

```lean
theorem canonicalDepthProjectionLE_refl
```

$$
\boxed{\rho_{k,k}=\operatorname{id}.}
$$

### Composition

For $j\le k\le m$:

```lean
theorem canonicalDepthProjectionLE_comp
```

$$
\boxed{
\rho_{j,k}\circ\rho_{k,m}=\rho_{j,m}.
}
$$

Thus the canonical finite quantity windows form a projective system.

This is the finite-factor structure underlying the usual base-$b$ adding machine / odometer, but here it emerges as the unique coherent hierarchy compatible with the finite quantity successors.

---

## 11. Cross-depth rigidity in opaque code coordinates

Let $C_m$ and $C_k$ be arbitrary optimal lossless code spaces. The forced projection is

$$
P_{k,m}
=
e_k\circ\rho_{k,m}\circ e_m^{-1}.
$$

Lean definition:

```lean
noncomputable def LosslessCompressedWindow.codeDepthProjectionLE
```

It preserves represented zero and commutes with exact successor.

### Theorem 11.1 — Unique code projection

Any

$$
F:C_m\to C_k
$$

that preserves represented zero and commutes with exact successor must satisfy

$$
\boxed{F=P_{k,m}.}
$$

Lean theorem:

```lean
theorem LosslessCompressedWindow.codeDepthProjectionLE_unique
```

Existence and uniqueness are packaged as:

```lean
theorem LosslessCompressedWindow.existsUnique_codeDepthProjectionLE
```

For arbitrary towers, the corresponding objects are:

```lean
LosslessCompressedTower.forcedProjection
LosslessCompressedTower.existsUnique_forcedProjection
LosslessCompressedTower.forcedProjection_refl
LosslessCompressedTower.forcedProjection_comp
LosslessCompressedTower.universal_projective_tower_laws
```

Therefore the arbitrary code tower itself is projective, and its projective structure is uniquely conjugate to residual reduction.

---

## 12. Universal carry-collapse theorem

The full result is collected in:

```lean
structure UniversalCarryCollapseCertificate
    {b : ℕ}
    (tower : LosslessCompressedTower b)
    (hb : 0 < b) : Prop
```

The certificate contains:

- exact level cardinality;
- bijectivity of every level encoding;
- successor conjugacy;
- carry/wrap equivalence;
- uniqueness of every ordered cross-depth projection;
- residual naturality of those projections;
- identity projections;
- projective composition.

### Theorem 12.1 — Universal optimal lossless representation collapses to carry

```lean
theorem universal_optimal_lossless_representation_collapses_to_carry
    {b : ℕ}
    (tower : LosslessCompressedTower b)
    (hb : 1 < b) :
    UniversalCarryCollapseCertificate tower (lt_trans Nat.zero_lt_one hb)
```

Equivalently, for an arbitrary optimal lossless finite quantitative tower:

$$
\boxed{|C_k|=b^k}
$$

for every depth;

$$
\boxed{C_k\simeq W_k}
$$

with exact successor conjugacy;

$$
\boxed{
\text{wrap}_k
\iff
\text{carry through depth }k;
}
$$

and for every $k\le m$,

$$
\boxed{
P_{k,m}=e_k\circ(n\mapsto n\bmod b^k)\circ e_m^{-1}.
}
$$

These maps form a projective system.

This is the precise formal content of the phrase:

> **Optimal lossless finite quantitative representation collapses to the residual/carry dynamics up to change of representation.**

---

## 13. Any two optimal towers are projectively equivalent

The capstone has a direct representation-independence corollary:

```lean
theorem any_two_optimal_lossless_towers_are_projectively_equivalent
```

Let $C_k$ and $D_k$ be two arbitrary optimal lossless towers with the same capacity $b$. For each depth, the canonical change of coordinates

$$
\Phi_k:C_k\simeq D_k
$$

preserves successor:

$$
\Phi_k\circ T_k^C=T_k^D\circ\Phi_k,
$$

and is natural with respect to every forced projection:

$$
\Phi_k\circ P_{k,m}^C
=
P_{k,m}^D\circ\Phi_m.
$$

Thus representation change preserves the complete projective quantitative mechanics.

This theorem is the strongest expression of conservation in the paper: after optimal lossless recoding, the symbols may change, but the quantitative successor and hierarchy do not.

---

## 14. Finite local cells: deriving the capacity parameter

The abstract tower accepts a capacity $b$. A particularly natural specialization derives it from local finite-state capacity.

Let `Local` be any finite type and define

```lean
abbrev LocalWord (Local : Type u) (k : ℕ) := Fin k → Local
```

Then

$$
|\operatorname{LocalWord}(Local,k)|=|Local|^k.
$$

Set

$$
b=|Local|.
$$

If

$$
e_k:\operatorname{Fin}(b^k)\to\operatorname{LocalWord}(Local,k)
$$

is injective, source and target already have equal cardinality, so the encoder is automatically bijective.

Lean theorem:

```lean
theorem universal_finiteLocal_lossless_representation_collapses_to_carry
```

Therefore an arbitrary family of $k$ finite local cells, with no positional semantics built into the cells, inherits the complete carry-collapse certificate.

This gives a concrete formulation of the main principle:

$$
\boxed{
\text{finite local capacity}
+
\text{complete exact quantitative occupancy}
\Longrightarrow
\text{carry projective dynamics up to coordinates}.
}
$$

---

## 15. Complementary constructive route

The universal theorem is a rigidity result: it starts from the complete finite quantity windows $W_k$ and proves that arbitrary optimal lossless codes cannot alter their exact dynamics or hierarchy.

The repository also contains a different formal program whose purpose is constructive rather than classificatory.

That program begins with more primitive representation questions:

```text
faithful distinguishability
→ finite-state obstruction
→ information escape
→ unbounded distinguishing depth
→ explicit unit-step dynamics
→ local recurrence
→ emergent local capacity
→ cycle coordinates
→ emergent quotient and remainder
→ boundary transport
→ carry
→ finite positional expansion
→ intrinsic digit uniqueness
```

Its key feature is non-circularity. The recursive emergent quotient and remainder are constructed before being identified with `Nat.div` and `Nat.mod`; the emergent digit list is constructed before being identified with `Nat.digits`; and the carry bridge is proved only after the boundary dynamics exists independently.

Representative theorems include:

```lean
finiteState_obstructs_faithfulRepresentation
finiteLocal_forces_information_into_extension
faithfulLayeredEncoding_has_arbitrarily_late_information
existsUnique_emergentLocalCapacity
existsUnique_cycleCoordinates
emergentQuotientRemainder_spec
emergent_step_at_boundary_is_oneCarry
emergent_weighted_positional_transport
exists_finite_emergent_positional_expansion
existsUnique_intrinsicCanonicalExpansion
```

The earlier theorem

```lean
existsUnique_foundationalCapstone
```

packages one explicit operational route to positional structure. It remains valid, but it is no longer the strongest theorem in the repository.

The two branches answer different questions:

- **construction:** how can quotient/remainder, carry, and canonical digits be built without assuming them?
- **rigidity:** can an optimal lossless recoding escape the residual/carry projective mechanics?

The universal theorem answers the second question negatively.

---

## 16. Relation to established literature

### 16.1 Numeration and automata

Finite automata and transducers have long been used to study normalization and arithmetic in established numeration systems (Frougny 1992, 1999; Frougny–Sakarovitch 2010). Abstract numeration systems and generalized radix systems broaden the possible representation languages (Lecomte–Rigo 2010; Rigo 2014; Akiyama–Pethő 2002; Akiyama et al. 2004).

These theories normally include a numeration architecture in the input. Our finite code type need not carry such syntax. The theorem is therefore a rigidity result about exact finite quantitative coding rather than a new normalization algorithm for a prescribed system.

### 16.2 Carry propagation

Berthé, Frougny, Rigo, and Sakarovitch (2020) study carry propagation of successor in several classes of numeration systems. Their work assumes representations and studies the extent of digit changes under increment.

Our theorem addresses the invariant event one level earlier: once an optimal lossless code represents the complete finite quantity cycle exactly, the code's wrap event is forced to be the canonical carry-through-depth event under every coordinate system.

### 16.3 Odometers and adding machines

Odometers provide the closest dynamical analogue. Classical constructions use finite cyclic factors, addition by one, and inverse/projective limits with residual connecting maps (Grabner–Liardet–Tichy 1995; Barat–Berthé–Liardet–Thuswaldner 2006).

We do not claim that this dynamical structure is new. The distinction is theorem direction. The classical object is constructed from cyclic factors or a numeration scale. Here the code levels and their syntax are arbitrary; the cyclic factors, exact successor conjugacy, and residual factor maps are proved to be the only possible quantitative structure under the optimal lossless hypotheses.

Thus the result can be read as a finite projective rigidity theorem whose canonical representative is the base-$b$ odometer tower.

### 16.4 Information-lossless coding

Information-lossless finite-state compression provides a natural neighboring vocabulary of recoverability and finite-state information preservation (Dai–Lathrop–Lutz–Mayordomo 2004). That literature studies achievable compression rates for sequences rather than the forced projective mechanics of complete finite quantitative windows.

Our state-budget condition is deliberately finite and exact. It turns recoverability plus optimal cardinality into bijectivity, which then drives the dynamical rigidity.

### 16.5 Periodic enumeration

Manca (2024) derives positional base equations from a periodic monotone enumeration system. This is an important precedent for deriving positional equations from periodic organization. The present theorem differs by assuming no numeral strings or period in the arbitrary code itself; the universal branch is based on finite state-count rigidity and conjugacy, while the complementary constructive branch derives a local capacity before canonical digits are introduced.

### 16.6 Literature claim

The scoped review does not justify an unconditional historical priority claim. The defensible novelty statement is narrower:

> **Among the literature examined, we did not find the same rigidity implication formulated from arbitrary opaque optimal lossless finite code spaces to unique successor conjugacy, carry-wrap invariance, and a forced projective residual hierarchy across all depths.**

---

## 17. Formal verification

All principal claims are formalized in Lean 4.

The universal branch is implemented in:

- `UniversalLosslessCompression.lean`;
- `UniversalLosslessCompressionTower.lean`;
- `UniversalCrossDepthCarryCoherence.lean`;
- `UniversalProjectiveCarryTower.lean`;
- `UniversalCarryCollapseCapstone.lean`.

The repository exports these modules through `QuantityRepresentationFoundations.lean`.

The audit surface is:

```text
QuantityRepresentationFoundations/Audit.lean
```

and includes:

```lean
#print axioms QuantityRepresentationFoundations.universal_optimal_lossless_representation_collapses_to_carry
#print axioms QuantityRepresentationFoundations.universal_finiteLocal_lossless_representation_collapses_to_carry
#print axioms QuantityRepresentationFoundations.any_two_optimal_lossless_towers_are_projectively_equivalent
```

The linked `carry-geometry` dependency is pinned by commit in the Lake manifest, so the carry predicate used by the finite-window theorem is not an informal external reference.

---

## 18. Scope and limitations

The theorem is universal within a precise formal class.

At depth $k$, it assumes:

$$
e_k:W_k\hookrightarrow C_k
$$

and

$$
|C_k|\le |W_k|=b^k.
$$

This is the exact notion of optimal finite-state lossless coding used in the theorem.

Several distinctions matter.

First, a redundant code with $|C_k|>b^k$ may contain non-quantitative degrees of freedom. The theorem does not claim those redundant states disappear.

Second, the theorem concerns complete finite windows. It is not an asymptotic source-coding theorem about probability distributions or variable-length codes.

Third, “carry” is asserted dynamically and invariantly: the finite successor wrap is equivalent to `carryAfterIncrementAtDepth`. A recoded implementation need not display a visually recognizable ripple-carry pattern in its raw symbols.

Fourth, the theorem does not say that all mathematically possible numeration languages are syntactically fixed-radix systems. It says that an optimal lossless code for the complete $b^k$ quantitative windows, organized over all depths, has no different exact successor/projective mechanics after coordinate change.

These restrictions are not weaknesses hidden from the statement. They are the formal meaning of the theorem.

---

## 19. Discussion: conservation under change of representation

The central result can be expressed as a conservation law.

A change of representation may alter the names and arrangement of code states, but if it is exact and uses no redundant finite states, it cannot alter:

- how many quantitative states exist at a given depth;
- the exact unit-successor orbit;
- the location of the quantitative wrap/carry event;
- the unique coherent map from a deeper quantitative window to a shallower one;
- the projective composition law of those maps.

In categorical language, the representation change acts by isomorphism/conjugacy on the finite levels and by natural compatibility on the projective maps. In dynamical language, all optimal lossless representations realize the same adding-machine factors. In positional language, the canonical representative is the residual/carry tower.

This explains the paper's title. The conserved object is not a specific string of digits. It is the quantitative information together with its exact successor and depth-consistency structure.

The slogan is therefore:

$$
\boxed{
\text{change the representation; preserve the quantitative mechanics.}
}
$$

Under optimal finite-state losslessness, those mechanics have a unique canonical representative: the residual/carry tower.

---

## 20. Conclusion

We formalized a universal rigidity theorem for optimal lossless finite representation of quantity.

At each depth, injectivity and the optimal state budget force an arbitrary finite code to have exactly the cardinality of the complete quantitative window, hence to be bijective with it. Exact unit successor is therefore unique up to conjugacy. Its wrap event is exactly the carry-through-depth event. Across depths, preservation of zero and successor forces a unique map: residual reduction modulo the lower capacity. These maps satisfy identity and projective composition laws. Consequently every arbitrary optimal lossless tower is projectively equivalent to the canonical residual/carry tower, and any two such towers are equivalent to one another through representation changes preserving the full quantitative dynamics.

For arbitrary finite local cells, the capacity parameter is simply the number of available local states, so the theorem applies without assigning positional semantics to the cells in advance.

A complementary formal branch constructs emergent quotient/remainder coordinates, carry transport, and canonical positional digits from explicit operational hypotheses, providing a non-circular constructive route to the same familiar arithmetic structures.

The combined picture is stronger than the earlier capstone narrative. Carry is not merely one convenient implementation inside a preselected positional notation. In the optimal lossless finite quantitative regime formalized here, the residual/carry projective dynamics is the representation-invariant structure left after arbitrary coordinate changes are removed.
