# Foundational Capstone — Universal Lossless Compression Collapses to Carry

## Conservation of quantitative information under change of representation

This note records the current theorem-level state of **Quantity Representation Foundations** after the universal carry-collapse program was completed in Lean 4.

The main question is now stated in its strongest formal form:

> **What remains invariant when a finite amount of local representational capacity is used to encode distinguishable quantities exactly, without loss, even if the code syntax is completely arbitrary?**

The answer proved by the repository is:

> **After arbitrary changes of representation are factored out, an optimal lossless finite representation has the canonical residual/carry dynamics, and the hierarchy of finite depths is the canonical projective residual tower.**

The main Lean theorem is:

```lean
theorem universal_optimal_lossless_representation_collapses_to_carry
    {b : ℕ}
    (tower : LosslessCompressedTower b)
    (hb : 1 < b) :
    UniversalCarryCollapseCertificate tower (lt_trans Nat.zero_lt_one hb)
```

Source:

- [`QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean`](QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean)

The key point is that the code spaces in `LosslessCompressedTower` are **opaque**. They are not assumed to be digit strings, positional words, binary strings, ordered tuples, Gray codes, or any other familiar notation.

The conclusion is therefore not that every valid code must *look* positional. The conclusion is stronger and more invariant:

> **Every optimal lossless code carries the same quantitative dynamics and the same cross-depth hierarchy, up to change of coordinates.**

---

## 1. Exact formal scope of “any representation”

At depth `k`, the universal finite-window object is:

```lean
structure LosslessCompressedWindow
    (b k : ℕ) (Code : Type*) [Fintype Code] where
  encode : Fin (b ^ k) → Code
  faithful : Function.Injective encode
  state_budget : Fintype.card Code ≤ b ^ k
```

Source:

- [`QuantityRepresentationFoundations/UniversalLosslessCompression.lean`](QuantityRepresentationFoundations/UniversalLosslessCompression.lean)

This says exactly:

1. there are $b^k$ distinguishable quantity states in the finite window;
2. the representation is lossless, so distinct quantity states remain distinct;
3. the code uses no more than $b^k$ states.

No other structure is assumed on `Code`.

In particular, `Code` need not carry:

- digits;
- a positional order;
- a place-value map;
- quotient or remainder;
- division or modulo;
- a native truncation operation;
- a native carry rule;
- an ordering compatible with quantity;
- any specific bit-level or symbol-level syntax.

This is the precise formal meaning of **arbitrary optimal lossless compression** in the theorem.

The finite local-cell specialization is even more concrete. If `Local` is any finite local state type, define

```lean
abbrev LocalWord (Local : Type u) (k : ℕ) := Fin k → Local
```

Then

$$
|\operatorname{LocalWord}(Local,k)| = |Local|^k.
$$

So if

$$
b := |Local|,
$$

then every faithful encoding

$$
\operatorname{Fin}(b^k) \longrightarrow \operatorname{LocalWord}(Local,k)
$$

is already in the optimal regime automatically: the source and code space have the same finite capacity.

The specialization theorem is:

```lean
theorem universal_finiteLocal_lossless_representation_collapses_to_carry
    {Local : Type u} [Fintype Local]
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local) :
    UniversalCarryCollapseCertificate tower.toCompressedTower
      (lt_trans Nat.zero_lt_one hLocal)
```

Thus, in the finite-local model, the radix/capacity is not separately postulated:

$$
\boxed{b = |Local|.}
$$

---

## 2. The first rigidity theorem: optimal losslessness forces bijectivity

For an arbitrary `LosslessCompressedWindow`, faithfulness gives the lower cardinal bound

$$
b^k \le |Code|.
$$

The compression budget gives

$$
|Code| \le b^k.
$$

Therefore Lean proves:

```lean
theorem card_eq_windowSize
    (rep : LosslessCompressedWindow b k Code) :
    Fintype.card Code = b ^ k
```

Hence the encoder is bijective:

```lean
theorem encode_bijective
    (rep : LosslessCompressedWindow b k Code) :
    Function.Bijective rep.encode
```

So every optimal lossless code is forced to be a change of coordinates of the canonical finite quantity window:

$$
\boxed{Code \simeq \operatorname{Fin}(b^k).}
$$

This already absorbs arbitrary permutations, Gray-like encodings, opaque labels, and other recodings. They can change coordinates, but they cannot create a new finite quantity state space.

---

## 3. The canonical finite quantity dynamics

For $b>0$, the canonical depth-`k` quantity window is

$$
\operatorname{Fin}(b^k).
$$

Its distinguished zero state is:

```lean
def windowZero (b k : ℕ) (hb : 0 < b) : Fin (b ^ k)
```

Its unit successor is:

```lean
def windowSuccessor
    (b k : ℕ) (hb : 0 < b) (n : Fin (b ^ k)) :
    Fin (b ^ k) :=
  ⟨(n.val + 1) % (b ^ k), ...⟩
```

Thus the finite window is a cyclic unit-step system.

The crucial theorem connects the wrap event to Carry Geometry:

```lean
theorem windowSuccessor_eq_zero_iff_carry
```

which proves

$$
\boxed{
S_k(n)=0
\iff
\operatorname{carryAfterIncrementAtDepth}(b,k,n).
}
$$

This theorem is the canonical finite-window bridge to [`carry-geometry`](https://github.com/thiagomassensini/carry-geometry).

---

## 4. Arbitrary code syntax cannot change exact successor dynamics

Because every optimal lossless encoder is bijective, the canonical successor transports to any opaque code space:

```lean
noncomputable def codeSuccessor
    (rep : LosslessCompressedWindow b k Code)
    (hb : 0 < b) : Code → Code
```

The encoding intertwines the two dynamics:

```lean
@[simp] theorem codeSuccessor_encode
```

or mathematically,

$$
\boxed{
S_{Code}(encode(n)) = encode(S_k(n)).
}
$$

The important rigidity theorem is:

```lean
theorem codeSuccessor_unique
```

If any operation

$$
T : Code \to Code
$$

implements exact unit successor on represented quantities, then

$$
\boxed{T = S_{Code}.}
$$

So there is no second exact quantity-successor dynamics hidden inside a different encoding syntax.

The wrap event in every such code is therefore forced:

```lean
theorem exact_successor_wrap_iff_carry
```

and

$$
\boxed{
T(encode(n)) = encode(0)
\iff
\operatorname{carryAfterIncrementAtDepth}(b,k,n).
}
$$

This is the first exact meaning of **collapse to carry up to change of representation**.

---

## 5. Any two optimal lossless codes are the same dynamics in different coordinates

For two arbitrary optimal codes of the same finite quantity window, the repository defines

```lean
noncomputable def changeOfRepresentation
```

and proves:

```lean
@[simp] theorem changeOfRepresentation_encode
```

and

```lean
theorem changeOfRepresentation_conjugates_successor
```

Thus, if `Code₁` and `Code₂` are two arbitrary optimal lossless representations of the same $b^k$ quantity states, then

$$
Code_1 \simeq Code_2
$$

through a change of coordinates that preserves represented quantity and conjugates exact successor.

So a Gray-like recoding, a permutation of labels, or an opaque symbolic code is not a counterexample. It is another coordinate system on the same finite quantitative dynamical system.

---

## 6. All depths simultaneously

The project next packages one arbitrary optimal lossless representation at every finite depth:

```lean
structure LosslessCompressedTower (b : ℕ) where
  level : (k : ℕ) → LosslessCompressedLevel b k
```

Source:

- [`QuantityRepresentationFoundations/UniversalLosslessCompressionTower.lean`](QuantityRepresentationFoundations/UniversalLosslessCompressionTower.lean)

At every depth Lean proves exact cardinality and bijectivity:

```lean
theorem LosslessCompressedTower.level_card_eq

theorem LosslessCompressedTower.level_encode_bijective
```

and simultaneously proves carry conjugacy at all finite depths:

```lean
theorem LosslessCompressedTower.all_depths_force_carry_conjugacy
```

For the finite-local specialization:

```lean
theorem LosslessFiniteLocalWordTower.all_depths_force_carry
```

Thus the finite-window theorem is not an isolated phenomenon. Every finite depth of the same lossless compression tower is forced into the same canonical quantity dynamics up to coordinates.

---

## 7. The missing global question: how are depths connected?

Levelwise equivalence alone is not enough for a hierarchical representation theorem.

One could still ask whether the map from depth `k+1` to depth `k` contains an additional arbitrary choice.

The repository therefore proves **cross-depth rigidity**.

Source:

- [`QuantityRepresentationFoundations/UniversalCrossDepthCarryCoherence.lean`](QuantityRepresentationFoundations/UniversalCrossDepthCarryCoherence.lean)

The canonical adjacent-depth projection is

$$
\pi_{k,k+1}(n) = n \bmod b^k.
$$

In Lean:

```lean
def canonicalDepthProjection
    (b k : ℕ) (hb : 0 < b) :
    Fin (b ^ (k + 1)) → Fin (b ^ k)
```

It preserves zero and commutes with unit successor:

```lean
theorem canonicalDepthProjection_zero

theorem canonicalDepthProjection_commutes_successor
```

The rigidity theorem is:

```lean
theorem canonicalDepthProjection_unique
```

If

$$
f : \operatorname{Fin}(b^{k+1}) \to \operatorname{Fin}(b^k)
$$

satisfies

$$
f(0)=0
$$

and

$$
f(S_{k+1}(n)) = S_k(f(n)),
$$

then

$$
\boxed{f(n)=n\bmod b^k.}
$$

So even the relation between adjacent scales is forced by quantity semantics.

---

## 8. Cross-depth rigidity survives arbitrary code coordinates

For arbitrary opaque code spaces at depths `k+1` and `k`, define the forced map by:

$$
Code_{k+1}
\xrightarrow{decode}
\operatorname{Fin}(b^{k+1})
\xrightarrow{\bmod b^k}
\operatorname{Fin}(b^k)
\xrightarrow{encode}
Code_k.
$$

Lean definition:

```lean
noncomputable def LosslessCompressedWindow.codeDepthProjection
```

The theorem

```lean
theorem LosslessCompressedWindow.codeDepthProjection_unique
```

proves that every code-level map preserving represented zero and commuting with exact successor is exactly this forced map.

Equivalently:

```lean
theorem LosslessCompressedWindow.existsUnique_codeDepthProjection
```

There is exactly one successor-coherent adjacent-depth projection.

For an arbitrary tower:

```lean
theorem LosslessCompressedTower.existsUnique_forcedAdjacentProjection
```

For arbitrary finite local-cell syntax:

```lean
theorem LosslessFiniteLocalWordTower.all_adjacent_depth_projections_are_forced
```

Thus the hierarchy cannot be modified independently of the finite-level dynamics.

---

## 9. The full projective tower

Adjacent-depth rigidity is then promoted to every ordered pair of depths.

Source:

- [`QuantityRepresentationFoundations/UniversalProjectiveCarryTower.lean`](QuantityRepresentationFoundations/UniversalProjectiveCarryTower.lean)

For $k\le m$, define

```lean
def canonicalDepthProjectionLE
    (b k m : ℕ) (hb : 0 < b) :
    Fin (b ^ m) → Fin (b ^ k)
```

by

$$
\boxed{\pi_{k,m}(n)=n\bmod b^k.}
$$

The canonical projections preserve zero and commute with successor:

```lean
theorem canonicalDepthProjectionLE_zero

theorem canonicalDepthProjectionLE_commutes_successor
```

They are unique:

```lean
theorem canonicalDepthProjectionLE_unique
```

So for every $k\le m$, any zero-preserving successor-equivariant map

$$
\operatorname{Fin}(b^m) \to \operatorname{Fin}(b^k)
$$

is forced to be reduction modulo $b^k$.

The projective laws are then proved directly.

### Identity

```lean
theorem canonicalDepthProjectionLE_refl
```

$$
\boxed{\pi_{k,k}=\operatorname{id}.}
$$

### Composition

```lean
theorem canonicalDepthProjectionLE_comp
```

For $j\le k\le m$,

$$
\boxed{
\pi_{j,k}\circ\pi_{k,m}=\pi_{j,m}.
}
$$

This is not inserted as a definition. The direct residual maps are defined first and then proved to satisfy the projective law.

---

## 10. The projective laws in arbitrary representations

For an arbitrary `LosslessCompressedTower`, Lean defines

```lean
noncomputable def LosslessCompressedTower.forcedProjection
```

between every ordered pair of depths and proves:

```lean
theorem LosslessCompressedTower.existsUnique_forcedProjection
```

Every coherent projection is unique.

On represented quantities it is exactly the residual map:

```lean
@[simp] theorem LosslessCompressedTower.forcedProjection_encode
```

Equal-depth projection is identity:

```lean
theorem LosslessCompressedTower.forcedProjection_refl
```

and projections compose transitively:

```lean
theorem LosslessCompressedTower.forcedProjection_comp
```

These laws are packaged by:

```lean
theorem LosslessCompressedTower.universal_projective_tower_laws
```

For finite local-cell representations, the corresponding capstone is:

```lean
theorem LosslessFiniteLocalWordTower.universal_finiteLocal_projective_carry_tower
```

Hence an arbitrary optimal lossless finite-local tower is not merely levelwise equivalent to carry. It is equivalent as a **projective successor dynamical system**.

---

## 11. The universal carry-collapse certificate

All of the preceding rigidity results are packaged in one proposition:

```lean
structure UniversalCarryCollapseCertificate
    {b : ℕ}
    (tower : LosslessCompressedTower b)
    (hb : 0 < b) : Prop where
  level_cardinality : ...
  level_bijective : ...
  successor_conjugacy : ...
  carry_wrap : ...
  projection_unique : ...
  projection_naturality : ...
  projection_refl : ...
  projection_comp : ...
```

Source:

- [`QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean`](QuantityRepresentationFoundations/UniversalCarryCollapseCapstone.lean)

The certificate records eight simultaneous facts:

1. every code level has exactly $b^k$ states;
2. every encoder is bijective;
3. exact successor is conjugate to the canonical cyclic successor;
4. wrap occurs exactly on the carry event;
5. every cross-depth quantitative projection is unique;
6. every such projection is modulo reduction after decode/encode;
7. equal-depth projection is identity;
8. projections compose transitively.

The main theorem is:

```lean
theorem universal_optimal_lossless_representation_collapses_to_carry
    {b : ℕ}
    (tower : LosslessCompressedTower b)
    (hb : 1 < b) :
    UniversalCarryCollapseCertificate tower (lt_trans Nat.zero_lt_one hb)
```

This is the current foundational capstone.

---

## 12. What “collapse to carry” means mathematically

The phrase **collapse to carry** does not mean that all valid code strings must visibly resemble ordinary base-$b$ numerals.

It means that once coordinate syntax is factored out, there is no second optimal lossless finite quantitative dynamics and no second coherent finite-depth hierarchy.

At each level:

$$
\boxed{Code_k \simeq \operatorname{Fin}(b^k).}
$$

Under this equivalence:

$$
\boxed{S_{Code_k} \sim S_k.}
$$

The distinguished wrap event is:

$$
\boxed{
S_k(n)=0
\iff
\operatorname{carryAfterIncrementAtDepth}(b,k,n).
}
$$

Between depths:

$$
\boxed{
\pi_{k,m}(n)=n\bmod b^k.
}
$$

And the full family satisfies:

$$
\boxed{
\pi_{k,k}=\operatorname{id},
\qquad
\pi_{j,k}\circ\pi_{k,m}=\pi_{j,m}.
}
$$

Therefore the invariant object is not a particular numeral spelling. It is the residual/carry projective dynamical system.

---

## 13. Any two optimal lossless towers are projectively equivalent

The repository proves the direct comparison theorem:

```lean
theorem any_two_optimal_lossless_towers_are_projectively_equivalent
```

For two arbitrary optimal lossless towers `left` and `right` with the same capacity $b>1$, the levelwise change of representation preserves:

- exact unit successor;
- every forced projection between depths.

So if two codes represent the same finite quantitative capacities exactly, they may differ syntactically, but they cannot define inequivalent quantitative mechanics.

This is the precise theorem that absorbs arbitrary recodings.

---

## 14. The finite-local interpretation

Let `Local` be any finite local state type with

$$
1 < |Local|.
$$

At depth `k`, use `k` arbitrary local cells:

$$
Code_k = \operatorname{Fin}(k) \to Local.
$$

Then

$$
|Code_k| = |Local|^k.
$$

Writing

$$
b = |Local|,
$$

any faithful encoding of the $b^k$ quantity states into those `k` local cells is automatically bijective.

The theorem

```lean
theorem universal_finiteLocal_lossless_representation_collapses_to_carry
```

therefore proves the complete carry-collapse certificate without separately assuming a positional alphabet interpretation.

This is the cleanest formal realization of the statement:

> **Finite local capacity + exact lossless compression of quantitative states forces the carry projective dynamics, up to representation equivalence.**

---

## 15. Relationship to the earlier emergent-construction program

The repository contains an earlier and complementary chain that begins much farther upstream from explicit structural principles and constructs quotient/remainder-like coordinates before identifying them with classical arithmetic.

That route remains formally valid and conceptually important.

Its main stages are:

```text
faithful distinguishability
        ↓
finite-state obstruction
        ↓
information escape from finite local state
        ↓
no fixed finite finite-layer depth suffices
        ↓
arbitrarily deep distinguishing information
        ↓
first distinguishing depth
        ↓
explicit unit-step dynamics
        ↓
finite local recurrence
        ↓
least positive local return
        ↓
emergent capacity
        ↓
cycle count + residual position
        ↓
emergent quotient and remainder
        ↓
boundary reset + one transported unit
        ↓
carry
        ↓
weighted hierarchical transport
        ↓
finite positional expansion
        ↓
intrinsic uniqueness of canonical digits
```

Representative theorems include:

- `finiteState_obstructs_faithfulRepresentation`;
- `finiteLocal_forces_information_into_extension`;
- `faithfulLayeredEncoding_has_arbitrarily_late_information`;
- `existsUnique_firstDistinguishingDepth`;
- `unitTrajectory_forces_localRecurrence`;
- `existsUnique_emergentLocalCapacity`;
- `existsUnique_cycleCoordinates`;
- `emergentQuotientRemainder_spec`;
- `emergent_step_at_boundary`;
- `emergent_step_at_boundary_is_oneCarry`;
- `emergent_weighted_positional_transport`;
- `exists_finite_emergent_positional_expansion`;
- `existsUnique_intrinsicCanonicalExpansion`;
- `existsUnique_foundationalCapstone`.

The earlier capstone uses explicit operational hypotheses such as `UnitTrajectory` and `AutonomousLocalDynamics`. It explains one route by which a nontrivial local capacity and positional structure can **emerge constructively**.

The new universal carry-collapse branch answers a different and stronger invariance question:

> Once a finite quantitative window is represented optimally and without loss, can arbitrary code syntax or arbitrary cross-depth wiring produce a genuinely different quantitative dynamics?

The answer formalized by PRs #19–#23 is **no**.

So the two branches play different roles:

- the **emergent branch** explains how familiar arithmetic coordinates can be constructed without postulating them;
- the **universal rigidity branch** proves that optimal lossless recodings do not create a different quantitative mechanics.

---

## 16. Downstream classical crosswalks remain non-circular

The emergent branch constructs

$$
Q_b(n), \qquad R_b(n)
$$

before identifying them with

$$
\frac{n}{b}, \qquad n\bmod b.
$$

The crosswalk theorems are:

```lean
theorem emergentQuotient_eq_div

theorem emergentRemainder_eq_mod
```

Likewise the emergent digit representation is constructed before the theorem

```lean
theorem emergentDigits_eq_natDigits
```

identifies it with `Nat.digits`.

The universal rigidity branch, by contrast, studies finite quantitative windows directly and proves uniqueness up to representation equivalence.

These are complementary logical routes, not circular definitions.

---

## 17. Connection to Carry Geometry

The project depends explicitly on [`carry-geometry`](https://github.com/thiagomassensini/carry-geometry).

Two distinct bridges are now present.

### 17.1 Emergent normalization bridge

The earlier constructive route proves:

```lean
theorem emergentCoordinates_are_carryGeometryNormalization

theorem emergentRemainder_eq_normalizedDigit

theorem emergentQuotient_eq_carryUnits
```

Thus its independently constructed cycle coordinates coincide with Carry Geometry normalization.

### 17.2 Universal dynamic bridge

The universal route uses:

```lean
theorem windowSuccessor_eq_zero_iff_carry
```

which identifies the canonical finite-window wrap event with:

```lean
CarryGeometry.carryAfterIncrementAtDepth
```

Since all exact optimal lossless codes are conjugate to that finite-window dynamics, the carry event is representation-invariant up to coordinates.

---

## 18. Precise scope and non-claims

The universal theorem is strong, but its formal domain should be stated exactly.

It proves universality for **optimal lossless finite quantitative compression towers** modeled by `LosslessCompressedTower`.

At depth `k`, this means:

$$
\operatorname{Fin}(b^k) \hookrightarrow Code_k,
\qquad
|Code_k|\le b^k.
$$

This is not a theorem about every object that might informally be called a representation without specifying what information it preserves or what “compressed” means.

In particular, the theorem does not identify all physical storage architectures, all variable-length codes, or all redundant error-correcting codes with a literal digit syntax.

What it does prove is the exact invariant statement relevant here:

> **Within optimal finite lossless representation of the complete $b^k$ quantitative window, arbitrary recoding cannot alter the successor dynamics, carry event, or projective hierarchy.**

If redundancy is allowed, then `state_budget ≤ b^k` no longer holds, and additional non-quantitative degrees of freedom may exist in the code space. Those degrees of freedom are outside the optimal-compression theorem precisely because they are redundant relative to the represented quantitative window.

---

## 19. The theorem-level map

| Mathematical role | Lean theorem / definition | Module |
|---|---|---|
| Arbitrary optimal finite code | `LosslessCompressedWindow` | `UniversalLosslessCompression.lean` |
| Forced exact cardinality | `card_eq_windowSize` | `UniversalLosslessCompression.lean` |
| Forced bijectivity | `encode_bijective` | `UniversalLosslessCompression.lean` |
| Canonical finite successor | `windowSuccessor` | `UniversalLosslessCompression.lean` |
| Wrap iff carry | `windowSuccessor_eq_zero_iff_carry` | `UniversalLosslessCompression.lean` |
| Unique exact code successor | `codeSuccessor_unique` | `UniversalLosslessCompression.lean` |
| Exact successor wrap iff carry | `exact_successor_wrap_iff_carry` | `UniversalLosslessCompression.lean` |
| Change of representation | `changeOfRepresentation` | `UniversalLosslessCompression.lean` |
| Successor conjugacy | `changeOfRepresentation_conjugates_successor` | `UniversalLosslessCompression.lean` |
| Arbitrary tower | `LosslessCompressedTower` | `UniversalLosslessCompressionTower.lean` |
| All-depth carry conjugacy | `all_depths_force_carry_conjugacy` | `UniversalLosslessCompressionTower.lean` |
| Arbitrary local-cell code | `LocalWord` | `UniversalLosslessCompressionTower.lean` |
| Finite-local all-depth theorem | `LosslessFiniteLocalWordTower.all_depths_force_carry` | `UniversalLosslessCompressionTower.lean` |
| Adjacent residual projection | `canonicalDepthProjection` | `UniversalCrossDepthCarryCoherence.lean` |
| Adjacent projection uniqueness | `canonicalDepthProjection_unique` | `UniversalCrossDepthCarryCoherence.lean` |
| Arbitrary-code adjacent uniqueness | `codeDepthProjection_unique` | `UniversalCrossDepthCarryCoherence.lean` |
| General residual projection | `canonicalDepthProjectionLE` | `UniversalProjectiveCarryTower.lean` |
| General projection uniqueness | `canonicalDepthProjectionLE_unique` | `UniversalProjectiveCarryTower.lean` |
| Projective identity | `canonicalDepthProjectionLE_refl` | `UniversalProjectiveCarryTower.lean` |
| Projective composition | `canonicalDepthProjectionLE_comp` | `UniversalProjectiveCarryTower.lean` |
| Arbitrary tower projection | `LosslessCompressedTower.forcedProjection` | `UniversalProjectiveCarryTower.lean` |
| Unique arbitrary tower projection | `LosslessCompressedTower.existsUnique_forcedProjection` | `UniversalProjectiveCarryTower.lean` |
| Tower projective laws | `LosslessCompressedTower.universal_projective_tower_laws` | `UniversalProjectiveCarryTower.lean` |
| Complete certificate | `UniversalCarryCollapseCertificate` | `UniversalCarryCollapseCapstone.lean` |
| Main universal theorem | `universal_optimal_lossless_representation_collapses_to_carry` | `UniversalCarryCollapseCapstone.lean` |
| Finite-local capstone | `universal_finiteLocal_lossless_representation_collapses_to_carry` | `UniversalCarryCollapseCapstone.lean` |
| Two-tower equivalence | `any_two_optimal_lossless_towers_are_projectively_equivalent` | `UniversalCarryCollapseCapstone.lean` |

---

## 20. Kernel audit

The public audit surface is:

- [`QuantityRepresentationFoundations/Audit.lean`](QuantityRepresentationFoundations/Audit.lean)

The universal capstone theorems are included in the `#print axioms` surface together with the earlier constructive chain.

The relevant final entries include:

```lean
#print axioms QuantityRepresentationFoundations.universal_optimal_lossless_representation_collapses_to_carry
#print axioms QuantityRepresentationFoundations.universal_finiteLocal_lossless_representation_collapses_to_carry
#print axioms QuantityRepresentationFoundations.any_two_optimal_lossless_towers_are_projectively_equivalent
```

---

## 21. Final mathematical statement

The current formal result can be summarized as follows.

Let $b>1$. At every finite depth $k$, suppose the complete set of $b^k$ distinguishable quantitative states is encoded faithfully into an arbitrary finite code space with no more than $b^k$ states. Suppose these finite levels are considered together as a depth-indexed tower.

Then Lean proves:

$$
\boxed{|Code_k|=b^k}
$$

and every encoding is a bijection;

$$
\boxed{Code_k \simeq \operatorname{Fin}(b^k)}
$$

with exact unit successor conjugate to the canonical cyclic successor;

$$
\boxed{
\text{wrap at depth }k
\iff
\text{carry through depth }k;
}
$$

for every $k\le m$, there is exactly one coherent quantitative projection

$$
\boxed{\pi_{k,m}:Code_m\to Code_k}
$$

and, after changing coordinates,

$$
\boxed{\pi_{k,m}(n)=n\bmod b^k;}
$$

finally,

$$
\boxed{
\pi_{k,k}=\operatorname{id},
\qquad
\pi_{j,k}\circ\pi_{k,m}=\pi_{j,m}.
}
$$

Therefore:

$$
\boxed{
\textbf{optimal lossless finite quantitative representation}
\Longrightarrow
\textbf{the canonical residual/carry projective dynamics, up to change of representation.}
}
$$

For a representation built from `k` arbitrary finite local cells, the capacity parameter is simply

$$
\boxed{b=|Local|.}
$$

This is the current foundational capstone of the repository.
