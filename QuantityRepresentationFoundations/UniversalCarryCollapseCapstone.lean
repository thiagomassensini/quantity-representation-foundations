import QuantityRepresentationFoundations.UniversalProjectiveCarryTower

/-!
# Universal carry-collapse capstone

This module packages the universal finite-compression results into a single
kernel-facing statement.

A `LosslessCompressedTower b` imposes no numeral syntax on its code spaces.
At depth `k`, the code type may be completely opaque.  The only representation
requirements are already carried by `LosslessCompressedWindow`:

* `b^k` distinguishable quantitative states are encoded faithfully;
* the code type has at most `b^k` states.

Previous modules prove that this forces exact cardinality and bijectivity at
each level, exact unit-successor dynamics up to conjugacy, carry as the wrap
event, and unique residual projections between every ordered pair of depths.
Those projections form a projective system.

The certificate below records all of these facts together.  In this precise
sense an arbitrary optimal lossless compressed quantity tower *collapses to
carry up to change of representation*: there is no distinct finite dynamics or
hierarchy left after coordinate changes are factored out.
-/

namespace QuantityRepresentationFoundations

open LosslessCompressedWindow

universe u

/--
Complete certificate that an arbitrary optimal lossless compressed tower is the
canonical residual/carry tower up to levelwise change of coordinates.
-/
structure UniversalCarryCollapseCertificate
    {b : ℕ}
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) : Prop where
  /-- Every compressed level uses exactly the available quantitative capacity. -/
  level_cardinality : ∀ k : ℕ,
    Fintype.card (tower.level k).Code = b ^ k
  /-- Every level encoding is therefore a bijection. -/
  level_bijective : ∀ k : ℕ,
    Function.Bijective (tower.level k).rep.encode
  /-- Exact successor is conjugate to canonical cyclic unit successor. -/
  successor_conjugacy : ∀ (k : ℕ) (n : Fin (b ^ k)),
    (tower.level k).rep.codeSuccessor hb
        ((tower.level k).rep.windowEquiv n) =
      (tower.level k).rep.windowEquiv
        (windowSuccessor b k hb n)
  /-- The code-level wrap event is exactly the carry event. -/
  carry_wrap : ∀ (k : ℕ) (n : Fin (b ^ k)),
    (tower.level k).rep.codeSuccessor hb
        ((tower.level k).rep.encode n) =
          (tower.level k).rep.encode (windowZero b k hb) ↔
      CarryGeometry.carryAfterIncrementAtDepth b k n.val
  /-- Every ordered pair of depths has one unique coherent quantitative map. -/
  projection_unique : ∀ (k m : ℕ) (hkm : k ≤ m),
    ∃! f : (tower.level m).Code → (tower.level k).Code,
      f ((tower.level m).rep.encode (windowZero b m hb)) =
          (tower.level k).rep.encode (windowZero b k hb) ∧
      ∀ c : (tower.level m).Code,
        f ((tower.level m).rep.codeSuccessor hb c) =
          (tower.level k).rep.codeSuccessor hb (f c)
  /-- Under the forced level equivalences, every projection is modulo `b^k`. -/
  projection_naturality : ∀ (k m : ℕ) (hkm : k ≤ m)
      (n : Fin (b ^ m)),
    tower.forcedProjection hb hkm
        ((tower.level m).rep.windowEquiv n) =
      (tower.level k).rep.windowEquiv
        (canonicalDepthProjectionLE b k m hb n)
  /-- Equal-depth projection is identity. -/
  projection_refl : ∀ k : ℕ,
    tower.forcedProjection hb (show k ≤ k from le_rfl) = id
  /-- Forced projections compose transitively. -/
  projection_comp : ∀ (j k m : ℕ) (hjk : j ≤ k) (hkm : k ≤ m)
      (c : (tower.level m).Code),
    tower.forcedProjection hb hjk
        (tower.forcedProjection hb hkm c) =
      tower.forcedProjection hb (le_trans hjk hkm) c

/--
Universal carry-collapse theorem for arbitrary opaque optimal lossless codes.

No positional syntax is assumed for the code types.  Once losslessness and the
finite optimal capacity budget are imposed at every depth, the entire tower is
projectively carry-equivalent.
-/
theorem universal_optimal_lossless_representation_collapses_to_carry
    {b : ℕ}
    (tower : LosslessCompressedTower.{u} b)
    (hb : 1 < b) :
    UniversalCarryCollapseCertificate tower (lt_trans Nat.zero_lt_one hb) := by
  let hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hlevels := tower.all_depths_force_carry_conjugacy hb0
  have hprojective := tower.universal_projective_tower_laws hb0
  refine
    { level_cardinality := ?_
      level_bijective := ?_
      successor_conjugacy := ?_
      carry_wrap := ?_
      projection_unique := ?_
      projection_naturality := ?_
      projection_refl := hprojective.1
      projection_comp := hprojective.2 }
  · intro k
    exact (hlevels k).1
  · intro k
    exact (hlevels k).2.1
  · intro k n
    change (tower.level k).rep.codeSuccessor hb0
        ((tower.level k).rep.encode n) =
      (tower.level k).rep.encode (windowSuccessor b k hb0 n)
    exact (tower.level k).rep.codeSuccessor_encode hb0 n
  · intro k n
    exact (hlevels k).2.2 n
  · intro k m hkm
    exact tower.existsUnique_forcedProjection hb0 hkm
  · intro k m hkm n
    change tower.forcedProjection hb0 hkm
        ((tower.level m).rep.encode n) =
      (tower.level k).rep.encode
        (canonicalDepthProjectionLE b k m hb0 n)
    exact tower.forcedProjection_encode hb0 hkm n

/--
Specialization to a representation made of arbitrary finite local cells.
Here the radix/capacity parameter is not supplied independently: it is exactly
`Fintype.card Local`.
-/
theorem universal_finiteLocal_lossless_representation_collapses_to_carry
    {Local : Type u} [Fintype Local]
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local) :
    UniversalCarryCollapseCertificate tower.toCompressedTower
      (lt_trans Nat.zero_lt_one hLocal) := by
  exact universal_optimal_lossless_representation_collapses_to_carry
    tower.toCompressedTower hLocal

/--
Direct corollary: any two arbitrary optimal lossless towers with the same finite
capacity are levelwise equivalent in a way that preserves both successor and
all forced projections.
-/
theorem any_two_optimal_lossless_towers_are_projectively_equivalent
    {b : ℕ}
    (left right : LosslessCompressedTower.{u} b)
    (hb : 1 < b) :
    (∀ (k : ℕ) (n : Fin (b ^ k)),
      left.levelChange right k
          ((left.level k).rep.codeSuccessor
            (lt_trans Nat.zero_lt_one hb) ((left.level k).rep.encode n)) =
        (right.level k).rep.codeSuccessor
          (lt_trans Nat.zero_lt_one hb)
          (left.levelChange right k ((left.level k).rep.encode n))) ∧
    (∀ (k m : ℕ) (hkm : k ≤ m) (n : Fin (b ^ m)),
      left.levelChange right k
          (left.forcedProjection (lt_trans Nat.zero_lt_one hb) hkm
            ((left.level m).rep.encode n)) =
        right.forcedProjection (lt_trans Nat.zero_lt_one hb) hkm
          (left.levelChange right m ((left.level m).rep.encode n))) := by
  constructor
  · intro k n
    exact left.levelChange_conjugates_successor right
      (lt_trans Nat.zero_lt_one hb) k ((left.level k).rep.encode n)
  · intro k m hkm n
    rw [left.forcedProjection_encode]
    rw [left.levelChange_encode]
    rw [left.levelChange_encode]
    rw [right.forcedProjection_encode]

end QuantityRepresentationFoundations
