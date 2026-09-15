import QuantityRepresentationFoundations.UniversalLosslessCompression

/-!
# Universal finite-local compression at every depth

The finite-window theorem allows a completely opaque code type with an explicit
state budget.  This module specializes and globalizes that result to the most
direct model of finite local compression.

Let `Local` be an arbitrary finite local alphabet/state type.  A depth-`k` code
is simply a function

`Fin k → Local`.

No positional weight, digit order, quotient, remainder, or carry rule is built
into this type.  It is only a block of `k` finite local cells.  If
`b = Fintype.card Local`, then the code space has exactly `b^k` states.
Consequently every injective encoding of the `b^k` distinguishable quantity
states into those `k` cells is automatically bijective and therefore conjugate
to the canonical depth-`k` quantity dynamics.

A family of such encoders over all depths is called a
`LosslessFiniteLocalWordTower`.  At every finite depth, any exact implementation
of unit successor is forced to be the transported successor and its wrap event
is exactly the carry event of `carry-geometry`.
-/

namespace QuantityRepresentationFoundations

universe u v

/-- An opaque optimal compressed level with its finite code type packaged. -/
structure LosslessCompressedLevel (b k : ℕ) where
  Code : Type u
  codeFintype : Fintype Code
  rep : @LosslessCompressedWindow b k Code codeFintype

namespace LosslessCompressedLevel

instance {b k : ℕ} (level : LosslessCompressedLevel.{u} b k) :
    Fintype level.Code :=
  level.codeFintype

end LosslessCompressedLevel

/-- A family of optimal lossless compressed windows at every depth. -/
structure LosslessCompressedTower (b : ℕ) where
  level : (k : ℕ) → LosslessCompressedLevel.{u} b k

namespace LosslessCompressedTower

variable {b : ℕ}

/-- Every level of an optimal lossless tower has the forced window cardinality. -/
theorem level_card_eq
    (tower : LosslessCompressedTower.{u} b) (k : ℕ) :
    Fintype.card (tower.level k).Code = b ^ k :=
  (tower.level k).rep.card_eq_windowSize

/-- Every level encoder is bijective. -/
theorem level_encode_bijective
    (tower : LosslessCompressedTower.{u} b) (k : ℕ) :
    Function.Bijective (tower.level k).rep.encode :=
  (tower.level k).rep.encode_bijective

/-- Carry conjugacy holds simultaneously at every depth of the tower. -/
theorem all_depths_force_carry_conjugacy
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) :
    ∀ k : ℕ,
      Fintype.card (tower.level k).Code = b ^ k ∧
        Function.Bijective (tower.level k).rep.encode ∧
        ∀ n : Fin (b ^ k),
          (tower.level k).rep.codeSuccessor hb
              ((tower.level k).rep.encode n) =
                (tower.level k).rep.encode
                  (LosslessCompressedWindow.windowZero b k hb) ↔
            CarryGeometry.carryAfterIncrementAtDepth b k n.val := by
  intro k
  exact (tower.level k).rep.universal_lossless_compression_forces_carry_conjugacy hb

/-- Levelwise change of representation between two arbitrary optimal towers. -/
noncomputable def levelChange
    (left : LosslessCompressedTower.{u} b)
    (right : LosslessCompressedTower.{v} b)
    (k : ℕ) :
    (left.level k).Code ≃ (right.level k).Code :=
  (left.level k).rep.changeOfRepresentation (right.level k).rep

/-- Every levelwise change of representation preserves the encoded quantity. -/
@[simp] theorem levelChange_encode
    (left : LosslessCompressedTower.{u} b)
    (right : LosslessCompressedTower.{v} b)
    (k : ℕ) (n : Fin (b ^ k)) :
    left.levelChange right k ((left.level k).rep.encode n) =
      (right.level k).rep.encode n :=
  (left.level k).rep.changeOfRepresentation_encode (right.level k).rep n

/-- Every levelwise change of representation conjugates exact unit successor. -/
theorem levelChange_conjugates_successor
    (left : LosslessCompressedTower.{u} b)
    (right : LosslessCompressedTower.{v} b)
    (hb : 0 < b) (k : ℕ) (c : (left.level k).Code) :
    left.levelChange right k ((left.level k).rep.codeSuccessor hb c) =
      (right.level k).rep.codeSuccessor hb (left.levelChange right k c) :=
  (left.level k).rep.changeOfRepresentation_conjugates_successor
    (right.level k).rep hb c

end LosslessCompressedTower

/-- A depth-`k` block of completely generic finite local states. -/
abbrev LocalWord (Local : Type u) (k : ℕ) := Fin k → Local

namespace LocalWord

variable {Local : Type u} [Fintype Local]

/-- `k` cells from a `b`-state local alphabet have exactly `b^k` states. -/
@[simp] theorem card (k : ℕ) :
    Fintype.card (LocalWord Local k) = (Fintype.card Local) ^ k := by
  simp [LocalWord]

/--
Any faithful encoding into exactly `k` finite local cells is an instance of the
abstract optimal-window theorem.  No separate compression-budget assumption is
needed because the code cardinality is exactly the product capacity.
-/
def asLosslessCompressedWindow
    (k : ℕ)
    (encode : Fin ((Fintype.card Local) ^ k) → LocalWord Local k)
    (faithful : Function.Injective encode) :
    LosslessCompressedWindow (Fintype.card Local) k (LocalWord Local k) where
  encode := encode
  faithful := faithful
  state_budget := by
    simp

/--
Universal finite-local compression theorem for one depth.

An arbitrary faithful representation into `k` cells of a finite local alphabet
is automatically a bijection, and its exact unit-successor wrap event is carry
up to the forced change of coordinates.
-/
theorem any_lossless_kCell_code_forces_carry
    (k : ℕ)
    (hLocal : 0 < Fintype.card Local)
    (encode : Fin ((Fintype.card Local) ^ k) → LocalWord Local k)
    (faithful : Function.Injective encode) :
    Function.Bijective encode ∧
      ∀ n : Fin ((Fintype.card Local) ^ k),
        (asLosslessCompressedWindow k encode faithful).codeSuccessor hLocal
            (encode n) =
              encode (LosslessCompressedWindow.windowZero
                (Fintype.card Local) k hLocal) ↔
          CarryGeometry.carryAfterIncrementAtDepth
            (Fintype.card Local) k n.val := by
  have h :=
    (asLosslessCompressedWindow k encode faithful)
      .universal_lossless_compression_forces_carry_conjugacy hLocal
  exact ⟨h.2.1, h.2.2⟩

/--
Any exact `+1` implementation on a faithful `k`-cell finite-local code is
unique.  Thus an alternative code syntax cannot supply a different exact
quantity successor.
-/
theorem any_exact_kCell_successor_is_forced
    (k : ℕ)
    (hLocal : 0 < Fintype.card Local)
    (encode : Fin ((Fintype.card Local) ^ k) → LocalWord Local k)
    (faithful : Function.Injective encode)
    (step : LocalWord Local k → LocalWord Local k)
    (hstep : ∀ n : Fin ((Fintype.card Local) ^ k),
      step (encode n) = encode
        (LosslessCompressedWindow.windowSuccessor
          (Fintype.card Local) k hLocal n)) :
    step = (asLosslessCompressedWindow k encode faithful).codeSuccessor hLocal :=
  (asLosslessCompressedWindow k encode faithful)
    .codeSuccessor_unique hLocal step hstep

end LocalWord

/--
A lossless representation family using the same finite local state type at every
depth.  At depth `k`, no numeral semantics are assumed: the code is simply an
arbitrary word of `k` local states.
-/
structure LosslessFiniteLocalWordTower (Local : Type u) [Fintype Local] where
  encode : ∀ k : ℕ,
    Fin ((Fintype.card Local) ^ k) → LocalWord Local k
  faithful : ∀ k : ℕ, Function.Injective (encode k)

namespace LosslessFiniteLocalWordTower

variable {Local : Type u} [Fintype Local]

/-- View the finite-local word family as an abstract lossless compressed tower. -/
def toCompressedTower
    (tower : LosslessFiniteLocalWordTower Local) :
    LosslessCompressedTower (Fintype.card Local) where
  level := fun k =>
    { Code := LocalWord Local k
      codeFintype := inferInstance
      rep := LocalWord.asLosslessCompressedWindow k
        (tower.encode k) (tower.faithful k) }

/--
All-depth universal carry theorem for finite-local lossless representation.

If the local alphabet has at least two states, then at every finite depth every
faithful `k`-cell encoding is bijective and its exact unit-successor wrap event
is the canonical carry event.  The base parameter is not separately chosen: it
is the cardinality of the local state type.
-/
theorem all_depths_force_carry
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local) :
    ∀ k : ℕ,
      Function.Bijective (tower.encode k) ∧
        ∀ n : Fin ((Fintype.card Local) ^ k),
          ((tower.toCompressedTower.level k).rep.codeSuccessor
              (lt_trans Nat.zero_lt_one hLocal)
              (tower.encode k n) =
            tower.encode k
              (LosslessCompressedWindow.windowZero
                (Fintype.card Local) k
                (lt_trans Nat.zero_lt_one hLocal)) ↔
            CarryGeometry.carryAfterIncrementAtDepth
              (Fintype.card Local) k n.val) := by
  intro k
  exact LocalWord.any_lossless_kCell_code_forces_carry
    k (lt_trans Nat.zero_lt_one hLocal) (tower.encode k) (tower.faithful k)

end LosslessFiniteLocalWordTower

end QuantityRepresentationFoundations
