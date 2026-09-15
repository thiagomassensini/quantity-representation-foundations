import QuantityRepresentationFoundations.UniversalProjectiveCarryTower

namespace QuantityRepresentationFoundations

open LosslessCompressedWindow

universe u v

/-- An optimal lossless finite code with an explicit encoder/decoder equivalence. -/
structure ExplicitLosslessWindow (b k : ℕ) (Code : Type u) where
  equiv : Fin (b ^ k) ≃ Code

namespace ExplicitLosslessWindow

variable {b k m : ℕ}
variable {Code : Type u} {CodeUpper : Type u} {CodeLower : Type v}

def encode (rep : ExplicitLosslessWindow b k Code) : Fin (b ^ k) → Code := rep.equiv

def decode (rep : ExplicitLosslessWindow b k Code) : Code → Fin (b ^ k) := rep.equiv.symm

@[simp] theorem decode_encode
    (rep : ExplicitLosslessWindow b k Code) (n : Fin (b ^ k)) :
    rep.decode (rep.encode n) = n := rep.equiv.symm_apply_apply n

@[simp] theorem encode_decode
    (rep : ExplicitLosslessWindow b k Code) (c : Code) :
    rep.encode (rep.decode c) = c := rep.equiv.apply_symm_apply c

def successor
    (rep : ExplicitLosslessWindow b k Code) (hb : 0 < b) : Code → Code :=
  fun c => rep.encode (windowSuccessor b k hb (rep.decode c))

@[simp] theorem successor_encode
    (rep : ExplicitLosslessWindow b k Code) (hb : 0 < b) (n : Fin (b ^ k)) :
    rep.successor hb (rep.encode n) = rep.encode (windowSuccessor b k hb n) := by
  unfold successor
  rw [rep.decode_encode]

theorem wrap_iff_carry
    (rep : ExplicitLosslessWindow b k Code) (hb : 0 < b) (n : Fin (b ^ k)) :
    rep.successor hb (rep.encode n) = rep.encode (windowZero b k hb) ↔
      CarryGeometry.carryAfterIncrementAtDepth b k n.val := by
  rw [rep.successor_encode hb n]
  constructor
  · intro h
    have hw : windowSuccessor b k hb n = windowZero b k hb := rep.equiv.injective h
    exact (windowSuccessor_eq_zero_iff_carry b k hb n).1 hw
  · intro h
    exact congrArg rep.encode ((windowSuccessor_eq_zero_iff_carry b k hb n).2 h)

theorem exact_successor_unique_pointwise
    (rep : ExplicitLosslessWindow b k Code)
    (hb : 0 < b)
    (step : Code → Code)
    (hstep : ∀ n : Fin (b ^ k),
      step (rep.encode n) = rep.encode (windowSuccessor b k hb n)) :
    ∀ c : Code, step c = rep.successor hb c := by
  intro c
  rw [← rep.encode_decode c]
  exact (hstep (rep.decode c)).trans (rep.successor_encode hb (rep.decode c)).symm

def projection
    (upper : ExplicitLosslessWindow b m CodeUpper)
    (lower : ExplicitLosslessWindow b k CodeLower)
    (hb : 0 < b) : CodeUpper → CodeLower :=
  fun c => lower.encode (canonicalDepthProjectionLE b k m hb (upper.decode c))

@[simp] theorem projection_encode
    (upper : ExplicitLosslessWindow b m CodeUpper)
    (lower : ExplicitLosslessWindow b k CodeLower)
    (hb : 0 < b) (n : Fin (b ^ m)) :
    projection upper lower hb (upper.encode n) =
      lower.encode (canonicalDepthProjectionLE b k m hb n) := by
  unfold projection
  rw [upper.decode_encode]

theorem projection_zero
    (upper : ExplicitLosslessWindow b m CodeUpper)
    (lower : ExplicitLosslessWindow b k CodeLower)
    (hb : 0 < b) :
    projection upper lower hb (upper.encode (windowZero b m hb)) =
      lower.encode (windowZero b k hb) := by
  rw [projection_encode]
  exact congrArg lower.encode (canonicalDepthProjectionLE_zero b k m hb)

theorem projection_commutes_successor
    (upper : ExplicitLosslessWindow b m CodeUpper)
    (lower : ExplicitLosslessWindow b k CodeLower)
    (hb : 0 < b) (hkm : k ≤ m)
    (c : CodeUpper) :
    projection upper lower hb (upper.successor hb c) =
      lower.successor hb (projection upper lower hb c) := by
  rw [← upper.encode_decode c]
  rw [upper.successor_encode]
  rw [projection_encode]
  rw [projection_encode]
  rw [lower.successor_encode]
  exact congrArg lower.encode
    (canonicalDepthProjectionLE_commutes_successor b k m hb hkm (upper.decode c))

theorem projection_unique_pointwise
    (upper : ExplicitLosslessWindow b m CodeUpper)
    (lower : ExplicitLosslessWindow b k CodeLower)
    (hb : 0 < b) (hkm : k ≤ m)
    (f : CodeUpper → CodeLower)
    (hzero : f (upper.encode (windowZero b m hb)) = lower.encode (windowZero b k hb))
    (hsucc : ∀ c : CodeUpper,
      f (upper.successor hb c) = lower.successor hb (f c)) :
    ∀ c : CodeUpper, f c = projection upper lower hb c := by
  have hquantity : ∀ a : ℕ, ∀ ha : a < b ^ m,
      f (upper.encode ⟨a, ha⟩) =
        lower.encode (canonicalDepthProjectionLE b k m hb ⟨a, ha⟩) := by
    intro a
    induction a with
    | zero =>
        intro ha
        simpa [windowZero, canonicalDepthProjectionLE] using hzero
    | succ a ih =>
        intro has
        have ha : a < b ^ m := Nat.lt_of_succ_lt has
        let x : Fin (b ^ m) := ⟨a, ha⟩
        have hxsucc : windowSuccessor b m hb x = ⟨a + 1, has⟩ := by
          exact windowSuccessor_mk_of_succ_lt b m a hb ha has
        calc
          f (upper.encode ⟨a + 1, has⟩) = f (upper.successor hb (upper.encode x)) := by
            rw [upper.successor_encode, hxsucc]
          _ = lower.successor hb (f (upper.encode x)) := hsucc (upper.encode x)
          _ = lower.successor hb
                (lower.encode (canonicalDepthProjectionLE b k m hb x)) := by
            rw [ih ha]
          _ = lower.encode
                (windowSuccessor b k hb (canonicalDepthProjectionLE b k m hb x)) := by
            rw [lower.successor_encode]
          _ = lower.encode
                (canonicalDepthProjectionLE b k m hb (windowSuccessor b m hb x)) := by
            exact congrArg lower.encode
              (canonicalDepthProjectionLE_commutes_successor b k m hb hkm x).symm
          _ = lower.encode
                (canonicalDepthProjectionLE b k m hb ⟨a + 1, has⟩) := by
            rw [hxsucc]
  intro c
  rw [← upper.encode_decode c]
  rw [projection_encode]
  exact hquantity (upper.decode c).val (upper.decode c).isLt

theorem projection_refl_pointwise
    (rep : ExplicitLosslessWindow b k Code)
    (hb : 0 < b) (c : Code) :
    projection rep rep hb c = c := by
  rw [← rep.encode_decode c]
  rw [projection_encode]
  exact congrArg rep.encode
    (congrFun (canonicalDepthProjectionLE_refl b k hb) (rep.decode c))

theorem projection_comp_pointwise
    {j : ℕ} {CodeJ : Type v}
    (upper : ExplicitLosslessWindow b m CodeUpper)
    (middle : ExplicitLosslessWindow b k CodeLower)
    (lower : ExplicitLosslessWindow b j CodeJ)
    (hb : 0 < b) (hjk : j ≤ k) (hkm : k ≤ m)
    (c : CodeUpper) :
    projection middle lower hb (projection upper middle hb c) =
      projection upper lower hb c := by
  rw [← upper.encode_decode c]
  rw [projection_encode]
  rw [projection_encode]
  rw [projection_encode]
  exact congrArg lower.encode
    (canonicalDepthProjectionLE_comp b j k m hb hjk hkm (upper.decode c))

end ExplicitLosslessWindow

structure ExplicitLosslessTower (b : ℕ) where
  Code : ℕ → Type u
  level : ∀ k : ℕ, ExplicitLosslessWindow b k (Code k)

namespace ExplicitLosslessTower

variable {b : ℕ}

structure ConstructiveCarryRigidityCertificate
    (tower : ExplicitLosslessTower.{u} b)
    (hb : 0 < b) : Prop where
  successor_wrap : ∀ (k : ℕ) (n : Fin (b ^ k)),
    (tower.level k).successor hb ((tower.level k).encode n) =
        (tower.level k).encode (windowZero b k hb) ↔
      CarryGeometry.carryAfterIncrementAtDepth b k n.val
  projection_zero : ∀ (k m : ℕ) (hkm : k ≤ m),
    ExplicitLosslessWindow.projection (tower.level m) (tower.level k) hb
        ((tower.level m).encode (windowZero b m hb)) =
      (tower.level k).encode (windowZero b k hb)
  projection_successor : ∀ (k m : ℕ) (hkm : k ≤ m) (c : tower.Code m),
    ExplicitLosslessWindow.projection (tower.level m) (tower.level k) hb
        ((tower.level m).successor hb c) =
      (tower.level k).successor hb
        (ExplicitLosslessWindow.projection (tower.level m) (tower.level k) hb c)
  projection_unique_pointwise : ∀ (k m : ℕ) (hkm : k ≤ m)
      (f : tower.Code m → tower.Code k),
    f ((tower.level m).encode (windowZero b m hb)) =
        (tower.level k).encode (windowZero b k hb) →
    (∀ c : tower.Code m,
      f ((tower.level m).successor hb c) = (tower.level k).successor hb (f c)) →
    ∀ c : tower.Code m,
      f c = ExplicitLosslessWindow.projection (tower.level m) (tower.level k) hb c
  projection_refl_pointwise : ∀ (k : ℕ) (c : tower.Code k),
    ExplicitLosslessWindow.projection (tower.level k) (tower.level k) hb c = c
  projection_comp_pointwise : ∀ (j k m : ℕ) (hjk : j ≤ k) (hkm : k ≤ m)
      (c : tower.Code m),
    ExplicitLosslessWindow.projection (tower.level k) (tower.level j) hb
        (ExplicitLosslessWindow.projection (tower.level m) (tower.level k) hb c) =
      ExplicitLosslessWindow.projection (tower.level m) (tower.level j) hb c

theorem explicit_lossless_tower_collapses_to_carry
    (tower : ExplicitLosslessTower.{u} b)
    (hb : 1 < b) :
    ConstructiveCarryRigidityCertificate tower (lt_trans Nat.zero_lt_one hb) := by
  let hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  refine
    { successor_wrap := ?_
      projection_zero := ?_
      projection_successor := ?_
      projection_unique_pointwise := ?_
      projection_refl_pointwise := ?_
      projection_comp_pointwise := ?_ }
  · intro k n
    exact (tower.level k).wrap_iff_carry hb0 n
  · intro k m hkm
    exact ExplicitLosslessWindow.projection_zero (tower.level m) (tower.level k) hb0
  · intro k m hkm c
    exact ExplicitLosslessWindow.projection_commutes_successor
      (tower.level m) (tower.level k) hb0 hkm c
  · intro k m hkm f hzero hsucc c
    exact ExplicitLosslessWindow.projection_unique_pointwise
      (tower.level m) (tower.level k) hb0 hkm f hzero hsucc c
  · intro k c
    exact ExplicitLosslessWindow.projection_refl_pointwise (tower.level k) hb0 c
  · intro j k m hjk hkm c
    exact ExplicitLosslessWindow.projection_comp_pointwise
      (tower.level m) (tower.level k) (tower.level j) hb0 hjk hkm c

end ExplicitLosslessTower

end QuantityRepresentationFoundations
