import QuantityRepresentationFoundations.UniversalCrossDepthCarryCoherence

/-!
# Universal projective carry tower

Adjacent-depth rigidity already forces every zero-preserving,
successor-equivariant map from depth `k+1` to depth `k` to be residual
reduction.  This module promotes that result to arbitrary depths `k ≤ m` and
proves the projective laws.

For every pair `k ≤ m`, the canonical quantity projection is

`Fin (b^m) → Fin (b^k),  n ↦ n mod b^k`.

It is the unique zero-preserving map commuting with unit successor.  Transported
through arbitrary optimal lossless encoders, it yields a unique projection
between arbitrary code levels.  These forced projections are identities at equal
depth and compose transitively.  Hence an arbitrary optimal lossless tower is,
as a projective successor dynamical system, canonically equivalent to the
residual/carry tower.
-/

namespace QuantityRepresentationFoundations

open LosslessCompressedWindow

universe u v

/-- Canonical residual projection from arbitrary upper depth `m` to `k`. -/
def canonicalDepthProjectionLE
    (b k m : ℕ) (hb : 0 < b) :
    Fin (b ^ m) → Fin (b ^ k) :=
  fun n => ⟨n.val % (b ^ k), Nat.mod_lt _ (pow_pos hb k)⟩

@[simp] theorem canonicalDepthProjectionLE_val
    (b k m : ℕ) (hb : 0 < b) (n : Fin (b ^ m)) :
    (canonicalDepthProjectionLE b k m hb n).val = n.val % (b ^ k) := rfl

/-- Powers at lower depth divide powers at higher depth. -/
theorem placeValue_dvd_of_depth_le
    (b k m : ℕ) (hkm : k ≤ m) :
    b ^ k ∣ b ^ m := by
  exact pow_dvd_pow b hkm

/-- General residual projection preserves zero. -/
theorem canonicalDepthProjectionLE_zero
    (b k m : ℕ) (hb : 0 < b) :
    canonicalDepthProjectionLE b k m hb (windowZero b m hb) =
      windowZero b k hb := by
  apply Fin.ext
  simp [canonicalDepthProjectionLE, windowZero]

/-- General residual projection commutes with unit successor whenever `k ≤ m`. -/
theorem canonicalDepthProjectionLE_commutes_successor
    (b k m : ℕ) (hb : 0 < b) (hkm : k ≤ m)
    (n : Fin (b ^ m)) :
    canonicalDepthProjectionLE b k m hb
        (windowSuccessor b m hb n) =
      windowSuccessor b k hb
        (canonicalDepthProjectionLE b k m hb n) := by
  apply Fin.ext
  change
    (((n.val + 1) % (b ^ m)) % (b ^ k)) =
      (((n.val % (b ^ k)) + 1) % (b ^ k))
  rw [Nat.mod_mod_of_dvd _ (placeValue_dvd_of_depth_le b k m hkm)]
  exact (Nat.mod_add_mod n.val (b ^ k) 1).symm

/-- At equal depth, residual projection is the identity. -/
theorem canonicalDepthProjectionLE_refl
    (b k : ℕ) (hb : 0 < b) :
    canonicalDepthProjectionLE b k k hb = id := by
  funext n
  apply Fin.ext
  exact Nat.mod_eq_of_lt n.isLt

/-- Canonical residual projections satisfy the projective composition law. -/
theorem canonicalDepthProjectionLE_comp
    (b j k m : ℕ) (hb : 0 < b)
    (hjk : j ≤ k) (hkm : k ≤ m)
    (n : Fin (b ^ m)) :
    canonicalDepthProjectionLE b j k hb
        (canonicalDepthProjectionLE b k m hb n) =
      canonicalDepthProjectionLE b j m hb n := by
  apply Fin.ext
  change (n.val % (b ^ k)) % (b ^ j) = n.val % (b ^ j)
  exact Nat.mod_mod_of_dvd _ (placeValue_dvd_of_depth_le b j k hjk)

/--
Rigidity at arbitrary depths.

Any zero-preserving successor-equivariant map from the depth-`m` cycle to the
depth-`k` cycle, with `k ≤ m`, is forced to be reduction modulo `b^k`.
-/
theorem canonicalDepthProjectionLE_unique
    (b k m : ℕ) (hb : 0 < b) (hkm : k ≤ m)
    (f : Fin (b ^ m) → Fin (b ^ k))
    (hzero : f (windowZero b m hb) = windowZero b k hb)
    (hsucc : ∀ n : Fin (b ^ m),
      f (windowSuccessor b m hb n) =
        windowSuccessor b k hb (f n)) :
    f = canonicalDepthProjectionLE b k m hb := by
  funext n
  have hmain : ∀ a : ℕ, ∀ ha : a < b ^ m,
      f ⟨a, ha⟩ = canonicalDepthProjectionLE b k m hb ⟨a, ha⟩ := by
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
          f ⟨a + 1, has⟩ = f (windowSuccessor b m hb x) := by
            rw [hxsucc]
          _ = windowSuccessor b k hb (f x) := hsucc x
          _ = windowSuccessor b k hb
                (canonicalDepthProjectionLE b k m hb x) := by
              rw [ih ha]
          _ = canonicalDepthProjectionLE b k m hb
                (windowSuccessor b m hb x) :=
              (canonicalDepthProjectionLE_commutes_successor
                b k m hb hkm x).symm
          _ = canonicalDepthProjectionLE b k m hb ⟨a + 1, has⟩ := by
              rw [hxsucc]
  exact hmain n.val n.isLt

namespace LosslessCompressedWindow

variable {b k m : ℕ}
variable {CodeUpper : Type u} {CodeLower : Type v}
variable [Fintype CodeUpper] [Fintype CodeLower]

/-- Forced code projection from any upper depth `m` to lower depth `k`. -/
noncomputable def codeDepthProjectionLE
    (upper : LosslessCompressedWindow b m CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) : CodeUpper → CodeLower :=
  fun c => lower.windowEquiv
    (canonicalDepthProjectionLE b k m hb (upper.windowEquiv.symm c))

/-- The forced general code projection acts by residual reduction on quantities. -/
@[simp] theorem codeDepthProjectionLE_encode
    (upper : LosslessCompressedWindow b m CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) (n : Fin (b ^ m)) :
    codeDepthProjectionLE upper lower hb (upper.encode n) =
      lower.encode (canonicalDepthProjectionLE b k m hb n) := by
  unfold codeDepthProjectionLE
  rw [upper.windowEquiv_symm_encode n]
  rfl

/-- General forced code projection preserves represented zero. -/
theorem codeDepthProjectionLE_zero
    (upper : LosslessCompressedWindow b m CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) :
    codeDepthProjectionLE upper lower hb (upper.encode (windowZero b m hb)) =
      lower.encode (windowZero b k hb) := by
  rw [codeDepthProjectionLE_encode]
  exact congrArg lower.encode (canonicalDepthProjectionLE_zero b k m hb)

/-- General forced code projection commutes with exact successor. -/
theorem codeDepthProjectionLE_commutes_successor
    (upper : LosslessCompressedWindow b m CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) (hkm : k ≤ m)
    (c : CodeUpper) :
    codeDepthProjectionLE upper lower hb (upper.codeSuccessor hb c) =
      lower.codeSuccessor hb (codeDepthProjectionLE upper lower hb c) := by
  obtain ⟨n, rfl⟩ := upper.encode_bijective.2 c
  rw [upper.codeSuccessor_encode]
  rw [codeDepthProjectionLE_encode]
  rw [codeDepthProjectionLE_encode]
  rw [lower.codeSuccessor_encode]
  exact congrArg lower.encode
    (canonicalDepthProjectionLE_commutes_successor b k m hb hkm n)

/-- Arbitrary-depth code projection is unique under zero and successor laws. -/
theorem codeDepthProjectionLE_unique
    (upper : LosslessCompressedWindow b m CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) (hkm : k ≤ m)
    (f : CodeUpper → CodeLower)
    (hzero : f (upper.encode (windowZero b m hb)) =
      lower.encode (windowZero b k hb))
    (hsucc : ∀ c : CodeUpper,
      f (upper.codeSuccessor hb c) = lower.codeSuccessor hb (f c)) :
    f = codeDepthProjectionLE upper lower hb := by
  let g : Fin (b ^ m) → Fin (b ^ k) :=
    fun n => lower.windowEquiv.symm (f (upper.encode n))
  have gzero : g (windowZero b m hb) = windowZero b k hb := by
    change lower.windowEquiv.symm (f (upper.encode (windowZero b m hb))) =
      windowZero b k hb
    rw [hzero]
    exact lower.windowEquiv_symm_encode (windowZero b k hb)
  have gsucc : ∀ n : Fin (b ^ m),
      g (windowSuccessor b m hb n) = windowSuccessor b k hb (g n) := by
    intro n
    have h := congrArg lower.windowEquiv.symm (hsucc (upper.encode n))
    simpa [g, codeSuccessor] using h
  have hg : g = canonicalDepthProjectionLE b k m hb :=
    canonicalDepthProjectionLE_unique b k m hb hkm g gzero gsucc
  funext c
  obtain ⟨n, rfl⟩ := upper.encode_bijective.2 c
  have hpoint := congrFun hg n
  have hencoded := congrArg lower.windowEquiv hpoint
  simpa [g] using hencoded

/-- Existence and uniqueness of the coherent projection between arbitrary depths. -/
theorem existsUnique_codeDepthProjectionLE
    (upper : LosslessCompressedWindow b m CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) (hkm : k ≤ m) :
    ∃! f : CodeUpper → CodeLower,
      f (upper.encode (windowZero b m hb)) = lower.encode (windowZero b k hb) ∧
      ∀ c : CodeUpper,
        f (upper.codeSuccessor hb c) = lower.codeSuccessor hb (f c) := by
  refine ⟨codeDepthProjectionLE upper lower hb, ?_, ?_⟩
  · exact ⟨codeDepthProjectionLE_zero upper lower hb,
      codeDepthProjectionLE_commutes_successor upper lower hb hkm⟩
  · intro f hf
    exact codeDepthProjectionLE_unique upper lower hb hkm f hf.1 hf.2

end LosslessCompressedWindow

namespace LosslessCompressedTower

variable {b : ℕ}

/-- Forced projection between any two ordered depths of an optimal tower. -/
noncomputable def forcedProjection
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) {k m : ℕ} (hkm : k ≤ m) :
    (tower.level m).Code → (tower.level k).Code :=
  LosslessCompressedWindow.codeDepthProjectionLE
    (tower.level m).rep (tower.level k).rep hb

/-- Forced tower projection is residual reduction on encoded quantities. -/
@[simp] theorem forcedProjection_encode
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) {k m : ℕ} (hkm : k ≤ m)
    (n : Fin (b ^ m)) :
    tower.forcedProjection hb hkm ((tower.level m).rep.encode n) =
      (tower.level k).rep.encode (canonicalDepthProjectionLE b k m hb n) :=
  LosslessCompressedWindow.codeDepthProjectionLE_encode
    (tower.level m).rep (tower.level k).rep hb n

/-- Every ordered pair of tower depths has one unique coherent projection. -/
theorem existsUnique_forcedProjection
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) {k m : ℕ} (hkm : k ≤ m) :
    ∃! f : (tower.level m).Code → (tower.level k).Code,
      f ((tower.level m).rep.encode (windowZero b m hb)) =
          (tower.level k).rep.encode (windowZero b k hb) ∧
      ∀ c : (tower.level m).Code,
        f ((tower.level m).rep.codeSuccessor hb c) =
          (tower.level k).rep.codeSuccessor hb (f c) :=
  LosslessCompressedWindow.existsUnique_codeDepthProjectionLE
    (tower.level m).rep (tower.level k).rep hb hkm

/-- Equal-depth forced projection is identity. -/
theorem forcedProjection_refl
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) (k : ℕ) :
    tower.forcedProjection hb (show k ≤ k from le_rfl) = id := by
  funext c
  obtain ⟨n, rfl⟩ := (tower.level k).rep.encode_bijective.2 c
  rw [forcedProjection_encode]
  have h := congrFun (canonicalDepthProjectionLE_refl b k hb) n
  exact congrArg (tower.level k).rep.encode h

/-- Forced projections compose transitively: the tower is projective. -/
theorem forcedProjection_comp
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b)
    {j k m : ℕ} (hjk : j ≤ k) (hkm : k ≤ m)
    (c : (tower.level m).Code) :
    tower.forcedProjection hb hjk
        (tower.forcedProjection hb hkm c) =
      tower.forcedProjection hb (le_trans hjk hkm) c := by
  obtain ⟨n, rfl⟩ := (tower.level m).rep.encode_bijective.2 c
  rw [forcedProjection_encode]
  rw [forcedProjection_encode]
  rw [forcedProjection_encode]
  exact congrArg (tower.level j).rep.encode
    (canonicalDepthProjectionLE_comp b j k m hb hjk hkm n)

/-- Capstone projective laws for an arbitrary optimal lossless tower. -/
theorem universal_projective_tower_laws
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) :
    (∀ k : ℕ,
      tower.forcedProjection hb (show k ≤ k from le_rfl) = id) ∧
    (∀ (j k m : ℕ) (hjk : j ≤ k) (hkm : k ≤ m)
        (c : (tower.level m).Code),
      tower.forcedProjection hb hjk
          (tower.forcedProjection hb hkm c) =
        tower.forcedProjection hb (le_trans hjk hkm) c) := by
  constructor
  · exact fun k => tower.forcedProjection_refl hb k
  · exact fun j k m hjk hkm c => tower.forcedProjection_comp hb hjk hkm c

end LosslessCompressedTower

namespace LosslessFiniteLocalWordTower

variable {Local : Type u} [Fintype Local]

/-- Every pair of finite-local depths has a unique coherent quantitative map. -/
theorem all_depth_projections_are_forced
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local) :
    ∀ (k m : ℕ), k ≤ m →
      ∃! f : LocalWord Local m → LocalWord Local k,
        f (tower.encode m
            (windowZero (Fintype.card Local) m
              (lt_trans Nat.zero_lt_one hLocal))) =
          tower.encode k
            (windowZero (Fintype.card Local) k
              (lt_trans Nat.zero_lt_one hLocal)) ∧
        ∀ c : LocalWord Local m,
          f ((tower.toCompressedTower.level m).rep.codeSuccessor
              (lt_trans Nat.zero_lt_one hLocal) c) =
            (tower.toCompressedTower.level k).rep.codeSuccessor
              (lt_trans Nat.zero_lt_one hLocal) (f c) := by
  intro k m hkm
  exact LosslessCompressedTower.existsUnique_forcedProjection
    tower.toCompressedTower (lt_trans Nat.zero_lt_one hLocal) hkm

/-- The forced finite-local projection is modulo `|Local|^k` in quantity coordinates. -/
theorem forced_projection_is_modulo
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local)
    {k m : ℕ} (hkm : k ≤ m)
    (n : Fin ((Fintype.card Local) ^ m)) :
    tower.toCompressedTower.forcedProjection
        (lt_trans Nat.zero_lt_one hLocal) hkm (tower.encode m n) =
      tower.encode k
        (canonicalDepthProjectionLE (Fintype.card Local) k m
          (lt_trans Nat.zero_lt_one hLocal) n) :=
  LosslessCompressedTower.forcedProjection_encode
    tower.toCompressedTower (lt_trans Nat.zero_lt_one hLocal) hkm n

/--
Full projective-system theorem for arbitrary finite-local lossless
representation.
-/
theorem universal_finiteLocal_projective_carry_tower
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local) :
    (∀ k : ℕ,
      tower.toCompressedTower.forcedProjection
        (lt_trans Nat.zero_lt_one hLocal)
        (show k ≤ k from le_rfl) = id) ∧
    (∀ (j k m : ℕ) (hjk : j ≤ k) (hkm : k ≤ m)
        (c : LocalWord Local m),
      tower.toCompressedTower.forcedProjection
          (lt_trans Nat.zero_lt_one hLocal) hjk
          (tower.toCompressedTower.forcedProjection
            (lt_trans Nat.zero_lt_one hLocal) hkm c) =
        tower.toCompressedTower.forcedProjection
          (lt_trans Nat.zero_lt_one hLocal) (le_trans hjk hkm) c) :=
  LosslessCompressedTower.universal_projective_tower_laws
    tower.toCompressedTower (lt_trans Nat.zero_lt_one hLocal)

end LosslessFiniteLocalWordTower

end QuantityRepresentationFoundations
