import QuantityRepresentationFoundations.UniversalLosslessCompressionTower

/-!
# Universal cross-depth carry coherence

The previous universal-compression theorems show that every finite depth of a
lossless finite-local representation is, independently, only a change of
coordinates of the canonical cyclic quantity window `Fin (b^k)`.

This module removes the remaining freedom between adjacent depths.

The canonical map from depth `k+1` to depth `k` is reduction modulo `b^k`.
We prove that it preserves zero, commutes with unit successor, and is the unique
map with those two properties.  Transporting this statement through arbitrary
lossless encoders yields the corresponding result for completely opaque code
types: every zero-preserving successor-equivariant cross-depth map is forced.

Thus the hierarchy itself, not only the dynamics inside each finite level, is
canonical up to change of coordinates.
-/

namespace QuantityRepresentationFoundations

open LosslessCompressedWindow

universe u v

/--
Canonical reduction from the depth-`k+1` quantity window to the depth-`k`
window.  Its value is exactly the lower-depth residual `n mod b^k`.
-/
def canonicalDepthProjection
    (b k : ℕ) (hb : 0 < b) :
    Fin (b ^ (k + 1)) → Fin (b ^ k) :=
  fun n => ⟨n.val % (b ^ k), Nat.mod_lt _ (pow_pos hb k)⟩

@[simp] theorem canonicalDepthProjection_val
    (b k : ℕ) (hb : 0 < b) (n : Fin (b ^ (k + 1))) :
    (canonicalDepthProjection b k hb n).val = n.val % (b ^ k) := rfl

/-- The canonical depth projection preserves the distinguished zero state. -/
theorem canonicalDepthProjection_zero
    (b k : ℕ) (hb : 0 < b) :
    canonicalDepthProjection b k hb
        (windowZero b (k + 1) hb) =
      windowZero b k hb := by
  apply Fin.ext
  simp [canonicalDepthProjection, windowZero]

/-- The lower place-value divides the next place-value. -/
theorem placeValue_dvd_nextDepth
    (b k : ℕ) :
    b ^ k ∣ b ^ (k + 1) := by
  refine ⟨b, ?_⟩
  simp [pow_succ]

/--
Canonical depth reduction commutes with cyclic unit successor.
This is the algebraic coherence of adjacent residual windows.
-/
theorem canonicalDepthProjection_commutes_successor
    (b k : ℕ) (hb : 0 < b)
    (n : Fin (b ^ (k + 1))) :
    canonicalDepthProjection b k hb
        (windowSuccessor b (k + 1) hb n) =
      windowSuccessor b k hb
        (canonicalDepthProjection b k hb n) := by
  apply Fin.ext
  change
    (((n.val + 1) % (b ^ (k + 1))) % (b ^ k)) =
      (((n.val % (b ^ k)) + 1) % (b ^ k))
  rw [Nat.mod_mod_of_dvd _ (placeValue_dvd_nextDepth b k)]
  exact (Nat.mod_add_mod n.val (b ^ k) 1).symm

/--
A non-wrapping canonical successor is ordinary increment on the underlying
natural representative.
-/
theorem windowSuccessor_mk_of_succ_lt
    (b depth m : ℕ) (hb : 0 < b)
    (hm : m < b ^ depth)
    (hms : m + 1 < b ^ depth) :
    windowSuccessor b depth hb ⟨m, hm⟩ = ⟨m + 1, hms⟩ := by
  apply Fin.ext
  simp [windowSuccessor, Nat.mod_eq_of_lt hms]

/--
Rigidity of adjacent cyclic windows.

Any map `Fin (b^(k+1)) → Fin (b^k)` that preserves zero and commutes with unit
successor is forced to be reduction modulo `b^k`.
-/
theorem canonicalDepthProjection_unique
    (b k : ℕ) (hb : 0 < b)
    (f : Fin (b ^ (k + 1)) → Fin (b ^ k))
    (hzero :
      f (windowZero b (k + 1) hb) = windowZero b k hb)
    (hsucc : ∀ n : Fin (b ^ (k + 1)),
      f (windowSuccessor b (k + 1) hb n) =
        windowSuccessor b k hb (f n)) :
    f = canonicalDepthProjection b k hb := by
  funext n
  have hmain : ∀ m : ℕ, ∀ hm : m < b ^ (k + 1),
      f ⟨m, hm⟩ = canonicalDepthProjection b k hb ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero =>
        intro hm
        simpa [windowZero, canonicalDepthProjection] using hzero
    | succ m ih =>
        intro hms
        have hm : m < b ^ (k + 1) := Nat.lt_of_succ_lt hms
        let x : Fin (b ^ (k + 1)) := ⟨m, hm⟩
        have hxsucc :
            windowSuccessor b (k + 1) hb x = ⟨m + 1, hms⟩ := by
          exact windowSuccessor_mk_of_succ_lt b (k + 1) m hb hm hms
        calc
          f ⟨m + 1, hms⟩ =
              f (windowSuccessor b (k + 1) hb x) := by rw [hxsucc]
          _ = windowSuccessor b k hb (f x) := hsucc x
          _ = windowSuccessor b k hb
                (canonicalDepthProjection b k hb x) := by
              rw [ih hm]
          _ = canonicalDepthProjection b k hb
                (windowSuccessor b (k + 1) hb x) :=
              (canonicalDepthProjection_commutes_successor b k hb x).symm
          _ = canonicalDepthProjection b k hb ⟨m + 1, hms⟩ := by
              rw [hxsucc]
  exact hmain n.val n.isLt

namespace LosslessCompressedWindow

variable {b k : ℕ}
variable {CodeUpper : Type u} {CodeLower : Type v}
variable [Fintype CodeUpper] [Fintype CodeLower]

/--
The forced cross-depth map between two arbitrary optimal lossless code spaces.
It is obtained by decoding the upper code, taking the canonical residual, and
re-encoding at the lower depth.
-/
noncomputable def codeDepthProjection
    (upper : LosslessCompressedWindow b (k + 1) CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) :
    CodeUpper → CodeLower :=
  fun c =>
    lower.windowEquiv
      (canonicalDepthProjection b k hb (upper.windowEquiv.symm c))

/-- On represented quantities, the forced code projection is exactly modulo. -/
@[simp] theorem codeDepthProjection_encode
    (upper : LosslessCompressedWindow b (k + 1) CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b)
    (n : Fin (b ^ (k + 1))) :
    codeDepthProjection upper lower hb (upper.encode n) =
      lower.encode (canonicalDepthProjection b k hb n) := by
  unfold codeDepthProjection
  rw [upper.windowEquiv_symm_encode n]
  rfl

/-- The forced code projection preserves the represented zero state. -/
theorem codeDepthProjection_zero
    (upper : LosslessCompressedWindow b (k + 1) CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) :
    codeDepthProjection upper lower hb
        (upper.encode (windowZero b (k + 1) hb)) =
      lower.encode (windowZero b k hb) := by
  rw [codeDepthProjection_encode]
  exact congrArg lower.encode (canonicalDepthProjection_zero b k hb)

/-- The forced code projection commutes with the exact code successor. -/
theorem codeDepthProjection_commutes_successor
    (upper : LosslessCompressedWindow b (k + 1) CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b)
    (c : CodeUpper) :
    codeDepthProjection upper lower hb (upper.codeSuccessor hb c) =
      lower.codeSuccessor hb (codeDepthProjection upper lower hb c) := by
  obtain ⟨n, rfl⟩ := upper.encode_bijective.2 c
  rw [upper.codeSuccessor_encode]
  rw [codeDepthProjection_encode]
  rw [codeDepthProjection_encode]
  rw [lower.codeSuccessor_encode]
  exact congrArg lower.encode
    (canonicalDepthProjection_commutes_successor b k hb n)

/-- Decode an arbitrary cross-depth code map back to canonical finite windows. -/
noncomputable def decodedDepthMap
    (upper : LosslessCompressedWindow b (k + 1) CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (f : CodeUpper → CodeLower) :
    Fin (b ^ (k + 1)) → Fin (b ^ k) :=
  fun n => lower.windowEquiv.symm (f (upper.encode n))

/--
Cross-depth rigidity for arbitrary code coordinates.

Every code map that preserves represented zero and commutes with the exact unit
successors is the forced decode--modulo--encode map.
-/
theorem codeDepthProjection_unique
    (upper : LosslessCompressedWindow b (k + 1) CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b)
    (f : CodeUpper → CodeLower)
    (hzero :
      f (upper.encode (windowZero b (k + 1) hb)) =
        lower.encode (windowZero b k hb))
    (hsucc : ∀ c : CodeUpper,
      f (upper.codeSuccessor hb c) =
        lower.codeSuccessor hb (f c)) :
    f = codeDepthProjection upper lower hb := by
  let g : Fin (b ^ (k + 1)) → Fin (b ^ k) :=
    decodedDepthMap upper lower f
  have gzero :
      g (windowZero b (k + 1) hb) = windowZero b k hb := by
    change lower.windowEquiv.symm
      (f (upper.encode (windowZero b (k + 1) hb))) =
        windowZero b k hb
    rw [hzero]
    exact lower.windowEquiv_symm_encode (windowZero b k hb)
  have gsucc : ∀ n : Fin (b ^ (k + 1)),
      g (windowSuccessor b (k + 1) hb n) =
        windowSuccessor b k hb (g n) := by
    intro n
    have h := congrArg lower.windowEquiv.symm (hsucc (upper.encode n))
    simpa [g, decodedDepthMap, codeSuccessor] using h
  have hg : g = canonicalDepthProjection b k hb :=
    canonicalDepthProjection_unique b k hb g gzero gsucc
  funext c
  obtain ⟨n, rfl⟩ := upper.encode_bijective.2 c
  have hpoint := congrFun hg n
  have hencoded := congrArg lower.windowEquiv hpoint
  simpa [g, decodedDepthMap] using hencoded

/--
Existence and uniqueness of the successor-coherent adjacent-depth projection in
arbitrary optimal lossless coordinates.
-/
theorem existsUnique_codeDepthProjection
    (upper : LosslessCompressedWindow b (k + 1) CodeUpper)
    (lower : LosslessCompressedWindow b k CodeLower)
    (hb : 0 < b) :
    ∃! f : CodeUpper → CodeLower,
      f (upper.encode (windowZero b (k + 1) hb)) =
          lower.encode (windowZero b k hb) ∧
        ∀ c : CodeUpper,
          f (upper.codeSuccessor hb c) =
            lower.codeSuccessor hb (f c) := by
  refine ⟨codeDepthProjection upper lower hb, ?_, ?_⟩
  · exact ⟨codeDepthProjection_zero upper lower hb,
      codeDepthProjection_commutes_successor upper lower hb⟩
  · intro f hf
    exact codeDepthProjection_unique upper lower hb f hf.1 hf.2

end LosslessCompressedWindow

namespace LosslessCompressedTower

variable {b : ℕ}

/-- The forced adjacent-depth projection in an arbitrary optimal tower. -/
noncomputable def forcedAdjacentProjection
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) (k : ℕ) :
    (tower.level (k + 1)).Code → (tower.level k).Code :=
  LosslessCompressedWindow.codeDepthProjection
    (tower.level (k + 1)).rep (tower.level k).rep hb

/-- The tower projection sends an encoded quantity to its lower residual. -/
@[simp] theorem forcedAdjacentProjection_encode
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) (k : ℕ)
    (n : Fin (b ^ (k + 1))) :
    tower.forcedAdjacentProjection hb k
        ((tower.level (k + 1)).rep.encode n) =
      (tower.level k).rep.encode
        (canonicalDepthProjection b k hb n) :=
  LosslessCompressedWindow.codeDepthProjection_encode
    (tower.level (k + 1)).rep (tower.level k).rep hb n

/--
At every adjacent pair of depths there exists exactly one zero-preserving,
successor-equivariant projection.
-/
theorem existsUnique_forcedAdjacentProjection
    (tower : LosslessCompressedTower.{u} b)
    (hb : 0 < b) (k : ℕ) :
    ∃! f : (tower.level (k + 1)).Code → (tower.level k).Code,
      f ((tower.level (k + 1)).rep.encode
          (windowZero b (k + 1) hb)) =
        (tower.level k).rep.encode (windowZero b k hb) ∧
      ∀ c : (tower.level (k + 1)).Code,
        f ((tower.level (k + 1)).rep.codeSuccessor hb c) =
          (tower.level k).rep.codeSuccessor hb (f c) :=
  LosslessCompressedWindow.existsUnique_codeDepthProjection
    (tower.level (k + 1)).rep (tower.level k).rep hb

end LosslessCompressedTower

namespace LosslessFiniteLocalWordTower

variable {Local : Type u} [Fintype Local]

/--
Global adjacent-depth rigidity for arbitrary finite-local lossless
representation.  No native truncation rule is assumed: the unique coherent rule
is induced by quantitative semantics and is conjugate to modulo reduction.
-/
theorem all_adjacent_depth_projections_are_forced
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local) :
    ∀ k : ℕ,
      ∃! f : LocalWord Local (k + 1) → LocalWord Local k,
        f (tower.encode (k + 1)
            (windowZero (Fintype.card Local) (k + 1)
              (lt_trans Nat.zero_lt_one hLocal))) =
          tower.encode k
            (windowZero (Fintype.card Local) k
              (lt_trans Nat.zero_lt_one hLocal)) ∧
        ∀ c : LocalWord Local (k + 1),
          f ((tower.toCompressedTower.level (k + 1)).rep.codeSuccessor
                (lt_trans Nat.zero_lt_one hLocal) c) =
            (tower.toCompressedTower.level k).rep.codeSuccessor
              (lt_trans Nat.zero_lt_one hLocal) (f c) := by
  intro k
  exact LosslessCompressedTower.existsUnique_forcedAdjacentProjection
    tower.toCompressedTower (lt_trans Nat.zero_lt_one hLocal) k

/--
The unique adjacent projection acts on represented quantities by reduction
modulo `|Local|^k`.
-/
theorem forced_adjacent_projection_is_modulo
    (tower : LosslessFiniteLocalWordTower Local)
    (hLocal : 1 < Fintype.card Local)
    (k : ℕ)
    (n : Fin ((Fintype.card Local) ^ (k + 1))) :
    tower.toCompressedTower.forcedAdjacentProjection
        (lt_trans Nat.zero_lt_one hLocal) k
        (tower.encode (k + 1) n) =
      tower.encode k
        (canonicalDepthProjection (Fintype.card Local) k
          (lt_trans Nat.zero_lt_one hLocal) n) :=
  LosslessCompressedTower.forcedAdjacentProjection_encode
    tower.toCompressedTower (lt_trans Nat.zero_lt_one hLocal) k n

end LosslessFiniteLocalWordTower

end QuantityRepresentationFoundations
