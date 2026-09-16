import QuantityRepresentationFoundations.ConstructiveFiniteInverse

/-!
# Primitive finite pigeonhole principle

This module proves the exact finite self-map statement needed by the
constructive capacity route without passing through `Fintype.card`.

The proof removes one explicit source slot and its image target slot.  The
remaining `Fin N → Fin N` map is handled inductively.  Only the raw axiom-free
`Fin.succAbove` definition is used; the standard higher lemmas around
`succAbove`/`predAbove` are deliberately reproved here because their current
library implementations carry logical dependencies in the axiom trace.
-/

namespace QuantityRepresentationFoundations
namespace PrimitiveFinitePigeonhole

/-- Raw `succAbove` never hits the skipped pivot. -/
theorem succAbove_ne_pivot {N : ℕ}
    (p : Fin (N + 1)) (i : Fin N) :
    p.succAbove i ≠ p := by
  unfold Fin.succAbove
  by_cases h : i.castSucc < p
  · rw [if_pos h]
    intro heq
    have hv : i.val = p.val := congrArg Fin.val heq
    exact (Nat.ne_of_lt h) hv
  · rw [if_neg h]
    intro heq
    apply h
    show i.val < p.val
    have hv : i.val + 1 = p.val := congrArg Fin.val heq
    rw [← hv]
    exact Nat.lt_succ_self i.val

/-- Raw `succAbove` is injective, proved directly from its two branches. -/
theorem succAbove_injective {N : ℕ}
    (p : Fin (N + 1)) :
    Function.Injective (fun i : Fin N => p.succAbove i) := by
  intro i j hij
  unfold Fin.succAbove at hij
  change
    (if i.castSucc < p then i.castSucc else i.succ) =
      (if j.castSucc < p then j.castSucc else j.succ) at hij
  by_cases hi : i.castSucc < p
  · rw [if_pos hi] at hij
    by_cases hj : j.castSucc < p
    · rw [if_pos hj] at hij
      have hv : i.val = j.val :=
        congrArg (fun q : Fin (N + 1) => q.val) hij
      exact Fin.ext hv
    · rw [if_neg hj] at hij
      exfalso
      apply hj
      change j.val < p.val
      change i.val < p.val at hi
      have hv : i.val = j.val + 1 :=
        congrArg (fun q : Fin (N + 1) => q.val) hij
      rw [hv] at hi
      exact Nat.lt_trans (Nat.lt_succ_self j.val) hi
  · rw [if_neg hi] at hij
    by_cases hj : j.castSucc < p
    · rw [if_pos hj] at hij
      exfalso
      apply hi
      change i.val < p.val
      change j.val < p.val at hj
      have hv : i.val + 1 = j.val :=
        congrArg (fun q : Fin (N + 1) => q.val) hij
      rw [← hv] at hj
      exact Nat.lt_trans (Nat.lt_succ_self i.val) hj
    · rw [if_neg hj] at hij
      have hv : i.val + 1 = j.val + 1 :=
        congrArg (fun q : Fin (N + 1) => q.val) hij
      change Nat.succ i.val = Nat.succ j.val at hv
      exact Fin.ext (Nat.succ.inj hv)

/-- Every point other than the pivot is reached by raw `succAbove`. -/
theorem exists_succAbove_eq_of_ne {N : ℕ}
    {x p : Fin (N + 1)} (hxp : x ≠ p) :
    ∃ i : Fin N, p.succAbove i = x := by
  by_cases hlt : x < p
  · have hp_le_N : p.val ≤ N := Nat.le_of_lt_succ p.isLt
    have hxN : x.val < N := Nat.lt_of_lt_of_le hlt hp_le_N
    let i : Fin N := ⟨x.val, hxN⟩
    refine ⟨i, ?_⟩
    unfold Fin.succAbove
    have hi : i.castSucc < p := by
      change x.val < p.val
      exact hlt
    rw [if_pos hi]
    apply Fin.ext
    rfl
  · have hle : p.val ≤ x.val := Nat.le_of_not_gt hlt
    have hp_ne_x : p.val ≠ x.val := by
      intro hv
      apply hxp
      apply Fin.ext
      exact hv.symm
    have hpltx : p.val < x.val := Nat.lt_of_le_of_ne hle hp_ne_x
    cases hxval : x.val with
    | zero =>
        rw [hxval] at hpltx
        exact (Nat.not_lt_zero p.val hpltx).elim
    | succ t =>
        have hxBound : Nat.succ t < Nat.succ N := by
          have h := x.isLt
          rw [hxval] at h
          exact h
        have htN : t < N := Nat.lt_of_succ_lt_succ hxBound
        let i : Fin N := ⟨t, htN⟩
        have hp_le_t : p.val ≤ t := by
          have h := hpltx
          rw [hxval] at h
          exact Nat.le_of_lt_succ h
        have hnot : ¬ i.castSucc < p := by
          intro hit
          exact (Nat.not_lt_of_ge hp_le_t) hit
        refine ⟨i, ?_⟩
        unfold Fin.succAbove
        rw [if_neg hnot]
        apply Fin.ext
        exact hxval.symm

/--
Decode an element of the complement of `p` back through `p.succAbove`.
The fallback is explicit; the complement hypothesis proves below that it is
never used.
-/
def complementDecode {N : ℕ}
    (p x : Fin (N + 1)) (fallback : Fin N) : Fin N :=
  match ConstructiveFiniteInverse.findPreimage
      (fun i : Fin N => p.succAbove i) x with
  | some i => i
  | none => fallback

/-- `complementDecode` really is the inverse of `succAbove` away from the pivot. -/
theorem complementDecode_spec {N : ℕ}
    (p x : Fin (N + 1)) (fallback : Fin N)
    (hxp : x ≠ p) :
    p.succAbove (complementDecode p x fallback) = x := by
  obtain ⟨w, hw⟩ := exists_succAbove_eq_of_ne hxp
  obtain ⟨j, hj⟩ :=
    ConstructiveFiniteInverse.findPreimage_complete
      (fun i : Fin N => p.succAbove i) x ⟨w, hw⟩
  unfold complementDecode
  rw [hj]
  exact ConstructiveFiniteInverse.findPreimage_sound
    (fun i : Fin N => p.succAbove i) x j hj

/--
Primitive finite pigeonhole principle for self-maps of `Fin N`: injectivity
already forces surjectivity.
-/
theorem injective_implies_surjective :
    ∀ {N : ℕ} (f : Fin N → Fin N),
      Function.Injective f → Function.Surjective f := by
  intro N
  induction N with
  | zero =>
      intro f _hinj y
      exact Fin.elim0 y
  | succ N ih =>
      intro f hinj y
      let z : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
      let p : Fin (N + 1) := f z
      let g : Fin N → Fin N := fun i =>
        complementDecode p (f (z.succAbove i)) i
      have htail (i : Fin N) : f (z.succAbove i) ≠ p := by
        intro hf
        change f (z.succAbove i) = f z at hf
        exact succAbove_ne_pivot z i (hinj hf)
      have g_spec (i : Fin N) :
          p.succAbove (g i) = f (z.succAbove i) := by
        exact complementDecode_spec p (f (z.succAbove i)) i (htail i)
      have g_inj : Function.Injective g := by
        intro i j hij
        apply succAbove_injective z
        apply hinj
        calc
          f (z.succAbove i) = p.succAbove (g i) := (g_spec i).symm
          _ = p.succAbove (g j) := congrArg (fun q => p.succAbove q) hij
          _ = f (z.succAbove j) := g_spec j
      have g_surj : Function.Surjective g := ih g g_inj
      by_cases hy : y = p
      · refine ⟨z, ?_⟩
        change y = f z at hy
        exact hy.symm
      · obtain ⟨j, hj⟩ := exists_succAbove_eq_of_ne hy
        obtain ⟨i, hi⟩ := g_surj j
        refine ⟨z.succAbove i, ?_⟩
        calc
          f (z.succAbove i) = p.succAbove (g i) := (g_spec i).symm
          _ = p.succAbove j := congrArg (fun q => p.succAbove q) hi
          _ = y := hj

end PrimitiveFinitePigeonhole
end QuantityRepresentationFoundations
