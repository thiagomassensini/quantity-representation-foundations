import QuantityRepresentationFoundations.ConstructiveFiniteInverse

/-!
# Primitive finite pigeonhole principle

This module proves the exact finite self-map statement needed by the
constructive capacity route without passing through `Fintype.card`.

The proof removes one explicit source slot and its image target slot.  The
remaining `Fin N → Fin N` map is handled inductively.  Inverting
`Fin.succAbove` on the complement is performed by the already axiom-free
structural finite search, rather than by choosing a witness from an existential.
-/

namespace QuantityRepresentationFoundations
namespace PrimitiveFinitePigeonhole

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
  obtain ⟨w, hw⟩ := Fin.exists_succAbove_eq hxp
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
        have hdom : z.succAbove i = z := by
          apply hinj
          simpa [p] using hf
        exact (Fin.succAbove_ne z i) hdom
      have g_spec (i : Fin N) :
          p.succAbove (g i) = f (z.succAbove i) := by
        exact complementDecode_spec p (f (z.succAbove i)) i (htail i)
      have g_inj : Function.Injective g := by
        intro i j hij
        apply Fin.succAbove_right_injective
        apply hinj
        calc
          f (z.succAbove i) = p.succAbove (g i) := (g_spec i).symm
          _ = p.succAbove (g j) := congrArg (fun q => p.succAbove q) hij
          _ = f (z.succAbove j) := g_spec j
      have g_surj : Function.Surjective g := ih g g_inj
      by_cases hy : y = p
      · refine ⟨z, ?_⟩
        simpa [p] using hy.symm
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hy
        obtain ⟨i, hi⟩ := g_surj j
        refine ⟨z.succAbove i, ?_⟩
        calc
          f (z.succAbove i) = p.succAbove (g i) := (g_spec i).symm
          _ = p.succAbove j := congrArg (fun q => p.succAbove q) hi
          _ = y := hj

end PrimitiveFinitePigeonhole
end QuantityRepresentationFoundations
