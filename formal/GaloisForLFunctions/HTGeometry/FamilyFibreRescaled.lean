import GaloisForLFunctions.HTGeometry.SaturatedFibreStep
import GaloisForLFunctions.HTGeometry.WeightScaleGraded

/-!
# The nonzero fibre of the family ideal is the rescaled ideal

```text
map_famEval_familyIdeal   ** evaluating the family ideal at a nonzero point of the base line gives
                             the image of the ideal under the weight rescaling **
map_famEval_ofList_C      and the adjoined constants evaluate to themselves
```

`eval_homogenize` says this generator by generator, up to an invertible scalar; the two containments
are then the two directions of that identity.

Together with `map_famEval_zero_familyIdeal` — the special fibre is the initial ideal — this is the
whole geometric content of the degeneration: one family whose fibre over `0` is the monomial
degeneration and whose fibre over every other point is a rescaled copy of the ideal itself.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **The fibre of the family ideal over a nonzero point is the rescaled ideal.** -/
theorem map_famEval_familyIdeal (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0)
    (I : Ideal (MvPolynomial σ K)) :
    Ideal.map (famEval (MvPolynomial.C lam)) (familyIdeal w I)
      = Ideal.map (weightScaleEquiv w hlam : MvPolynomial σ K →+* MvPolynomial σ K) I := by
  refine le_antisymm ?_ ?_
  · rw [familyIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨F, ⟨f, hf, hf0, rfl⟩, rfl⟩
    show Polynomial.eval (MvPolynomial.C lam) (homogenize w f) ∈ _
    rw [eval_homogenize w hlam f]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hf)
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show (weightScaleEquiv w hlam) f ∈ Ideal.map (famEval (MvPolynomial.C lam)) (familyIdeal w I)
    by_cases hf0 : f = 0
    · rw [hf0, map_zero]
      exact Ideal.zero_mem _
    have hev : Polynomial.eval (MvPolynomial.C lam) (homogenize w f)
        ∈ Ideal.map (famEval (MvPolynomial.C lam)) (familyIdeal w I) :=
      Ideal.mem_map_of_mem _ (homogenize_mem_familyIdeal hf hf0)
    have hmul := Ideal.mul_mem_left
      (Ideal.map (famEval (MvPolynomial.C lam)) (familyIdeal w I))
      (MvPolynomial.C (lam ^ (minWeight w f))) hev
    rw [eval_homogenize w hlam f, ← mul_assoc, ← map_mul, ← zpow_add₀ hlam,
      add_neg_cancel, zpow_zero, map_one, one_mul] at hmul
    exact hmul

/-- Adjoined scalar constants evaluate to themselves in every fibre. -/
theorem map_famEval_ofList_C (a : MvPolynomial σ K) (ls : List (MvPolynomial σ K)) :
    Ideal.map (famEval a) (Ideal.ofList (ls.map Polynomial.C)) = Ideal.ofList ls := by
  classical
  rw [Ideal.ofList, Ideal.ofList, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    show famEval a (Polynomial.C z) ∈ {r | r ∈ ls}
    simpa [famEval] using hz
  · intro hx
    exact ⟨Polynomial.C x, List.mem_map.mpr ⟨x, hx, rfl⟩, by simp [famEval]⟩

end GaloisForLFunctions.HTGeometry
