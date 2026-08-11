import GaloisForLFunctions.HTGeometry.ActivePhaseLattice

/-!
# Mean values of the characters of a product torus

A nontrivial character of the product torus integrates to zero: translating by
a point where the character is not `1` multiplies the integral by that value,
and Haar measure is translation invariant.

Consequently the Fourier coefficients of a character are the Kronecker delta,
and — since the measure is a probability measure — every Fourier coefficient is
bounded by the supremum of the function.
-/

open Complex Set Filter Topology MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance isProbabilityMeasureCircleTorusCharacterMean : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance isAddHaarMeasureCircleTorusCharacterMean : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### A nontrivial character is somewhere different from one -/

theorem exists_mFourier_ne_one {n : d → ℤ} (hn : n ≠ 0) :
    ∃ y : UnitAddTorus d, UnitAddTorus.mFourier n y ≠ 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra hc
    exact hn (funext fun j => not_not.1 fun h => hc ⟨j, h⟩)
  refine ⟨Pi.single j (((1 / (2 * (n j : ℝ)) : ℝ) : UnitAddCircle)), ?_⟩
  have hval : UnitAddTorus.mFourier n
      (Pi.single j (((1 / (2 * (n j : ℝ)) : ℝ) : UnitAddCircle))) = -1 := by
    rw [UnitAddTorus.mFourier]
    show (∏ i : d, fourier (n i)
      ((Pi.single j (((1 / (2 * (n j : ℝ)) : ℝ) : UnitAddCircle)) : d → UnitAddCircle) i)) = -1
    rw [Finset.prod_eq_single j]
    · rw [Pi.single_eq_same, fourier_coe_apply]
      have hne : ((n j : ℂ)) ≠ 0 := Int.cast_ne_zero.2 hj
      have harg : 2 * (Real.pi : ℂ) * I * (n j : ℂ) *
          ((1 / (2 * (n j : ℝ)) : ℝ) : ℂ) / ((1 : ℝ) : ℂ) = (Real.pi : ℂ) * I := by
        push_cast
        field_simp
      rw [harg, Complex.exp_pi_mul_I]
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, fourier_eval_zero]
    · intro hj'
      exact absurd (Finset.mem_univ j) hj'
  rw [hval]
  intro h
  exact absurd h (by norm_num)

/-! ### The mean of a character -/

/-- **A nontrivial character of the product torus has mean zero.** -/
theorem integral_mFourier (n : d → ℤ) :
    ∫ x : UnitAddTorus d, UnitAddTorus.mFourier n x = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    have hone : (fun x : UnitAddTorus d => UnitAddTorus.mFourier (0 : d → ℤ) x)
        = fun _ => (1 : ℂ) := by
      funext x
      rw [UnitAddTorus.mFourier_zero]
      rfl
    rw [hone, integral_const]
    simp
  · rw [if_neg hn]
    obtain ⟨y, hy⟩ := exists_mFourier_ne_one hn
    set I : ℂ := ∫ x : UnitAddTorus d, UnitAddTorus.mFourier n x with hI
    have hshift : I = UnitAddTorus.mFourier n y * I := by
      calc I = ∫ x : UnitAddTorus d, UnitAddTorus.mFourier n (y + x) :=
            (integral_add_left_eq_self (fun x => UnitAddTorus.mFourier n x) y).symm
        _ = ∫ x : UnitAddTorus d,
              UnitAddTorus.mFourier n y * UnitAddTorus.mFourier n x := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            show UnitAddTorus.mFourier n (y + x) = _
            rw [mFourier_add_point]
        _ = UnitAddTorus.mFourier n y * I := by rw [integral_const_mul]
    have hfac : (1 - UnitAddTorus.mFourier n y) * I = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    have hne : (1 : ℂ) - UnitAddTorus.mFourier n y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    exact (mul_eq_zero.1 hfac).resolve_left hne

/-- **The Fourier coefficients of a character are the Kronecker delta.** -/
theorem mFourierCoeff_mFourier (m n : d → ℤ) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier m) n = if n = m then 1 else 0 := by
  have hprod : (fun x : UnitAddTorus d =>
      UnitAddTorus.mFourier (-n) x • UnitAddTorus.mFourier m x)
      = fun x => UnitAddTorus.mFourier (m + -n) x := by
    funext x
    rw [smul_eq_mul, UnitAddTorus.mFourier_add]
    ring
  rw [UnitAddTorus.mFourierCoeff, hprod, integral_mFourier]
  by_cases h : n = m
  · rw [if_pos h, if_pos]
    rw [h, add_neg_cancel]
  · rw [if_neg h, if_neg]
    intro hc
    exact h (by rw [← neg_neg n, ← neg_eq_of_add_eq_zero_left hc])

/-! ### The size of a Fourier coefficient -/

omit [DecidableEq d] in
/-- **A Fourier coefficient is bounded by the supremum of the function.** -/
theorem norm_mFourierCoeff_le {g : UnitAddTorus d → ℂ} {C : ℝ}
    (hg : ∀ x, ‖g x‖ ≤ C) (m : d → ℤ) :
    ‖UnitAddTorus.mFourierCoeff g m‖ ≤ C := by
  have hbound : ∀ x : UnitAddTorus d,
      ‖UnitAddTorus.mFourier (-m) x • g x‖ ≤ C := by
    intro x
    rw [smul_eq_mul, norm_mul, norm_mFourier_apply, one_mul]
    exact hg x
  have := norm_integral_le_of_norm_le_const
    (μ := (volume : Measure (UnitAddTorus d)))
    (C := C) (Eventually.of_forall hbound)
  rw [UnitAddTorus.mFourierCoeff]
  simpa using this

end

end GaloisForLFunctions.HTGeometry
