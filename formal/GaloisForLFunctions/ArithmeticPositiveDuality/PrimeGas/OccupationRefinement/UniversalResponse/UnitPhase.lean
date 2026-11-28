import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Isometry

/-! # All conserving responses without regularity assumptions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

def unitPhase (A : ℝ → ℂ) (x : ℝ) := A x/(Real.sqrt x:ℂ)

def circleCharacter (C : ℝ → ℂ) := sequential C ∧ ∀ x ∈ Shares, ‖C x‖=1

private theorem product_mem {x y : ℝ} (hx : x∈Shares) (hy : y∈Shares) : x*y∈Shares :=
  ⟨mul_pos hx.1 hy.1,(mul_le_of_le_one_right hx.1.le hy.2).trans hx.2⟩

theorem factor (A : ℝ → ℂ) {x : ℝ} (hx : x∈Shares) :
    (Real.sqrt x:ℂ)*unitPhase A x=A x :=
  mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx.1).ne')

/-- Without any continuity requirement, all remaining freedom is exactly
a multiplicative phase of unit modulus on the positive shares. -/
theorem conserving_iff_character (A : ℝ → ℂ) :
    sequential A ∧ conserving A ↔ circleCharacter (unitPhase A) := by
  constructor
  · rintro ⟨seq,h⟩
    have B := (conserving_iff_born A seq).mp h
    constructor
    · intro x hx y hy
      rw [unitPhase,seq x hx y hy,Real.sqrt_mul hx.1.le,Complex.ofReal_mul,
        unitPhase,unitPhase,div_mul_div_comm]
    · intro x hx
      have pos := Real.sqrt_pos.mpr hx.1
      have normA : ‖A x‖=Real.sqrt x := (sq_eq_sq₀ (norm_nonneg _) pos.le).mp
        ((B x hx).trans (Real.sq_sqrt hx.1.le).symm)
      rw [unitPhase,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos,normA,div_self pos.ne']
  · rintro ⟨mult,unit⟩
    have seq : sequential A := by
      intro x hx y hy
      calc
        A (x*y) = (Real.sqrt (x*y):ℂ)*unitPhase A (x*y) := (factor A (product_mem hx hy)).symm
        _ = ((Real.sqrt x:ℂ)*unitPhase A x)*((Real.sqrt y:ℂ)*unitPhase A y) := by
          rw [Real.sqrt_mul hx.1.le,Complex.ofReal_mul,mult x hx y hy]
          ring
        _ = A x*A y := by rw [factor A hx,factor A hy]
    refine ⟨seq,conserving_of_born (fun x hx => ?_)⟩
    calc
      ‖A x‖^2 = ‖(Real.sqrt x:ℂ)*unitPhase A x‖^2 := congrArg (fun c : ℂ => ‖c‖^2) (factor A hx).symm
      _ = x := by rw [norm_mul,unit x hx,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hx.1.le]

#print axioms factor
#print axioms conserving_iff_character

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
