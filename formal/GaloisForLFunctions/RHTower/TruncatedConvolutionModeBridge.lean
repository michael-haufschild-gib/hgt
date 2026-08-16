import GaloisForLFunctions.RHTower.TruncatedConvolutionParityPacket
import GaloisForLFunctions.HTGeometry.TruncatedConvolutionFormBound

/-!
# The centered parity index is the symmetric mode window

Summing over the centered parity index is summing over the symmetric window of integer modes, and
the odd frame is the odd coefficient sequence in those coordinates.  Rescaling the unit interval to
`[0, 2π]` then turns a trigonometric polynomial in the exponential basis into the trigonometric
polynomial of the parity-free odd-ground law.
-/

open Matrix

open scoped Matrix ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem ccmParityCenteredMode_injective (N : ℕ) :
    Function.Injective (ccmParityCenteredMode N) := by
  intro a b hab
  refine ccmParityCenteredClock_injective N ?_
  rw [ccmParityCenteredClock, ccmParityCenteredClock, hab]

theorem ccmParityCenteredMode_mem (N : ℕ) (i : CCMCenteredParityIndex N) :
    ccmParityCenteredMode N i ∈ ccmModeWindow N := by
  rw [ccmModeWindow, Finset.mem_Icc]
  rcases i with _ | ⟨k, b⟩
  · simp [ccmParityCenteredMode]
  · have hk : (k : ℕ) < N := k.2
    cases b <;> simp only [ccmParityCenteredMode] <;> omega

theorem image_ccmParityCenteredMode (N : ℕ) :
    Finset.image (ccmParityCenteredMode N) Finset.univ = ccmModeWindow N := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hj
    exact ccmParityCenteredMode_mem N i
  · rw [Finset.card_image_of_injective _ (ccmParityCenteredMode_injective N), Finset.card_univ,
      ccmModeWindow, Int.card_Icc]
    simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega

theorem sum_ccmParityCenteredMode {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℤ → M) :
    ∑ i : CCMCenteredParityIndex N, F (ccmParityCenteredMode N i)
      = ∑ j ∈ ccmModeWindow N, F j := by
  rw [← image_ccmParityCenteredMode N,
    Finset.sum_image (fun a _ b _ h => ccmParityCenteredMode_injective N h)]

/-- The odd frame in mode coordinates is the odd coefficient sequence. -/
theorem ccmOddGroundCoeff_mode (N : ℕ) (c : Fin N → ℂ) (i : CCMCenteredParityIndex N) :
    ccmOddGroundCoeff N c (ccmParityCenteredMode N i) = (ccmOddParityFrame N *ᵥ c) i := by
  rcases i with _ | ⟨k, b⟩
  · simp only [ccmParityCenteredMode, ccmOddGroundCoeff_zero]
    rw [Matrix.mulVec, dotProduct]
    simp [ccmOddParityFrame]
  · have hk : (k : ℕ) < N := k.2
    have hmul : (ccmOddParityFrame N *ᵥ c) (some (k, b))
        = (if b then -ccmParityFrameScale else ccmParityFrameScale) * c k := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single k]
      · cases b <;> simp [ccmOddParityFrame]
      · intro l _ hlk
        cases b <;> simp [ccmOddParityFrame, Ne.symm hlk]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hmul]
    cases b
    · rw [ccmParityCenteredMode, ccmOddGroundCoeff, if_pos (by omega)]
      simp only [ccmOddGroundCoeffAux]
      rw [show ((((k : ℕ) + 1 : ℕ) : ℤ)).toNat - 1 = (k : ℕ) by omega, dif_pos hk]
      simp
    · rw [ccmParityCenteredMode, ccmOddGroundCoeff, if_neg (by omega), if_pos (by omega)]
      simp only [ccmOddGroundCoeffAux]
      rw [show (-(-((((k : ℕ) + 1 : ℕ) : ℤ)))).toNat - 1 = (k : ℕ) by omega, dif_pos hk]
      simp

/-- Rescaling the unit interval to `[0, 2π]` turns the exponential trigonometric polynomial into
the trigonometric polynomial of the parity-free law. -/
theorem indexTrigPoly_eq_ccmTrigPoly (N : ℕ) (c : Fin N → ℂ) (theta : ℝ) :
    indexTrigPoly (ccmParityCenteredMode N) (ccmOddParityFrame N *ᵥ c)
        (theta / (2 * Real.pi))
      = ccmTrigPoly N (ccmOddGroundCoeff N c) theta := by
  rw [indexTrigPoly, ccmTrigPoly, ← sum_ccmParityCenteredMode N
    (fun j => ccmOddGroundCoeff N c j * Complex.exp (Complex.I * ((j : ℂ) * (theta : ℂ))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ccmOddGroundCoeff_mode]
  congr 1
  rw [fourierChar]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- The mean-square error on `[0, 2π]` is `2π` times the mean-square error on the unit interval. -/
theorem integral_ccmTrigPoly_sub_sq (N : ℕ) (c : Fin N → ℂ) (xi : ℝ → ℂ) :
    (∫ theta in (0 : ℝ)..(2 * Real.pi),
        ‖ccmTrigPoly N (ccmOddGroundCoeff N c) theta - xi (theta / (2 * Real.pi))‖ ^ 2)
      = (2 * Real.pi) * l2NormSq (fun x =>
          indexTrigPoly (ccmParityCenteredMode N) (ccmOddParityFrame N *ᵥ c) x - xi x) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  set g : ℝ → ℝ := fun theta =>
    ‖ccmTrigPoly N (ccmOddGroundCoeff N c) theta - xi (theta / (2 * Real.pi))‖ ^ 2 with hg
  have harg : ∀ x : ℝ, (2 * Real.pi * x) / (2 * Real.pi) = x := by
    intro x
    field_simp
  have hscale : ∀ x : ℝ, g (2 * Real.pi * x)
      = ‖indexTrigPoly (ccmParityCenteredMode N) (ccmOddParityFrame N *ᵥ c) x - xi x‖ ^ 2 := by
    intro x
    rw [hg]
    simp only
    rw [harg x, ← indexTrigPoly_eq_ccmTrigPoly N c (2 * Real.pi * x), harg x]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := (1 : ℝ)) g hpi
  rw [mul_zero, mul_one] at hcomp
  have hkey : (∫ x in (0 : ℝ)..1,
      ‖indexTrigPoly (ccmParityCenteredMode N) (ccmOddParityFrame N *ᵥ c) x - xi x‖ ^ 2)
      = ∫ x in (0 : ℝ)..1, g (2 * Real.pi * x) :=
    intervalIntegral.integral_congr fun x _ => (hscale x).symm
  rw [l2NormSq, hkey, hcomp, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]

end

end RHTower
