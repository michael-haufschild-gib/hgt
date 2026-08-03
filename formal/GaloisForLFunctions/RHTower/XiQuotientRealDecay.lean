import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.XiHedenmalmFourierEquation

/-!
# Exponential decay of the Hedenmalm removable quotient on the real axis

The centered xi function decays exponentially along the real axis, and at a Xi zero the Hedenmalm
removable quotient is that function divided by a linear factor.  Away from the removed point the
factor is bounded below, so the quotient inherits the decay; near it the quotient is continuous on a
compact set.  This is the admissibility bound that places the eigenfunction quotients in the
Guinand--Weil test class.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- **The Hedenmalm removable quotient decays exponentially on the real axis.**  Away from the
removed point it is `XiC` divided by a factor bounded below; near it the quotient is continuous on a
compact set.  This is the admissibility bound behind the Guinand--Weil test class. -/
theorem exists_norm_xiThetaEigenFourier_ofReal_le {alpha : ℂ} (halpha : XiC alpha = 0)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖xiThetaEigenFourier alpha ((t : ℝ) : ℂ)‖ ≤ C * Real.exp (-(δ * |t|)) := by
  obtain ⟨C₀, hC₀, hXi⟩ := exists_norm_XiC_ofReal_le hδ0 hδ4
  set R : ℝ := ‖alpha‖ + 1 with hR
  have hR1 : 1 ≤ R := by
    rw [hR]
    linarith [norm_nonneg alpha]
  -- bound on the compact core
  have hcont : Continuous (fun t : ℝ => ‖xiThetaEigenFourier alpha ((t : ℝ) : ℂ)‖) :=
    ((continuous_xiThetaEigenFourier alpha).comp Complex.continuous_ofReal).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C₀ (M * Real.exp (δ * R)), le_max_of_le_left hC₀, fun t => ?_⟩
  rcases le_or_gt |t| R with hsmall | hbig
  · -- compact core
    have hmem : t ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
    have hle : ‖xiThetaEigenFourier alpha ((t : ℝ) : ℂ)‖ ≤ M := by
      simpa using hM t hmem
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) hle
    have hexp : Real.exp (-(δ * R)) ≤ Real.exp (-(δ * |t|)) := by
      refine Real.exp_le_exp.mpr ?_
      have : δ * |t| ≤ δ * R := mul_le_mul_of_nonneg_left hsmall hδ0
      linarith
    calc ‖xiThetaEigenFourier alpha ((t : ℝ) : ℂ)‖ ≤ M := hle
      _ = M * Real.exp (δ * R) * Real.exp (-(δ * R)) := by
          rw [mul_assoc, ← Real.exp_add]
          simp
      _ ≤ M * Real.exp (δ * R) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ max C₀ (M * Real.exp (δ * R)) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
  · -- far field
    have hne : ((t : ℝ) : ℂ) ≠ alpha := by
      intro hc
      have : ‖((t : ℝ) : ℂ)‖ = ‖alpha‖ := by rw [hc]
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      rw [hR] at hbig
      linarith
    have hden : (1 : ℝ) ≤ ‖alpha - ((t : ℝ) : ℂ)‖ := by
      have h1 : ‖((t : ℝ) : ℂ)‖ - ‖alpha‖ ≤ ‖alpha - ((t : ℝ) : ℂ)‖ := by
        rw [norm_sub_rev]
        exact norm_sub_norm_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs] at h1
      rw [hR] at hbig
      linarith
    rw [xiThetaEigenFourier_eq_div halpha hne, norm_div, norm_mul, norm_neg, Complex.norm_I,
      one_mul]
    have hdiv : ‖XiC ((t : ℝ) : ℂ)‖ / ‖alpha - ((t : ℝ) : ℂ)‖ ≤ ‖XiC ((t : ℝ) : ℂ)‖ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (XiC ((t : ℝ) : ℂ))]
    calc ‖XiC ((t : ℝ) : ℂ)‖ / ‖alpha - ((t : ℝ) : ℂ)‖ ≤ ‖XiC ((t : ℝ) : ℂ)‖ := hdiv
      _ ≤ C₀ * Real.exp (-(δ * |t|)) := hXi t
      _ ≤ max C₀ (M * Real.exp (δ * R)) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)

end RHTower
