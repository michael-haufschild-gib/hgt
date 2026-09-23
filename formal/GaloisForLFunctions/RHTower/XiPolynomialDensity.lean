import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic
import GaloisForLFunctions.RHTower.XiCSchwartzRestriction
import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip

/-!
# Polynomial multiples of the centered xi function are dense in `L^(2 : ℕ)`

The real restriction of the centered xi function decays exponentially and vanishes only on a null
set.  Hence a square-integrable function orthogonal to every polynomial multiple of it has all
polynomial moments of `f XiC` equal to zero, and the exponentially weighted determinacy theorem
forces `f XiC` to vanish almost everywhere; dividing by `XiC` leaves `f = 0` almost everywhere.

Only weighted integrability of `f XiC` is used --- a pointwise exponential bound is false for a
merely square-integrable `f`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem expWeightIntegrable_memLp_mul_XiC {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ExpWeightIntegrable (fun x : ℝ => f x * XiC ((x : ℝ) : ℂ)) δ := by
  intro a ha
  obtain ⟨C, hC, hbound⟩ := exists_norm_XiC_ofReal_le hδ0 hδ4
  have hmaj := integrable_memLp_mul_XiC_mul_expWeight ha hf
  refine Integrable.mono' (hmaj.const_mul C) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((hf.aestronglyMeasurable.mul
      continuous_XiC_ofReal.aestronglyMeasurable).norm).mul (by fun_prop)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    calc ‖f x‖ * ‖XiC ((x : ℝ) : ℂ)‖ * Real.exp (a * |x|)
        ≤ ‖f x‖ * (C * Real.exp (-(δ * |x|))) * Real.exp (a * |x|) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
      _ = C * (‖f x‖ * (Real.exp (-(δ * |x|)) * Real.exp (a * |x|))) := by ring

/-- **The polynomial multiples of the centered xi function have dense span in `L^(2 : ℕ)`.**  Stated in
the orthogonality form: a square-integrable function orthogonal to every polynomial multiple of the
real restriction of `XiC` vanishes almost everywhere. -/
theorem ae_eq_zero_of_orthogonal_polynomial_XiC {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (horth : ∀ n : ℕ, (∫ x : ℝ, f x * ((x : ℂ) ^ n * XiC ((x : ℝ) : ℂ))) = 0) :
    f =ᵐ[volume] 0 := by
  set δ : ℝ := Real.pi / 8 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδ0 : 0 ≤ δ := le_of_lt hδpos
  have hδ4 : 2 * δ < Real.pi / 2 := by
    rw [hδdef]
    linarith [Real.pi_pos]
  set g : ℝ → ℂ := fun x => f x * XiC ((x : ℝ) : ℂ) with hgdef
  have hmeas : AEStronglyMeasurable g volume :=
    hf.aestronglyMeasurable.mul continuous_XiC_ofReal.aestronglyMeasurable
  have hgw : ExpWeightIntegrable g δ := expWeightIntegrable_memLp_mul_XiC hδ0 hδ4 hf
  have hmom : ∀ n : ℕ, (∫ x : ℝ, g x * (x : ℂ) ^ n) = 0 := by
    intro n
    rw [← horth n]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hgdef]
    ring
  have hgzero := ae_eq_zero_of_moments_eq_zero' hmeas hδpos hgw hmom
  filter_upwards [hgzero, XiC_ofReal_ne_zero_ae] with x hx hne
  have hprod : f x * XiC ((x : ℝ) : ℂ) = 0 := hx
  rcases mul_eq_zero.mp hprod with h | h
  · exact h
  · exact absurd h hne

end RHTower
