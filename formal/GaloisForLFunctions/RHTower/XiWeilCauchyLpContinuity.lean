import GaloisForLFunctions.RHTower.XiWeilCauchyPoleExhaustion
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Norm continuity of the Xi-divisor Cauchy evaluation map

The regular Cauchy vector depends continuously in `ell^(2 : ℕ)` on its pole.  The proof is uniform over
the complete multiplicity-exact Xi divisor: local zero isolation gives one denominator gap, and
the fixed Cauchy square-summability supplies a Tannery majorant.

This is the analytic bridge needed to replace conjugate-colliding Cauchy packets by separated
packets without changing their Hilbert limit.
-/

open Complex Metric Function Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- Sequential norm continuity of the regular Cauchy evaluation vector on the Xi divisor. -/
theorem tendsto_xiWeilCauchyLp
    {z : ℕ → XiCRegularPoint} {z₀ : XiCRegularPoint}
    (hz : Tendsto (fun n ↦ (z n : ℂ)) atTop (nhds (z₀ : ℂ))) :
    Tendsto (fun n ↦ xiWeilCauchyLp (z n)) atTop
      (nhds (xiWeilCauchyLp z₀)) := by
  obtain ⟨delta, hdelta, hgap⟩ := exists_xiSpectralPoint_gap (z₀ : ℂ)
  have hnear : ∀ᶠ n in atTop, ‖(z n : ℂ) - (z₀ : ℂ)‖ ≤ delta / 2 := by
    have hball : ∀ᶠ n in atTop, (z n : ℂ) ∈ closedBall (z₀ : ℂ) (delta / 2) :=
      hz.eventually (Metric.closedBall_mem_nhds (z₀ : ℂ) (half_pos hdelta))
    filter_upwards [hball] with n hn
    simpa [Metric.mem_closedBall, dist_eq_norm] using hn
  let term : ℕ → XiZeroCopy → ℝ := fun n q ↦
    ‖xiWeilCauchyTest (z n : ℂ) (xiSpectralPoint q) -
      xiWeilCauchyTest (z₀ : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ)
  let bound : XiZeroCopy → ℝ := fun q ↦
    9 * ‖xiWeilCauchyTest (z₀ : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ)
  have hboundsum : Summable bound :=
    (XiWeilSquareSummable_cauchy (z₀ : ℂ)).mul_left 9
  have hterm_tend : ∀ q, Tendsto (fun n ↦ term n q) atTop (nhds 0) := by
    intro q
    have hden : xiSpectralPoint q - (z₀ : ℂ) ≠ 0 := by
      intro heq
      apply z₀.property
      apply (XiC_eq_zero_iff_exists_xiZeroCopy (z₀ : ℂ)).mpr
      exact ⟨q, sub_eq_zero.mp heq⟩
    have hdenT : Tendsto
        (fun n ↦ xiSpectralPoint q - (z n : ℂ)) atTop
        (nhds (xiSpectralPoint q - (z₀ : ℂ))) :=
      tendsto_const_nhds.sub hz
    have hinv : Tendsto
        (fun n ↦ (xiSpectralPoint q - (z n : ℂ))⁻¹) atTop
        (nhds ((xiSpectralPoint q - (z₀ : ℂ))⁻¹)) :=
      hdenT.inv₀ hden
    have hconst : Tendsto
        (fun _ : ℕ ↦ (xiSpectralPoint q - (z₀ : ℂ))⁻¹) atTop
        (nhds ((xiSpectralPoint q - (z₀ : ℂ))⁻¹)) := tendsto_const_nhds
    simpa [term, xiWeilCauchyTest] using (hinv.sub hconst).norm.pow 2
  have hbound : ∀ᶠ n in atTop, ∀ q, ‖term n q‖ ≤ bound q := by
    filter_upwards [hnear] with n hn
    intro q
    have hqne : xiSpectralPoint q ≠ (z₀ : ℂ) := by
      intro hq
      apply z₀.property
      exact (XiC_eq_zero_iff_exists_xiZeroCopy (z₀ : ℂ)).mpr ⟨q, hq⟩
    have hqgap := hgap q hqne
    have hhalf : ‖xiSpectralPoint q - (z₀ : ℂ)‖ / 2 ≤
        ‖xiSpectralPoint q - (z n : ℂ)‖ := by
      have hrev := norm_sub_norm_le
        (xiSpectralPoint q - (z₀ : ℂ)) ((z n : ℂ) - (z₀ : ℂ))
      have hid : (xiSpectralPoint q - (z₀ : ℂ)) -
          ((z n : ℂ) - (z₀ : ℂ)) = xiSpectralPoint q - (z n : ℂ) := by ring
      rw [hid] at hrev
      linarith
    have hqpos : 0 < ‖xiSpectralPoint q - (z₀ : ℂ)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hqne)
    have hninv :
        ‖xiWeilCauchyTest (z n : ℂ) (xiSpectralPoint q)‖ ≤
          2 / ‖xiSpectralPoint q - (z₀ : ℂ)‖ := by
      rw [xiWeilCauchyTest, norm_inv]
      rw [show ‖xiSpectralPoint q - (z n : ℂ)‖⁻¹ =
          1 / ‖xiSpectralPoint q - (z n : ℂ)‖ by rw [one_div]]
      exact (one_div_le_one_div_of_le (half_pos hqpos) hhalf).trans_eq (by field_simp)
    have h₀inv :
        ‖xiWeilCauchyTest (z₀ : ℂ) (xiSpectralPoint q)‖ =
          1 / ‖xiSpectralPoint q - (z₀ : ℂ)‖ := by
      rw [xiWeilCauchyTest, norm_inv, one_div]
    have hdiff :
        ‖xiWeilCauchyTest (z n : ℂ) (xiSpectralPoint q) -
          xiWeilCauchyTest (z₀ : ℂ) (xiSpectralPoint q)‖ ≤
          3 / ‖xiSpectralPoint q - (z₀ : ℂ)‖ := by
      calc
        _ ≤ ‖xiWeilCauchyTest (z n : ℂ) (xiSpectralPoint q)‖ +
            ‖xiWeilCauchyTest (z₀ : ℂ) (xiSpectralPoint q)‖ := norm_sub_le _ _
        _ ≤ 2 / ‖xiSpectralPoint q - (z₀ : ℂ)‖ +
            1 / ‖xiSpectralPoint q - (z₀ : ℂ)‖ := by
              exact add_le_add hninv h₀inv.le
        _ = 3 / ‖xiSpectralPoint q - (z₀ : ℂ)‖ := by ring
    dsimp only [term, bound]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hdiff 2
    rw [h₀inv]
    calc
      _ ≤ (3 / ‖xiSpectralPoint q - (z₀ : ℂ)‖) ^ (2 : ℕ) := hsq
      _ = 9 * (1 / ‖xiSpectralPoint q - (z₀ : ℂ)‖) ^ (2 : ℕ) := by ring
  have htsum : Tendsto (fun n ↦ ∑' q, term n q) atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hboundsum hterm_tend hbound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnormsq : ∀ n, ‖xiWeilCauchyLp (z n) - xiWeilCauchyLp z₀‖ ^ (2 : ℕ) =
      ∑' q, term n q := by
    intro n
    rw [HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro q
    rfl
  have hsqzero : Tendsto
      (fun n ↦ ‖xiWeilCauchyLp (z n) - xiWeilCauchyLp z₀‖ ^ (2 : ℕ))
      atTop (nhds 0) := htsum.congr' (Eventually.of_forall fun n ↦ (hnormsq n).symm)
  have hsqrt := hsqzero.sqrt
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

end

end RHTower
