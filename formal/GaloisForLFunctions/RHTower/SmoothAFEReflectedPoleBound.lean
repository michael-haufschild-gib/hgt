import GaloisForLFunctions.RHTower.SmoothAFEZetaRightReflectedPrimal
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound

open Complex
noncomputable section
namespace RHTower

/-- The actual reflected pole correction stays bounded when smoothing is below the height.
Its denominator is retained; no pole term is discarded from the AFE. -/
theorem exists_norm_reflectedShiftedPole_le_conductor
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → ∀ tau : ℝ, N ≤ tau →
      ‖zetaChi (rightDisplacedLinePt d tau) *
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d (-tau)) N‖ ≤ C := by
  obtain ⟨K, hK, hchi⟩ := exists_norm_zetaChi_fixed_right_line_le_rpow hd hdhalf
  let E := Real.exp ((1 / 2 + d) ^ 2)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨K * E, mul_nonneg hK hE.le, ?_⟩
  intro N hN tau hNt
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have htpos : 0 < tau := hNpos.trans_le hNt
  have hmax : max 1 |tau| = tau := by
    rw [abs_of_pos htpos, max_eq_right (hN.trans hNt)]
  have hchiN : ‖zetaChi (rightDisplacedLinePt d tau)‖ ≤ K / N ^ d := by
    have h := hchi tau
    rw [hmax] at h
    exact h.trans (div_le_div_of_nonneg_left hK
      (Real.rpow_pos_of_pos hNpos _) (Real.rpow_le_rpow hNpos.le hNt hd.le))
  have hre : (1 - displacedLinePt d (-tau)).re = 1 / 2 + d := by
    simp only [Complex.sub_re, Complex.one_re, displacedLinePt_re]
    ring
  have him : (1 - displacedLinePt d (-tau)).im = tau := by
    simp [displacedLinePt]
  have hden : N ≤ ‖1 - displacedLinePt d (-tau)‖ := by
    have h := Complex.abs_im_le_norm (1 - displacedLinePt d (-tau))
    rw [him, abs_of_pos htpos] at h
    exact hNt.trans h
  have hexp : ‖Complex.exp ((1 - displacedLinePt d (-tau)) ^ 2)‖ ≤ E := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [pow_two, Complex.mul_re, hre, him]
    nlinarith [sq_nonneg tau]
  have hpow : N ^ (1 / 2 + d) ≤ N ^ (1 + d) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hres : ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d (-tau)) N‖ ≤
      N ^ (1 + d) * E / N := by
    rw [smoothAFEZetaShiftedPoleResidue, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hNpos, hre]
    apply (div_le_div_of_nonneg_right
      (mul_le_mul hpow hexp (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans
    exact div_le_div_of_nonneg_left (by positivity) hNpos hden
  rw [norm_mul]
  calc
    _ ≤ (K / N ^ d) * (N ^ (1 + d) * E / N) :=
      mul_le_mul hchiN hres (norm_nonneg _) (by positivity)
    _ = K * E := by
      rw [Real.rpow_add hNpos, Real.rpow_one]
      field_simp

end RHTower
