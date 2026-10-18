import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenEquality
import GaloisForLFunctions.RHTower.FermiNymanCorrelationJets
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The Balazard–Saias–Yor identity as a convergent zero series

The radial Jensen identity in `ZetaCriticalLineJensenEquality` gives the boundary integral
as a limit of finite divisor sums. Nonnegative finite-sum domination proves summability
of the limiting disc weights and identifies their sum. The Cayley map then transports
both the zeros and their analytic multiplicities to `Re ρ > 1/2`.

`hasSum_log_norm_rightZetaZeros` records convergence as well as the value of the series;
`integral_log_norm_zeta_criticalLine_eq_tsum_rightZeros` is the literal BSY identity.
Neither theorem assumes RH or a zero-summability hypothesis.
-/

open Complex Metric Filter Topology MeasureTheory Set

namespace RHTower
noncomputable section

private def bsyDiscMultiplicity := MeromorphicOn.divisor zetaDisc (ball (0 : ℂ) 1)

private def bsyDiscWeight (u : ℂ) : ℝ :=
  (bsyDiscMultiplicity u : ℝ) * Real.log ‖u‖⁻¹

private def bsyRadialWeight (r : ℝ) (u : ℂ) : ℝ :=
  (MeromorphicOn.divisor zetaDisc (closedBall (0 : ℂ) |r|) u : ℝ) *
    Real.log (r * ‖u‖⁻¹)

private theorem bsy_analytic : AnalyticOnNhd ℂ zetaDisc (ball (0 : ℂ) 1) := by
  intro u hu
  apply analyticAt_zetaDisc
  rintro rfl
  simp at hu

private theorem bsyMultiplicity_nonneg (u : ℂ) : 0 ≤ bsyDiscMultiplicity u :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg bsy_analytic u

private theorem bsyWeight_nonneg (u : ℂ) : 0 ≤ bsyDiscWeight u := by
  by_cases hu : u ∈ ball (0 : ℂ) 1
  · rcases eq_or_ne u 0 with rfl | hu0
    · simp [bsyDiscWeight]
    · apply mul_nonneg (by exact_mod_cast bsyMultiplicity_nonneg u)
      apply Real.log_nonneg
      rw [one_le_inv₀ (norm_pos_iff.mpr hu0)]
      exact (mem_ball_zero_iff.mp hu).le
  · simp [bsyDiscWeight, bsyDiscMultiplicity,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

private theorem bsyRadial_finite (r : ℝ) : Function.HasFiniteSupport (bsyRadialWeight r) := by
  apply (MeromorphicOn.divisor zetaDisc (closedBall (0 : ℂ) |r|)).finiteSupport
    (isCompact_closedBall 0 |r|) |>.subset
  intro u hu
  contrapose! hu
  simp_all [Function.mem_support, bsyRadialWeight]

private theorem bsyRadial_nonneg {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (u : ℂ) :
    0 ≤ bsyRadialWeight r u := by
  have ha := analyticOnNhd_zetaDisc_closedBall (r := |r|)
    (by simpa only [abs_of_pos hr.1] using hr.2)
  by_cases hu : u ∈ closedBall (0 : ℂ) |r|
  · apply mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha u)
    rcases eq_or_ne u 0 with rfl | hu0
    · simp
    · apply Real.log_nonneg
      rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.mpr hu0)]
      simpa [mem_closedBall, dist_zero_right, abs_of_pos hr.1] using hu
  · simp [bsyRadialWeight, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

private theorem bsyRadial_eq {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) {u : ℂ}
    (hu : ‖u‖ ≤ r) :
    bsyRadialWeight r u = (bsyDiscMultiplicity u : ℝ) * Real.log (r * ‖u‖⁻¹) := by
  have ha := analyticOnNhd_zetaDisc_closedBall (r := |r|)
    (by simpa only [abs_of_pos hr.1] using hr.2)
  have hc : u ∈ closedBall (0 : ℂ) |r| := by
    simpa [mem_closedBall, dist_zero_right, abs_of_pos hr.1] using hu
  have hb : u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hu.trans_lt hr.2)
  simp only [bsyRadialWeight, bsyDiscMultiplicity,
    MeromorphicOn.divisor_apply ha.meromorphicOn hc,
    MeromorphicOn.divisor_apply bsy_analytic.meromorphicOn hb]

private theorem bsyRadial_le {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (u : ℂ) :
    bsyRadialWeight r u ≤ bsyDiscWeight u := by
  by_cases hu : ‖u‖ ≤ r
  · rw [bsyRadial_eq hr hu]
    apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast bsyMultiplicity_nonneg u)
    rcases eq_or_ne u 0 with rfl | hu0
    · simp
    · apply Real.log_le_log (mul_pos hr.1 (inv_pos.mpr (norm_pos_iff.mpr hu0)))
      exact mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg u)) hr.2.le
  · have hc : u ∉ closedBall (0 : ℂ) |r| := by
      simpa [mem_closedBall, dist_zero_right, abs_of_pos hr.1] using hu
    simpa [bsyRadialWeight,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc] using bsyWeight_nonneg u

private theorem tendsto_bsyRadial (u : ℂ) :
    Tendsto (fun r => bsyRadialWeight r u) (𝓝[<] (1 : ℝ)) (𝓝 (bsyDiscWeight u)) := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [bsyRadialWeight, bsyDiscWeight]
  by_cases hu : ‖u‖ < 1
  · have ht : Tendsto (fun r : ℝ => (bsyDiscMultiplicity u : ℝ) * Real.log (r * ‖u‖⁻¹))
        (𝓝[<] 1) (𝓝 (bsyDiscWeight u)) := by
      have h := ((tendsto_nhdsWithin_of_tendsto_nhds (s := Iio (1 : ℝ))
        (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 1) (𝓝 1))).mul_const ‖u‖⁻¹).log
        (by simpa using inv_ne_zero (norm_ne_zero_iff.mpr hu0))
      simpa [bsyDiscWeight] using h.const_mul (bsyDiscMultiplicity u : ℝ)
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsLT hu] with r hr
    exact (bsyRadial_eq ⟨(norm_nonneg u).trans_lt hr.1,hr.2⟩ hr.1.le).symm
  · have hb : u ∉ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using hu
    have hw : bsyDiscWeight u = 0 := by
      simp [bsyDiscWeight, bsyDiscMultiplicity,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb]
    rw [hw]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hc : u ∉ closedBall (0 : ℂ) |r| := by
      simp only [mem_closedBall, dist_zero_right, abs_of_pos hr.1]
      exact not_le.mpr (hr.2.trans_le (not_lt.mp hu))
    simp [bsyRadialWeight, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc]

private theorem tendsto_bsyRadial_sum :
    Tendsto (fun r => ∑ᶠ u, bsyRadialWeight r u) (𝓝[<] (1 : ℝ))
      (𝓝 ((2 * Real.pi)⁻¹ * ∫ t : ℝ,
        Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2))) := by
  simpa [bsyRadialWeight] using tendsto_jensenSum_zetaDisc

private theorem bsyWeight_sum_le (s : Finset ℂ) :
    ∑ u ∈ s, bsyDiscWeight u ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
  apply le_of_tendsto_of_tendsto (tendsto_finsetSum s (fun u _ => tendsto_bsyRadial u))
    tendsto_bsyRadial_sum
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) (bsyRadial_finite r)]
  exact (summable_of_hasFiniteSupport (bsyRadial_finite r)).sum_le_tsum s
    (fun u _ => bsyRadial_nonneg hr u)

private theorem summable_bsyWeight : Summable bsyDiscWeight :=
  summable_of_sum_le bsyWeight_nonneg bsyWeight_sum_le

private theorem tsum_bsyWeight_eq :
    ∑' u, bsyDiscWeight u = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
  apply le_antisymm (summable_bsyWeight.tsum_le_of_sum_le bsyWeight_sum_le)
  apply le_of_tendsto tendsto_bsyRadial_sum
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) (bsyRadial_finite r)]
  exact (summable_of_hasFiniteSupport (bsyRadial_finite r)).tsum_le_tsum
    (bsyRadial_le hr) summable_bsyWeight

private theorem bsyMultiplicity_eq_natOrder {u : ℂ} (hu : ‖u‖ < 1) :
    bsyDiscMultiplicity u = (analyticOrderNatAt zetaDisc u : ℤ) := by
  rw [bsyDiscMultiplicity, MeromorphicOn.AnalyticOnNhd.divisor_apply bsy_analytic
    (mem_ball_zero_iff.mpr hu)]
  unfold analyticOrderNatAt
  generalize analyticOrderAt zetaDisc u = n
  cases n using ENat.recTopCoe <;> simp

private theorem bsyWeight_eq_zero {u : ℂ} (hu : zetaDisc u ≠ 0) :
    bsyDiscWeight u = 0 := by
  by_cases hb : ‖u‖ < 1
  · rw [bsyDiscWeight, bsyMultiplicity_eq_natOrder hb]
    have ho := analyticOrderAt_eq_zero.mpr (Or.inr hu)
    simp [analyticOrderNatAt, ho]
  · have hb' : u ∉ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using hb
    simp [bsyDiscWeight, bsyDiscMultiplicity,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb']

private theorem bsy_disc_zero_iff (ρ : ℂ) :
    zetaDisc (1 - ρ⁻¹) = 0 ∧ ‖1 - ρ⁻¹‖ < 1 ↔
      riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re := by
  constructor
  · rintro ⟨hz,hr⟩
    have hre := re_halfPlaneOfDisc_gt hr
    simp only [halfPlaneOfDisc, sub_sub_cancel, inv_inv] at hre
    have hρ1 : ρ ≠ 1 := by
      rintro rfl
      simp [zetaDisc_zero] at hz
    simp only [zetaDisc, halfPlaneOfDisc, sub_sub_cancel, inv_inv,
      zetaEntire_eq hρ1] at hz
    exact ⟨(mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hρ1),hre⟩
  · rintro ⟨hz,hr⟩
    obtain ⟨h1,_,h3⟩ := zetaDisc_one_sub_inv hz hr
    exact ⟨h1,h3⟩

private theorem bsy_order_transport {ρ : ℂ} (hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    analyticOrderNatAt zetaDisc (1 - ρ⁻¹) = analyticOrderNatAt riemannZeta ρ := by
  have hden : (1 : ℂ) - (1 - ρ⁻¹) ≠ 0 := by simpa using inv_ne_zero hρ
  have han : AnalyticAt ℂ halfPlaneOfDisc (1 - ρ⁻¹) :=
    (analyticAt_const.sub analyticAt_id).inv hden
  have hd : HasDerivAt halfPlaneOfDisc (((1 : ℂ) - (1 - ρ⁻¹)) ^ 2)⁻¹ (1 - ρ⁻¹) := by
    change HasDerivAt (fun w : ℂ => (1 - w)⁻¹) _ _
    convert ((hasDerivAt_id ((1 : ℂ) - ρ⁻¹)).const_sub (1 : ℂ)).inv hden using 1 <;>
      first | rfl | norm_num
  have ho : analyticOrderAt zetaDisc (1 - ρ⁻¹) = analyticOrderAt zetaEntire ρ := by
    change analyticOrderAt (zetaEntire ∘ halfPlaneOfDisc) _ = _
    have h := analyticOrderAt_comp_of_deriv_ne_zero (f := zetaEntire) han
      (by rw [hd.deriv]; exact inv_ne_zero (pow_ne_zero _ hden))
    simpa [zetaDisc, Function.comp_def, halfPlaneOfDisc] using h
  simp only [analyticOrderNatAt, ho, analyticOrderAt_zetaEntire_of_ne_one hρ1]

private def bsyRightWeight (ρ : ℂ) : ℝ :=
  if riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re then
    (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.log ‖ρ / (1 - ρ)‖ else 0

private theorem bsyWeight_transport (ρ : ℂ) :
    bsyDiscWeight (1 - ρ⁻¹) = bsyRightWeight ρ := by
  classical
  by_cases hρ : riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re
  · have hρ0 : ρ ≠ 0 := by rintro rfl; norm_num at hρ
    have hρ1 : ρ ≠ 1 := by
      rintro rfl
      exact riemannZeta_ne_zero_of_one_le_re (by simp) hρ.1
    obtain ⟨_, hn, hr⟩ := zetaDisc_one_sub_inv hρ.1 hρ.2
    rw [bsyRightWeight, if_pos hρ, bsyDiscWeight, bsyMultiplicity_eq_natOrder hr,
      bsy_order_transport hρ0 hρ1, hn, inv_div, norm_div]
    simp
  · rw [bsyRightWeight, if_neg hρ]
    by_cases hr : ‖1 - ρ⁻¹‖ < 1
    · apply bsyWeight_eq_zero
      exact fun hz => hρ ((bsy_disc_zero_iff ρ).mp ⟨hz,hr⟩)
    · have hb : 1 - ρ⁻¹ ∉ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using hr
      simp [bsyDiscWeight, bsyDiscMultiplicity,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb]

private def bsyCayleyEquiv : ℂ ≃ ℂ where
  toFun ρ := 1 - ρ⁻¹
  invFun := halfPlaneOfDisc
  left_inv ρ := by simp [halfPlaneOfDisc]
  right_inv u := by simp [halfPlaneOfDisc]

/-- The BSY zero series converges, with the analytic multiplicity of every zero. -/
theorem hasSum_log_norm_rightZetaZeros :
    HasSum (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re} =>
      (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.log ‖(ρ : ℂ) / (1 - ρ)‖)
      ((2 * Real.pi)⁻¹ * ∫ t : ℝ,
        Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) := by
  have hs := summable_bsyWeight.hasSum
  rw [tsum_bsyWeight_eq] at hs
  have ht := bsyCayleyEquiv.hasSum_iff.mpr hs
  have ht' : HasSum bsyRightWeight ((2 * Real.pi)⁻¹ * ∫ t : ℝ,
      Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) := by
    simpa only [Function.comp_def, bsyCayleyEquiv, Equiv.coe_fn_mk,
      bsyWeight_transport] using ht
  have hsupp : Function.support bsyRightWeight ⊆
      {ρ : ℂ | riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re} := by
    intro ρ hρ
    by_contra hz
    change ¬ (riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re) at hz
    exact hρ (by simp only [bsyRightWeight,if_neg hz])
  have h := (hasSum_subtype_iff_of_support_subset hsupp).mpr ht'
  apply h.congr
  intro s
  apply Finset.sum_congr rfl
  intro ρ _
  have hρ : riemannZeta (ρ : ℂ) = 0 ∧ 1 / 2 < (ρ : ℂ).re := ρ.property
  simp only [Function.comp_def, bsyRightWeight, if_pos hρ]

/-- The unconditional Balazard–Saias–Yor Poisson–Jensen identity. -/
theorem integral_log_norm_zeta_criticalLine_eq_tsum_rightZeros :
    (∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) =
      2 * Real.pi * ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re},
        (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.log ‖(ρ : ℂ) / (1 - ρ)‖ := by
  rw [hasSum_log_norm_rightZetaZeros.tsum_eq]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0), one_mul]

end
end RHTower
