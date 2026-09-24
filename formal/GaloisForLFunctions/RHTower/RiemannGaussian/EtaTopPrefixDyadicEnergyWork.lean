import GaloisForLFunctions.RHTower.RiemannGaussian.EtaTopPrefixAmplitudeSignCriterion
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergyTransport

/-!
# Dyadic finite eta energy work at an off-line zero

The signed energy of the two literal completed finite eta prefixes has a
sharp asymptotic at a hypothetical right-half zero. Over a dyadic cutoff
block, its telescoping drop has a strictly positive leading coefficient.
The block is exactly a sum of one-step finite arithmetic works, so this is
a quantitative source-side sign law. It does not prove that such zeros exist
or that the opposite sign law holds unconditionally.
-/

open Complex Filter Topology
namespace RiemannGaussian
noncomputable section

/-- First omitted odd endpoint for the cutoff indexed by `N`. -/
def rgEtaEndpoint (N : ℕ) : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)

/-- Complementary real exponent of the reflected zero. -/
def rgEtaPartnerExponent (rho : NontrivialZetaZero) : ℝ :=
  (NontrivialZetaZero.conjugatePartner rho).1.re

/-- Positive sharp amplitude constant of the slower reflected component. -/
def rgEtaSharpConstant (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit rho

/-- Signed finite energy: reflected-partner magnitude squared minus original
magnitude squared. -/
def rgEtaEnergy (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference rho N

private theorem rgEtaEndpoint_pos (N : ℕ) : 0 < rgEtaEndpoint N := by
  unfold rgEtaEndpoint
  positivity

/-- At a hypothetical right-half zero, signed finite energy has the slower
partner's positive sharp leading coefficient. -/
theorem tendsto_scaled_rgEtaEnergy_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (rgEtaEndpoint N) ^ (2 * rgEtaPartnerExponent rho) * rgEtaEnergy rho N)
      atTop (nhds ((rgEtaSharpConstant rho) ^ 2)) := by
  let P (N : ℕ) : ℝ :=
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent rho N‖
  let Q (N : ℕ) : ℝ :=
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent rho N‖
  let scale (N : ℕ) : ℝ :=
    (rgEtaEndpoint N) ^ rgEtaPartnerExponent rho
  have hp : Tendsto (fun N => scale N * P N) atTop (nhds (rgEtaSharpConstant rho)) :=
    tendsto_succOddEndpoint_partner_rpow_mul_norm_topPrefixPartnerComponent rho
  have hq : Tendsto (fun N => scale N * Q N) atTop (nhds 0) :=
    tendsto_succOddEndpoint_partner_rpow_mul_norm_topPrefixConjugateComponent_zero_of_half_lt_re
      rho hrho
  have hsq := (hp.pow 2).sub (hq.pow 2)
  simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero] using
    hsq.congr' (Eventually.of_forall fun N => by
      have hx := rgEtaEndpoint_pos N
      have hpow : (scale N) ^ 2 =
          (rgEtaEndpoint N) ^ (2 * rgEtaPartnerExponent rho) := by
        dsimp only [scale]
        rw [pow_two, ← Real.rpow_add hx]
        congr 1
        ring
      dsimp only [rgEtaEnergy]
      rw [topPrefixFiniteEnergyDifference_eq_componentNormSq_sub]
      dsimp only [P, Q]
      rw [mul_pow, mul_pow, ← mul_sub, hpow]
      )

private theorem tendsto_rgEtaEndpoint_double_div_half :
    Tendsto (fun N : ℕ => rgEtaEndpoint N / rgEtaEndpoint (2 * N))
      atTop (nhds (1 / 2 : ℝ)) := by
  convert (tendsto_add_mul_div_add_mul_atTop_nhds
    (3 : ℝ) 3 2 (d := 4) (by norm_num)) using 1
  · funext N
    dsimp only [rgEtaEndpoint]
    push_cast
    ring
  · norm_num

private theorem tendsto_double_atTop : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with N hN
  omega

/-- The energy drop from cutoff `N` to cutoff `2N` has a sharp coefficient
that is strictly positive for every right-half zero. -/
theorem tendsto_scaled_rgEtaDyadicEnergyDrop_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (rgEtaEndpoint N) ^ (2 * rgEtaPartnerExponent rho) *
        (rgEtaEnergy rho N - rgEtaEnergy rho (2 * N)))
      atTop
      (nhds ((1 - (1 / 2 : ℝ) ^ (2 * rgEtaPartnerExponent rho)) *
        (rgEtaSharpConstant rho) ^ 2)) := by
  let q : ℝ := 2 * rgEtaPartnerExponent rho
  have hmain := tendsto_scaled_rgEtaEnergy_of_half_lt_re rho hrho
  have hdouble := hmain.comp tendsto_double_atTop
  have hratio := tendsto_rgEtaEndpoint_double_div_half
  have hratioPow : Tendsto
      (fun N : ℕ => (rgEtaEndpoint N / rgEtaEndpoint (2 * N)) ^ q)
      atTop (nhds ((1 / 2 : ℝ) ^ q)) := by
    exact ((Real.continuousAt_rpow_const (1 / 2) q
      (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))).tendsto).comp hratio
  have hscaledDouble : Tendsto (fun N : ℕ =>
      (rgEtaEndpoint N) ^ q * rgEtaEnergy rho (2 * N)) atTop
      (nhds ((1 / 2 : ℝ) ^ q * (rgEtaSharpConstant rho) ^ 2)) := by
    convert hratioPow.mul hdouble using 1
    · funext N
      have hx := rgEtaEndpoint_pos N
      have hy := rgEtaEndpoint_pos (2 * N)
      dsimp only [q]
      rw [Real.div_rpow hx.le hy.le]
      field_simp [(Real.rpow_pos_of_pos hy (2 * rgEtaPartnerExponent rho)).ne']
      simp only [Function.comp_apply]
      ring
  have hdrop := hmain.sub hscaledDouble
  convert hdrop using 1
  · funext N
    ring
  · congr 1
    dsimp only [q]
    ring

/-- Strict positivity of the dyadic work coefficient. -/
theorem rgEtaDyadicEnergyDropSharpLimit_pos
    (rho : NontrivialZetaZero) :
    0 < (1 - (1 / 2 : ℝ) ^ (2 * rgEtaPartnerExponent rho)) *
      (rgEtaSharpConstant rho) ^ 2 := by
  have hp : 0 < rgEtaPartnerExponent rho := by
    unfold rgEtaPartnerExponent
    exact NontrivialZetaZero.zero_lt_re (NontrivialZetaZero.conjugatePartner rho)
  have hpow : (1 / 2 : ℝ) ^ (2 * rgEtaPartnerExponent rho) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have hc : 0 < (rgEtaSharpConstant rho) ^ 2 := by
    exact pow_pos (topPrefixPartnerAmplitudeSharpLimit_pos rho) 2
  exact mul_pos (sub_pos.mpr hpow) hc

/-- Every hypothetical right-half zero eventually has positive dyadic signed
energy drop. -/
theorem eventually_pos_rgEtaDyadicEnergyDrop_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      0 < rgEtaEnergy rho N - rgEtaEnergy rho (2 * N) := by
  have hlim := tendsto_scaled_rgEtaDyadicEnergyDrop_of_half_lt_re rho hrho
  have hpos := hlim.eventually
    (eventually_gt_nhds (rgEtaDyadicEnergyDropSharpLimit_pos rho))
  filter_upwards [hpos] with N hN
  have hscale : 0 < (rgEtaEndpoint N) ^ (2 * rgEtaPartnerExponent rho) :=
    Real.rpow_pos_of_pos (rgEtaEndpoint_pos N) _
  by_contra h
  have hnonpos : rgEtaEnergy rho N - rgEtaEnergy rho (2 * N) ≤ 0 := le_of_not_gt h
  exact (not_le_of_gt hN)
    (mul_nonpos_of_nonneg_of_nonpos hscale.le hnonpos)

/-- The dyadic drop is exactly the finite arithmetic energy work accumulated
over cutoff indices `N, ..., 2N-1`. -/
theorem rgEtaDyadicEnergyDrop_eq_finiteWorkBlock
    (rho : NontrivialZetaZero) (N : ℕ) :
    rgEtaEnergy rho N - rgEtaEnergy rho (2 * N) =
      ∑ j ∈ Finset.range N,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho (N + j) := by
  simpa only [rgEtaEnergy, two_mul] using
    (sum_range_topPrefixFiniteEnergyWork_eq_sub rho N N).symm

/-- Sharp positive asymptotic of the literal finite-work block. -/
theorem tendsto_scaled_rgEtaDyadicFiniteWorkBlock_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (rgEtaEndpoint N) ^ (2 * rgEtaPartnerExponent rho) *
        (∑ j ∈ Finset.range N,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
            rho (N + j)))
      atTop
      (nhds ((1 - (1 / 2 : ℝ) ^ (2 * rgEtaPartnerExponent rho)) *
        (rgEtaSharpConstant rho) ^ 2)) := by
  simpa only [← rgEtaDyadicEnergyDrop_eq_finiteWorkBlock] using
    tendsto_scaled_rgEtaDyadicEnergyDrop_of_half_lt_re rho hrho

/-- Every hypothetical right-half zero eventually has positive dyadic
finite arithmetic work. -/
theorem eventually_pos_rgEtaDyadicFiniteWorkBlock_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      0 < ∑ j ∈ Finset.range N,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho (N + j) := by
  filter_upwards [eventually_pos_rgEtaDyadicEnergyDrop_of_half_lt_re rho hrho]
    with N hN
  simpa only [rgEtaDyadicEnergyDrop_eq_finiteWorkBlock] using hN

end
end RiemannGaussian
