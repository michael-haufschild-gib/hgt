import GaloisForLFunctions.RHTower.MobiusLaplaceBoundaryMultiplicity
import GaloisForLFunctions.RHTower.MobiusLaplaceHalfPolylogCriterion
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# Fixed-polylog Abel growth bounds boundary zeta multiplicity

If the critical Möbius--Laplace source has a fixed logarithmic loss of degree `q`, its Mellin
transform is expected to have at most radial growth `r⁻⁽q+1⁾` at a critical-line point.  This file
isolates the resulting boundary rigidity: that growth forbids a zeta zero of order greater than
`q + 1`.

The proof uses the local factorization `ζ(ρ+r) = rⁿ p(ρ+r)`.  If `n > q + 1`, then the canonical
Mellin identity factors into a bounded term `r^(q+1) G(ρ+r)` and a term vanishing like
`r^(n-q-1)`.  Its right side instead tends to the nonzero value `Γ(ρ) (ρ-1)`.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

private theorem tendsto_ofReal_nhdsGT_zero_nhds_zero :
    Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝 0) :=
  Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem tendsto_critical_ray (rho : ℂ) :
    Tendsto (fun r : ℝ => rho + (r : ℂ)) (𝓝[>] 0) (𝓝 rho) := by
  simpa using!
    ((continuous_const.add Complex.continuous_ofReal).tendsto 0).mono_left
      nhdsWithin_le_nhds

/-- Compatibility alias for the sharp source-to-Abel estimate proved in the half-polylog
criterion module. -/
theorem mobiusLaplaceCriticalPolylogAbelBound_of_halfPolylogDecay
    {q : ℕ} (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) {rho : ℂ}
    (hrho : rho.re = 1 / 2) :
    MobiusLaplaceCriticalPolylogAbelBound q rho :=
  mobiusLaplaceCriticalPolylogAbelBound_of_halfPolylog hdecay hrho

/-- **Boundary pole-order rigidity.**  A pole-order-`q+1` radial Abel bound for the canonical
Möbius Mellin transform caps the multiplicity of a critical-line zeta zero by `q + 1`. -/
theorem analyticOrderAt_riemannZeta_toNat_le_of_mobiusLaplaceCriticalPolylogAbelBound
    {q : ℕ} {rho : ℂ} (hrho : rho.re = 1 / 2) (hzero : riemannZeta rho = 0)
    (hGanalytic : AnalyticOnNhd ℂ
      (mellin mobiusDiscreteLaplaceTransform) rightHalf)
    (hAbel : MobiusLaplaceCriticalPolylogAbelBound q rho) :
    (analyticOrderAt riemannZeta rho).toNat ≤ q + 1 := by
  have hrhoPos : 0 < rho.re := by rw [hrho]; norm_num
  have hrhoLtOne : rho.re < 1 := by rw [hrho]; norm_num
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
  have hstrip : 0 < rho.re ∧ rho.re < 1 := ⟨hrhoPos, hrhoLtOne⟩
  have horderEq := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
  have horderFinite : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    rw [← horderEq]
    exact xi_orderAt_ne_top rho
  let n : ℕ := (analyticOrderAt riemannZeta rho).toNat
  have hncoe : (n : ℕ∞) = analyticOrderAt riemannZeta rho :=
    ENat.coe_toNat horderFinite
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho hrhoOne
  obtain ⟨p, hp, hpzero, hfactor⟩ :=
    (hzetaAnalytic.analyticOrderAt_eq_natCast).mp hncoe.symm
  by_contra hcap
  have hnlarge : q + 1 < n := Nat.lt_of_not_ge hcap
  let k : ℕ := n - (q + 1)
  have hkpos : 0 < k := Nat.sub_pos_of_lt hnlarge
  have hnSplit : q + 1 + k = n := by
    dsimp only [k]
    omega
  have hray := tendsto_critical_ray rho
  have hfactorRay : ∀ᶠ r : ℝ in 𝓝[>] 0,
      riemannZeta (rho + (r : ℂ)) =
        ((r : ℂ) ^ n) * p (rho + (r : ℂ)) := by
    have h := hray.eventually hfactor
    filter_upwards [h] with r hr
    simpa [smul_eq_mul] using hr
  have hpowZero : Tendsto (fun r : ℝ => (r : ℂ) ^ k)
      (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_ofReal_nhdsGT_zero_nhds_zero.pow k
    simpa [zero_pow hkpos.ne'] using h
  have hpRay : Tendsto (fun r : ℝ => p (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 (p rho)) := hp.continuousAt.tendsto.comp hray
  have hlinearRay : Tendsto (fun r : ℝ => rho + (r : ℂ) - 1)
      (𝓝[>] 0) (𝓝 (rho - 1)) := by
    exact (((continuous_id.sub continuous_const).tendsto rho).comp hray)
  have hvanishingFactor : Tendsto
      (fun r : ℝ =>
        (r : ℂ) ^ k * ((rho + (r : ℂ) - 1) * p (rho + (r : ℂ))))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hpowZero.mul (hlinearRay.mul hpRay)
  have hproductZero : Tendsto
      (fun r : ℝ =>
        ((r : ℂ) ^ (q + 1) *
            mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ))) *
          ((r : ℂ) ^ k *
            ((rho + (r : ℂ) - 1) * p (rho + (r : ℂ)))))
      (𝓝[>] 0) (𝓝 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero hAbel hvanishingFactor
  have hunitProductZero : Tendsto
      (fun r : ℝ =>
        mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
          zetaResidueUnit (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
    refine hproductZero.congr' ?_
    have hnotOne : ∀ᶠ r : ℝ in 𝓝[>] 0, rho + (r : ℂ) ≠ 1 := by
      have hne : {z : ℂ | z ≠ 1} ∈ 𝓝 rho :=
        isOpen_compl_singleton.mem_nhds hrhoOne
      exact hray.eventually hne
    filter_upwards [self_mem_nhdsWithin, hfactorRay, hnotOne] with r hr hfac hrOne
    simp only [zetaResidueUnit, Function.update_of_ne hrOne]
    have hpow : (r : ℂ) ^ (q + 1) * (r : ℂ) ^ k = (r : ℂ) ^ n := by
      rw [← pow_add, hnSplit]
    calc
      ((r : ℂ) ^ (q + 1) *
          mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ))) *
          ((r : ℂ) ^ k *
            ((rho + (r : ℂ) - 1) * p (rho + (r : ℂ)))) =
          mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
            ((rho + (r : ℂ) - 1) *
              ((r : ℂ) ^ n * p (rho + (r : ℂ)))) := by
        rw [← hpow]
        ring
      _ = mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
          ((rho + (r : ℂ) - 1) * riemannZeta (rho + (r : ℂ))) := by
        rw [hfac]
  have hcanonical :=
    mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_analyticOnNhd
      hGanalytic
  have hrightZero : Tendsto
      (fun r : ℝ =>
        Complex.Gamma (rho + (r : ℂ)) * (rho + (r : ℂ) - 1))
      (𝓝[>] 0) (𝓝 0) := by
    refine hunitProductZero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    apply hcanonical
    rw [mem_rightHalf]
    norm_num [Complex.add_re, hrho]
    exact hr
  have hnotGammaPole : ∀ m : ℕ, rho ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    rw [hrho] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hrightActual : Tendsto
      (fun r : ℝ =>
        Complex.Gamma (rho + (r : ℂ)) * (rho + (r : ℂ) - 1))
      (𝓝[>] 0) (𝓝 (Complex.Gamma rho * (rho - 1))) := by
    exact ((Complex.continuousAt_Gamma rho hnotGammaPole).tendsto.comp hray).mul
      (((continuous_id.sub continuous_const).tendsto rho).comp hray)
  have hvanish : Complex.Gamma rho * (rho - 1) = 0 :=
    tendsto_nhds_unique hrightActual hrightZero
  exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hrhoPos)
    (sub_ne_zero.mpr hrhoOne)) hvanish

/-- Fixed half-polylog source decay caps each critical-line zeta multiplicity by `q + 1`. -/
theorem analyticOrderAt_riemannZeta_toNat_le_of_mobiusDiscreteLaplaceHalfPolylogDecay
    {q : ℕ} (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) {rho : ℂ}
    (hrho : rho.re = 1 / 2) (hzero : riemannZeta rho = 0) :
    (analyticOrderAt riemannZeta rho).toNat ≤ q + 1 :=
  analyticOrderAt_riemannZeta_toNat_le_of_mobiusLaplaceCriticalPolylogAbelBound
    hrho hzero
      (analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_halfPolylog hdecay)
      (mobiusLaplaceCriticalPolylogAbelBound_of_halfPolylogDecay hdecay hrho)

/-- **Strengthened fixed-polylog criterion.** Degree-`q` half-polylog decay implies RH and caps
every critical-line zeta zero multiplicity by `q + 1`. -/
theorem mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis_and_multiplicityCap
    {q : ℕ} (hdecay : MobiusDiscreteLaplaceHalfPolylogDecay q) :
    RiemannHypothesis ∧
      ∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
        (analyticOrderAt riemannZeta rho).toNat ≤ q + 1 := by
  refine ⟨mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis hdecay, ?_⟩
  intro rho hrho hzero
  exact analyticOrderAt_riemannZeta_toNat_le_of_mobiusDiscreteLaplaceHalfPolylogDecay
    hdecay hrho hzero

end

end RHTower
