import GaloisForLFunctions.RHTower.DeningerMeyerXiDivisionGrowth
import GaloisForLFunctions.RHTower.DeningerMeyerDilationCapAverage
import GaloisForLFunctions.RHTower.DeningerMeyerGaussianSourceApproximation
import GaloisForLFunctions.RHTower.DeningerMeyerExactXiCapSource
import GaloisForLFunctions.RHTower.DeningerMeyerArithmeticSymmetricSplitting

/-! # Global Xi synthesis in the literal Meyer source

Entire Xi division, good-height contour control, and Gaussian inversion
produce actual cap boundaries approaching the original source. The closed
Poisson range then removes the entire jet-invisible sector. No arbitrary
packet admission, positivity, or Riemann-hypothesis premise is used.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

/-- Dilation averaging of the fixed Xi cap realizes exact Mellin products. -/
theorem deningerMeyerDilationXiCap_mellin (h : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogSumLM (deningerMeyerDilationCapAverage h deningerMeyerXiCapSource)) s =
      deningerMeyerStrongLogMellin h s * xi s := by
  have ha := analyticOnNhd_deningerMeyerStrongLogMellin
    (deningerMeyerStrongLogSumLM (deningerMeyerDilationCapAverage h deningerMeyerXiCapSource)).property
  have hb := (analyticOnNhd_deningerMeyerStrongLogMellin h.property).mul xi_analyticOnNhd_univ
  have he : deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogSumLM (deningerMeyerDilationCapAverage h deningerMeyerXiCapSource))
      =ᶠ[𝓝 (2:ℂ)] fun z => deningerMeyerStrongLogMellin h z * xi z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (2:ℂ) ∈ {z:ℂ | 1 < z.re})] with z hz
    rw [deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin _ hz]
    change riemannZeta z*mellin (deningerMeyerDilationAverage h deningerMeyerXiCapSource.val) z = _
    rw [deningerMeyerDilationAverage_mellin h _ hz]
    have hxi : riemannZeta z*mellin deningerMeyerXiCapSource z = xi z :=
      (deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin deningerMeyerXiCapSource hz).symm.trans
        (deningerMeyerXiCapSource_mellin z)
    calc riemannZeta z*(deningerMeyerStrongLogMellin h z*mellin deningerMeyerXiCapSource z)
        = deningerMeyerStrongLogMellin h z*(riemannZeta z*mellin deningerMeyerXiCapSource z) := by ring
      _ = _ := by rw [hxi]
  exact congrFun (ha.eq_of_eventuallyEq hb he) s

/-- Entire division produces a genuine Poisson preimage in the original cap. -/
theorem deningerMeyerXiDivision_has_cap
    (g : DeningerMeyerStrongLogTarget) {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hdiv : ∀ s, deningerMeyerStrongLogMellin g s = xi s*H s) :
    ∃ f : DeningerMeyerCap, deningerMeyerStrongLogSumLM f = g := by
  let caps (m : ℕ) := deningerMeyerDilationCapAverage
    (deningerMeyerInverseMellinSource
      (deningerGaussianMellinRegularization (1/((m:ℝ)+1)) H)
      (deningerMeyerXiQuotient_regularized g hH hdiv (by positivity)))
    deningerMeyerXiCapSource
  have hc (m : ℕ) : deningerMeyerStrongLogSumLM (caps m) = deningerMeyerGaussianSource g m := by
    apply deningerMeyerStrongLogMellin_injective
    funext s
    change deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogSumLM (deningerMeyerDilationCapAverage _ deningerMeyerXiCapSource)) s =
        deningerMeyerStrongLogMellin (deningerMeyerGaussianSource g m) s
    rw [deningerMeyerDilationXiCap_mellin, deningerMeyerInverseMellinSource_mellin,
      deningerMeyerGaussianSource_mellin, hdiv]
    dsimp [deningerGaussianMellinRegularization]
    ring
  exact deningerMeyerStrongLog_boundary_limit (l := atTop) caps g
    (by simpa only [hc] using deningerMeyerGaussianSource_tendsto g)

/-- Global source-native Xi spectral synthesis, without a synthesis premise. -/
theorem deningerMeyerXiSpectralSynthesis : DeningerMeyerXiSpectralSynthesis := by
  intro g hjets
  have hmem : deningerMeyerCenteredMellin g ∈ deningerCompactOpenXiRange := by
    rw [deningerCompactOpenXiRange_eq_allJets_ker]
    exact hjets
  obtain ⟨F, hF⟩ := hmem
  let H : ℂ → ℂ := fun s => F (-I*(s-1/2))
  have hH : Differentiable ℂ H := F.property.comp (by fun_prop)
  apply deningerMeyerXiDivision_has_cap g hH
  intro s
  have hc : 1/2+I*(-I*(s-1/2)) = s := by
    ring_nf
    rw [I_sq]
    ring
  have he := congrArg (fun A : DeningerCompactOpenEntire => A (-I*(s-1/2))) hF
  change XiC (-I*(s-1/2))*H s = deningerMeyerStrongLogMellin g (1/2+I*(-I*(s-1/2))) at he
  rw [XiC, mul_comm (-I*(s-1/2)) I, hc] at he
  exact he.symm

/-- The literal Meyer comparison is faithful on the whole source quotient. -/
theorem deningerMeyerCompactOpenXiComparison_injective :
    Function.Injective deningerMeyerCompactOpenXiComparison :=
  deningerMeyerCompactOpenXiComparison_injective_iff.mpr deningerMeyerXiSpectralSynthesis

/-- No globally invisible cohomology remains, including infinite-order classes. -/
theorem deningerMeyerInvisible_eq_bot : DeningerMeyerInvisible = ⊥ :=
  LinearMap.ker_eq_bot.mpr deningerMeyerCompactOpenXiComparison_injective

/-- Full arithmetic jets determine every literal cohomology class. -/
theorem deningerMeyerCohomology_eq_of_XiJets_eq
    {u v : DeningerMeyerStrongLogCohomology}
    (h : ∀ rho j, deningerMeyerXiSupportJetEvaluationLM rho j u =
      deningerMeyerXiSupportJetEvaluationLM rho j v) : u = v := by
  apply sub_eq_zero.mp
  have hm : u-v ∈ DeningerMeyerInvisible :=
    (mem_deningerMeyerInvisible_iff _).mpr fun rho j => by rw [map_sub, h rho j, sub_self]
  rw [deningerMeyerInvisible_eq_bot] at hm
  exact hm

/-- The arithmetic observable projector is the identity on the literal source. -/
theorem deningerMeyerArithmeticCausalProjector_eq_id :
    deningerMeyerArithmeticCausalProjector = LinearMap.id := by
  apply LinearMap.ext
  intro u
  apply deningerMeyerCompactOpenXiComparison_injective
  exact deningerMeyerArithmeticCausalProjector_comparison u

end
end RHTower
