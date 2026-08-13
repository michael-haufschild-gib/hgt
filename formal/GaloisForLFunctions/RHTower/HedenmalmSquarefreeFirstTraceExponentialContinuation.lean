import GaloisForLFunctions.RHTower.HedenmalmSquarefreeFirstTraceAnomalyCharge
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier
import GaloisForLFunctions.RHTower.PrimeArchAntiHerglotzGate
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-!
# Squarefree first-trace exponential continuation

The quotient of the squarefree partition by its nowhere-zero Hilbert--Carleman determinant is a
canonical continuation of `exp(P(s))` from the Euler chamber into `Re s > 1/2`.  This module proves
that no hidden regular current appears in that continuation: the Carleman logarithmic derivative
is exactly the doubled von Mangoldt current minus the higher-valuation tail, and the remaining
first-trace current is exactly the existing meromorphic valuation-one prime current.

Consequently the first-trace anomaly is normalized transport of one global field, its zero residue
is the complete zeta multiplicity, and the completed prime--Gamma flux differs from it only by the
explicit holomorphic higher-valuation and archimedean terms.  This identifies Route P's source
anomaly with the singular current in the anti-Herglotz RH gate without assuming RH.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Canonical strict-right continuation of the exponential of prime zeta. -/
def squarefreeFirstTraceExponentialContinuation (s : ℂ) : ℂ :=
  GaloisForLFunctions.squarefreePartition s / squarefreeCarlemanDet s

/-- In the Euler chamber the continued field is literally `exp(P(s))`. -/
theorem squarefreeFirstTraceExponentialContinuation_eq_exp_primeZeta
    {s : ℂ} (hs : 1 < s.re) :
    squarefreeFirstTraceExponentialContinuation s =
      Complex.exp (coronaPrimeZeta s) := by
  rw [squarefreeFirstTraceExponentialContinuation,
    squarefreePartition_eq_carleman_mul_exp hs]
  field_simp [squarefreeCarlemanDet_ne_zero]

/-- Every affine first-trace anomaly is normalized transport of the one global continuation.
This algebraic identity remains valid even when the base squarefree partition vanishes. -/
theorem squarefreeFirstTraceAnomaly_eq_exponentialContinuation_div
    (sigma epsilon u : ℂ) :
    squarefreeFirstTraceAnomaly sigma epsilon u =
      squarefreeFirstTraceExponentialContinuation (sigma + u * epsilon) /
        squarefreeFirstTraceExponentialContinuation sigma := by
  unfold squarefreeFirstTraceAnomaly squarefreeCarlemanTransport
    GaloisForLFunctions.squarefreeBoundaryOverlap
    squarefreeFirstTraceExponentialContinuation
  by_cases hbase : GaloisForLFunctions.squarefreePartition sigma = 0
  · simp [hbase]
  · field_simp [hbase, squarefreeCarlemanDet_ne_zero]

/-! ## Exact Carleman/higher-valuation current weld -/

/-- Euler-chamber form of the exact Carleman current identity. -/
theorem squarefreeCarleman_logDeriv_eq_two_flux_sub_higherValuation_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv squarefreeCarlemanDet s =
      2 * infinitePrimeFlux (2 * s) - xiPrimeLogHigherValuation s := by
  have hsq := squarefreeFixedCurrent_eq_carleman_logDeriv_sub_deriv hs
  have hprime := neg_deriv_coronaPrimeZeta_eq_xiPrimeLogDirichlet hs
  have hflux := infinitePrimeFlux_eq_primeLog_add_higherValuation hs
  simp only [GaloisForLFunctions.squarefreeFixedCurrent] at hsq
  linear_combination hsq + hprime - hflux

/-- **No higher-trace leakage.**  The Euler-chamber Carleman current identity extends exactly to
the full connected Hilbert--Schmidt half-plane. -/
theorem squarefreeCarleman_logDeriv_eq_two_flux_sub_higherValuation
    {s : ℂ} (hs : 1 / 2 < s.re) :
    logDeriv squarefreeCarlemanDet s =
      2 * infinitePrimeFlux (2 * s) - xiPrimeLogHigherValuation s := by
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  let F : ℂ → ℂ := logDeriv squarefreeCarlemanDet
  let G : ℂ → ℂ := fun z =>
    2 * infinitePrimeFlux (2 * z) - xiPrimeLogHigherValuation z
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hFan : AnalyticOnNhd ℂ F U := by
    intro z hz
    have hD : AnalyticAt ℂ squarefreeCarlemanDet z :=
      differentiableOn_squarefreeCarlemanDet.analyticAt
        (hUopen.mem_nhds hz)
    dsimp only [F]
    rw [show logDeriv squarefreeCarlemanDet =
        fun w => deriv squarefreeCarlemanDet w / squarefreeCarlemanDet w by
      funext w
      rw [logDeriv_apply]]
    exact hD.deriv.div hD (squarefreeCarlemanDet_ne_zero z)
  have hGan : AnalyticOnNhd ℂ G U := by
    intro z hz
    have hflux : AnalyticAt ℂ (fun w : ℂ => infinitePrimeFlux (2 * w)) z :=
      GaloisForLFunctions.analyticOnNhd_infinitePrimeFlux_two_mul_rightHalf z hz
    have hhigher : AnalyticAt ℂ xiPrimeLogHigherValuation z :=
      (differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd hUopen) z hz
    dsimp only [G]
    exact (analyticAt_const.mul hflux).sub hhigher
  have hpre : IsPreconnected U :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by
    change 1 / 2 < ((2 : ℂ).re)
    norm_num
  have heq : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have hEuler : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hEuler] with z hz
    dsimp only [F, G]
    exact
      squarefreeCarleman_logDeriv_eq_two_flux_sub_higherValuation_of_one_lt_re hz
  have hEqOn : Set.EqOn F G U :=
    hFan.eqOn_of_preconnected_of_eventuallyEq hGan hpre htwo heq
  exact hEqOn hs

/-! ## The continued valuation-one source current -/

/-- Squarefree logarithmic current on its zero-free strict-right domain. -/
theorem neg_logDeriv_squarefreePartition_eq_flux_sub_two_flux
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    -logDeriv GaloisForLFunctions.squarefreePartition s =
      infinitePrimeFlux s - 2 * infinitePrimeFlux (2 * s) := by
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      one_re] at hre
    linarith
  have hz2 : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re h2re
  have hnum : DifferentiableAt ℂ riemannZeta s :=
    (analyticOn_riemannZeta s hs1).differentiableAt
  have hden : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    (differentiableAt_riemannZeta h2one).comp s (by fun_prop)
  change -logDeriv (fun z : ℂ => riemannZeta z / riemannZeta (2 * z)) s = _
  rw [logDeriv_div (f := riemannZeta) (g := fun z : ℂ => riemannZeta (2 * z))
    s hzeta hz2 hnum hden]
  have hcomp : logDeriv (fun z : ℂ => riemannZeta (2 * z)) s =
      2 * logDeriv riemannZeta (2 * s) := by
    have hchain := logDeriv_comp (f := riemannZeta) (g := fun z : ℂ => 2 * z)
      (differentiableAt_riemannZeta h2one)
      (show DifferentiableAt ℂ (fun z : ℂ => 2 * z) s by fun_prop)
    change logDeriv (fun z : ℂ => riemannZeta (2 * z)) s =
      logDeriv riemannZeta (2 * s) * deriv (fun z : ℂ => 2 * z) s at hchain
    rw [show deriv (fun z : ℂ => 2 * z) s = 2 by simp] at hchain
    linear_combination hchain
  rw [hcomp]
  simp only [infinitePrimeFlux]
  ring

/-- Meromorphic continuation of the divisor-bearing first-prime-trace current. -/
def squarefreeFirstTraceContinuedCurrent (s : ℂ) : ℂ :=
  xiPrimeLogDirichletContinuation s

/-- Away from pole and divisor, the canonical exponential continuation has exactly the continued
valuation-one current as its negative logarithmic derivative. -/
theorem squarefreeFirstTraceContinuedCurrent_eq_neg_logDeriv
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hs1 : s ≠ 1)
    (hsq : GaloisForLFunctions.squarefreePartition s ≠ 0) :
    squarefreeFirstTraceContinuedCurrent s =
      -logDeriv squarefreeFirstTraceExponentialContinuation s := by
  have hsqAn : AnalyticAt ℂ GaloisForLFunctions.squarefreePartition s :=
    analyticAt_squarefreePartition_of_half_lt_re hhalf hs1
  have hDAn : AnalyticAt ℂ squarefreeCarlemanDet s :=
    differentiableOn_squarefreeCarlemanDet.analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hhalf)
  have hsqCurrent := neg_logDeriv_squarefreePartition_eq_flux_sub_two_flux
    hhalf hs1
      ((GaloisForLFunctions.squarefreePartition_eq_zero_iff_riemannZeta_eq_zero
        hhalf).not.mp hsq)
  have hDCurrent :=
    squarefreeCarleman_logDeriv_eq_two_flux_sub_higherValuation hhalf
  change xiPrimeLogDirichletContinuation s =
    -logDeriv (fun z =>
      GaloisForLFunctions.squarefreePartition z / squarefreeCarlemanDet z) s
  rw [logDeriv_div s hsq (squarefreeCarlemanDet_ne_zero s)
    hsqAn.differentiableAt hDAn.differentiableAt]
  simp only [xiPrimeLogDirichletContinuation]
  calc
    infinitePrimeFlux s - xiPrimeLogHigherValuation s =
        (infinitePrimeFlux s - 2 * infinitePrimeFlux (2 * s)) +
          (2 * infinitePrimeFlux (2 * s) - xiPrimeLogHigherValuation s) := by ring
    _ = -logDeriv GaloisForLFunctions.squarefreePartition s +
        logDeriv squarefreeCarlemanDet s := by rw [← hsqCurrent, ← hDCurrent]
    _ = -(logDeriv GaloisForLFunctions.squarefreePartition s -
        logDeriv squarefreeCarlemanDet s) := by ring

/-- At a strict-right zeta zero the continued source current has residue minus complete
multiplicity. -/
theorem squarefreeFirstTraceContinuedCurrent_zero_residue
    {rho : ℂ} (hrho : 1 / 2 < rho.re) (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - rho) * squarefreeFirstTraceContinuedCurrent s)
        (𝓝[≠] rho) (𝓝 (-(m : ℂ))) := by
  simpa only [squarefreeFirstTraceContinuedCurrent] using
    xiPrimeLogDirichletContinuation_zero_residue hrho hzeta

/-- Exact decomposition of completed prime--Gamma flux into first-trace anomaly current and two
explicit regular corrections. -/
theorem completedPrimeGammaFlux_eq_firstTrace_add_regular (s : ℂ) :
    completedPrimeGammaFlux s =
      squarefreeFirstTraceContinuedCurrent s +
        xiPrimeLogHigherValuation s - logDeriv archFactor s := by
  simp only [completedPrimeGammaFlux, squarefreeFirstTraceContinuedCurrent,
    xiPrimeLogDirichletContinuation]
  ring

/-! ## Exact source-passivity endpoint -/

/-- Right-source dissipativity stated entirely through the first-trace continuation and its two
explicit regular corrections. -/
def SquarefreeFirstTraceRightDissipative : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 →
    (squarefreeFirstTraceContinuedCurrent s +
      xiPrimeLogHigherValuation s - logDeriv archFactor s).re ≤ 0

/-- Completed flux is odd under functional-equation reflection away from strip zeros. -/
theorem completedPrimeGammaFlux_one_sub_eq_neg
    {s : ℂ} (hstrip : 0 < s.re ∧ s.re < 1)
    (hzeta : riemannZeta s ≠ 0) (hzetaRef : riemannZeta (1 - s) ≠ 0) :
    completedPrimeGammaFlux (1 - s) = -completedPrimeGammaFlux s := by
  have hrefStrip : 0 < (1 - s).re ∧ (1 - s).re < 1 := by
    change 0 < 1 - s.re ∧ 1 - s.re < 1
    constructor <;> linarith [hstrip.1, hstrip.2]
  have hs := seamFluxCochain_eq_infinitePrimeFlux_add_archimedean hstrip hzeta
  have href :=
    seamFluxCochain_eq_infinitePrimeFlux_add_archimedean hrefStrip hzetaRef
  have hs' : completedPrimeGammaFlux s = seamFluxCochain s := by
    simpa only [completedPrimeGammaFlux] using hs.symm
  have href' : completedPrimeGammaFlux (1 - s) = seamFluxCochain (1 - s) := by
    simpa only [completedPrimeGammaFlux] using href.symm
  rw [href', seamFluxCochain, logDeriv_xi_one_sub,
    ← seamFluxCochain, ← hs']

/-- The source-passivity law is a sharp unconditional producer target: proving it closes RH. -/
theorem riemannHypothesis_of_squarefreeFirstTraceRightDissipative
    (hsource : SquarefreeFirstTraceRightDissipative) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_completedPrimeGammaLeftHalfAccretive
  intro s hspos hshalf hzeta
  let r : ℂ := 1 - s
  have hrhalf : 1 / 2 < r.re := by
    dsimp only [r]
    change 1 / 2 < 1 - s.re
    linarith
  have hrone : r.re < 1 := by
    dsimp only [r]
    change 1 - s.re < 1
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hshalf
    norm_num at hshalf
  have hr1 : r ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [r] at hre
    norm_num only [sub_re, one_re] at hre
    linarith
  have hxi : xi s ≠ 0 := (xi_eq_zero_iff hspos hs1).not.mpr hzeta
  have hxiRef : xi r ≠ 0 := by
    dsimp only [r]
    rw [xi_one_sub]
    exact hxi
  have hzetaRef : riemannZeta r ≠ 0 :=
    (xi_eq_zero_iff (by dsimp only [r]; linarith) hr1).not.mp hxiRef
  have hright := hsource r hrhalf hrone hzetaRef
  rw [← completedPrimeGammaFlux_eq_firstTrace_add_regular] at hright
  have hreflect := completedPrimeGammaFlux_one_sub_eq_neg
    (s := s) ⟨hspos, by linarith⟩ hzeta (by simpa only [r] using hzetaRef)
  change completedPrimeGammaFlux r = -completedPrimeGammaFlux s at hreflect
  rw [hreflect] at hright
  change 0 ≤ (completedPrimeGammaFlux s).re
  simpa using hright

end

end RHTower
