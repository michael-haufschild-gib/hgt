import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CompensatedWidthFloorAndGroundEnergyRate
import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleSchurDefect
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleBoundaryPrimitives

/-!
# Unconditional Equality of the Polar and Full Restricted-Weil Ground-Energy Rates

This module proves that the unrestricted restricted-Weil ground-energy exponent
`groundEnergyRate` and the pole-constrained ground-energy exponent `polarGroundEnergyRate` are
equal unconditionally (`groundEnergyRate_eq_polarGroundEnergyRate`), and establishes the
unconditional trivial-width floor `CompensatedWidthFloor (1 / 2)` (`compensatedWidthFloor_half`).

## Mathematical mechanism

1. **Unconditional trivial-width floor (`compensatedWidthFloor_half`, `groundEnergyRate_le_half`).**
   Combining the Schur prime-pole defect lower bound `ccmRestrictedWeilSourceQuadratic_ge_schurEdgeEnergy`
   with Cauchy–Schwarz on the rank-two polar operator `ccmPolarOperator a` yields an explicit
   aperture-uniform constant `C > 0` such that `ccmRestrictedWeilGroundEnergy a ≥ −C e^a` at every
   positive aperture `a`. Consequently `CompensatedWidthFloor (1 / 2)` holds unconditionally,
   `groundEnergyRates` is nonempty, `0 ≤ zetaZeroWidth ≤ polarGroundEnergyRate ≤ groundEnergyRate ≤ 1 / 2`,
   and `RiemannHypothesis ↔ groundEnergyRate = 0`.

2. **Uniform $L^2$ control of the singular Gamma polar boundary (`integral_ccmGammaPoleBoundaryLog_sq_le_32`,
   `exists_norm_ccmPolarWeilBoundaryDefect_sq_le_of_zetaZeroWidth_le`).**
   Writing $z = (1 - e^{-t})^{1/4}$ via nested square roots, the elementary inequality
   $z - 1 \le z \log z$ together with $1 - z \le 1 - z^4 = e^{-t}$ gives the pointwise majorant
   $(-\log(1 - e^{-t}))^2 \le 16 e^{-t} / \sqrt{1 - e^{-t}}$, whose exact half-line antiderivative
   $2(\sqrt{1 - e^{-t}} - 1)$ evaluates the integral to $32$. Combining this bound with the
   generalized von Koch Chebyshev error estimate under `zetaZeroWidth ≤ α < 1 / 2` bounds the
   $L^2$ norm squared of `ccmPolarWeilBoundaryDefect a` by $O(a e^{(1 + 4\beta) a})$ for every
   $\beta > \alpha$.

3. **Orthogonal polar-parity decomposition and unconditional rate equality
   (`compensatedWidthFloor_of_polarGroundEnergyRate_lt`, `groundEnergyRate_eq_polarGroundEnergyRate`).**
   Every form vector `v : CCMArchimedeanFormDomain a` splits orthogonally in `suzukiApertureHilbert a`
   into a pole-constrained component `w` (`IsPolarConstrained a w`) and its two parity-pole
   projections along `ccmPolarParityFormVector a (±1)` with norms squared `D_±(a) = 4(\sinh a ± a) ≍ 2 e^a`.
   Given any `σ > polarGroundEnergyRate`:
   - if `1 / 2 ≤ σ`, monotonicity from `CompensatedWidthFloor (1 / 2)` gives `CompensatedWidthFloor σ`;
   - if `σ < 1 / 2`, choosing `polarGroundEnergyRate < α < β < σ` gives `zetaZeroWidth ≤ α < 1 / 2`,
     bounds the constrained block from below by `−C₁ e^{2α a} ‖J w‖²`, bounds the normalized
     two-pole matrix entries via `abs_ccmWeilPoleDiagonal_le` and
     `exists_abs_deficitPrimitive_le_of_zetaZeroWidth_le` by `O(e^{2β a})`, and bounds the
     normalized polar–constrained coupling norm `2 ‖ccmPolarWeilBoundaryDefect a‖ / √D_±(a)` by
     `O(\sqrt{a} e^{(1/2 + 2β) a} / e^{a/2}) = O(\sqrt{a} e^{2β a}) ≤ C₂ e^{2σ a}`.
   Symmetric Cauchy–Schwarz and AM–GM then yield `ccmRestrictedWeilGroundEnergy a ≥ −C_* e^{2σ a}`,
   proving `CompensatedWidthFloor σ` for every `σ > polarGroundEnergyRate` and hence
   `groundEnergyRate = polarGroundEnergyRate` without any zero-clustering hypothesis.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ENNReal BigOperators
open GaloisForLFunctions.HTGeometry RHTower
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCriticalityTheory

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

/-! ## 1. Unconditional trivial-width floor `CompensatedWidthFloor (1 / 2)` and order of `groundEnergyRate` -/

/-- Norm equality between the negative and positive polar aperture vectors via reflection isometry. -/
private theorem norm_ccmPolarApertureVector_neg_half (a : SuzukiPositiveAperture) :
    ‖ccmPolarApertureVector a (-1 / 2)‖ = ‖ccmPolarApertureVector a (1 / 2)‖ := by
  have h := l2ReflectionIsometry.norm_map (ccmPolarL2Vector a (1 / 2))
  change ‖l2Reflection (ccmPolarL2Vector a (1 / 2))‖ = _ at h
  rw [l2Reflection_ccmPolarL2Vector] at h
  change ‖ccmPolarApertureVector a (-(1 / 2))‖ = ‖ccmPolarApertureVector a (1 / 2)‖ at h
  simpa only [neg_div] using h

/-- Cauchy–Schwarz bound on the quadratic form of the rank-two polar operator `ccmPolarOperator a`. -/
theorem abs_re_inner_ccmPolarOperator_le (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    |(inner ℂ (ccmPolarOperator a f) f).re| ≤ 4 * Real.sinh a.1 * ‖f‖ ^ 2 := by
  set hp := ccmPolarApertureVector a (1 / 2)
  set hm := ccmPolarApertureVector a (-1 / 2)
  have hnorm_eq : ‖hm‖ = ‖hp‖ := norm_ccmPolarApertureVector_neg_half a
  have hhp_sq : ‖hp‖ ^ 2 = 2 * Real.sinh a.1 := norm_sq_ccmPolarApertureVector_half a
  have hcs_p : ‖inner ℂ hp f‖ ≤ ‖hp‖ * ‖f‖ := norm_inner_le_norm hp f
  have hcs_m : ‖inner ℂ hm f‖ ≤ ‖hp‖ * ‖f‖ := by
    rw [← hnorm_eq]
    exact norm_inner_le_norm hm f
  have hprod : ‖inner ℂ hm f‖ * ‖inner ℂ hp f‖ ≤ 2 * Real.sinh a.1 * ‖f‖ ^ 2 := by
    calc ‖inner ℂ hm f‖ * ‖inner ℂ hp f‖
        ≤ (‖hp‖ * ‖f‖) * (‖hp‖ * ‖f‖) :=
          mul_le_mul hcs_m hcs_p (norm_nonneg _) (by positivity)
      _ = ‖hp‖ ^ 2 * ‖f‖ ^ 2 := by ring
      _ = 2 * Real.sinh a.1 * ‖f‖ ^ 2 := by rw [hhp_sq]
  calc |(inner ℂ (ccmPolarOperator a f) f).re|
      ≤ ‖inner ℂ (ccmPolarOperator a f) f‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(starRingEnd ℂ) (inner ℂ hm f) * inner ℂ hp f‖ +
          ‖(starRingEnd ℂ) (inner ℂ hp f) * inner ℂ hm f‖ := by
        rw [inner_ccmPolarOperator]
        exact norm_add_le _ _
    _ = 2 * (‖inner ℂ hm f‖ * ‖inner ℂ hp f‖) := by
        simp only [norm_mul, Complex.norm_conj]
        ring
    _ ≤ 4 * Real.sinh a.1 * ‖f‖ ^ 2 := by linarith

/-- Explicit aperture-independent constant bounding `-e^{-a} ccmRestrictedWeilGroundEnergy a`. -/
def trivialWidthGroundConst : ℝ :=
  |2 * gammaHardyPhaseRate 0 - 1| + 2 * Real.log 4 + 16

theorem trivialWidthGroundConst_pos : 0 < trivialWidthGroundConst := by
  unfold trivialWidthGroundConst
  have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

/-- At every positive aperture `a`, the unrestricted restricted-Weil ground energy obeys the
unconditional square-root-scale lower bound `μ(a) ≥ −trivialWidthGroundConst · e^a`. -/
theorem neg_trivialWidthGroundConst_mul_exp_le_groundEnergy (a : SuzukiPositiveAperture) :
    -(trivialWidthGroundConst * Real.exp a.1) ≤ ccmRestrictedWeilGroundEnergy a := by
  have ha0 : 0 < a.1 := a.2
  have hexp1 : 1 ≤ Real.exp a.1 := Real.one_le_exp ha0.le
  have ha_le : a.1 ≤ Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have ha_half : a.1 ≤ 2 * Real.exp (a.1 / 2) := by
    linarith [Real.add_one_le_exp (a.1 / 2)]
  have hexp_half_sq : Real.exp (a.1 / 2) * Real.exp (a.1 / 2) = Real.exp a.1 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have henv : ccmPrimePoleSchurEnvelope a ≤ (2 * Real.log 4 + 14) * Real.exp a.1 := by
    have hmid : 4 * a.1 * Real.exp (a.1 / 2) ≤ 8 * Real.exp a.1 := by
      calc 4 * a.1 * Real.exp (a.1 / 2)
          ≤ 4 * (2 * Real.exp (a.1 / 2)) * Real.exp (a.1 / 2) := by
            nlinarith [Real.exp_pos (a.1 / 2)]
        _ = 8 * (Real.exp (a.1 / 2) * Real.exp (a.1 / 2)) := by ring
        _ = 8 * Real.exp a.1 := by rw [hexp_half_sq]
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    unfold ccmPrimePoleSchurEnvelope
    nlinarith
  have hsinh : 4 * Real.sinh a.1 ≤ 2 * Real.exp a.1 := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (-a.1)]
  have hscalar : -(2 * gammaHardyPhaseRate 0 - 1) ≤
      |2 * gammaHardyPhaseRate 0 - 1| * Real.exp a.1 := by
    calc -(2 * gammaHardyPhaseRate 0 - 1)
        ≤ |2 * gammaHardyPhaseRate 0 - 1| := neg_le_abs _
      _ ≤ |2 * gammaHardyPhaseRate 0 - 1| * Real.exp a.1 := by
        nlinarith [abs_nonneg (2 * gammaHardyPhaseRate 0 - 1)]
  obtain ⟨u, hu_ne, hu_ground⟩ := ccmRestrictedWeilSource_exists_groundFormState a
  set f := ccmArchimedeanFormToAperture a u
  have hf_pos : 0 < ‖f‖ ^ 2 := by positivity
  have hschur := ccmRestrictedWeilSourceQuadratic_ge_schurEdgeEnergy a u
  dsimp only at hschur
  have hpol := (abs_le.mp (abs_re_inner_ccmPolarOperator_le a f)).1
  have hedge : 0 ≤ ccmPrimePoleSchurEnergy a f.1 := ccmPrimePoleSchurEnergy_nonneg a f.1
  have hu_norm : 0 ≤ ‖u.1‖ ^ 2 := sq_nonneg _
  rw [hu_ground] at hschur
  have hprod : -(trivialWidthGroundConst * Real.exp a.1) * ‖f‖ ^ 2 ≤
      ccmRestrictedWeilGroundEnergy a * ‖f‖ ^ 2 := by
    unfold trivialWidthGroundConst
    nlinarith
  exact le_of_mul_le_mul_right hprod hf_pos

/-- **Unconditional trivial-width floor.** `CompensatedWidthFloor (1 / 2)` holds unconditionally. -/
theorem compensatedWidthFloor_half : CompensatedWidthFloor (1 / 2) := by
  rw [compensatedWidthFloor_iff_groundEnergy_ge_neg_exp]
  refine ⟨trivialWidthGroundConst, 0, fun A _ => ?_⟩
  rw [show (2 : ℝ) * (1 / 2) * A.1 = A.1 by ring]
  exact neg_trivialWidthGroundConst_mul_exp_le_groundEnergy A

/-- Monotonicity of `CompensatedWidthFloor`: if `σ ≤ τ`, then `CompensatedWidthFloor σ` implies
`CompensatedWidthFloor τ`. -/
theorem compensatedWidthFloor_mono {σ τ : ℝ} (hστ : σ ≤ τ) (h : CompensatedWidthFloor σ) :
    CompensatedWidthFloor τ := by
  rw [compensatedWidthFloor_iff_groundEnergy_ge_neg_exp] at h ⊢
  obtain ⟨C, A₀, hC⟩ := h
  refine ⟨max C 0, max A₀ 0, fun A hA => ?_⟩
  have hA₀ : A₀ ≤ A.1 := (le_max_left A₀ 0).trans hA
  have hA0 : 0 ≤ A.1 := (le_max_right A₀ 0).trans hA
  have hexp : Real.exp (2 * σ * A.1) ≤ Real.exp (2 * τ * A.1) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hmax : C * Real.exp (2 * σ * A.1) ≤ max C 0 * Real.exp (2 * τ * A.1) := by
    calc C * Real.exp (2 * σ * A.1)
        ≤ max C 0 * Real.exp (2 * σ * A.1) :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
      _ ≤ max C 0 * Real.exp (2 * τ * A.1) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right C 0)
  linarith [hC A hA₀]

/-- Every rate `σ ≥ 1 / 2` satisfies `CompensatedWidthFloor σ` unconditionally. -/
theorem compensatedWidthFloor_of_half_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    CompensatedWidthFloor σ :=
  compensatedWidthFloor_mono hσ compensatedWidthFloor_half

theorem half_mem_groundEnergyRates : (1 / 2 : ℝ) ∈ groundEnergyRates :=
  (mem_groundEnergyRates_iff_compensatedWidthFloor (by norm_num)).mpr compensatedWidthFloor_half

theorem groundEnergyRates_nonempty : groundEnergyRates.Nonempty :=
  ⟨1 / 2, half_mem_groundEnergyRates⟩

theorem bddBelow_groundEnergyRates : BddBelow groundEnergyRates :=
  ⟨0, fun _ h => h.1⟩

theorem groundEnergyRate_nonneg : 0 ≤ groundEnergyRate :=
  le_csInf groundEnergyRates_nonempty fun _ h => h.1

theorem groundEnergyRate_le_half : groundEnergyRate ≤ 1 / 2 :=
  csInf_le bddBelow_groundEnergyRates half_mem_groundEnergyRates

/-- Because `ccmRestrictedWeilGroundEnergy a ≤ ccmRestrictedWeilPolarGroundEnergy a` and
`groundEnergyRates` is unconditionally nonempty, `polarGroundEnergyRate ≤ groundEnergyRate`. -/
theorem polarGroundEnergyRate_le_groundEnergyRate :
    polarGroundEnergyRate ≤ groundEnergyRate :=
  le_csInf groundEnergyRates_nonempty fun _ hσ =>
    polarGroundEnergyRate_le_of_compensatedWidthFloor hσ.1
      ((mem_groundEnergyRates_iff_compensatedWidthFloor hσ.1).mp hσ)

theorem zetaZeroWidth_le_groundEnergyRate :
    zetaZeroWidth ≤ groundEnergyRate :=
  zetaZeroWidth_le_polarGroundEnergyRate.trans polarGroundEnergyRate_le_groundEnergyRate

/-- **Unconditional characterization of `RiemannHypothesis` via `groundEnergyRate`.** -/
theorem riemannHypothesis_iff_groundEnergyRate_eq_zero :
    RiemannHypothesis ↔ groundEnergyRate = 0 := by
  constructor
  · intro hRH
    have h0 : (0 : ℝ) ∈ groundEnergyRates := by
      refine ⟨le_rfl, 0, 0, fun A _ => ?_⟩
      obtain ⟨u, hu_ne, hu_ground⟩ := ccmRestrictedWeilSource_exists_groundFormState A
      have hpos : 0 < ‖ccmArchimedeanFormToAperture A u‖ ^ 2 := by positivity
      have hQ := ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH A u
      rw [hu_ground] at hQ
      have hge : 0 ≤ ccmRestrictedWeilGroundEnergy A := nonneg_of_mul_nonneg_left hQ hpos
      simpa using hge
    exact le_antisymm (csInf_le bddBelow_groundEnergyRates h0) groundEnergyRate_nonneg
  · intro h0
    rw [riemannHypothesis_iff_polarGroundEnergyRate_eq_zero]
    exact le_antisymm (polarGroundEnergyRate_le_groundEnergyRate.trans h0.le)
      polarGroundEnergyRate_nonneg

/-! ## 2. Square-integrability and uniform $L^2$ control of the Gamma polar boundary -/

private theorem ccmGammaPoleBoundaryLog_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ ccmGammaPoleBoundaryLog t := by
  unfold ccmGammaPoleBoundaryLog
  apply neg_nonneg.mpr
  apply Real.log_nonpos
  · exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
  · linarith [Real.exp_pos (-t)]

private theorem ccmGammaPoleBoundaryLog_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ccmGammaPoleBoundaryLog t ≤ ccmGammaPoleBoundaryLog s := by
  unfold ccmGammaPoleBoundaryLog
  apply neg_le_neg
  apply Real.log_le_log
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  · have := Real.exp_le_exp.mpr (show -t ≤ -s by linarith)
    linarith

/-- Pointwise integrable majorant for the squared Gamma endpoint logarithm: writing
`z = √√(1 − e^{-t})`, the concavity bound `z − 1 ≤ z log z` and `1 − z ≤ 1 − z^4 = e^{-t}` yield
`(-log(1 − e^{-t}))² ≤ 16 e^{-t} / √(1 − e^{-t})`. -/
theorem ccmGammaPoleBoundaryLog_sq_le_majorant {t : ℝ} (ht : 0 < t) :
    (ccmGammaPoleBoundaryLog t) ^ 2 ≤
      16 * (Real.exp (-t) / Real.sqrt (1 - Real.exp (-t))) := by
  set w : ℝ := 1 - Real.exp (-t)
  have hexp_lt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hexp_pos : 0 < Real.exp (-t) := Real.exp_pos (-t)
  have hw_pos : 0 < w := sub_pos.mpr hexp_lt
  have hw_lt : w < 1 := by dsimp [w]; linarith
  set s : ℝ := Real.sqrt w
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hw_pos
  have hs_lt : s < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hw_pos.le hw_lt
  set z : ℝ := Real.sqrt s
  have hz_pos : 0 < z := Real.sqrt_pos.mpr hs_pos
  have hz_lt : z < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hs_pos.le hs_lt
  have hz2 : z ^ 2 = s := Real.sq_sqrt hs_pos.le
  have hs2 : s ^ 2 = w := Real.sq_sqrt hw_pos.le
  have hz4 : z ^ 4 = w := by
    calc z ^ 4 = (z ^ 2) ^ 2 := by ring
      _ = s ^ 2 := by rw [hz2]
      _ = w := hs2
  have hlogw : ccmGammaPoleBoundaryLog t = 4 * (-Real.log z) := by
    unfold ccmGammaPoleBoundaryLog
    change -Real.log w = 4 * (-Real.log z)
    rw [← hz4, Real.log_pow]
    push_cast
    ring
  have h1sub : 1 - z ≤ Real.exp (-t) := by
    have hfac : (1 - z) * ((1 + z) * (1 + z ^ 2)) = Real.exp (-t) := by
      calc (1 - z) * ((1 + z) * (1 + z ^ 2))
          = 1 - z ^ 4 := by ring
        _ = 1 - w := by rw [hz4]
        _ = Real.exp (-t) := by dsimp [w]; ring
    have hge1 : 1 ≤ (1 + z) * (1 + z ^ 2) := by nlinarith [sq_nonneg z]
    nlinarith
  have hzlog : z * (-Real.log z) ≤ Real.exp (-t) := by
    have hm := Real.self_sub_one_le_mul_log hz_pos.le
    linarith
  have hprod : z * ccmGammaPoleBoundaryLog t ≤ 4 * Real.exp (-t) := by
    rw [hlogw]
    linarith
  have hprod_nonneg : 0 ≤ z * ccmGammaPoleBoundaryLog t :=
    mul_nonneg hz_pos.le (ccmGammaPoleBoundaryLog_nonneg ht)
  have hsq : s * (ccmGammaPoleBoundaryLog t) ^ 2 ≤ 16 * Real.exp (-t) := by
    have hpow := pow_le_pow_left₀ hprod_nonneg hprod 2
    calc s * (ccmGammaPoleBoundaryLog t) ^ 2
        = (z * ccmGammaPoleBoundaryLog t) ^ 2 := by rw [← hz2]; ring
      _ ≤ (4 * Real.exp (-t)) ^ 2 := hpow
      _ = 16 * (Real.exp (-t) * Real.exp (-t)) := by ring
      _ ≤ 16 * (Real.exp (-t) * 1) := by nlinarith
      _ = 16 * Real.exp (-t) := by ring
  rw [mul_div_assoc', le_div_iff₀ hs_pos]
  linarith

private def boundaryLogSqMajorantPrimitive (t : ℝ) : ℝ :=
  2 * (Real.sqrt (1 - Real.exp (-t)) - 1)

private theorem continuous_boundaryLogSqMajorantPrimitive :
    Continuous boundaryLogSqMajorantPrimitive := by
  unfold boundaryLogSqMajorantPrimitive
  fun_prop

private theorem hasDerivAt_boundaryLogSqMajorantPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt boundaryLogSqMajorantPrimitive
      (Real.exp (-t) / Real.sqrt (1 - Real.exp (-t))) t := by
  have hw_pos : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hexp : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-t)) t := by
    convert (((hasDerivAt_id t).neg).exp).const_sub 1 using 1
    ring
  have hsq := ((hexp.sqrt hw_pos.ne').sub_const 1).const_mul 2
  unfold boundaryLogSqMajorantPrimitive
  refine hsq.congr_deriv ?_
  have hs_ne : Real.sqrt (1 - Real.exp (-t)) ≠ 0 := (Real.sqrt_pos.mpr hw_pos).ne'
  field_simp [hs_ne]

private theorem tendsto_boundaryLogSqMajorantPrimitive_atTop :
    Tendsto boundaryLogSqMajorantPrimitive atTop (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hsub : Tendsto (fun t : ℝ => 1 - Real.exp (-t)) atTop (𝓝 1) := by
    have h1 := tendsto_const_nhds.sub hexp
    rwa [sub_zero] at h1
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-t))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-t))) atTop (𝓝 (Real.sqrt 1)) :=
      (Real.continuous_sqrt.tendsto 1).comp hsub
    rwa [Real.sqrt_one] at h1
  unfold boundaryLogSqMajorantPrimitive
  have h2 := (hsqrt.sub_const 1).const_mul 2
  rwa [show (2 : ℝ) * (1 - 1) = 0 by ring] at h2

private theorem integrableOn_boundaryLogSqMajorant :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / Real.sqrt (1 - Real.exp (-t))) (Ioi 0) volume :=
  integrableOn_Ioi_deriv_of_nonneg (g := boundaryLogSqMajorantPrimitive) (l := 0)
    continuous_boundaryLogSqMajorantPrimitive.continuousWithinAt
    (fun _ ht => hasDerivAt_boundaryLogSqMajorantPrimitive ht)
    (fun t _ => by positivity)
    tendsto_boundaryLogSqMajorantPrimitive_atTop

private theorem integral_Ioi_boundaryLogSqMajorant :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) / Real.sqrt (1 - Real.exp (-t))) = 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := boundaryLogSqMajorantPrimitive) (a := (0 : ℝ))
    continuous_boundaryLogSqMajorantPrimitive.continuousWithinAt
    (fun _ ht => hasDerivAt_boundaryLogSqMajorantPrimitive ht)
    (fun t _ => by positivity)
    tendsto_boundaryLogSqMajorantPrimitive_atTop
  have h0 : boundaryLogSqMajorantPrimitive 0 = -2 := by
    unfold boundaryLogSqMajorantPrimitive
    simp
  rw [h, h0]
  ring

/-- The squared Gamma endpoint logarithm `(-log(1 − e^{-t}))²` is interval-integrable across `t = 0`. -/
theorem intervalIntegrable_ccmGammaPoleBoundaryLog_sq {T : ℝ} (hT : 0 < T) :
    IntervalIntegrable (fun t => (ccmGammaPoleBoundaryLog t) ^ 2) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
  have hmaj : IntegrableOn
      (fun t => 16 * (Real.exp (-t) / Real.sqrt (1 - Real.exp (-t)))) (Ioc 0 T) volume :=
    (integrableOn_boundaryLogSqMajorant.mono_set (fun _ hx => hx.1)).const_mul 16
  refine hmaj.mono'
    ((by unfold ccmGammaPoleBoundaryLog; fun_prop :
      Measurable (fun t : ℝ => (ccmGammaPoleBoundaryLog t) ^ 2)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ccmGammaPoleBoundaryLog_sq_le_majorant ht.1

/-- Uniform horizon-independent bound `∫₀ᵀ (-log(1 − e^{-t}))² dt ≤ 32` for every `T > 0`. -/
theorem integral_ccmGammaPoleBoundaryLog_sq_le_32 {T : ℝ} (hT : 0 < T) :
    (∫ t in 0..T, (ccmGammaPoleBoundaryLog t) ^ 2) ≤ 32 := by
  rw [intervalIntegral.integral_of_le hT.le]
  have hsq : IntegrableOn (fun t => (ccmGammaPoleBoundaryLog t) ^ 2) (Ioc 0 T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      (intervalIntegrable_ccmGammaPoleBoundaryLog_sq hT)
  have hmaj : IntegrableOn
      (fun t => 16 * (Real.exp (-t) / Real.sqrt (1 - Real.exp (-t)))) (Ioc 0 T) volume :=
    (integrableOn_boundaryLogSqMajorant.mono_set (fun _ hx => hx.1)).const_mul 16
  have h1 : (∫ t in Ioc 0 T, (ccmGammaPoleBoundaryLog t) ^ 2) ≤
      ∫ t in Ioc 0 T, 16 * (Real.exp (-t) / Real.sqrt (1 - Real.exp (-t))) := by
    refine integral_mono_ae hsq hmaj ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ccmGammaPoleBoundaryLog_sq_le_majorant ht.1
  have h2 : (∫ t in Ioc 0 T, 16 * (Real.exp (-t) / Real.sqrt (1 - Real.exp (-t)))) ≤
      16 * ∫ t in Ioi (0 : ℝ), Real.exp (-t) / Real.sqrt (1 - Real.exp (-t)) := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine setIntegral_mono_set integrableOn_boundaryLogSqMajorant ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      positivity
    · exact Eventually.of_forall fun _ hx => hx.1
  rw [integral_Ioi_boundaryLogSqMajorant] at h2
  linarith

private theorem ccmGammaPolarBoundary_le_sum_boundaryLog {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ccmGammaPolarBoundary R L ≤ ccmGammaPoleBoundaryLog R + ccmGammaPoleBoundaryLog L := by
  have hR_anti := ccmGammaPoleBoundaryLog_antitone hR (by linarith : R ≤ 2 * R)
  have hR_nn := ccmGammaPoleBoundaryLog_nonneg hR
  have h2L_nn := ccmGammaPoleBoundaryLog_nonneg (by linarith : 0 < 2 * L)
  have heq : ccmGammaPolarBoundary R L =
      (1 / 2) * ccmGammaPoleBoundaryLog (2 * R) + ccmGammaPoleBoundaryLog L -
        (1 / 2) * ccmGammaPoleBoundaryLog (2 * L) := by
    unfold ccmGammaPolarBoundary ccmGammaPoleBoundaryLog
    ring
  linarith

/-- **Subtrivial zero-width $L^2$ bound on `ccmPolarWeilBoundaryDefect a`.** Under
`zetaZeroWidth ≤ α < 1 / 2` and `α < β`, the $L^2$ norm squared of the boundary–arithmetic defect
at aperture `a ≥ 1` is at most `C · a · e^{(1 + 4β) a}`. -/
theorem exists_norm_ccmPolarWeilBoundaryDefect_sq_le_of_zetaZeroWidth_le
    {α β : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2) (hw : zetaZeroWidth ≤ α) (hβ : α < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : SuzukiPositiveAperture, 1 ≤ a.1 →
      ‖ccmPolarWeilBoundaryDefect a‖ ^ 2 ≤ C * a.1 * Real.exp ((1 + 4 * β) * a.1) := by
  have hβ_pos : 0 < β := lt_of_le_of_lt hα hβ
  obtain ⟨K, hK0, hψ⟩ :=
    _root_.RHTower.Sieve.exists_chebyshevPsiReal_error_power_bound_of_xiZeroHalfPlaneBound
      hα hα' ((zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hα).mp hw) (sub_pos.mpr hβ)
  refine ⟨384 + 6 * K ^ 2 + 6 * (Real.log 4 + 5) ^ 2 + 1, by positivity, fun a ha1 => ?_⟩
  have ha0 : 0 < a.1 := a.2
  set d : SoninL2 := (ccmPolarWeilBoundaryDefect a : SoninL2)
  have hd_int : Integrable (fun x : ℝ => ‖d x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable d)).mp (Lp.memLp d)
  have hsq_int := intervalIntegrable_ccmGammaPoleBoundaryLog_sq (show 0 < 2 * a.1 by linarith)
  have hsub_int : IntegrableOn (fun x => (ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2)
      (centralInterval a.1) volume := by
    have hm := (hsq_int.comp_sub_left a.1).symm
    rw [sub_zero, show a.1 - 2 * a.1 = -a.1 by ring] at hm
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp hm
  have hadd_int : IntegrableOn (fun x => (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2)
      (centralInterval a.1) volume := by
    have hp := hsq_int.comp_add_left a.1
    rw [zero_sub, show 2 * a.1 - a.1 = a.1 by ring] at hp
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp hp
  have hconst_int : IntegrableOn
      (fun _ : ℝ => 3 * K ^ 2 * Real.exp ((1 + 4 * β) * a.1) +
        3 * (Real.log 4 + 5) ^ 2 * Real.exp a.1)
      (centralInterval a.1) volume := by
    exact integrableOn_const (by rw [centralInterval, Real.volume_Icc]; exact ENNReal.ofReal_lt_top.ne)
  set M_in : ℝ → ℝ := fun x =>
    6 * Real.exp a.1 * ((ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2 +
      (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2) +
    (3 * K ^ 2 * Real.exp ((1 + 4 * β) * a.1) + 3 * (Real.log 4 + 5) ^ 2 * Real.exp a.1)
  have hM_int : Integrable ((centralInterval a.1).indicator M_in) volume := by
    rw [integrable_indicator_iff (measurableSet_centralInterval a.1)]
    exact (((hsub_int.add hadd_int).const_mul (6 * Real.exp a.1)).add hconst_int)
  have hleft_ne : ∀ᵐ x : ℝ, x ≠ -a.1 := by rw [ae_iff]; simp
  have hright_ne : ∀ᵐ x : ℝ, x ≠ a.1 := by rw [ae_iff]; simp
  have hae_le : (fun x : ℝ => ‖d x‖ ^ 2) ≤ᵐ[volume] (centralInterval a.1).indicator M_in := by
    filter_upwards [ccmPolarWeilBoundaryDefect_coeFn a, hleft_ne, hright_ne] with x hx hneL hneR
    rw [hx]
    by_cases hmem : x ∈ centralInterval a.1
    · rw [indicator_of_mem hmem, indicator_of_mem hmem]
      have hxL : -a.1 < x := lt_of_le_of_ne hmem.1 (Ne.symm hneL)
      have hxR : x < a.1 := lt_of_le_of_ne hmem.2 hneR
      have hR_pos : 0 < a.1 - x := by linarith
      have hL_pos : 0 < a.1 + x := by linarith
      have hnorm_prof : ‖ccmPolarBoundaryArithmeticProfile a x‖ ^ 2 =
          Real.exp x * (ccmGammaPolarBoundary (a.1 - x) (a.1 + x) -
            (Chebyshev.psi (Real.exp (a.1 - x)) - Real.exp (a.1 - x)) -
            ccmReciprocalMangoldtError (a.1 + x)) ^ 2 := by
        unfold ccmPolarBoundaryArithmeticProfile
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
          ← Real.exp_nat_mul, show (2 : ℕ) * (x / 2) = x by push_cast; ring]
      rw [hnorm_prof]
      have h3sq : ∀ u v w : ℝ, (u - v - w) ^ 2 ≤ 3 * u ^ 2 + 3 * v ^ 2 + 3 * w ^ 2 := by
        intro u v w
        nlinarith [sq_nonneg (u + v), sq_nonneg (u + w), sq_nonneg (v - w)]
      have hB_pos := ccmGammaPolarBoundary_pos hR_pos hL_pos
      have hB_sum := ccmGammaPolarBoundary_le_sum_boundaryLog hR_pos hL_pos
      have hB_sq : (ccmGammaPolarBoundary (a.1 - x) (a.1 + x)) ^ 2 ≤
          2 * ((ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2 +
            (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2) := by
        have hp := pow_le_pow_left₀ hB_pos.le hB_sum 2
        nlinarith [sq_nonneg (ccmGammaPoleBoundaryLog (a.1 - x) -
          ccmGammaPoleBoundaryLog (a.1 + x))]
      have hψ_pt : |Chebyshev.psi (Real.exp (a.1 - x)) - Real.exp (a.1 - x)| ≤
          K * Real.exp ((1 / 2 + β) * (a.1 - x)) := by
        have h := hψ (Real.exp (a.1 - x)) (Real.one_le_exp hR_pos.le)
        rw [RHTower.FreeLagTrace.chebyshevPsiReal_eq_psi, ← Real.exp_mul] at h
        convert h using 3
        ring
      have hψ_sq : Real.exp x * (Chebyshev.psi (Real.exp (a.1 - x)) - Real.exp (a.1 - x)) ^ 2 ≤
          K ^ 2 * Real.exp ((1 + 4 * β) * a.1) := by
        have hp := pow_le_pow_left₀ (abs_nonneg _) hψ_pt 2
        rw [sq_abs, mul_pow, ← Real.exp_nat_mul] at hp
        calc Real.exp x * (Chebyshev.psi (Real.exp (a.1 - x)) - Real.exp (a.1 - x)) ^ 2
            ≤ Real.exp x * (K ^ 2 * Real.exp ((2 : ℕ) * ((1 / 2 + β) * (a.1 - x)))) :=
              mul_le_mul_of_nonneg_left hp (Real.exp_pos x).le
          _ = K ^ 2 * Real.exp (x + (2 : ℕ) * ((1 / 2 + β) * (a.1 - x))) := by
              rw [mul_left_comm, ← Real.exp_add]
          _ ≤ K ^ 2 * Real.exp ((1 + 4 * β) * a.1) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg K)
              push_cast
              nlinarith
      have hM_pt := abs_ccmReciprocalMangoldtError_le hL_pos.le
      have hM_sq : Real.exp x * (ccmReciprocalMangoldtError (a.1 + x)) ^ 2 ≤
          (Real.log 4 + 5) ^ 2 * Real.exp a.1 := by
        have hp := pow_le_pow_left₀ (abs_nonneg _) hM_pt 2
        rw [sq_abs] at hp
        have hexp_le : Real.exp x ≤ Real.exp a.1 := Real.exp_le_exp.mpr hmem.2
        calc Real.exp x * (ccmReciprocalMangoldtError (a.1 + x)) ^ 2
            ≤ Real.exp a.1 * (Real.log 4 + 5) ^ 2 :=
              mul_le_mul hexp_le hp (sq_nonneg _) (Real.exp_pos a.1).le
          _ = (Real.log 4 + 5) ^ 2 * Real.exp a.1 := mul_comm _ _
      have hexp_le : Real.exp x ≤ Real.exp a.1 := Real.exp_le_exp.mpr hmem.2
      have hB_exp : Real.exp x * (ccmGammaPolarBoundary (a.1 - x) (a.1 + x)) ^ 2 ≤
          2 * Real.exp a.1 * ((ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2 +
            (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2) := by
        calc Real.exp x * (ccmGammaPolarBoundary (a.1 - x) (a.1 + x)) ^ 2
            ≤ Real.exp a.1 * (2 * ((ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2 +
                (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2)) :=
              mul_le_mul hexp_le hB_sq (sq_nonneg _) (Real.exp_pos a.1).le
          _ = 2 * Real.exp a.1 * ((ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2 +
                (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2) := by ring
      have hsplit := mul_le_mul_of_nonneg_left
        (h3sq (ccmGammaPolarBoundary (a.1 - x) (a.1 + x))
          (Chebyshev.psi (Real.exp (a.1 - x)) - Real.exp (a.1 - x))
          (ccmReciprocalMangoldtError (a.1 + x))) (Real.exp_pos x).le
      dsimp only [M_in]
      linarith
    · simp [indicator_of_notMem hmem]
  have hint_le : (∫ x : ℝ, ‖d x‖ ^ 2) ≤ ∫ x : ℝ, (centralInterval a.1).indicator M_in x :=
    integral_mono_ae hd_int hM_int hae_le
  have hboth_int : IntegrableOn
      (fun x => (ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2 +
        (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2)
      (centralInterval a.1) volume := hsub_int.add hadd_int
  have h6_int : IntegrableOn
      (fun x => 6 * Real.exp a.1 * ((ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2 +
        (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2))
      (centralInterval a.1) volume := hboth_int.const_mul (6 * Real.exp a.1)
  have hsub_eq : (∫ x in centralInterval a.1, (ccmGammaPoleBoundaryLog (a.1 - x)) ^ 2) =
      ∫ t in 0..2 * a.1, (ccmGammaPoleBoundaryLog t) ^ 2 := by
    rw [centralInterval, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_left (fun t => (ccmGammaPoleBoundaryLog t) ^ 2) a.1,
      sub_self, show a.1 - -a.1 = 2 * a.1 by ring]
  have hadd_eq : (∫ x in centralInterval a.1, (ccmGammaPoleBoundaryLog (a.1 + x)) ^ 2) =
      ∫ t in 0..2 * a.1, (ccmGammaPoleBoundaryLog t) ^ 2 := by
    rw [centralInterval, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_add_left (fun t => (ccmGammaPoleBoundaryLog t) ^ 2) a.1,
      add_neg_cancel, show a.1 + a.1 = 2 * a.1 by ring]
  have hM_eval : (∫ x : ℝ, (centralInterval a.1).indicator M_in x) ≤
      384 * Real.exp a.1 +
        2 * a.1 * (3 * K ^ 2 * Real.exp ((1 + 4 * β) * a.1) +
          3 * (Real.log 4 + 5) ^ 2 * Real.exp a.1) := by
    rw [integral_indicator (measurableSet_centralInterval a.1)]
    dsimp only [M_in]
    rw [integral_add h6_int hconst_int, integral_const_mul, integral_add hsub_int hadd_int,
      hsub_eq, hadd_eq, setIntegral_const, measureReal_def, centralInterval, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, show a.1 - -a.1 = 2 * a.1 by ring]
    have h32 := integral_ccmGammaPoleBoundaryLog_sq_le_32 (show 0 < 2 * a.1 by linarith)
    nlinarith [Real.exp_pos a.1]
  have hexp_dom : Real.exp a.1 ≤ Real.exp ((1 + 4 * β) * a.1) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hnorm_d : ‖ccmPolarWeilBoundaryDefect a‖ ^ 2 = ∫ x : ℝ, ‖d x‖ ^ 2 :=
    HTGeometry.norm_l2_sq_eq_integral_norm_sq volume d
  rw [hnorm_d]
  have h1a : Real.exp a.1 ≤ a.1 * Real.exp ((1 + 4 * β) * a.1) := by
    calc Real.exp a.1
        ≤ 1 * Real.exp ((1 + 4 * β) * a.1) := by linarith
      _ ≤ a.1 * Real.exp ((1 + 4 * β) * a.1) :=
          mul_le_mul_of_nonneg_right ha1 (Real.exp_pos _).le
  have h2a : a.1 * Real.exp a.1 ≤ a.1 * Real.exp ((1 + 4 * β) * a.1) :=
    mul_le_mul_of_nonneg_left hexp_dom ha0.le
  nlinarith [hint_le, hM_eval, Real.exp_pos ((1 + 4 * β) * a.1)]

/-! ## 3. Orthogonal 2D polar parity projection and sesquilinear form decomposition -/

/-- The even and odd polar parity form vectors are orthogonal in `suzukiApertureHilbert a`. -/
theorem inner_ccmPolarParityFormVector_opposite (a : SuzukiPositiveAperture) :
    inner ℂ (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1))
      (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))) = 0 := by
  have hpp : inner ℂ (ccmPolarApertureVector a (1 / 2)) (ccmPolarApertureVector a (1 / 2)) =
      ((2 * Real.sinh a.1 : ℝ) : ℂ) := inner_ccmPolarApertureVector_half_self a
  have hmm : inner ℂ (ccmPolarApertureVector a (-1 / 2)) (ccmPolarApertureVector a (-1 / 2)) =
      ((2 * Real.sinh a.1 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmPolarApertureVector a (-1 / 2)),
      norm_ccmPolarApertureVector_neg_half,
      ← inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmPolarApertureVector a (1 / 2)), hpp]
  have hpm : inner ℂ (ccmPolarApertureVector a (1 / 2)) (ccmPolarApertureVector a (-1 / 2)) =
      ((2 * a.1 : ℝ) : ℂ) := by
    simpa only [neg_neg, neg_div] using inner_ccmPolarApertureVector_opposite a (-1 / 2)
  have hmp : inner ℂ (ccmPolarApertureVector a (-1 / 2)) (ccmPolarApertureVector a (1 / 2)) =
      ((2 * a.1 : ℝ) : ℂ) := by
    simpa only [neg_div] using inner_ccmPolarApertureVector_opposite a (1 / 2)
  rw [ccmArchimedeanFormToAperture_polarParity, ccmArchimedeanFormToAperture_polarParity]
  simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_one_smul,
    inner_add_left, inner_add_right, inner_neg_right, hpp, hmm, hpm, hmp]
  ring

/-- Orthogonal coordinate of `v` along `ccmPolarParityFormVector a r` in `suzukiApertureHilbert a`. -/
def ccmPolarParityCoeff (a : SuzukiPositiveAperture) (r : ℝ)
    (v : CCMArchimedeanFormDomain a) : ℂ :=
  inner ℂ (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r))
    (ccmArchimedeanFormToAperture a v) / ((2 * (2 * Real.sinh a.1 + 2 * a.1 * r) : ℝ) : ℂ)

/-- The pole-constrained residual of `v` obtained by subtracting both polar parity projections. -/
def ccmPolarConstrainedPart (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) : CCMArchimedeanFormDomain a :=
  v - (ccmPolarParityCoeff a 1 v • ccmPolarParityFormVector a 1 +
    ccmPolarParityCoeff a (-1) v • ccmPolarParityFormVector a (-1))

/-- `ccmPolarConstrainedPart a v` lies in the pole-constrained submodule (`IsPolarConstrained`). -/
theorem isPolarConstrained_ccmPolarConstrainedPart (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) :
    IsPolarConstrained a (ccmPolarConstrainedPart a v) := by
  let J := ccmArchimedeanFormToAperture a
  let p1 := ccmPolarParityFormVector a 1
  let pm1 := ccmPolarParityFormVector a (-1)
  let c1 := ccmPolarParityCoeff a 1 v
  let cm1 := ccmPolarParityCoeff a (-1) v
  let w := ccmPolarConstrainedPart a v
  have horth1m : inner ℂ (J p1) (J pm1) = 0 := inner_ccmPolarParityFormVector_opposite a
  have horthm1 : inner ℂ (J pm1) (J p1) = 0 := by
    rw [← inner_conj_symm (J pm1) (J p1), horth1m, map_zero]
  have hself1 : inner ℂ (J p1) (J p1) = ((2 * (2 * Real.sinh a.1 + 2 * a.1 * 1) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (J p1), ← Complex.ofReal_pow,
      norm_sq_ccmPolarParityFormVector_physical a (Or.inl rfl)]
  have hselfm1 : inner ℂ (J pm1) (J pm1) =
      ((2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1)) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (J pm1), ← Complex.ofReal_pow,
      norm_sq_ccmPolarParityFormVector_physical a (Or.inr rfl)]
  have hd1 : ((2 * (2 * Real.sinh a.1 + 2 * a.1 * 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos two_pos (polarParityGram_pos a (Or.inl rfl))).ne'
  have hdm1 : ((2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos two_pos (polarParityGram_pos a (Or.inr rfl))).ne'
  have hw1 : inner ℂ (J p1) (J w) = 0 := by
    change inner ℂ (J p1) (J (v - (c1 • p1 + cm1 • pm1))) = 0
    rw [map_sub, map_add, map_smul, map_smul, inner_sub_right, inner_add_right,
      inner_smul_right (E := suzukiApertureHilbert a),
      inner_smul_right (E := suzukiApertureHilbert a),
      hself1, horth1m, mul_zero, add_zero]
    dsimp [c1, ccmPolarParityCoeff, J, p1]
    rw [div_mul_cancel₀ _ hd1, sub_self]
  have hwm1 : inner ℂ (J pm1) (J w) = 0 := by
    change inner ℂ (J pm1) (J (v - (c1 • p1 + cm1 • pm1))) = 0
    rw [map_sub, map_add, map_smul, map_smul, inner_sub_right, inner_add_right,
      inner_smul_right (E := suzukiApertureHilbert a),
      inner_smul_right (E := suzukiApertureHilbert a),
      horthm1, hselfm1, mul_zero, zero_add]
    dsimp [cm1, ccmPolarParityCoeff, J, pm1]
    rw [div_mul_cancel₀ _ hdm1, sub_self]
  have hp_eq : ccmPolarApertureVector a (1 / 2) = (1 / 2 : ℂ) • (J p1 + J pm1) := by
    dsimp [J, p1, pm1]
    rw [ccmArchimedeanFormToAperture_polarParity, ccmArchimedeanFormToAperture_polarParity]
    simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_one_smul]
    module
  have hm_eq : ccmPolarApertureVector a (-1 / 2) = (1 / 2 : ℂ) • (J p1 - J pm1) := by
    dsimp [J, p1, pm1]
    rw [ccmArchimedeanFormToAperture_polarParity, ccmArchimedeanFormToAperture_polarParity]
    simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_one_smul]
    module
  constructor
  · change inner ℂ (ccmPolarApertureVector a (1 / 2)) (J w) = 0
    rw [hp_eq, inner_smul_left (E := suzukiApertureHilbert a), inner_add_left, hw1, hwm1]
    simp
  · change inner ℂ (ccmPolarApertureVector a (-1 / 2)) (J w) = 0
    rw [hm_eq, inner_smul_left (E := suzukiApertureHilbert a), inner_sub_left, hw1, hwm1]
    simp

/-- Pythagorean norm decomposition of `v` into its pole-constrained part and its two orthogonal
polar parity components. -/
theorem norm_sq_eq_constrained_add_polarParity (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormToAperture a v‖ ^ 2 =
      ‖ccmArchimedeanFormToAperture a (ccmPolarConstrainedPart a v)‖ ^ 2 +
        ‖ccmPolarParityCoeff a 1 v‖ ^ 2 * (2 * (2 * Real.sinh a.1 + 2 * a.1 * 1)) +
        ‖ccmPolarParityCoeff a (-1) v‖ ^ 2 * (2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1))) := by
  let J := ccmArchimedeanFormToAperture a
  let w := ccmPolarConstrainedPart a v
  let p1 := ccmPolarParityFormVector a 1
  let pm1 := ccmPolarParityFormVector a (-1)
  let c1 := ccmPolarParityCoeff a 1 v
  let cm1 := ccmPolarParityCoeff a (-1) v
  have hw : IsPolarConstrained a w := isPolarConstrained_ccmPolarConstrainedPart a v
  have hv_eq : J v = J w + (c1 • J p1 + cm1 • J pm1) := by
    have : v = w + (c1 • p1 + cm1 • pm1) := by
      dsimp [w, ccmPolarConstrainedPart, c1, cm1, p1, pm1]
      abel
    simpa only [map_add, map_smul] using congrArg J this
  have hwp1 : inner ℂ (J w) (J p1) = 0 := by
    rw [← inner_conj_symm (J w) (J p1), inner_polarParity_constrained a 1 w hw, map_zero]
  have hwpm1 : inner ℂ (J w) (J pm1) = 0 := by
    rw [← inner_conj_symm (J w) (J pm1), inner_polarParity_constrained a (-1) w hw, map_zero]
  have horth_wp : inner ℂ (J w) (c1 • J p1 + cm1 • J pm1) = 0 := by
    rw [inner_add_right, inner_smul_right (E := suzukiApertureHilbert a),
      inner_smul_right (E := suzukiApertureHilbert a), hwp1, hwpm1]
    simp
  have horth_1m1 : inner ℂ (c1 • J p1) (cm1 • J pm1) = 0 := by
    rw [inner_smul_left (E := suzukiApertureHilbert a),
      inner_smul_right (E := suzukiApertureHilbert a),
      inner_ccmPolarParityFormVector_opposite a]
    simp
  change ‖J v‖ ^ 2 = ‖J w‖ ^ 2 +
    ‖c1‖ ^ 2 * (2 * (2 * Real.sinh a.1 + 2 * a.1 * 1)) +
    ‖cm1‖ ^ 2 * (2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1)))
  rw [hv_eq, norm_add_sq (𝕜 := ℂ), horth_wp, norm_add_sq (𝕜 := ℂ), horth_1m1,
    map_zero, norm_smul, norm_smul, mul_pow, mul_pow,
    show ‖J p1‖ ^ 2 = 2 * (2 * Real.sinh a.1 + 2 * a.1 * 1) from
      norm_sq_ccmPolarParityFormVector_physical a (Or.inl rfl),
    show ‖J pm1‖ ^ 2 = 2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1)) from
      norm_sq_ccmPolarParityFormVector_physical a (Or.inr rfl)]
  ring

private theorem ccmRestrictedWeilForm_conj_symm (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a v u = (starRingEnd ℂ) (ccmRestrictedWeilForm a u v) := by
  unfold ccmRestrictedWeilForm
  rw [map_add]
  have h1 : inner ℂ v u = (starRingEnd ℂ) (inner ℂ u v) := (inner_conj_symm v u).symm
  have h2 : inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a v))
      (ccmArchimedeanFormToAperture a u) =
      (starRingEnd ℂ) (inner ℂ (ccmRestrictedWeilBoundedRemainder a
        (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a v)) := by
    rw [inner_conj_symm (ccmArchimedeanFormToAperture a v)
      (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u))]
    exact (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric _ _
  rw [h1, h2]

private theorem ccmRestrictedWeilSourceQuadratic_add_eq (a : SuzukiPositiveAperture)
    (w p : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a (w + p) =
      ccmRestrictedWeilSourceQuadratic a w + ccmRestrictedWeilSourceQuadratic a p +
        2 * (ccmRestrictedWeilForm a p w).re := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source, ← ccmRestrictedWeilForm_self_re_eq_source,
    ← ccmRestrictedWeilForm_self_re_eq_source]
  have hexp : ccmRestrictedWeilForm a (w + p) (w + p) =
      ccmRestrictedWeilForm a w w + ccmRestrictedWeilForm a p p +
        ccmRestrictedWeilForm a p w + (starRingEnd ℂ) (ccmRestrictedWeilForm a p w) := by
    rw [← ccmRestrictedWeilForm_conj_symm a p w]
    unfold ccmRestrictedWeilForm
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  rw [hexp]
  simp only [Complex.add_re, Complex.conj_re]
  ring

/-- Exact evaluation of the cross sesquilinear pairing between a polar parity vector and a
pole-constrained vector `w`: it equals the $L^2$ inner product against `ccmPolarParityBoundaryDefect`. -/
theorem ccmRestrictedWeilForm_polarParity_constrained_eq (a : SuzukiPositiveAperture)
    {r : ℝ} (w : CCMArchimedeanFormDomain a) (hw : IsPolarConstrained a w) :
    ccmRestrictedWeilForm a (ccmPolarParityFormVector a r) w =
      inner ℂ (ccmPolarParityBoundaryDefect a r) (ccmArchimedeanFormToAperture a w) := by
  have hhalf : ∀ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u →
      ccmRestrictedWeilForm a (ccmPolarFormVector a (1 / 2)) u =
        ccmPolarBoundarySourceFunctional a u := by
    intro u hu
    rw [ccmPolarWeilRepresentative_represents_form]
    change inner ℂ (ccmPolarWeilRepresentative a (1 / 2)) (ccmArchimedeanFormToAperture a u) =
      inner ℂ (ccmPolarWeilBoundaryDefect a) (ccmArchimedeanFormToAperture a u)
    rw [ccmPolarWeilBoundaryDefect, inner_add_left, inner_sub_left,
      inner_smul_left (ccmPolarApertureVector a (1 / 2)) (ccmArchimedeanFormToAperture a u),
      inner_smul_left (ccmPolarApertureVector a (-1 / 2)) (ccmArchimedeanFormToAperture a u),
      hu.1, hu.2]
    simp
  have hnhalf : ccmRestrictedWeilForm a (ccmPolarFormVector a (-1 / 2)) w =
      ccmPolarBoundarySourceFunctional a (ccmArchimedeanFormReflection a w) := by
    have href : ccmRestrictedWeilForm a (ccmPolarFormVector a (-1 / 2)) w =
        ccmRestrictedWeilForm a (ccmPolarFormVector a (1 / 2))
          (ccmArchimedeanFormReflection a w) := by
      have h := ccmRestrictedWeilForm_reflection a (ccmPolarFormVector a (-1 / 2)) w
      simpa only [ccmArchimedeanFormReflection_polar, neg_div, neg_neg] using h.symm
    rw [href]
    exact hhalf _ hw.reflection
  have hlin : ccmRestrictedWeilForm a (ccmPolarParityFormVector a r) w =
      ccmRestrictedWeilForm a (ccmPolarFormVector a (1 / 2)) w +
        (r : ℂ) * ccmRestrictedWeilForm a (ccmPolarFormVector a (-1 / 2)) w := by
    unfold ccmPolarParityFormVector ccmRestrictedWeilForm
    simp only [map_add, map_smul, inner_add_left,
      inner_smul_left (E := CCMArchimedeanFormDomain a),
      inner_smul_left (E := suzukiApertureHilbert a), Complex.conj_ofReal]
    ring
  rw [hlin, hhalf w hw, hnhalf, ← ccmPolarParityBoundarySourceFunctional_eq_inner]
  rfl

private theorem norm_ccmPolarParityBoundaryDefect_le (a : SuzukiPositiveAperture)
    {r : ℝ} (hr : r = 1 ∨ r = -1) :
    ‖ccmPolarParityBoundaryDefect a r‖ ≤ 2 * ‖ccmPolarWeilBoundaryDefect a‖ := by
  have hr_norm : ‖(r : ℂ)‖ = 1 := by
    rcases hr with rfl | rfl <;> simp
  unfold ccmPolarParityBoundaryDefect
  calc ‖ccmPolarWeilBoundaryDefect a +
        (r : ℂ) • suzukiAperturePhysicalReflection a (ccmPolarWeilBoundaryDefect a)‖
      ≤ ‖ccmPolarWeilBoundaryDefect a‖ +
          ‖(r : ℂ) • suzukiAperturePhysicalReflection a (ccmPolarWeilBoundaryDefect a)‖ :=
        norm_add_le _ _
    _ = 2 * ‖ccmPolarWeilBoundaryDefect a‖ := by
        rw [norm_smul, hr_norm, one_mul, (suzukiAperturePhysicalReflection a).norm_map]
        ring

/-! ## 4. Unconditional proof of `groundEnergyRate = polarGroundEnergyRate` -/

private theorem half_exp_le_polarParityGram (a : SuzukiPositiveAperture) (ha4 : 4 ≤ a.1)
    {r : ℝ} (hr : r = 1 ∨ r = -1) :
    (1 / 2) * Real.exp a.1 ≤ 2 * (2 * Real.sinh a.1 + 2 * a.1 * r) := by
  have hquad := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ a.1)
  have hexp_neg : Real.exp (-a.1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  rcases hr with rfl | rfl <;> nlinarith

/-- Single-aperture quadratic-form floor combining a pole-constrained ground-energy bound,
parity-pole diagonal/cross bounds, and a normalized boundary-defect coupling bound. -/
theorem ccmRestrictedWeilGroundEnergy_ge_of_polar_and_defect_bounds
    (a : SuzukiPositiveAperture) (ha4 : 4 ≤ a.1)
    {M₁ M_pole M_cpl E : ℝ} (hM₁ : 0 ≤ M₁) (hM_pole : 0 ≤ M_pole) (hM_cpl : 0 ≤ M_cpl)
    (hE : 0 ≤ E)
    (hμ₀ : -(M₁ * E) ≤ ccmRestrictedWeilPolarGroundEnergy a)
    (h1_entry : -(M_pole * E * (2 * (2 * Real.sinh a.1 + 2 * a.1 * 1))) ≤
      2 * (ccmWeilPoleDiagonal a + ccmWeilPoleCross a))
    (hm1_entry : -(M_pole * E * (2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1)))) ≤
      2 * (ccmWeilPoleDiagonal a - ccmWeilPoleCross a))
    (hquot : ∀ r : ℝ, r = 1 ∨ r = -1 →
      2 * ‖ccmPolarWeilBoundaryDefect a‖ ≤
        M_cpl * E * Real.sqrt (2 * (2 * Real.sinh a.1 + 2 * a.1 * r))) :
    -((M₁ + M_pole + 2 * M_cpl) * E) ≤ ccmRestrictedWeilGroundEnergy a := by
  obtain ⟨v, hv_ne, hv_ground⟩ := ccmRestrictedWeilSource_exists_groundFormState a
  let J := ccmArchimedeanFormToAperture a
  have hv_pos : 0 < ‖J v‖ ^ 2 := by positivity
  let w := ccmPolarConstrainedPart a v
  let c1 := ccmPolarParityCoeff a 1 v
  let cm1 := ccmPolarParityCoeff a (-1) v
  let p1 := ccmPolarParityFormVector a 1
  let pm1 := ccmPolarParityFormVector a (-1)
  let p := c1 • p1 + cm1 • pm1
  let D1 : ℝ := 2 * (2 * Real.sinh a.1 + 2 * a.1 * 1)
  let Dm1 : ℝ := 2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1))
  have hD1_ge : (1 / 2) * Real.exp a.1 ≤ D1 :=
    half_exp_le_polarParityGram a ha4 (Or.inl rfl)
  have hDm1_ge : (1 / 2) * Real.exp a.1 ≤ Dm1 :=
    half_exp_le_polarParityGram a ha4 (Or.inr rfl)
  have hD1_pos : 0 < D1 := lt_of_lt_of_le (by positivity) hD1_ge
  have hDm1_pos : 0 < Dm1 := lt_of_lt_of_le (by positivity) hDm1_ge
  have hw : IsPolarConstrained a w := isPolarConstrained_ccmPolarConstrainedPart a v
  have hv_decomp : v = w + p := by
    dsimp [w, p, ccmPolarConstrainedPart, c1, cm1, p1, pm1]
    abel
  have hpyth : ‖J v‖ ^ 2 = ‖J w‖ ^ 2 + ‖c1‖ ^ 2 * D1 + ‖cm1‖ ^ 2 * Dm1 :=
    norm_sq_eq_constrained_add_polarParity a v
  have hQ_w : -(M₁ * E) * ‖J w‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a w :=
    (mul_le_mul_of_nonneg_right hμ₀ (sq_nonneg _)).trans
      (ccmRestrictedWeilPolarGroundEnergy_mul_le a w hw)
  have hQ_p : -(M_pole * E) * (‖c1‖ ^ 2 * D1 + ‖cm1‖ ^ 2 * Dm1) ≤
      ccmRestrictedWeilSourceQuadratic a p := by
    have hp_eq : p = (c1 + cm1) • ccmPolarFormVector a (1 / 2) +
        (c1 - cm1) • ccmPolarFormVector a (-1 / 2) := by
      dsimp [p, p1, pm1, ccmPolarParityFormVector]
      simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_one_smul]
      module
    have hQ_p_eq : ccmRestrictedWeilSourceQuadratic a p =
        2 * (ccmWeilPoleDiagonal a + ccmWeilPoleCross a) * ‖c1‖ ^ 2 +
          2 * (ccmWeilPoleDiagonal a - ccmWeilPoleCross a) * ‖cm1‖ ^ 2 := by
      rw [hp_eq, ccmWeilPoleCompression_parity_decomposition,
        show (c1 + cm1) + (c1 - cm1) = (2 : ℂ) * c1 by ring,
        show (c1 + cm1) - (c1 - cm1) = (2 : ℂ) * cm1 by ring,
        norm_mul, norm_mul, Complex.norm_two]
      ring
    rw [hQ_p_eq]
    have ht1 := mul_le_mul_of_nonneg_right h1_entry (sq_nonneg ‖c1‖)
    have htm1 := mul_le_mul_of_nonneg_right hm1_entry (sq_nonneg ‖cm1‖)
    dsimp [D1, Dm1] at ht1 htm1 ⊢
    linarith
  have hcross_pair : ∀ (c : ℂ) (r : ℝ) (hr : r = 1 ∨ r = -1),
      2 * |(ccmRestrictedWeilForm a (c • ccmPolarParityFormVector a r) w).re| ≤
        M_cpl * E * (‖c‖ ^ 2 * (2 * (2 * Real.sinh a.1 + 2 * a.1 * r)) + ‖J w‖ ^ 2) := by
    intro c r hr
    let D := 2 * (2 * Real.sinh a.1 + 2 * a.1 * r)
    have hD_ge : (1 / 2) * Real.exp a.1 ≤ D := half_exp_le_polarParityGram a ha4 hr
    have hD_pos : 0 < D := lt_of_lt_of_le (by positivity) hD_ge
    have hform_smul : ccmRestrictedWeilForm a (c • ccmPolarParityFormVector a r) w =
        (starRingEnd ℂ) c * inner ℂ (ccmPolarParityBoundaryDefect a r) (J w) := by
      rw [← ccmRestrictedWeilForm_polarParity_constrained_eq a w hw]
      unfold ccmRestrictedWeilForm
      simp only [map_smul,
        inner_smul_left (E := CCMArchimedeanFormDomain a),
        inner_smul_left (E := suzukiApertureHilbert a)]
      ring
    have hcs : |(ccmRestrictedWeilForm a (c • ccmPolarParityFormVector a r) w).re| ≤
        2 * ‖ccmPolarWeilBoundaryDefect a‖ * ‖c‖ * ‖J w‖ := by
      calc |(ccmRestrictedWeilForm a (c • ccmPolarParityFormVector a r) w).re|
          ≤ ‖ccmRestrictedWeilForm a (c • ccmPolarParityFormVector a r) w‖ :=
            Complex.abs_re_le_norm _
        _ = ‖c‖ * ‖inner ℂ (ccmPolarParityBoundaryDefect a r) (J w)‖ := by
            rw [hform_smul, norm_mul, Complex.norm_conj]
        _ ≤ ‖c‖ * (‖ccmPolarParityBoundaryDefect a r‖ * ‖J w‖) :=
            mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg c)
        _ ≤ ‖c‖ * (2 * ‖ccmPolarWeilBoundaryDefect a‖ * ‖J w‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (norm_ccmPolarParityBoundaryDefect_le a hr) (norm_nonneg _))
              (norm_nonneg c)
        _ = 2 * ‖ccmPolarWeilBoundaryDefect a‖ * ‖c‖ * ‖J w‖ := by ring
    have hq_r : 2 * ‖ccmPolarWeilBoundaryDefect a‖ ≤ M_cpl * E * Real.sqrt D := hquot r hr
    have hamgm : 2 * (Real.sqrt D * ‖c‖ * ‖J w‖) ≤ ‖c‖ ^ 2 * D + ‖J w‖ ^ 2 := by
      have hsq : 0 ≤ (‖c‖ * Real.sqrt D - ‖J w‖) ^ 2 := sq_nonneg _
      have hs2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD_pos.le
      nlinarith
    calc 2 * |(ccmRestrictedWeilForm a (c • ccmPolarParityFormVector a r) w).re|
        ≤ 2 * (2 * ‖ccmPolarWeilBoundaryDefect a‖ * ‖c‖ * ‖J w‖) := by linarith
      _ ≤ 2 * (M_cpl * E * Real.sqrt D * ‖c‖ * ‖J w‖) := by
          have hm := mul_le_mul_of_nonneg_right hq_r
            (mul_nonneg (norm_nonneg c) (norm_nonneg (J w)))
          linarith
      _ = M_cpl * E * (2 * (Real.sqrt D * ‖c‖ * ‖J w‖)) := by ring
      _ ≤ M_cpl * E * (‖c‖ ^ 2 * D + ‖J w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hamgm (mul_nonneg hM_cpl hE)
  have hp_lin : ccmRestrictedWeilForm a p w =
      ccmRestrictedWeilForm a (c1 • p1) w + ccmRestrictedWeilForm a (cm1 • pm1) w := by
    dsimp [p]
    unfold ccmRestrictedWeilForm
    simp only [map_add, inner_add_left]
    ring
  have hcross_total : -(2 * M_cpl * E) * ‖J v‖ ^ 2 ≤
      2 * (ccmRestrictedWeilForm a p w).re := by
    have hc1 := hcross_pair c1 1 (Or.inl rfl)
    have hcm1 := hcross_pair cm1 (-1) (Or.inr rfl)
    change 2 * |(ccmRestrictedWeilForm a (c1 • p1) w).re| ≤
      M_cpl * E * (‖c1‖ ^ 2 * D1 + ‖J w‖ ^ 2) at hc1
    change 2 * |(ccmRestrictedWeilForm a (cm1 • pm1) w).re| ≤
      M_cpl * E * (‖cm1‖ ^ 2 * Dm1 + ‖J w‖ ^ 2) at hcm1
    rw [hp_lin, Complex.add_re]
    have h1L := (abs_le.mp (show |(ccmRestrictedWeilForm a (c1 • p1) w).re| ≤ _ by linarith)).1
    have hm1L := (abs_le.mp (show |(ccmRestrictedWeilForm a (cm1 • pm1) w).re| ≤ _ by linarith)).1
    have hnn1 : 0 ≤ ‖c1‖ ^ 2 * D1 := mul_nonneg (sq_nonneg _) hD1_pos.le
    have hnnm1 : 0 ≤ ‖cm1‖ ^ 2 * Dm1 := mul_nonneg (sq_nonneg _) hDm1_pos.le
    have hC_nn : 0 ≤ M_cpl * E := mul_nonneg hM_cpl hE
    nlinarith [hpyth, mul_nonneg hC_nn hnn1, mul_nonneg hC_nn hnnm1]
  have hQ_v : -((M₁ + M_pole + 2 * M_cpl) * E) * ‖J v‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a v := by
    rw [hv_decomp, ccmRestrictedWeilSourceQuadratic_add_eq]
    have hnn_w : 0 ≤ ‖J w‖ ^ 2 := sq_nonneg _
    have hnn_p : 0 ≤ ‖c1‖ ^ 2 * D1 + ‖cm1‖ ^ 2 * Dm1 := by positivity
    have hC1_nn : 0 ≤ M₁ * E := mul_nonneg hM₁ hE
    have hCp_nn : 0 ≤ M_pole * E := mul_nonneg hM_pole hE
    nlinarith [hpyth, hQ_w, hQ_p, hcross_total,
      mul_nonneg hC1_nn hnn_p, mul_nonneg hCp_nn hnn_w]
  change -( _) * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 ≤ _ at hQ_v
  rw [hv_ground] at hQ_v
  exact le_of_mul_le_mul_right hQ_v hv_pos

/-- **Unconditional polar-to-full rate bridge.** Every rate `σ > polarGroundEnergyRate` satisfies
`CompensatedWidthFloor σ` unconditionally, without any off-line zero-clustering hypothesis. -/
theorem compensatedWidthFloor_of_polarGroundEnergyRate_lt {σ : ℝ}
    (hσ : polarGroundEnergyRate < σ) :
    CompensatedWidthFloor σ := by
  rcases le_or_gt (1 / 2) σ with hhalf | hσ_half
  · exact compensatedWidthFloor_of_half_le hhalf
  · let σ₀ := polarGroundEnergyRate
    have hσ₀_nonneg : 0 ≤ σ₀ := polarGroundEnergyRate_nonneg
    have hgap : 0 < σ - σ₀ := sub_pos.mpr hσ
    let α : ℝ := σ₀ + (σ - σ₀) / 3
    let β : ℝ := σ₀ + 2 * (σ - σ₀) / 3
    have hα_gt : σ₀ < α := by dsimp [α]; linarith
    have hα_nonneg : 0 ≤ α := by linarith
    have hα_half : α < 1 / 2 := by dsimp [α]; linarith
    have hαβ : α < β := by dsimp [α, β]; linarith
    have hβσ : β < σ := by dsimp [β]; linarith
    have hδ : 0 < σ - β := sub_pos.mpr hβσ
    have hw_α : zetaZeroWidth ≤ α :=
      zetaZeroWidth_le_polarGroundEnergyRate.trans hα_gt.le
    obtain ⟨σ₁, hσ₁_mem, hσ₁_lt⟩ := exists_lt_of_csInf_lt
      ⟨1 / 2, half_mem_polarGroundEnergyRates⟩ hα_gt
    obtain ⟨_, C₁, A₁, hC₁⟩ := hσ₁_mem
    obtain ⟨B_prim, hB_prim0, hprim⟩ :=
      exists_abs_deficitPrimitive_le_of_zetaZeroWidth_le hα_nonneg hα_half hw_α hαβ
    obtain ⟨C_def, hC_def0, hdef⟩ :=
      exists_norm_ccmPolarWeilBoundaryDefect_sq_le_of_zetaZeroWidth_le hα_nonneg hα_half hw_α hαβ
    let K_lin : ℝ := |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5
    let C_cross : ℝ := B_prim * (3 / (2 * (σ - β)) + 1) +
      (2 * Real.log 2 + Real.pi + 1) + K_lin / (σ - β) + 1
    let C_pole : ℝ := 4 * (ccmWeilPoleUniformDiagonalBound + C_cross)
    let C_cpl : ℝ := 4 * Real.sqrt (C_def / (4 * (σ - β)) + 1)
    let C_tot : ℝ := max C₁ 0 + C_pole + 2 * C_cpl
    rw [compensatedWidthFloor_iff_groundEnergy_ge_neg_exp]
    refine ⟨C_tot, max 4 A₁, fun a ha_ge => ?_⟩
    have ha4 : 4 ≤ a.1 := (le_max_left 4 A₁).trans ha_ge
    have haA₁ : A₁ ≤ a.1 := (le_max_right 4 A₁).trans ha_ge
    have ha1 : 1 ≤ a.1 := by linarith
    have ha0 : 0 < a.1 := a.2
    have hμ₀ : -(max C₁ 0 * Real.exp (2 * σ * a.1)) ≤ ccmRestrictedWeilPolarGroundEnergy a := by
      have h1 := hC₁ a haA₁
      have hexp : Real.exp (2 * σ₁ * a.1) ≤ Real.exp (2 * σ * a.1) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hm : C₁ * Real.exp (2 * σ₁ * a.1) ≤ max C₁ 0 * Real.exp (2 * σ * a.1) := by
        calc C₁ * Real.exp (2 * σ₁ * a.1)
            ≤ max C₁ 0 * Real.exp (2 * σ₁ * a.1) :=
              mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (Real.exp_pos _).le
          _ ≤ max C₁ 0 * Real.exp (2 * σ * a.1) :=
              mul_le_mul_of_nonneg_left hexp (le_max_right C₁ 0)
      linarith
    have ha_exp_δ : a.1 ≤ (1 / (4 * (σ - β))) * Real.exp (4 * (σ - β) * a.1) := by
      have h := Real.add_one_le_exp (4 * (σ - β) * a.1)
      have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 / (4 * (σ - β)) by positivity)
      have hcancel : (1 / (4 * (σ - β))) * (4 * (σ - β) * a.1 + 1) =
          a.1 + 1 / (4 * (σ - β)) := by
        field_simp [hδ.ne']
      linarith [show (0 : ℝ) ≤ 1 / (4 * (σ - β)) by positivity]
    have ha_exp_2δ : 1 + 2 * a.1 ≤ (3 / (2 * (σ - β))) * Real.exp (2 * (σ - β) * a.1) := by
      have h := Real.add_one_le_exp (2 * (σ - β) * a.1)
      have h3a : 1 + 2 * a.1 ≤ 3 * a.1 := by linarith
      have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 3 / (2 * (σ - β)) by positivity)
      have hcancel : (3 / (2 * (σ - β))) * (2 * (σ - β) * a.1 + 1) =
          3 * a.1 + 3 / (2 * (σ - β)) := by
        field_simp [hδ.ne']
      linarith [show (0 : ℝ) ≤ 3 / (2 * (σ - β)) by positivity]
    have ha_exp_σ : 2 * a.1 ≤ (1 / (σ - β)) * Real.exp ((1 + 2 * σ) * a.1) := by
      have h := Real.add_one_le_exp (2 * (σ - β) * a.1)
      have hexp_le : Real.exp (2 * (σ - β) * a.1) ≤ Real.exp ((1 + 2 * σ) * a.1) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hmul := mul_le_mul_of_nonneg_left (h.trans hexp_le)
        (show 0 ≤ 1 / (σ - β) by positivity)
      have hcancel : (1 / (σ - β)) * (2 * (σ - β) * a.1 + 1) =
          2 * a.1 + 1 / (σ - β) := by
        field_simp [hδ.ne']
      linarith [show (0 : ℝ) ≤ 1 / (σ - β) by positivity]
    have hdiag : |ccmWeilPoleDiagonal a| ≤
        ccmWeilPoleUniformDiagonalBound * Real.exp ((1 + 2 * σ) * a.1) := by
      refine (abs_ccmWeilPoleDiagonal_le a).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith)) ccmWeilPoleUniformDiagonalBound_pos.le
    have hcross : |ccmWeilPoleCross a| ≤ C_cross * Real.exp ((1 + 2 * σ) * a.1) := by
      have hp := hprim (2 * a.1) (by linarith)
      rw [← ccmPoleIntegratedChebyshevDeficit_eq_logPrimitive] at hp
      have hexp_2δ_eq : Real.exp (2 * (σ - β) * a.1) * Real.exp ((1 / 2 + β) * (2 * a.1)) =
          Real.exp ((1 + 2 * σ) * a.1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hp' : |ccmPoleIntegratedChebyshevDeficit a| ≤
          B_prim * (3 / (2 * (σ - β)) + 1) * Real.exp ((1 + 2 * σ) * a.1) := by
        calc |ccmPoleIntegratedChebyshevDeficit a|
            ≤ B_prim * (1 + 2 * a.1) * Real.exp ((1 / 2 + β) * (2 * a.1)) := hp
          _ ≤ B_prim * ((3 / (2 * (σ - β))) * Real.exp (2 * (σ - β) * a.1)) *
                Real.exp ((1 / 2 + β) * (2 * a.1)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left ha_exp_2δ hB_prim0) (Real.exp_pos _).le
          _ = B_prim * (3 / (2 * (σ - β))) *
                (Real.exp (2 * (σ - β) * a.1) * Real.exp ((1 / 2 + β) * (2 * a.1))) := by ring
          _ = B_prim * (3 / (2 * (σ - β))) * Real.exp ((1 + 2 * σ) * a.1) := by rw [hexp_2δ_eq]
          _ ≤ B_prim * (3 / (2 * (σ - β)) + 1) * Real.exp ((1 + 2 * σ) * a.1) := by
              nlinarith [Real.exp_pos ((1 + 2 * σ) * a.1)]
      have hdiff := abs_integratedChebyshevDeficit_sub_weilPoleCross_le a
      have hB := ccmGammaPoleCrossBoundaryMass_le a
      have htri : |ccmWeilPoleCross a| ≤ |ccmPoleIntegratedChebyshevDeficit a| +
          |ccmPoleIntegratedChebyshevDeficit a - ccmWeilPoleCross a| := by
        have h := abs_sub_le (ccmWeilPoleCross a) (ccmPoleIntegratedChebyshevDeficit a) 0
        rw [sub_zero, sub_zero, abs_sub_comm] at h
        linarith
      have h1exp : 1 ≤ Real.exp ((1 + 2 * σ) * a.1) := Real.one_le_exp (by nlinarith)
      have hK_pos : 0 ≤ K_lin := by dsimp [K_lin]; positivity
      have hB_pos : 0 ≤ 2 * Real.log 2 + Real.pi + 1 := by positivity
      have hK_term : K_lin * (2 * a.1) ≤ (K_lin / (σ - β)) * Real.exp ((1 + 2 * σ) * a.1) := by
        calc K_lin * (2 * a.1)
            ≤ K_lin * ((1 / (σ - β)) * Real.exp ((1 + 2 * σ) * a.1)) :=
              mul_le_mul_of_nonneg_left ha_exp_σ hK_pos
          _ = (K_lin / (σ - β)) * Real.exp ((1 + 2 * σ) * a.1) := by ring
      dsimp only [C_cross, K_lin] at *
      nlinarith [mul_le_mul_of_nonneg_left h1exp hB_pos]
    have hdef_a : ‖ccmPolarWeilBoundaryDefect a‖ ≤
        Real.sqrt (C_def / (4 * (σ - β)) + 1) * Real.exp ((1 / 2 + 2 * σ) * a.1) := by
      have hd_sq := hdef a ha1
      have hexp_4δ_eq : Real.exp (4 * (σ - β) * a.1) * Real.exp ((1 + 4 * β) * a.1) =
          Real.exp ((2 : ℕ) * ((1 / 2 + 2 * σ) * a.1)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      have hd_sq' : ‖ccmPolarWeilBoundaryDefect a‖ ^ 2 ≤
          (Real.sqrt (C_def / (4 * (σ - β)) + 1) * Real.exp ((1 / 2 + 2 * σ) * a.1)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
        calc ‖ccmPolarWeilBoundaryDefect a‖ ^ 2
            ≤ C_def * a.1 * Real.exp ((1 + 4 * β) * a.1) := hd_sq
          _ ≤ C_def * ((1 / (4 * (σ - β))) * Real.exp (4 * (σ - β) * a.1)) *
                Real.exp ((1 + 4 * β) * a.1) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left ha_exp_δ hC_def0.le) (Real.exp_pos _).le
          _ = (C_def / (4 * (σ - β))) *
                (Real.exp (4 * (σ - β) * a.1) * Real.exp ((1 + 4 * β) * a.1)) := by ring
          _ = (C_def / (4 * (σ - β))) * Real.exp ((2 : ℕ) * ((1 / 2 + 2 * σ) * a.1)) := by
              rw [hexp_4δ_eq]
          _ ≤ (C_def / (4 * (σ - β)) + 1) * Real.exp ((2 : ℕ) * ((1 / 2 + 2 * σ) * a.1)) := by
              nlinarith [Real.exp_pos ((2 : ℕ) * ((1 / 2 + 2 * σ) * a.1))]
      exact (abs_le_of_sq_le_sq' hd_sq' (by positivity)).2
    have hCp_nonneg : 0 ≤ C_pole := by
      dsimp [C_pole, C_cross, K_lin]
      have := ccmWeilPoleUniformDiagonalBound_pos
      positivity
    have hCcpl_nonneg : 0 ≤ C_cpl := by dsimp [C_cpl]; positivity
    have hexp_split : Real.exp ((1 + 2 * σ) * a.1) =
        Real.exp (2 * σ * a.1) * Real.exp a.1 := by
      rw [← Real.exp_add]; congr 1; ring
    have h1_entry : -(C_pole * Real.exp (2 * σ * a.1) *
        (2 * (2 * Real.sinh a.1 + 2 * a.1 * 1))) ≤
        2 * (ccmWeilPoleDiagonal a + ccmWeilPoleCross a) := by
      have hD1_ge := half_exp_le_polarParityGram a ha4 (Or.inl rfl)
      have hsum : -(2 * (ccmWeilPoleUniformDiagonalBound + C_cross) *
          Real.exp ((1 + 2 * σ) * a.1)) ≤
          2 * (ccmWeilPoleDiagonal a + ccmWeilPoleCross a) := by
        linarith [(abs_le.mp hdiag).1, (abs_le.mp hcross).1]
      have hD_prod : 2 * (ccmWeilPoleUniformDiagonalBound + C_cross) *
          Real.exp ((1 + 2 * σ) * a.1) ≤
          C_pole * Real.exp (2 * σ * a.1) * (2 * (2 * Real.sinh a.1 + 2 * a.1 * 1)) := by
        rw [hexp_split]
        have hm := mul_le_mul_of_nonneg_left hD1_ge
          (mul_nonneg hCp_nonneg (Real.exp_pos (2 * σ * a.1)).le)
        dsimp [C_pole] at hm ⊢
        linarith
      linarith
    have hm1_entry : -(C_pole * Real.exp (2 * σ * a.1) *
        (2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1)))) ≤
        2 * (ccmWeilPoleDiagonal a - ccmWeilPoleCross a) := by
      have hDm1_ge := half_exp_le_polarParityGram a ha4 (Or.inr rfl)
      have hsum : -(2 * (ccmWeilPoleUniformDiagonalBound + C_cross) *
          Real.exp ((1 + 2 * σ) * a.1)) ≤
          2 * (ccmWeilPoleDiagonal a - ccmWeilPoleCross a) := by
        linarith [(abs_le.mp hdiag).1, (abs_le.mp hcross).2]
      have hD_prod : 2 * (ccmWeilPoleUniformDiagonalBound + C_cross) *
          Real.exp ((1 + 2 * σ) * a.1) ≤
          C_pole * Real.exp (2 * σ * a.1) * (2 * (2 * Real.sinh a.1 + 2 * a.1 * (-1))) := by
        rw [hexp_split]
        have hm := mul_le_mul_of_nonneg_left hDm1_ge
          (mul_nonneg hCp_nonneg (Real.exp_pos (2 * σ * a.1)).le)
        dsimp [C_pole] at hm ⊢
        linarith
      linarith
    have hquot : ∀ r : ℝ, r = 1 ∨ r = -1 →
        2 * ‖ccmPolarWeilBoundaryDefect a‖ ≤
          C_cpl * Real.exp (2 * σ * a.1) *
            Real.sqrt (2 * (2 * Real.sinh a.1 + 2 * a.1 * r)) := by
      intro r hr
      have hD_ge := half_exp_le_polarParityGram a ha4 hr
      have hsD_ge : (1 / 2) * Real.exp (a.1 / 2) ≤
          Real.sqrt (2 * (2 * Real.sinh a.1 + 2 * a.1 * r)) := by
        refine Real.le_sqrt_of_sq_le ?_
        calc ((1 / 2) * Real.exp (a.1 / 2)) ^ 2
            = (1 / 4) * Real.exp a.1 := by
              rw [mul_pow, ← Real.exp_nat_mul]
              norm_num
              congr 1; ring
          _ ≤ (1 / 2) * Real.exp a.1 := by linarith [Real.exp_pos a.1]
          _ ≤ 2 * (2 * Real.sinh a.1 + 2 * a.1 * r) := hD_ge
      calc 2 * ‖ccmPolarWeilBoundaryDefect a‖
          ≤ 2 * (Real.sqrt (C_def / (4 * (σ - β)) + 1) *
              Real.exp ((1 / 2 + 2 * σ) * a.1)) := by linarith [hdef_a]
        _ = C_cpl * Real.exp (2 * σ * a.1) * ((1 / 2) * Real.exp (a.1 / 2)) := by
            dsimp [C_cpl]
            have hexp_eq : Real.exp ((1 / 2 + 2 * σ) * a.1) =
                Real.exp (2 * σ * a.1) * Real.exp (a.1 / 2) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [hexp_eq]
            ring
        _ ≤ C_cpl * Real.exp (2 * σ * a.1) *
              Real.sqrt (2 * (2 * Real.sinh a.1 + 2 * a.1 * r)) :=
            mul_le_mul_of_nonneg_left hsD_ge
              (mul_nonneg hCcpl_nonneg (Real.exp_pos (2 * σ * a.1)).le)
    exact ccmRestrictedWeilGroundEnergy_ge_of_polar_and_defect_bounds a ha4
      (le_max_right C₁ 0) hCp_nonneg hCcpl_nonneg (Real.exp_pos (2 * σ * a.1)).le
      hμ₀ h1_entry hm1_entry hquot

/-- **Unconditional equality of the unrestricted and polar restricted-Weil ground-energy rates.**
Removing the two polar constraints cannot increase the exponential ground-energy growth rate. -/
theorem groundEnergyRate_eq_polarGroundEnergyRate :
    groundEnergyRate = polarGroundEnergyRate := by
  refine le_antisymm ?_ polarGroundEnergyRate_le_groundEnergyRate
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlt : polarGroundEnergyRate < polarGroundEnergyRate + ε := by linarith
  have hfloor := compensatedWidthFloor_of_polarGroundEnergyRate_lt hlt
  exact csInf_le bddBelow_groundEnergyRates
    ((mem_groundEnergyRates_iff_compensatedWidthFloor
      (by linarith [polarGroundEnergyRate_nonneg])).mpr hfloor)

/-- **Unconditional equivalence between the compensated width floor above `zetaZeroWidth` and
`polarGroundEnergyRate = zetaZeroWidth`.** Because `groundEnergyRate = polarGroundEnergyRate`
unconditionally, closing the polar rate gap above `zetaZeroWidth` is necessary and sufficient for
the full compensated sampling bound at every rate above `zetaZeroWidth`. -/
theorem forall_compensatedWidthFloor_above_width_iff_polarGroundEnergyRate_eq :
    (∀ σ : ℝ, zetaZeroWidth < σ → CompensatedWidthFloor σ) ↔
      polarGroundEnergyRate = zetaZeroWidth := by
  constructor
  · intro h
    exact (polarGroundEnergyRate_eq_zetaZeroWidth_of_forall_compensatedWidthFloor h).1
  · intro heq σ hσ
    rw [← heq] at hσ
    exact compensatedWidthFloor_of_polarGroundEnergyRate_lt hσ

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
