import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSumOfAProfileConvergesAfterOneSubtraction
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.GammaRealHalfPlane
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-!
# The pairings of a profile with a probe grow at most linearly

The pairings of a profile `F` of the energy domain with the probe `e_p` are controlled in the
exponent `p`, each on the half-plane where it is used:

* the Gamma pairing in Lévy form is `O(1 + |p|)` on `Re p ≥ 0`: the Lévy kernel is `O(|p| x + √x)`
  for `|p| x ≤ 1` and bounded beyond, against a density `≤ 3/(2x)` near the origin;
* the prime tail is bounded on `Re p ≥ -1`, the head term on `Re p ≤ 0`, the prime heads on
  `Re p ≤ -1`; hence the left form of the remainder is bounded on `Re p ≤ -1`;
* `Γℝ'/Γℝ(s) = O(1 + |s|)` on `Re s ≥ ½`, from `ψ(z) = log z + O(1/|z|)`.

No bound on `ζ'/ζ` inside the strip enters: these are the growth inputs of the Liouville argument
for the explicit formula on the domain.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The archimedean factor -/

theorem norm_half_arg (w : ℂ) : ‖w / 2‖ = ‖w‖ / 2 := by
  rw [show w / 2 = ((1 / 2 : ℝ) : ℂ) * w by push_cast; ring, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by norm_num)]
  ring

theorem re_half_arg (w : ℂ) : (w / 2).re = w.re / 2 := by
  rw [show w / 2 = ((1 / 2 : ℝ) : ℂ) * w by push_cast; ring, Complex.re_ofReal_mul]
  ring

theorem re_one_half : ((1 : ℂ) / 2).re = 1 / 2 := by
  rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- `Γℝ'/Γℝ` is holomorphic on `Re s > 0`. -/
theorem differentiableAt_logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (logDeriv Complex.Gammaℝ) s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓ : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} := fun z hz =>
    (differentiableAt_Gammaℝ_of_re_pos hz).differentiableWithinAt
  have hd : DifferentiableOn ℂ (deriv Complex.Gammaℝ) {z : ℂ | 0 < z.re} := hΓ.deriv hU
  have hq : DifferentiableOn ℂ (fun z => deriv Complex.Gammaℝ z / Complex.Gammaℝ z)
      {z : ℂ | 0 < z.re} := hd.div hΓ fun z hz => Complex.Gammaℝ_ne_zero_of_re_pos hz
  exact (hq.differentiableAt (hU.mem_nhds hs)).congr_of_eventuallyEq
    (Eventually.of_forall fun z => logDeriv_apply _ z)

/-- **`Γℝ'/Γℝ(s) = O(1 + |s|)` on `Re s ≥ ½`.** Near the origin the digamma function is bounded on a
compact set; beyond it `ψ(z) = log z + O(1/|z|)`. -/
theorem exists_bound_logDeriv_Gammaℝ :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → ‖logDeriv Complex.Gammaℝ s‖ ≤ C * (1 + ‖s‖) := by
  have hK : IsCompact ({z : ℂ | 1 / 4 ≤ z.re} ∩ closedBall (0 : ℂ) 2) :=
    (isCompact_closedBall 0 2).inter_left (isClosed_le continuous_const Complex.continuous_re)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (digamma_continuousOn_re_pos.mono fun z hz => by
      have h : 1 / 4 ≤ z.re := hz.1
      show 0 < z.re
      linarith)
  have hpi := Real.pi_pos
  have hMabs := le_abs_self M
  have hMn := abs_nonneg M
  have hlogn := abs_nonneg (Real.log Real.pi)
  refine ⟨|Real.log Real.pi| / 2 + (|M| + Real.pi + 3 / 2) / 2 + 1, by positivity, fun s hs => ?_⟩
  have hre : (s / 2).re = s.re / 2 := re_half_arg s
  have hn : ‖s / 2‖ = ‖s‖ / 2 := norm_half_arg s
  have hpos : 0 < (s / 2).re := by rw [hre]; linarith
  have hsn := norm_nonneg s
  have hdig : ‖Complex.digamma (s / 2)‖ ≤ |M| + Real.pi + 3 / 2 + ‖s‖ / 2 := by
    rcases le_or_gt ‖s / 2‖ 2 with hsmall | hbig
    · have h1 := hM (s / 2) ⟨by show 1 / 4 ≤ (s / 2).re; rw [hre]; linarith,
        by rw [mem_closedBall, dist_zero_right]; exact hsmall⟩
      linarith
    · have h1 := HTGeometry.norm_digamma_sub_log_le_of_re_pos hpos hbig.le
      have h2 := norm_sub_norm_le (Complex.digamma (s / 2)) (Complex.log (s / 2))
      have h3 : 3 / ‖s / 2‖ ≤ 3 / 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hbig.le
      have h4 : ‖Complex.log (s / 2)‖ ≤ ‖s / 2‖ + Real.pi := by
        have ha := Complex.norm_le_abs_re_add_abs_im (Complex.log (s / 2))
        rw [Complex.log_re, Complex.log_im] at ha
        have hb := Complex.abs_arg_le_pi (s / 2)
        have hc : |Real.log ‖s / 2‖| ≤ ‖s / 2‖ := by
          rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
          have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ‖s / 2‖)
          linarith
        linarith
      linarith
  rw [logDeriv_Gammaℝ_eq (by linarith)]
  have e1 : ‖-((Real.log Real.pi : ℂ) / 2)‖ = |Real.log Real.pi| / 2 := by
    rw [norm_neg, norm_half_arg, Complex.norm_real, Real.norm_eq_abs]
  have e2 : ‖Complex.digamma (s / 2) / 2‖ = ‖Complex.digamma (s / 2)‖ / 2 := norm_half_arg _
  have hsum := norm_add_le (-((Real.log Real.pi : ℂ) / 2)) (Complex.digamma (s / 2) / 2)
  rw [e1, e2] at hsum
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ |Real.log Real.pi| / 2 +
    (|M| + Real.pi + 3 / 2) / 2) hsn]

/-! ### The Gamma pairing -/

/-- The unit weight on `(0, 1]`. -/
def unitIntervalWeight (x : ℝ) : ℝ := (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x

/-- The part of the dominating profile of the Lévy integrand that does not depend on the exponent:
`x^{-1/2}` on `(0, 1]` and `e^{-x/2}` beyond. -/
def levyFixedDominator (C M : ℝ) (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => 27 / 4 * (M + 1) * x ^ (-(1 / 2) : ℝ)) x +
    (Ioi (1 : ℝ)).indicator (fun x => 8 * C * Real.exp (-(1 / 2) * x)) x

theorem integrable_unitIntervalWeight : Integrable unitIntervalWeight :=
  (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
    measurableSet_Ioc

theorem integrable_levyFixedDominator (C M : ℝ) : Integrable (levyFixedDominator C M) := by
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo, intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
    norm_num
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2) * x)) (Ioi 1) :=
    exp_neg_integrableOn_Ioi _ (by norm_num)
  have h1 : IntegrableOn (fun x : ℝ => 27 / 4 * (M + 1) * x ^ (-(1 / 2) : ℝ)) (Ioc 0 1) :=
    hrpow.const_mul _
  have h2 : IntegrableOn (fun x : ℝ => 8 * C * Real.exp (-(1 / 2) * x)) (Ioi 1) :=
    hexp.const_mul _
  exact (h1.integrable_indicator measurableSet_Ioc).add (h2.integrable_indicator measurableSet_Ioi)

theorem unitIntervalWeight_nonneg (x : ℝ) : 0 ≤ unitIntervalWeight x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem levyFixedDominator_nonneg {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (x : ℝ) :
    0 ≤ levyFixedDominator C M x :=
  add_nonneg
    (Set.indicator_nonneg (fun y hy => mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (Real.rpow_nonneg hy.1.le _)) x)
    (Set.indicator_nonneg (fun y _ => mul_nonneg (mul_nonneg (by norm_num) hC)
      (Real.exp_pos _).le) x)

theorem unitIntervalWeight_of_mem {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : unitIntervalWeight x = 1 := by
  unfold unitIntervalWeight
  exact Set.indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx, hx1⟩) _

theorem unitIntervalWeight_of_gt {x : ℝ} (hx1 : 1 < x) : unitIntervalWeight x = 0 := by
  unfold unitIntervalWeight
  exact Set.indicator_of_notMem (show x ∉ Ioc (0 : ℝ) 1 from fun h => not_le.mpr hx1 h.2) _

theorem levyFixedDominator_near (C M : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    levyFixedDominator C M x = 27 / 4 * (M + 1) * x ^ (-(1 / 2) : ℝ) := by
  unfold levyFixedDominator
  rw [Set.indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx, hx1⟩),
    Set.indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from not_lt.mpr hx1), add_zero]

theorem levyFixedDominator_far (C M : ℝ) {x : ℝ} (hx1 : 1 < x) :
    levyFixedDominator C M x = 8 * C * Real.exp (-(1 / 2) * x) := by
  unfold levyFixedDominator
  rw [Set.indicator_of_notMem (show x ∉ Ioc (0 : ℝ) 1 from fun h => not_le.mpr hx1 h.2),
    Set.indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx1), zero_add]

/-- On `Re p ≥ 0` the Lévy integrand is dominated by `6 C (1+|p|)` on `(0, 1]` plus the fixed
profile, with `C` the half-pole mass: for `(1+|p|) x ≤ 1` by the near bound of the kernel, beyond
it by the far bound and `1/x < 1 + |p|`. -/
theorem norm_levyIntegrand_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : 0 ≤ p.re) (x : ℝ) :
    ‖levyIntegrand F p x‖ ≤ 6 * halfPoleMass F * (1 + ‖p‖) * unitIntervalWeight x +
      levyFixedDominator (halfPoleMass F) (∫ u, F u ^ 2) x := by
  set C := halfPoleMass F with hC
  set M := ∫ u, F u ^ 2 with hM
  have hC0 : 0 ≤ C := halfPoleMass_nonneg F
  have hM0 : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  set P := 1 + ‖p‖ with hP
  have hP1 : 1 ≤ P := by rw [hP]; linarith [norm_nonneg p]
  have hP0 : 0 ≤ P := by linarith
  have hpP : ‖p‖ ≤ P := by rw [hP]; linarith
  have hp12 : -(1 / 2) ≤ p.re := by linarith
  by_cases hx : 0 < x
  · have hval : levyIntegrand F p x = (archLevyDensity x : ℂ) * levyKernel F p x := by
      simp [levyIntegrand, Set.indicator, hx]
    have hfar : ‖levyKernel F p x‖ ≤ 4 * C := by
      have h := norm_levyKernel_le_far hF hp12 hx.le
      have he : Real.exp (-(p.re * x)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hp hx.le))
      calc ‖levyKernel F p x‖ ≤ C * (3 + Real.exp (-(p.re * x))) := h
        _ ≤ C * (3 + 1) := by gcongr
        _ = 4 * C := by ring
    rw [hval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (archLevyDensity_pos hx).le]
    rcases le_or_gt x 1 with hx1 | hx1
    · rw [unitIntervalWeight_of_mem hx hx1, levyFixedDominator_near C M hx hx1, mul_one]
      have hω := archLevyDensity_le_near hx hx1
      have hrp : 0 ≤ 27 / 4 * (M + 1) * x ^ (-(1 / 2) : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg hx.le _)
      by_cases hxP : P * x ≤ 1
      · have hK := norm_levyKernel_le_near hF hpP hp12 hx hxP
        calc archLevyDensity x * ‖levyKernel F p x‖
            ≤ 3 / (2 * x) * (4 * C * P * x + 9 * (Real.sqrt x * (M + 1) / 2)) :=
              mul_le_mul hω hK (norm_nonneg _) (by positivity)
          _ = 6 * C * P + 27 / 4 * (M + 1) * x ^ (-(1 / 2) : ℝ) := by
              rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
              have hsp : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
              have hs2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
              have hx0 : x ≠ 0 := hx.ne'
              have hs0 : Real.sqrt x ≠ 0 := hsp.ne'
              field_simp
              nlinarith [hs2]
      · have hxP' : 1 < P * x := lt_of_not_ge hxP
        have hω' : archLevyDensity x ≤ 3 / 2 * P := by
          refine hω.trans ?_
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        calc archLevyDensity x * ‖levyKernel F p x‖ ≤ 3 / 2 * P * (4 * C) :=
              mul_le_mul hω' hfar (norm_nonneg _) (mul_nonneg (by norm_num) hP0)
          _ = 6 * C * P := by ring
          _ ≤ 6 * C * P + 27 / 4 * (M + 1) * x ^ (-(1 / 2) : ℝ) := le_add_of_nonneg_right hrp
    · rw [unitIntervalWeight_of_gt hx1, levyFixedDominator_far C M hx1, mul_zero, zero_add]
      have hω := archLevyDensity_le_far hx1.le
      calc archLevyDensity x * ‖levyKernel F p x‖
          ≤ 2 * Real.exp (-(x / 2)) * (4 * C) :=
            mul_le_mul hω hfar (norm_nonneg _) (by positivity)
        _ = 8 * C * Real.exp (-(1 / 2) * x) := by
            rw [show -(x / 2) = -(1 / 2) * x by ring]
            ring
  · have hval : levyIntegrand F p x = 0 := by simp [levyIntegrand, Set.indicator, hx]
    rw [hval, norm_zero]
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hP0)
      (unitIntervalWeight_nonneg x)) (levyFixedDominator_nonneg hC0 hM0 x)

/-- **The Gamma pairing in Lévy form is `O(1 + |p|)` on `Re p ≥ 0`.** -/
theorem exists_bound_levyGamma {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℂ, 0 ≤ p.re → ‖levyGamma F p‖ ≤ K * (1 + ‖p‖) := by
  have hC0 : 0 ≤ halfPoleMass F := halfPoleMass_nonneg F
  have hM0 : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hA0 : 0 ≤ ∫ x, unitIntervalWeight x := integral_nonneg unitIntervalWeight_nonneg
  have hB0 : 0 ≤ ∫ x, levyFixedDominator (halfPoleMass F) (∫ u, F u ^ 2) x :=
    integral_nonneg (levyFixedDominator_nonneg hC0 hM0)
  have hθ0 := abs_nonneg (gammaHardyPhaseRate 0)
  refine ⟨2 * |gammaHardyPhaseRate 0| * halfPoleMass F + 6 * halfPoleMass F * (∫ x, unitIntervalWeight x) +
    ∫ x, levyFixedDominator (halfPoleMass F) (∫ u, F u ^ 2) x, by positivity, fun p hp => ?_⟩
  have hpn := norm_nonneg p
  have hL := norm_laplace_le_halfPoleMass hF (by linarith : -(1 / 2) ≤ p.re)
  have hint : ‖∫ x, levyIntegrand F p x‖ ≤ 6 * halfPoleMass F * (1 + ‖p‖) * (∫ x, unitIntervalWeight x) +
      ∫ x, levyFixedDominator (halfPoleMass F) (∫ u, F u ^ 2) x := by
    have hg1 := integrable_unitIntervalWeight.const_mul (6 * halfPoleMass F * (1 + ‖p‖))
    have hg2 := integrable_levyFixedDominator (halfPoleMass F) (∫ u, F u ^ 2)
    calc ‖∫ x, levyIntegrand F p x‖
        ≤ ∫ x, (6 * halfPoleMass F * (1 + ‖p‖) * unitIntervalWeight x +
            levyFixedDominator (halfPoleMass F) (∫ u, F u ^ 2) x) :=
          norm_integral_le_of_norm_le (hg1.add hg2)
            (Eventually.of_forall fun x => norm_levyIntegrand_le hF hp x)
      _ = _ := by rw [integral_add hg1 hg2, integral_const_mul]
  have hθ : ‖2 * (gammaHardyPhaseRate 0 : ℂ) * negativeHalfLineLaplace (cx F) p‖ ≤
      2 * |gammaHardyPhaseRate 0| * halfPoleMass F := by
    rw [show (2 : ℂ) * (gammaHardyPhaseRate 0 : ℂ) = ((2 * gammaHardyPhaseRate 0 : ℝ) : ℂ) by
      push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  have hsplit : ‖levyGamma F p‖ ≤
      ‖2 * (gammaHardyPhaseRate 0 : ℂ) * negativeHalfLineLaplace (cx F) p‖ +
        ‖∫ x, levyIntegrand F p x‖ := norm_add_le _ _
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hθ0 hC0)) hpn,
    mul_nonneg hB0 hpn]

/-! ### The prime sides -/

/-- **The prime tail is bounded on `Re p ≥ -1`.** -/
theorem exists_bound_stateTail {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, ∀ p : ℂ, -1 ≤ p.re → ‖stateTail F p‖ ≤ K := by
  have hsum : Summable fun n : ℕ => vonMangoldtAtom n * (Real.exp (-(4 * Real.log n)) *
      (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * (-1 : ℝ) + 8)) / 2)) := by
    have h := (summable_vonMangoldt_div_rpow (σ := 1 / 2 + 4) (by norm_num)).mul_right
      (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * (-1 : ℝ) + 8)) / 2)
    refine h.congr fun n => ?_
    rw [← vonMangoldtAtom_mul_exp_eq]
    ring
  refine ⟨∑' n : ℕ, vonMangoldtAtom n * (Real.exp (-(4 * Real.log n)) *
    (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * (-1 : ℝ) + 8)) / 2)), fun p hp => ?_⟩
  unfold stateTail
  exact tsum_of_norm_bounded hsum.hasSum fun n => norm_stateTail_term_le_of hF (by norm_num) hp n

/-- **The head term is bounded on `Re p ≤ 0`.** -/
theorem exists_bound_levyHeadTerm {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, ∀ p : ℂ, p.re ≤ 0 → ‖levyHeadTerm F p‖ ≤ K := by
  obtain ⟨g, hg, hgb⟩ := exists_levyHeadTerm_dominator hF (σ := 0) le_rfl (by norm_num)
  exact ⟨∫ x in Ioi (0 : ℝ), g x, fun p hp => norm_integral_le_of_norm_le hg
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => hgb x hx p hp))⟩

/-- **The prime heads are bounded on `Re p ≤ -1`.** -/
theorem exists_bound_primeHead {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, ∀ p : ℂ, p.re ≤ -1 → ‖primeHead F p‖ ≤ K := by
  have hsum := summable_primeHead_bound (F := F) (σ := -1) (by norm_num)
  refine ⟨∑' n : ℕ, vonMangoldtAtom n * Real.exp (-1 * Real.log n) *
    ∫ u, |F u| * Real.exp (-1 * u), fun p hp => ?_⟩
  unfold primeHead
  exact tsum_of_norm_bounded hsum.hasSum fun n => norm_primeHead_term_le hF (by norm_num) hp n

/-- A charge `c/(p + ½)` is at most `2|c|` off the strip `|Re p + ½| < ½`. -/
theorem norm_div_add_half_le (c : ℂ) {p : ℂ} (hp : 1 / 2 ≤ |p.re + 1 / 2|) :
    ‖c / (p + 1 / 2)‖ ≤ 2 * ‖c‖ := by
  have h1 : 1 / 2 ≤ ‖p + 1 / 2‖ := by
    have h := Complex.abs_re_le_norm (p + 1 / 2)
    rw [Complex.add_re, re_one_half] at h
    linarith
  rw [norm_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg c)]

/-- **The left form of the remainder is bounded on `Re p ≤ -1`.** -/
theorem exists_bound_leftRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, ∀ p : ℂ, p.re ≤ -1 → ‖leftRemainder F p‖ ≤ K := by
  obtain ⟨KJ, hJ⟩ := exists_bound_levyHeadTerm hF
  obtain ⟨KS, hS⟩ := exists_bound_primeHead hF
  refine ⟨KJ + KS + ‖negativeHalfLineLaplace (cx F) (1 / 2)‖ +
    2 * ‖negativeHalfLineLaplace (cx F) (-(1 / 2))‖, fun p hp => ?_⟩
  have hP1 : ‖negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2)‖ ≤
      ‖negativeHalfLineLaplace (cx F) (1 / 2)‖ := by
    rw [norm_div]
    have h1 : 1 ≤ ‖p - 1 / 2‖ := by
      have h := Complex.abs_re_le_norm (p - 1 / 2)
      have h2 := neg_le_abs ((p - 1 / 2).re)
      rw [Complex.sub_re, re_one_half] at h h2
      linarith
    exact div_le_self (norm_nonneg _) h1
  have hP2 := norm_div_add_half_le (negativeHalfLineLaplace (cx F) (-(1 / 2))) (p := p) (by
    have h := neg_le_abs (p.re + 1 / 2)
    linarith)
  have hJ' := hJ p (by linarith)
  have hS' := hS p hp
  unfold leftRemainder
  calc ‖levyHeadTerm F p + primeHead F p + negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2) +
        negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)‖
      ≤ ‖levyHeadTerm F p‖ + ‖primeHead F p‖ +
          ‖negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2)‖ +
          ‖negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)‖ :=
        norm_add₄_le
    _ ≤ _ := by linarith

/-- **The regular part of the Lévy remainder is `O(1 + |p|)` on `Re p ≥ 0`.** -/
theorem exists_bound_levyRegularPart {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℂ, 0 ≤ p.re → ‖levyRegularPart F p‖ ≤ K * (1 + ‖p‖) := by
  obtain ⟨KΓ, hKΓ0, hΓ⟩ := exists_bound_levyGamma hF
  obtain ⟨KT, hT⟩ := exists_bound_stateTail hF
  have hKT0 : 0 ≤ KT := (norm_nonneg _).trans (hT 0 (by simp))
  have hm0 := transformMass_nonneg F (-3)
  have hc0 := norm_nonneg (negativeHalfLineLaplace (cx F) (-(1 / 2)))
  refine ⟨KΓ + transformMass F (-3) + KT + 2 * ‖negativeHalfLineLaplace (cx F) (-(1 / 2))‖,
    by positivity, fun p hp => ?_⟩
  have hD := norm_dslope_laplace_le hF (a := 1 / 2) (p := p) (by rw [re_one_half]; norm_num)
    (by linarith)
  have hP2 := norm_div_add_half_le (negativeHalfLineLaplace (cx F) (-(1 / 2))) (p := p) (by
    have h := le_abs_self (p.re + 1 / 2)
    linarith)
  have hΓ' := hΓ p hp
  have hT' := hT p (by linarith)
  have hpn := norm_nonneg p
  have e : levyRegularPart F p = levyGamma F p +
      -dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p + -stateTail F p +
      negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2) := by
    unfold levyRegularPart
    ring
  have h4 : ‖levyRegularPart F p‖ ≤ ‖levyGamma F p‖ +
      ‖dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p‖ + ‖stateTail F p‖ +
      ‖negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)‖ := by
    rw [e]
    calc ‖levyGamma F p + -dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p + -stateTail F p +
          negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)‖
        ≤ ‖levyGamma F p‖ + ‖-dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p‖ +
            ‖-stateTail F p‖ + ‖negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)‖ :=
          norm_add₄_le
      _ = _ := by rw [norm_neg, norm_neg]
  nlinarith [mul_nonneg (add_nonneg (add_nonneg hm0 hKT0) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    hc0)) hpn]

end GaloisForLFunctions.ExclusionOfTheCriticalState
