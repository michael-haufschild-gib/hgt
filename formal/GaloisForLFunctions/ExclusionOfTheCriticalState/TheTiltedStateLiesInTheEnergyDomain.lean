import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerExponentialBarriers
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyDomainIsStableUnderLipschitzMultipliers

/-!
# The tilted state lies in the energy domain

For the critical state `F` and `0 ≤ c ≤ 1` the tilted profile `e^{-cu} F` lies in the energy domain:
the Gamma energy of the state survives an exponential weight. In terms of the transform, `L F` has
finite logarithmic energy `∫ |L F(-c + it)|² log(2 + |t|) dt` on every line `Re p = -c`, not only on
the imaginary axis.

Mechanism (Agmon). For the truncated weight `φ(u) = e^{-c max(u, -N)}` and every `x`,

  `(φF(u) - φF(u+x))² = (F(u) - F(u+x)) (φ²F(u) - φ²F(u+x)) + F(u) F(u+x) (φ(u) - φ(u+x))²`.

Against the Lévy density the first term is the Gamma pairing of `F` with `φ²F`, a profile of the
domain: the weak equation of the state replaces it by prime and pole terms, bounded in the weighted
norm, and a confinement term of favourable sign. The second term is a commutator,
`0 ≤ φ(u) - φ(u+x) ≤ φ(u) min(cx, 1)`. Every bound is uniform in `N`, and Fatou's lemma passes to
the limit `N → ∞`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The truncated weight -/

/-- The truncated exponential weight `e^{-c max(u, -N)}`: equal to `e^{-cu}` on `u ≥ -N` and
constant below. -/
def truncatedTilt (c N u : ℝ) : ℝ := Real.exp (-(c * max u (-N)))

theorem truncatedTilt_pos (c N u : ℝ) : 0 < truncatedTilt c N u := Real.exp_pos _

theorem continuous_truncatedTilt (c N : ℝ) : Continuous (truncatedTilt c N) :=
  Real.continuous_exp.comp ((continuous_const.mul (continuous_id.max continuous_const)).neg)

theorem truncatedTilt_zero (N u : ℝ) : truncatedTilt 0 N u = 1 := by
  simp [truncatedTilt]

theorem truncatedTilt_le_exp_neg {c : ℝ} (hc : 0 ≤ c) (N u : ℝ) :
    truncatedTilt c N u ≤ Real.exp (-(c * u)) :=
  Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (le_max_left u (-N)) hc))

theorem truncatedTilt_le_exp {c : ℝ} (hc : 0 ≤ c) (N u : ℝ) :
    truncatedTilt c N u ≤ Real.exp (c * N) := by
  refine Real.exp_le_exp.mpr ?_
  have := mul_le_mul_of_nonneg_left (le_max_right u (-N)) hc
  linarith

theorem truncatedTilt_eq_exp_neg {c N u : ℝ} (h : -N ≤ u) :
    truncatedTilt c N u = Real.exp (-(c * u)) := by
  rw [truncatedTilt, max_eq_left h]

theorem exp_neg_mul_eq_truncatedTilt (c u : ℝ) :
    Real.exp (-(c * u)) = truncatedTilt c (-u) u :=
  (truncatedTilt_eq_exp_neg (le_of_eq (neg_neg u))).symm

theorem truncatedTilt_sq (c N u : ℝ) : truncatedTilt c N u ^ 2 = truncatedTilt (2 * c) N u := by
  unfold truncatedTilt
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem truncatedTilt_add_le {c : ℝ} (hc : 0 ≤ c) (N u : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    truncatedTilt c N (u + x) ≤ truncatedTilt c N u :=
  Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left
    (max_le_max (by linarith) le_rfl) hc))

theorem truncatedTilt_mul_exp_le {c : ℝ} (hc : 0 ≤ c) (N u : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    truncatedTilt c N u * Real.exp (-(c * x)) ≤ truncatedTilt c N (u + x) := by
  unfold truncatedTilt
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h : max (u + x) (-N) ≤ max u (-N) + x :=
    max_le (by linarith [le_max_left u (-N)]) (by linarith [le_max_right u (-N)])
  have := mul_le_mul_of_nonneg_left h hc
  linarith

/-- The jump of the weight: `(φ(u) - φ(u+x))² ≤ φ(u)² min(cx, 1)²`. -/
theorem truncatedTilt_jump {c : ℝ} (hc : 0 ≤ c) (N u : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (truncatedTilt c N u - truncatedTilt c N (u + x)) ^ 2 ≤
      truncatedTilt c N u ^ 2 * min (c * x) 1 ^ 2 := by
  have h1 := truncatedTilt_add_le hc N u hx
  have h2 := truncatedTilt_mul_exp_le hc N u hx
  have hp := truncatedTilt_pos c N u
  have hp' := truncatedTilt_pos c N (u + x)
  have he : 1 - c * x ≤ Real.exp (-(c * x)) := by
    have := Real.add_one_le_exp (-(c * x))
    linarith
  have h3 := mul_le_mul_of_nonneg_left he hp.le
  have hd : truncatedTilt c N u - truncatedTilt c N (u + x) ≤
      truncatedTilt c N u * min (c * x) 1 := by
    rcases le_total (c * x) 1 with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith
  rw [← mul_pow]
  exact pow_le_pow_left₀ (sub_nonneg.mpr h1) hd 2

theorem abs_exp_sub_exp_le {a b K : ℝ} (ha : a ≤ K) (hb : b ≤ K) :
    |Real.exp a - Real.exp b| ≤ Real.exp K * |a - b| := by
  have key : ∀ p q : ℝ, q ≤ K → Real.exp q - Real.exp p ≤ Real.exp K * |q - p| := by
    intro p q hq
    rcases le_total q p with h | h
    · have h1 : Real.exp q ≤ Real.exp p := Real.exp_le_exp.mpr h
      have h2 : 0 ≤ Real.exp K * |q - p| := mul_nonneg (Real.exp_pos K).le (abs_nonneg _)
      linarith
    · have h1 : Real.exp q * (p - q + 1) ≤ Real.exp p := by
        calc Real.exp q * (p - q + 1) ≤ Real.exp q * Real.exp (p - q) :=
              mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos q).le
          _ = Real.exp p := by
              rw [← Real.exp_add]
              congr 1
              ring
      have h2 : Real.exp q * (q - p) ≤ Real.exp K * (q - p) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hq) (sub_nonneg.mpr h)
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      linarith
  rw [abs_le]
  constructor
  · have := key a b hb
    rw [abs_sub_comm] at this
    linarith
  · exact key b a ha

theorem truncatedTilt_lipschitz {c : ℝ} (hc : 0 ≤ c) (N u v : ℝ) :
    |truncatedTilt c N u - truncatedTilt c N v| ≤ c * Real.exp (c * N) * |u - v| := by
  have hb : ∀ w : ℝ, -(c * max w (-N)) ≤ c * N := fun w => by
    have := mul_le_mul_of_nonneg_left (le_max_right w (-N)) hc
    linarith
  have h1 := abs_exp_sub_exp_le (hb u) (hb v)
  have h2 : |-(c * max u (-N)) - -(c * max v (-N))| ≤ c * |u - v| := by
    have e : -(c * max u (-N)) - -(c * max v (-N)) = -(c * (max u (-N) - max v (-N))) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs u v (-N)) hc
  calc |truncatedTilt c N u - truncatedTilt c N v|
      ≤ Real.exp (c * N) * |-(c * max u (-N)) - -(c * max v (-N))| := h1
    _ ≤ Real.exp (c * N) * (c * |u - v|) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = c * Real.exp (c * N) * |u - v| := by ring

/-- The truncated tilts of a profile of the domain lie in the domain. -/
theorem criticalHalfLineEnergyDomain_truncatedTilt_mul {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc : 0 ≤ c) (N : ℝ) :
    CriticalHalfLineEnergyDomain (fun u => truncatedTilt c N u * F u) :=
  criticalHalfLineEnergyDomain_lipschitz_mul hF (continuous_truncatedTilt c N).measurable
    (fun u => by
      rw [abs_of_pos (truncatedTilt_pos c N u)]
      exact truncatedTilt_le_exp hc N u)
    (truncatedTilt_lipschitz hc N)

/-! ### Sizes in the weighted norms -/

theorem sq_le_sq_mul_exp_of_support {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) (u : ℝ) :
    F u ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u)) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [hsupp u hu]
    simp
  · exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by linarith))

/-- For `c ≤ 3`: `(e^{|u|} φ(u) F(u))² ≤ F(u)² e^{-8u}`. -/
theorem sq_exp_abs_mul_truncatedTilt_mul_le {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) {c : ℝ}
    (hc0 : 0 ≤ c) (hc3 : c ≤ 3) (N u : ℝ) :
    (Real.exp |u| * (truncatedTilt c N u * F u)) ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u)) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [hsupp u hu]
    simp
  · have h1 : Real.exp |u| * truncatedTilt c N u ≤ Real.exp (-(4 * u)) := by
      rw [abs_of_neg hu]
      calc Real.exp (-u) * truncatedTilt c N u ≤ Real.exp (-u) * Real.exp (-(c * u)) :=
            mul_le_mul_of_nonneg_left (truncatedTilt_le_exp_neg hc0 N u) (Real.exp_pos _).le
        _ = Real.exp (-u + -(c * u)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-(4 * u)) := Real.exp_le_exp.mpr (by
            nlinarith [mul_nonneg (sub_nonneg.mpr hc3) (neg_nonneg.mpr hu.le)])
    have h0 : 0 ≤ Real.exp |u| * truncatedTilt c N u :=
      mul_nonneg (Real.exp_pos _).le (truncatedTilt_pos c N u).le
    have h2 : (Real.exp |u| * truncatedTilt c N u) ^ 2 ≤ Real.exp (-(8 * u)) := by
      calc (Real.exp |u| * truncatedTilt c N u) ^ 2 ≤ Real.exp (-(4 * u)) ^ 2 :=
            pow_le_pow_left₀ h0 h1 2
        _ = Real.exp (-(8 * u)) := by
            rw [sq, ← Real.exp_add]
            congr 1
            ring
    calc (Real.exp |u| * (truncatedTilt c N u * F u)) ^ 2
        = (Real.exp |u| * truncatedTilt c N u) ^ 2 * F u ^ 2 := by ring
      _ ≤ Real.exp (-(8 * u)) * F u ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = F u ^ 2 * Real.exp (-(8 * u)) := mul_comm _ _

theorem sq_truncatedTilt_mul_le {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) {c : ℝ}
    (hc0 : 0 ≤ c) (hc3 : c ≤ 3) (N u : ℝ) :
    (truncatedTilt c N u * F u) ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u)) := by
  refine le_trans ?_ (sq_exp_abs_mul_truncatedTilt_mul_le hsupp hc0 hc3 N u)
  rw [mul_pow (Real.exp |u|)]
  exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (Real.one_le_exp (abs_nonneg u)))

theorem exponentialSourceMass_truncatedTilt_mul_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc0 : 0 ≤ c) (hc3 : c ≤ 3) (N : ℝ) :
    exponentialSourceMass (fun u => truncatedTilt c N u * F u) ≤
      ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
  integral_mono (criticalHalfLineEnergyDomain_truncatedTilt_mul hF hc0 N).weighted.sq
    hF.exponential (fun u => sq_exp_abs_mul_truncatedTilt_mul_le hF.support hc0 hc3 N u)

theorem truncatedTilt_zero_mul (F : ℝ → ℝ) : (fun u => truncatedTilt 0 0 u * F u) = F :=
  funext fun u => by rw [truncatedTilt_zero, one_mul]

theorem exponentialSourceMass_le_exponential {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    exponentialSourceMass F ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  have h := exponentialSourceMass_truncatedTilt_mul_le hF le_rfl (by norm_num : (0 : ℝ) ≤ 3) 0
  rwa [truncatedTilt_zero_mul] at h

/-- The pairing `∫ F · φF` is nonnegative and at most the confinement mass. -/
theorem integral_mul_truncatedTilt_mul_nonneg_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc0 : 0 ≤ c) (hc3 : c ≤ 3) (N : ℝ) :
    0 ≤ (∫ u, F u * (truncatedTilt c N u * F u)) ∧
      (∫ u, F u * (truncatedTilt c N u * F u)) ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hF hc0 N
  have hi : Integrable fun u => F u * (truncatedTilt c N u * F u) :=
    integrable_mul_of_memLp hF.memLp_real hG.memLp_real
  have hnn : ∀ u, 0 ≤ F u * (truncatedTilt c N u * F u) := fun u => by
    have e : F u * (truncatedTilt c N u * F u) = truncatedTilt c N u * F u ^ 2 := by ring
    rw [e]
    exact mul_nonneg (truncatedTilt_pos c N u).le (sq_nonneg _)
  have hle : ∀ u, F u * (truncatedTilt c N u * F u) ≤ F u ^ 2 * Real.exp (-(8 * u)) := fun u => by
    have h1 := sq_le_sq_mul_exp_of_support hF.support u
    have h2 := sq_truncatedTilt_mul_le hF.support hc0 hc3 N u
    nlinarith [sq_nonneg (F u - truncatedTilt c N u * F u)]
  exact ⟨integral_nonneg hnn, integral_mono hi hF.exponential hle⟩

/-- For `c ≤ 2` and a kernel of size `e^{|u|/2}`: `|φ(u) F(u) k| ≤ |F(u)| e^{-5u/2}`. -/
theorem abs_truncatedTilt_mul_kernel_le {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) {c : ℝ}
    (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (N u : ℝ) {k : ℝ} (hk : |k| ≤ Real.exp (|u| / 2)) :
    |truncatedTilt c N u * F u * k| ≤ |F u| * Real.exp (-(5 / 2) * u) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [hsupp u hu]
    simp
  · rw [abs_mul, abs_mul, abs_of_pos (truncatedTilt_pos c N u)]
    have h1 : truncatedTilt c N u * |k| ≤ Real.exp (-(5 / 2) * u) := by
      calc truncatedTilt c N u * |k| ≤ Real.exp (-(c * u)) * Real.exp (|u| / 2) :=
            mul_le_mul (truncatedTilt_le_exp_neg hc0 N u) hk (abs_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (-(c * u) + |u| / 2) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-(5 / 2) * u) := Real.exp_le_exp.mpr (by
            rw [abs_of_neg hu]
            nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (neg_nonneg.mpr hu.le)])
    calc truncatedTilt c N u * |F u| * |k| = |F u| * (truncatedTilt c N u * |k|) := by ring
      _ ≤ |F u| * Real.exp (-(5 / 2) * u) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem abs_integral_truncatedTilt_mul_kernel_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (N : ℝ) {k : ℝ → ℝ}
    (hk : ∀ u, |k u| ≤ Real.exp (|u| / 2)) :
    |∫ u, truncatedTilt c N u * F u * k u| ≤ ∫ u, |F u| * Real.exp (-(5 / 2) * u) := by
  have h := norm_integral_le_of_norm_le (f := fun u => truncatedTilt c N u * F u * k u)
    (integrable_abs_mul_exp_of_domain hF (c := -(5 / 2)) (by norm_num))
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      exact abs_truncatedTilt_mul_kernel_le hF.support hc0 hc2 N u (hk u))
  rwa [Real.norm_eq_abs] at h

theorem abs_coshHalfMoment_truncatedTilt_mul_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (N : ℝ) :
    |coshHalfMoment (fun u => truncatedTilt c N u * F u)| ≤
      ∫ u, |F u| * Real.exp (-(5 / 2) * u) :=
  abs_integral_truncatedTilt_mul_kernel_le hF hc0 hc2 N (k := fun u => Real.cosh (u / 2))
    abs_cosh_half_le_exp

theorem abs_sinhHalfMoment_truncatedTilt_mul_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (N : ℝ) :
    |sinhHalfMoment (fun u => truncatedTilt c N u * F u)| ≤
      ∫ u, |F u| * Real.exp (-(5 / 2) * u) :=
  abs_integral_truncatedTilt_mul_kernel_le hF hc0 hc2 N (k := fun u => Real.sinh (u / 2))
    abs_sinh_half_le_exp

theorem abs_coshHalfMoment_le_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    |coshHalfMoment F| ≤ ∫ u, |F u| * Real.exp (-(5 / 2) * u) := by
  have h := abs_coshHalfMoment_truncatedTilt_mul_le hF le_rfl (by norm_num : (0 : ℝ) ≤ 2) 0
  rwa [truncatedTilt_zero_mul] at h

theorem abs_sinhHalfMoment_le_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    |sinhHalfMoment F| ≤ ∫ u, |F u| * Real.exp (-(5 / 2) * u) := by
  have h := abs_sinhHalfMoment_truncatedTilt_mul_le hF le_rfl (by norm_num : (0 : ℝ) ≤ 2) 0
  rwa [truncatedTilt_zero_mul] at h

/-- The mixed prime form is bounded by the weighted masses. -/
theorem abs_primeMixedForm_le {f g : ℝ → ℝ} (hf : WeightedTwo f) (hg : WeightedTwo g) :
    |primeMixedForm f g| ≤ 2 * vonMangoldtThreeHalvesMass *
      (Real.sqrt (exponentialSourceMass f) * Real.sqrt (exponentialSourceMass g)) := by
  have hs := summable_primePairTerm hf hg
  have hsumB := (summable_vonMangoldt_div_threeHalves.mul_left 2).mul_right
    (Real.sqrt (exponentialSourceMass f) * Real.sqrt (exponentialSourceMass g))
  have hnorm := norm_tsum_le_tsum_norm hs.norm
  simp only [Real.norm_eq_abs] at hnorm
  unfold primeMixedForm
  refine hnorm.trans ((hs.abs.tsum_le_tsum (abs_primePairTerm_le hf hg) hsumB).trans_eq ?_)
  rw [tsum_mul_right, tsum_mul_left]
  rfl

/-! ### The commutator -/

/-- **The localization identity with its commutator bound.** For every lag `x > 0` the jump
integral of `φF` exceeds the mixed jump integral of `F` and `φ²F` by at most
`min(cx, 1)² ∫ F² e^{-8u}`. -/
theorem integral_sq_jump_truncatedTilt_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (N : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
      (∫ u, (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
        truncatedTilt (2 * c) N (u + x) * F (u + x))) ≤
        min (c * x) 1 ^ 2 * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  have h2c : (0 : ℝ) ≤ 2 * c := by positivity
  have hH := criticalHalfLineEnergyDomain_truncatedTilt_mul hF hc0 N
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hF h2c N
  have hFm := hF.memLp_real
  have hHm := hH.memLp_real
  have hGm := hG.memLp_real
  have iH : Integrable fun u =>
      (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 :=
    integrable_sq_of_memLp (hHm.sub (memLp_two_shift hHm x))
  have iM : Integrable fun u => (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
      truncatedTilt (2 * c) N (u + x) * F (u + x)) :=
    integrable_mul_of_memLp (hFm.sub (memLp_two_shift hFm x)) (hGm.sub (memLp_two_shift hGm x))
  have iS : Integrable fun u => F (u + x) ^ 2 := hF.sq.comp_add_right x
  have hshift : (∫ u, F (u + x) ^ 2) = ∫ u, F u ^ 2 :=
    integral_add_right_eq_self (fun v => F v ^ 2) x
  have hm0 : 0 ≤ min (c * x) 1 ^ 2 := sq_nonneg _
  have hsqE : (∫ u, F u ^ 2) ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_mono hF.sq hF.exponential (fun u => sq_le_sq_mul_exp_of_support hF.support u)
  have iB : Integrable fun u => min (c * x) 1 ^ 2 *
      ((F u ^ 2 * Real.exp (-(8 * u)) + F (u + x) ^ 2) / 2) :=
    ((hF.exponential.add iS).div_const 2).const_mul _
  have hpt : ∀ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 -
      (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
        truncatedTilt (2 * c) N (u + x) * F (u + x)) ≤
        min (c * x) 1 ^ 2 * ((F u ^ 2 * Real.exp (-(8 * u)) + F (u + x) ^ 2) / 2) := by
    intro u
    have hj := truncatedTilt_jump hc0 N u hx.le
    have s1 := truncatedTilt_sq c N u
    have s2 := truncatedTilt_sq c N (u + x)
    have hg := sq_truncatedTilt_mul_le hF.support h2c (by linarith : 2 * c ≤ 3) N u
    rw [← s1] at hg
    have e : (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 -
        (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
          truncatedTilt (2 * c) N (u + x) * F (u + x)) =
          F u * F (u + x) * (truncatedTilt c N u - truncatedTilt c N (u + x)) ^ 2 := by
      rw [← s1, ← s2]
      ring
    rw [e]
    have h1 : F u * F (u + x) * (truncatedTilt c N u - truncatedTilt c N (u + x)) ^ 2 ≤
        |F u * F (u + x)| * (truncatedTilt c N u ^ 2 * min (c * x) 1 ^ 2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hj (abs_nonneg _))
    have h3 : |F u * F (u + x)| * truncatedTilt c N u ^ 2 ≤
        ((truncatedTilt c N u ^ 2 * F u) ^ 2 + F (u + x) ^ 2) / 2 := by
      have e3 : |F u * F (u + x)| * truncatedTilt c N u ^ 2 =
          |truncatedTilt c N u ^ 2 * F u| * |F (u + x)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (truncatedTilt c N u))]
        ring
      rw [e3]
      nlinarith [sq_nonneg (|truncatedTilt c N u ^ 2 * F u| - |F (u + x)|),
        sq_abs (truncatedTilt c N u ^ 2 * F u), sq_abs (F (u + x))]
    calc F u * F (u + x) * (truncatedTilt c N u - truncatedTilt c N (u + x)) ^ 2
        ≤ |F u * F (u + x)| * (truncatedTilt c N u ^ 2 * min (c * x) 1 ^ 2) := h1
      _ = min (c * x) 1 ^ 2 * (|F u * F (u + x)| * truncatedTilt c N u ^ 2) := by ring
      _ ≤ min (c * x) 1 ^ 2 * (((truncatedTilt c N u ^ 2 * F u) ^ 2 + F (u + x) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h3 hm0
      _ ≤ min (c * x) 1 ^ 2 * ((F u ^ 2 * Real.exp (-(8 * u)) + F (u + x) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hm0
  have hE : (∫ u, min (c * x) 1 ^ 2 * ((F u ^ 2 * Real.exp (-(8 * u)) + F (u + x) ^ 2) / 2)) =
      min (c * x) 1 ^ 2 * (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + ∫ u, F u ^ 2) / 2) := by
    rw [integral_const_mul, integral_div, integral_add hF.exponential iS, hshift]
  calc (∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
        (∫ u, (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
          truncatedTilt (2 * c) N (u + x) * F (u + x)))
      = ∫ u, ((truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 -
          (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
            truncatedTilt (2 * c) N (u + x) * F (u + x))) := (integral_sub iH iM).symm
    _ ≤ ∫ u, min (c * x) 1 ^ 2 * ((F u ^ 2 * Real.exp (-(8 * u)) + F (u + x) ^ 2) / 2) :=
        integral_mono (iH.sub iM) iB hpt
    _ = min (c * x) 1 ^ 2 * (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + ∫ u, F u ^ 2) / 2) := hE
    _ ≤ min (c * x) 1 ^ 2 * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
        mul_le_mul_of_nonneg_left (by linarith) hm0

/-- The jump energy of `φF` exceeds the mixed jump form of `F` and `φ²F` by a bounded
commutator. -/
theorem levyEnergy_truncatedTilt_sub_levyMixed_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (N : ℝ) :
    (∫ x in Ioi (0 : ℝ), archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
      levyMixed F (fun u => truncatedTilt (2 * c) N u * F u) ≤
        (3 * c ^ 2 + 2) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
          ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2)) := by
  have hH := criticalHalfLineEnergyDomain_truncatedTilt_mul hF hc0 N
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hF (by positivity : (0 : ℝ) ≤ 2 * c) N
  have hE0 : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have i1 := hH.integrableOn_levyIntegrand
  have i2 := integrableOn_levyMixedIntegrand hF hG
  have hB : IntegrableOn (fun x : ℝ => (3 * c ^ 2 + 2) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
      Real.exp (-(x / 2))) (Ioi 0) := integrableOn_exp_neg_half.const_mul _
  have key : ∀ x ∈ Ioi (0 : ℝ),
      archLevyDensity x * (∫ u, (truncatedTilt c N u * F u -
        truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
      archLevyDensity x * (∫ u, (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
        truncatedTilt (2 * c) N (u + x) * F (u + x))) ≤
        (3 * c ^ 2 + 2) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) * Real.exp (-(x / 2)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hA := integral_sq_jump_truncatedTilt_le hF hc0 hc1 N hx0
    have hmin := archLevyDensity_mul_min_sq_le hc0 zero_le_one hx0
    rw [one_pow, mul_one] at hmin
    have h1 := mul_le_mul_of_nonneg_left hA (archLevyDensity_pos hx0).le
    have h2 := mul_le_mul_of_nonneg_right hmin hE0
    nlinarith [h1, h2]
  calc (∫ x in Ioi (0 : ℝ), archLevyDensity x *
        ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
        levyMixed F (fun u => truncatedTilt (2 * c) N u * F u)
      = ∫ x in Ioi (0 : ℝ), (archLevyDensity x * (∫ u, (truncatedTilt c N u * F u -
          truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
          archLevyDensity x * (∫ u, (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
            truncatedTilt (2 * c) N (u + x) * F (u + x)))) := (integral_sub i1 i2).symm
    _ ≤ ∫ x in Ioi (0 : ℝ), (3 * c ^ 2 + 2) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
          Real.exp (-(x / 2)) := setIntegral_mono_on (i1.sub i2) hB measurableSet_Ioi key
    _ = (3 * c ^ 2 + 2) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
          ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2)) := integral_const_mul _ _

/-! ### The weak equation against the weighted state -/

/-- **The Gamma pairing of the state with its weighted copy is bounded uniformly in the
truncation.** The weak equation replaces it by prime and pole terms and a confinement term of
favourable sign. -/
theorem gammaMixedForm_truncatedTilt_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (N : ℝ) :
    gammaMixedForm F (fun u => truncatedTilt (2 * c) N u * F u) ≤
      2 * vonMangoldtThreeHalvesMass * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) +
        4 * (∫ u, |F u| * Real.exp (-(5 / 2) * u)) ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h2c0 : (0 : ℝ) ≤ 2 * c := by positivity
  have h2c2 : 2 * c ≤ 2 := by linarith
  have h2c3 : 2 * c ≤ 3 := by linarith
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hd h2c0 N
  have hw := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hG
  rw [criticalHalfLineMixedEnergy_eq_bare_add] at hw
  unfold bareMixedEnergy at hw
  -- the confinement term has a sign
  have hconf : 0 ≤ criticalAliasCoefficient W₀ *
      ∫ u in Iio (0 : ℝ), F u * (truncatedTilt (2 * c) N u * F u) * Real.exp (-(8 * u)) :=
    mul_nonneg (criticalAliasCoefficient_positive hW).le
      (setIntegral_nonneg measurableSet_Iio fun u _ =>
        mul_nonneg (by
          have e : F u * (truncatedTilt (2 * c) N u * F u) =
              truncatedTilt (2 * c) N u * F u ^ 2 := by ring
          rw [e]
          exact mul_nonneg (truncatedTilt_pos _ _ _).le (sq_nonneg _)) (Real.exp_pos _).le)
  -- prime terms
  have hE0 : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hs1 := Real.sqrt_le_sqrt (exponentialSourceMass_le_exponential hd)
  have hs2 := Real.sqrt_le_sqrt (exponentialSourceMass_truncatedTilt_mul_le hd h2c0 h2c3 N)
  have hss : Real.sqrt (exponentialSourceMass F) *
      Real.sqrt (exponentialSourceMass fun u => truncatedTilt (2 * c) N u * F u) ≤
        ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt hE0)
  have hv : (0 : ℝ) ≤ 2 * vonMangoldtThreeHalvesMass :=
    mul_nonneg two_pos.le vonMangoldtThreeHalvesMass_nonneg
  have hp1 := (abs_primeMixedForm_le hd.weighted hG.weighted).trans
    (mul_le_mul_of_nonneg_left hss hv)
  have hp2 := (abs_primeMixedForm_le hG.weighted hd.weighted).trans
    (mul_le_mul_of_nonneg_left ((mul_comm _ _).trans_le hss) hv)
  -- pole terms
  have hP0 : 0 ≤ ∫ u, |F u| * Real.exp (-(5 / 2) * u) :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hCC := mul_le_mul (abs_coshHalfMoment_le_of_domain hd)
    (abs_coshHalfMoment_truncatedTilt_mul_le hd h2c0 h2c2 N) (abs_nonneg _) hP0
  have hSS := mul_le_mul (abs_sinhHalfMoment_le_of_domain hd)
    (abs_sinhHalfMoment_truncatedTilt_mul_le hd h2c0 h2c2 N) (abs_nonneg _) hP0
  rw [← abs_mul] at hCC hSS
  have hCC' := (neg_le_abs _).trans hCC
  have hSS' := (le_abs_self _).trans hSS
  linarith [le_abs_self (primeMixedForm F fun u => truncatedTilt (2 * c) N u * F u),
    le_abs_self (primeMixedForm (fun u => truncatedTilt (2 * c) N u * F u) F)]

/-- **The Agmon bound.** The jump energies of the truncated tilts of the state are bounded
uniformly in the truncation. -/
theorem exists_levyEnergy_truncatedTilt_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ K : ℝ, ∀ N : ℝ, (∫ x in Ioi (0 : ℝ), archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) ≤ K := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine ⟨(2 * vonMangoldtThreeHalvesMass + 2 * |gammaHardyPhaseRate 0| +
    (3 * c ^ 2 + 2) * ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2))) *
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) +
        4 * (∫ u, |F u| * Real.exp (-(5 / 2) * u)) ^ 2, fun N => ?_⟩
  have h2c : (0 : ℝ) ≤ 2 * c := by positivity
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hd h2c N
  have hB := levyEnergy_truncatedTilt_sub_levyMixed_le hd hc0 hc1 N
  have hC := gammaMixedForm_truncatedTilt_le hW hthreshold hF hc0 hc1 N
  have hL := gammaMixedForm_eq_levy hd hG
  have hI := integral_mul_truncatedTilt_mul_nonneg_le hd h2c (by linarith : 2 * c ≤ 3) N
  have h1 : -(gammaHardyPhaseRate 0) * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      |gammaHardyPhaseRate 0| * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) :=
    mul_le_mul_of_nonneg_right (neg_le_abs _) hI.1
  have h2 : |gammaHardyPhaseRate 0| * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      |gammaHardyPhaseRate 0| * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    mul_le_mul_of_nonneg_left hI.2 (abs_nonneg _)
  linarith

/-! ### The limit -/

/-- **The tilted state lies in the energy domain.** For `0 ≤ c ≤ 1` the profile `e^{-cu} F` of the
critical state `F` has finite Gamma energy, together with the other data of the domain. -/
theorem criticalHalfLineEnergyDomain_exp_mul_groundState {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨K, hK⟩ := exists_levyEnergy_truncatedTilt_le hW hthreshold hF hc0 hc1
  have hmeas : Measurable fun u => Real.exp (-(c * u)) * F u :=
    (by fun_prop : Measurable fun u : ℝ => Real.exp (-(c * u))).mul hd.meas
  have hint : Integrable fun u => Real.exp (-(c * u)) * F u := by
    refine (integrable_abs_mul_exp_of_domain hd (c := -c) (by linarith)).mono'
      hmeas.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
    exact (mul_comm _ _).le
  have hsqle : ∀ u, (Real.exp (-(c * u)) * F u) ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u)) := fun u => by
    rw [exp_neg_mul_eq_truncatedTilt]
    exact sq_truncatedTilt_mul_le hd.support hc0 (by linarith) (-u) u
  have hsq : Integrable fun u => (Real.exp (-(c * u)) * F u) ^ 2 := by
    refine hd.exponential.mono' (hmeas.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsqle u
  have hexp : Integrable fun u => (Real.exp (-(c * u)) * F u) ^ 2 * Real.exp (-(8 * u)) := by
    refine ((criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).2 (8 + 2 * c)
      (by linarith)).congr (Eventually.of_forall fun u => ?_)
    show F u ^ 2 * Real.exp (-((8 + 2 * c) * u)) =
      (Real.exp (-(c * u)) * F u) ^ 2 * Real.exp (-(8 * u))
    have e : Real.exp (-((8 + 2 * c) * u)) = Real.exp (-(c * u)) ^ 2 * Real.exp (-(8 * u)) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  refine ⟨hmeas, hint, hsq, hexp, fun u hu => by rw [hd.support u hu, mul_zero], ?_⟩
  refine integrable_gamma_of_lintegral_levy_ne_top hint hsq ?_
  -- the truncated tilts converge to the tilt, dominated by it
  have hHN : ∀ N : ℕ, CriticalHalfLineEnergyDomain (fun u => truncatedTilt c N u * F u) :=
    fun N => criticalHalfLineEnergyDomain_truncatedTilt_mul hd hc0 N
  have hpt : ∀ u : ℝ, Tendsto (fun N : ℕ => truncatedTilt c N u * F u) atTop
      (𝓝 (Real.exp (-(c * u)) * F u)) := by
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈-u⌉₊] with N hN
    rw [truncatedTilt_eq_exp_neg (by linarith [Nat.ceil_le.mp hN])]
  have hbd : ∀ (N : ℕ) (u : ℝ), (truncatedTilt c N u * F u) ^ 2 ≤
      (Real.exp (-(c * u)) * F u) ^ 2 := fun N u => by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (truncatedTilt_pos c N u).le
      (truncatedTilt_le_exp_neg hc0 N u) 2) (sq_nonneg _)
  have hlim : ∀ x : ℝ, Tendsto (fun N : ℕ => ∫ u,
      (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) atTop
      (𝓝 (∫ u, (Real.exp (-(c * u)) * F u - Real.exp (-(c * (u + x))) * F (u + x)) ^ 2)) := by
    intro x
    refine tendsto_integral_of_dominated_convergence
      (fun u => 2 * (Real.exp (-(c * u)) * F u) ^ 2 +
        2 * (Real.exp (-(c * (u + x))) * F (u + x)) ^ 2) (fun N => ?_) ?_ (fun N => ?_) ?_
    · exact (((hHN N).meas.sub ((hHN N).meas.comp (measurable_id.add_const x))).pow_const
        2).aestronglyMeasurable
    · exact (hsq.const_mul 2).add ((hsq.comp_add_right x).const_mul 2)
    · refine Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hbd N u, hbd N (u + x), sq_nonneg (truncatedTilt c N u * F u +
        truncatedTilt c N (u + x) * F (u + x))]
    · exact Eventually.of_forall fun u => ((hpt u).sub (hpt (u + x))).pow 2
  -- Fatou in the lag
  have hfat : (∫⁻ x in Ioi (0 : ℝ), liminf (fun N : ℕ => ENNReal.ofReal (archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) atTop) ≤
      liminf (fun N : ℕ => ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
        ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) atTop :=
    lintegral_liminf_le' (fun N => ENNReal.measurable_ofReal.comp_aemeasurable
      (hHN N).aestronglyMeasurable_levyIntegrand.aemeasurable)
  have hliminf : ∀ x : ℝ, liminf (fun N : ℕ => ENNReal.ofReal (archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) atTop =
        ENNReal.ofReal (archLevyDensity x *
          ∫ u, (Real.exp (-(c * u)) * F u - Real.exp (-(c * (u + x))) * F (u + x)) ^ 2) :=
    fun x => ((ENNReal.continuous_ofReal.tendsto _).comp
      ((hlim x).const_mul (archLevyDensity x))).liminf_eq
  have hEq : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
      ∫ u, (Real.exp (-(c * u)) * F u - Real.exp (-(c * (u + x))) * F (u + x)) ^ 2)) =
      ∫⁻ x in Ioi (0 : ℝ), liminf (fun N : ℕ => ENNReal.ofReal (archLevyDensity x *
        ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) atTop :=
    lintegral_congr fun x => (hliminf x).symm
  have hN : ∀ N : ℕ, (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2)) ≤
        ENNReal.ofReal K := fun N => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hHN N).integrableOn_levyIntegrand
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
        mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun u => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hK N)
  exact ((hEq.le.trans (hfat.trans (liminf_le_of_frequently_le'
    (Frequently.of_forall hN)))).trans_lt ENNReal.ofReal_lt_top).ne

end GaloisForLFunctions.ExclusionOfTheCriticalState
