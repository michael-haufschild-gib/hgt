import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingContinuationCriterion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The damping average of the relative loss suffices

A continuation budget is a *pointwise* demand: at every parameter of the interval the loss must be
dominated by one horizon-free function.  Transport does not need that much.  Reading the energy
through the logarithmic scale, the quantity whose growth has to be stopped is the **relative loss**

`r_T(ε) = −E'_T(ε) / (1 + E_T(ε)) = −∂_ε log(1 + E_T(ε))`,

and the fundamental theorem of calculus turns the parameter *average* of the relative loss into
the exact logarithm of the ratio of shifted energies.  Hence:

* a horizon-free bound on `∫_a^c r_T` transports admission from `c` to `a`
  (`Admits.of_averagedContinuation`);
* that averaged bound is not merely sufficient, it is equivalent to the horizon-uniform ratio
  bound transport asserts (`averagedContinuation_iff_ratio_bound`), so no weaker budget could
  work: the averaged form is the bottom of the hierarchy;
* every pointwise budget is an averaged budget with total `β c − β a`, and no integrability of the
  budget derivative is needed (`AveragedContinuation.of_linearContinuation`);
* the converse fails, and badly: a family whose relative loss is a spike of height `T + 1` and
  width `(T+1)^{-2}` has averaged budget `π` on every interval and admits no pointwise budget at
  all (`exists_averagedContinuation_not_linearContinuation`).

For the arithmetic family the relative loss is *unconditionally* integrable on every compact
damping interval away from zero, because the centred prefix and its damping tangent are continuous
there.  So the averaged demand is a bound and not a regularity assumption, and the arithmetic
obligation becomes a mean value in the damping: cancellation between dampings is allowed and the
signed work may be arbitrarily negative at individual dampings.

The same weakening applies to the tangent-norm receiver: only
`∫_a^{1/2} ‖E_ε‖_T dε ≤ C`, with `C` free of the horizon, is needed
(`riemannHypothesis_of_averaged_tangentNorm`), where the owned criterion asks for a pointwise
majorant `‖E_ε‖_T ≤ g(ε)` with `g` integrable.
-/

open Set Filter Finset MeasureTheory RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

variable {E : ℝ → ℕ → ℝ} {E' : ℕ → ℝ → ℝ} {a c : ℝ}

/-! ## §1. The relative loss and its parameter average -/

/-- **The relative loss**: the energy's loss read through the logarithmic scale,
`−∂_ε log(1 + E_T(ε))`. -/
def relativeLoss (E : ℝ → ℕ → ℝ) (E' : ℕ → ℝ → ℝ) (T : ℕ) (ε : ℝ) : ℝ :=
  -(E' T ε) / (1 + E ε T)

/-- **An averaged continuation budget on `[a, c]`**: one constant, the same for every horizon,
bounding the parameter average of the relative loss.  Cancellation between parameters is allowed,
and the loss may be unbounded over the horizon at individual parameters. -/
def AveragedContinuation (E : ℝ → ℕ → ℝ) (E' : ℕ → ℝ → ℝ) (a c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ T : ℕ,
    IntervalIntegrable (relativeLoss E E' T) volume a c ∧
      ∫ ε in a..c, relativeLoss E E' T ε ≤ C

/-- The logarithmic scale of the energy has derivative minus the relative loss. -/
theorem hasDerivAt_log_one_add_energy {ε : ℝ} {T : ℕ} (hE0 : 0 ≤ E ε T)
    (hEd : HasDerivAt (fun x => E x T) (E' T ε) ε) :
    HasDerivAt (fun x => Real.log (1 + E x T)) (-relativeLoss E E' T ε) ε := by
  refine ((hasDerivAt_log_one_add hE0).comp ε hEd).congr_deriv ?_
  rw [relativeLoss, neg_div, neg_neg, div_eq_inv_mul]

/-- **The average is exactly the logarithm of the ratio of shifted energies.**  This identity is
the whole mechanism: the averaged budget is the integrated form of transport, not an estimate on
top of it. -/
theorem integral_relativeLoss_eq (hac : a ≤ c) {T : ℕ}
    (hE0 : ∀ ε ∈ Icc a c, 0 ≤ E ε T)
    (hEd : ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hint : IntervalIntegrable (relativeLoss E E' T) volume a c) :
    ∫ ε in a..c, relativeLoss E E' T ε = Real.log (1 + E a T) - Real.log (1 + E c T) := by
  have hderiv : ∀ ε ∈ uIcc a c,
      HasDerivAt (fun x => Real.log (1 + E x T)) (-relativeLoss E E' T ε) ε := by
    rw [uIcc_of_le hac]
    exact fun ε hε => hasDerivAt_log_one_add_energy (hE0 ε hε) (hEd ε hε)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- **Transport under an averaged budget.**  The bound at `a` is the bound at `c` amplified by
`exp C`; no horizon appears. -/
theorem Admits.of_averagedContinuation (hac : a ≤ c)
    (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hcont : AveragedContinuation E E' a c) (hc : Admits E c) : Admits E a := by
  obtain ⟨C, hC⟩ := hcont
  obtain ⟨B, hB⟩ := hc
  refine ⟨(1 + max B 0) * Real.exp C - 1, fun T => ?_⟩
  obtain ⟨hint, hle⟩ := hC T
  have hid := integral_relativeLoss_eq hac (fun ε hε => hE0 ε hε T) (hEd T) hint
  have hca : (0 : ℝ) < 1 + E a T := by linarith [hE0 a (left_mem_Icc.mpr hac) T]
  have hcc : (0 : ℝ) < 1 + E c T := by linarith [hE0 c (right_mem_Icc.mpr hac) T]
  have hlog : Real.log (1 + E a T) ≤ Real.log (1 + E c T) + C := by linarith
  have hstep : 1 + E a T ≤ (1 + E c T) * Real.exp C := by
    calc 1 + E a T = Real.exp (Real.log (1 + E a T)) := (Real.exp_log hca).symm
      _ ≤ Real.exp (Real.log (1 + E c T) + C) := Real.exp_le_exp.mpr hlog
      _ = (1 + E c T) * Real.exp C := by rw [Real.exp_add, Real.exp_log hcc]
  have h2 : (1 + E c T) * Real.exp C ≤ (1 + max B 0) * Real.exp C :=
    mul_le_mul_of_nonneg_right (by linarith [(hB T).trans (le_max_left B 0)])
      (Real.exp_pos _).le
  linarith

/-- **The averaged budget is the exact content of transport.**  Given the integrability that the
arithmetic family has unconditionally, an averaged budget on `[a, c]` is equivalent to a
horizon-uniform bound on the ratio of the shifted energies at the two ends.  Hence no continuation
hypothesis weaker than the averaged one can exist. -/
theorem averagedContinuation_iff_ratio_bound (hac : a ≤ c)
    (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hint : ∀ T : ℕ, IntervalIntegrable (relativeLoss E E' T) volume a c) :
    AveragedContinuation E E' a c ↔ ∃ M : ℝ, ∀ T : ℕ, 1 + E a T ≤ M * (1 + E c T) := by
  have hpos : ∀ T : ℕ, (0 : ℝ) < 1 + E a T := fun T => by
    linarith [hE0 a (left_mem_Icc.mpr hac) T]
  have hposc : ∀ T : ℕ, (0 : ℝ) < 1 + E c T := fun T => by
    linarith [hE0 c (right_mem_Icc.mpr hac) T]
  have hid : ∀ T : ℕ, ∫ ε in a..c, relativeLoss E E' T ε =
      Real.log (1 + E a T) - Real.log (1 + E c T) := fun T =>
    integral_relativeLoss_eq hac (fun ε hε => hE0 ε hε T) (hEd T) (hint T)
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨Real.exp C, fun T => ?_⟩
    have hlog : Real.log (1 + E a T) ≤ Real.log (1 + E c T) + C := by
      have := (hC T).2; rw [hid T] at this; linarith
    calc 1 + E a T = Real.exp (Real.log (1 + E a T)) := (Real.exp_log (hpos T)).symm
      _ ≤ Real.exp (Real.log (1 + E c T) + C) := Real.exp_le_exp.mpr hlog
      _ = Real.exp C * (1 + E c T) := by
          rw [Real.exp_add, Real.exp_log (hposc T)]; ring
  · rintro ⟨M, hM⟩
    have hM0 : 0 < M := by
      by_contra h
      have hle := hM 0
      nlinarith [hpos 0, hposc 0]
    refine ⟨Real.log M, fun T => ⟨hint T, ?_⟩⟩
    rw [hid T]
    have hlog : Real.log (1 + E a T) ≤ Real.log M + Real.log (1 + E c T) := by
      calc Real.log (1 + E a T) ≤ Real.log (M * (1 + E c T)) :=
            Real.log_le_log (hpos T) (hM T)
        _ = Real.log M + Real.log (1 + E c T) := Real.log_mul hM0.ne' (hposc T).ne'
    linarith

/-! ## §2. Every pointwise budget is an averaged budget -/

/-- **A pointwise budget is an averaged budget**, with total `β c − β a`.  Only the relative loss
has to be integrable: the budget derivative `β'` is not assumed integrable, because the
one-sided fundamental theorem of calculus compares an integrable minorant with any derivative. -/
theorem AveragedContinuation.of_linearContinuation (hac : a ≤ c)
    (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hint : ∀ T : ℕ, IntervalIntegrable (relativeLoss E E' T) volume a c)
    (h : LinearContinuation E E' a c) : AveragedContinuation E E' a c := by
  obtain ⟨β, β', hβ, hwork⟩ := h
  refine ⟨β c - β a, fun T => ⟨hint T, ?_⟩⟩
  refine intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hac
    (fun ε hε => ((hβ ε hε).continuousAt).continuousWithinAt)
    (fun ε hε => (hβ ε (Ioo_subset_Icc_self hε)).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hac).mp (hint T)) ?_
  intro ε hε
  have hmem := Ioo_subset_Icc_self hε
  have hposε : (0 : ℝ) < 1 + E ε T := by linarith [hE0 ε hmem T]
  rw [relativeLoss, div_le_iff₀ hposε]
  exact hwork T ε hmem

/-! ## §3. The averaged demand is strictly weaker: a thinning spike -/

/-- The scale of the spike family: `k⁻¹(arctan(k²(ε₀ − ε)) + π/2)` with `k = T + 1`. -/
def lossSpikeScale (ε₀ : ℝ) (T : ℕ) (ε : ℝ) : ℝ :=
  ((T : ℝ) + 1)⁻¹ * (Real.arctan (((T : ℝ) + 1) ^ 2 * (ε₀ - ε)) + Real.pi / 2)

/-- The spike family: its relative loss is a peak of height `T + 1` and width `(T+1)^{-2}` at
`ε₀`, so the peak thins out exactly as fast as it grows. -/
def lossSpikeEnergy (ε₀ : ℝ) (ε : ℝ) (T : ℕ) : ℝ := Real.exp (lossSpikeScale ε₀ T ε) - 1

/-- The parameter derivative of the spike family. -/
def lossSpikeEnergyDeriv (ε₀ : ℝ) (T : ℕ) (ε : ℝ) : ℝ :=
  -Real.exp (lossSpikeScale ε₀ T ε) *
    (((T : ℝ) + 1) / (1 + (((T : ℝ) + 1) ^ 2 * (ε₀ - ε)) ^ 2))

theorem lossSpikeScale_nonneg (ε₀ : ℝ) (T : ℕ) (ε : ℝ) : 0 ≤ lossSpikeScale ε₀ T ε := by
  have h1 : 0 < ((T : ℝ) + 1)⁻¹ := by positivity
  have h2 : 0 < Real.arctan (((T : ℝ) + 1) ^ 2 * (ε₀ - ε)) + Real.pi / 2 := by
    linarith [Real.neg_pi_div_two_lt_arctan (((T : ℝ) + 1) ^ 2 * (ε₀ - ε))]
  exact le_of_lt (mul_pos h1 h2)

/-- The scale never exceeds `π`: the spike's total weight is uniformly bounded. -/
theorem lossSpikeScale_le_pi (ε₀ : ℝ) (T : ℕ) (ε : ℝ) : lossSpikeScale ε₀ T ε ≤ Real.pi := by
  have hk : (1 : ℝ) ≤ (T : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) T]
  have hkinv : ((T : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; exact Or.inr hk
  have h2 : Real.arctan (((T : ℝ) + 1) ^ 2 * (ε₀ - ε)) + Real.pi / 2 ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two (((T : ℝ) + 1) ^ 2 * (ε₀ - ε))]
  have h3 : 0 ≤ Real.arctan (((T : ℝ) + 1) ^ 2 * (ε₀ - ε)) + Real.pi / 2 := by
    linarith [Real.neg_pi_div_two_lt_arctan (((T : ℝ) + 1) ^ 2 * (ε₀ - ε))]
  calc lossSpikeScale ε₀ T ε ≤ 1 * (Real.arctan (((T : ℝ) + 1) ^ 2 * (ε₀ - ε)) + Real.pi / 2) :=
        mul_le_mul_of_nonneg_right hkinv h3
    _ ≤ Real.pi := by linarith

theorem lossSpikeEnergy_nonneg (ε₀ ε : ℝ) (T : ℕ) : 0 ≤ lossSpikeEnergy ε₀ ε T := by
  have := Real.one_le_exp (lossSpikeScale_nonneg ε₀ T ε)
  simp only [lossSpikeEnergy]
  linarith

theorem hasDerivAt_lossSpikeEnergy (ε₀ : ℝ) (T : ℕ) (ε : ℝ) :
    HasDerivAt (fun x => lossSpikeEnergy ε₀ x T) (lossSpikeEnergyDeriv ε₀ T ε) ε := by
  set k : ℝ := (T : ℝ) + 1 with hk
  have hu : HasDerivAt (fun x : ℝ => k ^ 2 * (ε₀ - x)) (-(k ^ 2)) ε := by
    simpa using ((hasDerivAt_const ε ε₀).sub (hasDerivAt_id ε)).const_mul (k ^ 2)
  have harc : HasDerivAt (fun x : ℝ => Real.arctan (k ^ 2 * (ε₀ - x)))
      (1 / (1 + (k ^ 2 * (ε₀ - ε)) ^ 2) * -(k ^ 2)) ε :=
    (Real.hasDerivAt_arctan _).comp ε hu
  have hS : HasDerivAt (fun x => lossSpikeScale ε₀ T x)
      (k⁻¹ * (1 / (1 + (k ^ 2 * (ε₀ - ε)) ^ 2) * -(k ^ 2))) ε :=
    (harc.add_const (Real.pi / 2)).const_mul _
  have hkne : k ≠ 0 := by positivity
  refine ((hS.exp).sub_const 1).congr_deriv ?_
  rw [lossSpikeEnergyDeriv]
  field_simp
  ring

/-- The relative loss of the spike family is the explicit peak `k/(1 + k⁴(ε₀ − ε)²)`. -/
theorem relativeLoss_lossSpike (ε₀ : ℝ) (T : ℕ) (ε : ℝ) :
    relativeLoss (lossSpikeEnergy ε₀) (lossSpikeEnergyDeriv ε₀) T ε =
      ((T : ℝ) + 1) / (1 + (((T : ℝ) + 1) ^ 2 * (ε₀ - ε)) ^ 2) := by
  have hexp : Real.exp (lossSpikeScale ε₀ T ε) ≠ 0 := (Real.exp_pos _).ne'
  rw [relativeLoss, lossSpikeEnergyDeriv, lossSpikeEnergy]
  have h1 : (1 : ℝ) + (Real.exp (lossSpikeScale ε₀ T ε) - 1) =
      Real.exp (lossSpikeScale ε₀ T ε) := by ring
  rw [h1]
  field_simp

theorem continuous_relativeLoss_lossSpike (ε₀ : ℝ) (T : ℕ) :
    Continuous (relativeLoss (lossSpikeEnergy ε₀) (lossSpikeEnergyDeriv ε₀) T) := by
  have hfun : relativeLoss (lossSpikeEnergy ε₀) (lossSpikeEnergyDeriv ε₀) T =
      fun ε => ((T : ℝ) + 1) / (1 + (((T : ℝ) + 1) ^ 2 * (ε₀ - ε)) ^ 2) :=
    funext fun ε => relativeLoss_lossSpike ε₀ T ε
  rw [hfun]
  exact continuous_const.div (by continuity) fun ε => by positivity

/-- The scale is the logarithm of the shifted spike energy. -/
theorem log_one_add_lossSpikeEnergy (ε₀ ε : ℝ) (T : ℕ) :
    Real.log (1 + lossSpikeEnergy ε₀ ε T) = lossSpikeScale ε₀ T ε := by
  have h1 : (1 : ℝ) + lossSpikeEnergy ε₀ ε T = Real.exp (lossSpikeScale ε₀ T ε) := by
    rw [lossSpikeEnergy]; ring
  rw [h1, Real.log_exp]

/-- **The spike family has the averaged budget `π` on every interval.**  Its peak thins at exactly
the rate at which it grows, so the parameter average of the relative loss never exceeds the total
weight of one arctangent. -/
theorem averagedContinuation_lossSpikeEnergy (ε₀ : ℝ) (hac : a ≤ c) :
    AveragedContinuation (lossSpikeEnergy ε₀) (lossSpikeEnergyDeriv ε₀) a c := by
  refine ⟨Real.pi, fun T => ⟨(continuous_relativeLoss_lossSpike ε₀ T).intervalIntegrable a c, ?_⟩⟩
  rw [integral_relativeLoss_eq (E := lossSpikeEnergy ε₀) (E' := lossSpikeEnergyDeriv ε₀) (T := T)
      hac (fun ε _ => lossSpikeEnergy_nonneg ε₀ ε T)
      (fun ε _ => hasDerivAt_lossSpikeEnergy ε₀ T ε)
      ((continuous_relativeLoss_lossSpike ε₀ T).intervalIntegrable a c),
    log_one_add_lossSpikeEnergy, log_one_add_lossSpikeEnergy]
  linarith [lossSpikeScale_le_pi ε₀ T a, lossSpikeScale_nonneg ε₀ T c]

/-- **The spike family has no pointwise budget on an interval containing its peak.**  At the peak
the relative loss is `T + 1`, so no horizon-free budget derivative can dominate it. -/
theorem not_linearContinuation_lossSpikeEnergy {ε₀ : ℝ} (hmem : ε₀ ∈ Icc a c) :
    ¬ LinearContinuation (lossSpikeEnergy ε₀) (lossSpikeEnergyDeriv ε₀) a c := by
  rintro ⟨β, β', hβ, hwork⟩
  obtain ⟨T, hT⟩ := exists_nat_gt (β' ε₀)
  have h := hwork T ε₀ hmem
  have hpeak : relativeLoss (lossSpikeEnergy ε₀) (lossSpikeEnergyDeriv ε₀) T ε₀ =
      (T : ℝ) + 1 := by
    rw [relativeLoss_lossSpike]
    simp
  have hposε : (0 : ℝ) < 1 + lossSpikeEnergy ε₀ ε₀ T := by
    linarith [lossSpikeEnergy_nonneg ε₀ ε₀ T]
  rw [relativeLoss, div_eq_iff hposε.ne'] at hpeak
  nlinarith [hpeak, h]

/-- **The averaged demand is strictly weaker than the pointwise one.**  On every nondegenerate
interval there is a differentiable nonnegative energy family with averaged budget `π` and with no
pointwise linear continuation budget whatever: at the midpoint its relative loss exceeds every
constant as the horizon grows, while the parameter average stays bounded because the peak thins at
the same rate.  So a pointwise-in-parameter inequality is a genuinely stronger demand than the
mean value in the parameter. -/
theorem exists_averagedContinuation_not_linearContinuation (hac : a < c) :
    ∃ (F : ℝ → ℕ → ℝ) (F' : ℕ → ℝ → ℝ),
      (∀ ε T, 0 ≤ F ε T) ∧ (∀ T ε, HasDerivAt (fun x => F x T) (F' T ε) ε) ∧
        AveragedContinuation F F' a c ∧ ¬ LinearContinuation F F' a c :=
  ⟨lossSpikeEnergy ((a + c) / 2), lossSpikeEnergyDeriv ((a + c) / 2),
    fun ε T => lossSpikeEnergy_nonneg _ ε T, fun T ε => hasDerivAt_lossSpikeEnergy _ T ε,
    averagedContinuation_lossSpikeEnergy _ hac.le,
    not_linearContinuation_lossSpikeEnergy ⟨by linarith, by linarith⟩⟩

/-! ## §4. The arithmetic instance: integrability is unconditional -/

theorem continuousOn_dampedMobiusEnergy (T : ℕ) :
    ContinuousOn (fun ε => dampedMobiusEnergy ε T) (Ioi 0) := fun _ hε =>
  ((hasDerivAt_dampedMobiusEnergy (mem_Ioi.mp hε) T).continuousAt).continuousWithinAt

/-- The signed damping work is continuous at every positive damping: the centred prefix is
differentiable there and the damped Chebyshev tangent is continuous there. -/
theorem continuousOn_signedDampingWork (T : ℕ) :
    ContinuousOn (fun ε => signedDampingWork ε T) (Ioi 0) := by
  unfold signedDampingWork
  refine continuousOn_finsetSum _ fun n _ ε hε => ?_
  have hε0 : (0 : ℝ) < ε := mem_Ioi.mp hε
  have h1 : ContinuousAt (fun x => pmPowerDampedCenteredDivisorPrefix x n) ε :=
    (hasDerivAt_pmPowerDampedCenteredDivisorPrefix hε0 n).continuousAt
  have h2 : ContinuousAt (fun x => dampedChebyshevError x n) ε :=
    (continuousOn_dampedChebyshevError n).continuousAt (isOpen_Ioi.mem_nhds hε)
  exact ((h1.mul h2).div_const _).continuousWithinAt

/-- **The arithmetic relative loss is unconditionally integrable** on every compact damping
interval away from zero.  So the averaged continuation demand is purely a bound; no regularity in
the damping is being assumed. -/
theorem intervalIntegrable_relativeLoss_dampedMobiusEnergy {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) :
    IntervalIntegrable (relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv T) volume a c := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hac]
  intro ε hε
  have hε0 : (0 : ℝ) < ε := lt_of_lt_of_le ha hε.1
  have hmem : ε ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hε0
  have hW : ContinuousAt (fun x => signedDampingWork x T) ε :=
    (continuousOn_signedDampingWork T).continuousAt (isOpen_Ioi.mem_nhds hmem)
  have hnum : ContinuousAt (fun x => -(dampedMobiusEnergyDeriv T x)) ε :=
    hW.const_mul 2 |>.neg
  have hden : ContinuousAt (fun x => 1 + dampedMobiusEnergy x T) ε :=
    continuousAt_const.add ((continuousOn_dampedMobiusEnergy T).continuousAt
      (isOpen_Ioi.mem_nhds hmem))
  have hne : (1 : ℝ) + dampedMobiusEnergy ε T ≠ 0 := by
    have := dampedMobiusEnergy_nonneg ε T; positivity
  exact ((hnum.div hden hne)).continuousWithinAt

/-- **An averaged continuation budget for the damped Möbius energy on `[a, c]`.** -/
def AveragedDampingContinuation (a c : ℝ) : Prop :=
  AveragedContinuation dampedMobiusEnergy dampedMobiusEnergyDeriv a c

theorem admits_of_averagedDampingContinuation {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hadm : Admits dampedMobiusEnergy c) (h : AveragedDampingContinuation a c) :
    Admits dampedMobiusEnergy a :=
  Admits.of_averagedContinuation hac (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
    (fun T _ hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le ha hε.1) T) h hadm

/-- **The pointwise damping budget is an averaged budget.**  Nothing is lost by passing to the
average, and §3 shows something is gained. -/
theorem AveragedDampingContinuation.of_dampingContinuation {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (h : DampingContinuation a c) : AveragedDampingContinuation a c :=
  AveragedContinuation.of_linearContinuation hac (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
    (fun T => intervalIntegrable_relativeLoss_dampedMobiusEnergy ha hac T) h

/-- **The averaged damping continuation criterion for the Riemann hypothesis.**  A horizon-free
bound on the damping average of the relative loss, on every compact interval inside `(0, c]` for
one admitted `c`, gives RH. -/
theorem riemannHypothesis_of_averagedDampingContinuation_endpoint {c : ℝ} (hc : 0 < c)
    (hadm : Admits dampedMobiusEnergy c)
    (h : ∀ a : ℝ, 0 < a → a ≤ c → AveragedDampingContinuation a c) : RiemannHypothesis := by
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  have hmin : 0 < min c δ := lt_min hc hδ
  have hxc : min c δ / 2 ≤ c := by linarith [min_le_left c δ]
  have hx0 : 0 < min c δ / 2 := by positivity
  exact ⟨min c δ / 2, hx0, by linarith [min_le_right c δ],
    admits_of_averagedDampingContinuation hx0 hxc hadm (h _ hx0 hxc)⟩

/-- Averaged continuation from half damping, the unconditional endpoint. -/
theorem riemannHypothesis_of_averagedDampingContinuation
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → AveragedDampingContinuation a (1 / 2)) :
    RiemannHypothesis :=
  riemannHypothesis_of_averagedDampingContinuation_endpoint (by norm_num)
    (admits_dampedMobiusEnergy_of_half_le le_rfl) h

/-- **Partial averaged continuation is a zero-free strip.**  Averaged budgets on `[a, c]` for
every `a` above `a₀` bound the zero abscissa by `½ + a₀`. -/
theorem zetaZeroAbscissa_le_half_add_of_partial_averagedDampingContinuation {a₀ c : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₀c : a₀ < c) (hadm : Admits dampedMobiusEnergy c)
    (h : ∀ a : ℝ, a₀ < a → a ≤ c → AveragedDampingContinuation a c) :
    zetaZeroAbscissa ≤ 1 / 2 + a₀ := by
  refine zetaZeroAbscissa_le_of_accPt_receiverDampings (accPt_of_Ioo_subset ha₀c ?_)
  intro x hx
  have hx0 : 0 < x := lt_of_le_of_lt ha₀ hx.1
  exact (mem_receiverDampings_iff_admits hx0).mpr
    (admits_of_averagedDampingContinuation hx0 hx.2.le hadm (h x hx.1 hx.2.le))

/-! ## §5. The averaged tangent-norm receiver -/

theorem continuousOn_pronicNorm_dampedChebyshevError (T : ℕ) :
    ContinuousOn (fun ε => pronicNorm T (dampedChebyshevError ε)) (Ioi 0) := by
  unfold pronicNorm
  refine Real.continuous_sqrt.comp_continuousOn (continuousOn_finsetSum _ fun n _ _ hε => ?_)
  exact ((((continuousOn_dampedChebyshevError n).continuousAt
    (isOpen_Ioi.mem_nhds hε)).pow 2).div_const _).continuousWithinAt

/-- **An averaged tangent-norm bound pays the averaged budget.**  Where the owned receiver asks
for a pointwise majorant of the pronic tangent norm, uniform in the horizon, only the damping
average of that norm has to be bounded: the norm may spike with the horizon provided the spikes
thin out. -/
theorem averagedDampingContinuation_of_integral_tangentNorm_le {a c C : ℝ} (ha : 0 < a)
    (hac : a ≤ c)
    (hC : ∀ T : ℕ, (∫ ε in a..c, pronicNorm T (dampedChebyshevError ε)) ≤ C) :
    AveragedDampingContinuation a c := by
  refine ⟨C, fun T => ⟨intervalIntegrable_relativeLoss_dampedMobiusEnergy ha hac T, ?_⟩⟩
  have hnorm : IntervalIntegrable (fun ε => pronicNorm T (dampedChebyshevError ε)) volume a c := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hac]
    exact (continuousOn_pronicNorm_dampedChebyshevError T).mono fun ε hε =>
      mem_Ioi.mpr (lt_of_lt_of_le ha hε.1)
  refine le_trans (intervalIntegral.integral_mono_on hac
    (intervalIntegrable_relativeLoss_dampedMobiusEnergy ha hac T) hnorm ?_) (hC T)
  intro ε _
  have hwork := neg_two_mul_signedDampingWork_le_of_tangentNorm_le (ε := ε)
    (g := pronicNorm T (dampedChebyshevError ε)) T le_rfl
  have hposε : (0 : ℝ) < 1 + dampedMobiusEnergy ε T := by
    linarith [dampedMobiusEnergy_nonneg ε T]
  rw [relativeLoss, div_le_iff₀ hposε, dampedMobiusEnergyDeriv]
  exact hwork

/-- **The averaged tangent-norm criterion for the Riemann hypothesis.**  One horizon-free constant
per compact damping interval, bounding the damping average of the pronic norm of the centred damped
Chebyshev function, gives RH. -/
theorem riemannHypothesis_of_averaged_tangentNorm
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∃ C : ℝ, ∀ T : ℕ,
      (∫ ε in a..(1 / 2 : ℝ), pronicNorm T (dampedChebyshevError ε)) ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_averagedDampingContinuation fun x hx hx2 => by
    obtain ⟨C, hC⟩ := h x hx hx2
    exact averagedDampingContinuation_of_integral_tangentNorm_le hx hx2 hC

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
