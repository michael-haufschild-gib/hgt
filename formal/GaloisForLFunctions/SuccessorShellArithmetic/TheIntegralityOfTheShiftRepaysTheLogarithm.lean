import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellsRepayEveryConductor

/-!
# The integrality of the shift repays the logarithm

The conductor-one energy of the complete Weil form at overlap `c` subtracts the successor shells
`1 ≤ h < c` with weights `F_c(h) = ∫_{h/c}^1 G(u)/u du` (`shellSum`). The shift `h` is an integer:
the ratio pair `h = 0` is separated from the first shell by a unit gap. Replacing the lattice sum by
its integral over `h ∈ (0, c)` gives the **continuum shell completion**, the form a model without
integer successors would carry.

* **Continuum shells are the pole charge** (`continuumShellSum_eq`):
  `∫_0^c F_c(h) dh = c(∫φ)²/2`, so `(2/M)∫_0^c F_c = cq` is exactly the pole shift.
* **The continuum energy is unbounded below** (`continuumShellEnergy_eq`,
  `tendsto_continuumShellEnergy_atBot`): it equals the self finite part `log(1/(2πc)) + β(φ)/M`,
  negative for `c > e^{β/M}/(2π)`.
* **The lattice gain is the logarithm** (`latticeGain_eq`, `latticeGain_ge`,
  `tendsto_latticeGain_sub_log`): the actual energy minus the continuum energy is
  `log(2πc) − β/M + E(c) ≥ log(2πc) − β/M`, and `E(c) → 0`, so the gain is
  `log(2πc) − β/M + o(1)`.
* **Every conductor** (`sum_ramanujanLagCoefficient_period`, `continuumConductorEnergy_eq`,
  `conductorLatticeGain_ge`): the period mean of `c_m(h)` is `[m = 1]`, so the continuum
  conductor-`m` energy is the nonpolar reference energy `log(m/(2πc)) + …`, unbounded below, while
  the actual one is nonnegative and tends to `0`.

So the repayment of the logarithmic loss is carried by the gap `|h| ≥ 1` alone: the cell `0 < h < 1`
that the lattice omits holds `M log c` of shell weight.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset intervalIntegral
open scoped Real

namespace GaloisForLFunctions.SuccessorShellArithmetic

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis

variable {φ : ℝ → ℝ}

/-- The **continuum shell sum** `∫_0^c F_c(h) dh`: the shell sum with the integer shift replaced by
a continuous one. -/
def continuumShellSum (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ h in (0 : ℝ)..c, ∫ u in h / c..1, shellAutocorr φ u / u

/-- The conductor-one energy of the continuum shell completion. -/
def continuumShellEnergy (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  completeWeilSelfFinitePart φ c + completeWeilPoleShift φ c -
    2 * continuumShellSum φ c / ∫ u, φ u ^ 2

/-- What the integrality of the shift adds to the conductor-one energy. -/
def latticeGain (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  completedShellEnergy φ c - continuumShellEnergy φ c

/-- The gain is the deficit of the lattice shells against their continuum average. -/
theorem latticeGain_eq_shell_deficit (φ : ℝ → ℝ) (c : ℝ) :
    latticeGain φ c = 2 * (continuumShellSum φ c - shellSum φ c) / ∫ u, φ u ^ 2 := by
  unfold latticeGain continuumShellEnergy completedShellEnergy
  ring

section Continuum

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- `∫_0^1 ∫_s^1 H = ∫_0^1 s H(s)` for the regular part `H` of the shell integrand. -/
private theorem integral_tail_shellRegular :
    ∫ s in (0 : ℝ)..1, (∫ u in s..1, shellRegular φ u) =
      ∫ s in (0 : ℝ)..1, s * shellRegular φ s := by
  have hH := continuous_shellRegular hφ hsupp
  have hR : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => ∫ u in s..1, shellRegular φ u) (-shellRegular φ x) x := fun x _ =>
    integral_hasDerivAt_left (hH.intervalIntegrable _ _)
      hH.aestronglyMeasurable.stronglyMeasurableAtFilter hH.continuousAt
  have hid : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s) 1 x := fun x _ => hasDerivAt_id x
  have h := integral_mul_deriv_eq_deriv_mul hR hid (hH.neg.intervalIntegrable _ _)
    intervalIntegrable_const
  simp only [mul_one, integral_same, mul_zero, sub_zero, zero_sub, neg_mul,
    intervalIntegral.integral_neg, neg_neg] at h
  rw [h]
  exact integral_congr fun s _ => mul_comm _ _

/-- The unit-interval average of the shell weight: `∫_0^1 F = M − ∫_0^1 sH(s) ds`. -/
private theorem integral_shellWeight_unit :
    ∫ s in (0 : ℝ)..1, (∫ u in s..1, shellAutocorr φ u / u) =
      (∫ u, φ u ^ 2) - ∫ s in (0 : ℝ)..1, s * shellRegular φ s := by
  have hH := continuous_shellRegular hφ hsupp
  have hae : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) 1 →
      (∫ u in s..1, shellAutocorr φ u / u) =
        -(∫ u, φ u ^ 2) * Real.log s - ∫ u in s..1, shellRegular φ u := by
    refine Filter.Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    rw [integral_shell_eq_log_sub hφ hsupp hs.1, shellAutocorr_zero, one_div, Real.log_inv]
    ring
  have htail : Continuous fun s => ∫ u in s..1, shellRegular φ u := by
    have h1 := continuous_primitive (μ := volume) (fun a b => hH.intervalIntegrable a b) (1 : ℝ)
    refine h1.neg.congr fun s => ?_
    simp only [Pi.neg_apply]
    rw [integral_symm s 1, neg_neg]
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_sub (intervalIntegrable_log'.const_mul _)
      (htail.intervalIntegrable 0 1), intervalIntegral.integral_const_mul, integral_log,
    integral_tail_shellRegular hφ hsupp]
  simp

/-- **Continuum shells are the pole charge**: `∫_0^c F_c(h) dh = c(∫φ)²/2`. -/
theorem continuumShellSum_eq {c : ℝ} (hc : 0 < c) :
    continuumShellSum φ c = c * (∫ u, φ u) ^ 2 / 2 := by
  have hH := continuous_shellRegular hφ hsupp
  -- the charge: `(∫φ)² = 2(M − ∫_0^1 sH)`
  have hQ : (∫ u, φ u) ^ 2 = 2 * ((∫ u, φ u ^ 2) - ∫ u in (0 : ℝ)..1, u * shellRegular φ u) := by
    rw [← two_mul_integral_shellAutocorr hφ hsupp]
    have : ∫ u in (0 : ℝ)..1, shellAutocorr φ u =
        ∫ u in (0 : ℝ)..1, ((∫ v, φ v ^ 2) - u * shellRegular φ u) := by
      refine integral_congr fun u _ => ?_
      rw [shellAutocorr_eq_sub_mul u, shellAutocorr_zero]
    rw [this, intervalIntegral.integral_sub (f := fun _ => (∫ v, φ v ^ 2))
      (g := fun u => u * shellRegular φ u)
      intervalIntegrable_const ((continuous_id.mul hH).intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul]
  have hsub : continuumShellSum φ c =
      c * ∫ s in (0 : ℝ)..1, (∫ u in s..1, shellAutocorr φ u / u) := by
    unfold continuumShellSum
    have h := integral_comp_div (fun s => ∫ u in s..1, shellAutocorr φ u / u) hc.ne'
      (a := 0) (b := c)
    rw [zero_div, div_self hc.ne', smul_eq_mul] at h
    exact h
  rw [hsub, integral_shellWeight_unit hφ hsupp, hQ]
  ring

/-- **The continuum energy is the self finite part** `log(1/(2πc)) + β(φ)/M`. -/
theorem continuumShellEnergy_eq {c : ℝ} (hc : 0 < c) :
    continuumShellEnergy φ c = completeWeilSelfFinitePart φ c := by
  unfold continuumShellEnergy completeWeilPoleShift
  rw [continuumShellSum_eq hφ hsupp hc]
  ring

/-- The continuum energy tends to `−∞` at infinite overlap. -/
theorem tendsto_continuumShellEnergy_atBot :
    Tendsto (continuumShellEnergy φ) atTop atBot := by
  have hlog : Tendsto (fun c : ℝ => Real.log (2 * π * c)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  have h := tendsto_atBot_add_const_left atTop (bumpRobin φ 1 / (∫ u, φ u ^ 2))
    (tendsto_neg_atTop_atBot.comp hlog)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [continuumShellEnergy_eq hφ hsupp hc, completeWeilSelfFinitePart, one_div, Real.log_inv]
  simp only [Function.comp]
  ring

/-- The continuum energy is negative beyond `c₀ = e^{β/M}/(2π)`. -/
theorem continuumShellEnergy_neg {c : ℝ}
    (hc : Real.exp (bumpRobin φ 1 / (∫ u, φ u ^ 2)) / (2 * π) < c) :
    continuumShellEnergy φ c < 0 := by
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  rw [continuumShellEnergy_eq hφ hsupp hc0, completeWeilSelfFinitePart, one_div, Real.log_inv]
  have h1 : Real.exp (bumpRobin φ 1 / (∫ u, φ u ^ 2)) < 2 * π * c := by
    rw [div_lt_iff₀ (by positivity)] at hc
    linarith only [hc]
  have h2 := Real.log_lt_log (Real.exp_pos _) h1
  rw [Real.log_exp] at h2
  linarith only [h2]

/-- **The lattice gain is the logarithm plus the actual energy.** -/
theorem latticeGain_eq {c : ℝ} (hc : 0 < c) :
    latticeGain φ c = Real.log (2 * π * c) - bumpRobin φ 1 / (∫ u, φ u ^ 2) +
      completedShellEnergy φ c := by
  rw [latticeGain, continuumShellEnergy_eq hφ hsupp hc, completeWeilSelfFinitePart, one_div,
    Real.log_inv]
  ring

variable (hM : 0 < ∫ u, φ u ^ 2)
include hM

/-- **The integrality of the shift is worth at least `log(2πc) − β/M`.** -/
theorem latticeGain_ge {c : ℝ} (hc : 0 < c) :
    Real.log (2 * π * c) - bumpRobin φ 1 / (∫ u, φ u ^ 2) ≤ latticeGain φ c := by
  rw [latticeGain_eq hφ hsupp hc]
  linarith only [completedShellEnergy_nonneg hφ hsupp hM hc]

/-- The lattice gain is `log(2πc) − β/M + o(1)`: marginality of the actual energy. -/
theorem tendsto_latticeGain_sub_log :
    Tendsto (fun c => latticeGain φ c - Real.log (2 * π * c)) atTop
      (𝓝 (-(bumpRobin φ 1 / (∫ u, φ u ^ 2)))) := by
  have h := (tendsto_completedShellEnergy_atTop hφ hsupp hM).const_add
    (-(bumpRobin φ 1 / (∫ u, φ u ^ 2)))
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [latticeGain_eq hφ hsupp hc]
  ring

end Continuum

/-! ### Every conductor -/

/-- Over a full period the Ramanujan coefficients sum to `m[m = 1]`. -/
theorem sum_ramanujanLagCoefficient_period {m : ℕ} (hm : 0 < m) :
    ∑ h ∈ Finset.Ioc 0 m, ramanujanLagCoefficient m h = if m = 1 then 1 else 0 := by
  have hcount : ∀ d ∈ m.divisors,
      ∑ h ∈ Finset.Ioc 0 m, (if d ∣ h then (d : ℝ) else 0) = m := by
    intro d hd
    have hdm := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
    rw [Nat.cast_div hdm (by exact_mod_cast hd0.ne')]
    field_simp
  unfold ramanujanLagCoefficient
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun d hd => by rw [hcount d hd], ← Finset.sum_mul]
  have hμ := sum_divisors_moebius_div m
  have hμ' : ∑ d ∈ m.divisors, moebiusReal (m / d) = if m = 1 then 1 else 0 := by
    rw [← hμ]
    rfl
  rw [hμ']
  split_ifs with h1
  · subst h1; simp
  · simp

/-- The continuum conductor-`m` energy: the shell symbol `Σ c_m(h)F_c(h)` replaced by the period
mean of `c_m` times the continuum shell sum. -/
def continuumConductorEnergy (φ : ℝ → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  completeWeilAdjunctionEnergy φ c m -
    2 / ((∫ u, φ u ^ 2) * m.totient) *
      ((∑ h ∈ Finset.Ioc 0 m, ramanujanLagCoefficient m h) / m) * continuumShellSum φ c

section Conductor

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- **The continuum conductor energy is the nonpolar reference energy**
`log(1/(2πc)) + β(φ)/M + log m + τ(m) − γ`. -/
theorem continuumConductorEnergy_eq {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    continuumConductorEnergy φ c m =
      completeWeilSelfFinitePart φ c + ramanujanAdjunctionEnergy m -
        Real.eulerMascheroniConstant := by
  unfold continuumConductorEnergy completeWeilAdjunctionEnergy completeWeilPoleShift
  rw [sum_ramanujanLagCoefficient_period hm, continuumShellSum_eq hφ hsupp hc]
  split_ifs with h1
  · subst h1; simp only [Nat.totient_one, Nat.cast_one]; ring
  · simp

/-- Every continuum conductor energy tends to `−∞`. -/
theorem tendsto_continuumConductorEnergy_atBot {m : ℕ} (hm : 0 < m) :
    Tendsto (fun c => continuumConductorEnergy φ c m) atTop atBot := by
  have h := tendsto_atBot_add_const_right _ (ramanujanAdjunctionEnergy m -
    Real.eulerMascheroniConstant) (tendsto_continuumShellEnergy_atBot hφ hsupp)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [continuumConductorEnergy_eq hφ hsupp hc hm, continuumShellEnergy_eq hφ hsupp hc]
  ring

variable (hM : 0 < ∫ u, φ u ^ 2)
include hM

/-- **The lattice gain of conductor `m`** is at least `log(2πc) − β/M − log m − τ(m) + γ`, while
the actual energy is nonnegative. -/
theorem conductorLatticeGain_ge {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    Real.log (2 * π * c) - bumpRobin φ 1 / (∫ u, φ u ^ 2) - ramanujanAdjunctionEnergy m +
        Real.eulerMascheroniConstant ≤
      completedConductorEnergy φ c m - continuumConductorEnergy φ c m := by
  rw [continuumConductorEnergy_eq hφ hsupp hc hm, completeWeilSelfFinitePart, one_div,
    Real.log_inv]
  linarith only [completedConductorEnergy_nonneg hφ hsupp hM hc hm]

/-- The conductor lattice gain is `log(2πc) − β/M − log m − τ(m) + γ + o(1)`. -/
theorem tendsto_conductorLatticeGain_sub_log {m : ℕ} (hm : 0 < m) :
    Tendsto (fun c => completedConductorEnergy φ c m - continuumConductorEnergy φ c m -
        Real.log (2 * π * c)) atTop
      (𝓝 (-(bumpRobin φ 1 / (∫ u, φ u ^ 2)) - ramanujanAdjunctionEnergy m +
        Real.eulerMascheroniConstant)) := by
  have h := (tendsto_completedConductorEnergy_atTop hφ hsupp hM m).const_add
    (-(bumpRobin φ 1 / (∫ u, φ u ^ 2)) - ramanujanAdjunctionEnergy m +
      Real.eulerMascheroniConstant)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [continuumConductorEnergy_eq hφ hsupp hc hm, completeWeilSelfFinitePart, one_div,
    Real.log_inv]
  ring

end Conductor

end GaloisForLFunctions.SuccessorShellArithmetic

#print axioms GaloisForLFunctions.SuccessorShellArithmetic.continuumShellSum_eq
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.tendsto_continuumShellEnergy_atBot
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.tendsto_latticeGain_sub_log
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.conductorLatticeGain_ge
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.tendsto_conductorLatticeGain_sub_log
