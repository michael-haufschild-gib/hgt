import GaloisForLFunctions.RHTower.SuzukiCanonicalKernelDifferentiability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Local `W^{1,1}` structure of Suzuki's logarithmic kernel

The moving cusps of `h_omega(xy)` become fixed additive cusps after the logarithmic change of
variables.  This module establishes the exact derivative and interval integrability of each
arithmetic log atom.  It is the analytic replacement for an invalid fixed pointwise dominator in
Suzuki (2012), Lemma `lem_ad1`.
-/

open ArithmeticFunction Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- One arithmetic atom in `r ↦ h_omega(exp r)`, before multiplication by its Dirichlet
coefficient. -/
def suzukiSourceGLogAtom (omega : ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  ((Real.exp (-r) : ℝ) : ℂ) *
    suzukiSourceG omega ((n : ℝ) * Real.exp (-r))

/-- Exact a.e. derivative field of one logarithmic arithmetic atom. -/
def suzukiSourceGLogAtomDerivative (omega : ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  ((-Real.exp (-r) : ℝ) : ℂ) *
      suzukiSourceG omega ((n : ℝ) * Real.exp (-r)) +
    ((Real.exp (-r) : ℝ) : ℂ) *
      (((-(n : ℝ) * Real.exp (-r) : ℝ) : ℂ) *
        suzukiSourceGDerivativeTotal omega ((n : ℝ) * Real.exp (-r)))

/-- Exact derivative of a log atom away from its sole cusp `n exp(-r) = 1`. -/
theorem hasDerivAt_suzukiSourceGLogAtom
    {omega : ℝ} {n : ℕ} (homega : 1 < omega) (hn : 1 ≤ n) {r : ℝ}
    (hcusp : (n : ℝ) * Real.exp (-r) ≠ 1) :
    HasDerivAt (suzukiSourceGLogAtom omega n)
      (suzukiSourceGLogAtomDerivative omega n r) r := by
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-r)) r := by
    convert (Real.hasDerivAt_exp (-r)).comp r (hasDerivAt_neg r) using 1 <;>
      first | rfl | ring
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hu : HasDerivAt (fun z : ℝ => (n : ℝ) * Real.exp (-z))
      (-(n : ℝ) * Real.exp (-r)) r := by
    convert hexp.const_mul (n : ℝ) using 1 <;> first | rfl | ring
  have hu0 : 0 < (n : ℝ) * Real.exp (-r) := mul_pos hn0 (Real.exp_pos _)
  have hg := hasDerivAt_suzukiSourceG_total homega hu0 hcusp
  have hcomp := hg.hasFDerivAt.comp_hasDerivAt_of_eq r hu rfl
  have hprod := (ContinuousLinearMap.mul ℝ ℂ).hasDerivAt_of_bilinear
    (fun _ => hexp.ofReal_comp) (fun _ => hcomp)
  have hmulApply (a b : ℂ) : ((ContinuousLinearMap.mul ℝ ℂ) a) b = a * b := rfl
  change HasDerivAt (fun z => suzukiSourceGLogAtom omega n z)
    (suzukiSourceGLogAtomDerivative omega n r) r
  simpa only [suzukiSourceGLogAtom, suzukiSourceGLogAtomDerivative,
    ContinuousLinearMap.toSpanSingleton_apply, Function.comp_apply,
    Complex.real_smul, hmulApply, add_comm] using hprod

/-- The a.e. derivative of each logarithmic arithmetic atom is integrable on every compact
interval, including intervals crossing its cusp. -/
theorem intervalIntegrable_suzukiSourceGLogAtomDerivative
    {omega : ℝ} {n : ℕ} (homega : 1 < omega) (hn : 1 ≤ n) (p q : ℝ) :
    IntervalIntegrable (suzukiSourceGLogAtomDerivative omega n) volume p q := by
  let u : ℝ → ℝ := fun r => (n : ℝ) * Real.exp (-r)
  let u' : ℝ → ℝ := fun r => -(n : ℝ) * Real.exp (-r)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have huCont : Continuous u := by
    dsimp only [u]
    fun_prop
  have huDeriv : ∀ r ∈ Ioo (min p q) (max p q), HasDerivAt u (u' r) r := by
    intro r _
    have hexp : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-r)) r := by
      convert (Real.hasDerivAt_exp (-r)).comp r (hasDerivAt_neg r) using 1 <;>
        first | rfl | ring
    dsimp only [u, u']
    convert hexp.const_mul (n : ℝ) using 1 <;> first | rfl | ring
  have huNonpos : ∀ r ∈ Ioo (min p q) (max p q), u' r ≤ 0 := by
    intro r _
    dsimp only [u']
    have hnonneg : 0 ≤ (n : ℝ) * Real.exp (-r) :=
      mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le
    nlinarith
  have htotal : IntervalIntegrable (suzukiSourceGDerivativeTotal omega)
      volume (u p) (u q) := by
    apply intervalIntegrable_suzukiSourceGDerivativeTotal_of_pos homega
    · exact mul_pos hn0 (Real.exp_pos _)
    · exact mul_pos hn0 (Real.exp_pos _)
  have hchain : IntervalIntegrable
      (fun r => u' r • (suzukiSourceGDerivativeTotal omega ∘ u) r)
      volume p q := by
    exact (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonpos
      huCont.continuousOn huDeriv huNonpos).2 htotal
  have hA : ContinuousOn (fun r : ℝ => ((Real.exp (-r) : ℝ) : ℂ)) (uIcc p q) := by
    fun_prop
  have hsecondRaw := hchain.continuousOn_mul hA
  have hsecond : IntervalIntegrable (fun r =>
      ((Real.exp (-r) : ℝ) : ℂ) *
        (((-(n : ℝ) * Real.exp (-r) : ℝ) : ℂ) *
          suzukiSourceGDerivativeTotal omega ((n : ℝ) * Real.exp (-r))))
      volume p q := by
    simpa only [u, u', Function.comp_apply, Complex.real_smul] using hsecondRaw
  have hGcomp : Continuous (fun r : ℝ =>
      suzukiSourceG omega ((n : ℝ) * Real.exp (-r))) := by
    rw [continuous_iff_continuousAt]
    intro r
    exact (continuousAt_suzukiSourceG homega (mul_pos hn0 (Real.exp_pos _))).comp_of_eq
      huCont.continuousAt rfl
  have hfirst : IntervalIntegrable (fun r =>
      ((-Real.exp (-r) : ℝ) : ℂ) *
        suzukiSourceG omega ((n : ℝ) * Real.exp (-r))) volume p q := by
    have hcoef : Continuous (fun r : ℝ => ((-Real.exp (-r) : ℝ) : ℂ)) := by
      fun_prop
    change IntervalIntegrable
      ((fun r : ℝ => ((-Real.exp (-r) : ℝ) : ℂ)) *
        fun r => suzukiSourceG omega ((n : ℝ) * Real.exp (-r))) volume p q
    exact (hcoef.mul hGcomp).intervalIntegrable (μ := volume) p q
  change IntervalIntegrable
    (fun r => suzukiSourceGLogAtomDerivative omega n r) volume p q
  simpa only [suzukiSourceGLogAtomDerivative] using hfirst.add hsecond

/-- Every logarithmic arithmetic atom is globally continuous. -/
theorem continuous_suzukiSourceGLogAtom
    {omega : ℝ} {n : ℕ} (homega : 1 < omega) (hn : 1 ≤ n) :
    Continuous (suzukiSourceGLogAtom omega n) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hu : Continuous (fun r : ℝ => (n : ℝ) * Real.exp (-r)) := by fun_prop
  have hg : Continuous (fun r : ℝ =>
      suzukiSourceG omega ((n : ℝ) * Real.exp (-r))) := by
    rw [continuous_iff_continuousAt]
    intro r
    exact (continuousAt_suzukiSourceG homega (mul_pos hn0 (Real.exp_pos _))).comp_of_eq
      hu.continuousAt rfl
  unfold suzukiSourceGLogAtom
  fun_prop

/-- Exact fundamental-theorem identity for a log atom across its integrable cusp.  This packages
the atom as a genuine local `W^{1,1}` function, rather than merely piecewise `C¹`. -/
theorem integral_suzukiSourceGLogAtomDerivative_eq_sub
    {omega : ℝ} {n : ℕ} (homega : 1 < omega) (hn : 1 ≤ n) (p q : ℝ) :
    (∫ r in p..q, suzukiSourceGLogAtomDerivative omega n r) =
      suzukiSourceGLogAtom omega n q - suzukiSourceGLogAtom omega n p := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  apply MeasureTheory.integral_eq_of_hasDerivAt_off_countable
    (s := {Real.log (n : ℝ)}) (suzukiSourceGLogAtom omega n)
      (suzukiSourceGLogAtomDerivative omega n) (Set.countable_singleton _)
      (continuous_suzukiSourceGLogAtom homega hn).continuousOn
  · intro r hr
    have hrne : r ≠ Real.log (n : ℝ) := by simpa only [mem_singleton_iff] using hr.2
    apply hasDerivAt_suzukiSourceGLogAtom homega hn
    intro hcusp
    have hlog := congrArg Real.log hcusp
    rw [Real.log_mul (ne_of_gt hn0) (Real.exp_ne_zero _), Real.log_exp,
      Real.log_one] at hlog
    apply hrne
    linarith
  · exact intervalIntegrable_suzukiSourceGLogAtomDerivative homega hn p q

/-- Fixed arithmetic cutoff for the logarithmic Suzuki kernel.  Unlike the literal floor sum,
this representation has a fixed finite index set, while retaining all atoms up to `N`. -/
def suzukiSourceHLogFixed (omega : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
      suzukiSourceGLogAtom omega n r

/-- Exact a.e. derivative field of the fixed logarithmic arithmetic cutoff. -/
def suzukiSourceHLogFixedDerivative (omega : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
      suzukiSourceGLogAtomDerivative omega n r

/-- Every fixed logarithmic arithmetic cutoff is globally continuous. -/
theorem continuous_suzukiSourceHLogFixed
    {omega : ℝ} (homega : 1 < omega) (N : ℕ) :
    Continuous (suzukiSourceHLogFixed omega N) := by
  unfold suzukiSourceHLogFixed
  refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
  exact continuous_suzukiSourceGLogAtom homega (Finset.mem_Icc.mp hn).1

/-- The a.e. derivative of a fixed logarithmic arithmetic cutoff is interval integrable. -/
theorem intervalIntegrable_suzukiSourceHLogFixedDerivative
    {omega : ℝ} (homega : 1 < omega) (N : ℕ) (p q : ℝ) :
    IntervalIntegrable (suzukiSourceHLogFixedDerivative omega N) volume p q := by
  unfold suzukiSourceHLogFixedDerivative
  have h := IntervalIntegrable.sum
      (f := fun n r => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceGLogAtomDerivative omega n r)
      (Finset.Icc 1 N) fun n hn =>
    (intervalIntegrable_suzukiSourceGLogAtomDerivative homega
      (Finset.mem_Icc.mp hn).1 p q).const_mul
        ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)
  have heq : (∑ n ∈ Finset.Icc 1 N, fun r =>
      ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceGLogAtomDerivative omega n r) =
      fun r => ∑ n ∈ Finset.Icc 1 N,
        ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
          suzukiSourceGLogAtomDerivative omega n r := by
    funext r
    rw [Finset.sum_apply]
  rwa [heq] at h

/-- Exact fundamental-theorem identity for every fixed arithmetic cutoff.  Thus the whole finite
logarithmic Suzuki kernel, not only its individual cusp atoms, is locally `W^{1,1}`. -/
theorem integral_suzukiSourceHLogFixedDerivative_eq_sub
    {omega : ℝ} (homega : 1 < omega) (N : ℕ) (p q : ℝ) :
    (∫ r in p..q, suzukiSourceHLogFixedDerivative omega N r) =
      suzukiSourceHLogFixed omega N q - suzukiSourceHLogFixed omega N p := by
  change (∫ r in p..q, ∑ n ∈ Finset.Icc 1 N,
      ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceGLogAtomDerivative omega n r) = _
  rw [intervalIntegral.integral_finsetSum (fun n hn =>
      (intervalIntegrable_suzukiSourceGLogAtomDerivative homega
        (Finset.mem_Icc.mp hn).1 p q).const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]
  unfold suzukiSourceHLogFixed
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_suzukiSourceGLogAtomDerivative_eq_sub homega
    (Finset.mem_Icc.mp hn).1]
  ring

/-- The literal floor-truncated kernel in logarithmic coordinates equals any fixed cutoff beyond
the current floor.  This is the exact bridge between Suzuki's printed kernel and the local
`W^{1,1}` model. -/
theorem suzukiSourceHFinite_exp_eq_logFixed
    {omega r : ℝ} {N : ℕ} (hN : ⌊Real.exp r⌋₊ ≤ N) :
    suzukiSourceHFinite omega (Real.exp r) = suzukiSourceHLogFixed omega N r := by
  rw [suzukiSourceHFinite_eq_fixedSum (Real.exp_pos r) hN]
  have hscale : (1 / (((Real.exp r : ℝ) : ℂ))) =
      ((Real.exp (-r) : ℝ) : ℂ) := by
    rw [one_div, ← Complex.ofReal_inv, ← Real.exp_neg]
  rw [hscale, Finset.mul_sum]
  unfold suzukiSourceHLogFixed suzukiSourceGLogAtom
  apply Finset.sum_congr rfl
  intro n _
  have harg : (n : ℝ) / Real.exp r = (n : ℝ) * Real.exp (-r) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [harg]
  ring

/-- A single upper logarithmic endpoint supplies a common fixed arithmetic cutoff below it. -/
theorem suzukiSourceHFinite_exp_eq_logFixed_floor_of_le
    (omega : ℝ) {r B : ℝ} (hrB : r ≤ B) :
    suzukiSourceHFinite omega (Real.exp r) =
      suzukiSourceHLogFixed omega ⌊Real.exp B⌋₊ r := by
  apply suzukiSourceHFinite_exp_eq_logFixed
  exact Nat.floor_mono (Real.exp_le_exp.mpr hrB)

/-- The literal logarithmic Suzuki kernel is globally continuous despite its changing floor. -/
theorem continuous_suzukiSourceHFinite_exp
    {omega : ℝ} (homega : 1 < omega) :
    Continuous (fun r : ℝ => suzukiSourceHFinite omega (Real.exp r)) := by
  rw [continuous_iff_continuousAt]
  intro r
  change ContinuousAt (suzukiSourceHFinite omega ∘ Real.exp) r
  exact (continuousAt_suzukiSourceHFinite homega (Real.exp_pos r)).comp
    Real.continuous_exp.continuousAt

/-- Local derivative field for the literal logarithmic kernel, using the common arithmetic cutoff
forced by an upper log endpoint `B`. -/
def suzukiSourceHLogDerivativeBelow (omega B r : ℝ) : ℂ :=
  suzukiSourceHLogFixedDerivative omega ⌊Real.exp B⌋₊ r

/-- The local derivative field is interval integrable on every compact interval. -/
theorem intervalIntegrable_suzukiSourceHLogDerivativeBelow
    {omega : ℝ} (homega : 1 < omega) (B p q : ℝ) :
    IntervalIntegrable (suzukiSourceHLogDerivativeBelow omega B) volume p q := by
  exact intervalIntegrable_suzukiSourceHLogFixedDerivative homega ⌊Real.exp B⌋₊ p q

/-- Exact local `W^{1,1}` fundamental theorem for Suzuki's literal logarithmic kernel.  Both
endpoints may cross any finite collection of arithmetic cusps; only a common upper endpoint is
required. -/
theorem integral_suzukiSourceHLogDerivativeBelow_eq_sub
    {omega : ℝ} (homega : 1 < omega) {B p q : ℝ} (hpB : p ≤ B) (hqB : q ≤ B) :
    (∫ r in p..q, suzukiSourceHLogDerivativeBelow omega B r) =
      suzukiSourceHFinite omega (Real.exp q) -
        suzukiSourceHFinite omega (Real.exp p) := by
  change (∫ r in p..q,
      suzukiSourceHLogFixedDerivative omega ⌊Real.exp B⌋₊ r) = _
  rw [integral_suzukiSourceHLogFixedDerivative_eq_sub homega,
    ← suzukiSourceHFinite_exp_eq_logFixed_floor_of_le omega hqB,
    ← suzukiSourceHFinite_exp_eq_logFixed_floor_of_le omega hpB]

/-- Every arithmetic log atom vanishes before its cusp enters the support. -/
theorem suzukiSourceGLogAtom_eq_zero_of_le_log
    {omega : ℝ} {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : r ≤ Real.log n) :
    suzukiSourceGLogAtom omega n r = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hu : 1 ≤ (n : ℝ) * Real.exp (-r) := by
    have hexp : Real.exp (-Real.log n) ≤ Real.exp (-r) :=
      Real.exp_le_exp.mpr (neg_le_neg hr)
    rw [Real.exp_neg, Real.exp_log hn0, inv_eq_one_div] at hexp
    have hmul := (div_le_iff₀ hn0).mp hexp
    simpa only [one_mul, mul_comm] using hmul
  rw [suzukiSourceGLogAtom, suzukiSourceG, if_neg]
  · ring
  · exact fun h => (not_lt_of_ge hu) h.2

/-- The exact atom derivative field vanishes before the same cusp. -/
theorem suzukiSourceGLogAtomDerivative_eq_zero_of_le_log
    {omega : ℝ} {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : r ≤ Real.log n) :
    suzukiSourceGLogAtomDerivative omega n r = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hu : 1 ≤ (n : ℝ) * Real.exp (-r) := by
    have hexp : Real.exp (-Real.log n) ≤ Real.exp (-r) :=
      Real.exp_le_exp.mpr (neg_le_neg hr)
    rw [Real.exp_neg, Real.exp_log hn0, inv_eq_one_div] at hexp
    have hmul := (div_le_iff₀ hn0).mp hexp
    simpa only [one_mul, mul_comm] using hmul
  rw [suzukiSourceGLogAtomDerivative, suzukiSourceG, if_neg,
    suzukiSourceGDerivativeTotal, if_neg]
  · ring
  · exact fun h => (not_lt_of_ge hu) h.2
  · exact fun h => (not_lt_of_ge hu) h.2

/-- Fixed logarithmic cutoffs and their derivative fields vanish on the nonpositive half-line. -/
theorem suzukiSourceHLogFixed_eq_zero_of_nonpos
    (omega : ℝ) (N : ℕ) {r : ℝ} (hr : r ≤ 0) :
    suzukiSourceHLogFixed omega N r = 0 := by
  unfold suzukiSourceHLogFixed
  apply Finset.sum_eq_zero
  intro n hn
  rw [suzukiSourceGLogAtom_eq_zero_of_le_log (Finset.mem_Icc.mp hn).1]
  · ring
  · exact hr.trans (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1))

theorem suzukiSourceHLogFixedDerivative_eq_zero_of_nonpos
    (omega : ℝ) (N : ℕ) {r : ℝ} (hr : r ≤ 0) :
    suzukiSourceHLogFixedDerivative omega N r = 0 := by
  unfold suzukiSourceHLogFixedDerivative
  apply Finset.sum_eq_zero
  intro n hn
  rw [suzukiSourceGLogAtomDerivative_eq_zero_of_le_log (Finset.mem_Icc.mp hn).1]
  · ring
  · exact hr.trans (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1))

/-- Compact truncation of the literal logarithmic kernel at an upper log endpoint. -/
def suzukiSourceHLogTrunc (omega B r : ℝ) : ℂ :=
  (Ioc 0 B).indicator (fun u => suzukiSourceHFinite omega (Real.exp u)) r

/-- Compact truncation of its exact local derivative field. -/
def suzukiSourceHLogDerivativeTrunc (omega B r : ℝ) : ℂ :=
  (Ioc 0 B).indicator (suzukiSourceHLogDerivativeBelow omega B) r

/-- Below its upper endpoint, compact logarithmic truncation is exactly Suzuki's literal kernel,
including nonpositive logarithmic arguments where both sides vanish. -/
theorem suzukiSourceHLogTrunc_eq_sourceHFinite_exp
    (omega : ℝ) {B r : ℝ} (hrB : r ≤ B) :
    suzukiSourceHLogTrunc omega B r =
      suzukiSourceHFinite omega (Real.exp r) := by
  rw [suzukiSourceHLogTrunc]
  by_cases hr : r ∈ Ioc 0 B
  · rw [Set.indicator_of_mem hr]
  · have hr0 : r ≤ 0 := by
      by_contra h
      exact hr ⟨lt_of_not_ge h, hrB⟩
    rw [Set.indicator_of_notMem hr,
      suzukiSourceHFinite_exp_eq_logFixed_floor_of_le omega hrB,
      suzukiSourceHLogFixed_eq_zero_of_nonpos omega _ hr0]

theorem integrable_suzukiSourceHLogTrunc
    {omega B : ℝ} (homega : 1 < omega) (hB : 0 ≤ B) :
    Integrable (suzukiSourceHLogTrunc omega B) := by
  have hlocal : IntegrableOn (fun r : ℝ =>
      suzukiSourceHFinite omega (Real.exp r)) (Ioc 0 B) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mp
      ((continuous_suzukiSourceHFinite_exp homega).intervalIntegrable 0 B)
  exact hlocal.integrable_indicator measurableSet_Ioc

theorem integrable_suzukiSourceHLogDerivativeTrunc
    {omega B : ℝ} (homega : 1 < omega) (hB : 0 ≤ B) :
    Integrable (suzukiSourceHLogDerivativeTrunc omega B) := by
  have hlocal : IntegrableOn (suzukiSourceHLogDerivativeBelow omega B) (Ioc 0 B) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mp
      (intervalIntegrable_suzukiSourceHLogDerivativeBelow homega B 0 B)
  exact hlocal.integrable_indicator measurableSet_Ioc

/-- On intervals lying strictly below the upper truncation, the truncated derivative retains the
exact FTC identity of the literal logarithmic kernel. -/
theorem integral_suzukiSourceHLogDerivativeTrunc_eq_sub
    {omega B p q : ℝ} (homega : 1 < omega) (hpB : p < B) (hqB : q < B) :
    (∫ r in p..q, suzukiSourceHLogDerivativeTrunc omega B r) =
      suzukiSourceHFinite omega (Real.exp q) -
        suzukiSourceHFinite omega (Real.exp p) := by
  have hEq : (∫ r in p..q, suzukiSourceHLogDerivativeTrunc omega B r) =
      ∫ r in p..q, suzukiSourceHLogDerivativeBelow omega B r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r
    intro hr
    change (Ioc 0 B).indicator (suzukiSourceHLogDerivativeBelow omega B) r =
      suzukiSourceHLogDerivativeBelow omega B r
    by_cases hr0 : r ≤ 0
    · rw [Set.indicator_of_notMem (fun h => (not_lt_of_ge hr0) h.1)]
      exact (suzukiSourceHLogFixedDerivative_eq_zero_of_nonpos omega ⌊Real.exp B⌋₊ hr0).symm
    · have hrMax : r ≤ max p q := by
        rw [uIoc] at hr
        exact hr.2
      have hrmem : r ∈ Ioc 0 B :=
        ⟨lt_of_not_ge hr0, (hrMax.trans_lt (max_lt hpB hqB)).le⟩
      rw [Set.indicator_of_mem hrmem]
  rw [hEq]
  exact integral_suzukiSourceHLogDerivativeBelow_eq_sub homega hpB.le hqB.le

end RHTower
