import GaloisForLFunctions.RHTower.ReflectedBiHeatArbitraryTwoRateReceiverCone

/-!
# Reflected bi-heat separated-sign finite-rate cone

An arbitrary finite negative block of low hyperbolic rates and positive block of
separated high rates has only the forced wall zero exactly when its first wall
derivative is nonnegative. The converse is constructive: negative derivative
forces an additional positive root by low-wall asymptotics and high-rate dominance.

The classification permits arbitrary cardinalities and incommensurate real rates.
Canonical real-power aperture normalization transports it to an exact RH receiver.

`[NEW] [MULTI-RATE INCOMMENSURATE] [EXACT SIGN CONE] [LEAN-PROVED]`
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Finite signed packet with a negative low-rate block and positive high-rate block. -/
def reflectedBiHeatSeparatedSignReporter {m n : ℕ}
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ) (t : ℝ) : ℝ :=
  -(∑ i, p i * Real.sinh (lambda i * t)) +
    ∑ j, q j * Real.sinh (mu j * t)

/-- First wall derivative of a separated-sign packet. -/
def reflectedBiHeatSeparatedSignWallDerivative {m n : ℕ}
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ) : ℝ :=
  (∑ j, q j * mu j) - ∑ i, p i * lambda i

theorem reflectedBiHeatSeparatedSignReporter_neg {m n : ℕ}
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ) (t : ℝ) :
    reflectedBiHeatSeparatedSignReporter p lambda q mu (-t) =
      -reflectedBiHeatSeparatedSignReporter p lambda q mu t := by
  simp only [reflectedBiHeatSeparatedSignReporter]
  simp_rw [show ∀ r : ℝ, r * -t = -(r * t) by intro r; ring, Real.sinh_neg]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-- A nonnegative first wall derivative forces strict positivity on the positive half-line. -/
theorem reflectedBiHeatSeparatedSignReporter_pos
    {m n : ℕ} (hm : 0 < m)
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ)
    {kappa t : ℝ} (hkappa : 0 < kappa) (ht : 0 < t)
    (hp : ∀ i, 0 < p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa)
    (hq : ∀ j, 0 < q j)
    (hhigh : ∀ j, kappa ≤ mu j)
    (hderiv : 0 ≤ reflectedBiHeatSeparatedSignWallDerivative p lambda q mu) :
    0 < reflectedBiHeatSeparatedSignReporter p lambda q mu t := by
  let G : ℝ := Real.sinh (kappa * t) / (kappa * t)
  have hkt : 0 < kappa * t := mul_pos hkappa ht
  have hG : 0 < G := div_pos (Real.sinh_pos_iff.mpr hkt) hkt
  have hlowTerm : ∀ i : Fin m,
      p i * Real.sinh (lambda i * t) <
        (p i * lambda i) * t * G := by
    intro i
    have hlit : 0 < lambda i * t := mul_pos (hlambda i) ht
    have hmono := GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
      (show lambda i * t ∈ Ioi 0 from hlit)
      (show kappa * t ∈ Ioi 0 from hkt)
      (mul_lt_mul_of_pos_right (hlow i) ht)
    have heq : p i * Real.sinh (lambda i * t) =
        (p i * lambda i) * t *
          (Real.sinh (lambda i * t) / (lambda i * t)) := by
      field_simp [(hlambda i).ne', ht.ne']
    rw [heq]
    exact mul_lt_mul_of_pos_left hmono
      (mul_pos (mul_pos (hp i) (hlambda i)) ht)
  have hhighTerm : ∀ j : Fin n,
      (q j * mu j) * t * G ≤ q j * Real.sinh (mu j * t) := by
    intro j
    have hmupos : 0 < mu j := lt_of_lt_of_le hkappa (hhigh j)
    have hmut : 0 < mu j * t := mul_pos hmupos ht
    have hmono : G ≤ Real.sinh (mu j * t) / (mu j * t) := by
      rcases eq_or_lt_of_le (hhigh j) with heq | hlt
      · simp [G, heq]
      · exact (GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
          (show kappa * t ∈ Ioi 0 from hkt)
          (show mu j * t ∈ Ioi 0 from hmut)
          (mul_lt_mul_of_pos_right hlt ht)).le
    have heq : q j * Real.sinh (mu j * t) =
        (q j * mu j) * t *
          (Real.sinh (mu j * t) / (mu j * t)) := by
      field_simp [hmupos.ne', ht.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmono
      (mul_nonneg (mul_nonneg (hq j).le hmupos.le) ht.le)
  have hlowSum :
      (∑ i, p i * Real.sinh (lambda i * t)) <
        ∑ i, (p i * lambda i) * t * G := by
    exact Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm))
      (fun i _ => hlowTerm i)
  have hhighSum :
      (∑ j, (q j * mu j) * t * G) ≤
        ∑ j, q j * Real.sinh (mu j * t) := by
    exact Finset.sum_le_sum (fun j _ => hhighTerm j)
  have hcommon :
      (∑ i, (p i * lambda i) * t * G) ≤
        ∑ j, (q j * mu j) * t * G := by
    have hsum : (∑ i, p i * lambda i) ≤ ∑ j, q j * mu j := by
      simpa [reflectedBiHeatSeparatedSignWallDerivative] using hderiv
    have hmul := mul_le_mul_of_nonneg_right hsum (mul_nonneg ht.le hG.le)
    calc
      (∑ i, (p i * lambda i) * t * G) =
          (∑ i, p i * lambda i) * (t * G) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ (∑ j, q j * mu j) * (t * G) := hmul
      _ = ∑ j, (q j * mu j) * t * G := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [reflectedBiHeatSeparatedSignReporter]
  linarith

/-- A scaled hyperbolic atom divided by wall displacement tends to its rate. -/
theorem tendsto_sinh_rate_mul_div_self_nhdsGT_zero {rate : ℝ}
    (hrate : 0 < rate) :
    Tendsto (fun t : ℝ => Real.sinh (rate * t) / t)
      (𝓝[>] 0) (𝓝 rate) := by
  have hscale : Tendsto (fun t : ℝ => rate * t) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hbase : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul hbase)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [mem_compl_iff, mem_singleton_iff]
      exact mul_ne_zero hrate.ne' ht.ne'
  have hdiv : Tendsto
      (fun t : ℝ => Real.sinh (rate * t) / (rate * t))
      (𝓝[>] 0) (𝓝 1) := RHTower.tendsto_sinh_div.comp hscale
  have hconst : Tendsto (fun _ : ℝ => rate) (𝓝[>] 0) (𝓝 rate) :=
    tendsto_const_nhds
  have hlim := hconst.mul hdiv
  simpa using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    field_simp [hrate.ne', (show 0 < t from ht).ne'])

/-- The divided finite packet tends to its exact first wall derivative. -/
theorem tendsto_reflectedBiHeatSeparatedSignReporter_div_self_nhdsGT_zero
    {m n : ℕ} (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ)
    (hlambda : ∀ i, 0 < lambda i) (hmu : ∀ j, 0 < mu j) :
    Tendsto
      (fun t : ℝ => reflectedBiHeatSeparatedSignReporter p lambda q mu t / t)
      (𝓝[>] 0)
      (𝓝 (reflectedBiHeatSeparatedSignWallDerivative p lambda q mu)) := by
  have hlow : Tendsto
      (fun t : ℝ => ∑ i, p i * Real.sinh (lambda i * t) / t)
      (𝓝[>] 0) (𝓝 (∑ i, p i * lambda i)) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    simpa only [mul_div_assoc] using
      (tendsto_sinh_rate_mul_div_self_nhdsGT_zero (hlambda i)).const_mul (p i)
  have hhigh : Tendsto
      (fun t : ℝ => ∑ j, q j * Real.sinh (mu j * t) / t)
      (𝓝[>] 0) (𝓝 (∑ j, q j * mu j)) := by
    apply tendsto_finsetSum Finset.univ
    intro j _
    simpa only [mul_div_assoc] using
      (tendsto_sinh_rate_mul_div_self_nhdsGT_zero (hmu j)).const_mul (q j)
  have hlim := hlow.neg.add hhigh
  have heq :
      (fun t : ℝ =>
        -(∑ i, p i * Real.sinh (lambda i * t) / t) +
          ∑ j, q j * Real.sinh (mu j * t) / t) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => reflectedBiHeatSeparatedSignReporter p lambda q mu t / t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [reflectedBiHeatSeparatedSignReporter, ← Finset.sum_div, ← Finset.sum_div]
    field_simp [(show 0 < t from ht).ne']
    simp only [mul_comm]
  have hlim' := hlim.congr' heq
  rw [reflectedBiHeatSeparatedSignWallDerivative]
  simpa only [sub_eq_add_neg, add_comm] using hlim'

/-- Every finite low-rate block is negligible relative to one separated high-rate atom. -/
theorem tendsto_reflectedBiHeatLowRateSum_div_sinh_atTop
    {m : ℕ} (p lambda : Fin m → ℝ) {nu : ℝ}
    (hnu : 0 < nu) (hlambda : ∀ i, 0 < lambda i)
    (hsep : ∀ i, lambda i < nu) :
    Tendsto
      (fun t : ℝ =>
        (∑ i, p i * Real.sinh (lambda i * t)) / Real.sinh (nu * t))
      atTop (𝓝 0) := by
  have hterms : ∀ i : Fin m,
      Tendsto
        (fun t : ℝ => p i * Real.sinh (lambda i * t) / Real.sinh (nu * t))
        atTop (𝓝 0) := by
    intro i
    have htop := tendsto_sinh_rate_ratio_atTop (hlambda i) (hsep i)
    have hinv : Tendsto
        (fun t : ℝ => 1 / (Real.sinh (nu * t) / Real.sinh (lambda i * t)))
        atTop (𝓝 0) := htop.const_div_atTop 1
    have hratio : Tendsto
        (fun t : ℝ => Real.sinh (lambda i * t) / Real.sinh (nu * t))
        atTop (𝓝 0) := by
      apply hinv.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hsl : Real.sinh (lambda i * t) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (mul_pos (hlambda i) ht)).ne'
      have hsn : Real.sinh (nu * t) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (mul_pos hnu ht)).ne'
      field_simp
    have hmul := (tendsto_const_nhds.mul hratio :
      Tendsto
        (fun t : ℝ => p i *
          (Real.sinh (lambda i * t) / Real.sinh (nu * t)))
        atTop (𝓝 (p i * 0)))
    simpa [mul_div_assoc] using hmul
  have hsum : Tendsto
      (fun t : ℝ =>
        ∑ i, p i * Real.sinh (lambda i * t) / Real.sinh (nu * t))
      atTop (𝓝 (∑ _i : Fin m, (0 : ℝ))) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    exact hterms i
  have heq :
      (fun t : ℝ =>
        ∑ i, p i * Real.sinh (lambda i * t) / Real.sinh (nu * t)) =ᶠ[atTop]
      (fun t : ℝ =>
        (∑ i, p i * Real.sinh (lambda i * t)) / Real.sinh (nu * t)) := by
    filter_upwards with t
    rw [Finset.sum_div]
  simpa using hsum.congr' heq

/-- A negative first wall derivative forces an additional positive root. -/
theorem exists_pos_reflectedBiHeatSeparatedSignReporter_eq_zero_of_derivative_neg
    {m n : ℕ} (hn : 0 < n)
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa)
    (hq : ∀ j, 0 < q j)
    (hhigh : ∀ j, kappa ≤ mu j)
    (hderiv : reflectedBiHeatSeparatedSignWallDerivative p lambda q mu < 0) :
    ∃ t : ℝ, 0 < t ∧ reflectedBiHeatSeparatedSignReporter p lambda q mu t = 0 := by
  have hmu : ∀ j, 0 < mu j := fun j => lt_of_lt_of_le hkappa (hhigh j)
  have hzeroLim :=
    tendsto_reflectedBiHeatSeparatedSignReporter_div_self_nhdsGT_zero
      p lambda q mu hlambda hmu
  have hevNeg : ∀ᶠ t in 𝓝[>] 0,
      reflectedBiHeatSeparatedSignReporter p lambda q mu t / t < 0 :=
    (tendsto_order.mp hzeroLim).2 0 hderiv
  obtain ⟨t0, ht0, hneg0⟩ : ∃ t0 : ℝ, 0 < t0 ∧
      reflectedBiHeatSeparatedSignReporter p lambda q mu t0 < 0 := by
    have hevPos : ∀ᶠ t in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    have hev := hevPos.and hevNeg
    rcases hev.exists with ⟨t, ht, hnorm⟩
    have hvalue : reflectedBiHeatSeparatedSignReporter p lambda q mu t < 0 := by
      have := (div_lt_iff₀ (show 0 < t from ht)).mp hnorm
      simpa using this
    exact ⟨t, ht, hvalue⟩
  let j0 : Fin n := ⟨0, hn⟩
  have hnu : 0 < mu j0 := hmu j0
  have hsep : ∀ i, lambda i < mu j0 := fun i =>
    (hlow i).trans_le (hhigh j0)
  have hratioLim := tendsto_reflectedBiHeatLowRateSum_div_sinh_atTop
    p lambda hnu hlambda hsep
  have hevRatio : ∀ᶠ t in atTop,
      (∑ i, p i * Real.sinh (lambda i * t)) / Real.sinh (mu j0 * t) < q j0 :=
    (tendsto_order.mp hratioLim).2 (q j0) (hq j0)
  obtain ⟨t1, ht01, hratio⟩ : ∃ t1 : ℝ, t0 ≤ t1 ∧
      (∑ i, p i * Real.sinh (lambda i * t1)) /
          Real.sinh (mu j0 * t1) < q j0 := by
    have hev := (eventually_ge_atTop t0).and hevRatio
    exact hev.exists
  have ht1 : 0 < t1 := ht0.trans_le ht01
  have hsn : 0 < Real.sinh (mu j0 * t1) :=
    Real.sinh_pos_iff.mpr (mul_pos hnu ht1)
  have hlowLt : (∑ i, p i * Real.sinh (lambda i * t1)) <
      q j0 * Real.sinh (mu j0 * t1) :=
    (div_lt_iff₀ hsn).mp hratio
  have hhighSum : q j0 * Real.sinh (mu j0 * t1) ≤
      ∑ j, q j * Real.sinh (mu j * t1) := by
    have hs := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => q j * Real.sinh (mu j * t1))
      (fun j _ => mul_nonneg (hq j).le
        (Real.sinh_pos_iff.mpr (mul_pos (hmu j) ht1)).le)
      (Finset.mem_univ j0)
    simpa using hs
  have hpos1 : 0 < reflectedBiHeatSeparatedSignReporter p lambda q mu t1 := by
    rw [reflectedBiHeatSeparatedSignReporter]
    linarith
  have hcont : ContinuousOn
      (reflectedBiHeatSeparatedSignReporter p lambda q mu) (Icc t0 t1) := by
    have hc : Continuous
        (reflectedBiHeatSeparatedSignReporter p lambda q mu) := by
      unfold reflectedBiHeatSeparatedSignReporter
      fun_prop
    exact hc.continuousOn
  have hmem : (0 : ℝ) ∈ Icc
      (reflectedBiHeatSeparatedSignReporter p lambda q mu t0)
      (reflectedBiHeatSeparatedSignReporter p lambda q mu t1) :=
    ⟨hneg0.le, hpos1.le⟩
  rcases intermediate_value_Icc ht01 hcont hmem with ⟨t, ht, hzero⟩
  exact ⟨t, ht0.trans_le ht.1, hzero⟩

/-- Complete separated-sign finite-rate classification: one first-derivative inequality is exact. -/
theorem reflectedBiHeatSeparatedSignWallSelective_iff
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hp : ∀ i, 0 < p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa)
    (hq : ∀ j, 0 < q j)
    (hhigh : ∀ j, kappa ≤ mu j) :
    0 ≤ reflectedBiHeatSeparatedSignWallDerivative p lambda q mu ↔
      ∀ t : ℝ,
        reflectedBiHeatSeparatedSignReporter p lambda q mu t = 0 ↔ t = 0 := by
  constructor
  · intro hderiv t
    constructor
    · intro hzero
      by_contra ht
      rcases lt_or_gt_of_ne ht with htneg | htpos
      · have hpos := reflectedBiHeatSeparatedSignReporter_pos hm p lambda q mu
          hkappa (neg_pos.mpr htneg) hp hlambda hlow hq hhigh hderiv
        have hnegzero : reflectedBiHeatSeparatedSignReporter
            p lambda q mu (-t) = 0 := by
          rw [reflectedBiHeatSeparatedSignReporter_neg, hzero, neg_zero]
        exact hpos.ne' hnegzero
      · have hpos := reflectedBiHeatSeparatedSignReporter_pos hm p lambda q mu
          hkappa htpos hp hlambda hlow hq hhigh hderiv
        exact hpos.ne' hzero
    · rintro rfl
      simp [reflectedBiHeatSeparatedSignReporter]
  · intro hselect
    by_contra hnot
    have hderiv : reflectedBiHeatSeparatedSignWallDerivative p lambda q mu < 0 :=
      lt_of_not_ge hnot
    rcases
        exists_pos_reflectedBiHeatSeparatedSignReporter_eq_zero_of_derivative_neg
          hn p lambda q mu hkappa hlambda hlow hq hhigh hderiv with
      ⟨t, ht, hzero⟩
    exact ht.ne' ((hselect t).mp hzero)

/-- Physical finite separated-sign packet at arbitrary real-power apertures. -/
def reflectedBiHeatSeparatedSignApertureGap {m n : ℕ}
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ)
    (x : ℝ) (rho : XiDivisorSupport) : ℝ :=
  -(∑ i, p i * x ^ (lambda i / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda i) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda i) ^ 2)) +
    ∑ j, q j * x ^ (mu j / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu j) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ mu j) ^ 2)

/-- Exact physical factorization for an arbitrary finite separated-sign packet. -/
theorem reflectedBiHeatSeparatedSignApertureGap_eq_reporter
    {m n : ℕ} (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ)
    {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatSeparatedSignApertureGap p lambda q mu x rho =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        reflectedBiHeatSeparatedSignReporter p lambda q mu
          (Real.log x * ((rho : ℂ).re - 1 / 2)) := by
  have hlow :
      (∑ i, p i * x ^ (lambda i / 2) *
        (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda i) ^ 2 -
          reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda i) ^ 2)) =
      ∑ i, p i *
        (2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
          Real.sinh (lambda i *
            (Real.log x * ((rho : ℂ).re - 1 / 2)))) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh
      (lambda i) hx rho
    calc
      p i * x ^ (lambda i / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda i) ^ 2 -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda i) ^ 2) =
        p i * (x ^ (lambda i / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda i) ^ 2 -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda i) ^ 2)) := by ring
      _ = _ := by rw [hi]
  have hhigh :
      (∑ j, q j * x ^ (mu j / 2) *
        (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu j) ^ 2 -
          reflectedBiHeatRightLeadingJetNorm rho (x ^ mu j) ^ 2)) =
      ∑ j, q j *
        (2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
          Real.sinh (mu j *
            (Real.log x * ((rho : ℂ).re - 1 / 2)))) := by
    apply Finset.sum_congr rfl
    intro j _
    have hj := reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh
      (mu j) hx rho
    calc
      q j * x ^ (mu j / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu j) ^ 2 -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ mu j) ^ 2) =
        q j * (x ^ (mu j / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu j) ^ 2 -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ mu j) ^ 2)) := by ring
      _ = _ := by rw [hj]
  rw [reflectedBiHeatSeparatedSignApertureGap,
    reflectedBiHeatSeparatedSignReporter, hlow, hhigh]
  let C : ℝ := 2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2
  change
    -(∑ i, p i * (C * Real.sinh (lambda i *
      (Real.log x * ((rho : ℂ).re - 1 / 2))))) +
      ∑ j, q j * (C * Real.sinh (mu j *
        (Real.log x * ((rho : ℂ).re - 1 / 2)))) =
    C * (-(∑ i, p i * Real.sinh (lambda i *
      (Real.log x * ((rho : ℂ).re - 1 / 2)))) +
      ∑ j, q j * Real.sinh (mu j *
        (Real.log x * ((rho : ℂ).re - 1 / 2))))
  simp_rw [show ∀ r s : ℝ, r * (C * s) = C * (r * s) by intro r s; ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Every separated-sign packet in the exact cone balances physically only on the wall. -/
theorem reflectedBiHeatSeparatedSignApertureGap_eq_zero_iff
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hp : ∀ i, 0 < p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa)
    (hq : ∀ j, 0 < q j)
    (hhigh : ∀ j, kappa ≤ mu j)
    (hderiv : 0 ≤ reflectedBiHeatSeparatedSignWallDerivative p lambda q mu)
    {x : ℝ} (hx : 1 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatSeparatedSignApertureGap p lambda q mu x rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatSeparatedSignApertureGap_eq_reporter
    p lambda q mu (lt_trans zero_lt_one hx) rho]
  have hcoef :
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)))
  have hselect :=
    (reflectedBiHeatSeparatedSignWallSelective_iff hm hn p lambda q mu
      hkappa hp hlambda hlow hq hhigh).mp hderiv
  constructor
  · intro hzero
    have hreport : reflectedBiHeatSeparatedSignReporter p lambda q mu
        (Real.log x * ((rho : ℂ).re - 1 / 2)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcoef
    have hu := (hselect
      (Real.log x * ((rho : ℂ).re - 1 / 2))).mp hreport
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsub : (rho : ℂ).re - 1 / 2 = 0 :=
      (mul_eq_zero.mp hu).resolve_left hlog.ne'
    exact sub_eq_zero.mp hsub
  · intro hre
    rw [hre, sub_self, mul_zero]
    simp [reflectedBiHeatSeparatedSignReporter]

/-- Every finite separated-sign packet in the exact cone is an RH-equivalent receiver. -/
theorem riemannHypothesis_iff_reflectedBiHeatSeparatedSignApertureGap_eq_zero
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p lambda : Fin m → ℝ) (q mu : Fin n → ℝ)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hp : ∀ i, 0 < p i) (hlambda : ∀ i, 0 < lambda i)
    (hlow : ∀ i, lambda i < kappa)
    (hq : ∀ j, 0 < q j)
    (hhigh : ∀ j, kappa ≤ mu j)
    (hderiv : 0 ≤ reflectedBiHeatSeparatedSignWallDerivative p lambda q mu)
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatSeparatedSignApertureGap p lambda q mu x rho = 0 := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatSeparatedSignApertureGap_eq_zero_iff
      hm hn p lambda q mu hkappa hp hlambda hlow hq hhigh hderiv hx rho).mpr
        (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatSeparatedSignApertureGap_eq_zero_iff
        hm hn p lambda q mu hkappa hp hlambda hlow hq hhigh hderiv hx rho).mp
          (h rho)

end

end RHTower
