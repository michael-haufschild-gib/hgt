import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The ambient arithmetic dilation sum is unbounded

The finite arithmetic-summation operator of the CCM lower-tail mechanism is

```text
(S_(a,N) q)(v) = sqrt v * sum_(1 <= n <= N) q(n v),   v >= a,
```

read as a map from `L²([a,∞), dv)` to `L²([a,∞), dv/v)`.  Its norm grows like `sqrt N`, so the
infinite sum has no bounded extension.  The obstruction is a *coherent* vector: a logarithmically
scaled window on which every one of the `N` dilates contributes with the same sign.

The corpus already owns the *reason* this does not settle the CCM estimate: for a compactly supported
`C²` source the leading exterior Fourier term produces the bounded sawtooth sine series rather than a
coherent packet (`SawtoothFourierSeries.lean`, `CCMEndpointFourierJet.lean`), and the two-mode
zero-integral source has a central correction of concentration-deficit order
(`CCMTwoModeDeficitScale.lean`).

* `coherentPacket` — the extremal vector `L^{-1/2} v^{-1/2}` on `[a, a e^L]`, of unit `L²(dv)` norm.
* `arithDilationSum_coherentPacket_window` — on the window `[a, aN]` the image is *constant*: this is
  where coherence enters, and it is the only step of the proof that uses the choice `L = 2 log N`.
* `half_mul_sq_sum_le_integral`, `two_mul_sq_sub_one_le_integral` — the lower bounds
  `‖S q‖² ≥ (1/2)(∑_{n≤N} n^{-1/2})² ≥ 2(√N - 1)²`.
* `exists_unit_arithDilationSum_ge` — hence no bound holds uniformly in `N`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

/-- The finite arithmetic dilation sum of the CCM lower-tail mechanism. -/
def arithDilationSum (N : ℕ) (q : ℝ → ℝ) (v : ℝ) : ℝ :=
  Real.sqrt v * ∑ n ∈ Finset.Icc 1 N, q ((n : ℝ) * v)

/-- The coherent logarithmic packet on `[a, a e^L]`, normalised in `L²(dv)`. -/
def coherentPacket (a L : ℝ) : ℝ → ℝ :=
  Set.indicator (Icc a (a * Real.exp L)) fun v => (Real.sqrt L)⁻¹ * (Real.sqrt v)⁻¹

theorem coherentPacket_apply {a L v : ℝ} (hv : v ∈ Icc a (a * Real.exp L)) :
    coherentPacket a L v = (Real.sqrt L)⁻¹ * (Real.sqrt v)⁻¹ :=
  Set.indicator_of_mem hv _

theorem coherentPacket_eq_zero {a L v : ℝ} (hv : a * Real.exp L < v) :
    coherentPacket a L v = 0 :=
  Set.indicator_of_notMem (fun hmem => absurd hmem.2 (not_le.mpr hv)) _

theorem measurable_coherentPacket (a L : ℝ) : Measurable (coherentPacket a L) := by
  refine Measurable.indicator ?_ measurableSet_Icc
  fun_prop

theorem abs_coherentPacket_le {a : ℝ} (ha : 0 < a) (L v : ℝ) :
    |coherentPacket a L v| ≤ (Real.sqrt L)⁻¹ * (Real.sqrt a)⁻¹ := by
  have hnn : 0 ≤ (Real.sqrt L)⁻¹ * (Real.sqrt a)⁻¹ := by positivity
  by_cases hmem : v ∈ Icc a (a * Real.exp L)
  · rw [coherentPacket_apply hmem, abs_of_nonneg]
    · have hapos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
      have hva : Real.sqrt a ≤ Real.sqrt v := Real.sqrt_le_sqrt hmem.1
      have hinv : (Real.sqrt v)⁻¹ ≤ (Real.sqrt a)⁻¹ := by gcongr
      have hLnn : 0 ≤ (Real.sqrt L)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left hinv hLnn
    · have h1 : 0 ≤ v := le_trans ha.le hmem.1
      positivity
  · rw [coherentPacket, Set.indicator_of_notMem hmem]
    simpa using hnn

/-- The `L²(dv)` norm of the packet is one. -/
theorem integral_Ioi_coherentPacket_sq {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    (∫ v in Ioi a, coherentPacket a L v ^ 2) = 1 := by
  have hb : a ≤ a * Real.exp L := by
    have : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp hL.le
    nlinarith
  have hsq : ∀ v : ℝ, coherentPacket a L v ^ 2
      = Set.indicator (Icc a (a * Real.exp L)) (fun v => L⁻¹ * v⁻¹) v := by
    intro v
    by_cases hmem : v ∈ Icc a (a * Real.exp L)
    · rw [coherentPacket_apply hmem, Set.indicator_of_mem hmem]
      have hv : 0 < v := lt_of_lt_of_le ha hmem.1
      rw [mul_pow, ← Real.sqrt_inv, ← Real.sqrt_inv, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity)]
    · rw [coherentPacket, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      norm_num
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => hsq v),
    MeasureTheory.setIntegral_indicator measurableSet_Icc]
  have hinter : Ioi a ∩ Icc a (a * Real.exp L) = Ioc a (a * Real.exp L) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.le, h.2⟩⟩
  rw [hinter, ← intervalIntegral.integral_of_le hb, intervalIntegral.integral_const_mul,
    integral_inv_of_pos ha (by nlinarith [Real.exp_pos L]),
    mul_div_cancel_left₀ _ ha.ne', Real.log_exp, inv_mul_cancel₀ hL.ne']

theorem measurable_arithDilationSum {q : ℝ → ℝ} (hq : Measurable q) (N : ℕ) :
    Measurable (arithDilationSum N q) := by
  unfold arithDilationSum
  refine Measurable.mul (Real.continuous_sqrt.measurable) ?_
  exact Finset.measurable_sum _ fun n _ => hq.comp (measurable_const_mul _)

/-- The image, after division by `v`, is the square of the plain dilation sum. -/
theorem arithDilationSum_sq_div {N : ℕ} {q : ℝ → ℝ} {v : ℝ} (hv : 0 < v) :
    arithDilationSum N q v ^ 2 / v = (∑ n ∈ Finset.Icc 1 N, q ((n : ℝ) * v)) ^ 2 := by
  rw [arithDilationSum, mul_pow, Real.sq_sqrt hv.le, mul_comm, mul_div_assoc,
    div_self hv.ne', mul_one]

theorem arithDilationSum_coherentPacket_eq_zero {a L : ℝ} (ha : 0 < a) {N : ℕ} {v : ℝ}
    (hv : a * Real.exp L < v) : arithDilationSum N (coherentPacket a L) v = 0 := by
  have hvpos : 0 < v := lt_of_le_of_lt (by positivity) hv
  rw [arithDilationSum]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun n hn => ?_)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have := (Finset.mem_Icc.mp hn).1
    exact_mod_cast this
  refine coherentPacket_eq_zero (lt_of_lt_of_le hv ?_)
  nlinarith

/-! ## Coherence on the window -/

theorem exp_two_mul_log {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (2 * Real.log (N : ℝ)) = (N : ℝ) * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [show (2 : ℝ) * Real.log (N : ℝ) = Real.log (N : ℝ) + Real.log (N : ℝ) from by ring,
    Real.exp_add, Real.exp_log hNpos]

/-- **The coherent step.**  On the window `[a, aN]` every one of the `N` dilates lands inside the
support, and the `v`-dependence cancels exactly: the image is constant.  This is the only place the
choice `L = 2 log N` is used. -/
theorem arithDilationSum_coherentPacket_window {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 1 ≤ N)
    {v : ℝ} (hv : v ∈ Icc a (a * (N : ℝ))) :
    arithDilationSum N (coherentPacket a (2 * Real.log (N : ℝ))) v
      = (Real.sqrt (2 * Real.log (N : ℝ)))⁻¹ * ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hvpos : 0 < v := lt_of_lt_of_le ha hv.1
  have hsqv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hvpos
  have hsupp : a * Real.exp (2 * Real.log (N : ℝ)) = a * (N : ℝ) * (N : ℝ) := by
    rw [exp_two_mul_log hN]; ring
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      coherentPacket a (2 * Real.log (N : ℝ)) ((n : ℝ) * v)
        = (Real.sqrt (2 * Real.log (N : ℝ)))⁻¹ * ((Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt v)⁻¹) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have hmem : (n : ℝ) * v ∈ Icc a (a * Real.exp (2 * Real.log (N : ℝ))) := by
      rw [hsupp]
      refine ⟨?_, ?_⟩
      · calc a ≤ v := hv.1
          _ = 1 * v := by ring
          _ ≤ (n : ℝ) * v := mul_le_mul_of_nonneg_right hn1' hvpos.le
      · calc (n : ℝ) * v ≤ (N : ℝ) * v := mul_le_mul_of_nonneg_right hnN' hvpos.le
          _ ≤ (N : ℝ) * (a * (N : ℝ)) := mul_le_mul_of_nonneg_left hv.2 (by positivity)
          _ = a * (N : ℝ) * (N : ℝ) := by ring
    rw [coherentPacket_apply hmem,
      Real.sqrt_mul (show (0 : ℝ) ≤ (n : ℝ) from by positivity) v, mul_inv]
  rw [arithDilationSum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp

/-! ## Integrability of the image -/

theorem integrableOn_arithDilationSum_sq_div {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (N : ℕ) :
    IntegrableOn (fun v => arithDilationSum N (coherentPacket a L) v ^ 2 / v) (Ioi a) volume := by
  have hab : a ≤ a * Real.exp L := by
    have : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp hL.le
    nlinarith
  have hmeas : Measurable fun v => arithDilationSum N (coherentPacket a L) v ^ 2 / v :=
    ((measurable_arithDilationSum (measurable_coherentPacket a L) N).pow_const 2).div
      measurable_id
  -- on the bounded window the function is bounded
  have hbound : ∀ v ∈ Ioc a (a * Real.exp L),
      ‖arithDilationSum N (coherentPacket a L) v ^ 2 / v‖
        ≤ ((N : ℝ) * ((Real.sqrt L)⁻¹ * (Real.sqrt a)⁻¹)) ^ 2 := by
    intro v hv
    have hvpos : 0 < v := lt_trans ha hv.1
    rw [arithDilationSum_sq_div hvpos, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsum : |∑ n ∈ Finset.Icc 1 N, coherentPacket a L ((n : ℝ) * v)|
        ≤ (N : ℝ) * ((Real.sqrt L)⁻¹ * (Real.sqrt a)⁻¹) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ fun n _ =>
        abs_coherentPacket_le ha L ((n : ℝ) * v)) ?_
      simp [Nat.card_Icc, nsmul_eq_mul]
    have hnn : 0 ≤ (N : ℝ) * ((Real.sqrt L)⁻¹ * (Real.sqrt a)⁻¹) := by positivity
    calc (∑ n ∈ Finset.Icc 1 N, coherentPacket a L ((n : ℝ) * v)) ^ 2
        = |∑ n ∈ Finset.Icc 1 N, coherentPacket a L ((n : ℝ) * v)| ^ 2 := (sq_abs _).symm
      _ ≤ ((N : ℝ) * ((Real.sqrt L)⁻¹ * (Real.sqrt a)⁻¹)) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) hsum 2
  have hwin : IntegrableOn (fun v => arithDilationSum N (coherentPacket a L) v ^ 2 / v)
      (Ioc a (a * Real.exp L)) volume := by
    refine Measure.integrableOn_of_bounded (M := ((N : ℝ) * ((Real.sqrt L)⁻¹ * (Real.sqrt a)⁻¹)) ^ 2)
      ?_ hmeas.aestronglyMeasurable ?_
    · rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with v hv
      exact hbound v hv
  have htail : IntegrableOn (fun v => arithDilationSum N (coherentPacket a L) v ^ 2 / v)
      (Ioi (a * Real.exp L)) volume := by
    refine (integrableOn_zero (s := Ioi (a * Real.exp L)) (μ := volume)).congr_fun ?_
      measurableSet_Ioi
    intro v hv
    have hz : arithDilationSum N (coherentPacket a L) v = 0 :=
      arithDilationSum_coherentPacket_eq_zero ha hv
    simp [hz]
  have := hwin.union htail
  rwa [Set.Ioc_union_Ioi_eq_Ioi hab] at this

/-! ## The lower bound -/

theorem half_mul_sq_sum_le_integral {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 2 ≤ N) :
    (1 / 2) * (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) ^ 2
      ≤ ∫ v in Ioi a, arithDilationSum N (coherentPacket a (2 * Real.log (N : ℝ))) v ^ 2 / v := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  set L : ℝ := 2 * Real.log (N : ℝ) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  set S : ℝ := ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹ with hSdef
  have haN : a ≤ a * (N : ℝ) := by nlinarith
  have hint := integrableOn_arithDilationSum_sq_div ha hLpos N
  -- the window integral
  have hwin : (∫ v in Ioc a (a * (N : ℝ)),
      arithDilationSum N (coherentPacket a L) v ^ 2 / v)
      = (1 / 2) * S ^ 2 := by
    have hcongr : ∀ v ∈ Ioc a (a * (N : ℝ)),
        arithDilationSum N (coherentPacket a L) v ^ 2 / v
          = ((Real.sqrt L)⁻¹ * S) ^ 2 * v⁻¹ := by
      intro v hv
      have hvpos : 0 < v := lt_trans ha hv.1
      rw [arithDilationSum_coherentPacket_window ha hN1 ⟨hv.1.le, hv.2⟩]
      rw [div_eq_mul_inv]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hcongr,
      ← intervalIntegral.integral_of_le haN, intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha (by nlinarith), mul_div_cancel_left₀ _ ha.ne', mul_pow]
    have hLsq : (Real.sqrt L)⁻¹ ^ 2 = L⁻¹ := by
      rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
    have hlogne : Real.log (N : ℝ) ≠ 0 := hlogpos.ne'
    rw [hLsq, hLdef]
    field_simp
  -- extend to the whole ray
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)]
      fun v => arithDilationSum N (coherentPacket a L) v ^ 2 / v := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
    have hvpos : 0 < v := lt_trans ha hv
    positivity
  have hsub : (Ioc a (a * (N : ℝ)) : Set ℝ) ≤ᵐ[volume] Ioi a := by
    refine Filter.Eventually.of_forall fun v => ?_
    intro hv
    exact hv.1
  have hmono := MeasureTheory.setIntegral_mono_set hint hnn hsub
  rw [hwin] at hmono
  exact hmono

/-! ## The harmonic half-power sum -/

theorem two_mul_sqrt_succ_sub_one_le_sum : ∀ N : ℕ,
    2 * (Real.sqrt ((N : ℝ) + 1) - 1) ≤ ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹ := by
  intro N
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have ht : Real.sqrt ((N : ℝ) + 1 + 1) ^ 2 = (N : ℝ) + 1 + 1 := Real.sq_sqrt (by positivity)
    have hspos : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have htpos : 0 < Real.sqrt ((N : ℝ) + 1 + 1) := Real.sqrt_pos.mpr (by positivity)
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have hkey : 2 * (Real.sqrt ((N : ℝ) + 1 + 1) - Real.sqrt ((N : ℝ) + 1))
        * Real.sqrt ((N : ℝ) + 1) ≤ 1 := by
      nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) + 1 + 1) - Real.sqrt ((N : ℝ) + 1))]
    have hinvc : (Real.sqrt ((N : ℝ) + 1))⁻¹ * Real.sqrt ((N : ℝ) + 1) = 1 :=
      inv_mul_cancel₀ hspos.ne'
    have hstep : 2 * (Real.sqrt ((N : ℝ) + 1 + 1) - 1)
        ≤ 2 * (Real.sqrt ((N : ℝ) + 1) - 1) + (Real.sqrt ((N : ℝ) + 1))⁻¹ := by
      nlinarith [hkey, hinvc, hspos]
    rw [hcast]
    calc 2 * (Real.sqrt ((N : ℝ) + 1 + 1) - 1)
        ≤ 2 * (Real.sqrt ((N : ℝ) + 1) - 1) + (Real.sqrt ((N : ℝ) + 1))⁻¹ := hstep
      _ ≤ (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) + (Real.sqrt ((N : ℝ) + 1))⁻¹ := by
          linarith [ih]

theorem two_mul_sqrt_sub_one_le_sum (N : ℕ) :
    2 * (Real.sqrt (N : ℝ) - 1) ≤ ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹ := by
  refine le_trans ?_ (two_mul_sqrt_succ_sub_one_le_sum N)
  have : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- **Equation (1).**  The squared norm of the image of the coherent packet is at least
`2(√N - 1)²`, so the operator norm is at least `√2(√N - 1)`. -/
theorem two_mul_sq_sub_one_le_integral {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 2 ≤ N) :
    2 * (Real.sqrt (N : ℝ) - 1) ^ 2
      ≤ ∫ v in Ioi a, arithDilationSum N (coherentPacket a (2 * Real.log (N : ℝ))) v ^ 2 / v := by
  refine le_trans ?_ (half_mul_sq_sum_le_integral ha hN)
  have hlow := two_mul_sqrt_sub_one_le_sum N
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (by norm_num) hN
  have h1 : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hNpos
  nlinarith [sq_nonneg (Real.sqrt (N : ℝ) - 1)]

/-- **Equation (2).**  No bound holds uniformly in `N`: for every constant there is a unit vector
whose arithmetic dilation sum has larger tail energy. -/
theorem exists_unit_arithDilationSum_ge {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ (N : ℕ) (q : ℝ → ℝ), 2 ≤ N ∧ (∫ v in Ioi a, q v ^ 2) = 1 ∧
      C ≤ ∫ v in Ioi a, arithDilationSum N q v ^ 2 / v := by
  set r : ℝ := 1 + Real.sqrt (max C 0 / 2) with hrdef
  have hrpos : 1 ≤ r := by
    rw [hrdef]
    have : 0 ≤ Real.sqrt (max C 0 / 2) := Real.sqrt_nonneg _
    linarith
  set N : ℕ := max 2 ⌈r ^ 2⌉₊ with hNdef
  have hN2 : 2 ≤ N := le_max_left _ _
  have hNr : r ^ 2 ≤ (N : ℝ) := by
    have h1 : r ^ 2 ≤ ((⌈r ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : (⌈r ^ 2⌉₊ : ℕ) ≤ N := by rw [hNdef]; exact le_max_right _ _
    have h3 : ((⌈r ^ 2⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hsqrtN : r ≤ Real.sqrt (N : ℝ) := by
    rw [show r = Real.sqrt (r ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hNr
  have hlogpos : 0 < 2 * Real.log (N : ℝ) := by
    have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    have := Real.log_pos (show (1 : ℝ) < (N : ℝ) by linarith)
    linarith
  refine ⟨N, coherentPacket a (2 * Real.log (N : ℝ)), hN2,
    integral_Ioi_coherentPacket_sq ha hlogpos, ?_⟩
  refine le_trans ?_ (two_mul_sq_sub_one_le_integral ha hN2)
  have hsq : Real.sqrt (max C 0 / 2) ^ 2 = max C 0 / 2 := Real.sq_sqrt (by positivity)
  have hnn : 0 ≤ Real.sqrt (max C 0 / 2) := Real.sqrt_nonneg _
  have hstep : Real.sqrt (max C 0 / 2) ≤ Real.sqrt (N : ℝ) - 1 := by
    have hr : r ≤ Real.sqrt (N : ℝ) := hsqrtN
    rw [hrdef] at hr
    linarith
  have hmono : Real.sqrt (max C 0 / 2) ^ 2 ≤ (Real.sqrt (N : ℝ) - 1) ^ 2 :=
    pow_le_pow_left₀ hnn hstep 2
  have hCle : C ≤ max C 0 := le_max_left _ _
  rw [hsq] at hmono
  linarith

/-! ## The norm form of the bound -/

theorem sum_inv_sqrt_nonneg (N : ℕ) : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹ :=
  Finset.sum_nonneg fun n _ => by positivity

/-- **Equation (1), first inequality.**  The operator norm of `S_(a,N)` is at least
`2^{-1/2} ∑_{n<=N} n^{-1/2}`, witnessed by the coherent packet. -/
theorem inv_sqrt_two_mul_sum_le_sqrt_integral {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 2 ≤ N) :
    (Real.sqrt 2)⁻¹ * (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹)
      ≤ Real.sqrt (∫ v in Ioi a,
          arithDilationSum N (coherentPacket a (2 * Real.log (N : ℝ))) v ^ 2 / v) := by
  have hS := sum_inv_sqrt_nonneg N
  have hstep := Real.sqrt_le_sqrt (half_mul_sq_sum_le_integral ha hN)
  refine le_trans (le_of_eq ?_) hstep
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ from by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hS, Real.sqrt_inv]

/-- **Equation (1), second inequality.**  Hence the norm is at least `sqrt 2 (sqrt N - 1)`. -/
theorem sqrt_two_mul_sqrt_sub_one_le_sqrt_integral {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt 2 * (Real.sqrt (N : ℝ) - 1)
      ≤ Real.sqrt (∫ v in Ioi a,
          arithDilationSum N (coherentPacket a (2 * Real.log (N : ℝ))) v ^ 2 / v) := by
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (by norm_num) hN
  have h1 : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hNpos
  have hstep := Real.sqrt_le_sqrt (two_mul_sq_sub_one_le_integral ha hN)
  refine le_trans (le_of_eq ?_) hstep
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith)]

end GaloisForLFunctions.RHTower

end
