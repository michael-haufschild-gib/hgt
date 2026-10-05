import GaloisForLFunctions.RHTower.CausalMobiusThetaTransitionClock
import GaloisForLFunctions.RHTower.CausalMobiusThetaMovingCusp
import Mathlib.NumberTheory.AbelSummation

/-!
# The causal Möbius–theta tail as a boundary commutator, and its Abel form

* **(1)** For `t ≥ 1`, `B(t) = −[P₊, Σ_n μ(n) T_n] k (−log t)` with `T_n f(x) = n^{−1/2} f(x + log n)`
  and `P₊ f = 1_{x>0} f`;
* the finite Euler-prime filters `Σ_{d ∣ P_Y} μ(d) T_d` (the literal prime deletion,
  `thetaPrimeDeletion_eq_sum_divisors`) converge pointwise on the positive ray to (1);
* **(6)** `B(t) = −M(t) t^{−1/2} k(0) − ∫_t^∞ M(u) u^{−3/2} [k'(log(u/t)) − k(log(u/t))/2] du`;
* a bound `|M(u)| ≤ C u^{1/2+δ}` gives `|B(t)| ≤ C t^δ (k(0) + ∫_0^∞ e^{δv}(|k'(v)| + k(v)/2) dv)`,
  hence RH ⟹ (2) through the half-power Mertens bound;
* in **(7)**, `B^{(S)}(u) = O(u)` for `0 < u < 1`;
* **(4)** `ζ(w+1/2)(F(w) + K(w) + E(w)) = K(w)` for the meromorphic continuation `F` of the
  boundary transform (away from the zeros of `ζ(w+1/2)`);
* the sizes in **(13)–(14)**: `Σ_r g(r/N) = O_A(N^{−A})` and `g(1/N)/√N = O(N^{−5/2})`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## (1) as a boundary commutator -/

/-- `(Σ_n μ(n) T_n f)(x) = Σ_n μ(n) n^{−1/2} f(x + log n)`. -/
def mobiusShiftSum (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * f (x + Real.log n)

/-- The positive-ray cut `P₊ f = 1_{x>0} f`. -/
def positiveCut (f : ℝ → ℝ) : ℝ → ℝ := Set.indicator (Ioi 0) f

/-- **(1) as a commutator.** For `t ≥ 1`, `B(t) = −[P₊, Σ_n μ(n) T_n] k (−log t)`. -/
theorem causalMobiusThetaTail_eq_neg_commutator {t : ℝ} (ht : 1 ≤ t) :
    causalMobiusThetaTail t = -(positiveCut (mobiusShiftSum thetaCuspFullSource) (-Real.log t) -
      mobiusShiftSum (positiveCut thetaCuspFullSource) (-Real.log t)) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hcut : positiveCut (mobiusShiftSum thetaCuspFullSource) (-Real.log t) = 0 :=
    Set.indicator_of_notMem (by simp [Real.log_nonneg ht]) _
  rw [hcut, zero_sub, neg_neg, causalMobiusThetaTail, mobiusShiftSum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [causalMobiusThetaTerm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : -Real.log t + Real.log n = Real.log (n / t) := by
    rw [Real.log_div hnR.ne' ht0.ne']; ring
  rw [causalMobiusThetaTerm, positiveCut, hlog]
  by_cases htn : t < n
  · rw [Set.indicator_of_mem (show t ∈ Ioo 0 (n : ℝ) from ⟨ht0, htn⟩),
      Set.indicator_of_mem (show Real.log (n / t) ∈ Ioi (0 : ℝ) from
        Real.log_pos ((one_lt_div ht0).2 htn))]
  · rw [Set.indicator_of_notMem (fun h => htn h.2), Set.indicator_of_notMem, mul_zero]
    simp only [mem_Ioi, not_lt]
    exact Real.log_nonpos (by positivity) ((div_le_one ht0).2 (not_lt.1 htn))

/-- **The finite Euler-prime filters converge pointwise to (1).** The divisor sum over the
primorial `P_Y` (the positive-ray part of the literal prime deletion,
`thetaPrimeDeletion_neg_log_eq_add_port`) tends to `B(t)` as `Y → ∞`. -/
theorem tendsto_finitePrimeCausalPort (t : ℝ) :
    Tendsto (fun Y : ℕ => finitePrimeCausalPort Y t) atTop (𝓝 (causalMobiusThetaTail t)) := by
  have hsum := (summable_causalMobiusThetaTerm t).abs
  have htail : Tendsto (fun Y : ℕ => ∑' n : ℕ, if Y < n then |causalMobiusThetaTerm t n| else 0)
      atTop (𝓝 0) := by
    have h := tendsto_sum_nat_add fun n => |causalMobiusThetaTerm t n|
    have h1 : Tendsto (fun Y : ℕ => ∑' k : ℕ, |causalMobiusThetaTerm t (k + (Y + 1))|) atTop (𝓝 0) :=
      h.comp (tendsto_add_atTop_nat 1)
    refine h1.congr fun Y => ?_
    have hs : Summable fun n : ℕ => if Y < n then |causalMobiusThetaTerm t n| else 0 :=
      Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        (fun n => by split_ifs <;> simp [abs_nonneg]) hsum
    rw [← hs.sum_add_tsum_nat_add (Y + 1), Finset.sum_eq_zero fun n hn => by
      rw [if_neg (by simp only [Finset.mem_range] at hn; omega)], zero_add]
    refine tsum_congr fun k => ?_
    rw [if_pos (by omega)]
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun Y => ?_) htail)
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_causalMobiusThetaTail_sub_port_le Y t

/-! ## (6) The Abel form -/

theorem sum_Icc_moebius_eq_mertensReal (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, ((ArithmeticFunction.moebius k : ℤ) : ℝ) = mertensReal m := by
  rw [mertensReal, Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]

theorem causalProfile_self (t : ℝ) :
    causalProfile t t = t ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0 := by
  rw [causalProfile, sub_self]

/-- **(6)** `B(t) = −M(t) t^{−1/2} k(0) − ∫_t^∞ M(u) u^{−3/2} [k'(log(u/t)) − k(log(u/t))/2] du`. -/
theorem causalMobiusThetaTail_eq_mertens_abel {t : ℝ} (ht : 1 ≤ t) :
    causalMobiusThetaTail t = -(mertensReal ⌊t⌋₊ * t ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0) -
      ∫ u in Ioi t, mertensReal ⌊u⌋₊ * causalProfileDeriv t u := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  obtain ⟨D, hD0, hD⟩ := exists_causalProfile_bounds
  set c : ℕ → ℝ := fun k => ((ArithmeticFunction.moebius k : ℤ) : ℝ)
  set f := causalProfile t
  have hderiv : ∀ u, 0 < u → deriv f u = causalProfileDeriv t u := fun u hu =>
    (hasDerivAt_causalProfile t hu).deriv
  -- the integrand and its integrability on `(t, ∞)`
  set g : ℝ → ℝ := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k
  have hg_eq : ∀ u, t < u → g u = mertensReal ⌊u⌋₊ * causalProfileDeriv t u := fun u hu => by
    simp only [g, c]
    rw [sum_Icc_moebius_eq_mertensReal, hderiv u (ht0.trans hu), mul_comm]
  have hmeas : Measurable g :=
    (measurable_deriv f).mul
      ((measurable_from_nat (f := fun m : ℕ => ∑ k ∈ Finset.Icc 0 m, c k)).comp Nat.measurable_floor)
  have hg_le : ∀ u ∈ Ioi t, ‖g u‖ ≤ 3 * D * t ^ 2 * u ^ (-(5 / 2 : ℝ)) := by
    intro u hu
    have hu1 : 1 ≤ u := ht.trans (le_of_lt hu)
    have hu0 : 0 < u := ht0.trans hu
    rw [hg_eq u hu, Real.norm_eq_abs, abs_mul]
    have hM : |mertensReal ⌊u⌋₊| ≤ 2 * u := by
      refine (abs_mertensReal_le _).trans ?_
      have := Nat.floor_le hu0.le
      linarith
    have hf' := (hD t u ht0 (le_of_lt hu)).2
    calc |mertensReal ⌊u⌋₊| * |causalProfileDeriv t u| ≤ (2 * u) * (3 / 2 * D * t ^ 2 * u ^ (-(7 / 2 : ℝ))) :=
          mul_le_mul hM hf' (abs_nonneg _) (by positivity)
      _ = 3 * D * t ^ 2 * (u ^ (1 : ℝ) * u ^ (-(7 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = 3 * D * t ^ 2 * u ^ (-(5 / 2 : ℝ)) := by
          rw [← Real.rpow_add hu0]; norm_num
  have hg_int : IntegrableOn g (Ioi t) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := -(5 / 2 : ℝ)) (by norm_num) ht0).const_mul
      (3 * D * t ^ 2))
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using hg_le u hu
  -- Abel summation on `[t, n]`
  have habel : ∀ n : ℕ, t ≤ n →
      ∑ k ∈ Finset.Ioc ⌊t⌋₊ n, f k * c k =
        f n * mertensReal n - f t * mertensReal ⌊t⌋₊ - ∫ u in t..n, g u := by
    intro n hn
    have hdiff : ∀ u ∈ Icc t (n : ℝ), DifferentiableAt ℝ f u := fun u hu =>
      (hasDerivAt_causalProfile t (ht0.trans_le hu.1)).differentiableAt
    have hint : IntegrableOn (deriv f) (Icc t (n : ℝ)) := by
      refine Measure.integrableOn_of_bounded (M := 3 / 2 * D * t ^ 2) (by simp)
        (measurable_deriv f).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have hu0 : 0 < u := ht0.trans_le hu.1
      have hu1 : 1 ≤ u := ht.trans hu.1
      rw [hderiv u hu0, Real.norm_eq_abs]
      refine (hD t u ht0 hu.1).2.trans ?_
      have : u ^ (-(7 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
      calc 3 / 2 * D * t ^ 2 * u ^ (-(7 / 2 : ℝ)) ≤ 3 / 2 * D * t ^ 2 * 1 := by gcongr
        _ = 3 / 2 * D * t ^ 2 := mul_one _
    have h := sum_mul_eq_sub_sub_integral_mul c ht0.le hn hdiff hint
    rw [Nat.floor_natCast, sum_Icc_moebius_eq_mertensReal, sum_Icc_moebius_eq_mertensReal,
      ← intervalIntegral.integral_of_le hn] at h
    exact h
  -- the partial sums are the causal partial sums
  have hpartial : ∀ n : ℕ, ⌊t⌋₊ ≤ n → ∑ k ∈ Finset.Ioc ⌊t⌋₊ n, f k * c k =
      ∑ k ∈ Finset.range (n + 1), causalMobiusThetaTerm t k := by
    intro n hn
    rw [← Finset.sum_subset (s₁ := Finset.Ioc ⌊t⌋₊ n) (s₂ := Finset.range (n + 1))
      (fun k hk => Finset.mem_range.2 (by simp only [Finset.mem_Ioc] at hk; omega))
      (fun k hk1 hk => by
        have hkn := Finset.mem_range.1 hk1
        have hkt : (k : ℝ) ≤ t := by
          simp only [Finset.mem_Ioc, not_and, not_le] at hk
          rcases Nat.lt_or_ge ⌊t⌋₊ k with h | h
          · have := hk h; omega
          · exact (Nat.cast_le.2 h).trans (Nat.floor_le ht0.le)
        rw [causalMobiusThetaTerm, Set.indicator_of_notMem (fun h => not_lt.2 hkt h.2)])]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : t < k := by
      have := (Finset.mem_Ioc.1 hk).1
      exact Nat.lt_of_floor_lt this
    rw [causalMobiusThetaTerm_eq_profile ht0 k hk']
    ring
  -- pass to the limit
  have hlimS : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), causalMobiusThetaTerm t k) atTop
      (𝓝 (causalMobiusThetaTail t)) :=
    ((summable_causalMobiusThetaTerm t).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hlimB : Tendsto (fun n : ℕ => f n * mertensReal n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 2 * D * t ^ 2 * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 * D * t ^ 2)
      rw [mul_zero] at h
      exact h
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop ⌈t⌉₊] with n hn
    have hnt : t ≤ n := (Nat.le_ceil t).trans (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) < n := ht0.trans_le hnt
    have hn1 : (1 : ℝ) ≤ n := ht.trans hnt
    rw [Real.norm_eq_abs, abs_mul]
    have hf := (hD t n ht0 hnt).1
    have hM : |mertensReal n| ≤ 2 * n := by have := abs_mertensReal_le n; linarith
    calc |f n| * |mertensReal n| ≤ (D * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ))) * (2 * n) :=
          mul_le_mul hf hM (abs_nonneg _) (by positivity)
      _ = 2 * D * t ^ 2 * ((n : ℝ) ^ (-(5 / 2 : ℝ)) * (n : ℝ) ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = 2 * D * t ^ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hn0]; norm_num
      _ ≤ 2 * D * t ^ 2 * (n : ℝ)⁻¹ := by
          gcongr
          rw [← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hlimI : Tendsto (fun n : ℕ => ∫ u in t..n, g u) atTop (𝓝 (∫ u in Ioi t, g u)) :=
    intervalIntegral_tendsto_integral_Ioi t hg_int tendsto_natCast_atTop_atTop
  have hlim := (hlimB.sub (tendsto_const_nhds (x := f t * mertensReal ⌊t⌋₊))).sub hlimI
  have heq : ∀ᶠ n : ℕ in atTop, f n * mertensReal n - f t * mertensReal ⌊t⌋₊ - ∫ u in t..n, g u =
      ∑ k ∈ Finset.range (n + 1), causalMobiusThetaTerm t k := by
    filter_upwards [eventually_ge_atTop ⌈t⌉₊] with n hn
    have hnt : t ≤ n := (Nat.le_ceil t).trans (by exact_mod_cast hn)
    rw [← habel n hnt, hpartial n (Nat.floor_le_of_le hnt)]
  have huniq := tendsto_nhds_unique (hlim.congr' heq) hlimS
  have hft : f t = t ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0 := causalProfile_self t
  rw [← huniq, hft, setIntegral_congr_fun measurableSet_Ioi fun u hu => hg_eq u hu]
  ring

/-! ## The `t^δ` bound from a Mertens bound -/

theorem abs_causalProfileDeriv_le {t u : ℝ} (hu : 0 < u) :
    |causalProfileDeriv t u| ≤ u ^ (-(3 / 2 : ℝ)) *
      (|deriv thetaCuspFullSource (Real.log u - Real.log t)| +
        thetaCuspFullSource (Real.log u - Real.log t) / 2) := by
  rw [causalProfileDeriv, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu _)]
  gcongr
  refine (abs_sub _ _).trans (le_of_eq ?_)
  rw [abs_div, abs_of_pos (thetaCuspFullSource_pos_all _), abs_two]

/-- The Laplace weight `∫₀^∞ e^{δv} (|k'(v)| + k(v)/2) dv`. -/
def causalAbelWeight (δ : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), Real.exp (δ * v) *
    (|deriv thetaCuspFullSource v| + thetaCuspFullSource v / 2)

theorem integrableOn_causalAbelWeight {δ : ℝ} (hδ : δ < 2) :
    IntegrableOn (fun v => Real.exp (δ * v) *
      (|deriv thetaCuspFullSource v| + thetaCuspFullSource v / 2)) (Ioi 0) := by
  obtain ⟨C0, hC00, hC0⟩ := exists_abs_thetaCuspFullSource_le 2
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_deriv_thetaCuspFullSource_le 2
  have hcont : Continuous fun v => Real.exp (δ * v) *
      (|deriv thetaCuspFullSource v| + thetaCuspFullSource v / 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_deriv_thetaCuspFullSource.abs.add (contDiff_thetaCuspFullSource.continuous.div_const _))
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := δ - 2) (by linarith) 0).const_mul (C1 + C0))
    hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 ≤ v := le_of_lt hv
  have hk := hC0 v
  have hk' := hC1 v
  rw [abs_of_nonneg hv0] at hk hk'
  have hkpos := thetaCuspFullSource_pos_all v
  rw [abs_of_pos hkpos] at hk
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have he : Real.exp (δ * v) * Real.exp (-(2 * v)) = Real.exp ((δ - 2) * v) := by
    rw [← Real.exp_add]; ring_nf
  calc Real.exp (δ * v) * (|deriv thetaCuspFullSource v| + thetaCuspFullSource v / 2) ≤
        Real.exp (δ * v) * (C1 * Real.exp (-(2 * v)) + C0 * Real.exp (-(2 * v))) := by
        gcongr; linarith
    _ = (C1 + C0) * Real.exp ((δ - 2) * v) := by rw [← he]; ring

/-- The substitution `u = t e^v` for the Abel integrand. -/
theorem abel_substitution_eq {C δ t : ℝ} (ht : 0 < t) (v : ℝ) :
    t * Real.exp v * (C * (t * Real.exp v) ^ (δ - 1) *
      (|deriv thetaCuspFullSource (Real.log (t * Real.exp v) - Real.log t)| +
        thetaCuspFullSource (Real.log (t * Real.exp v) - Real.log t) / 2)) =
      C * t ^ δ * (Real.exp (δ * v) *
        (|deriv thetaCuspFullSource v| + thetaCuspFullSource v / 2)) := by
  rw [Real.log_mul ht.ne' (Real.exp_pos v).ne', Real.log_exp, add_sub_cancel_left,
    Real.mul_rpow ht.le (Real.exp_pos v).le, ← Real.exp_mul]
  have : t * Real.exp v * (t ^ (δ - 1) * Real.exp (v * (δ - 1))) = t ^ δ * Real.exp (δ * v) := by
    rw [show t * Real.exp v * (t ^ (δ - 1) * Real.exp (v * (δ - 1))) =
      (t ^ (1 : ℝ) * t ^ (δ - 1)) * (Real.exp v * Real.exp (v * (δ - 1))) by rw [Real.rpow_one]; ring,
      ← Real.rpow_add ht, ← Real.exp_add]
    ring_nf
  calc t * Real.exp v * (C * (t ^ (δ - 1) * Real.exp (v * (δ - 1))) *
        (|deriv thetaCuspFullSource v| + thetaCuspFullSource v / 2)) =
      C * (t * Real.exp v * (t ^ (δ - 1) * Real.exp (v * (δ - 1)))) *
        (|deriv thetaCuspFullSource v| + thetaCuspFullSource v / 2) := by ring
    _ = _ := by rw [this]; ring

/-- **(6) ⟹ (2).** If `|M(u)| ≤ C u^{1/2+δ}` for `u ≥ 1` (`0 < δ < 1`), then
`|B(t)| ≤ C t^δ (k(0) + ∫₀^∞ e^{δv}(|k'(v)| + k(v)/2) dv)`. -/
theorem abs_causalMobiusThetaTail_le_of_mertens_bound {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hC : 0 ≤ C) (hM : ∀ u : ℝ, 1 ≤ u → |mertensReal ⌊u⌋₊| ≤ C * u ^ (1 / 2 + δ)) {t : ℝ}
    (ht : 1 ≤ t) :
    |causalMobiusThetaTail t| ≤ C * t ^ δ * (thetaCuspFullSource 0 + causalAbelWeight δ) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hk0 := thetaCuspFullSource_pos_all 0
  obtain ⟨C0, hC00, hC0⟩ := exists_abs_thetaCuspFullSource_le 2
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_deriv_thetaCuspFullSource_le 2
  set h : ℝ → ℝ := fun v => |deriv thetaCuspFullSource v| + thetaCuspFullSource v / 2 with hhdef
  have hh0 : ∀ v, 0 ≤ h v := fun v => by
    have := thetaCuspFullSource_pos_all v; simp only [h]; positivity
  have hhc : Continuous h :=
    continuous_deriv_thetaCuspFullSource.abs.add (contDiff_thetaCuspFullSource.continuous.div_const _)
  have hhle : ∀ v, 0 ≤ v → h v ≤ (C1 + C0) * Real.exp (-(2 * v)) := fun v hv => by
    have hk := hC0 v
    have hk' := hC1 v
    rw [abs_of_nonneg hv] at hk hk'
    rw [abs_of_pos (thetaCuspFullSource_pos_all v)] at hk
    simp only [h]
    nlinarith [Real.exp_pos (-(2 * v))]
  -- the boundary term
  have e1 : |mertensReal ⌊t⌋₊ * t ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0| ≤
      C * t ^ δ * thetaCuspFullSource 0 := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_pos hk0]
    calc |mertensReal ⌊t⌋₊| * t ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0 ≤
          C * t ^ (1 / 2 + δ) * t ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0 := by gcongr; exact hM t ht
      _ = C * t ^ δ * thetaCuspFullSource 0 := by
          rw [mul_assoc C, ← Real.rpow_add ht0]; ring_nf
  -- the majorant `φ(u) = C u^{δ−1} h(log u − log t)`
  set φ : ℝ → ℝ := fun u => C * u ^ (δ - 1) * h (Real.log u - Real.log t) with hφdef
  have hφ_cont : ContinuousOn φ (Ioi 0) := by
    refine ContinuousOn.mul (continuousOn_const.mul ?_) (hhc.comp_continuousOn ?_)
    · exact fun u hu => (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hu))).continuousWithinAt
    · exact (Real.continuousOn_log.mono fun u hu => ne_of_gt hu).sub continuousOn_const
  have hφ_le : ∀ u, t ≤ u → φ u ≤ C * (C1 + C0) * t ^ 2 * u ^ (δ - 3) := by
    intro u hu
    have hu0 : 0 < u := ht0.trans_le hu
    have hv : 0 ≤ Real.log u - Real.log t := sub_nonneg.2 (Real.log_le_log ht0 hu)
    have he : Real.exp (-(2 * (Real.log u - Real.log t))) = t ^ 2 * (u ^ 2)⁻¹ := by
      rw [show -(2 * (Real.log u - Real.log t)) = 2 * Real.log t - 2 * Real.log u by ring,
        Real.exp_sub, ← Real.log_rpow ht0, ← Real.log_rpow hu0, Real.exp_log (by positivity),
        Real.exp_log (by positivity)]
      norm_num
      ring
    have hpow : u ^ (δ - 1) * (u ^ 2)⁻¹ = u ^ (δ - 3) := by
      rw [show (δ - 3) = (δ - 1) + (-2 : ℝ) by ring, Real.rpow_add hu0, Real.rpow_neg hu0.le]
      norm_num
    calc φ u = C * u ^ (δ - 1) * h (Real.log u - Real.log t) := rfl
      _ ≤ C * u ^ (δ - 1) * ((C1 + C0) * Real.exp (-(2 * (Real.log u - Real.log t)))) := by
          gcongr; exact hhle _ hv
      _ = C * (C1 + C0) * t ^ 2 * (u ^ (δ - 1) * (u ^ 2)⁻¹) := by rw [he]; ring
      _ = C * (C1 + C0) * t ^ 2 * u ^ (δ - 3) := by rw [hpow]
  have hφ_nonneg : ∀ u, 0 < u → 0 ≤ φ u := fun u hu => by
    simp only [φ]; have := hh0 (Real.log u - Real.log t); positivity
  have hφ_int : IntegrableOn φ (Ioi t) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := δ - 3) (by linarith) ht0).const_mul
      (C * (C1 + C0) * t ^ 2)) ((hφ_cont.mono fun u hu => ht0.trans hu).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ_nonneg u (ht0.trans hu))]
    exact hφ_le u (le_of_lt hu)
  have hφ_eq : ∫ u in Ioi t, φ u = C * t ^ δ * causalAbelWeight δ := by
    have himg : (fun v => t * Real.exp v) '' Ici 0 ⊆ Ici t := by
      rintro _ ⟨v, hv, rfl⟩
      exact le_mul_of_one_le_right ht0.le (Real.one_le_exp hv)
    have himg' : (fun v => t * Real.exp v) '' Ioi 0 ⊆ Ioi 0 := by
      rintro _ ⟨v, -, rfl⟩
      exact mul_pos ht0 (Real.exp_pos v)
    have hφ_Ici : IntegrableOn φ (Ici t) := (integrableOn_Ici_iff_integrableOn_Ioi (f := φ) (b := t)).2 hφ_int
    have hsub := integral_deriv_smul_comp_Ioi (f := fun v => t * Real.exp v)
      (f' := fun v => t * Real.exp v) (g := φ) (a := 0)
      ((continuous_const.mul Real.continuous_exp).continuousOn)
      (Tendsto.const_mul_atTop ht0 Real.tendsto_exp_atTop)
      (fun v _ => ((Real.hasDerivAt_exp v).const_mul t).hasDerivWithinAt)
      (hφ_cont.mono himg') (hφ_Ici.mono_set himg)
      (by
        have hw := (integrableOn_causalAbelWeight (by linarith : δ < 2)).const_mul (C * t ^ δ)
        refine ((integrableOn_Ici_iff_integrableOn_Ioi (b := (0 : ℝ))).2 hw).congr_fun (fun v _ => ?_)
          measurableSet_Ici
        simp only [φ, h, Function.comp_apply, smul_eq_mul]
        rw [abel_substitution_eq ht0])
    simp only [Real.exp_zero, mul_one] at hsub
    rw [← hsub, causalAbelWeight, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [φ, h, Function.comp_apply, smul_eq_mul]
    exact abel_substitution_eq ht0 v
  -- the integral term
  have e2 : |∫ u in Ioi t, mertensReal ⌊u⌋₊ * causalProfileDeriv t u| ≤ C * t ^ δ * causalAbelWeight δ := by
    rw [← hφ_eq, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hφ_int ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := ht0.trans hu
    have hu1 : 1 ≤ u := ht.trans (le_of_lt hu)
    rw [Real.norm_eq_abs, abs_mul]
    calc |mertensReal ⌊u⌋₊| * |causalProfileDeriv t u| ≤
          C * u ^ (1 / 2 + δ) * (u ^ (-(3 / 2 : ℝ)) * h (Real.log u - Real.log t)) :=
          mul_le_mul (hM u hu1) (abs_causalProfileDeriv_le hu0) (abs_nonneg _) (by positivity)
      _ = C * (u ^ (1 / 2 + δ) * u ^ (-(3 / 2 : ℝ))) * h (Real.log u - Real.log t) := by ring
      _ = φ u := by
          simp only [φ]
          rw [← Real.rpow_add hu0]
          ring_nf
  rw [causalMobiusThetaTail_eq_mertens_abel ht]
  calc |-(mertensReal ⌊t⌋₊ * t ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0) -
        ∫ u in Ioi t, mertensReal ⌊u⌋₊ * causalProfileDeriv t u|
      ≤ |mertensReal ⌊t⌋₊ * t ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0| +
        |∫ u in Ioi t, mertensReal ⌊u⌋₊ * causalProfileDeriv t u| := by
        refine (abs_sub _ _).trans (le_of_eq ?_); rw [abs_neg]
    _ ≤ C * t ^ δ * thetaCuspFullSource 0 + C * t ^ δ * causalAbelWeight δ := add_le_add e1 e2
    _ = C * t ^ δ * (thetaCuspFullSource 0 + causalAbelWeight δ) := by ring

theorem causalAbelWeight_nonneg (δ : ℝ) : 0 ≤ causalAbelWeight δ :=
  setIntegral_nonneg measurableSet_Ioi fun v _ => by
    have := thetaCuspFullSource_pos_all v; positivity

/-- **RH ⟹ (2) along (6):** the Littlewood bound for `M` feeds the Abel form. -/
theorem causalMobiusThetaTail_subpower_of_riemannHypothesis_via_abel (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → |causalMobiusThetaTail t| ≤ C * t ^ ε := by
  intro ε hε
  set δ : ℝ := min ε (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  obtain ⟨CM, hCM0, hCM⟩ := riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH δ hδ
  set C : ℝ := CM * 2 ^ (1 / 2 + δ)
  have hC : 0 ≤ C := by positivity
  have hM : ∀ u : ℝ, 1 ≤ u → |mertensReal ⌊u⌋₊| ≤ C * u ^ (1 / 2 + δ) := by
    intro u hu
    have h := hCM ⌊u⌋₊
    rw [norm_mobiusMertensPartialSum_eq] at h
    have hfl : ((⌊u⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * u := by
      have := Nat.floor_le (zero_le_one.trans hu); linarith
    refine h.trans ?_
    calc CM * (((⌊u⌋₊ : ℕ) : ℝ) + 1) ^ (1 / 2 + δ) ≤ CM * (2 * u) ^ (1 / 2 + δ) := by
          gcongr
      _ = C * u ^ (1 / 2 + δ) := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
  refine ⟨C * (thetaCuspFullSource 0 + causalAbelWeight δ), fun t ht => ?_⟩
  have hk0 := thetaCuspFullSource_pos_all 0
  have hW := causalAbelWeight_nonneg δ
  refine (abs_causalMobiusThetaTail_le_of_mertens_bound hδ hδ1 hC hM ht).trans ?_
  have htδ : t ^ δ ≤ t ^ ε := Real.rpow_le_rpow_of_exponent_le ht hδε
  calc C * t ^ δ * (thetaCuspFullSource 0 + causalAbelWeight δ) ≤
        C * t ^ ε * (thetaCuspFullSource 0 + causalAbelWeight δ) := by gcongr
    _ = C * (thetaCuspFullSource 0 + causalAbelWeight δ) * t ^ ε := by ring

/-! ## (7) The prime-deleted tail below the unit scale -/

/-- In **(7)**, `B^{(S)}(u) = O(u)` for `0 < u < 1`, uniformly in the finite prime set. -/
theorem exists_abs_causalTailCoprime_le_of_lt_one : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (S : Finset ℕ) (u : ℝ), 0 < u → u < 1 → |causalTailCoprime S u| ≤ C * u := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_causalTailCoprime_le_sq
  refine ⟨C, hC0, fun S u hu hu1 => (hC S u hu).trans ?_⟩
  have : u ^ 2 ≤ u := by nlinarith
  exact mul_le_mul_of_nonneg_left this hC0

/-! ## (4) The multiplied boundary identity -/

/-- **(4)** For the continuation `F = K(1/ζ − 1) − E` of the boundary transform (which equals the
Mellin transform of `B` on `Re w > 1/2`, `causalTailMellin_eq_continuation`),
`ζ(w + 1/2) (F(w) + K(w) + E(w)) = K(w)` wherever `ζ(w + 1/2) ≠ 0`; here `K + E = H` is the
correction `causalTailCorrection`. -/
theorem riemannZeta_mul_causalFrameContinuation_add_correction {w : ℂ}
    (hζ : riemannZeta (w + 1 / 2) ≠ 0) :
    riemannZeta (w + 1 / 2) * (causalFrameContinuation w + causalTailCorrection w) =
      thetaHalfLaplace w := by
  have h : causalFrameContinuation w + causalTailCorrection w =
      thetaHalfLaplace w * (riemannZeta (w + 1 / 2))⁻¹ := by
    rw [causalFrameContinuation, causalFrameCorrection]; ring
  rw [h, mul_left_comm, mul_inv_cancel₀ hζ, mul_one]

/-- On `Re w > 1/2`, (4) holds for the Mellin transform of `B` itself. -/
theorem riemannZeta_mul_causalTailMellin_add_correction {w : ℂ} (hw : 1 / 2 < w.re) :
    riemannZeta (w + 1 / 2) * (causalTailMellin w + causalTailCorrection w) = thetaHalfLaplace w := by
  have hs : 1 ≤ (w + 1 / 2).re := by simp; linarith
  rw [causalTailMellin_eq_continuation hw]
  exact riemannZeta_mul_causalFrameContinuation_add_correction (riemannZeta_ne_zero_of_one_le_re hs)

/-! ## Sizes in (13)–(14) -/

/-- The lattice sum in **(13)** is Gaussian-small: `Σ_r g(r/N) = O_A(N^{−A})` for every `A`. -/
theorem exists_abs_tsum_thetaCuspSeed_div_le (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |∑' r : ℕ, thetaCuspSeed (r / N)| ≤ C * (N : ℝ) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le (A + 1)
  refine ⟨C, hC0, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR : (0 : ℝ) < N := by linarith
  rw [tsum_thetaCuspSeed_div_eq hN, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hk := hC (Real.log N)
  rw [abs_of_nonneg (Real.log_nonneg hN1)] at hk
  have he : Real.exp (-((A + 1) * Real.log N)) = (N : ℝ) ^ (-A) * (N : ℝ)⁻¹ := by
    rw [Real.rpow_def_of_pos hNR,
      show (N : ℝ)⁻¹ = Real.exp (-Real.log N) by rw [Real.exp_neg, Real.exp_log hNR], ← Real.exp_add]
    congr 1
    ring
  have hsq : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left hNR.le]; nlinarith
  calc Real.sqrt N * |thetaCuspFullSource (Real.log N)| ≤ N * (C * ((N : ℝ) ^ (-A) * (N : ℝ)⁻¹)) := by
        rw [← he]; exact mul_le_mul hsq hk (abs_nonneg _) hNR.le
    _ = C * (N : ℝ) ^ (-A) := by field_simp

/-- The zeroth wavelet moment `g(1/N)/√N` is `O(N^{−5/2})`. -/
theorem exists_abs_thetaCuspSeed_inv_div_sqrt_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |thetaCuspSeed (1 / N) / Real.sqrt N| ≤ C / ((N : ℝ) ^ 2 * Real.sqrt N) := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_abs_thetaCuspSeed_le_sq
  refine ⟨Cs, hCs0, fun N hN => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  rw [abs_div, abs_of_pos hs]
  calc |thetaCuspSeed (1 / N)| / Real.sqrt N ≤ Cs * (1 / N) ^ 2 / Real.sqrt N := by
        gcongr; exact hCs _
    _ = Cs / ((N : ℝ) ^ 2 * Real.sqrt N) := by field_simp

end

end RHTower
