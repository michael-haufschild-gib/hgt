import GaloisForLFunctions.RHTower.ThetaTailIntegralCalculus
import GaloisForLFunctions.RHTower.ThetaTwoEndedTailLaw

/-!
# The full tail germ of zero-division deformations

Let `k` be the full theta source, `h` its logarithmic seed and `G(x) = e^{9x/2 − π e^{2x}}`, so that
`h = G (4π² − 6π e^{-2x})` exactly and `k − h = O(e^{-2Lx} G)` for every `L`.  Expansions are
power series in `w = e^{-2x}`: `F ∼ b Σ a_n w^n` means `F − b Σ_{n<L} a_n w^n = O(w^L b)` for all
`L`; they add, multiply (change of base) and invert.

* Integration by parts gives `I G_q = G_{q+1}/(2π) + ((5/4 − q)/π) I G_{q+1}` for
  `G_q = w^q G`, hence explicit expansions of `I G_q` and an operator `𝓘` on expansions with
  `I F ∼ G · 𝓘 A` whenever `F ∼ G · A`; the tail integrals `I^m k` have leading coefficient
  `(2π)^{-m}` relative to `k`.
* For a selection of off-line quartets with divisor `P_L` and real `N` of degree `≤ D`, the
  partial-fraction source `u_N` has the real symbol `ρ` with
  `ρ · ∏(1 + β²X²) = ∏β² · X^{2D} N(−1/X²)`, i.e. `ρ(1/s) = N(−s²)/P_L(is)`.
* **Watson expansion.**  With `κ_j = ρ_{j+1}` and universal constants `c_{n,j}`,
  `u_N/k ∼ ρ₀ + Σ_{n≥0} a_n e^{-2(n+1)x}` with `a_n = κ_n/(2π)^{n+1} + Σ_{j<n} c_{n,j} κ_j`.
  The diagonal never vanishes, so the tail coefficients recover every `κ_j` recursively, and two
  directions whose quotients by `k` agree to all orders have the same symbol.
* **Causal kernel.**  `K(t) = Σ κ_j t^j/j!` converges on the whole line and
  `(ρ₀ + ∫₀^∞ K(t) e^{-st} dt) · P_L(is) = N(−s²)` for all large `s`: the `κ_j` are the Taylor
  coefficients of the causal kernel whose Laplace transform is the proper part of `r(−s²)`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## The Gaussian tail base -/

/-- The Gaussian base `G(x) = e^{9x/2 − π e^{2x}}`. -/
def gaussTailBase (x : ℝ) : ℝ := Real.exp (9 / 2 * x - Real.pi * Real.exp (2 * x))

theorem gaussTailBase_pos (x : ℝ) : 0 < gaussTailBase x := Real.exp_pos _

/-- `h = G · (4π² − 6π e^{-2x})`. -/
theorem thetaCuspLogSeed_eq_gaussTailBase (x : ℝ) :
    thetaCuspLogSeed x = gaussTailBase x * (4 * Real.pi ^ 2 - 6 * Real.pi * Real.exp (-(2 * x))) := by
  rw [thetaCuspLogSeed_eq, gaussTailBase, Real.exp_sub]
  have h1 : Real.exp (9 / 2 * x) = Real.exp (5 * x / 2) * Real.exp (2 * x) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (2 * x) * Real.exp (-(2 * x)) = 1 := by rw [← Real.exp_add]; simp
  rw [h1, Real.exp_neg (Real.pi * Real.exp (2 * x))]
  field_simp
  linear_combination 6 * h2

/-- The Gaussian base has the theta tail. -/
theorem thetaTypeTail_gaussTailBase : ThetaTypeTail gaussTailBase := by
  refine ⟨by unfold gaussTailBase; fun_prop, ⟨1, 9 / 2, 0, by norm_num, le_rfl,
    fun x _ => ⟨gaussTailBase_pos x, fun t ht => ?_⟩⟩, fun τ hτ => ?_⟩
  · unfold gaussTailBase
    rw [one_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hq : 1 + 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
    have e2 : Real.exp (2 * (x + t)) = Real.exp (2 * x) * Real.exp (2 * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [e2]
    have := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ Real.pi * Real.exp (2 * x))
    nlinarith
  · have hy0 : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).congr fun x => by
          simp only [Function.comp, id]
    have hA : Tendsto (fun x => 9 / 2 * (τ * Real.exp (-(2 * x))) -
        Real.pi * (Real.exp (2 * x) * (Real.exp (2 * (τ * Real.exp (-(2 * x)))) - 1))) atTop
        (𝓝 (-(2 * Real.pi * τ))) := by
      have := ((hy0.const_mul τ).const_mul (9 / 2)).sub ((tendsto_exp_mul_exp_sub_one τ).const_mul Real.pi)
      convert this using 2
      ring
    refine ((Real.continuous_exp.tendsto _).comp hA).congr fun x => ?_
    simp only [Function.comp, gaussTailBase]
    rw [← Real.exp_sub]
    congr 1
    have e2 : Real.exp (2 * (x + τ * Real.exp (-(2 * x)))) =
        Real.exp (2 * x) * Real.exp (2 * (τ * Real.exp (-(2 * x)))) := by
      rw [← Real.exp_add]; ring_nf
    rw [e2]
    ring

/-- `e^{-2qx} G = O(e^{-2qx} G)`. -/
theorem tailSmall_exp_mul_gaussTailBase (q : ℕ) :
    TailSmall gaussTailBase q fun x => Real.exp (-(2 * q * x)) * gaussTailBase x :=
  ⟨1, Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (gaussTailBase_pos x)), one_mul]⟩

/-- The source differs from its first atom by `O(e^{-2Lx} G)` for every `L`. -/
theorem tailSmall_source_sub_seed (L : ℕ) :
    TailSmall gaussTailBase L fun x => thetaCuspFullSource x - thetaCuspLogSeed x := by
  have h := thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero L 0
  simp only [iteratedDeriv_zero] at h
  refine ⟨4 * Real.pi ^ 2 / Real.pi ^ L, ?_⟩
  filter_upwards [h.eventually (Metric.ball_mem_nhds 0 one_pos), eventually_ge_atTop (0 : ℝ)]
    with x hx hx0
  rw [Real.dist_eq, sub_zero, thetaCuspSourceTerm_one] at hx
  have hh := thetaCuspLogSeed_pos hx0
  have hsc : 0 < thetaCuspSingleAtomReflectionScale 1 x := thetaTailScale_pos x
  rw [abs_mul, abs_div, abs_of_pos hh, abs_of_pos (pow_pos hsc L), ← mul_div_assoc,
    div_lt_one hh] at hx
  have hscale : thetaCuspSingleAtomReflectionScale 1 x ^ L =
      Real.pi ^ L * Real.exp (2 * L * x) := by
    simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
    rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  rw [hscale] at hx
  have hw : Real.exp (-(2 * L * x)) * Real.exp (2 * L * x) = 1 := by rw [← Real.exp_add]; simp
  have hle : thetaCuspLogSeed x ≤ 4 * Real.pi ^ 2 * gaussTailBase x := by
    rw [thetaCuspLogSeed_eq_gaussTailBase]
    have := gaussTailBase_pos x
    have : 0 ≤ 6 * Real.pi * Real.exp (-(2 * x)) := by positivity
    nlinarith
  have hπL : 0 < Real.pi ^ L := pow_pos Real.pi_pos L
  rw [Real.norm_eq_abs]
  calc |thetaCuspFullSource x - thetaCuspLogSeed x|
      = Real.exp (-(2 * L * x)) / Real.pi ^ L *
          (Real.pi ^ L * Real.exp (2 * L * x) * |thetaCuspFullSource x - thetaCuspLogSeed x|) := by
        field_simp
        linear_combination (-|thetaCuspFullSource x - thetaCuspLogSeed x|) * hw
    _ ≤ Real.exp (-(2 * L * x)) / Real.pi ^ L * thetaCuspLogSeed x :=
        mul_le_mul_of_nonneg_left hx.le (by positivity)
    _ ≤ Real.exp (-(2 * L * x)) / Real.pi ^ L * (4 * Real.pi ^ 2 * gaussTailBase x) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by ring

/-! ## Asymptotic expansions in `e^{-2x}` -/

/-- `Σ_{n<L} a_n e^{-2nx}`. -/
def truncEval (a : PowerSeries ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range L, PowerSeries.coeff n a * Real.exp (-(2 * x)) ^ n

theorem truncEval_eq_eval (a : PowerSeries ℝ) (L : ℕ) (x : ℝ) :
    truncEval a L x = (PowerSeries.trunc L a).eval (Real.exp (-(2 * x))) := by
  rw [truncEval, Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range]
  rfl

theorem truncEval_add (a b : PowerSeries ℝ) (L : ℕ) (x : ℝ) :
    truncEval (a + b) L x = truncEval a L x + truncEval b L x := by
  simp only [truncEval, map_add, add_mul, Finset.sum_add_distrib]

theorem truncEval_sub (a b : PowerSeries ℝ) (L : ℕ) (x : ℝ) :
    truncEval (a - b) L x = truncEval a L x - truncEval b L x := by
  simp only [truncEval, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem truncEval_C_mul (c : ℝ) (a : PowerSeries ℝ) (L : ℕ) (x : ℝ) :
    truncEval (PowerSeries.C c * a) L x = c * truncEval a L x := by
  simp only [truncEval, PowerSeries.coeff_C_mul, Finset.mul_sum, mul_assoc]

theorem truncEval_congr {a b : PowerSeries ℝ} {L : ℕ}
    (h : ∀ n < L, PowerSeries.coeff n a = PowerSeries.coeff n b) (x : ℝ) :
    truncEval a L x = truncEval b L x :=
  Finset.sum_congr rfl fun n hn => by rw [h n (Finset.mem_range.1 hn)]

theorem abs_truncEval_le (a : PowerSeries ℝ) (L : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |truncEval a L x| ≤ ∑ n ∈ Finset.range L, |PowerSeries.coeff n a| := by
  have hw1 : Real.exp (-(2 * x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (Real.exp_pos _).le hw1)

theorem abs_eval_le_of_coeff_eq_zero {D : Polynomial ℝ} {L : ℕ} (h : ∀ n < L, D.coeff n = 0)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    |D.eval w| ≤ (∑ n ∈ Finset.range (D.natDegree + 1), |D.coeff n|) * w ^ L := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  by_cases hn : n < L
  · rw [h n hn]; simp
  · rw [abs_mul, abs_pow, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw0 hw1 (not_lt.1 hn)) (abs_nonneg _)

theorem tailSmall_mul_eval {b : ℝ → ℝ} (hb : ∀ᶠ x in atTop, 0 ≤ b x) {D : Polynomial ℝ} {L : ℕ}
    (h : ∀ n < L, D.coeff n = 0) :
    TailSmall b L fun x => b x * D.eval (Real.exp (-(2 * x))) := by
  refine ⟨∑ n ∈ Finset.range (D.natDegree + 1), |D.coeff n|, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with x hbx hx
  have hw1 : Real.exp (-(2 * x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h1 := abs_eval_le_of_coeff_eq_zero h (Real.exp_pos _).le hw1
  rw [← Real.exp_nat_mul, show (L : ℝ) * -(2 * x) = -(2 * L * x) by ring] at h1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hbx]
  calc b x * |D.eval (Real.exp (-(2 * x)))| ≤
        b x * ((∑ n ∈ Finset.range (D.natDegree + 1), |D.coeff n|) * Real.exp (-(2 * L * x))) :=
        mul_le_mul_of_nonneg_left h1 hbx
    _ = _ := by ring

namespace TailSmall

variable {b b' : ℝ → ℝ} {L : ℕ} {g : ℝ → ℝ}

theorem of_le_base (h : TailSmall b L g) {K : ℝ} (hb : ∀ᶠ x in atTop, |b x| ≤ K * b' x) :
    TailSmall b' L g := by
  obtain ⟨C, hC⟩ := h
  refine ⟨|C| * K, ?_⟩
  filter_upwards [hC, hb] with x hx hbx
  calc ‖g x‖ ≤ C * Real.exp (-(2 * L * x)) * b x := hx
    _ ≤ |C| * Real.exp (-(2 * L * x)) * |b x| := by
        have := Real.exp_pos (-(2 * L * x))
        have h1 : C * b x ≤ |C| * |b x| := by rw [← abs_mul]; exact le_abs_self _
        nlinarith
    _ ≤ |C| * Real.exp (-(2 * L * x)) * (K * b' x) :=
        mul_le_mul_of_nonneg_left hbx (by positivity)
    _ = _ := by ring

theorem mul_bounded (h : TailSmall b L g) {φ : ℝ → ℝ} {K : ℝ} (hφ : ∀ᶠ x in atTop, |φ x| ≤ K) :
    TailSmall b L fun x => φ x * g x := by
  obtain ⟨C, hC⟩ := h
  refine ⟨K * C, ?_⟩
  filter_upwards [hC, hφ] with x hx hφx
  rw [Real.norm_eq_abs, abs_mul]
  rw [Real.norm_eq_abs] at hx
  calc |φ x| * |g x| ≤ K * (C * Real.exp (-(2 * L * x)) * b x) :=
        mul_le_mul hφx hx (abs_nonneg _) ((abs_nonneg _).trans hφx)
    _ = _ := by ring

end TailSmall

/-- `F ∼ b Σ a_n e^{-2nx}`: every truncation is exact to the next order. -/
def HasExpansion (F b : ℝ → ℝ) (a : PowerSeries ℝ) : Prop :=
  ∀ L, TailSmall b L fun x => F x - b x * truncEval a L x

namespace HasExpansion

variable {F F' b b' : ℝ → ℝ} {a c : PowerSeries ℝ}

theorem congr (h : HasExpansion F b a) (h' : ∀ᶠ x in atTop, F x = F' x) : HasExpansion F' b a :=
  fun L => (h L).congr (h'.mono fun x hx => by rw [hx])

theorem add (h : HasExpansion F b a) (h' : HasExpansion F' b c) :
    HasExpansion (fun x => F x + F' x) b (a + c) := fun L =>
  ((h L).add (h' L)).congr (Eventually.of_forall fun x => by rw [truncEval_add]; ring)

theorem sub (h : HasExpansion F b a) (h' : HasExpansion F' b c) :
    HasExpansion (fun x => F x - F' x) b (a - c) := fun L =>
  ((h L).sub (h' L)).congr (Eventually.of_forall fun x => by rw [truncEval_sub]; ring)

theorem const_mul (h : HasExpansion F b a) (r : ℝ) :
    HasExpansion (fun x => r * F x) b (PowerSeries.C r * a) := fun L =>
  ((h L).const_smul r).congr (Eventually.of_forall fun x => by
    rw [truncEval_C_mul, smul_eq_mul]; ring)

theorem tailSmall (h : HasExpansion F b a) : TailSmall b 0 F :=
  (h 0).congr (Eventually.of_forall fun x => by simp [truncEval])

theorem abs_le (h : HasExpansion F b a) :
    ∃ K, ∀ᶠ x in atTop, |F x| ≤ K * b x := by
  obtain ⟨C, hC⟩ := h.tailSmall
  exact ⟨C, by filter_upwards [hC] with x hx; simpa using hx⟩

theorem of_polynomial (hb : ∀ᶠ x in atTop, 0 ≤ b x) (p : Polynomial ℝ)
    (hF : ∀ᶠ x in atTop, F x = b x * p.eval (Real.exp (-(2 * x)))) :
    HasExpansion F b (p : PowerSeries ℝ) := by
  intro L
  have hD : ∀ n < L, (p - PowerSeries.trunc L (p : PowerSeries ℝ)).coeff n = 0 := fun n hn => by
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hn, Polynomial.coeff_coe, sub_self]
  refine (tailSmall_mul_eval hb hD).congr ?_
  filter_upwards [hF] with x hx
  rw [hx, truncEval_eq_eval, Polynomial.eval_sub]
  ring

theorem mul (h : HasExpansion F b a) (h' : HasExpansion b b' c) (hb' : ∀ᶠ x in atTop, 0 ≤ b' x) :
    HasExpansion F b' (a * c) := by
  intro L
  obtain ⟨K, hK⟩ := h'.abs_le
  have hD : ∀ n < L, (PowerSeries.trunc L a * PowerSeries.trunc L c -
      PowerSeries.trunc L (a * c)).coeff n = 0 := fun n hn => by
    have := congrArg (fun p => Polynomial.coeff p n) (PowerSeries.trunc_trunc_mul_trunc (n := L) a c)
    simp only [PowerSeries.coeff_trunc, if_pos hn, ← Polynomial.coe_mul, Polynomial.coeff_coe] at this
    rw [Polynomial.coeff_sub, this, PowerSeries.coeff_trunc, if_pos hn, sub_self]
  have h3 := tailSmall_mul_eval hb' hD
  have h1 := (h L).of_le_base hK
  have h2 := (h' L).mul_bounded (φ := truncEval a L) (K := ∑ n ∈ Finset.range L,
    |PowerSeries.coeff n a|) (eventually_ge_atTop 0 |>.mono fun x hx => abs_truncEval_le a L hx)
  refine ((h1.add h2).add h3).congr (Eventually.of_forall fun x => ?_)
  simp only [truncEval_eq_eval, Polynomial.eval_sub, Polynomial.eval_mul]
  ring

theorem inv (h : HasExpansion b b' c) (hc : PowerSeries.coeff 0 c ≠ 0) (hb : ∀ᶠ x in atTop, 0 < b x)
    (hb' : ∀ᶠ x in atTop, 0 < b' x) : HasExpansion b' b c⁻¹ := by
  have hc' : PowerSeries.constantCoeff c ≠ 0 := by
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  -- `b' ≤ (2/|c₀|) b` near `+∞`
  obtain ⟨C, hC⟩ := h 1
  have hw : ∀ᶠ x in atTop, |C| * Real.exp (-(2 * x)) ≤ |PowerSeries.coeff 0 c| / 2 := by
    have hy0 : Tendsto (fun x : ℝ => |C| * Real.exp (-(2 * x))) atTop (𝓝 0) := by
      have := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul |C|)
      rw [mul_zero] at this
      exact this.congr fun x => by simp only [Function.comp, id]
    exact hy0.eventually (ge_mem_nhds (by positivity))
  have hbb : ∀ᶠ x in atTop, |b' x| ≤ 2 / |PowerSeries.coeff 0 c| * b x := by
    filter_upwards [hC, hw, hb, hb'] with x hx hwx hbx hbx'
    simp only [truncEval, Finset.sum_range_one, pow_zero, mul_one, Nat.cast_one, mul_one,
      Real.norm_eq_abs] at hx
    have hc0 : 0 < |PowerSeries.coeff 0 c| := abs_pos.2 hc
    rw [abs_of_pos hbx', div_mul_eq_mul_div, le_div_iff₀ hc0]
    have h1 : |b' x * PowerSeries.coeff 0 c| ≤ |b x| + |b x - b' x * PowerSeries.coeff 0 c| := by
      have := abs_sub_abs_le_abs_sub (b' x * PowerSeries.coeff 0 c) (b x)
      rw [abs_sub_comm] at this; linarith [abs_nonneg (b x)]
    rw [abs_mul, abs_of_pos hbx', abs_of_pos hbx] at h1
    have h2 : |b x - b' x * PowerSeries.coeff 0 c| ≤ |C| * Real.exp (-(2 * x)) * b' x := by
      refine hx.trans ?_
      have := Real.exp_pos (-(2 * x))
      gcongr
      exact le_abs_self C
    have h3 := mul_le_mul_of_nonneg_right hwx hbx'.le
    nlinarith
  intro L
  have hD : ∀ n < L, (1 - PowerSeries.trunc L c * PowerSeries.trunc L c⁻¹).coeff n = 0 := fun n hn => by
    have := congrArg (fun p => Polynomial.coeff p n) (PowerSeries.trunc_trunc_mul_trunc (n := L) c c⁻¹)
    simp only [PowerSeries.coeff_trunc, if_pos hn, ← Polynomial.coe_mul, Polynomial.coeff_coe,
      PowerSeries.mul_inv_cancel c hc', PowerSeries.coeff_one] at this
    rw [Polynomial.coeff_sub, this, Polynomial.coeff_one]
    split_ifs <;> simp_all
  have h1 := ((h L).mul_bounded (φ := fun x => -truncEval c⁻¹ L x) (K := ∑ n ∈ Finset.range L,
    |PowerSeries.coeff n c⁻¹|) (eventually_ge_atTop 0 |>.mono fun x hx => by
      rw [abs_neg]; exact abs_truncEval_le _ L hx)).of_le_base hbb
  have h2 := (tailSmall_mul_eval (hb'.mono fun x hx => hx.le) hD).of_le_base hbb
  refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
  simp only [truncEval_eq_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one]
  ring

end HasExpansion

theorem HasExpansion.zero {b : ℝ → ℝ} : HasExpansion (fun _ => 0) b 0 := fun L =>
  TailSmall.zero.congr (Eventually.of_forall fun x => by simp [truncEval])

theorem HasExpansion.sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} {b : ℝ → ℝ}
    {a : ι → PowerSeries ℝ} (h : ∀ i ∈ s, HasExpansion (F i) b (a i)) :
    HasExpansion (fun x => ∑ i ∈ s, F i x) b (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact HasExpansion.zero.congr (Eventually.of_forall fun x => by simp)
  | insert i s hi ih =>
    have := (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    exact this.congr (Eventually.of_forall fun x => by rw [Finset.sum_insert hi])

/-! ## Tail integrals of the Gaussian base -/

/-- `G_q(x) = e^{-2qx} G(x) = e^{(9/2 − 2q)x − π e^{2x}}`. -/
def gaussPow (q : ℕ) (x : ℝ) : ℝ := Real.exp ((9 / 2 - 2 * q) * x - Real.pi * Real.exp (2 * x))

theorem gaussPow_eq (q : ℕ) (x : ℝ) :
    gaussPow q x = Real.exp (-(2 * q * x)) * gaussTailBase x := by
  rw [gaussPow, gaussTailBase, ← Real.exp_add]; ring_nf

theorem continuous_gaussPow (q : ℕ) : Continuous (gaussPow q) := by unfold gaussPow; fun_prop

theorem tailSmall_gaussPow (q : ℕ) : TailSmall gaussTailBase q (gaussPow q) :=
  (tailSmall_exp_mul_gaussTailBase q).congr (Eventually.of_forall fun x => (gaussPow_eq q x).symm)

theorem gaussPow_le_exp_neg {q : ℕ} {x : ℝ} (hx : 0 ≤ x) : gaussPow q x ≤ Real.exp (-x) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have hπ := Real.pi_gt_three
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le]

theorem tendsto_gaussPow (q : ℕ) : Tendsto (gaussPow q) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun x => (Real.exp_pos _).le)
    (eventually_ge_atTop 0 |>.mono fun x hx => gaussPow_le_exp_neg hx)
    Real.tendsto_exp_neg_atTop_nhds_zero

theorem hasDerivAt_gaussPow (q : ℕ) (x : ℝ) :
    HasDerivAt (gaussPow (q + 1)) ((5 / 2 - 2 * q) * gaussPow (q + 1) x - 2 * Real.pi * gaussPow q x)
      x := by
  have h1 := (hasDerivAt_id x).const_mul (9 / 2 - 2 * ((q + 1 : ℕ) : ℝ))
  have h2 := (((hasDerivAt_id x).const_mul (2 : ℝ)).exp).const_mul Real.pi
  have hd : HasDerivAt (fun y => (9 / 2 - 2 * ((q + 1 : ℕ) : ℝ)) * y - Real.pi * Real.exp (2 * y))
      ((9 / 2 - 2 * ((q + 1 : ℕ) : ℝ)) * 1 - Real.pi * (Real.exp (2 * id x) * (2 * 1))) x :=
    h1.sub h2
  refine (hd.exp).congr_deriv ?_
  have e : Real.exp ((9 / 2 - 2 * ((q + 1 : ℕ) : ℝ)) * x - Real.pi * Real.exp (2 * x)) *
      Real.exp (2 * x) = Real.exp ((9 / 2 - 2 * (q : ℝ)) * x - Real.pi * Real.exp (2 * x)) := by
    rw [← Real.exp_add]; push_cast; ring_nf
  unfold gaussPow
  rw [← e, id]
  push_cast
  ring

/-- **Integration by parts for the Gaussian base**:
`I G_q = G_{q+1}/(2π) + ((5/4 − q)/π) I G_{q+1}` near `+∞`. -/
theorem tailIntegral_gaussPow (q : ℕ) :
    ∀ᶠ x in atTop, tailIntegral (gaussPow q) x =
      gaussPow (q + 1) x / (2 * Real.pi) + (5 / 4 - q) / Real.pi * tailIntegral (gaussPow (q + 1)) x := by
  have hm : ∀ q, StronglyMeasurable (gaussPow q) := fun q => (continuous_gaussPow q).stronglyMeasurable
  filter_upwards [(tailSmall_gaussPow q).integrableOn thetaTypeTail_gaussTailBase (hm q),
    (tailSmall_gaussPow (q + 1)).integrableOn thetaTypeTail_gaussTailBase (hm (q + 1))]
    with x hq hq1
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := fun t => gaussPow (q + 1) (x + t))
    (f' := fun t => (5 / 2 - 2 * q) * gaussPow (q + 1) (x + t) - 2 * Real.pi * gaussPow q (x + t))
    ((continuous_gaussPow (q + 1)).comp (continuous_const.add continuous_id)).continuousWithinAt
    (fun t _ => ((hasDerivAt_gaussPow q (x + t)).comp t ((hasDerivAt_id t).const_add x)).congr_deriv
      (by simp))
    ((hq1.const_mul _).sub (hq.const_mul _))
    ((tendsto_gaussPow (q + 1)).comp (tendsto_atTop_add_const_left _ x tendsto_id))
  simp only [add_zero, zero_sub] at hFTC
  have hsplit : tailIntegral (gaussPow q) x = ((5 / 2 - 2 * q) * tailIntegral (gaussPow (q + 1)) x -
      ∫ t in Ioi (0 : ℝ), ((5 / 2 - 2 * q) * gaussPow (q + 1) (x + t) -
        2 * Real.pi * gaussPow q (x + t))) / (2 * Real.pi) := by
    rw [integral_sub (hq1.const_mul _) (hq.const_mul _), integral_const_mul, integral_const_mul]
    unfold tailIntegral
    field_simp
    ring
  rw [hsplit, hFTC]
  field_simp
  ring

/-- The expansion of `I G_q` relative to `G`: `Σ_{l≥0} s_{q,l} e^{-2(q+1+l)x}` with
`s_{q,l} = (2π)^{-1} ∏_{i<l} (5/4 − q − i)/π`. -/
def gaussSym (q : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => if q < n then (2 * Real.pi)⁻¹ *
    ∏ i ∈ Finset.range (n - q - 1), ((5 / 4 - (q + i : ℝ)) / Real.pi) else 0

theorem coeff_gaussSym_of_le {q n : ℕ} (h : n ≤ q) : PowerSeries.coeff n (gaussSym q) = 0 := by
  rw [gaussSym, PowerSeries.coeff_mk, if_neg (by omega)]

theorem coeff_gaussSym_succ (q : ℕ) :
    PowerSeries.coeff (q + 1) (gaussSym q) = (2 * Real.pi)⁻¹ := by
  rw [gaussSym, PowerSeries.coeff_mk, if_pos (by omega), show q + 1 - q - 1 = 0 by omega]
  simp

theorem gaussSym_eq (q : ℕ) :
    gaussSym q = PowerSeries.C (2 * Real.pi)⁻¹ * PowerSeries.X ^ (q + 1) +
      PowerSeries.C ((5 / 4 - q) / Real.pi) * gaussSym (q + 1) := by
  ext n
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases hn : q + 1 < n
  · rw [gaussSym, gaussSym, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_pos (by omega),
      if_pos hn, if_neg (by omega), mul_zero, zero_add,
      show n - q - 1 = (n - (q + 1) - 1) + 1 by omega, Finset.prod_range_succ']
    have hp : ∏ i ∈ Finset.range (n - (q + 1) - 1), (5 / 4 - ((q : ℝ) + ((i + 1 : ℕ) : ℝ))) / Real.pi =
        ∏ i ∈ Finset.range (n - (q + 1) - 1), (5 / 4 - (((q + 1 : ℕ) : ℝ) + i)) / Real.pi :=
      Finset.prod_congr rfl fun i _ => by push_cast; ring
    rw [hp]
    push_cast
    ring
  · by_cases hq : n = q + 1
    · subst hq
      rw [coeff_gaussSym_succ, if_pos rfl, coeff_gaussSym_of_le le_rfl]
      ring
    · rw [gaussSym, gaussSym, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_neg hq, if_neg hn,
        if_neg (by omega)]
      ring

theorem hasExpansion_gaussPow (q : ℕ) :
    HasExpansion (gaussPow q) gaussTailBase
      (PowerSeries.X ^ q : PowerSeries ℝ) := by
  have := HasExpansion.of_polynomial (F := gaussPow q) (b := gaussTailBase)
    (Eventually.of_forall fun x => (gaussTailBase_pos x).le) (Polynomial.X ^ q)
    (Eventually.of_forall fun x => by
      rw [gaussPow_eq, Polynomial.eval_pow, Polynomial.eval_X, ← Real.exp_nat_mul]
      ring_nf)
  simpa using this

/-- **Expansion of `I G_q`** relative to `G`. -/
theorem hasExpansion_tailIntegral_gaussPow (q : ℕ) :
    HasExpansion (tailIntegral (gaussPow q)) gaussTailBase (gaussSym q) := by
  have hG := thetaTypeTail_gaussTailBase
  have key : ∀ n q L, L ≤ q + 1 + n → TailSmall gaussTailBase L
      fun x => tailIntegral (gaussPow q) x - gaussTailBase x * truncEval (gaussSym q) L x := by
    intro n
    induction n with
    | zero =>
      intro q L hL
      have h1 := ((tailSmall_gaussPow q).tailIntegral hG (continuous_gaussPow q).stronglyMeasurable).mono
        hL hG.eventually_nonneg
      refine h1.congr (Eventually.of_forall fun x => ?_)
      rw [truncEval_congr (b := 0) (fun m hm => by rw [coeff_gaussSym_of_le (by omega)]; simp)]
      simp [truncEval]
    | succ n ih =>
      intro q L hL
      have h1 := (hasExpansion_gaussPow (q + 1)).const_mul (2 * Real.pi)⁻¹ L
      have h2 := (ih (q + 1) L (by omega)).const_smul ((5 / 4 - q) / Real.pi)
      refine (h1.add h2).congr ?_
      filter_upwards [tailIntegral_gaussPow q] with x hx
      simp only [smul_eq_mul]
      rw [hx, gaussSym_eq q, truncEval_add, truncEval_C_mul, truncEval_C_mul]
      ring
  exact fun L => key L q L (by omega)

/-- The operator induced by `I` on expansions relative to `G`:
`(𝓘 A)_n = Σ_{q<n} A_q s_{q, n−q−1}`. -/
def tailOp (A : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => ∑ q ∈ Finset.range n, PowerSeries.coeff q A * PowerSeries.coeff n (gaussSym q)

theorem coeff_tailOp_eq_sum (A : PowerSeries ℝ) {L n : ℕ} (hn : n < L + 1) :
    PowerSeries.coeff n (tailOp A) =
      PowerSeries.coeff n (∑ q ∈ Finset.range L, PowerSeries.C (PowerSeries.coeff q A) * gaussSym q) := by
  rw [tailOp, PowerSeries.coeff_mk, map_sum]
  simp only [PowerSeries.coeff_C_mul]
  rcases Nat.lt_or_ge n L with h | h
  · rw [← Finset.sum_range_add_sum_Ico _ (show n ≤ L by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico n L) fun q hq => by
      rw [coeff_gaussSym_of_le (by simp at hq; omega), mul_zero], add_zero]
  · rw [show n = L by omega]

/-- **Tail integrals of expansions**: `F ∼ G·A` implies `I F ∼ G·𝓘 A`. -/
theorem HasExpansion.tailIntegral {F : ℝ → ℝ} {A : PowerSeries ℝ} (hF : StronglyMeasurable F)
    (h : HasExpansion F gaussTailBase A) :
    HasExpansion (RHTower.tailIntegral F) gaussTailBase (tailOp A) := by
  have hG := thetaTypeTail_gaussTailBase
  intro L
  cases L with
  | zero =>
    exact (h.tailSmall.tailIntegral hG hF |>.mono (Nat.zero_le _) hG.eventually_nonneg).congr
      (Eventually.of_forall fun x => by simp [truncEval])
  | succ L =>
    have hR := h L
    have hRm : StronglyMeasurable fun x => F x - gaussTailBase x * truncEval A L x :=
      hF.sub ((hG.continuous.mul (by unfold truncEval; fun_prop)).stronglyMeasurable)
    have hIR := hR.tailIntegral hG hRm
    have hsum := HasExpansion.sum (Finset.range L) (fun q _ =>
      (hasExpansion_tailIntegral_gaussPow q).const_mul (PowerSeries.coeff q A)) (L + 1)
    refine (hsum.add hIR).congr ?_
    have hint : ∀ᶠ x in atTop, ∀ q ∈ Finset.range L,
        IntegrableOn (fun t => gaussPow q (x + t)) (Ioi 0) :=
      (Filter.eventually_all_finset _).2 fun q _ =>
        (tailSmall_gaussPow q).integrableOn hG (continuous_gaussPow q).stronglyMeasurable
    filter_upwards [hint, hR.integrableOn hG hRm] with x hx hxR
    have hpt : ∀ y, gaussTailBase y * truncEval A L y =
        ∑ q ∈ Finset.range L, PowerSeries.coeff q A * gaussPow q y := fun y => by
      rw [truncEval, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [gaussPow_eq, ← Real.exp_nat_mul]; ring_nf
    have hsplit : RHTower.tailIntegral F x = RHTower.tailIntegral
        (fun y => F y - gaussTailBase y * truncEval A L y) x +
          ∑ q ∈ Finset.range L, PowerSeries.coeff q A * RHTower.tailIntegral (gaussPow q) x := by
      unfold RHTower.tailIntegral
      have hFeq : ∀ t, F (x + t) = (F (x + t) - gaussTailBase (x + t) * truncEval A L (x + t)) +
          ∑ q ∈ Finset.range L, PowerSeries.coeff q A * gaussPow q (x + t) := fun t => by
        rw [hpt]; ring
      rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => hFeq t,
        integral_add hxR (integrable_finsetSum _ fun q hq => (hx q hq).const_mul _),
        integral_finsetSum _ fun q hq => (hx q hq).const_mul _]
      simp only [integral_const_mul]
    rw [hsplit, truncEval_congr (b := ∑ q ∈ Finset.range L,
      PowerSeries.C (PowerSeries.coeff q A) * gaussSym q) fun n hn => coeff_tailOp_eq_sum A hn]
    simp only [truncEval, map_sum, PowerSeries.coeff_C_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    ring

/-! ## Iterated tail integrals of the source -/

/-- The expansion `4π² − 6π e^{-2x}` of the source relative to `G`. -/
def sourceSym : PowerSeries ℝ := PowerSeries.C (4 * Real.pi ^ 2) - PowerSeries.C (6 * Real.pi) * PowerSeries.X

theorem coeff_zero_sourceSym : PowerSeries.coeff 0 sourceSym = 4 * Real.pi ^ 2 := by
  simp [sourceSym]

theorem hasExpansion_seed : HasExpansion thetaCuspLogSeed gaussTailBase sourceSym := by
  have := HasExpansion.of_polynomial (F := thetaCuspLogSeed) (b := gaussTailBase)
    (Eventually.of_forall fun x => (gaussTailBase_pos x).le)
    (Polynomial.C (4 * Real.pi ^ 2) - Polynomial.C (6 * Real.pi) * Polynomial.X)
    (Eventually.of_forall fun x => by
      rw [thetaCuspLogSeed_eq_gaussTailBase]; simp)
  simpa [sourceSym] using this

theorem hasExpansion_source : HasExpansion thetaCuspFullSource gaussTailBase sourceSym := fun L =>
  ((hasExpansion_seed L).add (tailSmall_source_sub_seed L)).congr
    (Eventually.of_forall fun x => by ring)

theorem stronglyMeasurable_iterate_tailIntegral_source (m : ℕ) :
    StronglyMeasurable (tailIntegral^[m] thetaCuspFullSource) := by
  induction m with
  | zero => exact contDiff_thetaCuspFullSource.continuous.stronglyMeasurable
  | succ m ih => rw [Function.iterate_succ']; exact stronglyMeasurable_tailIntegral ih

/-- `I^m k ∼ G · 𝓘^m(4π² − 6πX)`. -/
theorem hasExpansion_iterate_tailIntegral_source (m : ℕ) :
    HasExpansion (tailIntegral^[m] thetaCuspFullSource) gaussTailBase (tailOp^[m] sourceSym) := by
  induction m with
  | zero => exact hasExpansion_source
  | succ m ih =>
    rw [Function.iterate_succ', Function.iterate_succ']
    exact ih.tailIntegral (stronglyMeasurable_iterate_tailIntegral_source m)

theorem coeff_tailOp_of_le {A : PowerSeries ℝ} {m : ℕ} (hA : ∀ q < m, PowerSeries.coeff q A = 0)
    {n : ℕ} (hn : n ≤ m) : PowerSeries.coeff n (tailOp A) = 0 := by
  rw [tailOp, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun q hq => by rw [hA q (by simp at hq; omega), zero_mul]

theorem coeff_tailOp_succ {A : PowerSeries ℝ} {m : ℕ} (hA : ∀ q < m, PowerSeries.coeff q A = 0) :
    PowerSeries.coeff (m + 1) (tailOp A) = PowerSeries.coeff m A / (2 * Real.pi) := by
  rw [tailOp, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_eq_zero fun q hq => by
    rw [hA q (by simpa using hq), zero_mul], zero_add, coeff_gaussSym_succ, div_eq_mul_inv]

theorem coeff_iterate_tailOp_of_lt (m : ℕ) {n : ℕ} (hn : n < m) :
    PowerSeries.coeff n (tailOp^[m] sourceSym) = 0 := by
  induction m generalizing n with
  | zero => omega
  | succ m ih =>
    rw [Function.iterate_succ']
    exact coeff_tailOp_of_le (fun q hq => ih hq) (by omega)

theorem coeff_iterate_tailOp_self (m : ℕ) :
    PowerSeries.coeff m (tailOp^[m] sourceSym) = 4 * Real.pi ^ 2 / (2 * Real.pi) ^ m := by
  induction m with
  | zero => simp [coeff_zero_sourceSym]
  | succ m ih =>
    rw [Function.iterate_succ', Function.comp_apply,
      coeff_tailOp_succ (fun q hq => coeff_iterate_tailOp_of_lt m hq), ih, pow_succ]
    field_simp
    ring

/-! ## Real tail series of the partial-fraction sources -/

theorem tailIntegral_ofReal (F : ℝ → ℝ) (x : ℝ) :
    tailIntegral (fun y => (F y : ℂ)) x = ((tailIntegral F x : ℝ) : ℂ) :=
  integral_complex_ofReal

theorem iterate_tailIntegral_ofReal (F : ℝ → ℝ) (m : ℕ) (x : ℝ) :
    (tailIntegral^[m] fun y => (F y : ℂ)) x = ((tailIntegral^[m] F x : ℝ) : ℂ) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [show (tailIntegral^[m] fun y => (F y : ℂ)) = fun y => ((tailIntegral^[m] F y : ℝ) : ℂ) from
      funext ih]
    exact tailIntegral_ofReal _ x

theorem perm_map_conj_quadrantListOf (l : List ℂ) :
    ((quadrantListOf l).map (starRingEnd ℂ)).Perm (quadrantListOf l) := by
  induction l with
  | nil => simp [quadrantListOf]
  | cons α l ih =>
    simp only [quadrantListOf, List.map_append, List.map_replicate, Complex.conj_conj]
    exact List.perm_append_comm.append ih

theorem prod_map_conj_quadrantListOf {M : Type*} [CommMonoid M] (l : List ℂ) (g : ℂ → M) :
    ((quadrantListOf l).map fun β => g ((starRingEnd ℂ) β)).prod = ((quadrantListOf l).map g).prod := by
  rw [show (fun β => g ((starRingEnd ℂ) β)) = g ∘ starRingEnd ℂ from rfl, ← List.map_map]
  exact ((perm_map_conj_quadrantListOf l).map g).prod_eq

theorem evenRev_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (e : Polynomial R) :
    (evenRev n e).map φ = evenRev n (e.map φ) := by
  simp only [evenRev, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one, Polynomial.map_neg,
    Polynomial.map_one]

/-- The combination symbol of a real numerator over a quadrant selection is real. -/
theorem map_conj_combSymbol (l : List ℂ) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) :
    PowerSeries.map (starRingEnd ℂ) (combSymbol (quadrantListOf l) (N.map (algebraMap ℝ ℂ))) =
      combSymbol (quadrantListOf l) (N.map (algebraMap ℝ ℂ)) := by
  have hdeg : (N.map (algebraMap ℝ ℂ)).natDegree ≤ (quadrantListOf l).length :=
    (Polynomial.natDegree_map_le).trans hN
  have h := combSymbol_mul_symbolDen (quadrantListOf l) hdeg
  have hQ : PowerSeries.map (starRingEnd ℂ) (symbolDen (quadrantListOf l)) =
      symbolDen (quadrantListOf l) := by
    rw [symbolDen, map_list_prod, List.map_map, ← prod_map_conj_quadrantListOf l
      (fun β => 1 + PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2)]
    congr 2
    funext β
    simp [map_pow]
  have hc : (starRingEnd ℂ) ((quadrantListOf l).map fun β => β ^ 2).prod =
      ((quadrantListOf l).map fun β => β ^ 2).prod := by
    rw [map_list_prod, List.map_map, ← prod_map_conj_quadrantListOf l (fun β => β ^ 2)]
    congr 2
    funext β
    simp [map_pow]
  have hE : PowerSeries.map (starRingEnd ℂ)
      ((evenRev (quadrantListOf l).length (N.map (algebraMap ℝ ℂ)) : Polynomial ℂ) : PowerSeries ℂ) =
      (evenRev (quadrantListOf l).length (N.map (algebraMap ℝ ℂ)) : PowerSeries ℂ) := by
    ext n
    rw [PowerSeries.coeff_map, Polynomial.coeff_coe, ← evenRev_map, Polynomial.coeff_map]
    exact Complex.conj_ofReal _
  have h2 := congrArg (PowerSeries.map (starRingEnd ℂ)) h
  rw [map_mul, map_mul, hQ, PowerSeries.map_C, hc, hE, ← h] at h2
  have hQ0 : symbolDen (quadrantListOf l) ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    simp [symbolDen, map_list_prod] at this
  exact mul_right_cancel₀ hQ0 h2

/-- The real symbol `ρ` of `u_N`: `ρ(w) = N(−1/w²)/P_L(−1/w²)` expanded at `w = 0`. -/
def realCombSymbol (l : List ℂ) (N : Polynomial ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n =>
    (PowerSeries.coeff n (combSymbol (quadrantListOf l) (N.map (algebraMap ℝ ℂ)))).re

theorem coeff_combSymbol_eq_ofReal (l : List ℂ) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) (n : ℕ) :
    PowerSeries.coeff n (combSymbol (quadrantListOf l) (N.map (algebraMap ℝ ℂ))) =
      ((PowerSeries.coeff n (realCombSymbol l N) : ℝ) : ℂ) := by
  have h := congrArg (PowerSeries.coeff n) (map_conj_combSymbol l N hN)
  rw [PowerSeries.coeff_map] at h
  rw [realCombSymbol, PowerSeries.coeff_mk]
  exact (Complex.conj_eq_iff_re.1 h).symm

/-- **Characterization of the real symbol**: `ρ · ∏(1 + β²X²) = ∏β² · X^{2D} N(−1/X²)`. -/
theorem realCombSymbol_mul_symbolDen (l : List ℂ) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) :
    PowerSeries.map (algebraMap ℝ ℂ) (realCombSymbol l N) * symbolDen (quadrantListOf l) =
      PowerSeries.C (((quadrantListOf l).map fun β => β ^ 2).prod) *
        ((evenRev (quadrantListOf l).length (N.map (algebraMap ℝ ℂ)) : Polynomial ℂ) : PowerSeries ℂ) := by
  have : PowerSeries.map (algebraMap ℝ ℂ) (realCombSymbol l N) =
      combSymbol (quadrantListOf l) (N.map (algebraMap ℝ ℂ)) := by
    ext n
    rw [PowerSeries.coeff_map, coeff_combSymbol_eq_ofReal l N hN]
    rfl
  rw [this]
  exact combSymbol_mul_symbolDen _ ((Polynomial.natDegree_map_le).trans hN)

/-- **Tail series of `u_N`**: `u_N − Σ_{m<P} ρ_m I^m k = O(e^{-2Px} k)` for every `P`. -/
theorem tailSmall_rationalSource_sub (l : List ℂ) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) (P : ℕ) :
    TailSmall thetaCuspFullSource P fun x => rationalSource l N x -
      ∑ m ∈ Finset.range P, PowerSeries.coeff m (realCombSymbol l N) *
        tailIntegral^[m] thetaCuspFullSource x := by
  obtain ⟨C, hC⟩ := hasTailSeries_listComb thetaTypeTail_source (quadrantListOf l)
    (N.map (algebraMap ℝ ℂ)) P
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans hx)
  rw [Real.norm_eq_abs]
  congr 1
  rw [Complex.sub_re, rationalSource, listComb_congr (fun L y hy => thetaListDivision_eq_halfListDivision L y hy)
    _ _ hx0, tailSeries, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_combSymbol_eq_ofReal l N hN, iterate_tailIntegral_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-! ## The full tail germ of `u_N / k` -/

/-- The expansion `Σ_m ρ_m 𝓘^m(4π² − 6πX)` of `Σ ρ_m I^m k` relative to `G`. -/
def sourceSeries (ρ : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
    PowerSeries.coeff m ρ * PowerSeries.coeff n (tailOp^[m] sourceSym)

theorem coeff_sourceSeries_eq (ρ : PowerSeries ℝ) {L n : ℕ} (hn : n < L) :
    PowerSeries.coeff n (sourceSeries ρ) =
      ∑ m ∈ Finset.range L, PowerSeries.coeff m ρ * PowerSeries.coeff n (tailOp^[m] sourceSym) := by
  rw [sourceSeries, PowerSeries.coeff_mk, ← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ L by omega),
    Finset.sum_eq_zero (s := Finset.Ico (n + 1) L) fun m hm => by
      rw [coeff_iterate_tailOp_of_lt m (by simp at hm; omega), mul_zero], add_zero]

theorem hasExpansion_rationalSource_gauss (l : List ℂ) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) :
    HasExpansion (rationalSource l N) gaussTailBase (sourceSeries (realCombSymbol l N)) := by
  obtain ⟨K, hK⟩ := hasExpansion_source.abs_le
  intro L
  have h1 := (tailSmall_rationalSource_sub l N hN L).of_le_base hK
  have h2 := HasExpansion.sum (Finset.range L) (fun m _ =>
    (hasExpansion_iterate_tailIntegral_source m).const_mul
      (PowerSeries.coeff m (realCombSymbol l N))) L
  refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
  rw [truncEval_congr (a := sourceSeries (realCombSymbol l N)) (b := ∑ m ∈ Finset.range L,
    PowerSeries.C (PowerSeries.coeff m (realCombSymbol l N)) * tailOp^[m] sourceSym) fun n hn => by
      rw [coeff_sourceSeries_eq _ hn, map_sum]
      simp only [PowerSeries.coeff_C_mul]]
  ring

/-- **The full tail series of `u_N/k`** as a power series in `e^{-2x}`. -/
theorem hasExpansion_rationalSource (l : List ℂ) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) :
    HasExpansion (rationalSource l N) thetaCuspFullSource
      (sourceSeries (realCombSymbol l N) * sourceSym⁻¹) :=
  (hasExpansion_rationalSource_gauss l N hN).mul
    (hasExpansion_source.inv (by rw [coeff_zero_sourceSym]; positivity)
      (Eventually.of_forall thetaCuspFullSource_pos) (Eventually.of_forall gaussTailBase_pos))
    (Eventually.of_forall fun x => (thetaCuspFullSource_pos x).le)

theorem coeff_mul_congr_left {a a' c : PowerSeries ℝ} {n : ℕ}
    (h : ∀ i ≤ n, PowerSeries.coeff i a = PowerSeries.coeff i a') :
    PowerSeries.coeff n (a * c) = PowerSeries.coeff n (a' * c) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [h p.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega)]

/-- The universal coefficient table `E_{m,n} = [w^n] 𝓘^m(4π² − 6πX)/(4π² − 6πX)`. -/
def tailTable (m n : ℕ) : ℝ := PowerSeries.coeff n (tailOp^[m] sourceSym * sourceSym⁻¹)

theorem coeff_sourceSeries_mul (ρ : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (sourceSeries ρ * sourceSym⁻¹) =
      ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff m ρ * tailTable m n := by
  rw [coeff_mul_congr_left (a' := ∑ m ∈ Finset.range (n + 1),
    PowerSeries.C (PowerSeries.coeff m ρ) * tailOp^[m] sourceSym) fun i hi => by
      rw [coeff_sourceSeries_eq _ (show i < n + 1 by omega), map_sum]
      simp only [PowerSeries.coeff_C_mul],
    Finset.sum_mul, map_sum]
  simp only [mul_assoc, PowerSeries.coeff_C_mul, tailTable]

theorem sourceSym_constantCoeff : PowerSeries.constantCoeff sourceSym ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_sourceSym]; positivity

theorem tailTable_zero (n : ℕ) : tailTable 0 n = if n = 0 then 1 else 0 := by
  rw [tailTable, Function.iterate_zero, id, PowerSeries.mul_inv_cancel _ sourceSym_constantCoeff,
    PowerSeries.coeff_one]

/-- The diagonal of the table: `E_{n,n} = (2π)^{-n}`. -/
theorem tailTable_self (n : ℕ) : tailTable n n = ((2 * Real.pi) ^ n)⁻¹ := by
  rw [tailTable, PowerSeries.coeff_mul, Finset.sum_eq_single (n, 0)]
  · rw [coeff_iterate_tailOp_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_inv, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_zero_sourceSym]
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  · intro p hp hpn
    have h1 := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    rw [coeff_iterate_tailOp_of_lt n (show p.1 < n by
      rcases p with ⟨a, b⟩
      simp only at h1 ⊢
      by_contra hc
      exact hpn (Prod.ext (by simp; omega) (by simp; omega))), zero_mul]
  · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

/-- The kernel coefficients `κ_j = ρ_{j+1}`: the coefficients of `s^{-j-1}` in the expansion of
`N(−s²)/P_L(−s²)` at `s = ∞` (the Taylor coefficients `K^{(j)}(0)` of its causal kernel). -/
def causalKernelCoeff (l : List ℂ) (N : Polynomial ℝ) (j : ℕ) : ℝ :=
  PowerSeries.coeff (j + 1) (realCombSymbol l N)

/-- **The full tail germ (Watson expansion).**  There are universal constants `c_{n,j}` such that for
every selection and every real `N` with `deg N ≤ D`,
`u_N/k ∼ ρ₀ + Σ_{n≥0} a_n e^{-2(n+1)x}` with `a_n = κ_n/(2π)^{n+1} + Σ_{j<n} c_{n,j} κ_j`. -/
theorem rationalSource_tail_germ :
    ∃ c : ℕ → ℕ → ℝ, ∀ (l : List ℂ) (N : Polynomial ℝ),
      N.natDegree ≤ (quadrantListOf l).length →
      ∃ a : ℕ → ℝ, (∀ n, a n = causalKernelCoeff l N n / (2 * Real.pi) ^ (n + 1) +
          ∑ j ∈ Finset.range n, c n j * causalKernelCoeff l N j) ∧
        ∀ M : ℕ, ∃ C, ∀ᶠ x in atTop, |rationalSource l N x / thetaCuspFullSource x -
          (PowerSeries.coeff 0 (realCombSymbol l N) + ∑ n ∈ Finset.range M,
            a n * Real.exp (-(2 * (n + 1) * x)))| ≤ C * Real.exp (-(2 * (M + 1) * x)) := by
  refine ⟨fun n j => tailTable (j + 1) (n + 1), fun l N hN => ?_⟩
  set A := sourceSeries (realCombSymbol l N) * sourceSym⁻¹ with hA
  refine ⟨fun n => PowerSeries.coeff (n + 1) A, fun n => ?_, fun M => ?_⟩
  · show PowerSeries.coeff (n + 1) A = causalKernelCoeff l N n / (2 * Real.pi) ^ (n + 1) +
      ∑ j ∈ Finset.range n, tailTable (j + 1) (n + 1) * causalKernelCoeff l N j
    rw [hA, coeff_sourceSeries_mul, Finset.sum_range_succ', tailTable_zero, if_neg (by omega),
      mul_zero, add_zero, Finset.sum_range_succ, tailTable_self]
    simp only [causalKernelCoeff, mul_comm (tailTable _ _)]
    rw [div_eq_mul_inv, add_comm]
  · obtain ⟨C, hC⟩ := hasExpansion_rationalSource l N hN (M + 1)
    refine ⟨C, ?_⟩
    filter_upwards [hC] with x hx
    have hk := thetaCuspFullSource_pos x
    have hA0 : PowerSeries.coeff 0 A = PowerSeries.coeff 0 (realCombSymbol l N) := by
      rw [hA, coeff_sourceSeries_mul, Finset.sum_range_one, tailTable_zero, if_pos rfl, mul_one]
    have htr : truncEval A (M + 1) x = PowerSeries.coeff 0 (realCombSymbol l N) +
        ∑ n ∈ Finset.range M, PowerSeries.coeff (n + 1) A * Real.exp (-(2 * (n + 1) * x)) := by
      rw [truncEval, Finset.sum_range_succ', pow_zero, mul_one, hA0, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [Real.norm_eq_abs] at hx
    push_cast at hx
    rw [← htr, show rationalSource l N x / thetaCuspFullSource x - truncEval A (M + 1) x =
      (rationalSource l N x - thetaCuspFullSource x * truncEval A (M + 1) x) /
        thetaCuspFullSource x by field_simp, abs_div, abs_of_pos hk, div_le_iff₀ hk]
    exact hx

/-- **Recursive recovery.**  In a triangular system `a_n = κ_n/(2π)^{n+1} + Σ_{j<n} c_{n,j} κ_j`, the
coefficients `a_0, …, a_n` determine `κ_0, …, κ_n`. -/
theorem triangular_recovery {c : ℕ → ℕ → ℝ} {κ κ' a a' : ℕ → ℝ}
    (h : ∀ n, a n = κ n / (2 * Real.pi) ^ (n + 1) + ∑ j ∈ Finset.range n, c n j * κ j)
    (h' : ∀ n, a' n = κ' n / (2 * Real.pi) ^ (n + 1) + ∑ j ∈ Finset.range n, c n j * κ' j)
    {n : ℕ} (ha : ∀ j ≤ n, a j = a' j) : ∀ j ≤ n, κ j = κ' j := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hsum : ∑ i ∈ Finset.range j, c j i * κ i = ∑ i ∈ Finset.range j, c j i * κ' i :=
      Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.1 hi) (by simp at hi; omega)]
    have := ha j hj
    rw [h, h', hsum, add_left_inj] at this
    have hπ : (2 * Real.pi) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by positivity)
    field_simp at this
    exact this

/-- **Uniqueness of expansions in `e^{-2x}`.**  If `Σ_{n<L} d_n e^{-2nx} = O(e^{-2Lx})`, then
`d_n = 0` for `n < L`. -/
theorem eq_zero_of_sum_exp_small {L : ℕ} {d : ℕ → ℝ}
    (h : ∃ C, ∀ᶠ x in atTop, |∑ n ∈ Finset.range L, d n * Real.exp (-(2 * x)) ^ n| ≤
      C * Real.exp (-(2 * x)) ^ L) : ∀ n < L, d n = 0 := by
  have hw : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).congr fun x => by
        simp only [Function.comp, id]
  induction L generalizing d with
  | zero => intro n hn; omega
  | succ L ih =>
    obtain ⟨C, hC⟩ := h
    -- the constant term vanishes
    have h0 : d 0 = 0 := by
      have hlim : Tendsto (fun x => ∑ n ∈ Finset.range (L + 1), d n * Real.exp (-(2 * x)) ^ n) atTop
          (𝓝 (∑ n ∈ Finset.range (L + 1), d n * 0 ^ n)) :=
        tendsto_finsetSum _ fun n _ => (hw.pow n).const_mul (d n)
      rw [Finset.sum_range_succ', Finset.sum_eq_zero fun n _ => by simp, zero_add, pow_zero,
        mul_one] at hlim
      have hsmall : Tendsto (fun x => ∑ n ∈ Finset.range (L + 1), d n * Real.exp (-(2 * x)) ^ n)
          atTop (𝓝 0) := by
        have hb := (hw.pow (L + 1)).const_mul C
        rw [zero_pow (by omega), mul_zero] at hb
        exact squeeze_zero_norm' (f := fun x => ∑ n ∈ Finset.range (L + 1),
          d n * Real.exp (-(2 * x)) ^ n) (hC.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx) hb
      exact tendsto_nhds_unique hlim hsmall
    have hrest := ih (d := fun n => d (n + 1)) ⟨C, by
      filter_upwards [hC] with x hx
      have hwp := Real.exp_pos (-(2 * x))
      rw [Finset.sum_range_succ', h0, zero_mul, add_zero] at hx
      have heq : ∑ n ∈ Finset.range L, d (n + 1) * Real.exp (-(2 * x)) ^ (n + 1) =
          Real.exp (-(2 * x)) * ∑ n ∈ Finset.range L, d (n + 1) * Real.exp (-(2 * x)) ^ n := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
      rw [heq, abs_mul, abs_of_pos hwp, pow_succ] at hx
      have := le_of_mul_le_mul_left (by linarith : Real.exp (-(2 * x)) *
        |∑ n ∈ Finset.range L, d (n + 1) * Real.exp (-(2 * x)) ^ n| ≤
          Real.exp (-(2 * x)) * (C * Real.exp (-(2 * x)) ^ L)) hwp
      exact this⟩
    intro n hn
    rcases n with _ | n
    · exact h0
    · exact hrest n (by omega)

/-- **The full tail germ is faithful.**  If `u_N/k` and `u_{N'}/k` (for possibly different selections)
agree to every order in `e^{-2x}`, then their symbols agree: the same constant `ρ₀` and the same
kernel coefficients `κ_j` for all `j`. -/
theorem causalKernelCoeff_eq_of_germ_eq {l l' : List ℂ} {N N' : Polynomial ℝ}
    (hN : N.natDegree ≤ (quadrantListOf l).length) (hN' : N'.natDegree ≤ (quadrantListOf l').length)
    (h : ∀ M : ℕ, TailSmall thetaCuspFullSource M fun x => rationalSource l N x - rationalSource l' N' x) :
    PowerSeries.coeff 0 (realCombSymbol l N) = PowerSeries.coeff 0 (realCombSymbol l' N') ∧
      ∀ j, causalKernelCoeff l N j = causalKernelCoeff l' N' j := by
  obtain ⟨c, hc⟩ := rationalSource_tail_germ
  obtain ⟨a, ha, hexp⟩ := hc l N hN
  obtain ⟨a', ha', hexp'⟩ := hc l' N' hN'
  set d : ℕ → ℝ := fun n => if n = 0 then PowerSeries.coeff 0 (realCombSymbol l N) -
    PowerSeries.coeff 0 (realCombSymbol l' N') else a (n - 1) - a' (n - 1) with hd
  have hzero : ∀ M, ∀ n < M + 1, d n = 0 := by
    intro M
    refine eq_zero_of_sum_exp_small ?_
    obtain ⟨C₁, h₁⟩ := hexp M
    obtain ⟨C₂, h₂⟩ := hexp' M
    obtain ⟨C₃, h₃⟩ := h (M + 1)
    refine ⟨|C₁| + |C₂| + |C₃|, ?_⟩
    filter_upwards [h₁, h₂, h₃] with x hx1 hx2 hx3
    have hk := thetaCuspFullSource_pos x
    have hpow : ∀ n : ℕ, Real.exp (-(2 * ((n : ℝ) + 1) * x)) = Real.exp (-(2 * x)) ^ (n + 1) :=
      fun n => by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hsum : ∑ n ∈ Finset.range (M + 1), d n * Real.exp (-(2 * x)) ^ n =
        (PowerSeries.coeff 0 (realCombSymbol l N) + ∑ n ∈ Finset.range M,
            a n * Real.exp (-(2 * ((n : ℝ) + 1) * x))) -
          (PowerSeries.coeff 0 (realCombSymbol l' N') + ∑ n ∈ Finset.range M,
            a' n * Real.exp (-(2 * ((n : ℝ) + 1) * x))) := by
      rw [Finset.sum_range_succ']
      simp only [hd, if_pos, pow_zero, mul_one, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, hpow]
      rw [add_sub_add_comm, ← Finset.sum_sub_distrib]
      simp only [sub_mul]
      ring
    rw [hsum]
    rw [Real.norm_eq_abs] at hx3
    have h3 : |rationalSource l N x / thetaCuspFullSource x - rationalSource l' N' x /
        thetaCuspFullSource x| ≤ |C₃| * Real.exp (-(2 * ((M + 1 : ℕ) : ℝ) * x)) := by
      rw [← sub_div, abs_div, abs_of_pos hk, div_le_iff₀ hk]
      exact hx3.trans (by gcongr; exact le_abs_self _)
    have hM : Real.exp (-(2 * ((M : ℝ) + 1) * x)) = Real.exp (-(2 * x)) ^ (M + 1) := hpow M
    push_cast at h3
    rw [hM] at hx1 hx2 h3
    have key : ∀ U U' T T' : ℝ, |T - T'| ≤ |U - T| + |U' - T'| + |U - U'| := fun U U' T T' => by
      calc |T - T'| = |((U - U') - (U - T)) + (U' - T')| := by ring_nf
        _ ≤ |(U - U') - (U - T)| + |U' - T'| := abs_add_le _ _
        _ ≤ |U - U'| + |U - T| + |U' - T'| := by gcongr; exact abs_sub _ _
        _ = _ := by ring
    calc _ ≤ _ := key (rationalSource l N x / thetaCuspFullSource x)
          (rationalSource l' N' x / thetaCuspFullSource x) _ _
      _ ≤ C₁ * Real.exp (-(2 * x)) ^ (M + 1) + C₂ * Real.exp (-(2 * x)) ^ (M + 1) +
          |C₃| * Real.exp (-(2 * x)) ^ (M + 1) := by
          linarith
      _ ≤ _ := by
          have := pow_pos (Real.exp_pos (-(2 * x))) (M + 1)
          nlinarith [le_abs_self C₁, le_abs_self C₂]
  refine ⟨?_, fun j => ?_⟩
  · simpa [hd] using sub_eq_zero.1 (hzero 0 0 (by omega))
  · refine triangular_recovery ha ha' (n := j) (fun i hi => ?_) j le_rfl
    have := hzero (i + 1) (i + 1) (by omega)
    simp only [hd, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at this
    exact sub_eq_zero.1 this

/-! ## The causal kernel of `r(−s²)` -/

/-- The polynomial `∏_{β∈L} (1 + β²X²)`. -/
def symbolDenPoly (L : List ℂ) : Polynomial ℂ :=
  (L.map fun β => 1 + Polynomial.C (β ^ 2) * Polynomial.X ^ 2).prod

theorem symbolDen_eq_coe (L : List ℂ) : symbolDen L = (symbolDenPoly L : PowerSeries ℂ) := by
  induction L with
  | nil => simp [symbolDen, symbolDenPoly]
  | cons β L ih =>
    simp only [symbolDen, symbolDenPoly, List.map_cons, List.prod_cons] at ih ⊢
    rw [Polynomial.coe_mul, ← ih]
    simp [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X]

theorem eval_symbolDenPoly (L : List ℂ) (w : ℂ) :
    (symbolDenPoly L).eval w = (L.map fun β => 1 + β ^ 2 * w ^ 2).prod := by
  rw [symbolDenPoly, Polynomial.eval_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp

theorem coeff_zero_symbolDenPoly (L : List ℂ) : (symbolDenPoly L).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_symbolDenPoly]
  simp

/-- **Geometric growth.**  If `ρ · Q = F` with polynomials `Q, F` and `Q(0) = 1`, then
`‖ρ_n‖ ≤ C R^n`. -/
theorem exists_geometric_bound {ρ : PowerSeries ℂ} {Q F : Polynomial ℂ} (hQ0 : Q.coeff 0 = 1)
    (h : ρ * (Q : PowerSeries ℂ) = (F : PowerSeries ℂ)) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ n, ‖PowerSeries.coeff n ρ‖ ≤ C * R ^ n := by
  classical
  set CF := ∑ i ∈ F.support, ‖F.coeff i‖ with hCF
  set S := ∑ j ∈ Q.support, ‖Q.coeff j‖ with hS
  have hCF0 : 0 ≤ CF := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hFb : ∀ n, ‖F.coeff n‖ ≤ CF := fun n => by
    by_cases hn : n ∈ F.support
    · exact Finset.single_le_sum (f := fun i => ‖F.coeff i‖) (fun i _ => norm_nonneg _) hn
    · rw [Polynomial.notMem_support_iff.1 hn, norm_zero]; exact hCF0
  have hQb : ∀ T : Finset ℕ, ∑ j ∈ T, ‖Q.coeff j‖ ≤ S := fun T => by
    rw [← Finset.sum_filter_add_sum_filter_not T (· ∈ Q.support),
      Finset.sum_eq_zero (s := T.filter (· ∉ Q.support)) fun j hj => by
        rw [Polynomial.notMem_support_iff.1 (Finset.mem_filter.1 hj).2, norm_zero], add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => (Finset.mem_filter.1 hj).2)
      fun _ _ _ => norm_nonneg _
  refine ⟨CF, 1 + S, hCF0, by linarith, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hc := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Nat.sub_self, Polynomial.coeff_coe, hQ0, mul_one, Polynomial.coeff_coe] at hc
  simp only [Polynomial.coeff_coe] at hc
  have hρ : PowerSeries.coeff n ρ = F.coeff n -
      ∑ k ∈ Finset.range n, PowerSeries.coeff k ρ * Q.coeff (n - k) := by
    rw [← hc]; ring
  rcases n with _ | n
  · rw [hρ, Finset.sum_range_zero, sub_zero, pow_zero, mul_one]
    exact hFb 0
  · have hR1 : (1 : ℝ) ≤ 1 + S := by linarith
    have hsum : ∑ k ∈ Finset.range (n + 1), ‖Q.coeff (n + 1 - k)‖ ≤ S := by
      rw [← Finset.sum_image (f := fun j => ‖Q.coeff j‖) (g := fun k => n + 1 - k) (s := Finset.range (n + 1))
        (fun a ha b hb hab => by simp at ha hb hab; omega)]
      exact hQb _
    rw [hρ]
    calc ‖F.coeff (n + 1) - ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k ρ * Q.coeff (n + 1 - k)‖
        ≤ CF + ∑ k ∈ Finset.range (n + 1), CF * (1 + S) ^ n * ‖Q.coeff (n + 1 - k)‖ := by
          refine (norm_sub_le _ _).trans (add_le_add (hFb _) ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k hk => ?_)))
          have hk' := Finset.mem_range.1 hk
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_right ((ih k (by omega)).trans ?_) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (by omega)) hCF0
      _ = CF + CF * (1 + S) ^ n * ∑ k ∈ Finset.range (n + 1), ‖Q.coeff (n + 1 - k)‖ := by
          rw [Finset.mul_sum]
      _ ≤ CF + CF * (1 + S) ^ n * S := by gcongr
      _ ≤ CF * (1 + S) ^ (n + 1) := by
          have h1 : 1 ≤ (1 + S) ^ n := one_le_pow₀ hR1
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_left h1 hCF0]

theorem exists_realCombSymbol_bound (l : List ℂ) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ n, |PowerSeries.coeff n (realCombSymbol l N)| ≤ C * R ^ n := by
  have hdeg : (N.map (algebraMap ℝ ℂ)).natDegree ≤ (quadrantListOf l).length :=
    (Polynomial.natDegree_map_le).trans hN
  obtain ⟨C, R, hC, hR, hb⟩ := exists_geometric_bound
    (ρ := combSymbol (quadrantListOf l) (N.map (algebraMap ℝ ℂ))) (Q := symbolDenPoly _)
    (F := Polynomial.C ((quadrantListOf l).map fun β => β ^ 2).prod *
      evenRev (quadrantListOf l).length (N.map (algebraMap ℝ ℂ)))
    (coeff_zero_symbolDenPoly _) (by
      rw [← symbolDen_eq_coe, combSymbol_mul_symbolDen _ hdeg, Polynomial.coe_mul, Polynomial.coe_C])
  refine ⟨C, R, hC, hR, fun n => ?_⟩
  have := hb n
  rwa [coeff_combSymbol_eq_ofReal l N hN, Complex.norm_real, Real.norm_eq_abs] at this

/-- The causal kernel `K(t) = Σ_j κ_j t^j/j!`. -/
def causalKernel (l : List ℂ) (N : Polynomial ℝ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, causalKernelCoeff l N j * (t ^ j / j.factorial)

/-- The Taylor series of the causal kernel converges on the whole line. -/
theorem summable_causalKernel (l : List ℂ) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) (t : ℝ) :
    Summable fun j => causalKernelCoeff l N j * (t ^ j / j.factorial) := by
  obtain ⟨C, R, hC, hR, hb⟩ := exists_realCombSymbol_bound l N hN
  refine ((Real.summable_pow_div_factorial (R * |t|)).mul_left (C * R)).of_norm_bounded fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast, mul_pow]
  have hk := hb (j + 1)
  simp only [causalKernelCoeff]
  calc |PowerSeries.coeff (j + 1) (realCombSymbol l N)| * (|t| ^ j / j.factorial)
      ≤ C * R ^ (j + 1) * (|t| ^ j / j.factorial) := mul_le_mul_of_nonneg_right hk (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem prod_one_add_sq_mul_inv_sq {L : List ℂ} (hL : ∀ β ∈ L, β ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    (L.map fun β => 1 + β ^ 2 * ((s : ℂ)⁻¹) ^ 2).prod =
      (L.map fun β => β ^ 2).prod * ((s : ℂ)⁻¹) ^ (2 * L.length) * listDivisor L (Complex.I * s) := by
  induction L with
  | nil => simp [listDivisor_nil]
  | cons β L ih =>
    have hβ : β ≠ 0 := hL β List.mem_cons_self
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    rw [List.map_cons, List.prod_cons, ih fun b hb => hL b (List.mem_cons_of_mem _ hb), List.map_cons,
      List.prod_cons, listDivisor_cons, List.length_cons, mul_pow, Complex.I_sq,
      show 2 * (L.length + 1) = 2 + 2 * L.length by ring, pow_add]
    field_simp
    ring

/-- **The causal kernel of `r(−s²)`.**  For all large real `s`, `K(t) e^{-st}` is integrable on
`(0, ∞)` and `(ρ₀ + ∫₀^∞ K(t) e^{-st} dt) · P_L(is) = N(−s²)`: the Laplace transform of `K` is the
proper part of `r(−s²) = N(−s²)/P_L(is)`, whose Laurent coefficients at `s = ∞` are the `κ_j`. -/
theorem causalKernel_laplace {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) :
    ∃ s₀ > 0, ∀ s : ℝ, s₀ < s →
      IntegrableOn (fun t => causalKernel l N t * Real.exp (-(s * t))) (Ioi 0) ∧
      ((PowerSeries.coeff 0 (realCombSymbol l N) +
        ∫ t in Ioi (0 : ℝ), causalKernel l N t * Real.exp (-(s * t)) : ℝ) : ℂ) *
          listDivisor (quadrantListOf l) (Complex.I * s) = ((N.eval (-s ^ 2) : ℝ) : ℂ) := by
  obtain ⟨C, R, hC, hR, hb⟩ := exists_realCombSymbol_bound l N hN
  refine ⟨R, by linarith, fun s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  set F : ℕ → ℝ → ℝ := fun j t => causalKernelCoeff l N j * (t ^ j / j.factorial) * Real.exp (-(s * t))
    with hF
  have hFint : ∀ j, Integrable (F j) (volume.restrict (Ioi 0)) := fun j =>
    ((integrableOn_natPow_mul_exp_neg_mul_Ioi j hs0).const_mul
      (causalKernelCoeff l N j / j.factorial)).congr (Eventually.of_forall fun t => by
        simp only [hF]; ring)
  have hFnorm : ∀ j, ∫ t in Ioi (0 : ℝ), ‖F j t‖ = |causalKernelCoeff l N j| / s ^ (j + 1) := fun j => by
    have hfact : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t => |causalKernelCoeff l N j| / j.factorial *
      (t ^ j * Real.exp (-(s * t)))) fun t ht => by
        have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
        simp only [hF, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_nonneg ht0, Nat.abs_cast,
          abs_of_pos (Real.exp_pos _)]
        ring,
      integral_const_mul, integral_natPow_mul_exp_neg_mul_Ioi j hs0]
    field_simp
  have hFval : ∀ j, ∫ t in Ioi (0 : ℝ), F j t = causalKernelCoeff l N j / s ^ (j + 1) := fun j => by
    have hfact : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t => causalKernelCoeff l N j / j.factorial *
      (t ^ j * Real.exp (-(s * t)))) fun t _ => by simp only [hF]; ring,
      integral_const_mul, integral_natPow_mul_exp_neg_mul_Ioi j hs0]
    field_simp
  have hgeom : Summable fun j : ℕ => C * (R / s) ^ (j + 1) :=
    ((summable_geometric_of_lt_one (by positivity) ((div_lt_one hs0).2 hs)).mul_left
      (C * (R / s))).congr fun j => by ring
  have hbound : ∀ j, |causalKernelCoeff l N j| / s ^ (j + 1) ≤ C * (R / s) ^ (j + 1) := fun j => by
    rw [div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    exact hb (j + 1)
  have hSum : Summable fun j => ∫ t in Ioi (0 : ℝ), ‖F j t‖ :=
    hgeom.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      fun j => (hFnorm j).le.trans (hbound j)
  have hKF : ∀ t, causalKernel l N t * Real.exp (-(s * t)) = ∑' j, F j t := fun t => by
    rw [causalKernel, ← tsum_mul_right]
  have hint_eq := integral_tsum_of_summable_integral_norm hFint hSum
  simp only [← hKF, hFval] at hint_eq
  -- integrability
  have hmeas : StronglyMeasurable fun t => causalKernel l N t * Real.exp (-(s * t)) := by
    refine stronglyMeasurable_of_tendsto (u := atTop)
      (f := fun n t => ∑ j ∈ Finset.range n, F j t) (fun n => ?_) ?_
    · exact (continuous_finsetSum _ fun j _ => by simp only [hF]; fun_prop).stronglyMeasurable
    · refine tendsto_pi_nhds.2 fun t => ?_
      rw [hKF]
      exact ((summable_causalKernel l N hN t).mul_right (Real.exp (-(s * t)))).hasSum.tendsto_sum_nat
        |>.congr fun n => by simp only [hF]
  have hIK : IntegrableOn (fun t => causalKernel l N t * Real.exp (-(s * t))) (Ioi 0) := by
    refine ((integrableOn_natPow_mul_exp_neg_mul_Ioi 0 (show 0 < s - R by linarith)).const_mul
      (C * R)).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [hKF, Real.norm_eq_abs]
    have hsF : Summable fun j => |F j t| :=
      ((summable_causalKernel l N hN t).mul_right (Real.exp (-(s * t)))).abs.congr fun j => by
        simp only [hF]
    calc |∑' j, F j t| ≤ ∑' j, |F j t| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun j => F j t) hsF
      _ ≤ ∑' j, C * R * ((R * t) ^ j / j.factorial) * Real.exp (-(s * t)) := by
          refine hsF.tsum_le_tsum (fun j => ?_) (((Real.summable_pow_div_factorial (R * t)).mul_left
            (C * R)).mul_right _)
          simp only [hF, abs_mul, abs_div, abs_pow, abs_of_nonneg ht0, Nat.abs_cast,
            abs_of_pos (Real.exp_pos _)]
          have hk := hb (j + 1)
          simp only [causalKernelCoeff] at hk ⊢
          calc |PowerSeries.coeff (j + 1) (realCombSymbol l N)| * (t ^ j / j.factorial) *
                Real.exp (-(s * t)) ≤ C * R ^ (j + 1) * (t ^ j / j.factorial) * Real.exp (-(s * t)) := by
                gcongr
            _ = _ := by rw [pow_succ, mul_pow]; ring
      _ = C * R * Real.exp (R * t) * Real.exp (-(s * t)) := by
          rw [tsum_mul_right, tsum_mul_left, Real.exp_eq_exp_ℝ,
            (NormedSpace.expSeries_div_hasSum_exp (R * t)).tsum_eq]
      _ = C * R * (t ^ 0 * Real.exp (-((s - R) * t))) := by
          rw [pow_zero, one_mul, mul_assoc, ← Real.exp_add]; ring_nf
  refine ⟨hIK, ?_⟩
  -- the evaluation of the symbol identity at `w = 1/s`
  have hβ0 : ∀ β ∈ quadrantListOf l, β ≠ 0 := fun β hβ => by
    obtain ⟨α, hα, h | h⟩ := mem_quadrantListOf hβ
    · rw [h]; exact ne_zero_of_mem_xiQuadrantZeros (hl α hα)
    · rw [h]; exact (map_ne_zero _).2 (ne_zero_of_mem_xiQuadrantZeros (hl α hα))
  have hdeg : (N.map (algebraMap ℝ ℂ)).natDegree ≤ (quadrantListOf l).length :=
    (Polynomial.natDegree_map_le).trans hN
  set w : ℂ := (s : ℂ)⁻¹ with hw
  have hw0 : w ≠ 0 := inv_ne_zero (by exact_mod_cast hs0.ne')
  have hwn : ‖w‖ = s⁻¹ := by rw [hw, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  set ρ := combSymbol (quadrantListOf l) (N.map (algebraMap ℝ ℂ)) with hρ
  set Q := symbolDenPoly (quadrantListOf l) with hQ
  set E := Polynomial.C ((quadrantListOf l).map fun β => β ^ 2).prod *
    evenRev (quadrantListOf l).length (N.map (algebraMap ℝ ℂ)) with hE
  have hρQ : ρ * (Q : PowerSeries ℂ) = (E : PowerSeries ℂ) := by
    rw [hρ, hQ, ← symbolDen_eq_coe, combSymbol_mul_symbolDen _ hdeg, hE, Polynomial.coe_mul,
      Polynomial.coe_C]
  have hρn : ∀ n, PowerSeries.coeff n ρ = ((PowerSeries.coeff n (realCombSymbol l N) : ℝ) : ℂ) :=
    coeff_combSymbol_eq_ofReal l N hN
  have hsumρ : Summable fun n => ‖PowerSeries.coeff n ρ * w ^ n‖ := by
    refine ((summable_geometric_of_lt_one (by positivity) ((div_lt_one hs0).2 hs)).mul_left C).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_
    rw [norm_mul, norm_pow, hwn, hρn, Complex.norm_real, Real.norm_eq_abs, div_pow, inv_pow,
      ← div_eq_mul_inv, mul_div_assoc']
    exact div_le_div_of_nonneg_right (hb n) (by positivity)
  have hfin : ∀ P : Polynomial ℂ, (∑' n, P.coeff n * w ^ n) = P.eval w := fun P => by
    rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1)) fun n hn => by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hn; omega), zero_mul],
      Polynomial.eval_eq_sum_range]
  have hfinsum : ∀ P : Polynomial ℂ, Summable fun n => ‖P.coeff n * w ^ n‖ := fun P =>
    summable_of_ne_finset_zero (s := Finset.range (P.natDegree + 1)) fun n hn => by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hn; omega), zero_mul, norm_zero]
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsumρ (hfinsum Q)
  have hprod : (∑' n, PowerSeries.coeff n ρ * w ^ n) * Q.eval w = E.eval w := by
    rw [← hfin Q, hcauchy, ← hfin E]
    refine tsum_congr fun n => ?_
    have := congrArg (PowerSeries.coeff n) hρQ
    rw [PowerSeries.coeff_mul, Polynomial.coeff_coe] at this
    simp only [Polynomial.coeff_coe] at this
    rw [← this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hkl, pow_add]
    ring
  have hsplit : (∑' n, PowerSeries.coeff n ρ * w ^ n) =
      (((PowerSeries.coeff 0 (realCombSymbol l N) +
        ∫ t in Ioi (0 : ℝ), causalKernel l N t * Real.exp (-(s * t)) : ℝ)) : ℂ) := by
    rw [(hsumρ.of_norm).tsum_eq_zero_add, ← hint_eq, pow_zero, mul_one, hρn, Complex.ofReal_add,
      Complex.ofReal_tsum]
    congr 1
    refine tsum_congr fun j => ?_
    rw [hρn, causalKernelCoeff, hw, Complex.ofReal_div, Complex.ofReal_pow, inv_pow, div_eq_mul_inv]
  rw [hsplit, hQ, eval_symbolDenPoly, hE, Polynomial.eval_mul, Polynomial.eval_C,
    eval_evenRev hdeg hw0, prod_one_add_sq_mul_inv_sq hβ0 hs0.ne'] at hprod
  have hNev : (N.map (algebraMap ℝ ℂ)).eval (-1 / w ^ 2) = ((N.eval (-s ^ 2) : ℝ) : ℂ) := by
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    rw [hw, Polynomial.eval_map, show (-1 / ((s : ℂ)⁻¹) ^ 2 : ℂ) = algebraMap ℝ ℂ (-s ^ 2) by
      rw [Complex.coe_algebraMap]; push_cast; field_simp, Polynomial.eval₂_at_apply]
    rfl
  rw [hNev] at hprod
  have hc0 : ((quadrantListOf l).map fun β => β ^ 2).prod * w ^ (2 * (quadrantListOf l).length) ≠ 0 :=
    mul_ne_zero (List.prod_ne_zero (by
      simp only [List.mem_map, not_exists, not_and]
      exact fun β hβ h => hβ0 β hβ (pow_eq_zero_iff (by norm_num) |>.1 h))) (pow_ne_zero _ hw0)
  apply mul_left_cancel₀ hc0
  linear_combination hprod

end

end RHTower
