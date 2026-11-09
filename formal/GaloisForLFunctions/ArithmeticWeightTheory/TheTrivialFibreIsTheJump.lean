import GaloisForLFunctions.ArithmeticWeightTheory.TheGenericFibreHasUniformWeights
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The trivial fibre is the jump

In a family of twists over a curve the trivial character is the bad fibre: its `H⁰` and `H²`
jump, and the poles of its L-function are coinvariants present only there. The gauge family of
`Spec ℤ` behaves the same way. The generic fibre has uniform weights
(`TheGenericFibreHasUniformWeights`); the trivial fibre `x = 0`, whose traces are the prime counts
of `ζ` in the windows, carries the pole.

**The pole at the trivial fibre** (`mul_sqrt_le_trivial_fibreTrace`). For a window with
`0 ≤ g` and `g ≥ c > 0` on `[−1, 1]`, radius `R ≥ 1`, and every prime `p ≥ e^{200}`,
`|T_0(log p)| ≥ c √p`: Chebyshev's bounds give `θ(e^{u+1}) − θ(e^{u−1}) ≥ e^u` for `u ≥ 200`
(`exp_le_theta_window`). The trivial fibre has trace exponent `½`
(`exists_prime_mul_rpow_lt_trivial_fibreTrace`).

**Constants against exponents** (`trivial_fibre_is_the_jump`). Let `0 < a < ½` and let
`C(K, a)` be the fibres whose traces satisfy `|T_x(log p)| ≤ K p^a` at every prime. Each `C(K, a)`
is closed in the product topology (`isClosed_traceConstantSet`): the trace constant is lower
semicontinuous, so constants specialize in Deligne's direction. Almost every fibre lies in some
`C(K, a)`, and `Haar(C(n, a)) → 1` (`tendsto_measure_traceConstantSet`); yet no `C(K, a)` meets a
neighbourhood of the trivial fibre. The trace constants of the generic fibres tend to infinity
at the special fibre: the pole is a jump of the coinvariants, and the weight of `ζ` cannot be read
from nearby fibres in the product topology.
-/

open MeasureTheory Finset Real Filter Topology
open scoped Chebyshev

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry

/-- The twist at the trivial point is `1`. -/
theorem twist_trivial (n : ℕ) : twist (0 : GaugeTorus) n = 1 := by
  have h := twist_add (0 : GaugeTorus) 0 n
  rw [add_zero] at h
  have hne : twist (0 : GaugeTorus) n ≠ 0 := by
    intro h0
    have := norm_twist (0 : GaugeTorus) n
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)

/-- At the trivial fibre the window trace is the real window prime count. -/
theorem fibreTrace_trivial (g : ℝ → ℝ) (R u : ℝ) :
    fibreTrace g R u 0 =
      ((∑ p ∈ windowPrimes R u, Real.exp (-(u / 2)) * Real.log p * g (Real.log p - u) : ℝ) : ℂ) := by
  simp only [fibreTrace, twistSum, twist_trivial, mul_one, windowWeight]
  rw [Complex.ofReal_sum]

/-- The window prime count bounds the trivial trace from below. -/
theorem theta_window_le_trivial_fibreTrace {g : ℝ → ℝ} (hg0 : ∀ v, 0 ≤ g v) {c : ℝ}
    (hgc : ∀ v, |v| ≤ 1 → c ≤ g v) {R : ℝ} (hR : 1 ≤ R) (u : ℝ) :
    c * (Real.exp (-(u / 2)) * (θ (Real.exp (u + 1)) - θ (Real.exp (u - 1)))) ≤
      ‖fibreTrace g R u 0‖ := by
  set A := Nat.primesLE ⌊Real.exp (u + 1)⌋₊
  set B := Nat.primesLE ⌊Real.exp (u - 1)⌋₊
  have hBA : B ⊆ A :=
    Nat.primesLE_mono (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith)))
  have hAW : A ⊆ windowPrimes R u :=
    Nat.primesLE_mono (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith)))
  have hθ : θ (Real.exp (u + 1)) - θ (Real.exp (u - 1)) = ∑ p ∈ A \ B, Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
      ← Finset.sum_sdiff hBA]
    ring
  rw [fibreTrace_trivial, Complex.norm_real, Real.norm_eq_abs, hθ]
  refine le_trans ?_ (le_abs_self _)
  rw [Finset.mul_sum, Finset.mul_sum]
  calc ∑ p ∈ A \ B, c * (Real.exp (-(u / 2)) * Real.log p)
      ≤ ∑ p ∈ A \ B, Real.exp (-(u / 2)) * Real.log p * g (Real.log p - u) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpA, hpB⟩ := Finset.mem_sdiff.mp hp
        obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hpA
        have hnot : ⌊Real.exp (u - 1)⌋₊ < p := by
          by_contra h
          push Not at h
          exact hpB (Nat.mem_primesLE.mpr ⟨h, hpp⟩)
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hlow : Real.exp (u - 1) < p := (Nat.floor_lt (Real.exp_pos _).le).mp hnot
        have hup : (p : ℝ) ≤ Real.exp (u + 1) :=
          (Nat.cast_le.mpr hpN).trans (Nat.floor_le (Real.exp_pos _).le)
        have hl1 : u - 1 < Real.log p := (Real.lt_log_iff_exp_lt hp0).mpr hlow
        have hl2 : Real.log p ≤ u + 1 := (Real.log_le_iff_le_exp hp0).mpr hup
        have hv : |Real.log p - u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
        have hgv := hgc _ hv
        have he : 0 ≤ Real.exp (-(u / 2)) * Real.log p := mul_nonneg (Real.exp_pos _).le hlog0
        calc c * (Real.exp (-(u / 2)) * Real.log p) = Real.exp (-(u / 2)) * Real.log p * c := by ring
          _ ≤ Real.exp (-(u / 2)) * Real.log p * g (Real.log p - u) :=
            mul_le_mul_of_nonneg_left hgv he
    _ ≤ ∑ p ∈ windowPrimes R u, Real.exp (-(u / 2)) * Real.log p * g (Real.log p - u) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset.trans hAW) fun p hp _ => ?_
        have hpp := (Nat.mem_primesLE.mp hp).2
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
          (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))) (hg0 _)

/-- **Chebyshev in a window.** For `u ≥ 200`, `θ(e^{u+1}) − θ(e^{u−1}) ≥ e^u`. -/
theorem exp_le_theta_window {u : ℝ} (hu : 200 ≤ u) :
    Real.exp u ≤ θ (Real.exp (u + 1)) - θ (Real.exp (u - 1)) := by
  set E := Real.exp u with hEdef
  set H := Real.exp (u / 2) with hHdef
  set e := Real.exp 1 with hedef
  set L := Real.log 2 with hLdef
  have hepos : 0 < e := Real.exp_pos 1
  have he_lo : 2.7182818283 < e := by rw [hedef]; exact Real.exp_one_gt_d9
  have he_hi : e < 2.7182818286 := by rw [hedef]; exact Real.exp_one_lt_d9
  have hL_lo : 0.6931471803 < L := by rw [hLdef]; exact Real.log_two_gt_d9
  have hL_hi : L < 0.6931471808 := by rw [hLdef]; exact Real.log_two_lt_d9
  have hE0 : 0 < E := Real.exp_pos u
  have hH0 : 0 < H := Real.exp_pos _
  have hu0 : 0 ≤ u := by linarith
  have hHE : H ^ 2 = E := by
    rw [hHdef, hEdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have he1 : Real.exp (u + 1) = e * E := by rw [Real.exp_add, mul_comm]
  have hem1 : Real.exp (u - 1) = E / e := by rw [Real.exp_sub]
  have hlow := Chebyshev.theta_ge' (Real.one_le_exp (by linarith : (0 : ℝ) ≤ u + 1))
  have hup := Chebyshev.theta_le_log4_mul_x (Real.exp_pos (u - 1)).le
  have hsqrt : √(Real.exp (u + 1)) = Real.exp (1 / 2) * H := by
    rw [← Real.exp_half, hHdef, ← Real.exp_add]; congr 1; ring
  have hloge : Real.log (Real.exp (u + 1)) = u + 1 := Real.log_exp _
  have hlog2 : Real.log (Real.exp (u + 1) + 2) ≤ u + 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h2 : Real.exp (u + 2) = e * Real.exp (u + 1) := by
      rw [hedef, ← Real.exp_add]; ring_nf
    have hX : e ≤ Real.exp (u + 1) := by
      rw [hedef]; exact Real.exp_le_exp.mpr (by linarith)
    rw [h2]
    have := mul_le_mul (show (1.7 : ℝ) ≤ e - 1 by linarith)
      (show (2.7 : ℝ) ≤ Real.exp (u + 1) by linarith) (by norm_num) (by linarith)
    linarith
  have hlog4 : Real.log 4 = 2 * L := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hhalf : Real.exp (1 / 2) ≤ 2 := by
    have hsq : Real.exp (1 / 2) ^ 2 = e := by
      rw [hedef, ← Real.exp_nat_mul]; norm_num
    by_contra h
    push Not at h
    have := mul_lt_mul h h.le (by norm_num) (Real.exp_pos _).le
    linarith
  have hH : 24 * (u + 1) ≤ H := by
    have h1 := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ u / 2)
    have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ u - 200) hu0
    rw [← hHdef] at h1
    linarith
  have hE : 6 * (u + 3) ≤ E := by
    have h1 := Real.quadratic_le_exp_of_nonneg hu0
    have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ u - 200) hu0
    rw [← hEdef] at h1
    linarith
  have hL1 : L ≤ 1 := by linarith
  have hL0 : 0 < L := by linarith
  have hconst : 4 / 3 * e ≤ L * (e ^ 2 - 2) := by
    have he2 : (5.38 : ℝ) ≤ e ^ 2 - 2 := by
      have := mul_le_mul he_lo.le he_lo.le (by norm_num) hepos.le
      linarith
    have hprod : (0.6931 : ℝ) * 5.38 ≤ L * (e ^ 2 - 2) :=
      mul_le_mul (by linarith) he2 (by norm_num) (by linarith)
    linarith
  -- the main term
  have h1 : 4 / 3 * E - L ≤ (Real.exp (u + 1) - 1) * L - Real.log 4 * Real.exp (u - 1) := by
    rw [he1, hem1, hlog4]
    have hq : 4 / 3 ≤ L * (e ^ 2 - 2) / e := by rw [le_div_iff₀ hepos]; linarith
    have : (e * E - 1) * L - 2 * L * (E / e) = E * (L * (e ^ 2 - 2) / e) - L := by
      field_simp; ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hq hE0.le
    linarith
  -- the error terms
  have h2 : 2 * √(Real.exp (u + 1)) * Real.log (Real.exp (u + 1)) ≤ E / 6 := by
    rw [hsqrt, hloge, ← hHE]
    have h0 : 0 ≤ H * (u + 1) := by positivity
    have h5 := mul_le_mul_of_nonneg_right hhalf h0
    have h6 := mul_le_mul_of_nonneg_left hH hH0.le
    linarith
  have h3 : Real.log (Real.exp (u + 1) + 2) + L ≤ E / 6 := by linarith
  linarith

/-- **The pole at the trivial fibre.** For `p ≥ e^{200}`, `c √p ≤ |T_0(log p)|`. -/
theorem mul_sqrt_le_trivial_fibreTrace {g : ℝ → ℝ} (hg0 : ∀ v, 0 ≤ g v) {c : ℝ} (hc : 0 ≤ c)
    (hgc : ∀ v, |v| ≤ 1 → c ≤ g v) {R : ℝ} (hR : 1 ≤ R) {p : ℕ} (hp : p.Prime)
    (hp200 : Real.exp 200 ≤ p) :
    c * √(p : ℝ) ≤ ‖fibreTrace g R (Real.log p) 0‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hu : 200 ≤ Real.log p := (Real.le_log_iff_exp_le hp0).mpr hp200
  refine le_trans ?_ (theta_window_le_trivial_fibreTrace hg0 hgc hR (Real.log p))
  have hsq : √(p : ℝ) = Real.exp (-(Real.log p / 2)) * Real.exp (Real.log p) := by
    rw [← Real.exp_add, show -(Real.log p / 2) + Real.log p = Real.log p / 2 by ring,
      Real.exp_half, Real.exp_log hp0]
  rw [hsq]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (exp_le_theta_window hu) (Real.exp_pos _).le) hc

/-- **The trivial fibre has trace exponent `½`.** Below `½` no constant bounds its traces. -/
theorem exists_prime_mul_rpow_lt_trivial_fibreTrace {g : ℝ → ℝ} (hg0 : ∀ v, 0 ≤ g v) {c : ℝ}
    (hc : 0 < c) (hgc : ∀ v, |v| ≤ 1 → c ≤ g v) {R : ℝ} (hR : 1 ≤ R) {a : ℝ} (ha : a < 1 / 2)
    (K : ℝ) :
    ∃ p : ℕ, p.Prime ∧ K * (p : ℝ) ^ a < ‖fibreTrace g R (Real.log p) 0‖ := by
  set δ := 1 / 2 - a with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hev : ∀ᶠ N : ℕ in atTop, Real.exp 200 ≤ (N : ℝ) ∧ |K| / c < (N : ℝ) ^ δ := by
    have h1 := (tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop
    exact (tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and (h1.eventually_gt_atTop _)
  obtain ⟨N, hN1, hN2⟩ := hev.exists
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  have hpN' : (N : ℝ) ≤ p := by exact_mod_cast hpN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨p, hp, ?_⟩
  have hpow : |K| / c < (p : ℝ) ^ δ :=
    hN2.trans_le (Real.rpow_le_rpow hN0 hpN' hδ0.le)
  have hsplit : √(p : ℝ) = (p : ℝ) ^ δ * (p : ℝ) ^ a := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp0, hδ]; ring_nf
  have hpa : 0 < (p : ℝ) ^ a := Real.rpow_pos_of_pos hp0 a
  calc K * (p : ℝ) ^ a ≤ |K| * (p : ℝ) ^ a := mul_le_mul_of_nonneg_right (le_abs_self K) hpa.le
    _ < c * (p : ℝ) ^ δ * (p : ℝ) ^ a := by
        have : |K| < c * (p : ℝ) ^ δ := by rwa [div_lt_iff₀ hc, mul_comm] at hpow
        exact mul_lt_mul_of_pos_right this hpa
    _ = c * √(p : ℝ) := by rw [hsplit]; ring
    _ ≤ ‖fibreTrace g R (Real.log p) 0‖ :=
        mul_sqrt_le_trivial_fibreTrace hg0 hc.le hgc hR hp (hN1.trans hpN')

/-! ### Constants against exponents -/

/-- The fibres whose traces at the primes are bounded by `K p^a`. -/
def traceConstantSet (g : ℝ → ℝ) (R K a : ℝ) : Set GaugeTorus :=
  {x | ∀ p : ℕ, p.Prime → ‖fibreTrace g R (Real.log p) x‖ ≤ K * (p : ℝ) ^ a}

/-- **Constants specialize.** The trace-constant sets are closed: the trace constant is lower
semicontinuous on the family. -/
theorem isClosed_traceConstantSet (g : ℝ → ℝ) (R K a : ℝ) : IsClosed (traceConstantSet g R K a) := by
  simp only [traceConstantSet, Set.setOf_forall]
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    isClosed_le (continuous_fibreTrace _ _ _).norm continuous_const

theorem traceConstantSet_mono (g : ℝ → ℝ) (R a : ℝ) : Monotone fun K => traceConstantSet g R K a :=
  fun _ _ hK _ hx p hp => (hx p hp).trans (mul_le_mul_of_nonneg_right hK (by positivity))

/-- Almost every fibre has a finite trace constant at every positive exponent. -/
theorem ae_exists_mem_traceConstantSet {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    {a : ℝ} (ha : 0 < a) : ∀ᵐ x ∂gaugeHaar, ∃ K : ℝ, x ∈ traceConstantSet g R K a := by
  filter_upwards [ae_norm_fibreTrace_le hg hR] with x hx
  obtain ⟨C, hC⟩ := hx a ha
  exact ⟨C, hC⟩

/-- The trace-constant sets exhaust the family in measure. -/
theorem tendsto_measure_traceConstantSet {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => gaugeHaar (traceConstantSet g R n a)) atTop (𝓝 1) := by
  have hmono : Monotone fun n : ℕ => traceConstantSet g R n a :=
    fun m n hmn => traceConstantSet_mono g R a (by exact_mod_cast hmn)
  have hmeas : MeasurableSet (⋃ n : ℕ, traceConstantSet g R n a) :=
    MeasurableSet.iUnion fun n => (isClosed_traceConstantSet g R n a).measurableSet
  have hae : ∀ᵐ x ∂gaugeHaar, x ∈ ⋃ n : ℕ, traceConstantSet g R n a := by
    filter_upwards [ae_exists_mem_traceConstantSet hg hR ha] with x hx
    obtain ⟨K, hK⟩ := hx
    obtain ⟨n, hn⟩ := exists_nat_ge K
    exact Set.mem_iUnion.mpr ⟨n, traceConstantSet_mono g R a hn hK⟩
  have hU : gaugeHaar (⋃ n : ℕ, traceConstantSet g R n a) = 1 :=
    (prob_compl_eq_zero_iff hmeas).mp (ae_iff.mp hae)
  rw [← hU]
  exact tendsto_measure_iUnion_atTop hmono

/-- **The trivial fibre is the jump.** For `0 < a < ½`: almost every fibre has a finite trace
constant at exponent `a`, each trace-constant set is closed, and no trace-constant set meets some
neighbourhood of the trivial fibre: the trace constants of the fibres tend to infinity at `ζ`. -/
theorem trivial_fibre_is_the_jump {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) (hg0 : ∀ v, 0 ≤ g v) {c : ℝ}
    (hc : 0 < c) (hgc : ∀ v, |v| ≤ 1 → c ≤ g v) {R : ℝ} (hR : 1 ≤ R) {a : ℝ} (ha0 : 0 < a)
    (ha : a < 1 / 2) :
    (∀ᵐ x ∂gaugeHaar, ∃ K : ℝ, x ∈ traceConstantSet g R K a) ∧
      ∀ K : ℝ, ∀ᶠ x in 𝓝 (0 : GaugeTorus), x ∉ traceConstantSet g R K a := by
  refine ⟨ae_exists_mem_traceConstantSet hg (by linarith) ha0, fun K => ?_⟩
  have hnot : (0 : GaugeTorus) ∉ traceConstantSet g R K a := by
    intro h
    obtain ⟨p, hp, hlt⟩ := exists_prime_mul_rpow_lt_trivial_fibreTrace hg0 hc hgc hR ha K
    exact absurd (h p hp) (not_le.mpr hlt)
  exact (isClosed_traceConstantSet g R K a).isOpen_compl.mem_nhds hnot

end GaloisForLFunctions.ArithmeticWeightTheory
