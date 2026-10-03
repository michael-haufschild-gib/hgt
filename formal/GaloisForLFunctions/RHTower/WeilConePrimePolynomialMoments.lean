import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Large values of prime-supported Dirichlet polynomials

Let `a` be supported on primes `p ≤ N` and `E_a(z) = Σ a(n) n^{−z}`.  On the line
`Re z = ½ − d`, with `W = Σ |a(n)|² n^{2d−1}`, the `k`-th moment bound
`∫_{T₁}^{T₂} |E_a|^{2k} ≤ (T₂ − T₁ + 8N^k(1 + log N^k)) k! W^k` and Markov's inequality give

`|{τ ∈ (T₁, T₂] : |E_a(½ − d + iτ)| ≥ V}| ≤ 2(T₂ − T₁) · e√k (kW/(eV²))^k`

whenever `8N^k(1 + log N^k) ≤ T₂ − T₁` (`measureReal_large_primePoly_le`).  The factor
`(kW/(eV²))^k` comes from the Stirling bound `k! ≤ e√k (k/e)^k` (`factorial_le_stirling`).  With
`k ≈ V²/W` it is the Gaussian tail `e^{−V²/W}`.
-/

open Complex Set MeasureTheory

namespace RHTower

namespace WeilConeMoments

noncomputable section

/-- **Stirling's upper bound** `k! ≤ e √k (k/e)^k` for `k ≥ 1`. -/
theorem factorial_le_stirling {k : ℕ} (hk : 1 ≤ k) :
    (k.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt k * (k / Real.exp 1) ^ k := by
  have hanti := Stirling.stirlingSeq'_antitone (show 0 ≤ k - 1 by omega)
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Nat.sub_add_cancel hk] at hanti
  rw [Stirling.stirlingSeq_one] at hanti
  have hpos : 0 < Real.sqrt (2 * k : ℝ) * (k / Real.exp 1) ^ k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  unfold Stirling.stirlingSeq at hanti
  rw [div_le_iff₀ hpos] at hanti
  have hs : Real.sqrt (2 * k : ℝ) = Real.sqrt 2 * Real.sqrt k := by
    rw [Real.sqrt_mul (by norm_num)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  calc (k.factorial : ℝ) ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt (2 * k : ℝ) * (k / Real.exp 1) ^ k) :=
        hanti
    _ = Real.exp 1 * Real.sqrt k * (k / Real.exp 1) ^ k := by
        rw [hs]; field_simp

theorem continuous_edPoly_displaced (a : ℕ → ℂ) (N : ℕ) (d : ℝ) :
    Continuous fun τ : ℝ => edPoly a (Finset.Icc 1 N) (displacedLinePt d τ) := by
  have h := differentiable_edPoly a (s := Finset.Icc 1 N) fun n hn => (Finset.mem_Icc.mp hn).1
  exact h.continuous.comp (by unfold displacedLinePt; fun_prop)

/-- **Markov's inequality for a high moment.**  For `a` supported on primes `p ≤ N`, `V > 0` and
`8N^k(1 + log N^k) ≤ T₂ − T₁`, the set of heights in `(T₁, T₂]` where `|E_a(½ − d + iτ)| ≥ V` has
measure at most `2(T₂ − T₁) k! W^k / V^{2k}`. -/
theorem measureReal_large_primePoly_le_factorial {a : ArithmeticFunction ℂ} {N : ℕ}
    (ha : ∀ k, a k ≠ 0 → k.Prime) (haN : ∀ k, a k ≠ 0 → k ≤ N) (d : ℝ) {k : ℕ} (hk : 1 ≤ k)
    {T₁ T₂ V : ℝ} (hT : T₁ ≤ T₂) (hV : 0 < V)
    (hN : 8 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log (N ^ k : ℕ)) ≤ T₂ - T₁) :
    (volume.restrict (Ioc T₁ T₂)).real
        {τ | V ≤ ‖edPoly (⇑a) (Finset.Icc 1 N) (displacedLinePt d τ)‖} ≤
      2 * (T₂ - T₁) * (k.factorial *
        (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1)) ^ k) / V ^ (2 * k) := by
  set E : ℝ → ℂ := fun τ => edPoly (⇑a) (Finset.Icc 1 N) (displacedLinePt d τ) with hE
  set W : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) with hW
  have hEc : Continuous E := continuous_edPoly_displaced (⇑a) N d
  have hmom := integral_norm_edPoly_pow_displaced_le ha haN d k T₁ T₂ hT
  rw [intervalIntegral.integral_of_le hT] at hmom
  set f : ℝ → ℝ := fun τ => ‖E τ ^ k‖ ^ 2 with hf
  have hfc : Continuous f := ((hEc.pow k).norm).pow 2
  have hfint : Integrable f (volume.restrict (Ioc T₁ T₂)) :=
    (hfc.integrableOn_Icc (a := T₁) (b := T₂)).mono_set Ioc_subset_Icc_self
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ioc T₁ T₂))
    (Filter.Eventually.of_forall fun τ => by positivity) hfint (V ^ (2 * k))
  have hset : {τ | V ≤ ‖E τ‖} = {τ | V ^ (2 * k) ≤ f τ} := by
    ext τ
    simp only [mem_setOf_eq, hf, norm_pow, ← pow_mul, mul_comm k 2]
    constructor
    · intro h; exact pow_le_pow_left₀ hV.le h _
    · intro h
      by_contra hlt
      push Not at hlt
      have := pow_lt_pow_left₀ hlt (norm_nonneg _) (show 2 * k ≠ 0 by omega)
      linarith
  rw [hset]
  have hVp : 0 < V ^ (2 * k) := by positivity
  rw [le_div_iff₀ hVp, mul_comm]
  refine hmk.trans (hmom.trans ?_)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun n _ => by positivity
  have hkW : 0 ≤ (k.factorial : ℝ) * W ^ k := by positivity
  have hle : T₂ - T₁ + 8 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log (N ^ k : ℕ)) ≤ 2 * (T₂ - T₁) := by
    linarith
  calc (T₂ - T₁ + 8 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log (N ^ k : ℕ))) * (k.factorial * W ^ k)
      ≤ 2 * (T₂ - T₁) * (k.factorial * W ^ k) := mul_le_mul_of_nonneg_right hle hkW
    _ = _ := rfl

/-- **The Gaussian form of the large-value bound.**  Under the hypotheses of
`measureReal_large_primePoly_le_factorial`, for `k ≥ 1`:
`|{|E_a| ≥ V}| ≤ 2e√k (T₂ − T₁)(kW/(eV²))^k`. -/
theorem measureReal_large_primePoly_le {a : ArithmeticFunction ℂ} {N : ℕ}
    (ha : ∀ k, a k ≠ 0 → k.Prime) (haN : ∀ k, a k ≠ 0 → k ≤ N) (d : ℝ) {k : ℕ} (hk : 1 ≤ k)
    {T₁ T₂ V : ℝ} (hT : T₁ ≤ T₂) (hV : 0 < V)
    (hN : 8 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log (N ^ k : ℕ)) ≤ T₂ - T₁) :
    (volume.restrict (Ioc T₁ T₂)).real
        {τ | V ≤ ‖edPoly (⇑a) (Finset.Icc 1 N) (displacedLinePt d τ)‖} ≤
      2 * Real.exp 1 * Real.sqrt k * (T₂ - T₁) *
        (k * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1)) /
          (Real.exp 1 * V ^ 2)) ^ k := by
  set W : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun n _ => by positivity
  refine (measureReal_large_primePoly_le_factorial ha haN d hk hT hV hN).trans ?_
  have hfac := factorial_le_stirling hk
  have hT0 : 0 ≤ T₂ - T₁ := by linarith
  have he := Real.exp_pos 1
  have hVp : 0 < V ^ (2 * k) := by positivity
  rw [div_le_iff₀ hVp]
  have e1 : (k * W / (Real.exp 1 * V ^ 2)) ^ k * V ^ (2 * k) = (k / Real.exp 1) ^ k * W ^ k := by
    rw [div_pow, mul_pow, mul_pow, div_pow, ← pow_mul, mul_comm 2 k]
    field_simp
  calc 2 * (T₂ - T₁) * (k.factorial * W ^ k)
      ≤ 2 * (T₂ - T₁) * ((Real.exp 1 * Real.sqrt k * (k / Real.exp 1) ^ k) * W ^ k) := by
        gcongr
    _ = 2 * Real.exp 1 * Real.sqrt k * (T₂ - T₁) * ((k / Real.exp 1) ^ k * W ^ k) := by ring
    _ = 2 * Real.exp 1 * Real.sqrt k * (T₂ - T₁) *
          ((k * W / (Real.exp 1 * V ^ 2)) ^ k * V ^ (2 * k)) := by rw [e1]
    _ = _ := by ring

end

end WeilConeMoments

end RHTower
