import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateFlowOnTheWindowAlgebra

/-!
# The tangent principle of the Tate family

The Tate family lies above its tangent at dimension zero:

* **Jordan's totient is multiplicative in every real dimension** (`isMultiplicative_jordanFun`) and
  nonnegative for `k ≥ 0` (`jordanTotient_nonneg`).
* **Tangent principle** (`jordanTotient_ge_tangent`): `J_k(n) ≥ [n = 1] + kΛ(n)` for `k ≥ 0`. At a prime
  power `J_k(p^a) = p^{k(a−1)}(p^k − 1) ≥ p^k − 1 ≥ k log p`; elsewhere `Λ = 0` and `J_k ≥ 0`.
* **For nonnegative tests** (`tateFunction_ge_tangent`): if every autocorrelation `∫H(u)H(u + log n)` of a
  window test is nonnegative (e.g. `H ≥ 0`), then `τ_H(k) ≥ ‖H‖² + k⟨ρ_A(Λ)H, H⟩` for `k ≥ 0`.
* **Weil's form of a nonnegative test is bounded below by its Tate counts**
  (`weilQuad_ge_of_nonneg_tangent`): for `k > 0`,
  `Q(H) ≥ Ω_Γ‖H‖² + J_∞(H) + pole − (2/k)(τ_H(k) − ‖H‖²)`;
  at `k = β + 1` the bound reads Weil's arithmetic term against the projective point counts
  `φ(m)#ℙ^β(ℤ/m)` of the window.
* **Every test is dominated by the counts of its modulus** (`weilQuad_ge_absTateCount`): replacing the
  autocorrelations of `H` by those of `|H|` only raises the arithmetic term, so for every window test and
  every `k > 0`, `Q(H) ≥ Ω_Γ‖H‖² + J_∞(H) + pole − (2/k)(τ^{|H|}(k) − ‖H‖²)`, where
  `τ^{|H|}(k) = Σ_{n ≤ e^A} J_k(n) n^{−1/2}∫|H(u)||H(u + log n)|` is the Tate count of the modulus.

Nonnegative tests are where the Markov part of Weil's form is smallest (normal contractions lower
it); on them the non-Tate piece is controlled by the Tate pieces in every positive dimension, with
equality in the limit `k → 0`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole
open ArithmeticDegenerationTheory

/-! ### Multiplicativity and positivity in real dimension -/

theorem isMultiplicative_tateTwist_zeta (s : ℝ) :
    (tateTwist s (ArithmeticFunction.zeta : ArithmeticFunction ℝ)).IsMultiplicative := by
  refine ⟨by simp [tateTwist_apply], fun {m n} _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [tateTwist_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tateTwist_apply]
  simp only [tateTwist_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hm.ne', ArithmeticFunction.zeta_apply_ne hn.ne',
    ArithmeticFunction.zeta_apply_ne (Nat.mul_ne_zero hm.ne' hn.ne'), Nat.cast_one, one_mul,
    Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Jordan's totient is multiplicative in every real dimension.** -/
theorem isMultiplicative_jordanFun (k : ℝ) : (jordanFun k).IsMultiplicative := by
  rw [jordanFun_eq]
  exact (isMultiplicative_tateTwist_zeta _).mul ArithmeticFunction.isMultiplicative_moebius.intCast

theorem jordanTotient_prime_pow_nonneg {p : ℕ} (hp : p.Prime) {k : ℝ} (hk : 0 ≤ k) {a : ℕ}
    (ha : 1 ≤ a) : 0 ≤ jordanTotient k (p ^ a) := by
  rw [jordanTotient_prime_pow hp k ha]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (sub_nonneg.mpr (Real.one_le_rpow hp1 hk))

/-- **Jordan's totient is nonnegative in nonnegative dimension.** -/
theorem jordanTotient_nonneg {k : ℝ} (hk : 0 ≤ k) (n : ℕ) : 0 ≤ jordanTotient k n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha => exact jordanTotient_prime_pow_nonneg hp hk ha
  | zero => simp [jordanTotient]
  | one => rw [jordanTotient_one]; norm_num
  | coprime a b _ _ hab iha ihb =>
    have h := (isMultiplicative_jordanFun k).map_mul_of_coprime hab
    simp only [jordanFun_apply] at h
    rw [h]
    exact mul_nonneg iha ihb

/-! ### The tangent principle -/

/-- **The tangent principle**: `J_k(n) ≥ [n = 1] + kΛ(n)` for `k ≥ 0`. -/
theorem jordanTotient_ge_tangent {k : ℝ} (hk : 0 ≤ k) (n : ℕ) :
    (if n = 1 then 1 else 0) + k * ArithmeticFunction.vonMangoldt n ≤ jordanTotient k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [jordanTotient]
  by_cases h1 : n = 1
  · subst h1; simp [jordanTotient_one]
  rw [if_neg h1, zero_add]
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [ArithmeticFunction.vonMangoldt_apply_pow ha.ne', ArithmeticFunction.vonMangoldt_apply_prime hp,
      jordanTotient_prime_pow hp k ha]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    -- `p^k − 1 ≥ k log p` and `p^{k(a−1)} ≥ 1`
    have hexp : k * Real.log p + 1 ≤ (p : ℝ) ^ k := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]; exact Real.add_one_le_exp _
    have hpow : 1 ≤ (p : ℝ) ^ (k * ((a - 1 : ℕ) : ℝ)) :=
      Real.one_le_rpow hp1 (mul_nonneg hk (Nat.cast_nonneg _))
    have hsub : 0 ≤ (p : ℝ) ^ k - 1 := sub_nonneg.mpr (Real.one_le_rpow hp1 hk)
    nlinarith
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, mul_zero]
    exact jordanTotient_nonneg hk n

/-! ### Nonnegative tests -/

variable {A : ℝ} {H : ℝ → ℝ}

/-- `⟨ρ_A(Λ)H, H⟩ = Σ_{n ≤ e^A} Λ(n)n^{−1/2}∫H(u)H(u + log n)`. -/
theorem integral_windowRep_vonMangoldt_eq_sum (hH : IsWindowTest A H) :
    ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u =
      ∑ n ∈ Finset.Icc 1 (windowLevel A), ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        ∫ u, H u * H (u + Real.log n) := by
  rw [integral_windowRep_vonMangoldt_mul hH]
  rcases Nat.eq_zero_or_pos (windowLevel A) with h0 | hpos
  · rw [h0]; simp
  · rw [← Finset.sum_Ioc_add_eq_sum_Icc (by omega : 1 ≤ windowLevel A)]
    simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul, add_zero]
    refine Finset.sum_congr ?_ fun n _ => by rw [primeJumpWeight]
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- **The tangent principle for the Tate function**: for a window test with nonnegative
autocorrelations and `k ≥ 0`, `τ_H(k) ≥ ‖H‖² + k⟨ρ_A(Λ)H, H⟩`. -/
theorem tateFunction_ge_tangent (hH : IsWindowTest A H)
    (hc : ∀ n ∈ Finset.Icc 1 (windowLevel A), 0 ≤ ∫ u, H u * H (u + Real.log n))
    {k : ℝ} (hk : 0 ≤ k) :
    (∫ u, H u ^ 2) + k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u ≤
      tateFunction A H k := by
  rw [tateFunction_eq hH, integral_windowRep_vonMangoldt_eq_sum hH, Finset.mul_sum]
  -- the `n = 1` term is `‖H‖²`
  have hone : (∫ u, H u ^ 2) = ∑ n ∈ Finset.Icc 1 (windowLevel A),
      (if n = 1 then 1 else 0) / Real.sqrt n * ∫ u, H u * H (u + Real.log n) := by
    rcases Nat.eq_zero_or_pos (windowLevel A) with h0 | hpos
    · rw [h0]
      simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty]
      have hz : ∀ u, H u = 0 := fun u => hH.vanish u fun hm => by
        have : A < 0 := by
          by_contra h
          have := Nat.one_le_floor_iff _ |>.mpr (Real.one_le_exp (not_lt.mp h))
          rw [windowLevel] at h0; omega
        linarith [hm.1, hm.2]
      simp [hz]
    · rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hpos⟩) fun n _ hn => by
        rw [if_neg hn, zero_div, zero_mul]]
      simp [sq]
  rw [hone, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n hn => ?_
  have hs : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have ht := jordanTotient_ge_tangent hk n
  have hcn := hc n hn
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  nlinarith [mul_le_mul_of_nonneg_right ht (mul_nonneg hs hcn)]

/-- Nonnegative tests have nonnegative autocorrelations. -/
theorem autocorr_nonneg_of_nonneg (hpos : ∀ u, 0 ≤ H u) (ℓ : ℝ) :
    0 ≤ ∫ u, H u * H (u + ℓ) := integral_nonneg fun u => mul_nonneg (hpos u) (hpos _)

/-- **Weil's form of a nonnegative test is bounded below by its Tate counts**: for `k > 0`,
`Q(H) ≥ Ω_Γ‖H‖² + J_∞(H) + pole − (2/k)(τ_H(k) − ‖H‖²)`. -/
theorem weilQuad_ge_of_nonneg_tangent (hH : IsWindowTest A H) (hpos : ∀ u, 0 ≤ H u) {k : ℝ}
    (hk : 0 < k) :
    EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
        (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) -
          2 / k * (tateFunction A H k - ∫ u, H u ^ 2) ≤ weilQuad H := by
  have ht := tateFunction_ge_tangent hH (fun n _ => autocorr_nonneg_of_nonneg hpos _) hk.le
  rw [weilQuad_eq_windowRep hH]
  have hdiv : ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u ≤
      (tateFunction A H k - ∫ u, H u ^ 2) / k := by
    rw [le_div_iff₀ hk]; linarith
  have : 2 / k * (tateFunction A H k - ∫ u, H u ^ 2) =
      2 * ((tateFunction A H k - ∫ u, H u ^ 2) / k) := by ring
  rw [this]
  linarith

/-! ### All tests: the counts of the modulus -/

/-- The **Tate count of the modulus** `τ^{|H|}(k) = Σ_{n ≤ e^A} J_k(n) n^{−1/2} ∫|H(u)||H(u + log n)|`. -/
def absTateCount (A : ℝ) (H : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (windowLevel A), jordanTotient k n / Real.sqrt n *
    ∫ u, |H u| * |H (u + Real.log n)|

theorem integrable_mul_shift (hH : IsWindowTest A H) (ℓ : ℝ) :
    MeasureTheory.Integrable fun u => H u * H (u + ℓ) :=
  (hH.continuous.mul (hH.continuous.comp (continuous_add_const ℓ))).integrable_of_hasCompactSupport
    (hH.hasCompactSupport.mul_right)

theorem integrable_abs_mul_shift (hH : IsWindowTest A H) (ℓ : ℝ) :
    MeasureTheory.Integrable fun u => |H u| * |H (u + ℓ)| :=
  (hH.continuous.abs.mul (hH.continuous.comp (continuous_add_const ℓ)).abs).integrable_of_hasCompactSupport
    (hH.hasCompactSupport.abs.mul_right)

/-- **Weil's form is bounded below by the Tate counts of the modulus**: for every window test and
every `k > 0`, `Q(H) ≥ Ω_Γ‖H‖² + J_∞(H) + pole − (2/k)(τ^{|H|}(k) − ‖H‖²)`. -/
theorem weilQuad_ge_absTateCount (hH : IsWindowTest A H) {k : ℝ} (hk : 0 < k) :
    EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
        (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) -
          2 / k * (absTateCount A H k - ∫ u, H u ^ 2) ≤ weilQuad H := by
  -- `⟨ρΛH,H⟩ ≤ (τ^{|H|}(k) − ‖H‖²)/k`, term by term
  have hterm : ∀ n ∈ Finset.Icc 1 (windowLevel A),
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * (∫ u, H u * H (u + Real.log n)) ≤
        ((jordanTotient k n - if n = 1 then 1 else 0) / k) / Real.sqrt n *
          ∫ u, |H u| * |H (u + Real.log n)| := fun n _ => by
    have hs : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hle : (∫ u, H u * H (u + Real.log n)) ≤ ∫ u, |H u| * |H (u + Real.log n)| :=
      MeasureTheory.integral_mono (integrable_mul_shift hH _) (integrable_abs_mul_shift hH _)
        fun u => by rw [← abs_mul]; exact le_abs_self _
    have hpos : 0 ≤ ∫ u, |H u| * |H (u + Real.log n)| :=
      MeasureTheory.integral_nonneg fun u => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have ht := jordanTotient_ge_tangent hk.le n
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ (jordanTotient k n - if n = 1 then 1 else 0) / k := by
      rw [le_div_iff₀ hk]; linarith
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    rw [div_eq_mul_inv, div_eq_mul_inv _ (Real.sqrt _)]
    calc ArithmeticFunction.vonMangoldt n * (Real.sqrt n)⁻¹ * (∫ u, H u * H (u + Real.log n))
        ≤ ArithmeticFunction.vonMangoldt n * (Real.sqrt n)⁻¹ *
            ∫ u, |H u| * |H (u + Real.log n)| :=
          mul_le_mul_of_nonneg_left hle (mul_nonneg hΛ0 hs)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΛ hs) hpos
  -- the `n = 1` part of the counts is `‖H‖²`
  have hone : (∑ n ∈ Finset.Icc 1 (windowLevel A), (if n = 1 then (1 : ℝ) else 0) / Real.sqrt n *
      ∫ u, |H u| * |H (u + Real.log n)|) = ∫ u, H u ^ 2 := by
    rcases Nat.eq_zero_or_pos (windowLevel A) with h0 | hpos
    · rw [h0]
      simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty]
      have hz : ∀ u, H u = 0 := fun u => hH.vanish u fun hm => by
        have : A < 0 := by
          by_contra h
          have := Nat.one_le_floor_iff _ |>.mpr (Real.one_le_exp (not_lt.mp h))
          rw [windowLevel] at h0; omega
        linarith [hm.1, hm.2]
      simp [hz]
    · rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hpos⟩) fun n _ hn => by
        rw [if_neg hn, zero_div, zero_mul]]
      simp only [if_true, Nat.cast_one, Real.sqrt_one, div_one, one_mul, Real.log_one, add_zero]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by
        show |H u| * |H u| = H u ^ 2
        rw [← sq, sq_abs])
  have hsum : ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u ≤
      (absTateCount A H k - ∫ u, H u ^ 2) / k := by
    rw [integral_windowRep_vonMangoldt_eq_sum hH]
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [absTateCount, ← hone, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [weilQuad_eq_windowRep hH]
  have : 2 / k * (absTateCount A H k - ∫ u, H u ^ 2) =
      2 * ((absTateCount A H k - ∫ u, H u ^ 2) / k) := by ring
  rw [this]
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
