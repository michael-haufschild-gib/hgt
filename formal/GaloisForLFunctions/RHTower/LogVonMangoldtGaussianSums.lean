import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.VonMangoldtLogHarmonicSummatory

/-!
# Gaussian sums of `ℓ = (Λ · log) ⋆ 1` at rational frequencies

`ℓ(n) = Σ_{ab = n} Λ(a) log a` is the coefficient of `ζ(w)·(ζ'/ζ)'(w)`; `0 ≤ ℓ(n) ≤ log² n`.
With `W_T(y) = e^{−4π²y²/T²}`:

* **Layers** (`sum_mul_weight_le_layers`): for `c ≥ 0` with `Σ_{a ≤ m} c(a) ≤ K m (log m + 1)^k`
  (`k ≤ 2`) and a weight `0 ≤ φ ≤ min(1, u⁻²)`, `Σ_{a ≤ N} c(a) φ(a/X) ≤ 48 K X (log X + 1)^k` for
  `X ≥ 1`.
* **Rational phases** (`exists_abs_sum_logVM_cos_le`): for `r = p/q` in lowest terms with `q ≥ 2`,
  `|Σ_{n ≤ N} ℓ(n) cos(2πnr) W_T(nr)| ≤ C T (log T + 1)` uniformly in `N`.  Write
  `ℓ = (Λ·log) ⋆ 1`.  For `q ∤ a`, the inner sum over `b` is bounded by Abel summation, since
  `|sin(πap/q)| ≥ 2/q`.  For `q | a`, `a` is a power of the least prime factor of `q`.
* **The main term** (`exists_sum_logVM_gaussW_ge`): `Σ_{n ≤ N} ℓ(n) W_T(nr) ≥ c (T/r) log²(T/r)`
  for an integer `r`, `N ≥ T/r` and `T/r` large, from `Σ_{a ≤ M} Λ(a) log a / a = ½ log² M + O(log M)`.
-/

open Finset ArithmeticFunction

namespace RHTower.GaussZeroSum

noncomputable section

/-- `ℓ(n) = Σ_{ab = n} Λ(a) log a`. -/
def logVM (n : ℕ) : ℝ := ∑ x ∈ n.divisorsAntidiagonal, vonMangoldt x.1 * Real.log x.1

theorem logVM_nonneg (n : ℕ) : 0 ≤ logVM n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg _)

theorem logVM_le_log_sq (n : ℕ) : logVM n ≤ Real.log n ^ 2 := by
  unfold logVM
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => vonMangoldt a * Real.log a)]
  calc ∑ i ∈ n.divisors, vonMangoldt i * Real.log i
      ≤ ∑ i ∈ n.divisors, vonMangoldt i * Real.log n := by
        refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
        have hn : n ≠ 0 := (Nat.mem_divisors.mp hi).2
        have hi0 : 0 < i := Nat.pos_of_mem_divisors hi
        exact Real.log_le_log (by exact_mod_cast hi0)
          (by exact_mod_cast Nat.divisor_le hi)
    _ = Real.log n ^ 2 := by rw [← Finset.sum_mul, vonMangoldt_sum, sq]

/-- **Summatory swap**: `Σ_{n ≤ N} ℓ(n) f(n) = Σ_{a ≤ N} Λ(a) log a Σ_{b ≤ N/a} f(ab)`. -/
theorem sum_logVM_mul (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, logVM n * f n =
      ∑ a ∈ Icc 1 N, vonMangoldt a * Real.log a * ∑ b ∈ Icc 1 (N / a), f (a * b) := by
  have h := Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun a b => vonMangoldt a * Real.log a * f (a * b)) N
  rw [show ∑ a ∈ Icc 1 N, vonMangoldt a * Real.log a * ∑ b ∈ Icc 1 (N / a), f (a * b) =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 (N / a), vonMangoldt a * Real.log a * f (a * b) from
    Finset.sum_congr rfl (fun a _ => Finset.mul_sum _ _ _), ← h]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold logVM
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]

/-! ## Layers -/

/-- `Σ_{j < n} (j + 1)² 2^{−j} = 12 − (n² + 4n + 6) 2^{1−n}`. -/
theorem sum_sq_succ_div_two_pow (n : ℕ) :
    ∑ j ∈ range n, ((j : ℝ) + 1) ^ 2 / 2 ^ j = 12 - ((n : ℝ) ^ 2 + 4 * n + 6) * 2 / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem sum_sq_succ_div_two_pow_le (n : ℕ) :
    ∑ j ∈ range n, ((j : ℝ) + 1) ^ 2 / 2 ^ j ≤ 12 := by
  rw [sum_sq_succ_div_two_pow]
  have : 0 ≤ ((n : ℝ) ^ 2 + 4 * n + 6) * 2 / 2 ^ n := by positivity
  linarith

/-- A weight bounded by `min(1, u⁻²)` is dominated by the dyadic layers `Σ_j w_j 1[u ≤ 2^j]`,
`w₀ = 1`, `w_j = 4^{1−j}`. -/
theorem weight_le_layers {φ : ℝ → ℝ} (hφ1 : ∀ u, φ u ≤ 1) (hφ2 : ∀ u, 0 < u → φ u * u ^ 2 ≤ 1)
    {u : ℝ} (hu : 0 < u) {J : ℕ} (huJ : u ≤ 2 ^ J) :
    φ u ≤ ∑ j ∈ range (J + 1), (4 : ℝ) / 4 ^ j * (if u ≤ 2 ^ j then 1 else 0) := by
  classical
  have hterm : ∀ j ∈ range (J + 1), 0 ≤ (4 : ℝ) / 4 ^ j * (if u ≤ 2 ^ j then 1 else 0) := by
    intro j _; split_ifs <;> positivity
  -- the least layer containing `u`
  obtain ⟨j, hjJ, hj, hmin⟩ : ∃ j, j ≤ J ∧ u ≤ 2 ^ j ∧ ∀ i < j, ¬ u ≤ 2 ^ i := by
    have hex : ∃ j : ℕ, u ≤ (2 : ℝ) ^ j := ⟨J, huJ⟩
    exact ⟨Nat.find hex, Nat.find_min' hex huJ, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hle : φ u ≤ (4 : ℝ) / 4 ^ j := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact (hφ1 u).trans (by norm_num)
    · have hlow : 2 ^ (j - 1) < u := by
        have := hmin (j - 1) (by omega)
        exact lt_of_not_ge this
      have h2 : (0 : ℝ) < 2 ^ (j - 1) := by positivity
      have hsq : (2 : ℝ) ^ (j - 1) * 2 ^ (j - 1) < u ^ 2 := by nlinarith
      have hpow : (4 : ℝ) ^ j = 4 * ((2 : ℝ) ^ (j - 1) * 2 ^ (j - 1)) := by
        rw [← pow_add, show j - 1 + (j - 1) = 2 * (j - 1) by ring, pow_mul]
        norm_num
        rw [← pow_succ']
        congr 1
        omega
      have hφu := hφ2 u hu
      have hu2 : 0 < u ^ 2 := by positivity
      rw [hpow, div_mul_eq_div_div, div_self (by norm_num : (4 : ℝ) ≠ 0)]
      rw [le_div_iff₀ (by positivity)]
      have hφ0 : φ u ≤ 1 / u ^ 2 := by rw [le_div_iff₀ hu2]; exact hφu
      rcases le_or_gt 0 (φ u) with h | h
      · exact (mul_le_mul_of_nonneg_left hsq.le h).trans hφu
      · have : φ u * (2 ^ (j - 1) * 2 ^ (j - 1)) < 0 := mul_neg_of_neg_of_pos h (by positivity)
        linarith
  calc φ u ≤ (4 : ℝ) / 4 ^ j * (if u ≤ 2 ^ j then 1 else 0) := by rw [if_pos hj, mul_one]; exact hle
    _ ≤ _ := Finset.single_le_sum hterm (mem_range.mpr (by omega))

/-- **Layer bound.**  For `c ≥ 0` with `Σ_{a ≤ m} c(a) ≤ K m (log m + 1)^k`, `k ≤ 2`, and a weight
`0 ≤ φ ≤ min(1, u⁻²)`: `Σ_{a ≤ N} c(a) φ(a/X) ≤ 48 K X (log X + 1)^k` for `X ≥ 1`. -/
theorem sum_mul_weight_le_layers {c : ℕ → ℝ} (hc : ∀ a, 0 ≤ c a) {K : ℝ} (hK : 0 ≤ K) {k : ℕ}
    (hk : k ≤ 2) (hpart : ∀ m : ℕ, ∑ a ∈ Icc 1 m, c a ≤ K * m * (Real.log m + 1) ^ k)
    {φ : ℝ → ℝ} (hφ1 : ∀ u, φ u ≤ 1) (hφ2 : ∀ u, 0 < u → φ u * u ^ 2 ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (N : ℕ) :
    ∑ a ∈ Icc 1 N, c a * φ (a / X) ≤ 48 * K * X * (Real.log X + 1) ^ k := by
  classical
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  -- pointwise layers with `J = N`
  have hpt : ∀ a ∈ Icc 1 N, c a * φ (a / X) ≤
      ∑ j ∈ range (N + 1), c a * ((4 : ℝ) / 4 ^ j * (if (a : ℝ) / X ≤ 2 ^ j then 1 else 0)) := by
    intro a ha
    have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
    have hu : 0 < (a : ℝ) / X := by positivity
    have huJ : (a : ℝ) / X ≤ 2 ^ N := by
      rw [div_le_iff₀ hX0]
      have h1 : (a : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp ha).2
      have h2 : (N : ℝ) ≤ 2 ^ N := by exact_mod_cast (Nat.lt_two_pow_self).le
      nlinarith
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (weight_le_layers hφ1 hφ2 hu huJ) (hc a)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_comm]
  -- each layer
  have hlayer : ∀ j ∈ range (N + 1),
      ∑ a ∈ Icc 1 N, c a * ((4 : ℝ) / 4 ^ j * (if (a : ℝ) / X ≤ 2 ^ j then 1 else 0)) ≤
        4 * K * X * (Real.log X + 1) ^ k * (((j : ℝ) + 1) ^ 2 / 2 ^ j) := by
    intro j _
    set m : ℕ := ⌊(2 : ℝ) ^ j * X⌋₊ with hm
    have hjX : (1 : ℝ) ≤ 2 ^ j * X := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have hm1 : 1 ≤ m := by rw [hm]; exact Nat.one_le_floor_iff _ |>.mpr hjX
    have hmle : (m : ℝ) ≤ 2 ^ j * X := Nat.floor_le (by positivity)
    have hsub : ∑ a ∈ Icc 1 N, c a * (if (a : ℝ) / X ≤ 2 ^ j then 1 else 0) ≤
        ∑ a ∈ Icc 1 m, c a := by
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hc a)
      intro a ha
      rw [mem_filter, mem_Icc] at ha
      rw [mem_Icc]
      refine ⟨ha.1.1, ?_⟩
      rw [hm]
      apply Nat.le_floor
      have := ha.2
      rw [div_le_iff₀ hX0] at this
      linarith
    have hpartm := hpart m
    have hlogm : Real.log m + 1 ≤ ((j : ℝ) + 1) * (Real.log X + 1) := by
      have h1 : Real.log m ≤ Real.log (2 ^ j * X) :=
        Real.log_le_log (by exact_mod_cast hm1) hmle
      rw [Real.log_mul (by positivity) hX0.ne', Real.log_pow] at h1
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have hlogm0 : 0 ≤ Real.log m + 1 := by
      have := Real.log_natCast_nonneg m; linarith
    have hpow : (Real.log m + 1) ^ k ≤ ((j : ℝ) + 1) ^ 2 * (Real.log X + 1) ^ k := by
      calc (Real.log m + 1) ^ k ≤ (((j : ℝ) + 1) * (Real.log X + 1)) ^ k :=
            pow_le_pow_left₀ hlogm0 hlogm k
        _ = ((j : ℝ) + 1) ^ k * (Real.log X + 1) ^ k := mul_pow _ _ _
        _ ≤ ((j : ℝ) + 1) ^ 2 * (Real.log X + 1) ^ k := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) hk
    have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
    calc ∑ a ∈ Icc 1 N, c a * ((4 : ℝ) / 4 ^ j * (if (a : ℝ) / X ≤ 2 ^ j then 1 else 0))
        = (4 : ℝ) / 4 ^ j * ∑ a ∈ Icc 1 N, c a * (if (a : ℝ) / X ≤ 2 ^ j then 1 else 0) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
      _ ≤ (4 : ℝ) / 4 ^ j * (K * m * (Real.log m + 1) ^ k) :=
          mul_le_mul_of_nonneg_left (hsub.trans hpartm) (by positivity)
      _ ≤ (4 : ℝ) / 4 ^ j * (K * (2 ^ j * X) * (((j : ℝ) + 1) ^ 2 * (Real.log X + 1) ^ k)) := by
          gcongr
      _ = 4 * K * X * (Real.log X + 1) ^ k * (((j : ℝ) + 1) ^ 2 / 2 ^ j) := by
          rw [h4]; field_simp
  refine (Finset.sum_le_sum hlayer).trans ?_
  rw [← Finset.mul_sum]
  have := sum_sq_succ_div_two_pow_le (N + 1)
  have hpos : 0 ≤ 4 * K * X * (Real.log X + 1) ^ k := by positivity
  calc 4 * K * X * (Real.log X + 1) ^ k * ∑ j ∈ range (N + 1), ((j : ℝ) + 1) ^ 2 / 2 ^ j
      ≤ 4 * K * X * (Real.log X + 1) ^ k * 12 := mul_le_mul_of_nonneg_left this hpos
    _ = 48 * K * X * (Real.log X + 1) ^ k := by ring

/-! ## Gaussian weights -/

/-- The weight `W_T(y) = e^{−4π²y²/T²}`. -/
def gaussW (T y : ℝ) : ℝ := Real.exp (-(4 * Real.pi ^ 2 * y ^ 2 / T ^ 2))

theorem gaussW_pos (T y : ℝ) : 0 < gaussW T y := Real.exp_pos _

/-- `e^{−u²} ≤ min(1, u⁻²)`. -/
theorem exp_neg_sq_le_one (u : ℝ) : Real.exp (-u ^ 2) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])

theorem exp_neg_sq_mul_sq_le_one (u : ℝ) : Real.exp (-u ^ 2) * u ^ 2 ≤ 1 := by
  have h := Real.add_one_le_exp (u ^ 2)
  have hpos := Real.exp_pos (u ^ 2)
  have he : Real.exp (-u ^ 2) * Real.exp (u ^ 2) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-u ^ 2)]

theorem gaussW_eq (T y : ℝ) (hT : T ≠ 0) :
    gaussW T y = Real.exp (-(2 * Real.pi * y / T) ^ 2) := by
  unfold gaussW
  congr 1
  field_simp
  ring

/-- `Σ_{b ≤ B} e^{−(b/X)²} ≤ 48 X` for every `X > 0`. -/
theorem sum_exp_neg_sq_le {X : ℝ} (hX : 0 < X) (B : ℕ) :
    ∑ b ∈ Icc 1 B, Real.exp (-((b : ℝ) / X) ^ 2) ≤ 48 * X := by
  rcases le_or_gt 1 X with hX1 | hX1
  · have h := sum_mul_weight_le_layers (c := fun _ => (1 : ℝ)) (fun _ => zero_le_one) zero_le_one
      (k := 0) (by norm_num) (fun m => by simp) (φ := fun u => Real.exp (-u ^ 2))
      exp_neg_sq_le_one (fun u _ => exp_neg_sq_mul_sq_le_one u) hX1 B
    simpa using h
  · -- `e^{−u²} ≤ u⁻²` and `Σ b⁻² ≤ 2`
    have hpt : ∀ b ∈ Icc 1 B, Real.exp (-((b : ℝ) / X) ^ 2) ≤ X ^ 2 * ((b : ℝ) ^ 2)⁻¹ := by
      intro b hb
      have hb0 : (0 : ℝ) < b := by exact_mod_cast (mem_Icc.mp hb).1
      have h := exp_neg_sq_mul_sq_le_one ((b : ℝ) / X)
      rw [show X ^ 2 * ((b : ℝ) ^ 2)⁻¹ = 1 / ((b : ℝ) / X) ^ 2 by field_simp]
      rw [le_div_iff₀ (by positivity)]
      exact h
    have hsum : ∑ b ∈ Icc 1 B, ((b : ℝ) ^ 2)⁻¹ ≤ 2 := by
      have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (B + 1)
      have hset : Icc 1 B = Ioo 0 (B + 1) := by
        ext b; simp only [mem_Icc, mem_Ioo]; omega
      rw [hset]
      simpa using h
    calc ∑ b ∈ Icc 1 B, Real.exp (-((b : ℝ) / X) ^ 2)
        ≤ ∑ b ∈ Icc 1 B, X ^ 2 * ((b : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum hpt
      _ = X ^ 2 * ∑ b ∈ Icc 1 B, ((b : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ X ^ 2 * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 48 * X := by nlinarith

/-- Chebyshev: `Σ_{a ≤ m} Λ(a) log a ≤ (log 4 + 4) m (log m + 1)`. -/
theorem sum_vonMangoldt_mul_log_le (m : ℕ) :
    ∑ a ∈ Icc 1 m, vonMangoldt a * Real.log a ≤ (Real.log 4 + 4) * m * (Real.log m + 1) ^ 1 := by
  have hpsi : ∑ a ∈ Icc 1 m, vonMangoldt a ≤ (Real.log 4 + 4) * m := by
    have h := Chebyshev.psi_le_const_mul_self (x := (m : ℝ)) (Nat.cast_nonneg m)
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast] at h
    have hsplit : ∑ a ∈ Icc 0 m, vonMangoldt a = ∑ a ∈ Icc 1 m, vonMangoldt a := by
      refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun x hx hnx => ?_).symm
      have : x = 0 := by
        rw [mem_Icc] at hx hnx; omega
      rw [this]; simp
    linarith
  have hlog : ∀ a ∈ Icc 1 m, vonMangoldt a * Real.log a ≤ vonMangoldt a * (Real.log m + 1) := by
    intro a ha
    refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (mem_Icc.mp ha).1
    have ham : (a : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp ha).2
    have := Real.log_le_log (by linarith) ham
    linarith
  calc ∑ a ∈ Icc 1 m, vonMangoldt a * Real.log a
      ≤ ∑ a ∈ Icc 1 m, vonMangoldt a * (Real.log m + 1) := Finset.sum_le_sum hlog
    _ = (∑ a ∈ Icc 1 m, vonMangoldt a) * (Real.log m + 1) := by rw [Finset.sum_mul]
    _ ≤ (Real.log 4 + 4) * m * (Real.log m + 1) := by
        apply mul_le_mul_of_nonneg_right hpsi
        have := Real.log_natCast_nonneg m; linarith
    _ = _ := by ring

/-! ## Abel summation for rational phases -/

/-- **Abel's inequality** on `[1, K]`. -/
theorem abel_abs_sum_mul_le {a w : ℕ → ℝ} {B : ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hB : ∀ j ≤ K, |∑ k ∈ Icc 1 j, a k| ≤ B)
    (hw0 : ∀ k, 1 ≤ k → k ≤ K → 0 ≤ w k) (hwanti : ∀ k, 1 ≤ k → k < K → w (k + 1) ≤ w k) :
    |∑ k ∈ Icc 1 K, a k * w k| ≤ B * w 1 := by
  have hparts : ∀ K' : ℕ, 1 ≤ K' → ∑ k ∈ Icc 1 K', a k * w k =
      (∑ k ∈ Icc 1 K', a k) * w K' +
        ∑ k ∈ Icc 1 (K' - 1), (∑ i ∈ Icc 1 k, a i) * (w k - w (k + 1)) := by
    intro K' hK'
    induction K' with
    | zero => omega
    | succ K'' ih =>
      rcases Nat.eq_zero_or_pos K'' with h0 | hpos
      · subst h0; simp
      · rw [Finset.sum_Icc_succ_top (by omega), ih hpos, Finset.sum_Icc_succ_top (by omega)]
        have : K'' + 1 - 1 = (K'' - 1) + 1 := by omega
        rw [this, Finset.sum_Icc_succ_top (by omega), show K'' - 1 + 1 = K'' by omega]
        ring
  have htel : ∀ K' : ℕ, ∑ k ∈ Icc 1 K', (w k - w (k + 1)) = w 1 - w (K' + 1) := by
    intro K'
    induction K' with
    | zero => simp
    | succ K'' ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
  rw [hparts K hK]
  have h1 : |(∑ k ∈ Icc 1 K, a k) * w K| ≤ B * w K := by
    rw [abs_mul, abs_of_nonneg (hw0 K hK le_rfl)]
    exact mul_le_mul_of_nonneg_right (hB K le_rfl) (hw0 K hK le_rfl)
  have h2 : |∑ k ∈ Icc 1 (K - 1), (∑ i ∈ Icc 1 k, a i) * (w k - w (k + 1))| ≤
      B * (w 1 - w K) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ k ∈ Icc 1 (K - 1),
        |(∑ i ∈ Icc 1 k, a i) * (w k - w (k + 1))| ≤ B * (w k - w (k + 1)) := by
      intro k hk
      have hk' := mem_Icc.mp hk
      have hd : 0 ≤ w k - w (k + 1) := sub_nonneg.mpr (hwanti k hk'.1 (by omega))
      rw [abs_mul, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right (hB k (by omega)) hd
    refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, htel, show K - 1 + 1 = K by omega]
  calc |(∑ k ∈ Icc 1 K, a k) * w K +
        ∑ k ∈ Icc 1 (K - 1), (∑ i ∈ Icc 1 k, a i) * (w k - w (k + 1))|
      ≤ B * w K + B * (w 1 - w K) := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = B * w 1 := by ring

/-- `|Σ_{k ≤ j} cos(kθ)| ≤ 1/|sin(θ/2)|`. -/
theorem abs_sum_cos_le {θ : ℝ} (hθ : Real.sin (θ / 2) ≠ 0) (j : ℕ) :
    |∑ k ∈ Icc 1 j, Real.cos (k * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  set x : ℂ := Complex.exp (Complex.I * θ) with hx
  have hx1 : x ≠ 1 := by
    intro h
    have hn := Complex.norm_exp_I_mul_ofReal_sub_one θ
    rw [← hx, h, sub_self, norm_zero, norm_mul, Real.norm_two, Real.norm_eq_abs] at hn
    exact hθ (abs_eq_zero.mp (by linarith [abs_nonneg (Real.sin (θ / 2))]))
  have hxn : ‖x‖ = 1 := by rw [hx, mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ
  have hsum : ∑ k ∈ Icc 1 j, Real.cos (k * θ) = (x * ∑ k ∈ range j, x ^ k).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    have hIcc : Icc 1 j = Ico 1 (j + 1) := rfl
    rw [hIcc, Finset.sum_Ico_eq_sum_range, show j + 1 - 1 = j by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx, ← Complex.exp_nat_mul, ← Complex.exp_add]
    rw [show Complex.I * θ + k * (Complex.I * θ) = (((1 + k : ℕ) : ℝ) * θ : ℝ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re]
  rw [hsum, geom_sum_eq hx1]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, hxn, one_mul, norm_div]
  have hden : ‖x - 1‖ = 2 * |Real.sin (θ / 2)| := by
    rw [hx, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_two, Real.norm_eq_abs]
  have hnum : ‖x ^ j - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hxn, one_pow, norm_one]; norm_num
  rw [hden]
  have hs : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hθ
  rw [div_le_div_iff₀ (by positivity) hs]
  have := mul_le_mul_of_nonneg_right hnum hs.le
  linarith

/-- `|sin(π m/q)| ≥ 2/q` when `q ∤ m`. -/
theorem two_div_le_abs_sin {m q : ℕ} (hq : 2 ≤ q) (hm : ¬ q ∣ m) :
    2 / (q : ℝ) ≤ |Real.sin (Real.pi * m / q)| := by
  have hq0 : (0 : ℝ) < q := by positivity
  set m' := m % q with hm'
  have hm'pos : 1 ≤ m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hm
    · exact h
  have hm'lt : m' < q := Nat.mod_lt _ (by omega)
  have hshift : Real.pi * m / q = Real.pi * m' / q + ((m / q : ℕ) : ℤ) * Real.pi := by
    have h := Nat.mod_add_div m q
    have h' : (m : ℝ) = m' + q * (m / q : ℕ) := by exact_mod_cast h.symm
    rw [Int.cast_natCast, h']
    field_simp
  rw [hshift, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have hx1 : (1 : ℝ) / q ≤ m' / q := by
    rw [div_le_div_iff_of_pos_right hq0]; exact_mod_cast hm'pos
  have hx2 : (m' : ℝ) / q ≤ 1 - 1 / q := by
    rw [div_le_iff₀ hq0, sub_mul, div_mul_cancel₀ _ hq0.ne', one_mul]
    have : (m' : ℝ) + 1 ≤ q := by exact_mod_cast hm'lt
    linarith
  have hJ : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → 2 * y ≤ Real.sin (Real.pi * y) := by
    intro y hy0 hy1
    have h := Real.mul_le_sin (x := Real.pi * y) (by positivity) (by nlinarith [Real.pi_pos])
    have : 2 / Real.pi * (Real.pi * y) = 2 * y := by field_simp
    linarith
  have hq1 : 0 ≤ 1 / (q : ℝ) := by positivity
  set x : ℝ := (m' : ℝ) / q with hxdef
  have hsx : Real.sin (Real.pi * m' / q) = Real.sin (Real.pi * x) := by rw [hxdef]; ring_nf
  rw [hsx]
  rcases le_total x (1 / 2) with hx | hx
  · have h := hJ x (by positivity) hx
    have : 0 ≤ Real.sin (Real.pi * x) := by linarith [show (0 : ℝ) ≤ 2 * x by positivity]
    rw [abs_of_nonneg this]
    have : 2 / (q : ℝ) = 2 * (1 / q) := by ring
    linarith
  · have h := hJ (1 - x) (by linarith) (by linarith)
    have hsym : Real.sin (Real.pi * (1 - x)) = Real.sin (Real.pi * x) := by
      rw [show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring, Real.sin_pi_sub]
    rw [hsym] at h
    have : 0 ≤ Real.sin (Real.pi * x) := by linarith
    rw [abs_of_nonneg this]
    have : 2 / (q : ℝ) = 2 * (1 / q) := by ring
    linarith

/-! ## The diagonal: multiples of `q` among prime powers -/

/-- `Σ_{j < n} j / 2^j = 2 − 2(n + 1)/2^n`. -/
theorem sum_div_two_pow (n : ℕ) :
    ∑ j ∈ range n, (j : ℝ) / 2 ^ j = 2 - 2 * ((n : ℝ) + 1) / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [pow_succ]
    field_simp
    ring

/-- A prime power divisible by `q ≥ 2` is a power of the least prime factor of `q`. -/
theorem eq_minFac_pow_of_dvd {q a : ℕ} (hq : 2 ≤ q) (hqa : q ∣ a) (ha : IsPrimePow a) :
    ∃ j : ℕ, 0 < j ∧ a = q.minFac ^ j := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff a).mp ha
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hqa
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
    omega
  refine ⟨k, hk, ?_⟩
  rw [hi, hp.pow_minFac hi0]

/-- `Σ_{a ≤ N, q | a} Λ(a) log a / a ≤ 2 log² q`. -/
theorem sum_dvd_vonMangoldt_log_div_le {q : ℕ} (hq : 2 ≤ q) (N : ℕ) :
    ∑ a ∈ (Icc 1 N).filter (fun a => q ∣ a), vonMangoldt a * Real.log a / a ≤
      2 * Real.log q ^ 2 := by
  classical
  set m := q.minFac with hm
  have hmprime : m.Prime := Nat.minFac_prime (by omega)
  have hm2 : 2 ≤ m := hmprime.two_le
  have hmq : m ≤ q := Nat.minFac_le (by omega)
  set g : ℕ → ℝ := fun a => vonMangoldt a * Real.log a / a with hg
  have hg0 : ∀ a, 0 ≤ g a := fun a => by
    simp only [hg]; exact div_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg _))
      (Nat.cast_nonneg _)
  -- restrict to prime powers, which are powers of `m`
  have hsub : ∑ a ∈ (Icc 1 N).filter (fun a => q ∣ a), g a ≤
      ∑ a ∈ (Icc 1 N).image (fun j => m ^ j), g a := by
    rw [← Finset.sum_filter_ne_zero]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hg0 a)
    intro a ha
    rw [mem_filter, mem_filter, mem_Icc] at ha
    obtain ⟨⟨⟨ha1, haN⟩, hqa⟩, hga⟩ := ha
    have hΛ : vonMangoldt a ≠ 0 := by
      intro h; apply hga; simp [hg, h]
    obtain ⟨j, hj, rfl⟩ := eq_minFac_pow_of_dvd hq hqa (vonMangoldt_ne_zero_iff.mp hΛ)
    rw [mem_image]
    refine ⟨j, mem_Icc.mpr ⟨hj, ?_⟩, rfl⟩
    have h1m : 1 < q.minFac := by rw [← hm]; omega
    have := Nat.lt_pow_self (n := j) h1m
    omega
  rw [Finset.sum_image (fun i _ j _ hij => Nat.pow_right_injective hm2 hij)] at hsub
  refine hsub.trans ?_
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hterm : ∀ j ∈ Icc 1 N, g (m ^ j) ≤ Real.log m ^ 2 * ((j : ℝ) / 2 ^ j) := by
    intro j hj
    have hj0 : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
    simp only [hg]
    rw [vonMangoldt_apply_pow hj0, vonMangoldt_apply_prime hmprime]
    push_cast
    rw [Real.log_pow]
    have hmpow : (2 : ℝ) ^ j ≤ (m : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm2) j
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc Real.log m * (j * Real.log m) = Real.log m ^ 2 * j := by ring
      _ = Real.log m ^ 2 * ((j : ℝ) / 2 ^ j) * 2 ^ j := by field_simp
      _ ≤ Real.log m ^ 2 * ((j : ℝ) / 2 ^ j) * (m : ℝ) ^ j := by
          apply mul_le_mul_of_nonneg_left hmpow; positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ j ∈ Icc 1 N, (j : ℝ) / 2 ^ j ≤ 2 := by
    have h := sum_div_two_pow (N + 1)
    have hsub' : ∑ j ∈ Icc 1 N, (j : ℝ) / 2 ^ j ≤ ∑ j ∈ range (N + 1), (j : ℝ) / 2 ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
        rw [mem_range]; have := (mem_Icc.mp hj).2; omega) (fun j _ _ => by positivity)
    have : 0 ≤ 2 * (((N + 1 : ℕ) : ℝ) + 1) / 2 ^ (N + 1) := by positivity
    linarith
  have hlogq : Real.log m ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hmq)
  calc Real.log m ^ 2 * ∑ j ∈ Icc 1 N, (j : ℝ) / 2 ^ j ≤ Real.log m ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ Real.log q ^ 2 * 2 := by gcongr
    _ = 2 * Real.log q ^ 2 := by ring

/-! ## Rational phases -/

/-- **Rational phases cancel.**  For `r = p/q` in lowest terms, `q ≥ 2`, `X = qT/(2πp) ≥ 1`:
`|Σ_{n ≤ N} ℓ(n) cos(2πnr) W_T(nr)| ≤ (q/2)·48(log 4 + 4) X (log X + 1) + 96 X log² q`. -/
theorem abs_sum_logVM_cos_le {p q : ℕ} (hp : 0 < p) (hq : 2 ≤ q) (hcop : Nat.Coprime p q)
    {T : ℝ} (hT : 2 * Real.pi * p / q ≤ T) (N : ℕ) :
    |∑ n ∈ Icc 1 N, logVM n * (Real.cos (2 * Real.pi * n * ((p : ℝ) / q)) *
        gaussW T (n * ((p : ℝ) / q)))| ≤
      (q / 2) * (48 * (Real.log 4 + 4) * (q * T / (2 * Real.pi * p)) *
        (Real.log (q * T / (2 * Real.pi * p)) + 1) ^ 1) +
      48 * (q * T / (2 * Real.pi * p)) * (2 * Real.log q ^ 2) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set r : ℝ := (p : ℝ) / q with hr
  have hr0 : 0 < r := by positivity
  set X : ℝ := q * T / (2 * Real.pi * p) with hX
  have hX1 : 1 ≤ X := by
    rw [hX, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hq0] at hT
    linarith
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by
    have : 0 < 2 * Real.pi * p / q := by positivity
    linarith
  have hW : ∀ y : ℝ, gaussW T (y * r) = Real.exp (-(y / X) ^ 2) := by
    intro y
    rw [gaussW_eq _ _ hT0.ne']
    congr 2
    rw [hX, hr]
    field_simp
  set c : ℕ → ℝ := fun a => vonMangoldt a * Real.log a with hc
  have hc0 : ∀ a, 0 ≤ c a := fun a => mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg _)
  -- the inner sums
  have hinner : ∀ a ∈ Icc 1 N,
      |∑ b ∈ Icc 1 (N / a), Real.cos (2 * Real.pi * ((a * b : ℕ) : ℝ) * r) *
          gaussW T (((a * b : ℕ) : ℝ) * r)| ≤
        (q / 2) * Real.exp (-((a : ℝ) / X) ^ 2) + (if q ∣ a then 48 * X / a else 0) := by
    intro a ha
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (mem_Icc.mp ha).1
    have ha0 : (0 : ℝ) < a := by linarith
    simp_rw [hW]
    by_cases hqa : q ∣ a
    · rw [if_pos hqa]
      have hle : |∑ b ∈ Icc 1 (N / a), Real.cos (2 * Real.pi * ((a * b : ℕ) : ℝ) * r) *
          Real.exp (-((((a * b : ℕ) : ℝ)) / X) ^ 2)| ≤ 48 * (X / a) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hpt : ∀ b ∈ Icc 1 (N / a), |Real.cos (2 * Real.pi * ((a * b : ℕ) : ℝ) * r) *
            Real.exp (-((((a * b : ℕ) : ℝ)) / X) ^ 2)| ≤ Real.exp (-((b : ℝ) / (X / a)) ^ 2) := by
          intro b _
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hcos := Real.abs_cos_le_one (2 * Real.pi * ((a * b : ℕ) : ℝ) * r)
          have he : Real.exp (-((((a * b : ℕ) : ℝ)) / X) ^ 2) =
              Real.exp (-((b : ℝ) / (X / a)) ^ 2) := by
            congr 2; push_cast; field_simp
          rw [he]
          nlinarith [Real.exp_pos (-((b : ℝ) / (X / a)) ^ 2)]
        exact (Finset.sum_le_sum hpt).trans (sum_exp_neg_sq_le (by positivity) _)
      have hpos : 0 ≤ (q / 2 : ℝ) * Real.exp (-((a : ℝ) / X) ^ 2) := by positivity
      calc _ ≤ 48 * (X / a) := hle
        _ = 48 * X / a := by ring
        _ ≤ _ := by linarith
    · rw [if_neg hqa, add_zero]
      have hqap : ¬ q ∣ a * p := fun h => hqa (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h)
      have hsin := two_div_le_abs_sin (m := a * p) hq hqap
      have hsin0 : 0 < |Real.sin (Real.pi * ((a * p : ℕ) : ℝ) / q)| :=
        lt_of_lt_of_le (by positivity) hsin
      set θ : ℝ := 2 * Real.pi * a * r with hθ
      have hθ2 : Real.sin (θ / 2) = Real.sin (Real.pi * ((a * p : ℕ) : ℝ) / q) := by
        congr 1; rw [hθ, hr]; push_cast; ring
      rcases Nat.eq_zero_or_pos (N / a) with hK | hK
      · rw [hK]; simp; positivity
      have hab := abel_abs_sum_mul_le (a := fun b => Real.cos (b * θ))
        (w := fun b => Real.exp (-((((a * b : ℕ) : ℝ)) / X) ^ 2)) (B := (q : ℝ) / 2) hK
        (fun j _ => (abs_sum_cos_le (by rw [hθ2]; exact abs_pos.mp hsin0) j).trans (by
          rw [hθ2, div_le_div_iff₀ hsin0 (by norm_num)]
          rw [div_le_iff₀ hq0] at hsin
          linarith))
        (fun k _ _ => (Real.exp_pos _).le)
        (fun k hk _ => by
          apply Real.exp_le_exp.mpr
          have h1 : ((a * k : ℕ) : ℝ) / X ≤ ((a * (k + 1) : ℕ) : ℝ) / X := by
            apply div_le_div_of_nonneg_right _ hX0.le
            exact_mod_cast Nat.mul_le_mul_left a (Nat.le_succ k)
          have h0 : 0 ≤ ((a * k : ℕ) : ℝ) / X := by positivity
          nlinarith)
      have hcongr : ∑ b ∈ Icc 1 (N / a), Real.cos (2 * Real.pi * ((a * b : ℕ) : ℝ) * r) *
          Real.exp (-((((a * b : ℕ) : ℝ)) / X) ^ 2) =
          ∑ b ∈ Icc 1 (N / a), Real.cos (b * θ) * Real.exp (-((((a * b : ℕ) : ℝ)) / X) ^ 2) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        congr 2
        rw [hθ]; push_cast; ring
      rw [hcongr]
      refine hab.trans (le_of_eq ?_)
      simp
  -- assemble
  rw [show (∑ n ∈ Icc 1 N, logVM n * (Real.cos (2 * Real.pi * n * r) * gaussW T (n * r))) =
      ∑ n ∈ Icc 1 N, logVM n * (fun m : ℕ => Real.cos (2 * Real.pi * (m : ℝ) * r) *
        gaussW T ((m : ℝ) * r)) n from rfl, sum_logVM_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsplit : ∀ a ∈ Icc 1 N, |vonMangoldt a * Real.log a *
      ∑ b ∈ Icc 1 (N / a), Real.cos (2 * Real.pi * ((a * b : ℕ) : ℝ) * r) *
        gaussW T (((a * b : ℕ) : ℝ) * r)| ≤
      (q / 2) * (c a * Real.exp (-((a : ℝ) / X) ^ 2)) +
        48 * X * (if q ∣ a then c a / a else 0) := by
    intro a ha
    rw [abs_mul, abs_of_nonneg (hc0 a)]
    refine (mul_le_mul_of_nonneg_left (hinner a ha) (hc0 a)).trans (le_of_eq ?_)
    split_ifs <;> simp only [hc] <;> ring
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_filter]
  have hlayer := sum_mul_weight_le_layers (c := c) hc0 (by positivity : (0 : ℝ) ≤ Real.log 4 + 4)
    (k := 1) (by norm_num) sum_vonMangoldt_mul_log_le (φ := fun u => Real.exp (-u ^ 2))
    exp_neg_sq_le_one (fun u _ => exp_neg_sq_mul_sq_le_one u) hX1 N
  have hdiag := sum_dvd_vonMangoldt_log_div_le hq N
  gcongr

/-- **Rational phases**, in the form `O(T log T)`. -/
theorem exists_abs_sum_logVM_cos_le {p q : ℕ} (hp : 0 < p) (hq : 2 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → 2 * Real.pi * p / q ≤ T → ∀ N : ℕ,
      |∑ n ∈ Icc 1 N, logVM n * (Real.cos (2 * Real.pi * n * ((p : ℝ) / q)) *
          gaussW T (n * ((p : ℝ) / q)))| ≤ C * T * (Real.log T + 1) := by
  have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq0 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  refine ⟨(q / 2) * (48 * (Real.log 4 + 4) * q * (Real.log q + 1)) + 96 * q * Real.log q ^ 2,
    by positivity, fun T hT1 hT N => ?_⟩
  refine (abs_sum_logVM_cos_le hp hq hcop hT N).trans ?_
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hX1 : 1 ≤ q * T / (2 * Real.pi * p) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by linarith)] at hT
    linarith
  have hXle : q * T / (2 * Real.pi * p) ≤ q * T := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ 2 * Real.pi * p := by nlinarith [Real.pi_gt_three]
    nlinarith [show (0 : ℝ) ≤ q * T by positivity]
  have hlogX : Real.log (q * T / (2 * Real.pi * p)) + 1 ≤ (Real.log q + 1) * (Real.log T + 1) := by
    have h1 : Real.log (q * T / (2 * Real.pi * p)) ≤ Real.log (q * T) :=
      Real.log_le_log (by linarith) hXle
    rw [Real.log_mul (by linarith) (by linarith)] at h1
    nlinarith
  have hlogX0 : 0 ≤ Real.log (q * T / (2 * Real.pi * p)) + 1 := by
    have := Real.log_nonneg hX1; linarith
  rw [pow_one]
  calc (q / 2 : ℝ) * (48 * (Real.log 4 + 4) * (q * T / (2 * Real.pi * p)) *
        (Real.log (q * T / (2 * Real.pi * p)) + 1)) +
      48 * (q * T / (2 * Real.pi * p)) * (2 * Real.log q ^ 2)
      ≤ (q / 2) * (48 * (Real.log 4 + 4) * (q * T) * ((Real.log q + 1) * (Real.log T + 1))) +
        48 * (q * T * (Real.log T + 1)) * (2 * Real.log q ^ 2) := by
        gcongr
        · exact hXle.trans (le_mul_of_one_le_right (by positivity) (by linarith))
    _ = _ := by ring

/-! ## The main term -/

/-- `Σ_{n ≤ M} ℓ(n) ≥ M (½ log² M − 15 log M − 1) − (log 4 + 4) M (log M + 1)`. -/
theorem sum_logVM_ge (M : ℕ) (hM : 1 ≤ M) :
    (M : ℝ) * (Real.log M ^ 2 / 2 - 15 * Real.log M - 1) -
        (Real.log 4 + 4) * M * (Real.log M + 1) ≤ ∑ n ∈ Icc 1 M, logVM n := by
  have hswap := sum_logVM_mul (fun _ => (1 : ℝ)) M
  simp only [mul_one, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hswap
  rw [hswap]
  have hdiv : ∀ a ∈ Icc 1 M, (M : ℝ) / a - 1 ≤ ((M / a : ℕ) : ℝ) := by
    intro a ha
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    have h := Nat.lt_div_mul_add (a := M) ha0
    have h' : (M : ℝ) < ((M / a : ℕ) : ℝ) * a + a := by exact_mod_cast h
    have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
    rw [div_sub_one ha0'.ne', div_le_iff₀ ha0']
    linarith
  have hlow : ∑ a ∈ Icc 1 M, vonMangoldt a * Real.log a * ((M : ℝ) / a - 1) ≤
      ∑ a ∈ Icc 1 M, vonMangoldt a * Real.log a * ((M / a : ℕ) : ℝ) :=
    Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hdiv a ha)
      (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg _))
  refine le_trans ?_ hlow
  have hexp : ∑ a ∈ Icc 1 M, vonMangoldt a * Real.log a * ((M : ℝ) / a - 1) =
      (M : ℝ) * ∑ a ∈ Icc 1 M, vonMangoldt a * Real.log a / a -
        ∑ a ∈ Icc 1 M, vonMangoldt a * Real.log a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [hexp]
  have hmert := RHTower.abs_sum_vonMangoldt_log_div_sub_le M hM
  have hcheb := sum_vonMangoldt_mul_log_le M
  rw [pow_one] at hcheb
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h1 : Real.log M ^ 2 / 2 - 15 * Real.log M - 1 ≤
      ∑ a ∈ Icc 1 M, vonMangoldt a * Real.log a / a := by
    have := (abs_le.mp hmert).1
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hM0
  linarith

/-- **The main term**: for integers `r ≥ 1`, `N ≥ T/r` and `T/r ≥ e^{202}`,
`Σ_{n ≤ N} ℓ(n) W_T(nr) ≥ (e^{−4π²}/32) (T/r) log²(T/r)`. -/
theorem sum_logVM_gaussW_ge {r : ℕ} (hr : 1 ≤ r) {T : ℝ} (hTr : Real.exp 202 ≤ T / r) {N : ℕ}
    (hN : T / r ≤ N) :
    Real.exp (-(4 * Real.pi ^ 2)) / 32 * (T / r) * Real.log (T / r) ^ 2 ≤
      ∑ n ∈ Icc 1 N, logVM n * gaussW T (n * r) := by
  set Y : ℝ := T / r with hY
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hY4 : (4 : ℝ) ≤ Y := by
    have : (4 : ℝ) ≤ Real.exp 202 := by
      have := Real.add_one_le_exp (202 : ℝ); linarith
    linarith
  have hY0 : 0 < Y := by linarith
  have hT0 : 0 < T := by
    have : T = Y * r := by rw [hY]; field_simp
    rw [this]; positivity
  set M : ℕ := ⌊Y⌋₊ with hMdef
  have hMY : (M : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hYM : Y - 1 ≤ M := by have := Nat.lt_floor_add_one Y; linarith
  have hMN : M ≤ N := by
    rw [hMdef]; exact Nat.floor_le_of_le hN
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  -- restrict to `n ≤ M`, where `W_T(nr) ≥ e^{−4π²}`
  have hsub : ∑ n ∈ Icc 1 M, logVM n * gaussW T (n * r) ≤ ∑ n ∈ Icc 1 N, logVM n * gaussW T (n * r) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hMN)
      (fun n _ _ => mul_nonneg (logVM_nonneg n) (gaussW_pos _ _).le)
  have hW : ∀ n ∈ Icc 1 M, Real.exp (-(4 * Real.pi ^ 2)) ≤ gaussW T (n * r) := by
    intro n hn
    unfold gaussW
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast (mem_Icc.mp hn).2
    have hnr : (n : ℝ) * r ≤ T := by
      have : (n : ℝ) ≤ T / r := hnM.trans hMY
      rwa [le_div_iff₀ hr0] at this
    have hsq : ((n : ℝ) * r) ^ 2 / T ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (by positivity) hnr 2
    have : 4 * Real.pi ^ 2 * ((n : ℝ) * r) ^ 2 / T ^ 2 ≤ 4 * Real.pi ^ 2 := by
      rw [mul_div_assoc]
      nlinarith [Real.pi_pos]
    linarith
  have hlower : Real.exp (-(4 * Real.pi ^ 2)) * ∑ n ∈ Icc 1 M, logVM n ≤
      ∑ n ∈ Icc 1 M, logVM n * gaussW T (n * r) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hW n hn) (logVM_nonneg n)
  refine le_trans ?_ (hlower.trans hsub)
  -- the count
  have hcount := sum_logVM_ge M hM1
  have hYhalf : Y / 2 ≤ M := by linarith
  have hlogM : 200 ≤ Real.log M := by
    have hM' : Real.exp 200 ≤ M := by
      have : Real.exp 200 * 2 ≤ Real.exp 202 := by
        rw [show (202 : ℝ) = 200 + 2 by norm_num, Real.exp_add]
        have : (2 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
        nlinarith [Real.exp_pos 200]
      linarith
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hM'
  have hlog4 : Real.log 4 + 4 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hkey : (M : ℝ) * (Real.log M ^ 2 / 4) ≤
      (M : ℝ) * (Real.log M ^ 2 / 2 - 15 * Real.log M - 1) - (Real.log 4 + 4) * M * (Real.log M + 1) := by
    have h7 : (Real.log 4 + 4) * M * (Real.log M + 1) ≤ 7 * M * (Real.log M + 1) := by
      gcongr
    have hq : 0 ≤ Real.log M ^ 2 / 4 - 22 * Real.log M - 8 := by nlinarith
    have := mul_nonneg hM0.le hq
    nlinarith
  have hlogY : Real.log Y / 2 ≤ Real.log M := by
    have h1 : Real.log (Y / 2) ≤ Real.log M := Real.log_le_log (by positivity) hYhalf
    rw [Real.log_div hY0.ne' (by norm_num)] at h1
    have hlog2 : Real.log 2 ≤ Real.log Y / 2 := by
      have : Real.log 4 ≤ Real.log Y := Real.log_le_log (by norm_num) hY4
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hfinal : Y * Real.log Y ^ 2 / 32 ≤ (M : ℝ) * (Real.log M ^ 2 / 4) := by
    have h1 : (Real.log Y / 2) ^ 2 ≤ Real.log M ^ 2 := pow_le_pow_left₀ (by positivity) hlogY 2
    have h2 : Y / 2 * (Real.log Y / 2) ^ 2 ≤ (M : ℝ) * Real.log M ^ 2 :=
      mul_le_mul hYhalf h1 (by positivity) hM0.le
    nlinarith
  have hE := Real.exp_pos (-(4 * Real.pi ^ 2))
  calc Real.exp (-(4 * Real.pi ^ 2)) / 32 * Y * Real.log Y ^ 2
      = Real.exp (-(4 * Real.pi ^ 2)) * (Y * Real.log Y ^ 2 / 32) := by ring
    _ ≤ Real.exp (-(4 * Real.pi ^ 2)) * ∑ n ∈ Icc 1 M, logVM n := by
        apply mul_le_mul_of_nonneg_left _ hE.le
        linarith

end

end RHTower.GaussZeroSum
