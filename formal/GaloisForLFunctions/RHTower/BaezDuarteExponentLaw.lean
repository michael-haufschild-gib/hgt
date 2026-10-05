import GaloisForLFunctions.RHTower.BaezDuarteRieszPoissonCriterion
import GaloisForLFunctions.RHTower.RieszFunctionExponentLaw

/-!
# The Báez--Duarte exponent law

Let `Θ = sup {Re ρ : ζ(ρ) = 0}` and `c_k = Σ_n μ(n) f_k(n)`, `f_k(n) = n^{-2}(1 - n^{-2})^k`.
Then `c_k` decays with exponent exactly `1 - Θ/2`:

* if `|M(N)| ≤ C (N+1)^a` then `|c_k| ≤ K k^{(a+δ)/2 - 1}`: Abel summation, with consecutive
  weights `|f_k(n) - f_k(n+1)| ≤ (u - v)(1-v)^{k-1}(1 + kv) ≤ 9 · 128^θ k^{-2θ} n^{4θ-3}`
  (`u = n^{-2}`, `v = (n+1)^{-2}`), the same majorant as for the Riesz weights with `x = k`;
* conversely `c_k = O((k+1)^{b-1})` forces `Θ ≤ 2b` through Poissonization into the Riesz series.

Hence `Θ = 2 inf {b : c_k = O((k+1)^{b-1})}`; RH is the case `1 - Θ/2 = 3/4`, and unconditionally
`c_k` is never `O(k^{-β})` with `β > 3/4`.
-/

open Filter Finset

namespace RHTower

noncomputable section

/-- `a^k - b^k ≤ k (a - b) a^{k-1}` for `0 ≤ b ≤ a`. -/
theorem pow_sub_pow_le_mul_sub_mul_pow {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (k : ℕ) :
    a ^ k - b ^ k ≤ k * (a - b) * a ^ (k - 1) := by
  have ha : 0 ≤ a := hb.trans hba
  rw [← geom_sum₂_mul]
  have hsum : ∑ i ∈ range k, a ^ i * b ^ (k - 1 - i) ≤ ∑ _i ∈ range k, a ^ (k - 1) := by
    refine sum_le_sum fun i hi => ?_
    have hik : i ≤ k - 1 := by have := mem_range.mp hi; omega
    calc a ^ i * b ^ (k - 1 - i) ≤ a ^ i * a ^ (k - 1 - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hba _) (pow_nonneg ha _)
      _ = a ^ (k - 1) := by rw [← pow_add]; congr 1; omega
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have hab : 0 ≤ a - b := by linarith
  nlinarith

/-- Increment of the Báez--Duarte weight `u(1-u)^k`: for `0 ≤ v ≤ u ≤ 1`, `k ≥ 1`,
`|u(1-u)^k - v(1-v)^k| ≤ (u - v)(1-v)^{k-1}(1 + kv)`. -/
theorem abs_mul_one_sub_pow_sub_le {u v : ℝ} {k : ℕ} (hk : 1 ≤ k) (hv : 0 ≤ v) (hvu : v ≤ u)
    (hu1 : u ≤ 1) :
    |u * (1 - u) ^ k - v * (1 - v) ^ k| ≤ (u - v) * ((1 - v) ^ (k - 1) * (1 + k * v)) := by
  set a := 1 - v with ha
  set b := 1 - u with hb
  have hb0 : 0 ≤ b := by linarith
  have hba : b ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hpow := pow_sub_pow_le_mul_sub_mul_pow hb0 hba k
  have hab : a - b = u - v := by rw [ha, hb]; ring
  rw [hab] at hpow
  have hbk : b ^ k ≤ a ^ (k - 1) := by
    calc b ^ k ≤ a ^ k := pow_le_pow_left₀ hb0 hba k
      _ = a ^ (k - 1) * a := by rw [← pow_succ]; congr 1; omega
      _ ≤ a ^ (k - 1) := mul_le_of_le_one_right (pow_nonneg (hb0.trans hba) _) ha1
  have hbk0 : 0 ≤ b ^ k := pow_nonneg hb0 k
  have hak : b ^ k ≤ a ^ k := pow_le_pow_left₀ hb0 hba k
  have huv : 0 ≤ u - v := by linarith
  have hak1 : 0 ≤ a ^ (k - 1) := pow_nonneg (hb0.trans hba) _
  have hsplit : u * b ^ k - v * a ^ k = (u - v) * b ^ k - v * (a ^ k - b ^ k) := by ring
  rw [hsplit, abs_le]
  constructor
  · nlinarith [mul_nonneg huv hbk0, mul_nonneg hv (mul_nonneg huv hak1),
      mul_nonneg (mul_nonneg huv hak1) (mul_nonneg (Nat.cast_nonneg k) hv)]
  · nlinarith [mul_nonneg hv (sub_nonneg.mpr hak), mul_nonneg huv hak1,
      mul_nonneg (mul_nonneg huv hak1) (mul_nonneg (Nat.cast_nonneg k) hv)]

/-- The Báez--Duarte weight `f_k(n) = n^{-2}(1 - n^{-2})^k`. -/
def bdWeight (k n : ℕ) : ℝ := ((n : ℝ) ^ 2)⁻¹ * (1 - ((n : ℝ) ^ 2)⁻¹) ^ k

theorem bdRealTerm_eq_mul_bdWeight (k n : ℕ) :
    bdRealTerm k n = (ArithmeticFunction.moebius n : ℝ) * bdWeight k n := by
  unfold bdRealTerm bdWeight; ring

/-- Consecutive Báez--Duarte weights: for `n, k ≥ 1`, `0 ≤ θ ≤ 1`,
`|f_k(n) - f_k(n+1)| ≤ 9 · 128^θ k^{-2θ} n^{4θ-3}`. -/
theorem abs_bdWeight_succ_sub_le {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    |bdWeight k n - bdWeight k (n + 1)| ≤
      9 * 128 ^ θ * (k : ℝ) ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ - 3) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold bdWeight
  push_cast
  set u : ℝ := ((n : ℝ) ^ 2)⁻¹ with hu
  set v : ℝ := (((n : ℝ) + 1) ^ 2)⁻¹ with hv
  have hv0 : 0 < v := by positivity
  have hvu : v ≤ u := inv_anti₀ (by positivity) (by nlinarith)
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hv1 : v ≤ 1 := hvu.trans hu1
  have h1 := abs_mul_one_sub_pow_sub_le hk hv0.le hvu hu1
  have hexp : (1 - v) ^ (k - 1) ≤ 3 * Real.exp (-((k : ℝ) * v)) := by
    have h1v : 0 ≤ 1 - v := by linarith
    calc (1 - v) ^ (k - 1) ≤ Real.exp (-v) ^ (k - 1) :=
          pow_le_pow_left₀ h1v (by linarith [Real.add_one_le_exp (-v)]) _
      _ = Real.exp (v) * Real.exp (-((k : ℝ) * v)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          rw [Nat.cast_sub hk]
          push_cast
          ring
      _ ≤ 3 * Real.exp (-((k : ℝ) * v)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          calc Real.exp v ≤ Real.exp 1 := Real.exp_le_exp.mpr hv1
            _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have h2 := inv_sq_sub_mul_one_add_mul_exp_neg_le hk' hθ0 hθ1 hn
  have huv : 0 ≤ u - v := by linarith
  calc |u * (1 - u) ^ k - v * (1 - v) ^ k|
      ≤ (u - v) * ((1 - v) ^ (k - 1) * (1 + k * v)) := h1
    _ ≤ (u - v) * (3 * Real.exp (-((k : ℝ) * v)) * (1 + k * v)) := by
        gcongr
    _ = 3 * ((u - v) * ((1 + k * v) * Real.exp (-((k : ℝ) * v)))) := by ring
    _ ≤ 3 * (3 * 128 ^ θ * (k : ℝ) ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ - 3)) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 9 * 128 ^ θ * (k : ℝ) ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ - 3) := by ring

/-- **Mertens bounds transfer to the Báez--Duarte coefficients.**  If `|M(N)| ≤ C (N+1)^a`, then
`|c_k| ≤ K k^{(a+δ)/2 - 1}` for every `k ≥ 1`, for any `δ > 0` with `a + δ ≤ 2`. -/
theorem abs_bdReal_le_of_mertens_bound {a δ C : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (haδ : a + δ ≤ 2) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, 1 ≤ k → |bdReal k| ≤ K * (k : ℝ) ^ ((a + δ) / 2 - 1) := by
  set θ : ℝ := (2 - a - δ) / 4 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  set S : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-1 - δ)
  have hS0 : 0 ≤ S := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨2 ^ a * C * (9 * 128 ^ θ) * S, by positivity, fun k hk => ?_⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : Summable fun n => (ArithmeticFunction.moebius n : ℝ) * bdWeight k n :=
    (summable_bdRealTerm k).congr fun n => bdRealTerm_eq_mul_bdWeight k n
  have hval : bdReal k = ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * bdWeight k n :=
    tsum_congr fun n => bdRealTerm_eq_mul_bdWeight k n
  have h := abs_tsum_moebius_mul_le_of_mertens_bound (f := bdWeight k)
    (D := 9 * 128 ^ θ * (k : ℝ) ^ (-(2 * θ))) ha hδ hC (by positivity) hM hsum
    (fun n hn => ?_) (fun n hn => ?_)
  · rw [hval]
    calc |∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * bdWeight k n|
        ≤ 2 ^ a * C * (9 * 128 ^ θ * (k : ℝ) ^ (-(2 * θ))) * S := h
      _ = 2 ^ a * C * (9 * 128 ^ θ) * S * (k : ℝ) ^ ((a + δ) / 2 - 1) := by
          rw [show -(2 * θ) = (a + δ) / 2 - 1 by rw [hθ]; ring]; ring
  · unfold bdWeight
    have hu1 := inv_natCast_sq_le_one n
    have hu0 : 0 ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
    rw [abs_mul, abs_of_nonneg hu0, abs_of_nonneg (pow_nonneg (by linarith) _)]
    exact mul_le_of_le_one_right hu0 (pow_le_one₀ (by linarith) (by linarith))
  · have hd := abs_bdWeight_succ_sub_le hk hθ0 hθ1 hn
    rw [show 4 * θ - 3 = -1 - δ - a by rw [hθ]; ring] at hd
    exact hd

/-! ## The Báez--Duarte exponent law -/

/-- **Upper half of the Báez--Duarte exponent law.**  `c_k = O((k+1)^{b-1})` for every `b > Θ/2`. -/
theorem exists_abs_bdReal_le_rpow_of_zetaZeroAbscissa_lt {b : ℝ}
    (hb : zetaZeroAbscissa < 2 * b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |bdReal k| ≤ C * ((k : ℝ) + 1) ^ (b - 1) := by
  have hΘ := half_le_zetaZeroAbscissa
  have hΘ1 := zetaZeroAbscissa_le_one
  set b' : ℝ := min b (3 / 4) with hb'
  have hb'b : b' ≤ b := min_le_left _ _
  have hb'34 : b' ≤ 3 / 4 := min_le_right _ _
  have hb'Θ : zetaZeroAbscissa < 2 * b' := by
    rcases le_total b (3 / 4) with h | h
    · rw [hb', min_eq_left h]; exact hb
    · rw [hb', min_eq_right h]; linarith
  set ε : ℝ := 2 * b' - zetaZeroAbscissa with hε
  have hε0 : 0 < ε := by linarith
  obtain ⟨C, hC0, hC⟩ := mobiusMertens_subpower_zetaZeroAbscissa (ε / 2) (by positivity)
  obtain ⟨K, hK0, hK⟩ := abs_bdReal_le_of_mertens_bound (a := zetaZeroAbscissa + ε / 2)
    (δ := ε / 2) (by linarith) (by positivity) (by linarith) hC0 hC
  have hexp : (zetaZeroAbscissa + ε / 2 + ε / 2) / 2 - 1 = b' - 1 := by rw [hε]; ring
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹
  have hZ : 0 ≤ Z := tsum_nonneg fun n => by positivity
  refine ⟨max (2 * K) Z, le_max_of_le_right hZ, fun k => ?_⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmono : ((k : ℝ) + 1) ^ (b' - 1) ≤ ((k : ℝ) + 1) ^ (b - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
      (by linarith)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    exact (abs_bdReal_le 0).trans (le_max_right _ _)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbound := hK k hk
  rw [hexp] at hbound
  have hcmp : (k : ℝ) ^ (b' - 1) ≤ 2 * ((k : ℝ) + 1) ^ (b' - 1) := by
    have h2k : (k : ℝ) + 1 ≤ 2 * k := by linarith
    have hneg : b' - 1 ≤ 0 := by linarith
    calc (k : ℝ) ^ (b' - 1) = 2 ^ (1 - b') * (2 * (k : ℝ)) ^ (b' - 1) := by
          rw [Real.mul_rpow (by norm_num) (by linarith), ← mul_assoc, ← Real.rpow_add
            (by norm_num)]
          norm_num
      _ ≤ 2 ^ (1 - b') * ((k : ℝ) + 1) ^ (b' - 1) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hk1 h2k hneg)
            (Real.rpow_nonneg (by norm_num) _)
      _ ≤ 2 * ((k : ℝ) + 1) ^ (b' - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hk1.le _)
          calc (2 : ℝ) ^ (1 - b') ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  calc |bdReal k| ≤ K * (k : ℝ) ^ (b' - 1) := hbound
    _ ≤ K * (2 * ((k : ℝ) + 1) ^ (b - 1)) :=
        mul_le_mul_of_nonneg_left (hcmp.trans (mul_le_mul_of_nonneg_left hmono (by norm_num)))
          hK0
    _ = 2 * K * ((k : ℝ) + 1) ^ (b - 1) := by ring
    _ ≤ max (2 * K) Z * ((k : ℝ) + 1) ^ (b - 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hk1.le _)

/-- **Lower half of the Báez--Duarte exponent law.**  `c_k = O((k+1)^{b-1})` forces `Θ ≤ 2b`. -/
theorem zetaZeroAbscissa_le_of_abs_bdReal_le_rpow {b C : ℝ}
    (h : ∀ k : ℕ, |bdReal k| ≤ C * ((k : ℝ) + 1) ^ (b - 1)) :
    zetaZeroAbscissa ≤ 2 * b := by
  have hΘ := half_le_zetaZeroAbscissa
  have hΘ1 := zetaZeroAbscissa_le_one
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (h 0)
    simpa using this
  rcases le_or_gt (1 / 2) b with hb | hb
  · linarith
  rcases le_or_gt 0 b with hb0 | hb0
  · have := zetaZeroAbscissa_le_of_bdReal_le (C := C) (β := 1 - b) (by linarith) (by linarith)
      fun k => by rw [show -(1 - b) = b - 1 by ring]; exact h k
    linarith
  · exfalso
    have h1 : ∀ k : ℕ, |bdReal k| ≤ C * ((k : ℝ) + 1) ^ (-(1 : ℝ)) := fun k =>
      (h k).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) (by linarith)) hC)
    have := zetaZeroAbscissa_le_of_bdReal_le (C := C) (β := 1) (by norm_num) le_rfl h1
    linarith

/-- **The Báez--Duarte exponent law.**  The zeta zero abscissa is twice the decay exponent of the
Báez--Duarte coefficients shifted by one: `Θ = 2 inf {b : c_k = O((k+1)^{b-1})}`. -/
theorem zetaZeroAbscissa_eq_two_mul_sInf_bdReal_exponents :
    zetaZeroAbscissa = 2 * sInf {b : ℝ | ∃ C : ℝ, ∀ k : ℕ,
      |bdReal k| ≤ C * ((k : ℝ) + 1) ^ (b - 1)} := by
  set S := {b : ℝ | ∃ C : ℝ, ∀ k : ℕ, |bdReal k| ≤ C * ((k : ℝ) + 1) ^ (b - 1)} with hS
  have hlow : ∀ b ∈ S, zetaZeroAbscissa / 2 ≤ b := fun b ⟨C, hC⟩ => by
    have := zetaZeroAbscissa_le_of_abs_bdReal_le_rpow hC
    linarith
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, _, hC⟩ := exists_abs_bdReal_le_rpow_of_zetaZeroAbscissa_lt
      (b := zetaZeroAbscissa / 2 + ε) (by linarith)
    exact ⟨C, hC⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨_, hlow⟩
  have hinf : sInf S = zetaZeroAbscissa / 2 := by
    refine le_antisymm ?_ (le_csInf hne hlow)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le hbdd (hmem ε hε)
  rw [hinf]
  ring

/-- The Báez--Duarte coefficients are never `O(k^{-β})` with `β > 3/4`. -/
theorem not_abs_bdReal_le_rpow_of_lt {β : ℝ} (hβ : 3 / 4 < β) (C : ℝ) :
    ¬ ∀ k : ℕ, |bdReal k| ≤ C * ((k : ℝ) + 1) ^ (-β) := fun h => by
  have := zetaZeroAbscissa_le_of_abs_bdReal_le_rpow (b := 1 - β) (C := C)
    fun k => by rw [show 1 - β - 1 = -β by ring]; exact h k
  have := half_le_zetaZeroAbscissa
  linarith

end

end RHTower
