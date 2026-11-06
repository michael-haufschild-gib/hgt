import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheTowerDeficit
import Mathlib.NumberTheory.Chebyshev

/-!
# The pole is the top of the prime form

The covariant counterterm of the atomic prime form is `log N + O(1)`
(`TheCovariantCountertermIsTheAnomaly`: between `log N − log 8 − 4` and `log N + log 4 + 4`). This
file computes its finite part: the top of `P_N` is `log N − γ + o(1)`, attained by the pole vector.
On every vector, not only on class profiles, the prime place exceeds the archimedean counterterm
`log N` by exactly the Euler constant of the pole.

* **Weighted Schur test** (`atomicWeilForm_le_of_weight`): a positive weight `v` with
  `P v ≤ R v` entrywise gives `P_N(x) ≤ R |x|²`.
* **The rows of the tilted pole** (`sum_weilPrimeKernel_mul_sqrt_le`): against `√n`,
  `Σ_n P(m, n) √n ≤ √m (ψ(⌊N/m⌋) + ½ log m)`: the up-tower is Chebyshev's function, every down-tower
  ratio `n/m` is at most `½`.
* **The tilted pole is a Collatz–Wielandt vector** (`eventually_row_tiltedPole_le`): with
  `v_n = n^{−1/2}(1 + η n/N)` and `η = ε/(2(log 4 + 4))`, eventually in `N`,
  `(P v)_m ≤ (log N − γ + ε) v_m` for every `m ≤ N`. On rows with `⌊N/m⌋` large Mertens' theorem
  gives `A(⌊N/m⌋) + log m ≤ log N − γ + ε/2`; on the top rows the tilt lowers the ratio by
  `(η m/N)(½ log N − γ)`, which grows without bound.
* **The sharp counterterm** (`eventually_atomicWeilForm_le_sharp`,
  `covariantCounterterm_sharp`): for every `ε > 0`, eventually `P_N ≤ (log N − γ + ε)|·|²`, and every
  scalar dominating `P_N` is at least `log N − γ − ε`.

So the pole vector is extremal for Weil's prime form over all atomic vectors, not only over the
`p`-adic class profiles (`TheArchimedeanPlacePaysTheTowerDeficit`): matched against the archimedean
self-energy, the prime place has finite part `−γ`, the finite part of the pole.
-/

noncomputable section

open Filter Topology Finset
open scoped Chebyshev

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticIntersectionTheory GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticEffectivityTheory ArithmeticFunction

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. The weighted Schur test -/

/-- **Weighted Schur test.** If `v > 0` on `[1, N]` and `Σ_n P(m, n) v_n ≤ R v_m` for every `m`,
then `P_N(x) ≤ R |x|²`. -/
theorem atomicWeilForm_le_of_weight {N : ℕ} {R : ℝ} (v : ℕ → ℝ)
    (hv : ∀ n ∈ Icc 1 N, 0 < v n)
    (hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, weilPrimeKernel m n * v n ≤ R * v m)
    (x : ℕ → ℝ) : atomicWeilForm N x ≤ R * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set S := Icc 1 N
  have hpair : ∀ m ∈ S, ∀ n ∈ S, x m * x n * weilPrimeKernel m n ≤
      (x m ^ 2 / v m * (weilPrimeKernel m n * v n) +
        x n ^ 2 / v n * (weilPrimeKernel n m * v m)) / 2 := by
    intro m hm n hn
    have hvm := hv m hm
    have hvn := hv n hn
    rw [weilPrimeKernel_comm n m]
    have hP := weilPrimeKernel_nonneg m n
    have key : x m ^ 2 / v m * v n + x n ^ 2 / v n * v m - 2 * (x m * x n) =
        (x m * v n - x n * v m) ^ 2 / (v m * v n) := by
      field_simp
      ring
    have h2 : 2 * (x m * x n) ≤ x m ^ 2 / v m * v n + x n ^ 2 / v n * v m := by
      have : 0 ≤ (x m * v n - x n * v m) ^ 2 / (v m * v n) := by positivity
      linarith
    nlinarith
  have hsym : ∑ m ∈ S, ∑ n ∈ S, x n ^ 2 / v n * (weilPrimeKernel n m * v m) =
      ∑ m ∈ S, ∑ n ∈ S, x m ^ 2 / v m * (weilPrimeKernel m n * v n) := sum_comm
  calc atomicWeilForm N x
      ≤ ∑ m ∈ S, ∑ n ∈ S, (x m ^ 2 / v m * (weilPrimeKernel m n * v n) +
          x n ^ 2 / v n * (weilPrimeKernel n m * v m)) / 2 :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
    _ = ∑ m ∈ S, x m ^ 2 / v m * ∑ n ∈ S, weilPrimeKernel m n * v n := by
        simp only [← sum_div, sum_add_distrib, hsym, mul_sum]
        ring
    _ ≤ ∑ m ∈ S, x m ^ 2 / v m * (R * v m) := sum_le_sum fun m hm =>
        mul_le_mul_of_nonneg_left (hrow m hm) (div_nonneg (sq_nonneg _) (hv m hm).le)
    _ = R * ∑ n ∈ S, x n ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun m hm => ?_
        field_simp [(hv m hm).ne']

/-! ### 2. The rows of `√n` -/

/-- Up the tower, a function of the ratio: `Σ_{n ≤ N, m ∣ n, n ≠ m} f(n/m) = Σ_{t ≤ N/m} f(t)` when
`f(1) = 0`. -/
theorem sum_up_eq_of_one {m N : ℕ} (hm : 0 < m) (f : ℕ → ℝ) (hf : f 1 = 0) :
    ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then f (n / m) else 0) = ∑ t ∈ Icc 1 (N / m), f t := by
  have hterm : ∀ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then f (n / m) else 0) =
      if m ∣ n then f (n / m) else 0 := by
    intro n _
    by_cases h : m ∣ n
    · by_cases h' : m = n
      · subst h'; simp [Nat.div_self hm, hf]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_dvd_Icc_eq_image hm,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h]
  exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]

/-- `P(m, n) √n = √m (Λ(n/m) [m ∣ n] + Λ(m/n) (n/m) [n ∣ m])`, off the diagonal. -/
theorem weilPrimeKernel_mul_sqrt {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    weilPrimeKernel m n * Real.sqrt n = Real.sqrt m *
      ((if m ∣ n ∧ m ≠ n then Λ (n / m) else 0) +
        (if n ∣ m ∧ n ≠ m then Λ (m / n) * ((n : ℝ) / m) else 0)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := weilPrimeKernel_mul_sqrt_ratio hm hn
  have hsq : Real.sqrt n = Real.sqrt ((m : ℝ) / n) * ((n : ℝ) / Real.sqrt m) := by
    rw [Real.sqrt_div' _ hn0.le]
    have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
    have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    field_simp
    rw [Real.sq_sqrt hn0.le]
  rw [hsq, ← mul_assoc, h]
  have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
  have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_pos h1, if_neg h2, if_neg h2, add_zero, add_zero]
    have hcast : ((n / m : ℕ) : ℝ) = (n : ℝ) / m := Nat.cast_div h1.1 (by exact_mod_cast hm.ne')
    rw [hcast]
    field_simp
    rw [Real.sq_sqrt hm0.le]
  · rw [if_neg h1, if_neg h1, zero_add, zero_add]
    by_cases h2 : n ∣ m ∧ n ≠ m
    · rw [if_pos h2, if_pos h2]
      field_simp
      rw [Real.sq_sqrt hm0.le]
    · rw [if_neg h2, if_neg h2]; ring

/-- **The rows of `√n`**: `Σ_n P(m, n) √n ≤ √m (ψ(⌊N/m⌋) + ½ log m)`. -/
theorem sum_weilPrimeKernel_mul_sqrt_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, weilPrimeKernel m n * Real.sqrt n ≤
      Real.sqrt m * (ψ ((N / m : ℕ) : ℝ) + Real.log m / 2) := by
  rw [sum_congr rfl fun n hn => weilPrimeKernel_mul_sqrt hm (mem_Icc.mp hn).1, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [sum_add_distrib]
  have hup : ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then Λ (n / m) else 0) = ψ ((N / m : ℕ) : ℝ) := by
    rw [sum_up_eq_of_one hm (fun t => Λ t) vonMangoldt_apply_one, Chebyshev.psi,
      Nat.floor_natCast]
    rfl
  have hdown : ∑ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then Λ (m / n) * ((n : ℝ) / m) else 0) ≤
      Real.log m / 2 := by
    rw [← sum_down_eq hm hmN, sum_div]
    refine sum_le_sum fun n hn => ?_
    by_cases h : n ∣ m ∧ n ≠ m
    · rw [if_pos h, if_pos h]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      obtain ⟨k, hk⟩ := h.1
      have hk2 : 2 ≤ k := by
        rcases k with _ | _ | k
        · simp at hk; omega
        · simp at hk; exact absurd hk.symm h.2
        · omega
      have hratio : (n : ℝ) / m ≤ 1 / 2 := by
        rw [hk, Nat.cast_mul, div_le_iff₀ (by positivity)]
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        nlinarith
      have hΛ := vonMangoldt_nonneg (n := m / n)
      nlinarith
    · rw [if_neg h, if_neg h]; norm_num
  rw [hup]
  linarith

/-! ### 3. The tilted pole is a Collatz–Wielandt vector -/

/-- Chebyshev: `ψ(q) ≤ (log 4 + 4) q` for `q ≥ 1`. -/
theorem psi_le_linear {q : ℝ} (hq : 1 ≤ q) : ψ q ≤ (Real.log 4 + 4) * q := by
  have h := Chebyshev.psi_le hq
  have hs := Real.sqrt_nonneg q
  have hlog : Real.log q ≤ 2 * Real.sqrt q := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < q))
    have h2 : Real.log q = 2 * Real.log (Real.sqrt q) := by
      rw [← Real.log_rpow (Real.sqrt_pos.mpr (by linarith)), Real.rpow_two, Real.sq_sqrt (by linarith)]
    linarith
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (by linarith)
  have : 2 * Real.sqrt q * Real.log q ≤ 4 * q := by nlinarith
  linarith

/-- The tilted pole `v_n = n^{−1/2} (1 + η n/N)`. -/
def tiltedPole (N : ℕ) (η : ℝ) (n : ℕ) : ℝ := poleVector n * (1 + η * ((n : ℝ) / N))

theorem poleVector_mul_self {n : ℕ} (hn : 0 < n) : poleVector n * n = Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  unfold poleVector
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hs.ne', Real.mul_self_sqrt hn0.le]

/-- The scalar inequality on the bulk rows. -/
theorem row_scalar_bulk {A lq lm lN g e s η ψv : ℝ} (hM : A - lq < -g + e / 2)
    (hlogs : lq + lm ≤ lN) (hηψ : η * s * ψv ≤ e / 2) (hhalf : lm / 2 ≤ lN - g)
    (hηs : 0 ≤ η * s) (he : 0 ≤ e) :
    A + lm + η * s * (ψv + lm / 2) ≤ (lN - g + e) * (1 + η * s) := by
  nlinarith [mul_le_mul_of_nonneg_left hhalf hηs, mul_nonneg hηs he]

/-- The scalar inequality on the top rows, where the tilt pays. -/
theorem row_scalar_top {A lm lN g e s η ψv AQ : ℝ} (hA : A ≤ AQ) (hηψ : η * s * ψv ≤ e / 2)
    (hlm : lm ≤ lN) (htilt : AQ + g + 1 ≤ η * s * (lN / 2 - g)) (hηs : 0 ≤ η * s) (he : 0 < e) :
    A + lm + η * s * (ψv + lm / 2) ≤ (lN - g + e) * (1 + η * s) := by
  nlinarith [mul_nonneg hηs (sub_nonneg.mpr hlm), mul_nonneg hηs he.le]

/-- **The row inequality from one Mertens threshold.** If `A(q) − log q < −γ + ε/2` for `q ≥ Q₀`, the tilted pole is a
Collatz–Wielandt vector for `log N − γ + ε` at every `N` above the explicit horizon. -/
theorem row_tiltedPole_le_of_mertens_threshold {ε : ℝ} (hε : 0 < ε) {Q₀ : ℕ}
    (hQ₀ : ∀ q : ℕ, Q₀ ≤ q → mertensSum q - Real.log q < -γ + ε / 2) {N : ℕ}
    (hlogN : 2 * γ + 2 * (((Q₀ + 1 : ℕ) : ℝ) * (mertensSum (Q₀ + 1) + γ + 1) /
        (ε / (2 * (Real.log 4 + 4)))) ≤ Real.log N) (hN1 : 1 ≤ N) :
    ∀ m ∈ Icc 1 N,
      ∑ n ∈ Icc 1 N, weilPrimeKernel m n * tiltedPole N (ε / (2 * (Real.log 4 + 4))) n ≤
        (Real.log N - γ + ε) * tiltedPole N (ε / (2 * (Real.log 4 + 4))) m := by
  set c : ℝ := Real.log 4 + 4 with hc
  have hc0 : 0 < c := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  set η : ℝ := ε / (2 * c) with hη
  have hη0 : 0 < η := by positivity
  have hηc : η * c = ε / 2 := by rw [hη]; field_simp
  have hγ0 : 0 < γ := (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  set Q : ℕ := Q₀ + 1
  set AQ : ℝ := mertensSum Q
  have hAQ : 0 ≤ AQ := sum_nonneg fun t _ => div_nonneg vonMangoldt_nonneg (by positivity)
  have hQB : 0 ≤ (Q : ℝ) * (AQ + γ + 1) / η := by positivity
  intro m hm
  obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq1 : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm1).mpr (by linarith)
  have hq1' : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hq1
  -- the row
  have hsplit : ∑ n ∈ Icc 1 N, weilPrimeKernel m n * tiltedPole N η n =
      ∑ n ∈ Icc 1 N, weilPrimeKernel m n * poleVector n +
        η / N * ∑ n ∈ Icc 1 N, weilPrimeKernel m n * Real.sqrt n := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [tiltedPole, ← poleVector_mul_self (mem_Icc.mp hn).1]
    ring
  rw [hsplit, sum_weilPrimeKernel_poleVector hm1 hmN]
  have hroot := mul_le_mul_of_nonneg_left (sum_weilPrimeKernel_mul_sqrt_le hm1 hmN)
    (by positivity : (0 : ℝ) ≤ η / N)
  refine (add_le_add le_rfl hroot).trans ?_
  -- normalize by the pole: `√m = u_m m`
  rw [← poleVector_mul_self hm1]
  have hpu : 0 < poleVector m := by unfold poleVector; positivity
  have e1 : (mertensSum (N / m) + Real.log m) * poleVector m +
      η / N * (poleVector m * m * (ψ ((N / m : ℕ) : ℝ) + Real.log m / 2)) =
      poleVector m * (mertensSum (N / m) + Real.log m +
        η * ((m : ℝ) / N) * (ψ ((N / m : ℕ) : ℝ) + Real.log m / 2)) := by
    field_simp
  rw [e1, tiltedPole, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ hpu.le
  -- the scalar inequality
  have hlogs : Real.log ((N / m : ℕ) : ℝ) + Real.log m ≤ Real.log N := log_div_add_log_le hm1 hmN
  have hlogm : Real.log m ≤ Real.log N := Real.log_le_log hm0 (by exact_mod_cast hmN)
  have hs0 : 0 ≤ (m : ℝ) / N := by positivity
  have hηs : 0 ≤ η * ((m : ℝ) / N) := by positivity
  have hψ : (m : ℝ) / N * ψ ((N / m : ℕ) : ℝ) ≤ c := by
    have h1 := psi_le_linear hq1'
    have h2 : ((N / m : ℕ) : ℝ) * m ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
    have hψ0 : 0 ≤ ψ ((N / m : ℕ) : ℝ) := Chebyshev.psi_nonneg _
    rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
    nlinarith
  have hηψ : η * ((m : ℝ) / N) * ψ ((N / m : ℕ) : ℝ) ≤ ε / 2 := by
    have := mul_le_mul_of_nonneg_left hψ hη0.le
    rw [hηc] at this; linarith
  by_cases hqQ : Q₀ ≤ N / m
  · exact row_scalar_bulk (hQ₀ _ hqQ) hlogs hηψ (by linarith) hηs hε.le
  · have hqQ' : N / m < Q₀ := not_le.mp hqQ
    have hmono : mertensSum (N / m) ≤ AQ := by
      unfold AQ mertensSum
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (by omega))
        fun t _ _ => div_nonneg vonMangoldt_nonneg (by positivity)
    have hlt : N < (N / m + 1) * m := by
      have := Nat.lt_succ_self (N / m)
      rwa [Nat.div_lt_iff_lt_mul hm1] at this
    have hNQ : N ≤ Q * m := by
      have : N / m + 1 ≤ Q := by omega
      nlinarith
    have hQ0 : (0 : ℝ) < Q := by positivity
    have hsQ : 1 / (Q : ℝ) ≤ (m : ℝ) / N := by
      rw [div_le_div_iff₀ hQ0 hN0, one_mul, mul_comm]
      exact_mod_cast hNQ
    have hhalf0 : 0 ≤ Real.log N / 2 - γ := by linarith
    have htilt : AQ + γ + 1 ≤ η * ((m : ℝ) / N) * (Real.log N / 2 - γ) := by
      have h1 : η / Q ≤ η * ((m : ℝ) / N) := by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hsQ hη0.le
      have h2 : AQ + γ + 1 ≤ η / Q * (Real.log N / 2 - γ) := by
        have e : η / Q * (Q * (AQ + γ + 1) / η) = AQ + γ + 1 := by
          field_simp
        have : Q * (AQ + γ + 1) / η ≤ Real.log N / 2 - γ := by linarith
        calc AQ + γ + 1 = η / Q * (Q * (AQ + γ + 1) / η) := e.symm
          _ ≤ η / Q * (Real.log N / 2 - γ) :=
            mul_le_mul_of_nonneg_left this (by positivity)
      exact h2.trans (mul_le_mul_of_nonneg_right h1 hhalf0)
    exact row_scalar_top hmono hηψ hlogm htilt hηs hε

/-- **The tilted pole is a Collatz–Wielandt vector for `log N − γ + ε`.** -/
theorem eventually_row_tiltedPole_le {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ m ∈ Icc 1 N,
      ∑ n ∈ Icc 1 N, weilPrimeKernel m n * tiltedPole N (ε / (2 * (Real.log 4 + 4))) n ≤
        (Real.log N - γ + ε) * tiltedPole N (ε / (2 * (Real.log 4 + 4))) m := by
  have hγ0 : 0 < γ := (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp
    (tendsto_mertensSum_sub_log.eventually (gt_mem_nhds (by linarith : -γ < -γ + ε / 2)))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (2 * γ + 2 * (((Q₀ + 1 : ℕ) : ℝ) * (mertensSum (Q₀ + 1) + γ + 1) /
        (ε / (2 * (Real.log 4 + 4))))))
  exact ⟨N₀ + 1, fun N hN => row_tiltedPole_le_of_mertens_threshold hε hQ₀ (hN₀ N (by omega)) (by omega)⟩

/-! ### 4. The sharp counterterm -/

/-- The tilted pole row inequality bounds the atomic prime form on every vector. -/
theorem atomicWeilForm_le_sharp_of_row {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hrow : ∀ m ∈ Icc 1 N,
      ∑ n ∈ Icc 1 N, weilPrimeKernel m n * tiltedPole N (ε / (2 * (Real.log 4 + 4))) n ≤
        (Real.log N - γ + ε) * tiltedPole N (ε / (2 * (Real.log 4 + 4))) m) (x : ℕ → ℝ) :
    atomicWeilForm N x ≤ (Real.log N - γ + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  refine atomicWeilForm_le_of_weight _ (fun n hn => ?_) hrow x
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have : 0 < ε / (2 * (Real.log 4 + 4)) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  unfold tiltedPole poleVector
  have : (0 : ℝ) < N := by
    have := (mem_Icc.mp hn).2; have := (mem_Icc.mp hn).1; exact_mod_cast (by omega : 0 < N)
  positivity

/-- **The top of the atomic prime form is at most `log N − γ + ε`**, eventually in `N`, on every
vector. -/
theorem eventually_atomicWeilForm_le_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x : ℕ → ℝ,
      atomicWeilForm N x ≤ (Real.log N - γ + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := eventually_row_tiltedPole_le hε
  exact ⟨N₀, fun N hN x => atomicWeilForm_le_sharp_of_row hε (hN₀ N hN) x⟩

/-- **The covariant counterterm is `log N − γ + o(1)`.** For every `ε > 0`, eventually the scalar
`log N − γ + ε` renormalizes the atomic prime form, and every renormalizing scalar is at least
`log N − γ − ε`: the pole vector is extremal. -/
theorem covariantCounterterm_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      (∀ x : ℕ → ℝ, atomicWeilForm N x ≤ (Real.log N - γ + ε) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
        ∀ κ : ℝ, (∀ x : ℕ → ℝ, atomicWeilForm N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2) →
          Real.log N - γ - ε ≤ κ := by
  obtain ⟨N₁, h₁⟩ := eventually_atomicWeilForm_le_sharp hε
  obtain ⟨N₂, h₂⟩ := eventually_atomicWeilForm_truncPole_ge hε
  refine ⟨max (max N₁ N₂) 1, fun N hN => ⟨h₁ N (by omega), fun κ hκ => ?_⟩⟩
  have hlow := h₂ N (by omega)
  have hup := hκ (truncPole N)
  have hmass : 0 < ∑ n ∈ Icc 1 N, truncPole N n ^ 2 := by
    refine sum_pos (fun n hn => ?_) ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hn := mem_Icc.mp hn
    simp only [truncPole, if_pos hn.2]
    have : (0 : ℝ) < n := by exact_mod_cast hn.1
    unfold poleVector; positivity
  exact le_of_mul_le_mul_right (hlow.trans hup) hmass

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
