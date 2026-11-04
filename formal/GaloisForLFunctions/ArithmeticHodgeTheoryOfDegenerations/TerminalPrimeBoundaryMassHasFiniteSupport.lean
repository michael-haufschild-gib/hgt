import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheUpwardPrimeWindowsCarryTheShellCorrection

/-!
# Terminal prime boundary mass has finite support

A receiver separated from the origin sees only finitely many prime
multipliers at the horizon boundary. Counting their integer fibres pays
the boundary mass without a short-interval estimate for primes.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- Multiplication by a positive integer injects a horizon boundary fibre into its shell. -/
theorem card_upwardBoundary_fibre_le {N H k : ℕ} (hk : 1 ≤ k) :
    ((Icc 1 N).filter (fun n => N < k * n + H ∧ k * n ≤ N + H)).card ≤
      2 * H + 1 := by
  have hi := card_le_card_of_injOn (s := (Icc 1 N).filter
      (fun n => N < k * n + H ∧ k * n ≤ N + H))
    (t := Icc (N - H) (N + H)) (fun n => k * n)
    (by
      intro n hn
      obtain ⟨_, hlo, hhi⟩ := mem_filter.mp hn
      exact mem_Icc.mpr ⟨by change N - H ≤ k * n; omega, hhi⟩)
    (by
      intro n _ j _ heq
      exact mul_left_cancel₀ (by omega : k ≠ 0) heq)
  apply hi.trans
  rw [Nat.card_Icc]
  omega

/-- Separation from the origin pays the reciprocal receiver mass uniformly in the horizon. -/
theorem sum_terminal_abs_div_le
    {f : ℕ → ℝ} {B δ : ℝ} (hδ : 0 < δ) (hf : ∀ n, |f n| ≤ B)
    {N : ℕ} (hN : 1 ≤ N)
    (hsupp : ∀ n ∈ Icc 1 N, f n ≠ 0 → δ * N ≤ n) :
    (∑ n ∈ Icc 1 N, |f n| / n) ≤ B / δ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  have hδN : 0 < δ * N := mul_pos hδ hN0
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, B / (δ * N) := by
      apply sum_le_sum
      intro n hn
      by_cases hz : f n = 0
      · rw [hz, abs_zero, zero_div]
        exact div_nonneg hB hδN.le
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      exact (div_le_div_of_nonneg_right (hf n) hn0.le).trans
        (div_le_div_of_nonneg_left hB hδN (hsupp n hn hz))
    _ = B / δ := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
      simp only [Nat.add_sub_cancel]
      field_simp [hδ.ne', hN0.ne']

/-- A bounded receiver above `δ N` pays the entire boundary by finitely many prime weights. -/
theorem terminal_upwardBoundaryMass_le
    {f : ℕ → ℝ} {B δ : ℝ} (hδ : 0 < δ) (hf : ∀ n, |f n| ≤ B)
    {N H K : ℕ} (hN : 1 ≤ N) (hH : H ≤ N) (hK : 2 / δ ≤ K)
    (hsupp : ∀ n ∈ Icc 1 N, f n ≠ 0 → δ * N ≤ n) :
    (∑ n ∈ Icc 1 N, |f n| / n * upwardBoundaryMass N n H) ≤
      B * (2 * H + 1) / (δ * N) * (∑ k ∈ Icc 1 K, (Λ k : ℝ) / k) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  have hδN : 0 < δ * N := mul_pos hδ hN0
  let C : ℝ := B * (2 * H + 1) / (δ * N)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let S : ℕ → Finset ℕ := fun k =>
    (Icc 1 N).filter (fun n => N < k * n + H ∧ k * n ≤ N + H)
  have hweight : ∀ n ∈ Icc 1 N, |f n| / n ≤ B / (δ * N) := by
    intro n hn
    by_cases hz : f n = 0
    · rw [hz, abs_zero, zero_div]
      exact div_nonneg hB hδN.le
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    exact (div_le_div_of_nonneg_right (hf n) hn0.le).trans
      (div_le_div_of_nonneg_left hB hδN (hsupp n hn hz))
  have hsmall : ∀ k, 1 ≤ k → (∑ n ∈ S k, |f n| / n) ≤ C := by
    intro k hk
    calc
      _ ≤ ∑ _n ∈ S k, B / (δ * N) :=
        sum_le_sum fun n hn => hweight n (mem_filter.mp hn).1
      _ = (S k).card * (B / (δ * N)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * H + 1 : ℕ) * (B / (δ * N)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_upwardBoundary_fibre_le (N := N) (H := H) hk)
          (div_nonneg hB hδN.le)
      _ = C := by simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, C]; ring
  have hzero : ∀ k, K < k → (∑ n ∈ S k, |f n| / n) = 0 := by
    intro k hk
    apply sum_eq_zero
    intro n hn
    obtain ⟨hnN, _, hkn⟩ := mem_filter.mp hn
    have hz : f n = 0 := by
      by_contra hne
      have hknR : (k : ℝ) * n ≤ 2 * N := by
        exact_mod_cast (hkn.trans (by omega : N + H ≤ 2 * N))
      have hprod : (k : ℝ) * δ * N ≤ 2 * N := by
        calc
          _ = (k : ℝ) * (δ * N) := by ring
          _ ≤ (k : ℝ) * n := mul_le_mul_of_nonneg_left (hsupp n hnN hne) (Nat.cast_nonneg k)
          _ ≤ _ := hknR
      have hkd : (k : ℝ) * δ ≤ 2 := (mul_le_mul_iff_of_pos_right hN0).mp hprod
      have hkK : (k : ℝ) ≤ K := ((le_div_iff₀ hδ).mpr hkd).trans hK
      have : k ≤ K := by exact_mod_cast hkK
      omega
    rw [hz, abs_zero, zero_div]
  have hswap : (∑ n ∈ Icc 1 N, |f n| / n * upwardBoundaryMass N n H) =
      ∑ k ∈ Icc 1 (2 * N), (Λ k : ℝ) / k * ∑ n ∈ S k, |f n| / n := by
    simp only [upwardBoundaryMass, sum_filter, mul_sum, S]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [hswap]
  calc
    _ ≤ ∑ k ∈ (Icc 1 (2 * N)).filter (fun k => k ≤ K), (Λ k : ℝ) / k * C := by
      rw [sum_filter]
      apply sum_le_sum
      intro k hk
      by_cases hkK : k ≤ K
      · rw [if_pos hkK]
        exact mul_le_mul_of_nonneg_left (hsmall k (mem_Icc.mp hk).1) (vonMangoldt_div_nonneg k)
      · rw [if_neg hkK, hzero k (lt_of_not_ge hkK), mul_zero]
    _ ≤ ∑ k ∈ Icc 1 K, (Λ k : ℝ) / k * C := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨hkN, hkK⟩ := mem_filter.mp hk
        exact mem_Icc.mpr ⟨(mem_Icc.mp hkN).1, hkK⟩
      · intro k _ _
        exact mul_nonneg (vonMangoldt_div_nonneg k) hC
    _ = _ := by rw [mul_sum]; exact sum_congr rfl fun _ _ => mul_comm _ _

/-- The fixed linear support of a terminal profile gives the required receiver separation. -/
theorem terminal_profile_upwardBoundaryMass_le
    {F : ℝ → ℝ} {B δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0)
    {N H K : ℕ} (hN : 1 ≤ N) (hH : H ≤ N) (hK : 2 / δ ≤ K) :
    (∑ n ∈ Icc 1 N, |F ((n : ℝ) / N)| / n * upwardBoundaryMass N n H) ≤
      B * (2 * H + 1) / (δ * N) * (∑ k ∈ Icc 1 K, (Λ k : ℝ) / k) := by
  apply terminal_upwardBoundaryMass_le hδ (fun n => hF _) hN hH hK
  intro n _ hn
  have hx : δ < (n : ℝ) / N := lt_of_not_ge fun hx => hn (hzero _ hx)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact ((lt_div_iff₀ hN0).mp hx).le

/-- The actual upward-row comparison retains a finite boundary cost against terminal receivers. -/
theorem abs_terminal_upward_row_sub_model_le
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0)
    {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hGL : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ L * |x - y|)
    {N m H K : ℕ} (hN : 1 ≤ N) (hH1 : 1 ≤ H) (hH : 2 * c ≤ H)
    (hNH : 4 * c * H ≤ N) (hHN : 2 * H ≤ N) (hK : 2 / δ ≤ K)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hac : a * (2 * c) ≤ 1) :
    |∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n *
      (upwardModeRow φ c N m n - upwardModel φ c N m H n)| ≤
      B / δ * |H * m.totient * (2 * upwardLinearError φ c L H / ((∫ u, φ u ^ 2) * N)) *
        (Real.log (2 / a) + mertensWindowConstant)| +
      3 * H * m.totient * (B * (2 * H + 1) / (δ * N)) *
        (∑ k ∈ Icc 1 K, (Λ k : ℝ) / k) := by
  let A : ℝ := H * m.totient * (2 * upwardLinearError φ c L H / ((∫ u, φ u ^ 2) * N)) *
    (Real.log (2 / a) + mertensWindowConstant)
  let D : ℝ := 3 * H * m.totient
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hreceiver : ∀ n ∈ Icc 1 N, F ((n : ℝ) / N) ≠ 0 → δ * N ≤ n := by
    intro n _ hn
    have hx : δ < (n : ℝ) / N := lt_of_not_ge fun hx => hn (hzero _ hx)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact ((lt_div_iff₀ hN0).mp hx).le
  have hmass := sum_terminal_abs_div_le hδ (fun n => hF ((n : ℝ) / N)) hN hreceiver
  have hboundary := terminal_profile_upwardBoundaryMass_le hδ hF hzero hN (by omega : H ≤ N) hK
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |F ((n : ℝ) / N) / n *
        (upwardModeRow φ c N m n - upwardModel φ c N m H n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, |F ((n : ℝ) / N)| / n * (|A| + D * upwardBoundaryMass N n H) := by
      apply sum_le_sum
      intro n hn
      rw [abs_mul, abs_div, Nat.abs_cast]
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (abs_nonneg _) (Nat.cast_nonneg n))
      exact (abs_upwardModeRow_sub_model_le hφ hsupp hM hc hL hGL hH1 hH hNH hHN hn
        ha ha1 hac).trans (add_le_add_right (le_abs_self A) _)
    _ = |A| * (∑ n ∈ Icc 1 N, |F ((n : ℝ) / N)| / n) +
        D * (∑ n ∈ Icc 1 N, |F ((n : ℝ) / N)| / n * upwardBoundaryMass N n H) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ |A| * (B / δ) + D *
        (B * (2 * H + 1) / (δ * N) * (∑ k ∈ Icc 1 K, (Λ k : ℝ) / k)) :=
      add_le_add (mul_le_mul_of_nonneg_left hmass (abs_nonneg A))
        (mul_le_mul_of_nonneg_left hboundary hD)
    _ = _ := by dsimp only [A, D]; ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminal_upwardBoundaryMass_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminal_profile_upwardBoundaryMass_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_upward_row_sub_model_le
