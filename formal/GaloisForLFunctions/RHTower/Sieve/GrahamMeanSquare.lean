import GaloisForLFunctions.RHTower.Sieve.SelbergMoebiusLogDiagonal

/-!
# Graham's mean square for the Barban–Vehov coefficient

Expanding the square into the lcm quadratic form, removing the floor, diagonalising by the totient,
and inserting the logarithmic diagonal bound gives the upper half of Graham's theorem:

`∑_{k ≤ N} ( ∑_{m ∣ k, m ≤ X} μ(m) log(X/m) )² ≤ C·N·(1 + log X) + X² log²X` ,

for every mollifier length `X ≤ N`.  The two error sources are the floor removal, which costs the
square of the `ℓ¹` mass of the coefficients, and the diagonal bound itself.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- Each Barban–Vehov weight is at most `log X` in modulus. -/
theorem abs_barbanVehovWeight_le {X m : ℕ} (hX : 1 ≤ X) :
    |barbanVehovWeight X m| ≤ Real.log X := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
  rw [barbanVehovWeight]
  split_ifs with hmX
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
      exact hlogX
    · have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hmXR : (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast hmX
      have h0 : (0 : ℝ) ≤ Real.log ((X : ℝ) / (m : ℝ)) := by
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ (by linarith)]
        linarith
      have hle : Real.log ((X : ℝ) / (m : ℝ)) ≤ Real.log (X : ℝ) := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      rw [abs_mul, abs_of_nonneg h0]
      calc |(μ m : ℝ)| * Real.log ((X : ℝ) / (m : ℝ))
          ≤ 1 * Real.log ((X : ℝ) / (m : ℝ)) :=
            mul_le_mul_of_nonneg_right (abs_moebius_le_one m) h0
        _ = Real.log ((X : ℝ) / (m : ℝ)) := one_mul _
        _ ≤ Real.log (X : ℝ) := hle
  · rw [abs_zero]
    exact hlogX

/-- The `ℓ¹` mass of the Barban–Vehov weights. -/
theorem sum_abs_barbanVehovWeight_le {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, |barbanVehovWeight X m| ≤ (X : ℝ) * Real.log X := by
  classical
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
  have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 N := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨h1, le_trans h2 hXN⟩
  have hvanish : ∀ m ∈ Finset.Icc 1 N, m ∉ Finset.Icc 1 X → |barbanVehovWeight X m| = 0 := by
    intro m hm hnot
    obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
    have hXm : ¬ m ≤ X := by
      intro hle
      exact hnot (Finset.mem_Icc.mpr ⟨hm1, hle⟩)
    rw [barbanVehovWeight, if_neg hXm, abs_zero]
  rw [← Finset.sum_subset hsub hvanish]
  calc ∑ m ∈ Finset.Icc 1 X, |barbanVehovWeight X m|
      ≤ ∑ m ∈ Finset.Icc 1 X, Real.log (X : ℝ) :=
        Finset.sum_le_sum fun m _ => abs_barbanVehovWeight_le hX
    _ = (X : ℝ) * Real.log (X : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num

/-- **Graham's mean square, upper half.** -/
theorem sum_sq_barbanVehovCoeff_le {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (barbanVehovCoeff X k) ^ 2
      ≤ (N : ℝ) * (4 * coprimeLogMoebiusConst ^ 2 * (1 + Real.log X))
        + ((X : ℝ) * Real.log X) ^ 2 := by
  classical
  have hNpos : ∀ m ∈ Finset.Icc 1 N, 0 < m := by
    intro m hm
    obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hm
    omega
  have hNR : (0 : ℝ) ≤ (N : ℝ) := by positivity
  -- the smooth quadratic form, diagonalised
  have hdiag := sum_div_lcm_eq_totient_diagonal (Finset.Icc 1 N) hNpos (barbanVehovWeight X)
  have hbiUnion : (Finset.Icc 1 N).biUnion Nat.divisors ⊆ Finset.Icc 1 N := by
    intro e he
    obtain ⟨m, hm, hem⟩ := Finset.mem_biUnion.mp he
    obtain ⟨-, hmN⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hdvd, hm0⟩ := Nat.mem_divisors.mp hem
    have hpos : 0 < e := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hm0)
    have hle : e ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
    exact Finset.mem_Icc.mpr ⟨hpos, le_trans hle hmN⟩
  have hnn : ∀ e ∈ Finset.Icc 1 N, e ∉ (Finset.Icc 1 N).biUnion Nat.divisors →
      (0 : ℝ) ≤ (Nat.totient e : ℝ) *
        (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m),
          barbanVehovWeight X m / (m : ℝ)) ^ 2 := by
    intro e _ _
    positivity
  have hform : ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      barbanVehovWeight X p.1 * barbanVehovWeight X p.2 / (Nat.lcm p.1 p.2 : ℝ)
      ≤ 4 * coprimeLogMoebiusConst ^ 2 * (1 + Real.log X) := by
    rw [hdiag]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hbiUnion hnn) ?_
    exact barbanVehov_totient_diagonal_le hXN
  -- the floor removal
  have hfloor := abs_sum_sq_divisorSum_sub_lcm_main_le N (barbanVehovWeight X)
  have hmain : ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      barbanVehovWeight X p.1 * barbanVehovWeight X p.2 * ((N : ℝ) / (Nat.lcm p.1 p.2 : ℝ))
      = (N : ℝ) * ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
          barbanVehovWeight X p.1 * barbanVehovWeight X p.2 / (Nat.lcm p.1 p.2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have herr : ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      |barbanVehovWeight X p.1| * |barbanVehovWeight X p.2|
      = (∑ m ∈ Finset.Icc 1 N, |barbanVehovWeight X m|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  have hl1 := sum_abs_barbanVehovWeight_le hX hXN
  have hl1nn : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 N, |barbanVehovWeight X m| :=
    Finset.sum_nonneg fun m _ => abs_nonneg _
  have herrle : (∑ m ∈ Finset.Icc 1 N, |barbanVehovWeight X m|) ^ 2
      ≤ ((X : ℝ) * Real.log X) ^ 2 := by
    have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hlogX : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
    nlinarith [hl1, hl1nn]
  have hsub := abs_sub_le_iff.mp hfloor
  have hcoeff : ∀ k ∈ Finset.Icc 1 N,
      (∑ m ∈ k.divisors, barbanVehovWeight X m) ^ 2 = (barbanVehovCoeff X k) ^ 2 := by
    intro k _
    rw [barbanVehovCoeff]
  rw [← Finset.sum_congr rfl hcoeff]
  rw [herr] at hsub
  have hmainle : (N : ℝ) * ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      barbanVehovWeight X p.1 * barbanVehovWeight X p.2 / (Nat.lcm p.1 p.2 : ℝ)
      ≤ (N : ℝ) * (4 * coprimeLogMoebiusConst ^ 2 * (1 + Real.log X)) :=
    mul_le_mul_of_nonneg_left hform hNR
  rw [hmain] at hsub
  linarith [hsub.1, hmainle, herrle]

end RHTower.Sieve
