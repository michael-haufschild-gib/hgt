import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PolynomialProgressionStatement
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PolynomialZeroSum
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.TruncatedExplicitFormula
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.FarRangeScales
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevPacketAssembly

/-! In the large-modulus range the weighted zero sum controls the relative character error. -/

open Finset Complex Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

theorem psi_relative_far_range_polynomial (hS : SharpenS) :
    ∀ cA : ℝ, 0 < cA → PsiRelPolynomialB cA := by
  intro cA hcA
  obtain ⟨κ, hκ, hκ', hZ⟩ := polynomial_zero_sum
  obtain ⟨C, hC, hEx⟩ := truncated_explicit_formula_with_orders κ hκ hκ'
  obtain ⟨cz, Az, Cz, hcz, hAz, _, hZ⟩ := hZ 12 (by norm_num)
  obtain ⟨C₀, B, hC₀, hB, hnum⟩ := num_main cA κ C hcA hκ hC
  obtain ⟨c₁, hc₁, heta⟩ := etaOf_lower 1 one_pos
  refine ⟨min cz (cA ^ 2), 22 * Az + B / c₁, max Cz C₀, lt_min hcz (by positivity), ?_⟩
  intro M _ h8 y hy hr1 hr2
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8r : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM3 : 3 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by linarith
  have hy0 : 0 < y := by linarith
  have hT8 : (8 : ℝ) ≤ (M : ℝ) ^ (12 : ℝ) := by
    calc (8 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hM8r
      _ ≤ (M : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hδ0 : 0 < ((M : ℝ) ^ 5)⁻¹ := by positivity
  have hδ : ((M : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    apply inv_anti₀ (by norm_num)
    calc (2 : ℝ) ≤ (M : ℝ) ^ 1 := by rw [pow_one]; linarith
      _ ≤ (M : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  choose Z m K h1 h2 hord h3 h4 h5 h6 using fun χ => hEx M χ ((M : ℝ) ^ (12 : ℝ)) hM3 (by linarith)
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hrz : Cz * Real.log M ≤ Real.log y :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogM).trans hr1
  have hrn : C₀ * Real.log M ≤ Real.log y :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hlogM).trans hr1
  have hZS := hZ M Z m hM8 h1 hord y hy hrz
  have hN := hnum M y hM8r hy hrn hr2
  generalize hTdef : (M : ℝ) ^ (12 : ℝ) = T at *
  generalize hδdef : ((M : ℝ) ^ 5)⁻¹ = δ at *
  generalize htdef : y ^ (-(κ / 2)) = t at *
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = C * (((M : ℝ) * T) ^ C * t
      + Real.log (2 * y) * Real.log ((M : ℝ) * T) ^ 2 / T) := ⟨_, rfl⟩
  rw [← hEdef] at hN
  have hT0 : 0 < T := by linarith
  have ht0 : 0 ≤ t := by rw [← htdef]; positivity
  have hlg : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hre : ∀ χ, ∀ ρ ∈ Z χ, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
    intro χ ρ hρ
    obtain ⟨hz, hlo, -⟩ := h1 χ ρ hρ
    exact ⟨by linarith only [hlo, hκ'], re_lt_one_of_isLZero hz⟩
  have hEu : ∀ u : ℝ, y ≤ u → u ≤ 2 * y →
      C * (((M : ℝ) * T) ^ C * u ^ (-(κ / 2)) + Real.log u * Real.log ((M : ℝ) * T) ^ 2 / T) ≤ E := by
    intro u hu1 hu2
    rw [hEdef]
    have a1 : u ^ (-(κ / 2)) ≤ t := by
      rw [← htdef]; exact Real.rpow_le_rpow_of_nonpos hy0 hu1 (by linarith)
    have a2 : Real.log u ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hu2
    gcongr
  obtain ⟨W, hW⟩ : ∃ W : DirichletCharacter ℂ M → ℝ, W = fun χ =>
      ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) := ⟨_, rfl⟩
  have hsum := psi_total_from_zero_packets hM3 hS Z m K y κ T δ E hy hT0.le hδ0 hδ hE0 h2 hre h3
    (fun χ u hu => by
      obtain ⟨hu1, hu2⟩ : y ≤ u ∧ u ≤ 2 * y := by
        rcases hu with rfl | rfl
        · exact ⟨le_rfl, by linarith only [hy]⟩
        · exact ⟨le_mul_of_one_le_left hy0.le (by linarith only [hδ0]),
            mul_le_mul_of_nonneg_right (by linarith only [hδ]) hy0.le⟩
      exact (h6 χ u (hy.trans hu1)).trans (hEu u hu1 hu2))
  rw [← hW, htdef] at hsum
  have hη0 : 0 < etaOf M := etaOf_pos M (by omega)
  have hex := inv_le_exp hcA (lt_min hcz (by positivity : 0 < cA ^ 2)) (min_le_right _ _) hM8r hy hr2
  have hηM : (M : ℝ)⁻¹ ≤ etaOf M / c₁ := by
    have := heta M hM3
    rw [Real.rpow_neg_one] at this
    rw [le_div_iff₀ hc₁]; linarith
  have hMi : 0 < (M : ℝ)⁻¹ := by positivity
  have hWs : ∑ χ, W χ ≤ Az * etaOf M * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
    rw [hW]
    refine hZS.trans ?_
    have e1 : Real.exp (-(cz * Real.log y / Real.log M))
        ≤ Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have : min cz (cA ^ 2) ≤ cz := min_le_left _ _
      gcongr
    gcongr
  have hfin : B * y * ((M : ℝ)⁻¹ * (M : ℝ)⁻¹)
      ≤ B * y * (etaOf M / c₁ * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M))) := by
    gcongr
  generalize Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) = ex at *
  have f1 : 22 * y * ∑ χ, W χ ≤ 22 * y * (Az * etaOf M * ex) :=
    mul_le_mul_of_nonneg_left hWs (by positivity)
  have f2 : (22 * Az + B / c₁) * y * etaOf M * ex
      = 22 * y * (Az * etaOf M * ex) + B * y * (etaOf M / c₁ * ex) := by ring
  rw [f2]
  linarith

end QH.PrimeProgressions
