import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusCancellationAndOddDilationMeans
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeSquarefreeDensityAndMobiusDilationMeans
import GaloisForLFunctions.BezoutValuationIncidence.TranslatedWindowStrideAnnihilationAndLcmReturnObservability

/-!
# Coprime Möbius sign and even dilation means

Full-radical reduction removes the squarefree-modulus restriction from the
existing squarefree mean. Together with the existing signed mean, it gives
exact frequencies for either Möbius sign and their rationally scaled prefixes.

Every positive even dilation product then has its finite Euler-product mean,
including overlapping prime supports and zero multipliers. These arithmetic
producers support the cofinal source-value law.
-/

open Filter Topology Finset ArithmeticFunction
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

private theorem squarefree_mean_full_radical {Q : ℕ} (hQ : Q ≠ 0) (x : ℝ) :
    coprimeSquarefreeMean (primeRadical Q) x = coprimeSquarefreeMean Q x := by
  have hR : primeRadical Q ≠ 0 :=
    (show 0 < primeRadical Q from
      Finset.prod_pos fun _ hp => (Nat.mem_primeFactors.mp hp).1.pos).ne'
  unfold coprimeSquarefreeMean coprimeSquarefreeCount
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hcop : Nat.Coprime (primeRadical Q) n ↔ Nat.Coprime Q n := by
    rw [← Nat.disjoint_primeFactors hR hn0, ← Nat.disjoint_primeFactors hQ hn0]
    simp only [primeRadical, Nat.primeFactors_prod_primeFactors]
  simp only [coprimeSquarefreeIndicator, hcop]

private theorem squarefree_density_full_radical (Q : ℕ) :
    coprimeSquarefreeDensity (primeRadical Q) = coprimeSquarefreeDensity Q := by
  simp only [coprimeSquarefreeDensity, primeRadical, Nat.primeFactors_prod_primeFactors]

/-- Every finite local coprimality factor preserves strict positivity. -/
theorem coprimeSquarefreeDensity_pos (Q : ℕ) : 0 < coprimeSquarefreeDensity Q := by
  have hD : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  unfold coprimeSquarefreeDensity
  apply mul_pos hD
  apply Finset.prod_pos
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos
  exact div_pos hpR (by linarith)

/-- Coprimality only sees prime support, so repeated factors do not change the density. -/
theorem tendsto_coprimeSquarefreeMean_positive_modulus (Q : ℕ+) :
    Tendsto (coprimeSquarefreeMean Q) atTop (𝓝 (coprimeSquarefreeDensity Q)) := by
  have h := tendsto_coprimeSquarefreeMean_of_squarefree (primeRadical Q)
    (squarefree_primeRadical Q Q.property.ne')
  have heq : coprimeSquarefreeMean (primeRadical Q) = coprimeSquarefreeMean Q :=
    funext (squarefree_mean_full_radical Q.property.ne')
  rw [heq, squarefree_density_full_radical] at h
  exact h

/-- Literal count of either Möbius sign among integers coprime to the modulus. -/
def coprimeMoebiusSignCount (Q M : ℕ) (positive : Bool) : ℕ :=
  ((Finset.Icc 1 M).filter (fun n => Nat.Coprime Q n ∧
    μ n = (if positive then 1 else -1))).card

/-- The literal sign count at the natural floor, normalized by the real endpoint. -/
def coprimeMoebiusSignMean (Q : ℕ) (positive : Bool) (x : ℝ) : ℝ :=
  (coprimeMoebiusSignCount Q ⌊x⌋₊ positive : ℝ) / x

private theorem sign_indicator_split (Q n : ℕ) (positive : Bool) :
    (if Nat.Coprime Q n ∧ μ n = (if positive then 1 else -1) then (1 : ℝ) else 0) =
      (coprimeSquarefreeIndicator Q n +
        (if positive then 1 else -1) * coprimeMoebiusIndicator Q n) / 2 := by
  by_cases hc : Nat.Coprime Q n
  · rw [coprimeSquarefreeIndicator, if_pos hc, coprimeMoebiusIndicator, if_pos hc]
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
      cases positive <;> norm_num [hc, h]
  · simp [coprimeSquarefreeIndicator, coprimeMoebiusIndicator, hc]

private theorem sign_count_split (Q M : ℕ) (positive : Bool) :
    (coprimeMoebiusSignCount Q M positive : ℝ) =
      (coprimeSquarefreeCount Q M +
        (if positive then 1 else -1) * coprimeMoebiusSum Q M) / 2 := by
  have hcard : (coprimeMoebiusSignCount Q M positive : ℝ) =
      ∑ n ∈ Finset.Icc 1 M,
        if Nat.Coprime Q n ∧ μ n = (if positive then 1 else -1) then (1 : ℝ) else 0 := by
    simp [coprimeMoebiusSignCount]
  rw [hcard]
  simp_rw [sign_indicator_split]
  unfold coprimeSquarefreeCount coprimeMoebiusSum
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem sign_mean_split (Q : ℕ) (positive : Bool) (x : ℝ) :
    coprimeMoebiusSignMean Q positive x =
      (coprimeSquarefreeMean Q x +
        (if positive then 1 else -1) * coprimeMoebiusMean Q x) / 2 := by
  rw [coprimeMoebiusSignMean, sign_count_split, coprimeSquarefreeMean, coprimeMoebiusMean]
  ring

/-- The two Möbius signs split every positive-modulus squarefree density equally. -/
theorem tendsto_coprimeMoebiusSignMean (Q : ℕ+) (positive : Bool) :
    Tendsto (coprimeMoebiusSignMean Q positive) atTop
      (𝓝 (coprimeSquarefreeDensity Q / 2)) := by
  have h := ((tendsto_coprimeSquarefreeMean_positive_modulus Q).add
    ((tendsto_coprimeMoebiusMean Q).const_mul (if positive then (1 : ℝ) else -1))).div_const 2
  simpa only [← sign_mean_split, mul_zero, add_zero] using h

/-- Each literal sign prefix has its expected mean at every fixed positive rational scale. -/
theorem tendsto_coprimeMoebiusSignCount_scaled (Q A d : ℕ+) (positive : Bool) :
    Tendsto (fun N : ℕ =>
      (coprimeMoebiusSignCount Q ((A : ℕ) * N / d) positive : ℝ) / (N : ℝ))
      atTop (𝓝 (((A : ℕ) : ℝ) / (d : ℕ) * (coprimeSquarefreeDensity Q / 2))) := by
  have hAR : (0 : ℝ) < (A : ℕ) := by exact_mod_cast A.property
  have hdR : (0 : ℝ) < (d : ℕ) := by exact_mod_cast d.property
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => ((A : ℕ) : ℝ) * N / (d : ℕ)) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (div_pos hAR hdR)).mpr hnat
    simpa only [div_mul_eq_mul_div] using h
  have hmean := ((tendsto_coprimeMoebiusSignMean Q positive).comp hscale).const_mul
    (((A : ℕ) : ℝ) / (d : ℕ))
  change Tendsto (fun N : ℕ => ((A : ℕ) : ℝ) / (d : ℕ) *
    ((coprimeMoebiusSignCount Q ⌊((A : ℕ) : ℝ) * N / (d : ℕ)⌋₊ positive : ℝ) /
      (((A : ℕ) : ℝ) * N / (d : ℕ)))) atTop
    (𝓝 (((A : ℕ) : ℝ) / (d : ℕ) * (coprimeSquarefreeDensity Q / 2))) at hmean
  apply hmean.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hfloor : ⌊((A : ℕ) : ℝ) * N / (d : ℕ)⌋₊ = (A : ℕ) * N / d := by
    rw [← Nat.cast_mul, Nat.floor_div_eq_div]
  rw [hfloor]
  field_simp

private theorem even_dilation_product (r : ℕ) (a : Fin (2 * r + 2) → ℕ) (n : ℕ) :
    (∏ i, ((μ (a i * n) : ℤ) : ℝ)) =
      (∏ i, ((μ (a i) : ℤ) : ℝ)) * coprimeSquarefreeIndicator (∏ i, a i) n := by
  have hp : ((μ n : ℤ) : ℝ) ^ (2 * r + 2) = ((μ n : ℤ) : ℝ) ^ 2 := by
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ, moebius_real_odd_pow]
    ring
  rw [moebius_dilation_product_eq_coprime_power]
  simp only [Fintype.card_fin, hp, coprimeSquarefreeIndicator]

/-- Every positive even dilation product has an explicit mean, with overlapping supports allowed. -/
theorem tendsto_moebius_even_dilation_product_mean (r : ℕ)
    (a : Fin (2 * r + 2) → ℕ) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∏ i, ((μ (a i * n) : ℤ) : ℝ)) / x)
      atTop (𝓝 ((∏ i, ((μ (a i) : ℤ) : ℝ)) * coprimeSquarefreeDensity (∏ i, a i))) := by
  let Q := ∏ i, a i
  let C : ℝ := ∏ i, ((μ (a i) : ℤ) : ℝ)
  have heq (x : ℝ) :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∏ i, ((μ (a i * n) : ℤ) : ℝ)) / x =
        C * coprimeSquarefreeMean Q x := by
    simp_rw [even_dilation_product]
    unfold coprimeSquarefreeMean coprimeSquarefreeCount
    rw [← Finset.mul_sum]
    dsimp [C, Q]
    ring
  simp_rw [heq]
  change Tendsto (fun x : ℝ => C * coprimeSquarefreeMean Q x) atTop
    (𝓝 (C * coprimeSquarefreeDensity Q))
  by_cases hQ : Q = 0
  · have hC : C = 0 := by
      obtain ⟨i, hi, hz⟩ := Finset.prod_eq_zero_iff.mp hQ
      exact Finset.prod_eq_zero hi (by simp [hz])
    simpa only [hC, zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  · exact (tendsto_coprimeSquarefreeMean_positive_modulus
      ⟨Q, Nat.pos_of_ne_zero hQ⟩).const_mul C

end
end GaloisForLFunctions.BezoutValuationIncidence
