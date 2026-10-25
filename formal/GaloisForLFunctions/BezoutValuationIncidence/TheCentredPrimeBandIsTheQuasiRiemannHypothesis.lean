import GaloisForLFunctions.BezoutValuationIncidence.TheCentredPrimeBandForcesAZeroFreeStrip

/-!
# The balanced prime statistic is the quasi-Riemann hypothesis

For the centred prime row `(Λ - 1)𝟙_{(Q,2Q]}`, a power saving of the dual-norm statistic on a
neighbourhood `Q^{1-ε} ≤ d ≤ Q^{1+ε}` of the diagonal holds if and only if `Θ < 1`
(`centredPrimeBandPowerSaving_iff`). With `balancedStatisticPowerSaving_iff` this covers both
actual rows of the balanced cross-scale Gram: on the diagonal the first rung of each is exactly a
zero-free strip.

* `⇒`: the chain of blocks bounds `Σ_{n > X} (Λ(n) - 1)/n² ≪ X^{-1-κ}`; Abel summation gives
  `ψ(N) - N ≪ N^{1-κ}` and the square-sample exponent law `Θ ≤ 1 - κ`.
* `⇐`: `ψ(N) - N ≪ N^{Θ+ε}` bounds the long-window partial sums of the window, and the archimedean
  law gives the saving `Q^{-(1-Θ)/8}` on the band of width `(1-Θ)/8`.
-/

open Finset Filter Topology ArithmeticFunction RHTower
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- **A power saving for the balanced prime statistic forces a zero-free strip.** -/
theorem zetaZeroAbscissa_lt_one_of_centredPrimeBandPowerSaving (h : CentredPrimeBandPowerSaving) :
    zetaZeroAbscissa < 1 := by
  obtain ⟨ε, η, C, hε, hη, hband⟩ := h
  have hC : 0 ≤ C := by
    have h2 := hband 2 2 le_rfl
      (by calc ((2 : ℕ) : ℝ) ^ (1 - ε) ≤ ((2 : ℕ) : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = ((2 : ℕ) : ℝ) := Real.rpow_one _)
      (by calc ((2 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ ((2 : ℕ) : ℝ) ^ (1 + ε) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    have hp : (0 : ℝ) < (((2 : ℕ) : ℝ) ^ 2 / ((2 : ℕ) : ℝ)) * ((2 : ℕ) : ℝ) ^ (-η) := by positivity
    have key := (abs_nonneg _).trans h2
    rw [mul_assoc] at key
    exact (mul_nonneg_iff_of_pos_right hp).mp key
  set e := min ε (1 / 2) with hedef
  have he : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have hband' : ∀ Q d : ℕ, 2 ≤ Q → (Q : ℝ) ^ (1 - e) ≤ d → (d : ℝ) ≤ (Q : ℝ) ^ (1 + e) →
      |kernelStatisticAll (2 * Q) (centredPrimeBlock Q) d| ≤ C * ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-η) := by
    intro Q d hQ hlo hhi
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
    exact hband Q d hQ ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hlo)
      (hhi.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)))
  set κ := min η (e / 2) with hκdef
  have hκ0 : 0 < κ := lt_min hη (by positivity)
  have hκe : κ ≤ e / 2 := min_le_right _ _
  have hκ1 : κ < 1 := by linarith
  set X₀ : ℕ := ⌈(2 : ℝ) ^ (1 / e)⌉₊ + 2 with hX₀
  have hX₀le : ∀ X : ℕ, X₀ ≤ X → (2 : ℝ) ^ (1 / e) ≤ X := fun X hX => by
    have h1 := Nat.le_ceil ((2 : ℝ) ^ (1 / e))
    have h2 : ((⌈(2 : ℝ) ^ (1 / e)⌉₊ : ℕ) : ℝ) ≤ X := by exact_mod_cast (by omega : ⌈(2 : ℝ) ^ (1 / e)⌉₊ ≤ X)
    linarith
  set K₁ := 24 / Real.pi ^ 2 * (4 * C + 80 * (1 + 6 / e) ^ 3) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hstep : ∀ X, X₀ ≤ X → 2 * X ≤ primeBlockStep e X := fun X hX =>
    two_mul_le_primeBlockStep he (hX₀le X hX)
  have hblock : ∀ X, X₀ ≤ X →
      |∑ n ∈ Ioc X (primeBlockStep e X), primeSqTerm n| ≤ K₁ * (X : ℝ) ^ (-1 - κ) := fun X hX =>
    abs_primeBlockStep_le he he1 hη hC hband' (by omega) (two_le_rpow_of_le he (hX₀le X hX))
  have hc := summable_primeSqTerm.hasSum
  set c' := ∑' n, primeSqTerm n
  have htail : ∀ X, X₀ ≤ X → |primeSqSum X - c'| ≤ 2 * K₁ * (X : ℝ) ^ (-1 - κ) := fun X hX =>
    abs_sum_Ioc_sub_tsum_le_of_blocks (by simp [primeSqTerm]) hc hK₁0 hκ0.le (by omega) hstep
      hblock hX
  -- the finitely many small `n`
  set A := ∑' n, |primeSqTerm n|
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => abs_nonneg _
  have hSA : ∀ n, |primeSqSum n| ≤ A := fun n =>
    (abs_sum_le_sum_abs _ _).trans (sum_le_hasSum _ (fun _ _ => abs_nonneg _) summable_primeSqTerm.abs.hasSum)
  have hcA : |c'| ≤ A := by
    have := norm_tsum_le_tsum_norm summable_primeSqTerm.norm
    simpa only [Real.norm_eq_abs] using this
  set C₃ := 2 * K₁ + 2 * A * (X₀ : ℝ) ^ (1 + κ)
  have hC₃ : 0 ≤ C₃ := by positivity
  have hD : ∀ n : ℕ, 1 ≤ n → |primeSqSum n - c'| ≤ C₃ * (n : ℝ) ^ (-1 - κ) := by
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow0 : 0 ≤ (n : ℝ) ^ (-1 - κ) := Real.rpow_nonneg (by linarith) _
    rcases le_or_gt X₀ n with hXn | hnX
    · refine (htail n hXn).trans ?_
      have : 0 ≤ 2 * A * (X₀ : ℝ) ^ (1 + κ) * (n : ℝ) ^ (-1 - κ) := by positivity
      nlinarith
    · have h1 : |primeSqSum n - c'| ≤ 2 * A := by
        have := abs_sub (primeSqSum n) c'
        linarith [hSA n]
      have h2 : 1 ≤ (X₀ : ℝ) ^ (1 + κ) * (n : ℝ) ^ (-1 - κ) := by
        have hle : (n : ℝ) ≤ X₀ := by exact_mod_cast hnX.le
        have h3 : (n : ℝ) ^ (1 + κ) ≤ (X₀ : ℝ) ^ (1 + κ) :=
          Real.rpow_le_rpow (by linarith) hle (by linarith)
        have h4 : (n : ℝ) ^ (1 + κ) * (n : ℝ) ^ (-1 - κ) = 1 := by
          rw [← Real.rpow_add (by linarith)]; norm_num
        nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ n) (-1 - κ)]
      refine h1.trans ?_
      have : 0 ≤ 2 * K₁ * (n : ℝ) ^ (-1 - κ) := by positivity
      nlinarith
  -- Abel summation and the square-sample law
  set K₂ := C₃ + |c'| + 3 * C₃ / (1 - κ)
  have hK₂ : 0 ≤ K₂ := by have : 0 < 1 - κ := by linarith
                          positivity
  have hR : ∀ N : ℕ, 1 ≤ N → |psiRemainder N| ≤ 2 * K₂ * (N : ℝ) ^ (1 - κ) := by
    intro N hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [psiRemainder_eq_sum_sq_mul]
    refine (abs_sum_Ioc_sq_mul_le hκ0 hκ1 hC₃ hD N).trans ?_
    have h1 : ((N : ℝ) + 1) ^ (1 - κ) ≤ 2 * (N : ℝ) ^ (1 - κ) := by
      calc ((N : ℝ) + 1) ^ (1 - κ) ≤ (2 * (N : ℝ)) ^ (1 - κ) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
        _ = (2 : ℝ) ^ (1 - κ) * (N : ℝ) ^ (1 - κ) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 2 * (N : ℝ) ^ (1 - κ) := by
            gcongr
            calc (2 : ℝ) ^ (1 - κ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
    calc K₂ * ((N : ℝ) + 1) ^ (1 - κ) ≤ K₂ * (2 * (N : ℝ) ^ (1 - κ)) :=
          mul_le_mul_of_nonneg_left h1 hK₂
      _ = 2 * K₂ * (N : ℝ) ^ (1 - κ) := by ring
  have := zetaZeroAbscissa_le_of_psiRemainder_le (by positivity) (by linarith) hR
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
