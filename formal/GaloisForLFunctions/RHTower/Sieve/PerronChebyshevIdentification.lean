import GaloisForLFunctions.RHTower.Sieve.LogDominatedByPower
import GaloisForLFunctions.RHTower.Sieve.PerronErrorNearHalfInt
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtPerronSeries
import GaloisForLFunctions.RHTower.Sieve.PerronContourAssembly

/-!
# Identifying the two sides of the Perron formula for `ψ`

At the half-integer cutoff `x = N + 1/2` the Perron sum is exactly the Chebyshev function, and the
Perron integral is exactly the normalised vertical integral of `(−ζ'/ζ)(s)·x^s/s`.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

noncomputable section

/-- The Perron sum at a half-integer cutoff is the Chebyshev function. -/
theorem tsum_indicator_vonMangoldt_eq (N : ℕ) :
    ∑' n : ℕ, (if (n : ℝ) < (N : ℝ) + 1 / 2 then ((Λ n : ℝ) : ℂ) else 0)
      = ((∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) : ℝ) : ℂ) := by
  classical
  have hsupp : ∀ n : ℕ, n ∉ Finset.range (N + 1) →
      (if (n : ℝ) < (N : ℝ) + 1 / 2 then ((Λ n : ℝ) : ℂ) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    refine if_neg ?_
    have : (N : ℝ) + 1 ≤ (n : ℝ) := by
      have : N + 1 ≤ n := by omega
      exact_mod_cast this
    linarith
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ n ∈ Finset.range (N + 1),
      (if (n : ℝ) < (N : ℝ) + 1 / 2 then ((Λ n : ℝ) : ℂ) else 0) = ((Λ n : ℝ) : ℂ) := by
    intro n hn
    rw [Finset.mem_range] at hn
    refine if_pos ?_
    have : (n : ℝ) ≤ (N : ℝ) := by
      have : n ≤ N := by omega
      exact_mod_cast this
    linarith
  rw [Finset.sum_congr rfl hterm]
  rw [show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega]
  rw [Finset.sum_insert (by simp)]
  push_cast
  simp

/-- The Perron integral is the normalised vertical integral of `(−ζ'/ζ)(s)·x^s/s`. -/
theorem perron_integral_eq_vIntegral' {x σ T : ℝ} (hσ : 1 < σ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        (∑' n : ℕ, ((Λ n : ℝ) : ℂ) * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
      = VIntegral' (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
          σ (-T) T := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpt : ∀ t : ℝ,
      (∑' n : ℕ, ((Λ n : ℝ) : ℂ) * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
        = (-deriv riemannZeta ((σ : ℂ) + (t : ℝ) * I)
            / riemannZeta ((σ : ℂ) + (t : ℝ) * I))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)) := by
    intro t
    congr 1
    refine tsum_vonMangoldt_cpow_neg ?_
    have hre : (((σ : ℂ) + (t : ℝ) * I)).re = σ := by simp
    rw [hre]
    exact hσ
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (-deriv riemannZeta ((σ : ℂ) + (t : ℝ) * I) / riemannZeta ((σ : ℂ) + (t : ℝ) * I))
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    (fun t _ => hpt t)]
  rw [VIntegral', VIntegral, smul_smul]
  have hcoef : (1 / (2 * (Real.pi : ℂ) * I)) * I = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    have hIne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hpine : ((Real.pi : ℂ)) ≠ 0 := by
      simp [hpi.ne']
    push_cast
    field_simp
  rw [hcoef, smul_eq_mul]

end

end RHTower.Sieve
