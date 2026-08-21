import GaloisForLFunctions.HTGeometry.PoincareTermAppellHumbertDecay

/-!
# Seeds of polynomially bounded normalised modulus

The seeds the induction actually produces are a lower-automorphic form of bounded normalised modulus
multiplied by an interpolating **polynomial**, so their normalised modulus is bounded only
polynomially:

`‖seed y‖ ≤ M · (1 + ‖y‖)^N · exp((π/2)·Re H_l(y,y))`.

The polynomial factor costs nothing: at the complement translate it contributes `(1 + ‖z‖ + ‖γ‖)^N`,
and a Gaussian in the lattice index absorbs any power of `‖γ‖` at the price of a constant and half
the Gaussian rate.  The absorption is algebraic — `1 + t ≤ exp t` and the maximum of `a·u − b·u²` —
with no limiting argument.

* `one_add_pow_le_exp`, `poly_gaussian_absorb`;
* `norm_poincareTerm_appellHumbert_poly_le` — the decay estimate for a polynomially bounded seed.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem one_add_pow_le_exp {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    (1 + t) ^ N ≤ Real.exp ((N : ℝ) * t) := by
  have h1 : (1 : ℝ) + t ≤ Real.exp t := Real.add_one_le_exp t |>.trans_eq' (by ring)
  have h2 : (1 + t) ^ N ≤ (Real.exp t) ^ N := by
    refine pow_le_pow_left₀ (by linarith) h1 N
  refine le_trans h2 (le_of_eq ?_)
  rw [← Real.exp_nat_mul]

/-- **A Gaussian in the lattice index absorbs any power of the index.** -/
theorem poly_gaussian_absorb {N : ℕ} {Cv sigma t s : ℝ} (hsigma : 0 < sigma)
    (hs : 0 ≤ s) (ht0 : 0 ≤ t) (ht : t ≤ Cv * Real.sqrt s) :
    (1 + t) ^ N * Real.exp (-sigma * s)
      ≤ Real.exp (((N : ℝ) * Cv) ^ 2 / (2 * sigma)) * Real.exp (-(sigma / 2) * s) := by
  have hu : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have hunn : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hpow : (1 + t) ^ N ≤ Real.exp ((N : ℝ) * t) := one_add_pow_le_exp ht0 N
  have hexp : Real.exp ((N : ℝ) * t) * Real.exp (-sigma * s)
      ≤ Real.exp (((N : ℝ) * Cv) ^ 2 / (2 * sigma)) * Real.exp (-(sigma / 2) * s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hNt : (N : ℝ) * t ≤ (N : ℝ) * (Cv * Real.sqrt s) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N)
    have hkey : (N : ℝ) * (Cv * Real.sqrt s) - sigma * s
        ≤ ((N : ℝ) * Cv) ^ 2 / (2 * sigma) - sigma / 2 * s := by
      have hcore : (N : ℝ) * Cv * Real.sqrt s
          ≤ sigma / 2 * Real.sqrt s ^ 2 + ((N : ℝ) * Cv) ^ 2 / (2 * sigma) := by
        have h2 : 0 ≤ (sigma * Real.sqrt s - (N : ℝ) * Cv) ^ 2 := sq_nonneg _
        have hrhs : 2 * sigma * (sigma / 2 * Real.sqrt s ^ 2
            + ((N : ℝ) * Cv) ^ 2 / (2 * sigma))
            = sigma ^ 2 * Real.sqrt s ^ 2 + ((N : ℝ) * Cv) ^ 2 := by
          field_simp
        have h3 : 2 * sigma * ((N : ℝ) * Cv * Real.sqrt s)
            ≤ 2 * sigma * (sigma / 2 * Real.sqrt s ^ 2
              + ((N : ℝ) * Cv) ^ 2 / (2 * sigma)) := by
          rw [hrhs]
          nlinarith [h2]
        exact le_of_mul_le_mul_left h3 (by positivity)
      rw [hu] at hcore
      linarith
    linarith
  refine le_trans (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)) hexp

section Decay

variable {d : ℕ} {Hu Hl : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χu : (Fin d → ℂ) → ℂ}

/-- **The Poincaré term of a polynomially bounded seed.** -/
theorem norm_poincareTerm_appellHumbert_poly_le (hHu : IsHermitianForm Hu)
    (hHl : IsHermitianForm Hl) (hχu : ∀ γ, ‖χu γ‖ = 1)
    (hpos : ∀ w : Fin d → ℂ, 0 ≤ (Hu w w - Hl w w).re)
    {C : ℝ} (hC : 0 ≤ C) {z : Fin d → ℂ} (hz : (Hu z z - Hl z z).re ≤ C ^ 2)
    {Γ : AddSubgroup (Fin d → ℂ)}
    (hsemiu : IsSemicharacterOn Hu χu Γ)
    (seed : MultivariateEntire d) {M : ℝ} {N : ℕ} (hM : 0 ≤ M)
    (hseednorm : ∀ y : Fin d → ℂ,
      ‖seed.1 y‖ ≤ M * (1 + ‖y‖) ^ N * Real.exp (Real.pi / 2 * (Hl y y).re))
    (γ : Γ) :
    ‖poincareTerm (appellHumbertAutomorphicFactor hHu hχu hsemiu) seed γ z‖
      ≤ M * (1 + ‖z‖ + ‖γ.1‖) ^ N * Real.exp (Real.pi / 2 * (Hl z z).re)
          * Real.exp (Real.pi * C ^ 2)
          * Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re) := by
  have hM' : (0 : ℝ) ≤ M * (1 + ‖z‖ + ‖γ.1‖) ^ N := by positivity
  have hseedz : ‖seed.1 (z + γ.1)‖
      ≤ (M * (1 + ‖z‖ + ‖γ.1‖) ^ N)
        * Real.exp (Real.pi / 2 * (Hl (z + γ.1) (z + γ.1)).re) := by
    refine le_trans (hseednorm (z + γ.1)) ?_
    have htri : ‖z + γ.1‖ ≤ ‖z‖ + ‖γ.1‖ := norm_add_le _ _
    have hmono : (1 + ‖z + γ.1‖) ^ N ≤ (1 + ‖z‖ + ‖γ.1‖) ^ N := by
      refine pow_le_pow_left₀ (by positivity) ?_ N
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hM) (Real.exp_nonneg _)
  exact norm_poincareTerm_appellHumbert_le_at hHu hHl hχu hpos hC hz hsemiu seed hM' γ hseedz

end Decay

end

end GaloisForLFunctions.HTGeometry
