import GaloisForLFunctions.RHTower.Sieve.VonMangoldtPerron

/-!
# The twisted von Mangoldt sum under the Perron formula

Twisting the von Mangoldt coefficients by the character `n ↦ n^{-iτ}` leaves their modulus
unchanged, so the absolute convergence right of the abscissa survives, and their Dirichlet series is
the untwisted one evaluated at `s + iτ`:

```text
∑_n Λ(n) n^{-iτ} n^{-s}  =  -ζ'/ζ (s + iτ)      (Re s > 1).
```

Feeding that into the corpus's smoothed Perron formula writes the twisted smoothed Chebyshev sum as
a vertical integral of `-ζ'/ζ` against the cutoff's Mellin transform, the twist appearing only as a
vertical translation of the integrand.  This is the Perron side of a twisted prime sum, and the
counterpart for `-ζ'/ζ` of the corpus's `moebiusTwist` layer for `1/ζ`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The von Mangoldt function twisted by the character `n ↦ n^{-iτ}`. -/
noncomputable def vonMangoldtTwist (τ : ℝ) (n : ℕ) : ℂ :=
  ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))

@[simp] theorem vonMangoldtTwist_zero (τ : ℝ) : vonMangoldtTwist τ 0 = 0 := by
  simp [vonMangoldtTwist]

/-- The twist does not change the modulus. -/
theorem norm_vonMangoldtTwist (τ : ℝ) (n : ℕ) :
    ‖vonMangoldtTwist τ n‖ = (vonMangoldt n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    have h1 : ‖((n : ℕ) : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ = 1 := by
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp
    rw [vonMangoldtTwist, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]

/-- The twisted von Mangoldt coefficients are absolutely summable right of the abscissa. -/
theorem summable_vonMangoldtTwist_rpow (τ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖vonMangoldtTwist τ n‖ * (n : ℝ) ^ (-σ) := by
  refine (summable_vonMangoldt_rpow hσ).congr fun n => ?_
  rw [norm_vonMangoldtTwist, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]

/-- The Dirichlet series of the twisted von Mangoldt function is the untwisted one, shifted. -/
theorem tsum_vonMangoldtTwist_cpow (τ : ℝ) (s : ℂ) :
    (∑' n : ℕ, vonMangoldtTwist τ n * (n : ℂ) ^ (-s))
      = LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (s + (τ : ℂ) * Complex.I) := by
  rw [← tsum_cpow_neg_eq_LSeries (a := fun n => ((vonMangoldt n : ℝ) : ℂ)) (by simp)
    (s + (τ : ℂ) * Complex.I)]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [vonMangoldtTwist, mul_assoc, ← Complex.cpow_add _ _ hn0,
      show -((τ : ℂ) * Complex.I) + -s = -(s + (τ : ℂ) * Complex.I) by ring]

/-- **The twisted Perron integrand is the shifted logarithmic derivative.** -/
theorem tsum_vonMangoldtTwist_cpow_eq_logDeriv (τ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, vonMangoldtTwist τ n * (n : ℂ) ^ (-s))
      = -logDeriv riemannZeta (s + (τ : ℂ) * Complex.I) := by
  have hshift : 1 < (s + (τ : ℂ) * Complex.I).re := by
    simpa using hs
  rw [tsum_vonMangoldtTwist_cpow τ s,
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hshift, logDeriv]
  simp only [Pi.div_apply]
  ring

/-- **The twisted smoothed Chebyshev sum as a vertical integral.** -/
theorem tsum_vonMangoldtTwist_smoothWeight_eq_integral (τ : ℝ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {σ : ℝ} (hσ : 1 < σ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (∑' n : ℕ, vonMangoldtTwist τ n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I))) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I) :=
  tsum_mul_smoothWeight_eq_integral_summable (by simp) hN hH hσ
    (summable_vonMangoldtTwist_rpow τ hσ)

/-- **The twisted smoothed Chebyshev sum against the shifted logarithmic derivative.**  This is the
Perron side of a twisted prime sum: the integrand is `-ζ'/ζ` on the line `Re s = σ`, translated
vertically by the twist. -/
theorem tsum_vonMangoldtTwist_smoothWeight_eq_logDeriv_integral (τ : ℝ) {N H : ℝ} (hN : 0 < N)
    (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (-logDeriv riemannZeta ((σ : ℂ) + ((y + τ : ℝ)) * Complex.I)) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I) := by
  rw [tsum_vonMangoldtTwist_smoothWeight_eq_integral τ hN hH hσ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hre : (1 : ℝ) < ((σ : ℂ) + (y : ℝ) * Complex.I).re := by
    simpa using hσ
  show (∑' n : ℕ, vonMangoldtTwist τ n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I))) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * Complex.I)
    = (-logDeriv riemannZeta ((σ : ℂ) + ((y + τ : ℝ)) * Complex.I)) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * Complex.I)
  have harg : ((σ : ℂ) + (y : ℝ) * Complex.I) + (τ : ℂ) * Complex.I
      = (σ : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [tsum_vonMangoldtTwist_cpow_eq_logDeriv τ hre, harg]

end RHTower.Sieve
