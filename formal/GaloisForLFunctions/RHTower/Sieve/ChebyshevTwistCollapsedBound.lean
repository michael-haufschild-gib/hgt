import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistRouteTBound

/-!
# The twisted Route-T bound in collapsed form

The seven pieces of the twisted contour share two factors: the sum of the pole and regular sizes,
and one common edge mass.  Since the Route-T abscissa is above `1/2` and the horizontal edges are
divided by `T² ≥ 1`, the edge mass collapses to `4(N+H)^σ + 5C`, and the whole estimate becomes

```text
‖2π ∑ₙ Λ(n) n^{-iτ} w(n)‖ ≤ ((|τ|-T)⁻¹ + C'·log K / w(K+1))·(4(N+H)^σ + 5C) + 2Σ(d)C/T,
```

`K = |τ| + T`.  In this form the two competing quantities are visible: `(N+H)^σ` carries the
zero-free saving, and `C` — the cutoff's order-two Mellin constant — carries the cost of smoothing,
divided by the truncation height.

Specialising `T = |τ|/2` costs nothing and removes a parameter: the pole factor becomes `2/|τ|`, the
contour parameter becomes `3|τ|/2`, and the twist alone fixes the geometry.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

theorem routeTTwistAbscissa_ge_half (A delta K : ℝ) :
    1 / 2 ≤ routeTTwistAbscissa A delta K := by
  unfold routeTTwistAbscissa
  have h1 := routeTUniformRegWidth_le_half (A := A) (delta := delta) (K := K)
  have h2 := routeTZeroFreeWidth_le_one_sixtieth A (K + 1)
  linarith

theorem routeTTwistAbscissa_ge_one_sub (A delta K : ℝ) :
    1 - 1 / 320 ≤ routeTTwistAbscissa A delta K := by
  unfold routeTTwistAbscissa
  have h1 := routeTUniformRegWidth_le_half (A := A) (delta := delta) (K := K)
  have h2 := routeTZeroFreeWidth_le_one_sixtieth A (K + 1)
  linarith

/-- **The twisted Route-T bound, collapsed to two factors.** -/
theorem exists_norm_tsum_vonMangoldtTwist_routeT_simple :
    ∃ A Creg delta K₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 3 ≤ K₀ ∧
      ∀ (N H d T τ C : ℝ), 0 < N → 0 < H → 1 < d → d ≤ 9 / 8 → 1 ≤ T → T < |τ| →
        K₀ ≤ |τ| + T →
        (∀ s : ℂ, 0 < s.re → s.re ≤ d →
          |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) →
        ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, vonMangoldtTwist τ n
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
          ≤ ((|τ| - T)⁻¹
                + Creg * Real.log (|τ| + T) / routeTZeroFreeWidth A (|τ| + T + 1))
              * (4 * (N + H) ^ routeTTwistAbscissa A delta (|τ| + T) + 5 * C)
            + 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / T := by
  obtain ⟨A, Creg, delta, K₀, hCreg, hdelta, hK₀, hmain⟩ :=
    exists_norm_tsum_vonMangoldtTwist_routeT_le
  refine ⟨A, Creg, delta, K₀, hCreg, hdelta, hK₀, ?_⟩
  intro N H d T τ C hN hH hd hd98 hT hτ hK hbd
  have hcap := hmain N H d T τ C hN hH hd hd98 hT hτ hK hbd
  set K : ℝ := |τ| + T with hKdef
  set σ : ℝ := routeTTwistAbscissa A delta K with hσdef
  have hσhalf : 1 / 2 ≤ σ := routeTTwistAbscissa_ge_half A delta K
  have hσlow : 1 - 1 / 320 ≤ σ := routeTTwistAbscissa_ge_one_sub A delta K
  have hσ1 : σ < 1 := routeTTwistAbscissa_lt_one hdelta
  have hT0 : (0 : ℝ) < T := by linarith
  have hτ0 : (0 : ℝ) < |τ| - T := by linarith
  have hMp : (0 : ℝ) ≤ (|τ| - T)⁻¹ := inv_nonneg.2 hτ0.le
  have hK3 : (3 : ℝ) ≤ K := le_trans hK₀ hK
  have hwpos : (0 : ℝ) < routeTZeroFreeWidth A (K + 1) := routeTZeroFreeWidth_pos A _
  have hMreg : (0 : ℝ) ≤ Creg * Real.log K / routeTZeroFreeWidth A (K + 1) := by
    have hlog : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
    positivity
  -- the Mellin constant is nonnegative, read off one point of the strip
  have hC0 : 0 ≤ C := by
    have hpt := hbd (((d / 2 : ℝ)) + Complex.I) (by simp; linarith) (by simp; linarith)
    have him : (((d / 2 : ℝ) : ℂ) + Complex.I).im = 1 := by simp
    rw [him] at hpt
    simp only [abs_one, one_pow, one_mul] at hpt
    exact le_trans (norm_nonneg _) hpt
  have hpowpos : (0 : ℝ) < (N + H) ^ σ := Real.rpow_pos_of_pos (by linarith) _
  -- the edge mass collapses
  have hmass : 2 * ((N + H) ^ σ / σ) + 2 * C + 2 * (C / T ^ 2 * (d - σ))
      ≤ 4 * (N + H) ^ σ + 5 * C := by
    have hdiv : (N + H) ^ σ / σ ≤ 2 * (N + H) ^ σ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hpowpos, hσhalf]
    have hT2 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
    have hgap : (0 : ℝ) ≤ d - σ := by linarith
    have hgapsmall : d - σ ≤ 1 / 4 := by linarith
    have hfrac : C / T ^ 2 * (d - σ) ≤ C := by
      have h1 : C / T ^ 2 ≤ C := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hC0, hT2]
      nlinarith [hC0, h1, hgap, hgapsmall, div_nonneg hC0 (by positivity : (0:ℝ) ≤ T ^ 2)]
    linarith
  have hfac : (0 : ℝ) ≤ (|τ| - T)⁻¹ + Creg * Real.log K / routeTZeroFreeWidth A (K + 1) := by
    linarith
  have hexpand : ((|τ| - T)⁻¹ * C / T ^ 2 * (d - σ) + (|τ| - T)⁻¹ * C / T ^ 2 * (d - σ)
        + (|τ| - T)⁻¹ * (2 * ((N + H) ^ σ / σ) + 2 * C))
      + ((Creg * Real.log K / routeTZeroFreeWidth A (K + 1)) * C / T ^ 2 * (d - σ)
        + (Creg * Real.log K / routeTZeroFreeWidth A (K + 1)) * C / T ^ 2 * (d - σ)
        + (Creg * Real.log K / routeTZeroFreeWidth A (K + 1))
          * (2 * ((N + H) ^ σ / σ) + 2 * C))
      = ((|τ| - T)⁻¹ + Creg * Real.log K / routeTZeroFreeWidth A (K + 1))
        * (2 * ((N + H) ^ σ / σ) + 2 * C + 2 * (C / T ^ 2 * (d - σ))) := by
    field_simp
    ring
  rw [hexpand] at hcap
  have hstep : ((|τ| - T)⁻¹ + Creg * Real.log K / routeTZeroFreeWidth A (K + 1))
      * (2 * ((N + H) ^ σ / σ) + 2 * C + 2 * (C / T ^ 2 * (d - σ)))
      ≤ ((|τ| - T)⁻¹ + Creg * Real.log K / routeTZeroFreeWidth A (K + 1))
        * (4 * (N + H) ^ σ + 5 * C) :=
    mul_le_mul_of_nonneg_left hmass hfac
  linarith

/-- **The twisted Route-T bound at half height.**  Taking the truncation height to be half the twist
removes a parameter: the pole factor is `2/|τ|` and the contour parameter is `3|τ|/2`. -/
theorem exists_norm_tsum_vonMangoldtTwist_routeT_half :
    ∃ A Creg delta τ₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 2 ≤ τ₀ ∧
      ∀ (N H d τ C : ℝ), 0 < N → 0 < H → 1 < d → d ≤ 9 / 8 → τ₀ ≤ |τ| →
        (∀ s : ℂ, 0 < s.re → s.re ≤ d →
          |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) →
        ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, vonMangoldtTwist τ n
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
          ≤ (2 / |τ|
                + Creg * Real.log (3 * |τ| / 2)
                    / routeTZeroFreeWidth A (3 * |τ| / 2 + 1))
              * (4 * (N + H) ^ routeTTwistAbscissa A delta (3 * |τ| / 2) + 5 * C)
            + 4 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / |τ| := by
  obtain ⟨A, Creg, delta, K₀, hCreg, hdelta, hK₀, hsimple⟩ :=
    exists_norm_tsum_vonMangoldtTwist_routeT_simple
  refine ⟨A, Creg, delta, max 2 K₀, hCreg, hdelta, le_max_left _ _, ?_⟩
  intro N H d τ C hN hH hd hd98 hτ hbd
  have hτ2 : (2 : ℝ) ≤ |τ| := le_trans (le_max_left _ _) hτ
  have hτK : K₀ ≤ |τ| := le_trans (le_max_right _ _) hτ
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hh := hsimple N H d (|τ| / 2) τ C hN hH hd hd98 (by linarith) (by linarith)
    (by linarith) hbd
  have hKeq : |τ| + |τ| / 2 = 3 * |τ| / 2 := by ring
  have hinv : (|τ| - |τ| / 2)⁻¹ = 2 / |τ| := by
    rw [show |τ| - |τ| / 2 = |τ| / 2 by ring, inv_div]
  rw [hKeq, hinv] at hh
  have hlast : 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / (|τ| / 2)
      = 4 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / |τ| := by
    field_simp
    ring
  rw [hlast] at hh
  exact hh

end RHTower.Sieve
