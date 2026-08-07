import GaloisForLFunctions.HTGeometry.IrrationalSineSubsequence

/-!
# Exact Gevrey order of the zeta tail, in the Gamma normalization

The tail coefficients of the Barnes expansion of an irrational-power canonical product have the
closed modulus

`|b k| = 2 |sin (π s k / 2)| Γ(1 + s k) Z k / (2π)^(1 + s k)`,

where `Z k = ζ(1 + s k)` satisfies `1 ≤ Z k ≤ ζ(1 + s)`.

In the Gamma normalization of Gevrey order — bounding `|b k|` by `C A^k Γ(1 + r k)` — both halves
of the exact-order statement are elementary: the upper bound uses only `|sin| ≤ 1` and `Z k ≤ M`,
and the lower bound along a subsequence uses only `Z k ≥ 1` together with the fact that an
irrational rotation is far from the integers infinitely often.  No Stirling estimate is needed;
Stirling is required only to convert this normalization into the factorial one.
-/

namespace GaloisForLFunctions.HTGeometry

open Real

/-- The geometric factor of the tail. -/
theorem two_pi_rpow_split {s : ℝ} (k : ℕ) :
    (2 * Real.pi) ^ (1 + s * (k : ℝ))
      = (2 * Real.pi) * (((2 * Real.pi) ^ s) ^ k) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [Real.rpow_add h2pi, Real.rpow_one, Real.rpow_mul h2pi.le, Real.rpow_natCast]

/-- **The Gevrey upper bound.**  Only `|sin| ≤ 1` and the upper bound on the zeta factor are used. -/
theorem gevrey_upper_bound {s M : ℝ} {b Z : ℕ → ℝ} (hZ : ∀ k, 1 ≤ Z k) (hM : ∀ k, Z k ≤ M)
    (hb : ∀ k : ℕ, |b k| = 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * Z k
      / (2 * Real.pi) ^ (1 + s * (k : ℝ)))
    (hGamma : ∀ k : ℕ, 0 < Real.Gamma (1 + s * k)) (k : ℕ) :
    |b k| ≤ (M / Real.pi) * (((2 * Real.pi) ^ s)⁻¹) ^ k * Real.Gamma (1 + s * k) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpow : (0 : ℝ) < ((2 * Real.pi) ^ s) ^ k := by
    have : (0 : ℝ) < (2 * Real.pi) ^ s := Real.rpow_pos_of_pos h2pi s
    positivity
  have hsin : |Real.sin (Real.pi * s * k / 2)| ≤ 1 := abs_sin_le_one _
  have hG := hGamma k
  rw [hb k, two_pi_rpow_split k, div_le_iff₀ (by positivity)]
  have hMk : Z k ≤ M := hM k
  have hZ1 := hZ k
  have hSnn := abs_nonneg (Real.sin (Real.pi * s * k / 2))
  have hZnn : (0 : ℝ) ≤ Z k := by linarith
  have hkey : 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * Z k
      ≤ 2 * Real.Gamma (1 + s * k) * M := by
    have hfac : 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k)
        ≤ 2 * Real.Gamma (1 + s * k) := by nlinarith
    have h1 : 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * Z k
        ≤ 2 * Real.Gamma (1 + s * k) * Z k := mul_le_mul_of_nonneg_right hfac hZnn
    have h2 : 2 * Real.Gamma (1 + s * k) * Z k ≤ 2 * Real.Gamma (1 + s * k) * M :=
      mul_le_mul_of_nonneg_left hMk (by positivity)
    linarith
  have hrpow : ((2 * Real.pi) ^ s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h2pi s)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hexp : (M / Real.pi) * (((2 * Real.pi) ^ s)⁻¹) ^ k * Real.Gamma (1 + s * k)
      * (2 * Real.pi * ((2 * Real.pi) ^ s) ^ k)
      = 2 * Real.Gamma (1 + s * k) * M := by
    rw [inv_pow]
    field_simp
  rw [hexp]
  linarith

/-- **The Gevrey lower bound along the sharp subsequence.**  Only `Z k ≥ 1` and the sine bound of
the irrational rotation are used. -/
theorem gevrey_lower_bound {s : ℝ} {b Z : ℕ → ℝ} (hZ : ∀ k, 1 ≤ Z k)
    (hb : ∀ k : ℕ, |b k| = 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * Z k
      / (2 * Real.pi) ^ (1 + s * (k : ℝ)))
    (hGamma : ∀ k : ℕ, 0 < Real.Gamma (1 + s * k))
    {k : ℕ} (hk : 1 / 2 ≤ |Real.sin (Real.pi * s * k / 2)|) :
    (1 / (2 * Real.pi)) * (((2 * Real.pi) ^ s)⁻¹) ^ k * Real.Gamma (1 + s * k) ≤ |b k| := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpow : (0 : ℝ) < ((2 * Real.pi) ^ s) ^ k := by
    have : (0 : ℝ) < (2 * Real.pi) ^ s := Real.rpow_pos_of_pos h2pi s
    positivity
  have hG := hGamma k
  rw [hb k, two_pi_rpow_split k, le_div_iff₀ (by positivity)]
  have hZ1 := hZ k
  have hSnn := abs_nonneg (Real.sin (Real.pi * s * k / 2))
  have hkey : Real.Gamma (1 + s * k)
      ≤ 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * Z k := by
    have hfac : Real.Gamma (1 + s * k)
        ≤ 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) := by nlinarith
    have h2 : 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * 1
        ≤ 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * Z k :=
      mul_le_mul_of_nonneg_left hZ1 (by positivity)
    linarith
  have hrpow : ((2 * Real.pi) ^ s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h2pi s)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hexp : (1 / (2 * Real.pi)) * (((2 * Real.pi) ^ s)⁻¹) ^ k * Real.Gamma (1 + s * k)
      * (2 * Real.pi * ((2 * Real.pi) ^ s) ^ k)
      = Real.Gamma (1 + s * k) := by
    rw [inv_pow]
    field_simp
  rw [hexp]
  linarith

/-- **The exact Gevrey order of an irrational-power zeta tail, in the Gamma normalization.**  The
tail is bounded by `C A^k Γ(1 + s k)` for every `k`, and bounded below by `c A^k Γ(1 + s k)` for
infinitely many `k`, so no smaller order can bound it. -/
theorem gevrey_exact_order {s M : ℝ} (hs : Irrational s) {b Z : ℕ → ℝ}
    (hZ : ∀ k, 1 ≤ Z k) (hM : ∀ k, Z k ≤ M)
    (hb : ∀ k : ℕ, |b k| = 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * Z k
      / (2 * Real.pi) ^ (1 + s * (k : ℝ)))
    (hGamma : ∀ k : ℕ, 0 < Real.Gamma (1 + s * k)) :
    (∀ k : ℕ, |b k| ≤ (M / Real.pi) * (((2 * Real.pi) ^ s)⁻¹) ^ k * Real.Gamma (1 + s * k)) ∧
      {k : ℕ | (1 / (2 * Real.pi)) * (((2 * Real.pi) ^ s)⁻¹) ^ k * Real.Gamma (1 + s * k)
        ≤ |b k|}.Infinite := by
  refine ⟨fun k => gevrey_upper_bound hZ hM hb hGamma k, ?_⟩
  refine (infinite_setOf_half_le_abs_sin_half hs).mono ?_
  intro k hk
  exact gevrey_lower_bound hZ hb hGamma hk

end GaloisForLFunctions.HTGeometry
