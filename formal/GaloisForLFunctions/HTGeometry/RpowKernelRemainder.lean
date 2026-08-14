import GaloisForLFunctions.HTGeometry.LogWeightedRpowIntegral

/-!
# Vanishing weights against a power kernel

If `g → 0` and a kernel is dominated by `C·t^(a-1)` with `a > 0`, then

```text
∫_2^x g(t) K(t) dt = o(x^a).
```

Splitting at a height where `|g| ≤ δ` bounds the tail by `Cδ(x^a - T^a)/a` and leaves a constant
head, which the power normalization kills.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace HTGeometry

noncomputable section

/-- **A vanishing weight against a power kernel contributes nothing.** -/
theorem tendsto_rpowKernelRemainder {a : ℝ} (ha0 : 0 < a) {C : ℝ} (hC0 : 0 ≤ C) {g K : ℝ → ℝ}
    (hgt : Tendsto g atTop (nhds 0))
    (hKbd : ∀ t : ℝ, 2 ≤ t → |K t| ≤ C * t ^ (a - 1))
    (hgint : ∀ x : ℝ, 2 ≤ x → IntervalIntegrable (fun t : ℝ => g t * K t) volume 2 x) :
    Tendsto (fun x : ℝ => (∫ t in (2 : ℝ)..x, g t * K t) / x ^ a) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hCC : (0 : ℝ) < 2 * (C + 1) := by linarith
  set δ : ℝ := ε * a / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := div_pos (mul_pos hε ha0) hCC
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (NormedAddGroup.tendsto_nhds_zero.mp hgt δ hδ0)
  set T : ℝ := max T₀ 2 with hT
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hTg : ∀ t : ℝ, T ≤ t → |g t| ≤ δ := by
    intro t ht
    have h := hT₀ t (le_trans (le_max_left _ _) ht)
    rw [Real.norm_eq_abs] at h
    exact h.le
  set A : ℝ := ∫ t in (2 : ℝ)..T, g t * K t with hA
  have hhead : Tendsto (fun x : ℝ => |A| / x ^ a) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha0)
  have hsmallhead : ∀ᶠ x : ℝ in atTop, |A| / x ^ a < ε / 2 :=
    (NormedAddGroup.tendsto_nhds_zero.mp hhead (ε / 2) (by linarith)).mono fun x hx => by
      rw [Real.norm_eq_abs] at hx
      exact lt_of_le_of_lt (le_abs_self _) hx
  filter_upwards [eventually_ge_atTop T, hsmallhead] with x hx hxhead
  have hx2 : (2 : ℝ) ≤ x := le_trans hT2 hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hsplit : (∫ t in (2 : ℝ)..x, g t * K t) = A + ∫ t in T..x, g t * K t := by
    rw [hA]
    exact (intervalIntegral.integral_add_adjacent_intervals (hgint T hT2)
      ((hgint x hx2).mono_set (by
        rw [uIcc_of_le hx, uIcc_of_le hx2]
        exact Icc_subset_Icc hT2 le_rfl))).symm
  have htailint : IntervalIntegrable (fun t : ℝ => g t * K t) volume T x :=
    (hgint x hx2).mono_set (by
      rw [uIcc_of_le hx, uIcc_of_le hx2]
      exact Icc_subset_Icc hT2 le_rfl)
  have hmajor : IntervalIntegrable (fun t : ℝ => C * δ * t ^ (a - 1)) volume T x :=
    (intervalIntegrable_rpowSubOne a hT2 hx2).const_mul _
  have hpt : ∀ t ∈ Icc T x, |g t * K t| ≤ C * δ * t ^ (a - 1) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := le_trans hT2 ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    rw [abs_mul]
    calc |g t| * |K t| ≤ δ * (C * t ^ (a - 1)) :=
          mul_le_mul (hTg t ht.1) (hKbd t ht2) (abs_nonneg _) hδ0.le
      _ = C * δ * t ^ (a - 1) := by ring
  have hupper : (∫ t in T..x, g t * K t) ≤ ∫ t in T..x, C * δ * t ^ (a - 1) :=
    intervalIntegral.integral_mono_on hx htailint hmajor fun t ht =>
      le_trans (le_abs_self _) (hpt t ht)
  have hlower : (∫ t in T..x, -(C * δ * t ^ (a - 1))) ≤ ∫ t in T..x, g t * K t :=
    intervalIntegral.integral_mono_on hx hmajor.neg htailint fun t ht =>
      neg_le_of_abs_le (hpt t ht)
  rw [intervalIntegral.integral_neg] at hlower
  have habs : |∫ t in T..x, g t * K t| ≤ ∫ t in T..x, C * δ * t ^ (a - 1) :=
    abs_le.mpr ⟨hlower, hupper⟩
  have hval : (∫ t in T..x, C * δ * t ^ (a - 1)) = C * δ * ((x ^ a - T ^ a) / a) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow_sub_one ha0]
  have hTa : (0 : ℝ) < T ^ a := Real.rpow_pos_of_pos (by linarith) a
  have hCδ0 : (0 : ℝ) ≤ C * δ := mul_nonneg hC0 hδ0.le
  have hle : C * δ * ((x ^ a - T ^ a) / a) ≤ C * δ * (x ^ a / a) := by
    apply mul_le_mul_of_nonneg_left _ hCδ0
    rw [sub_div]
    have hTdiv : (0 : ℝ) < T ^ a / a := div_pos hTa ha0
    linarith
  have hnum : |∫ t in (2 : ℝ)..x, g t * K t| ≤ |A| + C * δ * (x ^ a / a) := by
    rw [hsplit]
    calc |A + ∫ t in T..x, g t * K t| ≤ |A| + |∫ t in T..x, g t * K t| := abs_add_le _ _
      _ ≤ |A| + C * δ * (x ^ a / a) := by
          rw [hval] at habs
          linarith
  have hdiv : |∫ t in (2 : ℝ)..x, g t * K t| / x ^ a ≤
      (|A| + C * δ * (x ^ a / a)) / x ^ a := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hXpos.le)
  have hane : a ≠ 0 := ne_of_gt ha0
  have hexpand : (|A| + C * δ * (x ^ a / a)) / x ^ a = |A| / x ^ a + C * δ / a := by
    field_simp
  have hCδa : C * δ / a ≤ ε / 2 := by
    have hval : C * δ / a = C * ε / (2 * (C + 1)) := by
      rw [hδ]
      field_simp
    rw [hval, div_le_div_iff₀ hCC (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hε, hC0]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hXpos]
  rw [hexpand] at hdiv
  linarith

end

end HTGeometry
