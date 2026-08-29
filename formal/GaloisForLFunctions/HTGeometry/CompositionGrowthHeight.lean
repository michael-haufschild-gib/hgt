import GaloisForLFunctions.HTGeometry.PolyaCompositionMaximum
import GaloisForLFunctions.HTGeometry.IterExpExponentComparison

/-!
# Composing with a positive-lower-order factor raises the growth height

Pólya's composition inequality, together with the exponent comparison for iterated exponentials,
gives the step of the growth-depth lemma:

```text
PositiveLowerOrder g,  GrowthHeightAtLeast h k  ⟹  GrowthHeightAtLeast (g ∘ h) (k+1).
```

The translation `h ↦ h − h 0`, `g ↦ g(· + h 0)` normalises the inner function so that Pólya's
`h(0) = 0` hypothesis holds, without changing the composite.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- Composing the tower heights. -/
theorem iterExp_add (k j : ℕ) (x : ℝ) : iterExp (k + j) x = iterExp j (iterExp k x) := by
  simp only [iterExp, ← Function.iterate_add_apply]
  congr 1
  omega

/-- **The growth-depth step.**  Composing an outer factor of growth height `j` with an inner factor
of growth height `k` gives growth height `k + j`. -/
theorem growthHeightAtLeast_comp_add {g h : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hh : Differentiable ℂ h) {j : ℕ} (hgpos : GrowthHeightAtLeast g j) {k : ℕ}
    (hhk : GrowthHeightAtLeast h k) :
    GrowthHeightAtLeast (fun z => g (h z)) (k + j) := by
  obtain ⟨c, hc0, hpolya⟩ := exists_polya_constant
  obtain ⟨δ, hδ, hhev⟩ := hhk
  obtain ⟨ε, hε, hgev⟩ := hgpos
  obtain ⟨δ', hδ'0, hcmp⟩ := exists_exponent_iterExp_le_rpow k hδ (half_pos hε)
  refine ⟨δ', hδ'0, ?_⟩
  set b : ℝ := ‖h 0‖ with hbdef
  have hb0 : 0 ≤ b := norm_nonneg _
  set Y : ℝ → ℝ := fun r => iterExp k ((r / 2) ^ δ) with hYdef
  have hhalf : Tendsto (fun r : ℝ => r / 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun x => ⟨2 * x, fun a ha => by linarith⟩
  have hYtop : Tendsto Y atTop atTop := (tendsto_iterExp_rpow k hδ).comp hhalf
  set S : ℝ → ℝ := fun r => c * (Y r - b) - b with hSdef
  have hStop : Tendsto S atTop atTop := by
    have h1 : Tendsto (fun r : ℝ => c * Y r) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc0 hYtop
    have h2 : Tendsto (fun r : ℝ => c * Y r + (-(c * b) - b)) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ _ h1
    refine h2.congr fun r => ?_
    rw [hSdef]
    ring
  have hhev2 : ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ ≤ r / 2 ∧ Y r ≤ ‖h z‖ := hhalf.eventually hhev
  have hgev2 : ∀ᶠ r : ℝ in atTop,
      ∃ v : ℂ, ‖v‖ ≤ S r ∧ iterExp j ((S r) ^ ε) ≤ ‖g v‖ := hStop.eventually hgev
  have hYrpow : Tendsto (fun r : ℝ => (Y r) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp hYtop
  filter_upwards [hhev2, hgev2, hcmp,
    hYtop.eventually_ge_atTop (2 * b + 1),
    hYtop.eventually_ge_atTop (2 * (c + 1) * b / c),
    hYrpow.eventually_ge_atTop (((c / 2) ^ ε)⁻¹),
    eventually_gt_atTop (0 : ℝ)] with r hz hv hcm hY1 hY2 hY3 hr0
  obtain ⟨z₀, hz₀, hz₀Y⟩ := hz
  obtain ⟨u, hu, huval⟩ := hv
  set H : ℝ := Y r - b with hHdef
  have hH0 : 0 < H := by rw [hHdef]; linarith
  -- the normalised inner and outer functions
  have hhtilde : Differentiable ℂ (fun z => h z - h 0) := hh.sub_const _
  have hgtilde : Differentiable ℂ (fun w => g (w + h 0)) :=
    hg.comp (differentiable_id.add_const _)
  have hzero : (fun z => h z - h 0) 0 = 0 := by simp
  have hreach : ∃ w₀ : ℂ, ‖w₀‖ ≤ r / 2 ∧ H ≤ ‖(fun z => h z - h 0) w₀‖ := by
    refine ⟨z₀, hz₀, ?_⟩
    have hnorm : ‖h z₀‖ - b ≤ ‖h z₀ - h 0‖ := by
      have hns := norm_sub_norm_le (h z₀) (h 0)
      rw [hbdef]
      exact hns
    show H ≤ ‖h z₀ - h 0‖
    rw [hHdef]
    linarith
  obtain ⟨z, hzr, hzmax⟩ := hpolya (fun w => g (w + h 0)) (fun z => h z - h 0)
    hgtilde hhtilde hzero r H hr0 hH0 hreach
  refine ⟨z, le_of_lt hzr, ?_⟩
  -- transport the value bound back
  have hvbound : ‖u - h 0‖ ≤ c * H := by
    have h1 := norm_sub_le u (h 0)
    have h2 : ‖u‖ + b ≤ S r + b := by linarith
    have h3 : S r + b = c * H := by rw [hSdef, hHdef]; ring
    rw [← hbdef] at h1
    linarith
  have hkey : iterExp j ((S r) ^ ε) ≤ ‖g (h z)‖ := by
    have h1 := hzmax (u - h 0) hvbound
    simp only [sub_add_cancel] at h1
    linarith
  -- the exponent comparison
  have hYpos : 0 < Y r := by linarith
  have hSpos : 0 < S r := by
    have hstep : c / 2 * Y r ≤ S r := by
      rw [hSdef]
      rw [div_le_iff₀ hc0] at hY2
      nlinarith [hY2, hc0, hYpos]
    nlinarith [hstep, hc0, hYpos]
  have hSge : c / 2 * Y r ≤ S r := by
    rw [hSdef]
    rw [div_le_iff₀ hc0] at hY2
    nlinarith [hY2, hc0, hYpos]
  have hYhalfpos : (0 : ℝ) < (Y r) ^ (ε / 2) := Real.rpow_pos_of_pos hYpos _
  have hcpow : (0 : ℝ) < (c / 2) ^ ε := Real.rpow_pos_of_pos (by linarith) _
  have hsplitY : (Y r) ^ ε = (Y r) ^ (ε / 2) * (Y r) ^ (ε / 2) := by
    rw [← Real.rpow_add hYpos]
    congr 1
    ring
  have hstep1 : (Y r) ^ (ε / 2) ≤ (c / 2) ^ ε * (Y r) ^ ε := by
    rw [hsplitY]
    have h1 : 1 ≤ (c / 2) ^ ε * (Y r) ^ (ε / 2) := by
      have := mul_le_mul_of_nonneg_left hY3 hcpow.le
      rw [mul_inv_cancel₀ (ne_of_gt hcpow)] at this
      exact this
    nlinarith [h1, hYhalfpos]
  have hstep2 : (c / 2) ^ ε * (Y r) ^ ε ≤ (S r) ^ ε := by
    rw [← Real.mul_rpow (by linarith) hYpos.le]
    exact Real.rpow_le_rpow (by positivity) hSge hε.le
  have hfinal : iterExp k (r ^ δ') ≤ (S r) ^ ε := by
    calc iterExp k (r ^ δ') ≤ (Y r) ^ (ε / 2) := hcm
      _ ≤ (c / 2) ^ ε * (Y r) ^ ε := hstep1
      _ ≤ (S r) ^ ε := hstep2
  rw [iterExp_add]
  calc iterExp j (iterExp k (r ^ δ')) ≤ iterExp j ((S r) ^ ε) := iterExp_monotone j hfinal
    _ ≤ ‖g (h z)‖ := hkey



/-! ## Every nonconstant entire function has growth height at least zero -/

/-- The maximum modulus on a circle centred anywhere is attained. -/
theorem exists_sphere_max_center {g : ℂ → ℂ} (hg : Differentiable ℂ g) (c : ℂ) {R : ℝ}
    (hR : 0 < R) :
    ∃ u₀ : ℂ, ‖u₀ - c‖ = R ∧ ∀ z : ℂ, ‖z - c‖ = R → ‖g z‖ ≤ ‖g u₀‖ := by
  have hne : (Metric.sphere c R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
  obtain ⟨u₀, hu₀mem, hu₀max⟩ :=
    (isCompact_sphere c R).exists_isMaxOn hne (hg.continuous.norm.continuousOn)
  refine ⟨u₀, by simpa [Metric.mem_sphere, dist_eq_norm] using hu₀mem, fun z hz => ?_⟩
  exact hu₀max (by simpa [Metric.mem_sphere, dist_eq_norm] using hz)

/-- **A nonconstant entire function grows at least linearly.**  Cauchy's estimate at a point where
the derivative does not vanish forces the maximum modulus on the disc of radius `s` to be at least
`‖g'(z₁)‖·(s − ‖z₁‖)`. -/
theorem exists_linear_lower_bound_of_nonconstant {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hnc : ∃ z₁ z₂ : ℂ, g z₁ ≠ g z₂) :
    ∃ (A : ℝ) (z₁ : ℂ), 0 < A ∧ ∀ s : ℝ, ‖z₁‖ < s →
      ∃ u : ℂ, ‖u‖ ≤ s ∧ A * (s - ‖z₁‖) ≤ ‖g u‖ := by
  have hderiv : ∃ z₁ : ℂ, deriv g z₁ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (is_const_of_deriv_eq_zero hg hcon a b)
  obtain ⟨z₁, hz₁⟩ := hderiv
  refine ⟨‖deriv g z₁‖, z₁, norm_pos_iff.mpr hz₁, fun s hs => ?_⟩
  set R : ℝ := s - ‖z₁‖ with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  obtain ⟨u₀, hu₀n, hu₀max⟩ := exists_sphere_max_center hg z₁ hR
  refine ⟨u₀, ?_, ?_⟩
  · have h1 := norm_sub_norm_le u₀ z₁
    rw [hu₀n] at h1
    rw [hRdef] at h1
    linarith
  · have hdc : DiffContOnCl ℂ g (Metric.ball z₁ R) := hg.diffContOnCl
    have hbd : ∀ z ∈ Metric.sphere z₁ R, ‖g z‖ ≤ ‖g u₀‖ := by
      intro z hz
      exact hu₀max z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz)
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hdc hbd
    rw [iteratedDeriv_one] at hcauchy
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at hcauchy
    rw [le_div_iff₀ hR] at hcauchy
    linarith [hcauchy]

/-- **Every nonconstant entire function has growth height at least zero.** -/
theorem growthHeightAtLeast_zero_of_nonconstant {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hnc : ∃ z₁ z₂ : ℂ, g z₁ ≠ g z₂) : GrowthHeightAtLeast g 0 := by
  obtain ⟨A, z₁, hA, hgrow⟩ := exists_linear_lower_bound_of_nonconstant hg hnc
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hev : ∀ᶠ s : ℝ in atTop, 2 / A ≤ s ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).eventually_ge_atTop _
  filter_upwards [hev, eventually_ge_atTop (2 * ‖z₁‖ + 1), eventually_gt_atTop (0 : ℝ)]
    with r hr hrz hr0
  have hz₁0 : (0 : ℝ) ≤ ‖z₁‖ := norm_nonneg z₁
  have hrz1 : ‖z₁‖ < r := by linarith
  obtain ⟨u, hu, hval⟩ := hgrow r hrz1
  refine ⟨u, hu, ?_⟩
  simp only [iterExp_zero]
  have hrp : (0 : ℝ) < r ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hsplit : r ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) = r := by
    rw [← Real.rpow_add hr0]
    norm_num
  have h1 : 1 ≤ A / 2 * r ^ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hA] at hr
    nlinarith [hr, hA]
  have hstep : r ^ (1 / 2 : ℝ) ≤ A / 2 * r := by
    nlinarith [h1, hrp, hsplit]
  have hhalf : A / 2 * r ≤ A * (r - ‖z₁‖) := by
    nlinarith [hA, hrz, hz₁0]
  linarith [hval, hstep, hhalf]

