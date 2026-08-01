import GaloisForLFunctions.HTGeometry.VerticalFlatness

/-!
# Flatness along the upper part of a right half-plane

The sets `{s | σ₀ ≤ Re s, T ≤ Im s}` generate a filter on `ℂ`.  Along it the modulus escapes, so a
polynomial is squeezed between two multiples of the power of its own degree, and a function is
*flat* when it beats every power of the modulus.

Flatness on this filter is a ring-theoretic notion: it is stable under differences, under
multiplication and division by a nonzero polynomial, and under the unit translation, which maps the
filter into itself.  No nonzero polynomial is flat.  These are exactly the closure properties of an
annihilator space for the digamma jets.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- The filter of the upper part of the closed right half-plane `Re s ≥ σ₀`. -/
def halfPlaneUpper (σ₀ : ℝ) : Filter ℂ :=
  Filter.comap Complex.im atTop ⊓ Filter.principal {s : ℂ | σ₀ ≤ s.re}

theorem eventually_halfPlaneUpper_re {σ₀ : ℝ} :
    ∀ᶠ s : ℂ in halfPlaneUpper σ₀, σ₀ ≤ s.re :=
  Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun _ h => h)

theorem eventually_halfPlaneUpper_im {σ₀ : ℝ} (T : ℝ) :
    ∀ᶠ s : ℂ in halfPlaneUpper σ₀, T ≤ s.im := by
  refine Filter.Eventually.filter_mono inf_le_left ?_
  exact Filter.eventually_comap.mpr
    (by filter_upwards [eventually_ge_atTop T] with x hx s hs using hs ▸ hx)

instance halfPlaneUpper_neBot (σ₀ : ℝ) : (halfPlaneUpper σ₀).NeBot := by
  rw [halfPlaneUpper, Filter.inf_principal_neBot_iff]
  intro s hs
  obtain ⟨T, hT⟩ := (Filter.mem_comap.mp hs)
  obtain ⟨T₀, hT₀⟩ := Filter.mem_atTop_sets.mp hT.1
  refine ⟨(σ₀ : ℂ) + (T₀ : ℂ) * Complex.I, hT.2 ?_, ?_⟩
  · exact hT₀ _ (by simp)
  · simp

theorem tendsto_norm_halfPlaneUpper (σ₀ : ℝ) :
    Tendsto (fun s : ℂ => ‖s‖) (halfPlaneUpper σ₀) atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [eventually_halfPlaneUpper_im (σ₀ := σ₀) b] with s hs
  exact le_trans hs (le_trans (le_abs_self _) (Complex.abs_im_le_norm s))

theorem eventually_one_le_norm (σ₀ : ℝ) : ∀ᶠ s : ℂ in halfPlaneUpper σ₀, (1 : ℝ) ≤ ‖s‖ :=
  (tendsto_norm_halfPlaneUpper σ₀).eventually_ge_atTop 1

/-- A function is flat on the upper right half-plane when it beats every power of the modulus. -/
def IsFlatOn (σ₀ : ℝ) (A : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, Tendsto (fun s : ℂ => ‖s‖ ^ N * ‖A s‖) (halfPlaneUpper σ₀) (nhds 0)

theorem IsFlatOn.sub {σ₀ : ℝ} {A B : ℂ → ℂ} (hA : IsFlatOn σ₀ A) (hB : IsFlatOn σ₀ B) :
    IsFlatOn σ₀ (fun s => A s - B s) := by
  intro N
  have h := (hA N).add (hB N)
  rw [add_zero] at h
  refine squeeze_zero' (Filter.Eventually.of_forall fun s => by positivity) ?_ h
  refine Filter.Eventually.of_forall fun s => ?_
  have hnorm : ‖A s - B s‖ ≤ ‖A s‖ + ‖B s‖ := norm_sub_le _ _
  calc ‖s‖ ^ N * ‖A s - B s‖ ≤ ‖s‖ ^ N * (‖A s‖ + ‖B s‖) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ‖s‖ ^ N * ‖A s‖ + ‖s‖ ^ N * ‖B s‖ := by ring

/-- A polynomial is bounded by a multiple of the power of its degree on the filter. -/
theorem eventually_norm_eval_le_filter (σ₀ : ℝ) (p : Polynomial ℂ) :
    ∀ᶠ s : ℂ in halfPlaneUpper σ₀,
      ‖p.eval s‖ ≤ (‖p.leadingCoeff‖ + 1) * ‖s‖ ^ p.natDegree := by
  have hlim := (tendsto_eval_div_pow_natDegree_of_norm_atTop
    (tendsto_norm_halfPlaneUpper σ₀) p).norm
  have hlt : ∀ᶠ s : ℂ in halfPlaneUpper σ₀,
      ‖p.eval s / s ^ p.natDegree‖ < ‖p.leadingCoeff‖ + 1 :=
    hlim.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hlt, eventually_one_le_norm σ₀] with s hs hs1
  have hne : s ≠ 0 := by
    intro h
    rw [h] at hs1
    simp at hs1
    linarith
  have hpow : (0 : ℝ) < ‖s ^ p.natDegree‖ := norm_pos_iff.mpr (pow_ne_zero _ hne)
  rw [norm_div] at hs
  have hlt' := (div_lt_iff₀ hpow).mp hs
  rw [norm_pow] at hlt'
  exact hlt'.le

/-- A nonzero polynomial is bounded below by a multiple of the power of its degree. -/
theorem eventually_norm_eval_ge_filter (σ₀ : ℝ) {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∀ᶠ s : ℂ in halfPlaneUpper σ₀,
      ‖p.leadingCoeff‖ / 2 * ‖s‖ ^ p.natDegree ≤ ‖p.eval s‖ := by
  have hpos : 0 < ‖p.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hlim := (tendsto_eval_div_pow_natDegree_of_norm_atTop
    (tendsto_norm_halfPlaneUpper σ₀) p).norm
  have hgt : ∀ᶠ s : ℂ in halfPlaneUpper σ₀,
      ‖p.leadingCoeff‖ / 2 < ‖p.eval s / s ^ p.natDegree‖ :=
    hlim.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hgt, eventually_one_le_norm σ₀] with s hs hs1
  have hne : s ≠ 0 := by
    intro h
    rw [h] at hs1
    simp at hs1
    linarith
  have hpow : (0 : ℝ) < ‖s ^ p.natDegree‖ := norm_pos_iff.mpr (pow_ne_zero _ hne)
  rw [norm_div] at hs
  have := (lt_div_iff₀ hpow).mp hs
  rw [norm_pow] at this
  exact this.le

/-- Flatness survives multiplication by a polynomial. -/
theorem IsFlatOn.mul_poly {σ₀ : ℝ} {A : ℂ → ℂ} (hA : IsFlatOn σ₀ A) (p : Polynomial ℂ) :
    IsFlatOn σ₀ (fun s => p.eval s * A s) := by
  intro N
  have hA' := (hA (N + p.natDegree)).const_mul (‖p.leadingCoeff‖ + 1)
  rw [mul_zero] at hA'
  refine squeeze_zero' (Filter.Eventually.of_forall fun s => by positivity) ?_ hA'
  filter_upwards [eventually_norm_eval_le_filter σ₀ p] with s hs
  have hnn : (0 : ℝ) ≤ ‖A s‖ := norm_nonneg _
  calc ‖s‖ ^ N * ‖p.eval s * A s‖ = ‖s‖ ^ N * (‖p.eval s‖ * ‖A s‖) := by rw [norm_mul]
    _ ≤ ‖s‖ ^ N * ((‖p.leadingCoeff‖ + 1) * ‖s‖ ^ p.natDegree * ‖A s‖) := by
        have := mul_le_mul_of_nonneg_right hs hnn
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = (‖p.leadingCoeff‖ + 1) * (‖s‖ ^ (N + p.natDegree) * ‖A s‖) := by
        rw [pow_add]
        ring

/-- Flatness survives division by a nonzero polynomial. -/
theorem IsFlatOn.div_poly {σ₀ : ℝ} {A : ℂ → ℂ} (hA : IsFlatOn σ₀ A) {p : Polynomial ℂ}
    (hp : p ≠ 0) : IsFlatOn σ₀ (fun s => A s / p.eval s) := by
  intro N
  have hpos : 0 < ‖p.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hA' := (hA N).const_mul (‖p.leadingCoeff‖ / 2)⁻¹
  rw [mul_zero] at hA'
  refine squeeze_zero' (Filter.Eventually.of_forall fun s => by positivity) ?_ hA'
  filter_upwards [eventually_norm_eval_ge_filter σ₀ hp, eventually_one_le_norm σ₀] with s hs hs1
  have hc : 0 < ‖p.leadingCoeff‖ / 2 := by linarith
  have hpowge : (1 : ℝ) ≤ ‖s‖ ^ p.natDegree := one_le_pow₀ hs1
  have hge : ‖p.leadingCoeff‖ / 2 ≤ ‖p.eval s‖ := by nlinarith
  have hppos : (0 : ℝ) < ‖p.eval s‖ := lt_of_lt_of_le hc hge
  have hquot : ‖A s / p.eval s‖ ≤ (‖p.leadingCoeff‖ / 2)⁻¹ * ‖A s‖ := by
    rw [norm_div, div_le_iff₀ hppos]
    have hstep : (‖p.leadingCoeff‖ / 2)⁻¹ * ‖A s‖ * (‖p.leadingCoeff‖ / 2)
        ≤ (‖p.leadingCoeff‖ / 2)⁻¹ * ‖A s‖ * ‖p.eval s‖ :=
      mul_le_mul_of_nonneg_left hge (by positivity)
    have hcc : (‖p.leadingCoeff‖ / 2)⁻¹ * ‖A s‖ * (‖p.leadingCoeff‖ / 2) = ‖A s‖ := by
      field_simp
    linarith
  calc ‖s‖ ^ N * ‖A s / p.eval s‖ ≤ ‖s‖ ^ N * ((‖p.leadingCoeff‖ / 2)⁻¹ * ‖A s‖) :=
        mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = (‖p.leadingCoeff‖ / 2)⁻¹ * (‖s‖ ^ N * ‖A s‖) := by ring

/-- The unit translation maps the filter into itself. -/
theorem tendsto_add_one_halfPlaneUpper (σ₀ : ℝ) :
    Tendsto (fun s : ℂ => s + 1) (halfPlaneUpper σ₀) (halfPlaneUpper σ₀) := by
  rw [halfPlaneUpper, tendsto_inf]
  constructor
  · rw [tendsto_comap_iff]
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_halfPlaneUpper_im (σ₀ := σ₀) b] with s hs
    simpa using hs
  · rw [tendsto_principal]
    filter_upwards [eventually_halfPlaneUpper_re (σ₀ := σ₀)] with s hs
    simpa using le_trans hs (by linarith : s.re ≤ s.re + 1)

/-- Flatness survives the unit translation. -/
theorem IsFlatOn.shift {σ₀ : ℝ} {A : ℂ → ℂ} (hA : IsFlatOn σ₀ A) :
    IsFlatOn σ₀ (fun s => A (s + 1)) := by
  intro N
  have hcomp := (hA N).comp (tendsto_add_one_halfPlaneUpper σ₀)
  have hpow := hcomp.const_mul ((2 : ℝ) ^ N)
  rw [mul_zero] at hpow
  refine squeeze_zero' (Filter.Eventually.of_forall fun s => by positivity) ?_ hpow
  filter_upwards [eventually_halfPlaneUpper_im (σ₀ := σ₀) 1] with s him
  have h4 : (1 : ℝ) ≤ ‖s + 1‖ := by
    have him' : (s + 1).im = s.im := by simp
    calc (1 : ℝ) ≤ s.im := him
      _ = (s + 1).im := him'.symm
      _ ≤ |(s + 1).im| := le_abs_self _
      _ ≤ ‖s + 1‖ := Complex.abs_im_le_norm _
  have hnorm : ‖s‖ ≤ 2 * ‖s + 1‖ := by
    have hEq : s = (s + 1) + (-1 : ℂ) := by ring
    have h1 : ‖s‖ ≤ ‖s + 1‖ + 1 := by
      calc ‖s‖ = ‖(s + 1) + (-1 : ℂ)‖ := by rw [← hEq]
        _ ≤ ‖s + 1‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
        _ = ‖s + 1‖ + 1 := by simp
    linarith
  have hpowle : ‖s‖ ^ N ≤ 2 ^ N * ‖s + 1‖ ^ N := by
    calc ‖s‖ ^ N ≤ (2 * ‖s + 1‖) ^ N := pow_le_pow_left₀ (norm_nonneg _) hnorm N
      _ = 2 ^ N * ‖s + 1‖ ^ N := mul_pow _ _ _
  calc ‖s‖ ^ N * ‖A (s + 1)‖ ≤ 2 ^ N * ‖s + 1‖ ^ N * ‖A (s + 1)‖ :=
        mul_le_mul_of_nonneg_right hpowle (norm_nonneg _)
    _ = 2 ^ N * (‖s + 1‖ ^ N * ‖A (s + 1)‖) := by ring

/-- **A nonzero polynomial is not flat.** -/
theorem not_isFlatOn_polynomial {σ₀ : ℝ} {p : Polynomial ℂ} (hp : p ≠ 0) :
    ¬ IsFlatOn σ₀ (fun s => p.eval s) := by
  intro hflat
  have hpos : 0 < ‖p.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have h := hflat 0
  simp only [pow_zero, one_mul] at h
  have hlt : ∀ᶠ s : ℂ in halfPlaneUpper σ₀, ‖p.eval s‖ < ‖p.leadingCoeff‖ / 2 :=
    h.eventually (eventually_lt_nhds (by linarith))
  have hboth : ∀ᶠ s : ℂ in halfPlaneUpper σ₀, False := by
    filter_upwards [hlt, eventually_norm_eval_ge_filter σ₀ hp, eventually_one_le_norm σ₀]
      with s h1 h2 h3
    have hpowge : (1 : ℝ) ≤ ‖s‖ ^ p.natDegree := one_le_pow₀ h3
    nlinarith
  exact (halfPlaneUpper_neBot σ₀).ne (Filter.empty_mem_iff_bot.mp hboth)

end GaloisForLFunctions
