import GaloisForLFunctions.HTGeometry.LogProductPowerSeries

/-!
# The unique tangent-normalizing gauge of a polarized product

The polarized logarithm of a linear product family is the difference of the logarithms of its two
opposite orientations.  Its first Taylor coefficient is exactly minus twice the first power sum of
the family, because after adding the linear counterterm the remaining series starts at the cube.

Consequently a linear exponential gauge `exp (c·t)` makes the polarized phase tangent to the
constant `1` at the marked point exactly for one value of `c`, namely twice the first power sum.
When the family is the reciprocal of a finite smooth monoid this is the divergent Euler mass, so
the gauge is forced at every finite aperture and the counterterm is not a choice.

* `HTGeometry.polarizedLog`;
* `HTGeometry.hasDerivAt_polarizedLog_zero`;
* `HTGeometry.polarizedLog_gauge_tangent_eq_zero_iff`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace HTGeometry

variable {ι : Type*} {a : ι → ℂ}

/-- The polarized logarithm of a linear product family. -/
def polarizedLog (a : ι → ℂ) (t : ℂ) : ℂ :=
  (∑' i, Complex.log (1 - t * a i)) - ∑' i, Complex.log (1 + t * a i)

@[simp] theorem polarizedLog_zero (a : ι → ℂ) : polarizedLog a 0 = 0 := by
  simp [polarizedLog]

theorem norm_powerSum_le (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1) {k : ℕ}
    (hk : 1 ≤ k) : ‖powerSum a k‖ ≤ ∑' i, ‖a i‖ := by
  have hsn : Summable fun i => ‖(a i) ^ k‖ := summable_norm_pow ha hb hk
  calc ‖powerSum a k‖ = ‖∑' i, (a i) ^ k‖ := rfl
    _ ≤ ∑' i, ‖(a i) ^ k‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' i, ‖a i‖ := by
        refine Summable.tsum_le_tsum (fun i => ?_) hsn ha
        rw [norm_pow]
        calc ‖a i‖ ^ k ≤ ‖a i‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (hb i) hk
          _ = ‖a i‖ := pow_one _

/-- **The tangent-normalized polarized logarithm vanishes to third order.** -/
theorem norm_polarizedLog_add_tangent_le (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1)
    {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    ‖polarizedLog a t + 2 * powerSum a 1 * t‖ ≤ 4 * (∑' i, ‖a i‖) * ‖t‖ ^ 3 := by
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht (by norm_num)
  have hsum := hasSum_logPolarizedPhase ha hb ht1
  set A : ℝ := ∑' i, ‖a i‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  set f : ℕ → ℂ := fun j => -(2 * powerSum a (2 * (j + 1) + 1) * t ^ (2 * (j + 1) + 1)
      / ((2 * (j + 1) + 1 : ℕ) : ℂ)) with hf
  have htn : (0 : ℝ) ≤ ‖t‖ := norm_nonneg _
  have hbound : ∀ j : ℕ, ‖f j‖ ≤ (2 * A * ‖t‖ ^ 3) * (‖t‖ ^ 2) ^ j := by
    intro j
    have hPk : ‖powerSum a (2 * (j + 1) + 1)‖ ≤ A := norm_powerSum_le ha hb (by omega)
    have hcast : ‖((2 * (j + 1) + 1 : ℕ) : ℂ)‖ = ((2 * (j + 1) + 1 : ℕ) : ℝ) := by
      rw [Complex.norm_natCast]
    have hval : ‖f j‖
        = 2 * ‖powerSum a (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1)
          / ((2 * (j + 1) + 1 : ℕ) : ℝ) := by
      rw [hf]
      simp only [norm_neg, norm_div, norm_mul, norm_pow, hcast]
      norm_num
    have hpowsplit : ‖t‖ ^ (2 * (j + 1) + 1) = ‖t‖ ^ 3 * (‖t‖ ^ 2) ^ j := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hden : (1 : ℝ) ≤ ((2 * (j + 1) + 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 2 * (j + 1) + 1 := by omega
      exact_mod_cast this
    have hnum0 : (0 : ℝ) ≤ 2 * ‖powerSum a (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1) := by
      positivity
    calc ‖f j‖ = 2 * ‖powerSum a (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1)
          / ((2 * (j + 1) + 1 : ℕ) : ℝ) := hval
      _ ≤ 2 * ‖powerSum a (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1) := by
          exact div_le_self hnum0 hden
      _ ≤ 2 * A * ‖t‖ ^ (2 * (j + 1) + 1) := by
          have : ‖powerSum a (2 * (j + 1) + 1)‖ * ‖t‖ ^ (2 * (j + 1) + 1)
              ≤ A * ‖t‖ ^ (2 * (j + 1) + 1) := by
            exact mul_le_mul_of_nonneg_right hPk (by positivity)
          nlinarith [this]
      _ = (2 * A * ‖t‖ ^ 3) * (‖t‖ ^ 2) ^ j := by rw [hpowsplit]; ring
  have hgeo : ‖t‖ ^ 2 < 1 := by
    have : ‖t‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ htn ht 2
    linarith [this]
  have hsummable : Summable fun j : ℕ => (2 * A * ‖t‖ ^ 3) * (‖t‖ ^ 2) ^ j :=
    (summable_geometric_of_lt_one (by positivity) hgeo).mul_left _
  have hsn : Summable fun j => ‖f j‖ :=
    hsummable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hgeoval : ∑' j : ℕ, (2 * A * ‖t‖ ^ 3) * (‖t‖ ^ 2) ^ j
      = (2 * A * ‖t‖ ^ 3) * (1 - ‖t‖ ^ 2)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hgeo]
  have hquarter : ‖t‖ ^ 2 ≤ 1 / 4 := by
    have : ‖t‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ htn ht 2
    linarith [this]
  have hinv : (1 - ‖t‖ ^ 2)⁻¹ ≤ 4 / 3 := by
    have hpos : (0 : ℝ) < 1 - ‖t‖ ^ 2 := by linarith
    rw [inv_le_iff_one_le_mul₀ hpos]
    linarith
  have hfsum : (∑' j, f j) = polarizedLog a t + 2 * powerSum a 1 * t := by
    rw [hsum.tsum_eq, polarizedLog]
  rw [← hfsum]
  calc ‖∑' j, f j‖ ≤ ∑' j, ‖f j‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' j : ℕ, (2 * A * ‖t‖ ^ 3) * (‖t‖ ^ 2) ^ j :=
        Summable.tsum_le_tsum hbound hsn hsummable
    _ = (2 * A * ‖t‖ ^ 3) * (1 - ‖t‖ ^ 2)⁻¹ := hgeoval
    _ ≤ (2 * A * ‖t‖ ^ 3) * (4 / 3) := by
        have hnn : (0 : ℝ) ≤ 2 * A * ‖t‖ ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_left hinv hnn
    _ ≤ 4 * A * ‖t‖ ^ 3 := by nlinarith [hA0, pow_nonneg htn 3]

/-- **The first logarithmic trace of the polarized product is minus twice the first power sum.** -/
theorem hasDerivAt_polarizedLog_zero (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1) :
    HasDerivAt (polarizedLog a) (-(2 * powerSum a 1)) 0 := by
  set A : ℝ := ∑' i, ‖a i‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  rw [hasDerivAt_iff_tendsto_slope]
  have hev : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ), ‖t‖ ≤ 1 / 2 := by
    have hball : ∀ᶠ t : ℂ in 𝓝 (0 : ℂ), ‖t‖ ≤ 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
      rw [Metric.mem_ball, dist_zero_right] at ht
      linarith
    exact hball.filter_mono nhdsWithin_le_nhds
  have hbnd : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ),
      ‖slope (polarizedLog a) 0 t - (-(2 * powerSum a 1))‖ ≤ 4 * A * ‖t‖ ^ 2 := by
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
    have htne' : t ≠ 0 := htne
    have hslope : slope (polarizedLog a) 0 t = polarizedLog a t / t := by
      rw [slope_def_field, polarizedLog_zero]
      field_simp
      ring
    have hdiff : slope (polarizedLog a) 0 t - (-(2 * powerSum a 1))
        = (polarizedLog a t + 2 * powerSum a 1 * t) / t := by
      rw [hslope]
      field_simp
      ring
    rw [hdiff, norm_div]
    have hnum := norm_polarizedLog_add_tangent_le ha hb ht
    have htpos : 0 < ‖t‖ := norm_pos_iff.2 htne'
    rw [div_le_iff₀ htpos]
    calc ‖polarizedLog a t + 2 * powerSum a 1 * t‖ ≤ 4 * A * ‖t‖ ^ 3 := hnum
      _ = 4 * A * ‖t‖ ^ 2 * ‖t‖ := by ring
  have hzero : Tendsto (fun t : ℂ => 4 * A * ‖t‖ ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have hcont : Continuous fun t : ℂ => 4 * A * ‖t‖ ^ 2 := by fun_prop
    have := (hcont.tendsto (0 : ℂ)).mono_left (nhdsWithin_le_nhds (s := ({(0 : ℂ)}ᶜ)))
    simpa using this
  have hkey : Tendsto (fun t : ℂ => slope (polarizedLog a) 0 t - (-(2 * powerSum a 1)))
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := squeeze_zero_norm' hbnd hzero
  exact tendsto_sub_nhds_zero_iff.1 hkey

/-- The tangent of a linearly gauged polarized logarithm. -/
theorem hasDerivAt_polarizedLog_gauge (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1)
    (c : ℂ) :
    HasDerivAt (fun t => polarizedLog a t + c * t) (c - 2 * powerSum a 1) 0 := by
  have h1 := hasDerivAt_polarizedLog_zero ha hb
  have h2 : HasDerivAt (fun t : ℂ => c * t) c 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul c
  have h3 := h1.add h2
  have hval : -(2 * powerSum a 1) + c = c - 2 * powerSum a 1 := by ring
  rwa [hval] at h3

/-- **The tangent-normalizing gauge is unique.**  A linear exponential gauge removes the first
logarithmic trace of the polarized product exactly for the doubled first power sum. -/
theorem polarizedLog_gauge_tangent_eq_zero_iff (ha : Summable fun i => ‖a i‖)
    (hb : ∀ i, ‖a i‖ ≤ 1) (c : ℂ) :
    HasDerivAt (fun t => polarizedLog a t + c * t) 0 0 ↔ c = 2 * powerSum a 1 := by
  constructor
  · intro h
    have hu := h.unique (hasDerivAt_polarizedLog_gauge ha hb c)
    linear_combination -hu
  · intro hc
    subst hc
    have h := hasDerivAt_polarizedLog_gauge ha hb (2 * powerSum a 1)
    have hval : 2 * powerSum a 1 - 2 * powerSum a 1 = (0 : ℂ) := by ring
    rwa [hval] at h

end HTGeometry
