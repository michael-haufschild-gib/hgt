import GaloisForLFunctions.RHTower.XiHerglotzCriterion

/-!
# RH as vertical monotonicity of `|Ξ|`

Along a vertical line the logarithmic derivative of the modulus is the imaginary
part of the logarithmic derivative up to sign,
`∂_y log |XiC (x + iy)| = −Im (logDeriv XiC (x + iy))`, so the Herglotz sign
condition says exactly that `y ↦ |XiC (x + iy)|` never decreases.

That reading makes the criterion elementary in one direction: an off-critical
zero sits at some `x₀ + iy₀` with `y₀ > 0`, where the modulus vanishes, while at
nearby smaller heights it is nonzero because zeros are isolated.  Monotonicity
along the vertical ray through `x₀` is therefore impossible, so

**vertical monotonicity of `|Ξ|` on every ray forces the Riemann Hypothesis.**

Under RH the same monotonicity is the transparent statement that
`|Ξ(x + iy)| = ∏ √((x − tₙ)² + y²)` (times a nonvanishing factor) increases in
`y`, each factor being the distance from `x + iy` to a real zero.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-- Zeros of the centred completed zeta are isolated: below any zero on its own
vertical ray there are heights at which the modulus is positive. -/
theorem exists_pos_norm_below_zero {pt₀ : ℂ} (h0 : XiC pt₀ = 0)
    (him : 0 < pt₀.im) :
    ∃ y : ℝ, 0 < y ∧ y < pt₀.im ∧
      XiC ((pt₀.re : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ := XiC_peel_ball pt₀
  set m := (analyticOrderAt XiC pt₀).toNat with hm
  have hmpos : 0 < m := XiC_order_toNat_pos h0
  set t : ℝ := min (pt₀.im / 2) (R / 2) with ht
  have htpos : 0 < t := lt_min (by linarith) (by linarith)
  have htim : t < pt₀.im := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htR : t < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨pt₀.im - t, by linarith, by linarith, ?_⟩
  set z : ℂ := (pt₀.re : ℂ) + ((pt₀.im - t : ℝ) : ℂ) * Complex.I with hz
  have hzval : z = pt₀ - (t : ℂ) * Complex.I := by
    rw [hz]
    apply Complex.ext <;> simp
  have hmem : z ∈ ball pt₀ R := by
    rw [mem_ball, dist_eq_norm, hzval]
    simp only [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    exact htR
  have hzne : z ≠ pt₀ := by
    rw [hzval]
    intro hcon
    have hcon' : ((t : ℂ)) * Complex.I = 0 := by linear_combination -hcon
    rcases mul_eq_zero.mp hcon' with h | h
    · exact absurd (by exact_mod_cast h : (t : ℝ) = 0) htpos.ne'
    · exact Complex.I_ne_zero h
  rw [hfact z hmem]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzne)) (hg0 z hmem)

/-- **The vertical monotonicity criterion.**  If for every real abscissa the
modulus `y ↦ ‖XiC (x + iy)‖` never decreases on the nonnegative ray, then the
Riemann Hypothesis holds: an off-critical zero would force the modulus to drop
to zero at its own height while being positive just below it. -/
theorem riemannHypothesis_of_norm_XiC_vertical_monotone
    (hmono : ∀ x y₁ y₂ : ℝ, 0 ≤ y₁ → y₁ ≤ y₂ →
      ‖XiC ((x : ℂ) + (y₁ : ℂ) * Complex.I)‖ ≤
        ‖XiC ((x : ℂ) + (y₂ : ℂ) * Complex.I)‖) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hzero
  -- centred coordinate of the off-critical zero, conjugated into the upper half
  set pt₁ : ℂ := -Complex.I * (s - 1 / 2) with hpt
  have hre : 1 / 2 < s.re := hs
  have hXpt : XiC pt₁ = 0 := by
    show xi ((1 / 2 : ℂ) + pt₁ * Complex.I) = 0
    have harg : (1 / 2 : ℂ) + pt₁ * Complex.I = s := by
      rw [hpt,
        show (-Complex.I * (s - 1 / 2) * Complex.I) =
          -(Complex.I * Complex.I) * (s - 1 / 2) from by ring,
        Complex.I_mul_I]
      ring
    rw [harg]
    exact hzero
  have hptim : pt₁.im < 0 := by
    have hval : pt₁.im = -(s.re - 1 / 2) := by
      rw [hpt]
      simp [Complex.mul_im, Complex.sub_re]
    rw [hval]
    linarith
  set pt₀ : ℂ := (starRingEnd ℂ) pt₁ with hpt₀
  have hX0 : XiC pt₀ = 0 := by
    rw [hpt₀, XiC_conj', hXpt, map_zero]
  have him : 0 < pt₀.im := by
    rw [hpt₀]
    simpa using hptim
  obtain ⟨y, hypos, hylt, hyne⟩ := exists_pos_norm_below_zero hX0 him
  -- the modulus is positive below the zero and vanishes at it
  have hzero_at : XiC ((pt₀.re : ℂ) + ((pt₀.im : ℝ) : ℂ) * Complex.I) = 0 := by
    have hre_eq : ((pt₀.re : ℂ)) + ((pt₀.im : ℝ) : ℂ) * Complex.I = pt₀ := by
      apply Complex.ext <;> simp
    rw [hre_eq]
    exact hX0
  have hstep := hmono pt₀.re y pt₀.im (le_of_lt hypos) (le_of_lt hylt)
  rw [hzero_at, norm_zero] at hstep
  exact hyne (norm_eq_zero.mp (le_antisymm hstep (norm_nonneg _)))

end

end RHTower
