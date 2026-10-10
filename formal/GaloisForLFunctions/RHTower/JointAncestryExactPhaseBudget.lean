import GaloisForLFunctions.RHTower.JointAncestrySimilarityLaw

/-!
# The exact phase budget of a dressed explicit-formula sector

After rotation to its Kronecker frame, the local density of a dressed sector with radii
`r₁, r₂ ∈ [0, 1)` is

`ℓ(θ) = (1 - r₁r₂) / ((1 - r₁e^{iθ})(1 - r₂e^{-iθ}))`,

with positive real part and `tan arg ℓ(θ) = (r₁ - r₂) sin θ / (1 + r₁r₂ - (r₁ + r₂) cos θ)`.

* **Phase width.**  `|arg ℓ(θ)| ≤ W(r₁, r₂) := arctan (|r₁ - r₂| / √((1 - r₁²)(1 - r₂²)))`, with
  equality at `cos θ = (r₁ + r₂)/(1 + r₁r₂)`.  The bound is the identity
  `(a - b cos θ)² - (a² - b²) sin² θ = (b - a cos θ)²` with `a = 1 + r₁r₂`, `b = r₁ + r₂`,
  `a² - b² = (1 - r₁²)(1 - r₂²)`.
* **Exact criterion.**  A finite product of such densities has nonnegative real part at every point
  of its torus iff the widths sum to at most `π/2`.

Applied to the dressed sector of a strip point `ρ` (radii `p^{-(Re ρ + c)}`, `p^{-(1 - Re ρ + c)}`),
the sector is nonnegative at every finite depth iff `Σ_p W_p ≤ π/2`.  This makes the single-sector
gap law exact: the dressing threshold is the solution of `Σ_p W_p(c) = π/2`; for a zero at small
distance `δ` from the line, `W_p ≈ 2δ p^{-1/2-c} log p`, which places the threshold at
`σ ≈ 1 + 4δ/π`.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-- The local density in its Kronecker frame. -/
def jasRotLocal (r₁ r₂ θ : ℝ) : ℂ :=
  ((1 - r₁ * r₂ : ℝ) : ℂ) /
    ((1 - (r₁ : ℂ) * cexp ((θ : ℂ) * I)) * (1 - (r₂ : ℂ) * cexp (((-θ : ℝ) : ℂ) * I)))

/-- `1 + r₁r₂ - (r₁ + r₂) cos θ`. -/
def jasRotDen (r₁ r₂ θ : ℝ) : ℝ := 1 + r₁ * r₂ - (r₁ + r₂) * Real.cos θ

/-- The slope `tan arg ℓ(θ)`. -/
def jasRotSlope (r₁ r₂ θ : ℝ) : ℝ := (r₁ - r₂) * Real.sin θ / jasRotDen r₁ r₂ θ

/-- The phase width `arctan (|r₁ - r₂| / √((1 - r₁²)(1 - r₂²)))`. -/
def jasPhaseWidth (r₁ r₂ : ℝ) : ℝ :=
  Real.arctan (|r₁ - r₂| / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)))

section Local

variable {r₁ r₂ : ℝ}

theorem jasRotDen_pos (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) (θ : ℝ) :
    0 < jasRotDen r₁ r₂ θ := by
  unfold jasRotDen
  have hc := Real.cos_le_one θ
  nlinarith [mul_pos (sub_pos.mpr h₁') (sub_pos.mpr h₂')]

/-- The denominator `(1 - r₁e^{iθ})(1 - r₂e^{-iθ}) = D - i(r₁ - r₂) sin θ`. -/
theorem jasRotLocal_den_eq (r₁ r₂ θ : ℝ) :
    (1 - (r₁ : ℂ) * cexp ((θ : ℂ) * I)) * (1 - (r₂ : ℂ) * cexp (((-θ : ℝ) : ℂ) * I)) =
      ((jasRotDen r₁ r₂ θ : ℝ) : ℂ) - ((r₁ - r₂) * Real.sin θ : ℝ) * I := by
  have he : cexp ((θ : ℂ) * I) * cexp (((-θ : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; push_cast; simp
  apply Complex.ext
  · simp only [jasRotDen, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.sub_im,
      Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im, Real.cos_neg, Real.sin_neg]
    linear_combination (r₁ * r₂) * Real.sin_sq_add_cos_sq θ
  · simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.sub_im,
      Complex.one_im, Complex.mul_re, Complex.I_re, Complex.I_im, Real.cos_neg, Real.sin_neg]
    ring

theorem jasRotDenC_ne_zero (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) (θ : ℝ) :
    ((jasRotDen r₁ r₂ θ : ℝ) : ℂ) - ((r₁ - r₂) * Real.sin θ : ℝ) * I ≠ 0 := by
  have hD := jasRotDen_pos h₁ h₁' h₂ h₂' θ
  intro h; have := congrArg Complex.re h; simp at this; linarith

theorem normSq_jasRotDenC (r₁ r₂ θ : ℝ) :
    Complex.normSq (((jasRotDen r₁ r₂ θ : ℝ) : ℂ) - ((r₁ - r₂) * Real.sin θ : ℝ) * I) =
      (jasRotDen r₁ r₂ θ) ^ 2 + ((r₁ - r₂) * Real.sin θ) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_sub,
    add_zero]
  ring

theorem re_jasRotLocal (r₁ r₂ θ : ℝ) :
    (jasRotLocal r₁ r₂ θ).re = (1 - r₁ * r₂) * jasRotDen r₁ r₂ θ /
      ((jasRotDen r₁ r₂ θ) ^ 2 + ((r₁ - r₂) * Real.sin θ) ^ 2) := by
  rw [jasRotLocal, jasRotLocal_den_eq, Complex.div_re, normSq_jasRotDenC]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, zero_sub,
    add_zero]
  ring

theorem im_jasRotLocal (r₁ r₂ θ : ℝ) :
    (jasRotLocal r₁ r₂ θ).im = (1 - r₁ * r₂) * ((r₁ - r₂) * Real.sin θ) /
      ((jasRotDen r₁ r₂ θ) ^ 2 + ((r₁ - r₂) * Real.sin θ) ^ 2) := by
  rw [jasRotLocal, jasRotLocal_den_eq, Complex.div_im, normSq_jasRotDenC]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_sub,
    add_zero]
  ring

theorem re_jasRotLocal_pos (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) (θ : ℝ) :
    0 < (jasRotLocal r₁ r₂ θ).re := by
  rw [re_jasRotLocal]
  have hD := jasRotDen_pos h₁ h₁' h₂ h₂' θ
  have hr : 0 < 1 - r₁ * r₂ := by nlinarith
  positivity

theorem jasRotLocal_ne_zero (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) (θ : ℝ) :
    jasRotLocal r₁ r₂ θ ≠ 0 := fun h => by
  have := re_jasRotLocal_pos h₁ h₁' h₂ h₂' θ
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- `arg ℓ(θ) = arctan (slope)`. -/
theorem arg_jasRotLocal (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) (θ : ℝ) :
    (jasRotLocal r₁ r₂ θ).arg = Real.arctan (jasRotSlope r₁ r₂ θ) := by
  have hre := re_jasRotLocal_pos h₁ h₁' h₂ h₂' θ
  have habs : |(jasRotLocal r₁ r₂ θ).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have ht := Real.arctan_tan (x := (jasRotLocal r₁ r₂ θ).arg)
    (by linarith [neg_abs_le (jasRotLocal r₁ r₂ θ).arg])
    (by linarith [le_abs_self (jasRotLocal r₁ r₂ θ).arg])
  rw [Complex.tan_arg] at ht
  rw [← ht]
  congr 1
  rw [re_jasRotLocal, im_jasRotLocal, jasRotSlope]
  have hD := jasRotDen_pos h₁ h₁' h₂ h₂' θ
  have hr : 0 < 1 - r₁ * r₂ := by nlinarith
  have hN : 0 < (jasRotDen r₁ r₂ θ) ^ 2 + ((r₁ - r₂) * Real.sin θ) ^ 2 := by positivity
  field_simp

/-- `a² - b² = (1 - r₁²)(1 - r₂²)` for `a = 1 + r₁r₂`, `b = r₁ + r₂`. -/
theorem jasRot_disc (r₁ r₂ : ℝ) :
    (1 + r₁ * r₂) ^ 2 - (r₁ + r₂) ^ 2 = (1 - r₁ ^ 2) * (1 - r₂ ^ 2) := by ring

/-- **Slope bound**: `|slope| ≤ |r₁ - r₂| / √((1 - r₁²)(1 - r₂²))`. -/
theorem abs_jasRotSlope_le (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) (θ : ℝ) :
    |jasRotSlope r₁ r₂ θ| ≤ |r₁ - r₂| / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by
  have hD := jasRotDen_pos h₁ h₁' h₂ h₂' θ
  have hP : 0 < (1 - r₁ ^ 2) * (1 - r₂ ^ 2) := by
    apply mul_pos <;> nlinarith
  have hS := Real.sqrt_pos.mpr hP
  have hkey : |Real.sin θ| * Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) ≤ jasRotDen r₁ r₂ θ := by
    rw [← Real.sqrt_sq (abs_nonneg (Real.sin θ)), ← Real.sqrt_mul (sq_nonneg _),
      ← Real.sqrt_sq hD.le]
    apply Real.sqrt_le_sqrt
    rw [sq_abs, ← jasRot_disc]
    have hid : (jasRotDen r₁ r₂ θ) ^ 2 - Real.sin θ ^ 2 * ((1 + r₁ * r₂) ^ 2 - (r₁ + r₂) ^ 2) =
        ((r₁ + r₂) - (1 + r₁ * r₂) * Real.cos θ) ^ 2 := by
      unfold jasRotDen
      have := Real.sin_sq_add_cos_sq θ
      nlinarith [this]
    nlinarith [sq_nonneg ((r₁ + r₂) - (1 + r₁ * r₂) * Real.cos θ)]
  rw [jasRotSlope, abs_div, abs_mul, abs_of_pos hD, div_le_div_iff₀ hD hS]
  calc |r₁ - r₂| * |Real.sin θ| * Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2))
      = |r₁ - r₂| * (|Real.sin θ| * Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2))) := by ring
    _ ≤ |r₁ - r₂| * jasRotDen r₁ r₂ θ := mul_le_mul_of_nonneg_left hkey (abs_nonneg _)

/-- **Phase width bound**: `|arg ℓ(θ)| ≤ W(r₁, r₂)`. -/
theorem abs_arg_jasRotLocal_le (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1)
    (θ : ℝ) : |(jasRotLocal r₁ r₂ θ).arg| ≤ jasPhaseWidth r₁ r₂ := by
  rw [arg_jasRotLocal h₁ h₁' h₂ h₂', jasPhaseWidth]
  have hb := abs_jasRotSlope_le h₁ h₁' h₂ h₂' θ
  rcases le_total 0 (jasRotSlope r₁ r₂ θ) with hs | hs
  · rw [abs_of_nonneg (by rw [← Real.arctan_zero]; exact Real.arctan_strictMono.monotone hs)]
    exact Real.arctan_strictMono.monotone ((le_abs_self _).trans hb)
  · rw [abs_of_nonpos (by rw [← Real.arctan_zero]; exact Real.arctan_strictMono.monotone hs),
      ← Real.arctan_neg]
    exact Real.arctan_strictMono.monotone ((neg_le_abs _).trans hb)

theorem jasPhaseWidth_nonneg (r₁ r₂ : ℝ) : 0 ≤ jasPhaseWidth r₁ r₂ := by
  rw [jasPhaseWidth, ← Real.arctan_zero]
  exact Real.arctan_strictMono.monotone (by positivity)

/-- The width is attained: at `cos θ₀ = (r₁+r₂)/(1+r₁r₂)` the slope equals
`(r₁ - r₂)/√((1 - r₁²)(1 - r₂²))`. -/
theorem jasRotSlope_extremal (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) :
    jasRotSlope r₁ r₂ (Real.arccos ((r₁ + r₂) / (1 + r₁ * r₂))) =
      (r₁ - r₂) / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by
  have ha : 0 < 1 + r₁ * r₂ := by positivity
  have hb0 : 0 ≤ (r₁ + r₂) / (1 + r₁ * r₂) := by positivity
  have hb1 : (r₁ + r₂) / (1 + r₁ * r₂) < 1 := by
    rw [div_lt_one ha]; nlinarith [mul_pos (sub_pos.mpr h₁') (sub_pos.mpr h₂')]
  have hP : 0 < (1 - r₁ ^ 2) * (1 - r₂ ^ 2) := by apply mul_pos <;> nlinarith
  set x := (r₁ + r₂) / (1 + r₁ * r₂) with hx
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos (by linarith) hb1.le
  have hsin : Real.sin (Real.arccos x) = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
  have h1x : 1 - x ^ 2 = (1 - r₁ ^ 2) * (1 - r₂ ^ 2) / (1 + r₁ * r₂) ^ 2 := by
    rw [hx, div_pow, ← jasRot_disc]; field_simp
  have hsq : Real.sqrt (1 - x ^ 2) = Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) / (1 + r₁ * r₂) := by
    rw [h1x, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq ha.le]
  have hden : jasRotDen r₁ r₂ (Real.arccos x) =
      (1 - r₁ ^ 2) * (1 - r₂ ^ 2) / (1 + r₁ * r₂) := by
    rw [jasRotDen, hcos, hx, ← jasRot_disc]; field_simp
  have hS := Real.sqrt_pos.mpr hP
  have hSS : Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) ^ 2 = (1 - r₁ ^ 2) * (1 - r₂ ^ 2) :=
    Real.sq_sqrt hP.le
  rw [jasRotSlope, hsin, hsq, hden]
  generalize hSdef : Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) = S at hS hSS ⊢
  have hP' : (1 - r₁ ^ 2) * (1 - r₂ ^ 2) ≠ 0 := hP.ne'
  rw [← hSS]
  field_simp

/-- Along the ray `θ = t·θ₀` the slope is continuous. -/
theorem continuous_jasRotSlope (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) :
    Continuous fun θ => jasRotSlope r₁ r₂ θ := by
  unfold jasRotSlope jasRotDen
  exact Continuous.div (by fun_prop) (by fun_prop)
    (fun θ => (jasRotDen_pos h₁ h₁' h₂ h₂' θ).ne')

end Local

/-! ## The exact criterion -/

/-- **Exact phase-budget criterion.**  A finite product of rotated local densities has nonnegative
real part at every point of its torus iff the phase widths sum to at most `π/2`. -/
theorem forall_re_prod_jasRotLocal_nonneg_iff {ι : Type*} (P : Finset ι) {r₁ r₂ : ι → ℝ}
    (h₁ : ∀ i, 0 ≤ r₁ i) (h₁' : ∀ i, r₁ i < 1) (h₂ : ∀ i, 0 ≤ r₂ i) (h₂' : ∀ i, r₂ i < 1) :
    (∀ θ : ι → ℝ, 0 ≤ (∏ i ∈ P, jasRotLocal (r₁ i) (r₂ i) (θ i)).re) ↔
      ∑ i ∈ P, jasPhaseWidth (r₁ i) (r₂ i) ≤ Real.pi / 2 := by
  constructor
  · intro h
    by_contra hgt
    push Not at hgt
    -- extremal angles, oriented so that each slope is nonnegative
    set θ₀ : ι → ℝ := fun i => (if r₂ i ≤ r₁ i then 1 else -1) *
      Real.arccos ((r₁ i + r₂ i) / (1 + r₁ i * r₂ i)) with hθ₀
    have hslope0 : ∀ i, jasRotSlope (r₁ i) (r₂ i) (θ₀ i) =
        |r₁ i - r₂ i| / Real.sqrt ((1 - r₁ i ^ 2) * (1 - r₂ i ^ 2)) := by
      intro i
      simp only [hθ₀]
      split_ifs with hle
      · rw [one_mul, jasRotSlope_extremal (h₁ i) (h₁' i) (h₂ i) (h₂' i),
          abs_of_nonneg (by linarith)]
      · have hneg : jasRotSlope (r₁ i) (r₂ i) (-1 * Real.arccos ((r₁ i + r₂ i) / (1 + r₁ i * r₂ i)))
            = -jasRotSlope (r₁ i) (r₂ i) (Real.arccos ((r₁ i + r₂ i) / (1 + r₁ i * r₂ i))) := by
          simp only [jasRotSlope, jasRotDen, neg_one_mul, Real.sin_neg, Real.cos_neg]; ring
        rw [hneg, jasRotSlope_extremal (h₁ i) (h₁' i) (h₂ i) (h₂' i),
          abs_of_neg (by push Not at hle; linarith), neg_div]
    set F : ℝ → ℝ := fun t => ∑ i ∈ P, Real.arctan (jasRotSlope (r₁ i) (r₂ i) (t * θ₀ i))
      with hF
    have hFc : Continuous F :=
      continuous_finsetSum _ fun i _ => Real.continuous_arctan.comp
        ((continuous_jasRotSlope (h₁ i) (h₁' i) (h₂ i) (h₂' i)).comp
          (continuous_id.mul continuous_const))
    have hF0 : F 0 = 0 := Finset.sum_eq_zero fun i _ => by
      simp [jasRotSlope]
    have hF1 : F 1 = ∑ i ∈ P, jasPhaseWidth (r₁ i) (r₂ i) :=
      Finset.sum_congr rfl fun i _ => by rw [one_mul, hslope0, jasPhaseWidth]
    set τ : ℝ := (Real.pi / 2 + min (F 1) Real.pi) / 2 with hτ
    have hτ1 : Real.pi / 2 < τ := by
      rw [hτ]; have : Real.pi / 2 < min (F 1) Real.pi := lt_min (by rw [hF1]; exact hgt)
        (by linarith [Real.pi_pos])
      linarith
    have hτ2 : τ ≤ Real.pi := by
      rw [hτ]; linarith [min_le_right (F 1) Real.pi, Real.pi_pos]
    have hτF : τ ≤ F 1 := by
      rw [hτ]; linarith [min_le_left (F 1) Real.pi, min_le_right (F 1) Real.pi,
        show Real.pi / 2 < min (F 1) Real.pi from lt_min (by rw [hF1]; exact hgt)
          (by linarith [Real.pi_pos])]
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc (zero_le_one' ℝ) hFc.continuousOn
      ⟨by rw [hF0]; linarith [Real.pi_pos], hτF⟩
    have hre := h (fun i => t * θ₀ i)
    rw [prod_eq_prod_norm_mul_exp_sum_arg, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re] at hre
    have hsum : ∑ i ∈ P, (jasRotLocal (r₁ i) (r₂ i) (t * θ₀ i)).arg = τ := by
      rw [← ht]
      exact Finset.sum_congr rfl fun i _ => arg_jasRotLocal (h₁ i) (h₁' i) (h₂ i) (h₂' i) _
    rw [hsum] at hre
    have hnorm : 0 < ∏ i ∈ P, ‖jasRotLocal (r₁ i) (r₂ i) (t * θ₀ i)‖ :=
      Finset.prod_pos fun i _ => norm_pos_iff.mpr (jasRotLocal_ne_zero (h₁ i) (h₁' i) (h₂ i)
        (h₂' i) _)
    have hcos : Real.cos τ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hτ1 (by linarith)
    nlinarith
  · intro hsum θ
    rw [prod_eq_prod_norm_mul_exp_sum_arg, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    refine mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) ?_
    apply Real.cos_nonneg_of_mem_Icc
    have hb : |∑ i ∈ P, (jasRotLocal (r₁ i) (r₂ i) (θ i)).arg| ≤ Real.pi / 2 :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ =>
        abs_arg_jasRotLocal_le (h₁ i) (h₁' i) (h₂ i) (h₂' i) _).trans hsum)
    exact ⟨by linarith [neg_abs_le (∑ i ∈ P, (jasRotLocal (r₁ i) (r₂ i) (θ i)).arg)],
      by linarith [le_abs_self (∑ i ∈ P, (jasRotLocal (r₁ i) (r₂ i) (θ i)).arg)]⟩

/-! ## Dressed sectors -/

theorem inv_one_sub_add_inv_one_sub_sub_one {x y : ℂ} (hx : 1 - x ≠ 0) (hy : 1 - y ≠ 0) :
    (1 - x)⁻¹ + (1 - y)⁻¹ - 1 = (1 - x * y) / ((1 - x) * (1 - y)) := by
  rw [eq_div_iff (mul_ne_zero hx hy)]
  have e1 : (1 - x)⁻¹ * ((1 - x) * (1 - y)) = 1 - y := by
    rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  have e2 : (1 - y)⁻¹ * ((1 - x) * (1 - y)) = 1 - x := by
    rw [mul_comm (1 - x), ← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  rw [sub_mul, add_mul, e1, e2]
  ring

theorem jasHoloLocal_twisted_eq_jasRotLocal (ρ : ℂ) (c θ : ℝ) (p : Nat.Primes)
    (h₁ : jasR1 (ρ + c) p < 1) (h₂ : jasR2 (ρ - c) p < 1) :
    jasHoloLocal (jasHoloA (ρ + c) p) (jasHoloB (ρ - c) p)
        (cexp ((θ : ℂ) * I) * jasKroneckerPoint (ρ + c) p) =
      jasRotLocal (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) θ := by
  have hK : jasKroneckerPoint (ρ + c) p = jasKroneckerPoint (ρ - c) p :=
    jasKroneckerPoint_congr_im (by simp) p
  have hA : jasHoloA (ρ + c) p * (cexp ((θ : ℂ) * I) * jasKroneckerPoint (ρ + c) p) =
      (jasR1 (ρ + c) p : ℂ) * cexp ((θ : ℂ) * I) := by
    rw [mul_left_comm, jasHoloA_mul_kronecker, mul_comm]
  have hconj : conj (cexp ((θ : ℂ) * I)) = cexp (((-θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj]; congr 1; simp
  have hB : jasHoloB (ρ - c) p * conj (cexp ((θ : ℂ) * I) * jasKroneckerPoint (ρ + c) p) =
      (jasR2 (ρ - c) p : ℂ) * cexp (((-θ : ℝ) : ℂ) * I) := by
    rw [map_mul, hconj, hK, mul_left_comm, jasHoloB_mul_conj_kronecker, mul_comm]
  have hx : ‖(jasR1 (ρ + c) p : ℂ) * cexp ((θ : ℂ) * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by rw [jasR1]; exact (Real.exp_pos _).le)]; exact h₁
  have hy : ‖(jasR2 (ρ - c) p : ℂ) * cexp (((-θ : ℝ) : ℂ) * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by rw [jasR2]; exact (Real.exp_pos _).le)]; exact h₂
  have hx0 : 1 - (jasR1 (ρ + c) p : ℂ) * cexp ((θ : ℂ) * I) ≠ 0 := fun h => by
    have : (jasR1 (ρ + c) p : ℂ) * cexp ((θ : ℂ) * I) = 1 := by linear_combination -h
    rw [this, norm_one] at hx; exact lt_irrefl 1 hx
  have hy0 : 1 - (jasR2 (ρ - c) p : ℂ) * cexp (((-θ : ℝ) : ℂ) * I) ≠ 0 := fun h => by
    have : (jasR2 (ρ - c) p : ℂ) * cexp (((-θ : ℝ) : ℂ) * I) = 1 := by linear_combination -h
    rw [this, norm_one] at hy; exact lt_irrefl 1 hy
  have he : cexp ((θ : ℂ) * I) * cexp (((-θ : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; push_cast; simp
  have hxy : (jasR1 (ρ + c) p : ℂ) * cexp ((θ : ℂ) * I) *
      ((jasR2 (ρ - c) p : ℂ) * cexp (((-θ : ℝ) : ℂ) * I)) =
      (jasR1 (ρ + c) p : ℂ) * (jasR2 (ρ - c) p : ℂ) := by
    linear_combination (jasR1 (ρ + c) p : ℂ) * (jasR2 (ρ - c) p : ℂ) * he
  rw [jasHoloLocal, hA, hB, jasRotLocal]
  rw [inv_one_sub_add_inv_one_sub_sub_one hx0 hy0, hxy]
  push_cast
  ring

/-- **Exact criterion for dressed sectors.**  The dressed explicit-formula sector of a strip point
has nonnegative real part at every point of the depth-`P` torus iff `Σ_{p ∈ P} W_p ≤ π/2`. -/
theorem forall_re_prod_jasHoloLocal_dressed_nonneg_iff {ρ : ℂ} {c : ℝ} (hα0 : 0 < ρ.re + c)
    (hα1 : 0 < 1 - ρ.re + c) (P : Finset Nat.Primes) :
    (∀ w : Nat.Primes → ℂ, (∀ p, ‖w p‖ = 1) →
      0 ≤ (∏ p ∈ P, jasHoloLocal (jasHoloA (ρ + c) p) (jasHoloB (ρ - c) p) (w p)).re) ↔
      ∑ p ∈ P, jasPhaseWidth (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) ≤ Real.pi / 2 := by
  have h₁ : ∀ p, 0 ≤ jasR1 (ρ + c) p := fun p => (Real.exp_pos _).le
  have h₂ : ∀ p, 0 ≤ jasR2 (ρ - c) p := fun p => (Real.exp_pos _).le
  have h₁' : ∀ p, jasR1 (ρ + c) p < 1 := fun p => by
    rw [jasR1_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have h₂' : ∀ p, jasR2 (ρ - c) p < 1 := fun p => by
    rw [jasR2_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  rw [← forall_re_prod_jasRotLocal_nonneg_iff P h₁ h₁' h₂ h₂']
  constructor
  · intro h θ
    have := h (fun p => cexp ((θ p : ℂ) * I) * jasKroneckerPoint (ρ + c) p)
      (fun p => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, norm_jasKroneckerPoint, one_mul])
    simpa only [jasHoloLocal_twisted_eq_jasRotLocal ρ c _ _ (h₁' _) (h₂' _)] using this
  · intro h w hw
    -- write each unit `w p` as a rotation of the Kronecker point
    have hw' : ∀ p, w p = cexp (((w p / jasKroneckerPoint (ρ + c) p).arg : ℂ) * I) *
        jasKroneckerPoint (ρ + c) p := by
      intro p
      have hK : jasKroneckerPoint (ρ + c) p ≠ 0 := by
        rw [jasKroneckerPoint]; exact Complex.exp_ne_zero _
      have hn : ‖w p / jasKroneckerPoint (ρ + c) p‖ = 1 := by
        rw [norm_div, hw, norm_jasKroneckerPoint, div_one]
      have := Complex.norm_mul_exp_arg_mul_I (w p / jasKroneckerPoint (ρ + c) p)
      rw [hn, Complex.ofReal_one, one_mul] at this
      rw [this, div_mul_cancel₀ _ hK]
    have := h (fun p => (w p / jasKroneckerPoint (ρ + c) p).arg)
    rw [Finset.prod_congr rfl fun p _ => by rw [hw' p]]
    simpa only [jasHoloLocal_twisted_eq_jasRotLocal ρ c _ _ (h₁' _) (h₂' _)] using this

end

end RHTower
