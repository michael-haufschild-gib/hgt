import GaloisForLFunctions.RHTower.ConstrainedWeilTwistedOddTest

/-!
# The plateau profile and its exact twisted moments

The odd plateau profile at aperture `a` is `ψ_a(u) = h_a(u) − h_a(−u)` with the bump
`h_a(u) = τ(4u) τ(4(a − u))`, where `τ` is the smooth transition (`0` on `(−∞, 0]`, `1` on
`[1, ∞)`).  Thus `h_a` rises from `0` to `1` on `[0, 1/4]`, equals `1` on `[1/4, a − 1/4]`, and falls
back to `0` on `[a − 1/4, a]`.  Its edge shape does not depend on the aperture, so for `a ≥ 1/2` and
`c ≠ 0` the exponential moment of the bump is an exact exponential polynomial in the aperture:

`∫ e^{cu} h_a(u) du = e^{ca} κ(c) + ρ(c)`,

`κ(c) = ∫_0^{1/4} e^{−cs} τ(4s) ds + e^{−c/4}/c`, `ρ(c) = ∫_0^{1/4} e^{cu} τ(4u) du − e^{c/4}/c`.

Consequently the twisted moment of the profile is
`A(b, μ) = e^{ca} κ(c) + ρ(c) − e^{−ca} κ(−c) − ρ(−c)` with `c = b + iμ`.  This closed form is what
makes the aperture a usable averaging variable for the ray energy of the twisted odd test.
-/

open MeasureTheory Complex Set intervalIntegral

namespace RHTower

noncomputable section

/-! ## The edge and the bump -/

/-- The rising edge `τ(4u)`: `0` for `u ≤ 0`, `1` for `u ≥ 1/4`. -/
def plateauEdge (u : ℝ) : ℝ := Real.smoothTransition (4 * u)

theorem plateauEdge_contDiff : ContDiff ℝ (⊤ : ℕ∞) plateauEdge :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)

theorem plateauEdge_continuous : Continuous plateauEdge := plateauEdge_contDiff.continuous

theorem plateauEdge_eq_zero {u : ℝ} (h : u ≤ 0) : plateauEdge u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem plateauEdge_eq_one {u : ℝ} (h : 1 / 4 ≤ u) : plateauEdge u = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem plateauEdge_nonneg (u : ℝ) : 0 ≤ plateauEdge u := Real.smoothTransition.nonneg _

theorem plateauEdge_le_one (u : ℝ) : plateauEdge u ≤ 1 := Real.smoothTransition.le_one _

/-- The plateau bump `τ(4u) τ(4(a − u))`. -/
def plateauBump (a u : ℝ) : ℝ := plateauEdge u * plateauEdge (a - u)

theorem plateauBump_contDiff (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (plateauBump a) :=
  plateauEdge_contDiff.mul (plateauEdge_contDiff.comp (contDiff_const.sub contDiff_id))

theorem plateauBump_continuous (a : ℝ) : Continuous (plateauBump a) :=
  (plateauBump_contDiff a).continuous

theorem plateauBump_nonneg (a u : ℝ) : 0 ≤ plateauBump a u :=
  mul_nonneg (plateauEdge_nonneg _) (plateauEdge_nonneg _)

theorem plateauBump_le_one (a u : ℝ) : plateauBump a u ≤ 1 :=
  mul_le_one₀ (plateauEdge_le_one _) (plateauEdge_nonneg _) (plateauEdge_le_one _)

theorem plateauBump_eq_zero_of_nonpos {a u : ℝ} (h : u ≤ 0) : plateauBump a u = 0 := by
  unfold plateauBump
  rw [plateauEdge_eq_zero h, zero_mul]

theorem plateauBump_eq_zero_of_ge {a u : ℝ} (h : a ≤ u) : plateauBump a u = 0 := by
  unfold plateauBump
  rw [plateauEdge_eq_zero (by linarith : a - u ≤ 0), mul_zero]

theorem plateauBump_eq_edge_left {a u : ℝ} (h : u ≤ a - 1 / 4) :
    plateauBump a u = plateauEdge u := by
  unfold plateauBump
  rw [plateauEdge_eq_one (by linarith : 1 / 4 ≤ a - u), mul_one]

theorem plateauBump_eq_edge_right {a u : ℝ} (h : 1 / 4 ≤ u) :
    plateauBump a u = plateauEdge (a - u) := by
  unfold plateauBump
  rw [plateauEdge_eq_one h, one_mul]

theorem plateauBump_eq_one {a u : ℝ} (h1 : 1 / 4 ≤ u) (h2 : u ≤ a - 1 / 4) :
    plateauBump a u = 1 := by
  rw [plateauBump_eq_edge_left h2, plateauEdge_eq_one h1]

theorem plateauBump_support_subset (a : ℝ) : Function.support (plateauBump a) ⊆ Icc 0 a := by
  intro u hu
  rw [Function.mem_support] at hu
  rw [mem_Icc]
  constructor
  · by_contra h
    exact hu (plateauBump_eq_zero_of_nonpos (by linarith))
  · by_contra h
    exact hu (plateauBump_eq_zero_of_ge (by linarith))

theorem plateauBump_hasCompactSupport (a : ℝ) : HasCompactSupport (plateauBump a) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (plateauBump_support_subset a)

/-! ## The odd profile -/

/-- The odd plateau profile `h_a(u) − h_a(−u)`. -/
def plateauProfileFun (a u : ℝ) : ℝ := plateauBump a u - plateauBump a (-u)

theorem plateauProfileFun_of_nonneg {a u : ℝ} (h : 0 ≤ u) :
    plateauProfileFun a u = plateauBump a u := by
  unfold plateauProfileFun
  rw [plateauBump_eq_zero_of_nonpos (by linarith : -u ≤ 0), sub_zero]

theorem abs_plateauProfileFun_le_one (a u : ℝ) : |plateauProfileFun a u| ≤ 1 := by
  unfold plateauProfileFun
  rcases le_or_gt 0 u with h | h
  · rw [plateauBump_eq_zero_of_nonpos (by linarith : -u ≤ 0), sub_zero, abs_of_nonneg
      (plateauBump_nonneg _ _)]
    exact plateauBump_le_one _ _
  · rw [plateauBump_eq_zero_of_nonpos h.le, zero_sub, abs_neg, abs_of_nonneg
      (plateauBump_nonneg _ _)]
    exact plateauBump_le_one _ _

/-- The odd plateau profile as an `OddSmoothProfile`. -/
def plateauProfile (a : ℝ) (ha : 0 ≤ a) : OddSmoothProfile a where
  toFun := plateauProfileFun a
  smooth := (plateauBump_contDiff a).sub ((plateauBump_contDiff a).comp contDiff_neg)
  support_subset := by
    intro u hu
    simp only [Function.mem_support] at hu
    rw [mem_Icc]
    by_contra hmem
    apply hu
    unfold plateauProfileFun
    rcases le_or_gt u a with h1 | h1
    · have h2 : u < -a := by
        by_contra h3
        push Not at h3
        exact hmem ⟨h3, h1⟩
      rw [plateauBump_eq_zero_of_nonpos (by linarith), plateauBump_eq_zero_of_ge (by linarith)]
      ring
    · rw [plateauBump_eq_zero_of_ge h1.le, plateauBump_eq_zero_of_nonpos (by linarith)]
      ring
  odd := by
    intro u
    unfold plateauProfileFun
    rw [neg_neg]
    ring

theorem plateauProfile_apply (a : ℝ) (ha : 0 ≤ a) (u : ℝ) :
    (plateauProfile a ha) u = plateauProfileFun a u := rfl

/-! ## Exact exponential moments of the bump -/

/-- `λ₀(c) = ∫_0^{1/4} e^{cu} τ(4u) du`. -/
def plateauLambda₀ (c : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 / 4 : ℝ), Complex.exp (c * (u : ℂ)) * ((plateauEdge u : ℝ) : ℂ)

/-- `λ₁(c) = ∫_0^{1/4} e^{−cs} τ(4s) ds`. -/
def plateauLambda₁ (c : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..(1 / 4 : ℝ), Complex.exp (-(c * (s : ℂ))) * ((plateauEdge s : ℝ) : ℂ)

/-- `κ(c) = λ₁(c) + e^{−c/4}/c`, the coefficient of `e^{ca}` in the bump moment. -/
def plateauKappa (c : ℂ) : ℂ := plateauLambda₁ c + Complex.exp (-(c / 4)) / c

/-- `ρ(c) = λ₀(c) − e^{c/4}/c`, the aperture-independent part of the bump moment. -/
def plateauRho (c : ℂ) : ℂ := plateauLambda₀ c - Complex.exp (c / 4) / c

theorem continuous_exp_mul_plateauBump (a : ℝ) (c : ℂ) :
    Continuous (fun u : ℝ => Complex.exp (c * (u : ℂ)) * ((plateauBump a u : ℝ) : ℂ)) :=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
    (Complex.continuous_ofReal.comp (plateauBump_continuous a))

theorem integrable_exp_mul_plateauBump (a : ℝ) (c : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (c * (u : ℂ)) * ((plateauBump a u : ℝ) : ℂ)) := by
  refine (continuous_exp_mul_plateauBump a c).integrable_of_hasCompactSupport ?_
  refine ((plateauBump_hasCompactSupport a).comp_left Complex.ofReal_zero).mono ?_
  intro u hu
  simp only [Function.mem_support] at hu ⊢
  intro h0
  apply hu
  change ((plateauBump a u : ℝ) : ℂ) = 0 at h0
  rw [h0, mul_zero]

/-- **Exact bump moment.**  For `a ≥ 1/2` and `c ≠ 0`,
`∫ e^{cu} h_a(u) du = e^{ca} κ(c) + ρ(c)`. -/
theorem integral_exp_mul_plateauBump {a : ℝ} (ha : 1 / 2 ≤ a) {c : ℂ} (hc : c ≠ 0) :
    ∫ u : ℝ, Complex.exp (c * (u : ℂ)) * ((plateauBump a u : ℝ) : ℂ)
      = Complex.exp (c * (a : ℂ)) * plateauKappa c + plateauRho c := by
  set f : ℝ → ℂ := fun u => Complex.exp (c * (u : ℂ)) * ((plateauBump a u : ℝ) : ℂ) with hf
  have hcont : Continuous f := continuous_exp_mul_plateauBump a c
  have ha0 : (0 : ℝ) ≤ a := by linarith
  -- restrict to `(0, a]`
  have h1 : ∫ u : ℝ, f u = ∫ u in (0 : ℝ)..a, f u := by
    rw [integral_of_le ha0]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hu
    simp only [hf]
    rcases hu with hu | hu
    · rw [plateauBump_eq_zero_of_nonpos hu, Complex.ofReal_zero, mul_zero]
    · rw [plateauBump_eq_zero_of_ge hu.le, Complex.ofReal_zero, mul_zero]
  -- split at `1/4` and `a − 1/4`
  have hint : ∀ p q : ℝ, IntervalIntegrable f volume p q := fun p q =>
    hcont.intervalIntegrable p q
  have h2 : ∫ u in (0 : ℝ)..a, f u
      = (∫ u in (0 : ℝ)..(1 / 4 : ℝ), f u) + (∫ u in (1 / 4 : ℝ)..(a - 1 / 4), f u)
        + ∫ u in (a - 1 / 4)..a, f u := by
    rw [integral_add_adjacent_intervals (hint _ _) (hint _ _),
      integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  -- the left edge
  have h3 : ∫ u in (0 : ℝ)..(1 / 4 : ℝ), f u = plateauLambda₀ c := by
    unfold plateauLambda₀
    refine integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num), mem_Icc] at hu
    simp only [hf]
    rw [plateauBump_eq_edge_left (by linarith [hu.2])]
  -- the plateau
  have h4 : ∫ u in (1 / 4 : ℝ)..(a - 1 / 4), f u
      = (Complex.exp (c * ((a - 1 / 4 : ℝ) : ℂ)) - Complex.exp (c * ((1 / 4 : ℝ) : ℂ))) / c := by
    rw [← integral_exp_mul_complex hc]
    refine integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith), mem_Icc] at hu
    simp only [hf]
    rw [plateauBump_eq_one hu.1 hu.2, Complex.ofReal_one, mul_one]
  -- the right edge, by the substitution `u = a − s`
  have h5 : ∫ u in (a - 1 / 4)..a, f u = Complex.exp (c * (a : ℂ)) * plateauLambda₁ c := by
    have hcongr : ∫ u in (a - 1 / 4)..a, f u
        = ∫ u in (a - 1 / 4)..a,
            (fun s : ℝ => Complex.exp (c * ((a - s : ℝ) : ℂ)) * ((plateauEdge s : ℝ) : ℂ)) (a - u) := by
      refine integral_congr fun u hu => ?_
      rw [uIcc_of_le (by linarith), mem_Icc] at hu
      simp only [hf]
      rw [plateauBump_eq_edge_right (by linarith [hu.1])]
      congr 2
      push_cast
      ring
    rw [hcongr, integral_comp_sub_left (fun s : ℝ =>
      Complex.exp (c * ((a - s : ℝ) : ℂ)) * ((plateauEdge s : ℝ) : ℂ)) a, sub_self,
      sub_sub_cancel]
    unfold plateauLambda₁
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun s _ => ?_
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h1, h2, h3, h4, h5]
  unfold plateauKappa plateauRho
  have e1 : Complex.exp (c * ((a - 1 / 4 : ℝ) : ℂ))
      = Complex.exp (c * (a : ℂ)) * Complex.exp (-(c / 4)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : Complex.exp (c * ((1 / 4 : ℝ) : ℂ)) = Complex.exp (c / 4) := by
    congr 1
    push_cast
    ring
  rw [e1, e2]
  field_simp
  ring

/-- The bump moment of the reflected argument is the moment at `−c`. -/
theorem integral_exp_mul_plateauBump_neg (a : ℝ) (c : ℂ) :
    ∫ u : ℝ, Complex.exp (c * (u : ℂ)) * ((plateauBump a (-u) : ℝ) : ℂ)
      = ∫ u : ℝ, Complex.exp (-c * (u : ℂ)) * ((plateauBump a u : ℝ) : ℂ) := by
  rw [← integral_neg_eq_self (fun u : ℝ => Complex.exp (-c * (u : ℂ)) * ((plateauBump a u : ℝ) : ℂ))
    volume]
  congr 1
  funext u
  show Complex.exp (c * (u : ℂ)) * ((plateauBump a (-u) : ℝ) : ℂ)
    = Complex.exp (-c * ((-u : ℝ) : ℂ)) * ((plateauBump a (-u) : ℝ) : ℂ)
  congr 2
  push_cast
  ring

/-- **Exact twisted moment of the plateau profile.**  For `a ≥ 1/2` and `c = b + iμ ≠ 0`,
`A(b, μ) = e^{ca} κ(c) + ρ(c) − e^{−ca} κ(−c) − ρ(−c)`. -/
theorem twistedMoment_plateauProfile {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) {b μ : ℝ}
    (hc : (b : ℂ) + I * (μ : ℂ) ≠ 0) :
    twistedMoment (plateauProfile a ha0) b μ
      = (Complex.exp (((b : ℂ) + I * (μ : ℂ)) * (a : ℂ)) * plateauKappa ((b : ℂ) + I * (μ : ℂ))
          + plateauRho ((b : ℂ) + I * (μ : ℂ)))
        - (Complex.exp (-((b : ℂ) + I * (μ : ℂ)) * (a : ℂ)) * plateauKappa (-((b : ℂ) + I * (μ : ℂ)))
          + plateauRho (-((b : ℂ) + I * (μ : ℂ)))) := by
  unfold twistedMoment
  set c : ℂ := (b : ℂ) + I * (μ : ℂ) with hcdef
  have hsplit : ∀ u : ℝ, Complex.exp (c * (u : ℂ)) * (((plateauProfile a ha0) u : ℝ) : ℂ)
      = Complex.exp (c * (u : ℂ)) * ((plateauBump a u : ℝ) : ℂ)
        - Complex.exp (c * (u : ℂ)) * ((plateauBump a (-u) : ℝ) : ℂ) := by
    intro u
    rw [plateauProfile_apply]
    unfold plateauProfileFun
    push_cast
    ring
  simp_rw [hsplit]
  rw [integral_sub (integrable_exp_mul_plateauBump a c) ?_, integral_exp_mul_plateauBump ha hc,
    integral_exp_mul_plateauBump_neg, integral_exp_mul_plateauBump ha (neg_ne_zero.mpr hc)]
  have hint := (integrable_exp_mul_plateauBump a (-c)).comp_neg
  refine hint.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Complex.ofReal_neg]
  congr 2
  ring

end

end RHTower
