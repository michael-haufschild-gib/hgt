import GaloisForLFunctions.HTGeometry.HalfPlanePoissonBoundedReproduction
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheAveragedStateDecaysAtTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateIsTheCauchyTransformOfItsZeroValues

/-!
# The Cauchy transform of the zero values is square-integrable up to a logarithm

For square-summable coefficients `c_z` on the centred zeros `z = ρ - 1/2` (with multiplicity) and
a line `Re p = σ` to the right of all of them, `δ ≤ σ - Re z ≤ D` with `δ ≤ 1 ≤ D`,

  `∫ |Σ_z c_z/(σ + it - z)|² dt / log(|t| + 4) ≤ (160 π D (|C₀| + 2)/δ) Σ_z |c_z|²`.

No separation of the zeros is used. The only arithmetic input is the unit-window count
`Σ_z 1/(1 + (t - Im z)²) ≤ 8 (C₀ + log(|t| + 4))`, and the logarithm in the weight is that count:
coefficients carried by a cluster of `N` zeros lose a factor of order `N`.

For the critical state, whose transform continues as `-(1/a) Σ_z L F(z)/(w + 8 - z)` with
square-summable zero values, this gives on every line to the right of the transported zeros

  `∫ |L F(σ - 8 + it)|² dt / log(|t| + 4) ≤ (K/a²) Σ_z |L F(z)|²`.

The square-integrability on the line `Re w = -b/2` that a decay law `∫ F² e^{-bu} du < ∞` gives by
Plancherel therefore holds up to one logarithm at every `b = 16 - 2σ` down to the abscissa of the
zeros; unconditionally for `σ > 8999/24000`.

Mechanism: self-duality against an analytic weight. `Λ(p) = log(p - σ + 4)` is holomorphic on
`Re p ≥ σ` with real part `log |4 + it|` on the line and bounded argument. For a finite Cauchy sum
`C` put `h = C/Λ` and `X = ∫ |C|² Re(1/Λ) = Re ∫ conj(C) h`. Each term of `conj(C)` is the
conjugate Cauchy kernel of a zero, which evaluates `h` at the reflected zero `z* = 2σ - conj z`, so
`∫ conj(C) h = 2π Σ_z conj(c_z) h(z*)`. The values `h(z*)` are Poisson averages of `h` on the line;
by Jensen's inequality and the unit-window count `Σ_z |h(z*)|² ≲ ∫ (C₀ + log) |C|²/|Λ|² ≲ X`.
Cauchy–Schwarz gives `X² ≲ (Σ |c_z|²) X`, and Fatou's lemma passes to square-summable coefficients.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The Poisson kernel at depth `d` -/

theorem halfPlanePoisson_neg_mul {d : ℝ} (hd : 0 < d) (x : ℝ) :
    halfPlanePoisson d (-d * x) = d⁻¹ * halfPlanePoisson 1 x := by
  have e : d ^ (2 : ℕ) + (-d * x) ^ (2 : ℕ) = d ^ (2 : ℕ) * (1 ^ (2 : ℕ) + x ^ (2 : ℕ)) := by ring
  unfold halfPlanePoisson
  rw [e, inv_mul_eq_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- For depths `δ ≤ d ≤ D` the Poisson kernel is dominated by the unit Lorentzian. -/
theorem halfPlanePoisson_le_lorentz_of_le {d δ D : ℝ} (hδ : 0 < δ) (hδd : δ ≤ d) (hdD : d ≤ D)
    (hδ1 : δ ≤ 1) (hD1 : 1 ≤ D) (τ : ℝ) :
    halfPlanePoisson d τ ≤ D / (δ * Real.pi) * (1 + τ ^ 2)⁻¹ := by
  have hd0 : 0 < d := hδ.trans_le hδd
  have hπ := Real.pi_pos
  have h1 : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  have hD : (0 : ℝ) < d ^ (2 : ℕ) + τ ^ (2 : ℕ) := by positivity
  have h2 : d * δ ≤ d ^ (2 : ℕ) := by nlinarith
  have h3 : d ^ (2 : ℕ) ≤ D * d ^ (2 : ℕ) := by nlinarith [sq_nonneg d]
  have h4 : d * δ ≤ D := by nlinarith
  have key : d * δ * (1 + τ ^ 2) ≤ D * (d ^ (2 : ℕ) + τ ^ (2 : ℕ)) := by
    nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg τ)]
  unfold halfPlanePoisson
  rw [← div_eq_mul_inv, div_div, div_le_div_iff₀ (mul_pos hπ hD) (mul_pos (mul_pos hδ hπ) h1)]
  have := mul_le_mul_of_nonneg_left key hπ.le
  linarith

theorem pi_div_mul_halfPlanePoisson {d : ℝ} (hd : 0 < d) (τ : ℝ) :
    Real.pi / d * halfPlanePoisson d τ = (d ^ 2 + τ ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < d ^ 2 + τ ^ 2 := by positivity
  unfold halfPlanePoisson
  rw [div_mul_div_comm, inv_eq_one_div, div_eq_div_iff (by positivity) hpos.ne']
  ring

/-- `P_d(τ) (d + iτ) = (d/π) conj (1/(d + iτ))`: the Poisson kernel is the Cauchy kernel of the
reflected point. -/
theorem ofReal_halfPlanePoisson_mul_eq {d : ℝ} (hd : 0 < d) (τ : ℝ) :
    ((halfPlanePoisson d τ : ℝ) : ℂ) * ((d : ℂ) + (τ : ℂ) * I) =
      ((d / Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (((d : ℂ) + (τ : ℂ) * I)⁻¹) := by
  have hu : (d : ℂ) + (τ : ℂ) * I ≠ 0 := fun h => by
    have h1 := congrArg Complex.re h
    simp at h1
    exact hd.ne' h1
  have hcu : (starRingEnd ℂ) ((d : ℂ) + (τ : ℂ) * I) ≠ 0 := (map_ne_zero _).mpr hu
  have hpos : (0 : ℝ) < d ^ 2 + τ ^ 2 := by positivity
  have hP : halfPlanePoisson d τ * (d ^ 2 + τ ^ 2) = d / Real.pi := by
    unfold halfPlanePoisson
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hpos.ne']
  rw [map_inv₀, eq_mul_inv_iff_mul_eq₀ hcu, mul_assoc, Complex.mul_conj, Complex.normSq_add_mul_I,
    ← Complex.ofReal_mul, hP]

/-! ### Bounded holomorphic functions on a right half-plane -/

theorem continuous_comp_verticalLine {g : ℂ → ℂ} {σ : ℝ}
    (hdiff : ∀ p : ℂ, σ ≤ p.re → DifferentiableAt ℂ g p) :
    Continuous fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * I) :=
  continuous_iff_continuousAt.mpr fun t =>
    ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (hdiff _ (by simp)).continuousAt (by fun_prop)

/-- **Poisson reproduction on a right half-plane.** A function holomorphic and bounded on
`Re p ≥ σ` is the Poisson average of its values on the line `Re p = σ`. -/
theorem integral_halfPlanePoisson_mul_eq_apply {g : ℂ → ℂ} {σ M : ℝ}
    (hdiff : ∀ p : ℂ, σ ≤ p.re → DifferentiableAt ℂ g p)
    (hbd : ∀ p : ℂ, σ ≤ p.re → ‖g p‖ ≤ M) {d : ℝ} (hd : 0 < d) (γ : ℝ) :
    (∫ t : ℝ, ((halfPlanePoisson d (t - γ) : ℝ) : ℂ) * g ((σ : ℂ) + (t : ℂ) * I)) =
      g ((σ : ℂ) + (d : ℂ) + (γ : ℂ) * I) := by
  -- the rotation `z ↦ σ + iγ - i d z` carries the upper half-plane onto `Re p ≥ σ`
  have hre : ∀ z : ℂ, ((σ : ℂ) + (γ : ℂ) * I - I * (d : ℂ) * z).re = σ + d * z.im := fun z => by
    rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re,
      mul_zero, add_zero, mul_assoc, Complex.I_mul_re, Complex.im_ofReal_mul]
    ring
  have hmem : ∀ z : ℂ, 0 ≤ z.im → σ ≤ ((σ : ℂ) + (γ : ℂ) * I - I * (d : ℂ) * z).re :=
    fun z hz => by
      rw [hre]
      linarith [mul_nonneg hd.le hz]
  have h : (∫ x : ℝ, ((halfPlanePoisson 1 x : ℝ) : ℂ) *
      g ((σ : ℂ) + (γ : ℂ) * I - I * (d : ℂ) * (x : ℂ))) =
      g ((σ : ℂ) + (γ : ℂ) * I - I * (d : ℂ) * I) :=
    integral_halfPlanePoisson_one_mul_eq_apply_I
      (F := fun z => g ((σ : ℂ) + (γ : ℂ) * I - I * (d : ℂ) * z)) (M := M)
      (fun z hz => (hdiff _ (hmem z hz)).comp z (by fun_prop)) (fun z hz => hbd _ (hmem z hz))
  have hI : (σ : ℂ) + (γ : ℂ) * I - I * (d : ℂ) * I = (σ : ℂ) + (d : ℂ) + (γ : ℂ) * I := by
    linear_combination (-(d : ℂ)) * Complex.I_mul_I
  -- substitute `t = γ - d x`
  have e1 : (∫ t : ℝ, ((halfPlanePoisson d (t - γ) : ℝ) : ℂ) * g ((σ : ℂ) + (t : ℂ) * I)) =
      ∫ y : ℝ, ((halfPlanePoisson d y : ℝ) : ℂ) * g ((σ : ℂ) + ((y + γ : ℝ) : ℂ) * I) := by
    rw [← integral_sub_right_eq_self
      (fun y : ℝ => ((halfPlanePoisson d y : ℝ) : ℂ) * g ((σ : ℂ) + ((y + γ : ℝ) : ℂ) * I)) γ]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show _ = ((halfPlanePoisson d (t - γ) : ℝ) : ℂ) * g ((σ : ℂ) + ((t - γ + γ : ℝ) : ℂ) * I)
    rw [sub_add_cancel]
  have e2 : (∫ x : ℝ, ((halfPlanePoisson d (-d * x) : ℝ) : ℂ) *
      g ((σ : ℂ) + ((-d * x + γ : ℝ) : ℂ) * I)) =
      |(-d)⁻¹| • ∫ y : ℝ, ((halfPlanePoisson d y : ℝ) : ℂ) *
        g ((σ : ℂ) + ((y + γ : ℝ) : ℂ) * I) :=
    Measure.integral_comp_mul_left
      (fun y : ℝ => ((halfPlanePoisson d y : ℝ) : ℂ) * g ((σ : ℂ) + ((y + γ : ℝ) : ℂ) * I)) (-d)
  have e3 : ∀ x : ℝ, ((halfPlanePoisson d (-d * x) : ℝ) : ℂ) *
      g ((σ : ℂ) + ((-d * x + γ : ℝ) : ℂ) * I) =
      ((d⁻¹ : ℝ) : ℂ) * (((halfPlanePoisson 1 x : ℝ) : ℂ) *
        g ((σ : ℂ) + (γ : ℂ) * I - I * (d : ℂ) * (x : ℂ))) := fun x => by
    have hpt : (σ : ℂ) + ((-d * x + γ : ℝ) : ℂ) * I =
        (σ : ℂ) + (γ : ℂ) * I - I * (d : ℂ) * (x : ℂ) := by
      push_cast
      ring
    rw [halfPlanePoisson_neg_mul hd, Complex.ofReal_mul, hpt, mul_assoc]
  have habs : |(-d)⁻¹| = d⁻¹ := by rw [abs_inv, abs_neg, abs_of_pos hd]
  simp only [e3] at e2
  rw [integral_const_mul, h, habs, Complex.real_smul] at e2
  rw [e1, ← mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hd.ne')) e2, hI]

/-- Jensen's inequality for the Poisson average on a right half-plane. -/
theorem norm_sq_apply_le_integral_halfPlanePoisson {g : ℂ → ℂ} {σ M : ℝ}
    (hdiff : ∀ p : ℂ, σ ≤ p.re → DifferentiableAt ℂ g p)
    (hbd : ∀ p : ℂ, σ ≤ p.re → ‖g p‖ ≤ M) {d : ℝ} (hd : 0 < d) (γ : ℝ) :
    ‖g ((σ : ℂ) + (d : ℂ) + (γ : ℂ) * I)‖ ^ 2 ≤
      ∫ t : ℝ, halfPlanePoisson d (t - γ) * ‖g ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  rw [← integral_halfPlanePoisson_mul_eq_apply hdiff hbd hd γ]
  have hgc := continuous_comp_verticalLine hdiff
  have hP : Integrable fun t : ℝ => halfPlanePoisson d (t - γ) :=
    (integrable_halfPlanePoisson hd).comp_sub_right γ
  have hP0 : ∀ t : ℝ, 0 ≤ halfPlanePoisson d (t - γ) := fun t => (halfPlanePoisson_pos hd _).le
  have hP1 : (∫ t : ℝ, halfPlanePoisson d (t - γ)) = 1 :=
    (integral_sub_right_eq_self (halfPlanePoisson d) γ).trans (integral_halfPlanePoisson hd)
  have hwg2 : Integrable fun t : ℝ =>
      halfPlanePoisson d (t - γ) * ‖g ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine (hP.mul_const (M ^ 2)).mono'
      (hP.aestronglyMeasurable.mul (hgc.norm.pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hP0 t) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbd _ (by simp)) 2) (hP0 t)
  have h1 : ‖∫ t : ℝ, ((halfPlanePoisson d (t - γ) : ℝ) : ℂ) * g ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      ∫ t : ℝ, halfPlanePoisson d (t - γ) * ‖g ((σ : ℂ) + (t : ℂ) * I)‖ := by
    refine (norm_integral_le_integral_norm _).trans
      (le_of_eq (integral_congr_ae (Eventually.of_forall fun t => ?_)))
    show ‖((halfPlanePoisson d (t - γ) : ℝ) : ℂ) * g ((σ : ℂ) + (t : ℂ) * I)‖ =
      halfPlanePoisson d (t - γ) * ‖g ((σ : ℂ) + (t : ℂ) * I)‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP0 t)]
  have h2 := sq_integral_weighted_le (μ := volume) (w := fun t : ℝ => halfPlanePoisson d (t - γ))
    (g := fun t => ‖g ((σ : ℂ) + (t : ℂ) * I)‖) hP0 hP.aestronglyMeasurable
    hgc.norm.aestronglyMeasurable hP hwg2
  rw [hP1, one_mul] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- A function with `h(p) (p - z)` bounded on `Re p ≥ σ` is integrable on the line against the
conjugate Cauchy kernel of a point `z` to its left. -/
theorem integrable_conj_inv_mul {h : ℂ → ℂ} {σ M : ℝ}
    (hdiff : ∀ p : ℂ, σ ≤ p.re → DifferentiableAt ℂ h p) {z : ℂ} (hz : z.re < σ)
    (hbd : ∀ p : ℂ, σ ≤ p.re → ‖h p * (p - z)‖ ≤ M) :
    Integrable fun t : ℝ =>
      (starRingEnd ℂ) (((σ : ℂ) + (t : ℂ) * I - z)⁻¹) * h ((σ : ℂ) + (t : ℂ) * I) := by
  have hd : 0 < σ - z.re := sub_pos.mpr hz
  have hu : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * I - z =
      ((σ - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I := fun t => by
    push_cast
    linear_combination Complex.re_add_im z
  have hne : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * I - z ≠ 0 := fun t h0 => by
    have h1 := congrArg Complex.re h0
    rw [hu t] at h1
    simp at h1
    linarith
  have hsq : ∀ t : ℝ, ‖((σ : ℂ) + (t : ℂ) * I - z)⁻¹‖ ^ 2 =
      Real.pi / (σ - z.re) * halfPlanePoisson (σ - z.re) (t - z.im) := fun t => by
    rw [hu t, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_add_mul_I,
      pi_div_mul_halfPlanePoisson hd]
  have hcont : Continuous fun t : ℝ =>
      (starRingEnd ℂ) (((σ : ℂ) + (t : ℂ) * I - z)⁻¹) * h ((σ : ℂ) + (t : ℂ) * I) :=
    (Complex.continuous_conj.comp (Continuous.inv₀ (by fun_prop) hne)).mul
      (continuous_comp_verticalLine hdiff)
  refine ((((integrable_halfPlanePoisson hd).comp_sub_right z.im).const_mul
    (Real.pi / (σ - z.re))).const_mul M).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hh : ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M * ‖((σ : ℂ) + (t : ℂ) * I - z)⁻¹‖ := by
    calc ‖h ((σ : ℂ) + (t : ℂ) * I)‖
        = ‖h ((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I - z)‖ *
            ‖((σ : ℂ) + (t : ℂ) * I - z)⁻¹‖ := by
          rw [← norm_mul, mul_assoc, mul_inv_cancel₀ (hne t), mul_one]
      _ ≤ M * ‖((σ : ℂ) + (t : ℂ) * I - z)⁻¹‖ :=
          mul_le_mul_of_nonneg_right (hbd _ (by simp)) (norm_nonneg _)
  rw [norm_mul, RCLike.norm_conj]
  calc ‖((σ : ℂ) + (t : ℂ) * I - z)⁻¹‖ * ‖h ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ‖((σ : ℂ) + (t : ℂ) * I - z)⁻¹‖ * (M * ‖((σ : ℂ) + (t : ℂ) * I - z)⁻¹‖) :=
        mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = M * ‖((σ : ℂ) + (t : ℂ) * I - z)⁻¹‖ ^ 2 := by ring
    _ = M * (Real.pi / (σ - z.re) * halfPlanePoisson (σ - z.re) (t - z.im)) := by rw [hsq t]

/-- **The Cauchy formula of the reflected point.** For `h` holomorphic on `Re p ≥ σ` with
`h(p) (p - z)` bounded and `z` to the left of the line, the conjugate Cauchy kernel of `z`
evaluates `h` at the reflection `2σ - conj z`. -/
theorem integral_conj_inv_mul_eq {h : ℂ → ℂ} {σ M : ℝ}
    (hdiff : ∀ p : ℂ, σ ≤ p.re → DifferentiableAt ℂ h p) {z : ℂ} (hz : z.re < σ)
    (hbd : ∀ p : ℂ, σ ≤ p.re → ‖h p * (p - z)‖ ≤ M) :
    (∫ t : ℝ, (starRingEnd ℂ) (((σ : ℂ) + (t : ℂ) * I - z)⁻¹) * h ((σ : ℂ) + (t : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        h ((σ : ℂ) + ((σ - z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I) := by
  have hd : 0 < σ - z.re := sub_pos.mpr hz
  have hu : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * I - z =
      ((σ - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I := fun t => by
    push_cast
    linear_combination Complex.re_add_im z
  have hP : (∫ t : ℝ, ((halfPlanePoisson (σ - z.re) (t - z.im) : ℝ) : ℂ) *
      (h ((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I - z))) =
      h ((σ : ℂ) + ((σ - z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I) *
        ((σ : ℂ) + ((σ - z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I - z) :=
    integral_halfPlanePoisson_mul_eq_apply (g := fun p => h p * (p - z)) (σ := σ) (M := M)
      (fun p hp => (hdiff p hp).mul (by fun_prop)) hbd hd z.im
  have e : ∀ t : ℝ, ((halfPlanePoisson (σ - z.re) (t - z.im) : ℝ) : ℂ) *
      (h ((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I - z)) =
      (((σ - z.re) / Real.pi : ℝ) : ℂ) *
        ((starRingEnd ℂ) (((σ : ℂ) + (t : ℂ) * I - z)⁻¹) * h ((σ : ℂ) + (t : ℂ) * I)) :=
    fun t => by
      rw [hu t]
      calc ((halfPlanePoisson (σ - z.re) (t - z.im) : ℝ) : ℂ) * (h ((σ : ℂ) + (t : ℂ) * I) *
            (((σ - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I))
          = (((halfPlanePoisson (σ - z.re) (t - z.im) : ℝ) : ℂ) *
              (((σ - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I)) *
                h ((σ : ℂ) + (t : ℂ) * I) := by ring
        _ = _ := by rw [ofReal_halfPlanePoisson_mul_eq hd, mul_assoc]
  have hpt : (σ : ℂ) + ((σ - z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I - z =
      ((2 * (σ - z.re) : ℝ) : ℂ) := by
    push_cast
    linear_combination Complex.re_add_im z
  simp only [e] at hP
  rw [integral_const_mul, hpt] at hP
  have hne : (((σ - z.re) / Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero hd.ne' Real.pi_ne_zero)
  have e3 : (σ - z.re) / Real.pi * (2 * Real.pi) = 2 * (σ - z.re) := by
    rw [div_mul_eq_mul_div, div_eq_iff Real.pi_ne_zero]
    ring
  have e2 : (((σ - z.re) / Real.pi : ℝ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) *
      h ((σ : ℂ) + ((σ - z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I)) =
      h ((σ : ℂ) + ((σ - z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I) *
        ((2 * (σ - z.re) : ℝ) : ℂ) := by
    rw [← mul_assoc, ← Complex.ofReal_mul, e3, mul_comm]
  exact mul_left_cancel₀ hne (hP.trans e2.symm)

/-! ### The analytic logarithmic weight -/

/-- The analytic logarithmic weight of the half-plane `Re p ≥ σ`: on the line `Re p = σ` its
real part is `log |4 + it|`. -/
def lineLogWeight (σ : ℝ) (p : ℂ) : ℂ := Complex.log (p - (σ : ℂ) + 4)

theorem four_le_re_sub_add {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) : 4 ≤ (p - (σ : ℂ) + 4).re := by
  have e : (p - (σ : ℂ) + 4).re = p.re - σ + 4 := by simp
  rw [e]
  linarith

theorem differentiableAt_lineLogWeight {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) :
    DifferentiableAt ℂ (lineLogWeight σ) p := by
  have h4 := four_le_re_sub_add hp
  have hd : DifferentiableAt ℂ (fun p : ℂ => p - (σ : ℂ) + 4) p := by fun_prop
  exact hd.clog (Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith)))

theorem one_le_re_lineLogWeight {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) :
    1 ≤ (lineLogWeight σ p).re := by
  have hn : 4 ≤ ‖p - (σ : ℂ) + 4‖ := (four_le_re_sub_add hp).trans (Complex.re_le_norm _)
  unfold lineLogWeight
  rw [Complex.log_re, Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem abs_im_lineLogWeight_le {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) :
    |(lineLogWeight σ p).im| ≤ 2 := by
  have h4 := four_le_re_sub_add hp
  have h := Complex.abs_arg_le_pi_div_two_iff.mpr (by linarith : 0 ≤ (p - (σ : ℂ) + 4).re)
  have := Real.pi_le_four
  unfold lineLogWeight
  rw [Complex.log_im]
  linarith

theorem lineLogWeight_ne_zero {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) : lineLogWeight σ p ≠ 0 := by
  intro h
  have h1 := one_le_re_lineLogWeight hp
  rw [h, Complex.zero_re] at h1
  linarith

/-- The argument of the weight is bounded, so its modulus is comparable to its real part. -/
theorem normSq_lineLogWeight_le {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) :
    Complex.normSq (lineLogWeight σ p) ≤ 5 * (lineLogWeight σ p).re ^ 2 := by
  have h1 := one_le_re_lineLogWeight hp
  have h2 := abs_le.mp (abs_im_lineLogWeight_le hp)
  rw [Complex.normSq_apply]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - (lineLogWeight σ p).im)
    (by linarith : (0 : ℝ) ≤ 2 + (lineLogWeight σ p).im)]

theorem norm_inv_lineLogWeight_le_one {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) :
    ‖(lineLogWeight σ p)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ ((one_le_re_lineLogWeight hp).trans (Complex.re_le_norm _))

/-- `L |1/Λ|² ≤ K Re (1/Λ)` as soon as `L ≤ K Re Λ`. -/
theorem mul_norm_sq_inv_lineLogWeight_le {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) {L K : ℝ}
    (hL : L ≤ K * (lineLogWeight σ p).re) :
    L * ‖(lineLogWeight σ p)⁻¹‖ ^ 2 ≤ K * ((lineLogWeight σ p)⁻¹).re := by
  have hN : 0 < Complex.normSq (lineLogWeight σ p) :=
    Complex.normSq_pos.mpr (lineLogWeight_ne_zero hp)
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.inv_re, ← div_eq_mul_inv, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hL hN.le

/-- The density `Re (1/Λ)` is at least `1/(5 Re Λ)`. -/
theorem inv_le_re_inv_lineLogWeight {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) :
    (5 * (lineLogWeight σ p).re)⁻¹ ≤ ((lineLogWeight σ p)⁻¹).re := by
  have h1 := one_le_re_lineLogWeight hp
  have hN : 0 < Complex.normSq (lineLogWeight σ p) :=
    Complex.normSq_pos.mpr (lineLogWeight_ne_zero hp)
  have h5 := normSq_lineLogWeight_le hp
  rw [Complex.inv_re, inv_eq_one_div, div_le_div_iff₀ (by linarith) hN]
  nlinarith

theorem re_inv_lineLogWeight_nonneg {σ : ℝ} {p : ℂ} (hp : σ ≤ p.re) :
    0 ≤ ((lineLogWeight σ p)⁻¹).re :=
  (inv_nonneg.mpr (by linarith [one_le_re_lineLogWeight hp])).trans
    (inv_le_re_inv_lineLogWeight hp)

theorem lineLogWeight_line (σ t : ℝ) :
    lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I) = Complex.log ((4 : ℂ) + (t : ℂ) * I) := by
  unfold lineLogWeight
  congr 1
  ring

theorem re_lineLogWeight_line_le (σ t : ℝ) :
    (lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I)).re ≤ Real.log (|t| + 4) := by
  have h1 : 1 ≤ (lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I)).re := one_le_re_lineLogWeight (by simp)
  rw [lineLogWeight_line, Complex.log_re] at h1 ⊢
  have h4n : ‖(4 : ℂ)‖ = 4 := by simp
  have htn : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hle := norm_add_le (4 : ℂ) ((t : ℂ) * I)
  rw [h4n, htn] at hle
  have hpos : 0 < ‖(4 : ℂ) + (t : ℂ) * I‖ := by
    by_contra hneg
    have h0 : ‖(4 : ℂ) + (t : ℂ) * I‖ = 0 := le_antisymm (not_lt.mp hneg) (norm_nonneg _)
    rw [h0, Real.log_zero] at h1
    linarith
  exact Real.log_le_log hpos (by linarith)

theorem log_le_one_add_re_lineLogWeight_line (σ t : ℝ) :
    Real.log (|t| + 4) ≤ 1 + (lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I)).re := by
  rw [lineLogWeight_line, Complex.log_re]
  have hre : ((4 : ℂ) + (t : ℂ) * I).re = 4 := by simp
  have him : ((4 : ℂ) + (t : ℂ) * I).im = t := by simp
  have h1 := Complex.re_le_norm ((4 : ℂ) + (t : ℂ) * I)
  have h2 := Complex.abs_im_le_norm ((4 : ℂ) + (t : ℂ) * I)
  rw [hre] at h1
  rw [him] at h2
  have hpos : (0 : ℝ) < ‖(4 : ℂ) + (t : ℂ) * I‖ := by linarith
  have h3 : Real.log (|t| + 4) ≤ Real.log (2 * ‖(4 : ℂ) + (t : ℂ) * I‖) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) hpos.ne'] at h3
  have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- On the line the weight dominates every `C + log(|t| + 4)`. -/
theorem const_add_log_le_mul_re_lineLogWeight_line (C σ t : ℝ) :
    C + Real.log (|t| + 4) ≤ (|C| + 2) * (lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I)).re := by
  have h1 := log_le_one_add_re_lineLogWeight_line σ t
  have h2 : 1 ≤ (lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I)).re := one_le_re_lineLogWeight (by simp)
  have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
  linarith [le_abs_self C]

/-- On the line the density `Re (1/Λ)` is at least `1/(5 log(|t| + 4))`. -/
theorem inv_log_le_re_inv_lineLogWeight_line (σ t : ℝ) :
    (Real.log (|t| + 4))⁻¹ ≤ 5 * ((lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I))⁻¹).re := by
  have hp : σ ≤ ((σ : ℂ) + (t : ℂ) * I).re := by simp
  have h1 := one_le_re_lineLogWeight hp
  have h2 := inv_le_re_inv_lineLogWeight hp
  have h3 : (Real.log (|t| + 4))⁻¹ ≤ ((lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I)).re)⁻¹ :=
    inv_anti₀ (by linarith) (re_lineLogWeight_line_le σ t)
  have h4 : ((lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I)).re)⁻¹ =
      5 * (5 * (lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I)).re)⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (5 : ℝ) ≠ 0), one_mul]
  linarith

/-! ### Finite Cauchy sums over the zeros -/

theorem le_norm_sub_of_re {z p : ℂ} {σ δ : ℝ} (h : δ ≤ σ - z.re) (hp : σ ≤ p.re) :
    δ ≤ ‖p - z‖ := by
  have h1 := Complex.re_le_norm (p - z)
  rw [Complex.sub_re] at h1
  linarith

theorem norm_inv_sub_mul_sub_le {p z z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ) (h : δ ≤ ‖p - z‖) :
    ‖(p - z)⁻¹ * (p - z₀)‖ ≤ 1 + ‖z - z₀‖ * δ⁻¹ := by
  have hne : p - z ≠ 0 := norm_pos_iff.mp (hδ.trans_le h)
  have e : (p - z)⁻¹ * (p - z₀) = 1 + (z - z₀) * (p - z)⁻¹ := by
    have e1 : p - z₀ = (p - z) + (z - z₀) := by ring
    rw [e1, mul_add, inv_mul_cancel₀ hne, mul_comm]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, norm_inv]
  linarith [mul_le_mul_of_nonneg_left (inv_anti₀ hδ h) (norm_nonneg (z - z₀))]

/-- The Cauchy sum of finitely many zero terms. -/
def zeroCauchySum (c : XiZeroCopy → ℂ) (S : Finset XiZeroCopy) (p : ℂ) : ℂ :=
  ∑ q ∈ S, c q * (p - centredZero q)⁻¹

/-- The Cauchy sum divided by the analytic logarithmic weight. -/
def weightedCauchySum (σ : ℝ) (c : XiZeroCopy → ℂ) (S : Finset XiZeroCopy) (p : ℂ) : ℂ :=
  zeroCauchySum c S p * (lineLogWeight σ p)⁻¹

/-- The reflection of a centred zero in the line `Re p = σ`. -/
def reflectedZero (σ : ℝ) (q : XiZeroCopy) : ℂ :=
  (σ : ℂ) + ((σ - (centredZero q).re : ℝ) : ℂ) + (((centredZero q).im : ℝ) : ℂ) * I

/-- The pairing of the Cauchy sum with its weighted copy on the line `Re p = σ`. -/
def linePairing (σ : ℝ) (c : XiZeroCopy → ℂ) (S : Finset XiZeroCopy) (t : ℝ) : ℂ :=
  (starRingEnd ℂ) (zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)) *
    weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)

section FiniteSums

variable {σ δ : ℝ} (hδ : 0 < δ) (hlo : ∀ q : XiZeroCopy, δ ≤ σ - (centredZero q).re)
  (c : XiZeroCopy → ℂ) (S : Finset XiZeroCopy)
include hδ hlo

theorem differentiableAt_zeroCauchySum {p : ℂ} (hp : σ ≤ p.re) :
    DifferentiableAt ℂ (zeroCauchySum c S) p := by
  unfold zeroCauchySum
  refine DifferentiableAt.fun_sum fun q _ => ?_
  have hne : p - centredZero q ≠ 0 :=
    norm_pos_iff.mp (hδ.trans_le (le_norm_sub_of_re (hlo q) hp))
  have h1 : DifferentiableAt ℂ (fun y : ℂ => y - centredZero q) p := by fun_prop
  exact (differentiableAt_const _).mul (h1.inv hne)

theorem norm_zeroCauchySum_le {p : ℂ} (hp : σ ≤ p.re) :
    ‖zeroCauchySum c S p‖ ≤ (∑ q ∈ S, ‖c q‖) * δ⁻¹ := by
  rw [zeroCauchySum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, norm_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hδ (le_norm_sub_of_re (hlo q) hp)) (norm_nonneg _)

theorem norm_zeroCauchySum_mul_sub_le {p : ℂ} (hp : σ ≤ p.re) (z₀ : ℂ) :
    ‖zeroCauchySum c S p * (p - z₀)‖ ≤
      ∑ q ∈ S, ‖c q‖ * (1 + ‖centredZero q - z₀‖ * δ⁻¹) := by
  rw [zeroCauchySum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_inv_sub_mul_sub_le hδ (le_norm_sub_of_re (hlo q) hp)) (norm_nonneg _)

theorem differentiableAt_weightedCauchySum {p : ℂ} (hp : σ ≤ p.re) :
    DifferentiableAt ℂ (weightedCauchySum σ c S) p := by
  unfold weightedCauchySum
  exact (differentiableAt_zeroCauchySum hδ hlo c S hp).mul
    ((differentiableAt_lineLogWeight hp).inv (lineLogWeight_ne_zero hp))

theorem norm_weightedCauchySum_le {p : ℂ} (hp : σ ≤ p.re) :
    ‖weightedCauchySum σ c S p‖ ≤ (∑ q ∈ S, ‖c q‖) * δ⁻¹ := by
  rw [weightedCauchySum, norm_mul]
  exact (mul_le_mul (norm_zeroCauchySum_le hδ hlo c S hp) (norm_inv_lineLogWeight_le_one hp)
    (norm_nonneg _) (mul_nonneg (Finset.sum_nonneg fun q _ => norm_nonneg _)
      (inv_nonneg.mpr hδ.le))).trans_eq (mul_one _)

theorem norm_weightedCauchySum_mul_sub_le {p : ℂ} (hp : σ ≤ p.re) (z₀ : ℂ) :
    ‖weightedCauchySum σ c S p * (p - z₀)‖ ≤
      ∑ q ∈ S, ‖c q‖ * (1 + ‖centredZero q - z₀‖ * δ⁻¹) := by
  rw [weightedCauchySum, mul_right_comm, norm_mul]
  exact (mul_le_mul (norm_zeroCauchySum_mul_sub_le hδ hlo c S hp z₀)
    (norm_inv_lineLogWeight_le_one hp) (norm_nonneg _)
    (Finset.sum_nonneg fun q _ => mul_nonneg (norm_nonneg _) (add_nonneg zero_le_one
      (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hδ.le))))).trans_eq (mul_one _)

end FiniteSums

theorem linePairing_re (σ : ℝ) (c : XiZeroCopy → ℂ) (S : Finset XiZeroCopy) (t : ℝ) :
    (linePairing σ c S t).re = ‖zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
      ((lineLogWeight σ ((σ : ℂ) + (t : ℂ) * I))⁻¹).re := by
  rw [linePairing, weightedCauchySum, ← mul_assoc, mul_comm ((starRingEnd ℂ) _),
    Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

theorem linePairing_eq_sum (σ : ℝ) (c : XiZeroCopy → ℂ) (S : Finset XiZeroCopy) (t : ℝ) :
    linePairing σ c S t = ∑ q ∈ S, (starRingEnd ℂ) (c q) *
      ((starRingEnd ℂ) (((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹) *
        weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)) := by
  rw [linePairing, zeroCauchySum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, mul_assoc]

/-! ### The pairing identity and the sampling bound -/

theorem le_mul_of_sq_le_of_le {X A B K₁ K₂ : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (h1 : X ^ 2 ≤ K₁ * (A * B)) (h2 : B ≤ K₂ * X) : X ≤ K₁ * K₂ * A := by
  rcases hX.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (mul_nonneg hK₁ hK₂) hA
  · refine le_of_mul_le_mul_right ?_ hpos
    calc X * X = X ^ 2 := (sq X).symm
      _ ≤ K₁ * (A * B) := h1
      _ ≤ K₁ * (A * (K₂ * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hA) hK₁
      _ = K₁ * K₂ * A * X := by ring

theorem halfPlanePoisson_le_lorentzMassTerm {σ δ D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hD1 : 1 ≤ D)
    (q : XiZeroCopy) (hlo : δ ≤ σ - (centredZero q).re) (hhi : σ - (centredZero q).re ≤ D)
    (t : ℝ) :
    halfPlanePoisson (σ - (centredZero q).re) (t - (centredZero q).im) ≤
      D / (δ * Real.pi) * lorentzMassTerm t q := by
  have e : lorentzMassTerm t q = (1 + (t - (centredZero q).im) ^ 2)⁻¹ := by
    rw [im_centredZero, lorentzMassTerm, one_div]
  rw [e]
  exact halfPlanePoisson_le_lorentz_of_le hδ hlo hhi hδ1 hD1 _

section Pairing

variable {σ δ : ℝ} (hδ : 0 < δ) (hlo : ∀ q : XiZeroCopy, δ ≤ σ - (centredZero q).re)
  (c : XiZeroCopy → ℂ) (S : Finset XiZeroCopy)
include hδ hlo

theorem integrable_conj_inv_mul_weightedCauchySum (q : XiZeroCopy) :
    Integrable fun t : ℝ => (starRingEnd ℂ) (((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹) *
      weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I) :=
  integrable_conj_inv_mul (fun p hp => differentiableAt_weightedCauchySum hδ hlo c S hp)
    (by linarith [hlo q])
    (fun p hp => norm_weightedCauchySum_mul_sub_le hδ hlo c S hp (centredZero q))

theorem integrable_linePairing : Integrable (linePairing σ c S) :=
  (integrable_finsetSum S fun q _ =>
    (integrable_conj_inv_mul_weightedCauchySum hδ hlo c S q).const_mul
      ((starRingEnd ℂ) (c q))).congr
    (Eventually.of_forall fun t => (linePairing_eq_sum σ c S t).symm)

/-- **The pairing identity.** Each term of `conj C` is the conjugate Cauchy kernel of a zero, so
the pairing of `C` with `C/Λ` on the line is a sum of values of `C/Λ` at the reflected zeros. -/
theorem integral_linePairing :
    ∫ t : ℝ, linePairing σ c S t = ((2 * Real.pi : ℝ) : ℂ) *
      ∑ q ∈ S, (starRingEnd ℂ) (c q) * weightedCauchySum σ c S (reflectedZero σ q) := by
  rw [integral_congr_ae (Eventually.of_forall (linePairing_eq_sum σ c S)),
    integral_finsetSum S fun q _ =>
      (integrable_conj_inv_mul_weightedCauchySum hδ hlo c S q).const_mul
        ((starRingEnd ℂ) (c q)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_const_mul, integral_conj_inv_mul_eq
    (fun p hp => differentiableAt_weightedCauchySum hδ hlo c S hp) (by linarith [hlo q])
    (fun p hp => norm_weightedCauchySum_mul_sub_le hδ hlo c S hp (centredZero q)), reflectedZero]
  ring

/-- **Sampling at the reflected zeros.** The values of `C/Λ` at the reflected zeros are Poisson
averages of its values on the line; summed over the zeros the kernels add up to the unit-window
count, which the weight absorbs. -/
theorem sum_norm_sq_weightedCauchySum_reflectedZero_le {D : ℝ} (hδ1 : δ ≤ 1) (hD1 : 1 ≤ D)
    (hhi : ∀ q : XiZeroCopy, σ - (centredZero q).re ≤ D) :
    ∑ q ∈ S, ‖weightedCauchySum σ c S (reflectedZero σ q)‖ ^ 2 ≤
      D / (δ * Real.pi) * (8 * (|xiLineTwoLogDerivConstant| + 2)) *
        ∫ t : ℝ, (linePairing σ c S t).re := by
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD1
  have hΦre : Integrable fun t : ℝ => (linePairing σ c S t).re :=
    (integrable_linePairing hδ hlo c S).re
  have hwc : Continuous fun t : ℝ => weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I) :=
    continuous_comp_verticalLine fun p hp => differentiableAt_weightedCauchySum hδ hlo c S hp
  have hline : ∀ t : ℝ, σ ≤ ((σ : ℂ) + (t : ℂ) * I).re := fun t => by simp
  have hw2le : ∀ t : ℝ, ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (linePairing σ c S t).re := fun t => by
    have h1 := mul_norm_sq_inv_lineLogWeight_le (hline t) (L := 1) (K := 1)
      (by rw [one_mul]; exact one_le_re_lineLogWeight (hline t))
    rw [one_mul, one_mul] at h1
    rw [linePairing_re, weightedCauchySum, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hw2 : Integrable fun t : ℝ =>
      ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine hΦre.mono' (hwc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hw2le t
  have hlor : ∀ q : XiZeroCopy, Integrable fun t : ℝ =>
      lorentzMassTerm t q * ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun q => by
    have hmq : Measurable fun t : ℝ => lorentzMassTerm t q :=
      measurable_const.div (measurable_const.add ((measurable_id.sub_const _).pow_const 2))
    refine hw2.mono' (hmq.mul (hwc.norm.pow 2).measurable).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (lorentzMassTerm_nonneg t q) (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (lorentzMassTerm_le_one t q) (sq_nonneg _)).trans_eq
      (one_mul _)
  have hq : ∀ q ∈ S, ‖weightedCauchySum σ c S (reflectedZero σ q)‖ ^ 2 ≤
      D / (δ * Real.pi) * ∫ t : ℝ, lorentzMassTerm t q *
        ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun q _ => by
    have hd : 0 < σ - (centredZero q).re := hδ.trans_le (hlo q)
    have h1 : ‖weightedCauchySum σ c S (reflectedZero σ q)‖ ^ 2 ≤
        ∫ t : ℝ, halfPlanePoisson (σ - (centredZero q).re) (t - (centredZero q).im) *
          ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      norm_sq_apply_le_integral_halfPlanePoisson
        (fun p hp => differentiableAt_weightedCauchySum hδ hlo c S hp)
        (fun p hp => norm_weightedCauchySum_le hδ hlo c S hp) hd (centredZero q).im
    rw [← integral_const_mul]
    refine h1.trans (integral_mono_of_nonneg
      (Eventually.of_forall fun t => mul_nonneg (halfPlanePoisson_pos hd _).le (sq_nonneg _))
      ((hlor q).const_mul _) (Eventually.of_forall fun t => ?_))
    show halfPlanePoisson (σ - (centredZero q).re) (t - (centredZero q).im) *
        ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      D / (δ * Real.pi) * (lorentzMassTerm t q *
        ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (halfPlanePoisson_le_lorentzMassTerm hδ hδ1 hD1 q (hlo q) (hhi q) t) (sq_nonneg _)
  calc ∑ q ∈ S, ‖weightedCauchySum σ c S (reflectedZero σ q)‖ ^ 2
      ≤ ∑ q ∈ S, D / (δ * Real.pi) * ∫ t : ℝ, lorentzMassTerm t q *
          ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := Finset.sum_le_sum hq
    _ = D / (δ * Real.pi) * ∫ t : ℝ, ∑ q ∈ S, lorentzMassTerm t q *
          ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
        rw [← Finset.mul_sum, integral_finsetSum S fun q _ => hlor q]
    _ ≤ D / (δ * Real.pi) * ∫ t : ℝ, 8 * (|xiLineTwoLogDerivConstant| + 2) *
          (linePairing σ c S t).re := by
        refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (Eventually.of_forall fun t => Finset.sum_nonneg fun q _ =>
            mul_nonneg (lorentzMassTerm_nonneg t q) (sq_nonneg _))
          (hΦre.const_mul _) (Eventually.of_forall fun t => ?_)) (by positivity)
        show ∑ q ∈ S, lorentzMassTerm t q *
            ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          8 * (|xiLineTwoLogDerivConstant| + 2) * (linePairing σ c S t).re
        have hsum : ∑ q ∈ S, lorentzMassTerm t q ≤
            8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) :=
          ((summable_lorentzMassTerm t).sum_le_tsum S fun q _ =>
            lorentzMassTerm_nonneg t q).trans (lorentzMass_le_log t)
        have h3 : (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
            ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
            (|xiLineTwoLogDerivConstant| + 2) * (linePairing σ c S t).re := by
          have h4 := mul_norm_sq_inv_lineLogWeight_le (hline t)
            (const_add_log_le_mul_re_lineLogWeight_line xiLineTwoLogDerivConstant σ t)
          rw [linePairing_re, weightedCauchySum, norm_mul, mul_pow]
          linarith [mul_le_mul_of_nonneg_left h4
            (sq_nonneg ‖zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)‖)]
        rw [← Finset.sum_mul]
        linarith [mul_le_mul_of_nonneg_right hsum
          (sq_nonneg ‖weightedCauchySum σ c S ((σ : ℂ) + (t : ℂ) * I)‖)]
    _ = D / (δ * Real.pi) * (8 * (|xiLineTwoLogDerivConstant| + 2)) *
          ∫ t : ℝ, (linePairing σ c S t).re := by
        rw [integral_const_mul]
        ring

/-- **The weighted Hilbert inequality for finitely many zeros.**
`∫ |C(σ + it)|² Re(1/Λ) dt ≤ (32 π D (|C₀| + 2)/δ) Σ |c_z|²`: the pairing identity,
Cauchy–Schwarz and the sampling bound give `X² ≲ (Σ |c_z|²) X`. -/
theorem integral_linePairing_re_le {D : ℝ} (hδ1 : δ ≤ 1) (hD1 : 1 ≤ D)
    (hhi : ∀ q : XiZeroCopy, σ - (centredZero q).re ≤ D) :
    ∫ t : ℝ, (linePairing σ c S t).re ≤
      32 * Real.pi * D * (|xiLineTwoLogDerivConstant| + 2) / δ * ∑ q ∈ S, ‖c q‖ ^ 2 := by
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD1
  have hΦ := integrable_linePairing hδ hlo c S
  have hX0 : 0 ≤ ∫ t : ℝ, (linePairing σ c S t).re := integral_nonneg fun t => by
    rw [linePairing_re]
    exact mul_nonneg (sq_nonneg _) (re_inv_lineLogWeight_nonneg (by simp))
  have hXre : ∫ t : ℝ, (linePairing σ c S t).re = (∫ t : ℝ, linePairing σ c S t).re := by
    have h := Complex.reCLM.integral_comp_comm hΦ
    simpa only [Complex.reCLM_apply] using h
  have h1 : ∫ t : ℝ, (linePairing σ c S t).re ≤
      2 * Real.pi * ∑ q ∈ S, ‖c q‖ * ‖weightedCauchySum σ c S (reflectedZero σ q)‖ := by
    rw [hXre, integral_linePairing hδ hlo c S]
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) (by positivity)
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [norm_mul, RCLike.norm_conj]
  have h2 : (∫ t : ℝ, (linePairing σ c S t).re) ^ 2 ≤ (2 * Real.pi) ^ 2 *
      ((∑ q ∈ S, ‖c q‖ ^ 2) *
        ∑ q ∈ S, ‖weightedCauchySum σ c S (reflectedZero σ q)‖ ^ 2) := by
    calc (∫ t : ℝ, (linePairing σ c S t).re) ^ 2
        ≤ (2 * Real.pi * ∑ q ∈ S, ‖c q‖ *
            ‖weightedCauchySum σ c S (reflectedZero σ q)‖) ^ 2 := pow_le_pow_left₀ hX0 h1 2
      _ = (2 * Real.pi) ^ 2 * (∑ q ∈ S, ‖c q‖ *
            ‖weightedCauchySum σ c S (reflectedZero σ q)‖) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_mul_sq_le_sq_mul_sq S _ _) (sq_nonneg _)
  have h3 := le_mul_of_sq_le_of_le hX0 (Finset.sum_nonneg fun q _ => sq_nonneg ‖c q‖)
    (sq_nonneg (2 * Real.pi)) (by positivity) h2
    (sum_norm_sq_weightedCauchySum_reflectedZero_le hδ hlo c S hδ1 hD1 hhi)
  refine h3.trans_eq ?_
  congr 1
  rw [div_mul_eq_mul_div, ← mul_div_assoc,
    div_eq_div_iff (mul_ne_zero hδ.ne' Real.pi_ne_zero) hδ.ne']
  ring

end Pairing

/-! ### Passage to square-summable coefficients -/

/-- Fatou: a pointwise limit of nonnegative functions with uniformly bounded integrals is
integrable with the same bound. -/
theorem integrable_and_integral_le_of_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hm : ∀ n, Measurable (f n)) (h0 : ∀ n t, 0 ≤ f n t) (hi : ∀ n, Integrable (f n))
    (hB : ∀ n, ∫ t, f n t ≤ B) (hlim : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (g t))) :
    Integrable g ∧ ∫ t, g t ≤ B := by
  have hgm : Measurable g := measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr hlim)
  have hg0 : ∀ t, 0 ≤ g t := fun t => ge_of_tendsto' (hlim t) fun n => h0 n t
  have hB0 : 0 ≤ B := (integral_nonneg (h0 0)).trans (hB 0)
  have hfat : ∫⁻ t, ENNReal.ofReal (g t) ≤ ENNReal.ofReal B := by
    calc ∫⁻ t, ENNReal.ofReal (g t)
        = ∫⁻ t, liminf (fun n => ENNReal.ofReal (f n t)) atTop :=
          lintegral_congr fun t =>
            (((ENNReal.continuous_ofReal.tendsto _).comp (hlim t)).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ t, ENNReal.ofReal (f n t)) atTop :=
          lintegral_liminf_le' fun n => (ENNReal.measurable_ofReal.comp (hm n)).aemeasurable
      _ ≤ ENNReal.ofReal B := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (h0 n))]
          exact ENNReal.ofReal_le_ofReal (hB n)
  have hgi : Integrable g :=
    (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable
      (Eventually.of_forall hg0)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfat)
  refine ⟨hgi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hfat

theorem countable_zeroCopies : Countable XiZeroCopy :=
  Set.countable_univ_iff.mp (summable_inv_sq_centredZero.countable_support.mono fun q _ =>
    pow_ne_zero 2 (inv_ne_zero (norm_ne_zero_iff.mpr (centredZero_ne_zero q))))

/-- **The weighted Hilbert inequality on the zeros.** For square-summable coefficients and a line
to the right of all zeros (`δ ≤ σ - Re z ≤ D`, `δ ≤ 1 ≤ D`),
`∫ |Σ_z c_z/(σ + it - z)|² dt/log(|t| + 4) ≤ (160 π D (|C₀| + 2)/δ) Σ_z |c_z|²`. No separation of
the zeros enters; the logarithm is their unit-window count. -/
theorem integrable_and_integral_norm_sq_tsum_zeroCauchy_le {σ δ D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD1 : 1 ≤ D) (hlo : ∀ q : XiZeroCopy, δ ≤ σ - (centredZero q).re)
    (hhi : ∀ q : XiZeroCopy, σ - (centredZero q).re ≤ D) {c : XiZeroCopy → ℂ}
    (hc : Summable fun q => ‖c q‖ ^ 2) :
    Integrable (fun t : ℝ => ‖∑' q : XiZeroCopy,
        c q * ((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹‖ ^ 2 / Real.log (|t| + 4)) ∧
      ∫ t : ℝ, ‖∑' q : XiZeroCopy, c q * ((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹‖ ^ 2 /
        Real.log (|t| + 4) ≤
        160 * Real.pi * D * (|xiLineTwoLogDerivConstant| + 2) / δ * ∑' q, ‖c q‖ ^ 2 := by
  haveI := countable_zeroCopies
  obtain ⟨T, hT⟩ := exists_seq_tendsto (atTop : Filter (Finset XiZeroCopy))
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD1
  have hline : ∀ t : ℝ, σ ≤ ((σ : ℂ) + (t : ℂ) * I).re := fun t => by simp
  have hlog : ∀ t : ℝ, 0 < Real.log (|t| + 4) := fun t =>
    Real.log_pos (by linarith [abs_nonneg t])
  have hCc : ∀ S : Finset XiZeroCopy, Continuous fun t : ℝ =>
      zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I) := fun S =>
    continuous_comp_verticalLine fun p hp => differentiableAt_zeroCauchySum hδ hlo c S hp
  have hlogm : Measurable fun t : ℝ => Real.log (|t| + 4) :=
    Real.measurable_log.comp (continuous_abs.measurable.add_const 4)
  have hΦre : ∀ S : Finset XiZeroCopy, Integrable fun t : ℝ => (linePairing σ c S t).re :=
    fun S => (integrable_linePairing hδ hlo c S).re
  -- the weight `1/log` is at most five times the density `Re (1/Λ)`
  have hle : ∀ (S : Finset XiZeroCopy) (t : ℝ),
      ‖zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4) ≤
        5 * (linePairing σ c S t).re := fun S t => by
    rw [linePairing_re, div_eq_mul_inv]
    linarith [mul_le_mul_of_nonneg_left (inv_log_le_re_inv_lineLogWeight_line σ t)
      (sq_nonneg ‖zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)‖)]
  have hint : ∀ S : Finset XiZeroCopy, Integrable fun t : ℝ =>
      ‖zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4) := fun S => by
    refine ((hΦre S).const_mul 5).mono'
      (((hCc S).norm.pow 2).measurable.div hlogm).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hlog t).le)]
    exact hle S t
  have hK0 : 0 ≤ 160 * Real.pi * D * (|xiLineTwoLogDerivConstant| + 2) / δ := by positivity
  have hbound : ∀ S : Finset XiZeroCopy, ∫ t : ℝ,
      ‖zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4) ≤
        160 * Real.pi * D * (|xiLineTwoLogDerivConstant| + 2) / δ * ∑' q, ‖c q‖ ^ 2 :=
    fun S => by
      have h1 : ∫ t : ℝ, ‖zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          Real.log (|t| + 4) ≤ ∫ t : ℝ, 5 * (linePairing σ c S t).re :=
        integral_mono (hint S) ((hΦre S).const_mul 5) (hle S)
      rw [integral_const_mul] at h1
      have h2 := integral_linePairing_re_le hδ hlo c S hδ1 hD1 hhi
      have h3 : ∑ q ∈ S, ‖c q‖ ^ 2 ≤ ∑' q, ‖c q‖ ^ 2 :=
        hc.sum_le_tsum S fun q _ => sq_nonneg _
      calc ∫ t : ℝ, ‖zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4)
          ≤ 5 * ∫ t : ℝ, (linePairing σ c S t).re := h1
        _ ≤ 5 * (32 * Real.pi * D * (|xiLineTwoLogDerivConstant| + 2) / δ *
              ∑ q ∈ S, ‖c q‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = 160 * Real.pi * D * (|xiLineTwoLogDerivConstant| + 2) / δ *
              ∑ q ∈ S, ‖c q‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 hK0
  have hlim : ∀ t : ℝ, Tendsto (fun n : ℕ =>
      ‖zeroCauchySum c (T n) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4)) atTop
      (𝓝 (‖∑' q : XiZeroCopy, c q * ((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹‖ ^ 2 /
        Real.log (|t| + 4))) := fun t => by
    have hs : HasSum (fun q : XiZeroCopy => c q * ((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹)
        (∑' q : XiZeroCopy, c q * ((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹) :=
      (summable_norm_mul_inv_sub_centredZero hc hδ fun q =>
        le_norm_sub_of_re (hlo q) (hline t)).of_norm.hasSum
    have h1 : Tendsto (fun S : Finset XiZeroCopy => zeroCauchySum c S ((σ : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (∑' q : XiZeroCopy, c q * ((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹)) := hs
    exact (((continuous_norm.tendsto _).comp (h1.comp hT)).pow 2).div_const _
  exact integrable_and_integral_le_of_tendsto
    (f := fun n t => ‖zeroCauchySum c (T n) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4))
    (fun n => ((hCc (T n)).norm.pow 2).measurable.div hlogm)
    (fun n t => div_nonneg (sq_nonneg _) (hlog t).le) (fun n => hint (T n))
    (fun n => hbound (T n)) hlim

/-! ### The continuation of the state on vertical lines -/

/-- A line to the right of all zeros carries no zero. -/
theorem xi_ne_zero_of_right_of_zeros {σ δ : ℝ} (hδ : 0 < δ)
    (hlo : ∀ q : XiZeroCopy, δ ≤ σ - (centredZero q).re) (t : ℝ) :
    xi (1 / 2 + ((σ : ℂ) + (t : ℂ) * I)) ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
  have hz : centredZero q = (σ : ℂ) + (t : ℂ) * I := by
    unfold centredZero
    rw [hq]
    ring
  have e : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have h1 := hlo q
  rw [hz, e] at h1
  linarith

/-- **The continuation of the state on vertical lines.** On a line `Re w = σ - 8` to the right
of the transported zeros the continuation of `L F` is square-integrable against
`dt/log(|t| + 4)`, with norm controlled by the square sum of the zero values. -/
theorem criticalState_integral_norm_sq_stateMeromorphic_line_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {σ δ D : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hD1 : 1 ≤ D) (hlo : ∀ q : XiZeroCopy, δ ≤ σ - (centredZero q).re)
    (hhi : ∀ q : XiZeroCopy, σ - (centredZero q).re ≤ D) :
    Integrable (fun t : ℝ => ‖stateMeromorphic W₀ F ((σ : ℂ) - 8 + (t : ℂ) * I)‖ ^ 2 /
        Real.log (|t| + 4)) ∧
      ∫ t : ℝ, ‖stateMeromorphic W₀ F ((σ : ℂ) - 8 + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4) ≤
        (criticalAliasCoefficient W₀)⁻¹ ^ 2 *
          (160 * Real.pi * D * (|xiLineTwoLogDerivConstant| + 2) / δ *
            ∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2) := by
  obtain ⟨hi, hle⟩ := integrable_and_integral_norm_sq_tsum_zeroCauchy_le hδ hδ1 hD1 hlo hhi
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF)
  have e : ∀ t : ℝ, ‖stateMeromorphic W₀ F ((σ : ℂ) - 8 + (t : ℂ) * I)‖ ^ 2 /
      Real.log (|t| + 4) = (criticalAliasCoefficient W₀)⁻¹ ^ 2 *
        (‖∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
          ((σ : ℂ) + (t : ℂ) * I - centredZero q)⁻¹‖ ^ 2 / Real.log (|t| + 4)) := fun t => by
    have e1 : (σ : ℂ) - 8 + (t : ℂ) * I + 8 = (σ : ℂ) + (t : ℂ) * I := by ring
    have hxi : xi (1 / 2 + ((σ : ℂ) - 8 + (t : ℂ) * I + 8)) ≠ 0 := by
      rw [e1]
      exact xi_ne_zero_of_right_of_zeros hδ hlo t
    have hs := criticalState_hasSum_stateMeromorphic hW hthreshold hF hxi
    rw [e1] at hs
    rw [← hs.tsum_eq, tsum_mul_left, norm_mul, norm_neg, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, ← abs_inv, sq_abs, mul_div_assoc]
  refine ⟨(hi.const_mul _).congr (Eventually.of_forall fun t => (e t).symm), ?_⟩
  rw [integral_congr_ae (Eventually.of_forall e), integral_const_mul]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- The same bound on every line to the right of an abscissa `κ` of the zeros. -/
theorem criticalState_integral_norm_sq_stateMeromorphic_line_le_of_abscissa {W₀ : ℝ}
    (hW : 0 < W₀) (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {κ σ : ℝ}
    (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hσ : κ < σ) :
    Integrable (fun t : ℝ => ‖stateMeromorphic W₀ F ((σ : ℂ) - 8 + (t : ℂ) * I)‖ ^ 2 /
        Real.log (|t| + 4)) ∧
      ∫ t : ℝ, ‖stateMeromorphic W₀ F ((σ : ℂ) - 8 + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4) ≤
        (criticalAliasCoefficient W₀)⁻¹ ^ 2 *
          (160 * Real.pi * max 1 (σ + 1 / 2) * (|xiLineTwoLogDerivConstant| + 2) /
            min (σ - κ) 1 *
            ∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2) :=
  criticalState_integral_norm_sq_stateMeromorphic_line_le hW hthreshold hF
    (lt_min (sub_pos.mpr hσ) one_pos) (min_le_right _ _) (le_max_left _ _)
    (fun q => (min_le_left _ _).trans (by linarith [hκ q]))
    (fun q => le_trans (by linarith [(abs_lt.mp (abs_re_centredZero_lt q)).1])
      (le_max_right _ _))

/-- Unconditionally the bound holds on every line `Re w = σ - 8` with `σ > 8999/24000`, an
eighth beyond the line `Re w = -15/2` of the exponential energy bounds. -/
theorem criticalState_integral_norm_sq_stateMeromorphic_line_le_seed {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {σ : ℝ} (hσ : 8999 / 24000 < σ) :
    Integrable (fun t : ℝ => ‖stateMeromorphic W₀ F ((σ : ℂ) - 8 + (t : ℂ) * I)‖ ^ 2 /
        Real.log (|t| + 4)) ∧
      ∫ t : ℝ, ‖stateMeromorphic W₀ F ((σ : ℂ) - 8 + (t : ℂ) * I)‖ ^ 2 / Real.log (|t| + 4) ≤
        (criticalAliasCoefficient W₀)⁻¹ ^ 2 *
          (160 * Real.pi * max 1 (σ + 1 / 2) * (|xiLineTwoLogDerivConstant| + 2) /
            min (σ - 8999 / 24000) 1 *
            ∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2) :=
  criticalState_integral_norm_sq_stateMeromorphic_line_le_of_abscissa hW hthreshold hF
    re_centredZero_le_seed hσ

end GaloisForLFunctions.ExclusionOfTheCriticalState
