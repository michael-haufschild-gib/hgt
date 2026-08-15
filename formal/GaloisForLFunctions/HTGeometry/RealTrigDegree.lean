import GaloisForLFunctions.HTGeometry.ComplexTrigPolynomial
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Real trigonometric polynomials by degree

A real function is a trigonometric polynomial of degree at most `D` when its complexification is a
combination of the exponential monomials of frequency at most `D`.  In that description the three
operations the Cayley transport needs are all immediate:

* differentiating keeps the degree;
* multiplying by `cos θ` or `sin θ` raises it by one;
* the `L²` Bernstein inequality `‖F'‖₂ ≤ D‖F'‖₂` transfers from the complex statement.

Together with Minkowski on the period — which follows from the real Cauchy–Schwarz inequality — this
is everything needed to iterate the Cayley transport operator.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem expMon_one_add_neg_one (θ : ℝ) :
    expMon 1 θ + expMon (-1) θ = 2 * ((Real.cos θ : ℝ) : ℂ) := by
  have h1 : expMon 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [expMon]
    congr 1
    push_cast
    ring
  have h2 : expMon (-1) θ = Complex.exp ((((-θ : ℝ)) : ℂ) * Complex.I) := by
    rw [expMon]
    congr 1
    push_cast
    ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I,
    show (((-θ : ℝ)) : ℂ) = -((θ : ℝ) : ℂ) by push_cast; ring,
    Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

theorem expMon_one_sub_neg_one (θ : ℝ) :
    expMon 1 θ - expMon (-1) θ = 2 * Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
  have h1 : expMon 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [expMon]
    congr 1
    push_cast
    ring
  have h2 : expMon (-1) θ = Complex.exp ((((-θ : ℝ)) : ℂ) * Complex.I) := by
    rw [expMon]
    congr 1
    push_cast
    ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I,
    show (((-θ : ℝ)) : ℂ) = -((θ : ℝ) : ℂ) by push_cast; ring,
    Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_sin]
  ring

/-- A real trigonometric polynomial of degree at most `D`. -/
def RealTrigDeg (D : ℕ) (F : ℝ → ℝ) : Prop :=
  ∃ f : ℤ → ℂ, TrigSupp D f ∧ ∀ θ : ℝ, ((F θ : ℝ) : ℂ) = trigExp D f θ

theorem RealTrigDeg.mono {D E : ℕ} (hDE : D ≤ E) {F : ℝ → ℝ} (hF : RealTrigDeg D F) :
    RealTrigDeg E F := by
  obtain ⟨f, hsupp, hval⟩ := hF
  refine ⟨f, fun k hk => hsupp k ?_, fun θ => ?_⟩
  · have : (D : ℤ) ≤ (E : ℤ) := by exact_mod_cast hDE
    omega
  · rw [hval θ, trigExp_eq_of_supp hDE hsupp]

/-- Differentiating keeps the degree. -/
theorem RealTrigDeg.deriv {D : ℕ} {F F' : ℝ → ℝ} (hF : RealTrigDeg D F)
    (hderiv : ∀ θ : ℝ, HasDerivAt F (F' θ) θ) : RealTrigDeg D F' := by
  obtain ⟨f, hsupp, hval⟩ := hF
  refine ⟨fun k => f k * ((k : ℂ) * Complex.I), trigSupp_deriv hsupp, fun θ => ?_⟩
  have hc : HasDerivAt (fun u : ℝ => ((F u : ℝ) : ℂ)) ((F' θ : ℝ) : ℂ) θ :=
    (hderiv θ).ofReal_comp
  have ht : HasDerivAt (trigExp D f)
      (trigExp D (fun k => f k * ((k : ℂ) * Complex.I)) θ) θ := hasDerivAt_trigExp D f θ
  have hc' : HasDerivAt (trigExp D f) ((F' θ : ℝ) : ℂ) θ := by
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards with u
    exact (hval u).symm
  exact hc'.unique ht

/-- Multiplying by `cos θ` raises the degree by one. -/
theorem RealTrigDeg.mul_cos {D : ℕ} {F : ℝ → ℝ} (hF : RealTrigDeg D F) :
    RealTrigDeg (D + 1) (fun θ => Real.cos θ * F θ) := by
  obtain ⟨f, hsupp, hval⟩ := hF
  refine ⟨fun l => (1 / 2 : ℂ) * (f (l - 1) + f (l + 1)), ?_, fun θ => ?_⟩
  · exact trigSupp_smul (trigSupp_add (trigSupp_shift_succ hsupp) (trigSupp_shift_pred hsupp)) _
  · have hsplit : ((Real.cos θ : ℝ) : ℂ) = (1 / 2 : ℂ) * (expMon 1 θ + expMon (-1) θ) := by
      rw [expMon_one_add_neg_one]
      ring
    rw [Complex.ofReal_mul, hsplit, hval θ]
    rw [trigExp_smul, trigExp_add, ← expMon_one_mul_trigExp hsupp,
      ← expMon_neg_one_mul_trigExp hsupp]
    ring

/-- Multiplying by `sin θ` raises the degree by one. -/
theorem RealTrigDeg.mul_sin {D : ℕ} {F : ℝ → ℝ} (hF : RealTrigDeg D F) :
    RealTrigDeg (D + 1) (fun θ => Real.sin θ * F θ) := by
  obtain ⟨f, hsupp, hval⟩ := hF
  refine ⟨fun l => (1 / (2 * Complex.I) : ℂ) * (f (l - 1) - f (l + 1)), ?_, fun θ => ?_⟩
  · refine trigSupp_smul ?_ _
    intro k hk
    show f (k - 1) - f (k + 1) = 0
    have h1 : f (k - 1) = 0 := trigSupp_shift_succ hsupp k hk
    have h2 : f (k + 1) = 0 := trigSupp_shift_pred hsupp k hk
    rw [h1, h2, sub_self]
  · have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hsplit : ((Real.sin θ : ℝ) : ℂ)
        = (1 / (2 * Complex.I) : ℂ) * (expMon 1 θ - expMon (-1) θ) := by
      rw [expMon_one_sub_neg_one]
      field_simp
    have hsub : trigExp (D + 1) (fun l => f (l - 1) - f (l + 1)) θ
        = trigExp (D + 1) (fun l => f (l - 1)) θ - trigExp (D + 1) (fun l => f (l + 1)) θ := by
      rw [trigExp, trigExp, trigExp, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [Complex.ofReal_mul, hsplit, hval θ, trigExp_smul, hsub,
      ← expMon_one_mul_trigExp hsupp, ← expMon_neg_one_mul_trigExp hsupp]
    ring

theorem RealTrigDeg.add {D : ℕ} {F G : ℝ → ℝ} (hF : RealTrigDeg D F) (hG : RealTrigDeg D G) :
    RealTrigDeg D (fun θ => F θ + G θ) := by
  obtain ⟨f, hsf, hvf⟩ := hF
  obtain ⟨g, hsg, hvg⟩ := hG
  refine ⟨fun k => f k + g k, trigSupp_add hsf hsg, fun θ => ?_⟩
  rw [Complex.ofReal_add, hvf θ, hvg θ, trigExp_add]

theorem RealTrigDeg.smul {D : ℕ} {F : ℝ → ℝ} (hF : RealTrigDeg D F) (c : ℝ) :
    RealTrigDeg D (fun θ => c * F θ) := by
  obtain ⟨f, hsf, hvf⟩ := hF
  refine ⟨fun k => (c : ℂ) * f k, trigSupp_smul hsf _, fun θ => ?_⟩
  rw [Complex.ofReal_mul, hvf θ, trigExp_smul]

/-- **The `L²` Bernstein inequality for real trigonometric polynomials.** -/
theorem RealTrigDeg.integral_deriv_sq_le {D : ℕ} {F F' : ℝ → ℝ} (hF : RealTrigDeg D F)
    (hderiv : ∀ θ : ℝ, HasDerivAt F (F' θ) θ) :
    (∫ θ in (-Real.pi)..Real.pi, F' θ ^ 2)
      ≤ (D : ℝ) ^ 2 * ∫ θ in (-Real.pi)..Real.pi, F θ ^ 2 := by
  obtain ⟨f, hsupp, hval⟩ := hF
  have hFsq : ∀ θ : ℝ, F θ ^ 2 = ‖trigExp D f θ‖ ^ 2 := by
    intro θ
    rw [← hval θ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hderivVal : ∀ θ : ℝ,
      ((F' θ : ℝ) : ℂ) = trigExp D (fun k => f k * ((k : ℂ) * Complex.I)) θ := by
    intro θ
    have hc : HasDerivAt (fun u : ℝ => ((F u : ℝ) : ℂ)) ((F' θ : ℝ) : ℂ) θ :=
      (hderiv θ).ofReal_comp
    have hc' : HasDerivAt (trigExp D f) ((F' θ : ℝ) : ℂ) θ := by
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards with u
      exact (hval u).symm
    exact hc'.unique (hasDerivAt_trigExp D f θ)
  have hF'sq : ∀ θ : ℝ,
      F' θ ^ 2 = ‖trigExp D (fun k => f k * ((k : ℂ) * Complex.I)) θ‖ ^ 2 := by
    intro θ
    rw [← hderivVal θ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [intervalIntegral.integral_congr (fun θ _ => hF'sq θ),
    intervalIntegral.integral_congr (fun θ _ => hFsq θ)]
  exact integral_normSq_trigExp_deriv_le D f


/-! ## The `L²` norm on the period -/

theorem neg_pi_le_pi : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]

theorem RealTrigDeg.continuous {D : ℕ} {F : ℝ → ℝ} (hF : RealTrigDeg D F) : Continuous F := by
  obtain ⟨f, _, hval⟩ := hF
  have heq : F = fun θ => (trigExp D f θ).re := by
    funext θ
    rw [← hval θ, Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp (continuous_trigExp D f)

theorem RealTrigDeg.congr {D : ℕ} {F G : ℝ → ℝ} (hF : RealTrigDeg D F) (h : ∀ θ, F θ = G θ) :
    RealTrigDeg D G := by
  obtain ⟨f, hsupp, hval⟩ := hF
  exact ⟨f, hsupp, fun θ => by rw [← h θ, hval θ]⟩

/-- The `L²` norm of a function on the period. -/
def trigNorm (F : ℝ → ℝ) : ℝ := Real.sqrt (∫ θ in (-Real.pi)..Real.pi, F θ ^ 2)

theorem trigNorm_nonneg (F : ℝ → ℝ) : 0 ≤ trigNorm F := Real.sqrt_nonneg _

theorem integral_sq_nonneg (F : ℝ → ℝ) : 0 ≤ ∫ θ in (-Real.pi)..Real.pi, F θ ^ 2 := by
  rw [intervalIntegral.integral_of_le neg_pi_le_pi]
  exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _

theorem trigNorm_sq (F : ℝ → ℝ) : trigNorm F ^ 2 = ∫ θ in (-Real.pi)..Real.pi, F θ ^ 2 :=
  Real.sq_sqrt (integral_sq_nonneg F)

/-- **Minkowski on the period.** -/
theorem trigNorm_add_le {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B) :
    trigNorm (fun θ => A θ + B θ) ≤ trigNorm A + trigNorm B := by
  have hcA0 : Continuous fun θ : ℝ => A θ ^ 2 := hA.pow 2
  have hcB0 : Continuous fun θ : ℝ => B θ ^ 2 := hB.pow 2
  have hcAB0 : Continuous fun θ : ℝ => A θ * B θ := hA.mul hB
  have hIA : IntegrableOn (fun θ : ℝ => A θ ^ 2) (Set.Ioc (-Real.pi) Real.pi) volume :=
    (hcA0.intervalIntegrable (-Real.pi) Real.pi).1
  have hIB : IntegrableOn (fun θ : ℝ => B θ ^ 2) (Set.Ioc (-Real.pi) Real.pi) volume :=
    (hcB0.intervalIntegrable (-Real.pi) Real.pi).1
  have hIAB : IntegrableOn (fun θ : ℝ => A θ * B θ) (Set.Ioc (-Real.pi) Real.pi) volume :=
    (hcAB0.intervalIntegrable (-Real.pi) Real.pi).1
  have hcs := sq_integral_mul_le (μ := (volume : Measure ℝ).restrict (Set.Ioc (-Real.pi) Real.pi))
    hA.aestronglyMeasurable hB.aestronglyMeasurable hIA hIB
  have hexp : ∀ θ : ℝ, (A θ + B θ) ^ 2 = A θ ^ 2 + 2 * (A θ * B θ) + B θ ^ 2 := by
    intro θ
    ring
  have hsplit : (∫ θ in (-Real.pi)..Real.pi, (A θ + B θ) ^ 2)
      = (∫ θ in (-Real.pi)..Real.pi, A θ ^ 2) + 2 * (∫ θ in (-Real.pi)..Real.pi, A θ * B θ)
        + ∫ θ in (-Real.pi)..Real.pi, B θ ^ 2 := by
    have hcA : Continuous fun θ : ℝ => A θ ^ 2 := hA.pow 2
    have hcB : Continuous fun θ : ℝ => B θ ^ 2 := hB.pow 2
    have hcAB : Continuous fun θ : ℝ => A θ * B θ := hA.mul hB
    have hi3 : IntervalIntegrable (fun θ : ℝ => A θ ^ 2) volume (-Real.pi) Real.pi :=
      hcA.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun θ : ℝ => B θ ^ 2) volume (-Real.pi) Real.pi :=
      hcB.intervalIntegrable _ _
    have hi4 : IntervalIntegrable (fun θ : ℝ => 2 * (A θ * B θ)) volume (-Real.pi) Real.pi :=
      (hcAB.intervalIntegrable _ _).const_mul 2
    have hi1 : IntervalIntegrable (fun θ : ℝ => A θ ^ 2 + 2 * (A θ * B θ))
        volume (-Real.pi) Real.pi := hi3.add hi4
    rw [intervalIntegral.integral_congr (fun θ _ => hexp θ),
      intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_add hi3 hi4,
      intervalIntegral.integral_const_mul]
  have hIocA : (∫ θ in (-Real.pi)..Real.pi, A θ ^ 2)
      = ∫ θ in Set.Ioc (-Real.pi) Real.pi, A θ ^ 2 :=
    intervalIntegral.integral_of_le neg_pi_le_pi
  have hIocB : (∫ θ in (-Real.pi)..Real.pi, B θ ^ 2)
      = ∫ θ in Set.Ioc (-Real.pi) Real.pi, B θ ^ 2 :=
    intervalIntegral.integral_of_le neg_pi_le_pi
  have hIocAB : (∫ θ in (-Real.pi)..Real.pi, A θ * B θ)
      = ∫ θ in Set.Ioc (-Real.pi) Real.pi, A θ * B θ :=
    intervalIntegral.integral_of_le neg_pi_le_pi
  have hmid : (∫ θ in (-Real.pi)..Real.pi, A θ * B θ) ≤ trigNorm A * trigNorm B := by
    have habs : (∫ θ in Set.Ioc (-Real.pi) Real.pi, A θ * B θ) ^ 2
        ≤ (trigNorm A * trigNorm B) ^ 2 := by
      rw [mul_pow, trigNorm_sq, trigNorm_sq, hIocA, hIocB]
      exact hcs
    have hnn : (0 : ℝ) ≤ trigNorm A * trigNorm B :=
      mul_nonneg (trigNorm_nonneg A) (trigNorm_nonneg B)
    rw [hIocAB]
    nlinarith [habs, hnn]
  have hfinal : (∫ θ in (-Real.pi)..Real.pi, (A θ + B θ) ^ 2)
      ≤ (trigNorm A + trigNorm B) ^ 2 := by
    rw [hsplit]
    have h1 : trigNorm A ^ 2 = ∫ θ in (-Real.pi)..Real.pi, A θ ^ 2 := trigNorm_sq A
    have h2 : trigNorm B ^ 2 = ∫ θ in (-Real.pi)..Real.pi, B θ ^ 2 := trigNorm_sq B
    nlinarith [hmid, h1, h2]
  have hsq := Real.sqrt_le_sqrt hfinal
  rw [Real.sqrt_sq (add_nonneg (trigNorm_nonneg A) (trigNorm_nonneg B))] at hsq
  exact hsq

theorem trigNorm_le_of_sq_le {F G : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hF : Continuous F) (hG : Continuous G)
    (h : ∀ θ : ℝ, F θ ^ 2 ≤ M ^ 2 * G θ ^ 2) : trigNorm F ≤ M * trigNorm G := by
  have hint : (∫ θ in (-Real.pi)..Real.pi, F θ ^ 2)
      ≤ M ^ 2 * ∫ θ in (-Real.pi)..Real.pi, G θ ^ 2 := by
    rw [intervalIntegral.integral_of_le neg_pi_le_pi,
      intervalIntegral.integral_of_le neg_pi_le_pi, ← MeasureTheory.integral_const_mul]
    have hcF : Continuous fun θ : ℝ => F θ ^ 2 := hF.pow 2
    have hcG : Continuous fun θ : ℝ => G θ ^ 2 := hG.pow 2
    refine MeasureTheory.setIntegral_mono_on (hcF.intervalIntegrable _ _).1
      ((hcG.intervalIntegrable _ _).1.const_mul _) measurableSet_Ioc fun θ _ => h θ
  have hsq := Real.sqrt_le_sqrt hint
  rw [trigNorm, trigNorm]
  calc Real.sqrt (∫ θ in (-Real.pi)..Real.pi, F θ ^ 2)
      ≤ Real.sqrt (M ^ 2 * ∫ θ in (-Real.pi)..Real.pi, G θ ^ 2) := hsq
    _ = M * Real.sqrt (∫ θ in (-Real.pi)..Real.pi, G θ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

theorem trigNorm_deriv_le {D : ℕ} {F F' : ℝ → ℝ} (hF : RealTrigDeg D F)
    (hderiv : ∀ θ : ℝ, HasDerivAt F (F' θ) θ) : trigNorm F' ≤ (D : ℝ) * trigNorm F := by
  have hbase := hF.integral_deriv_sq_le hderiv
  have hsq := Real.sqrt_le_sqrt hbase
  rw [trigNorm, trigNorm]
  calc Real.sqrt (∫ θ in (-Real.pi)..Real.pi, F' θ ^ 2)
      ≤ Real.sqrt ((D : ℝ) ^ 2 * ∫ θ in (-Real.pi)..Real.pi, F θ ^ 2) := hsq
    _ = (D : ℝ) * Real.sqrt (∫ θ in (-Real.pi)..Real.pi, F θ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg D)]


/-! ## The Cayley transport operator on angular profiles -/

/-- The Cayley transport of an angular profile: the profile of the derivative in the spectral
variable. -/
def trigCayleyStep (a : ℝ) (F F' : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (1 / a) * (-(1 / 2) * Real.sin θ * F θ + (1 + Real.cos θ) * F' θ)

theorem realTrigDeg_trigCayleyStep {D : ℕ} (a : ℝ) {F F' : ℝ → ℝ}
    (hF : RealTrigDeg D F) (hderiv : ∀ θ : ℝ, HasDerivAt F (F' θ) θ) :
    RealTrigDeg (D + 1) (trigCayleyStep a F F') := by
  have hF' : RealTrigDeg D F' := hF.deriv hderiv
  have h1 : RealTrigDeg (D + 1) (fun θ => (-(1 / 2) * (1 / a)) * (Real.sin θ * F θ)) :=
    (hF.mul_sin).smul _
  have h2 : RealTrigDeg (D + 1) (fun θ => (1 / a) * F' θ) :=
    RealTrigDeg.mono (by omega) (hF'.smul (1 / a))
  have h3 : RealTrigDeg (D + 1) (fun θ => (1 / a) * (Real.cos θ * F' θ)) :=
    (hF'.mul_cos).smul (1 / a)
  refine ((h1.add h2).add h3).congr fun θ => ?_
  rw [trigCayleyStep]
  ring

/-- **The Cayley transport raises the `L²` norm by at most `(1/a)(1/2 + 2D)`.** -/
theorem trigNorm_trigCayleyStep_le {D : ℕ} {a : ℝ} (ha : 0 < a) {F F' : ℝ → ℝ}
    (hF : RealTrigDeg D F) (hderiv : ∀ θ : ℝ, HasDerivAt F (F' θ) θ) :
    trigNorm (trigCayleyStep a F F') ≤ (1 / a) * (1 / 2 + 2 * (D : ℝ)) * trigNorm F := by
  have hF' : RealTrigDeg D F' := hF.deriv hderiv
  have hFc : Continuous F := hF.continuous
  have hF'c : Continuous F' := hF'.continuous
  have hA : Continuous fun θ : ℝ => (1 / a) * (-(1 / 2) * Real.sin θ * F θ) := by
    exact continuous_const.mul (((continuous_const.mul Real.continuous_sin)).mul hFc)
  have hB : Continuous fun θ : ℝ => (1 / a) * ((1 + Real.cos θ) * F' θ) := by
    exact continuous_const.mul (((continuous_const.add Real.continuous_cos)).mul hF'c)
  have hsplit : trigCayleyStep a F F' = fun θ => (1 / a) * (-(1 / 2) * Real.sin θ * F θ)
      + (1 / a) * ((1 + Real.cos θ) * F' θ) := by
    funext θ
    rw [trigCayleyStep]
    ring
  rw [hsplit]
  refine le_trans (trigNorm_add_le hA hB) ?_
  have h1 : trigNorm (fun θ : ℝ => (1 / a) * (-(1 / 2) * Real.sin θ * F θ))
      ≤ (1 / (2 * a)) * trigNorm F := by
    refine trigNorm_le_of_sq_le (by positivity) hA hFc fun θ => ?_
    have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hs2 : Real.sin θ ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
    have hane : a ≠ 0 := ne_of_gt ha
    have hFsq : (0 : ℝ) ≤ F θ ^ 2 := sq_nonneg _
    have hexp : ((1 / a) * (-(1 / 2) * Real.sin θ * F θ)) ^ 2
        = (1 / (2 * a)) ^ 2 * (Real.sin θ ^ 2 * F θ ^ 2) := by
      field_simp
    rw [hexp]
    have hnn : (0 : ℝ) ≤ (1 / (2 * a)) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hs2 hFsq, hnn]
  have h2 : trigNorm (fun θ : ℝ => (1 / a) * ((1 + Real.cos θ) * F' θ))
      ≤ (2 / a) * trigNorm F' := by
    refine trigNorm_le_of_sq_le (by positivity) hB hF'c fun θ => ?_
    have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    obtain ⟨hc1, hc2⟩ := abs_le.mp hc
    have hcsq : (1 + Real.cos θ) ^ 2 ≤ 4 := by nlinarith
    have hane : a ≠ 0 := ne_of_gt ha
    have hFsq : (0 : ℝ) ≤ F' θ ^ 2 := sq_nonneg _
    have hexp : ((1 / a) * ((1 + Real.cos θ) * F' θ)) ^ 2
        = (1 / a) ^ 2 * ((1 + Real.cos θ) ^ 2 * F' θ ^ 2) := by
      ring
    have hexp2 : (2 / a) ^ 2 * F' θ ^ 2 = (1 / a) ^ 2 * (4 * F' θ ^ 2) := by
      field_simp
      ring
    rw [hexp, hexp2]
    have hnn : (0 : ℝ) ≤ (1 / a) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hcsq hFsq, hnn]
  have h3 : trigNorm F' ≤ (D : ℝ) * trigNorm F := trigNorm_deriv_le hF hderiv
  have hn : 0 ≤ trigNorm F := trigNorm_nonneg F
  have ha2 : (0 : ℝ) < 2 / a := by positivity
  have h4 : (2 / a) * trigNorm F' ≤ (2 / a) * ((D : ℝ) * trigNorm F) :=
    mul_le_mul_of_nonneg_left h3 ha2.le
  have hane : a ≠ 0 := ne_of_gt ha
  have hid : (1 / (2 * a)) * trigNorm F + (2 / a) * ((D : ℝ) * trigNorm F)
      = (1 / a) * (1 / 2 + 2 * (D : ℝ)) * trigNorm F := by
    field_simp
  linarith [h1, h2, h4, hid.le, hid.ge]


/-! ## Iterating the Cayley transport -/

theorem hasDerivAt_re {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (h : HasDerivAt g g' x) :
    HasDerivAt (fun t => (g t).re) g'.re x := by
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  simp only [Function.comp_def, Complex.reCLM_apply] at h2
  exact h2

/-- A real trigonometric polynomial is differentiable. -/
theorem RealTrigDeg.hasDerivAt {D : ℕ} {F : ℝ → ℝ} (hF : RealTrigDeg D F) (θ : ℝ) :
    HasDerivAt F (_root_.deriv F θ) θ := by
  obtain ⟨f, hsupp, hval⟩ := hF
  have heq : F = fun u => (trigExp D f u).re := by
    funext u
    rw [← hval u, Complex.ofReal_re]
  have hd : HasDerivAt F ((trigExp D (fun k => f k * ((k : ℂ) * Complex.I)) θ).re) θ := by
    rw [heq]
    exact hasDerivAt_re (hasDerivAt_trigExp D f θ)
  exact hd.differentiableAt.hasDerivAt

theorem RealTrigDeg.deriv_mem {D : ℕ} {F : ℝ → ℝ} (hF : RealTrigDeg D F) :
    RealTrigDeg D (_root_.deriv F) := hF.deriv fun θ => hF.hasDerivAt θ

/-- The `m`-fold Cayley transport of an angular profile. -/
def trigCayleyIter (a : ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, F => F
  | (m + 1), F => trigCayleyStep a (trigCayleyIter a m F) (deriv (trigCayleyIter a m F))

theorem trigCayleyIter_zero (a : ℝ) (F : ℝ → ℝ) : trigCayleyIter a 0 F = F := rfl

theorem trigCayleyIter_succ (a : ℝ) (m : ℕ) (F : ℝ → ℝ) :
    trigCayleyIter a (m + 1) F
      = trigCayleyStep a (trigCayleyIter a m F) (deriv (trigCayleyIter a m F)) := rfl

theorem realTrigDeg_trigCayleyIter {a : ℝ} :
    ∀ (m D : ℕ) {F : ℝ → ℝ}, RealTrigDeg D F → RealTrigDeg (D + m) (trigCayleyIter a m F) := by
  intro m
  induction m with
  | zero =>
    intro D F hF
    rw [trigCayleyIter_zero]
    exact RealTrigDeg.mono (by omega) hF
  | succ m ih =>
    intro D F hF
    have hiter := ih D hF
    rw [trigCayleyIter_succ]
    exact realTrigDeg_trigCayleyStep a hiter (fun θ => hiter.hasDerivAt θ)

/-- **The iterated Cayley transport bound.** -/
theorem trigNorm_trigCayleyIter_le {a : ℝ} (ha : 0 < a) :
    ∀ (m D : ℕ) {F : ℝ → ℝ}, RealTrigDeg D F →
      trigNorm (trigCayleyIter a m F)
        ≤ (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ)))) * trigNorm F := by
  intro m
  induction m with
  | zero =>
    intro D F hF
    rw [trigCayleyIter_zero]
    simp
  | succ m ih =>
    intro D F hF
    have hiter := realTrigDeg_trigCayleyIter (a := a) m D hF
    have hstep := trigNorm_trigCayleyStep_le ha hiter (fun θ => hiter.hasDerivAt θ)
    have hcast : ((D + m : ℕ) : ℝ) = (D : ℝ) + (m : ℝ) := by push_cast; ring
    rw [hcast] at hstep
    have hprev := ih D hF
    have hcoef : (0 : ℝ) ≤ (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (m : ℝ))) := by
      have h1 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
      have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h3 : (0 : ℝ) < 1 / a := by positivity
      nlinarith
    rw [trigCayleyIter_succ, Finset.prod_range_succ]
    calc trigNorm (trigCayleyStep a (trigCayleyIter a m F) (deriv (trigCayleyIter a m F)))
        ≤ (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (m : ℝ))) * trigNorm (trigCayleyIter a m F) :=
          hstep
      _ ≤ (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (m : ℝ)))
            * ((∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ)))) * trigNorm F) :=
          mul_le_mul_of_nonneg_left hprev hcoef
      _ = (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))))
            * ((1 / a) * (1 / 2 + 2 * ((D : ℝ) + (m : ℝ)))) * trigNorm F := by ring


/-! ## Basic membership -/

theorem expMon_add_neg (j : ℤ) (θ : ℝ) :
    expMon j θ + expMon (-j) θ = 2 * ((Real.cos ((j : ℝ) * θ) : ℝ) : ℂ) := by
  have h1 : expMon j θ = Complex.exp ((((j : ℝ) * θ : ℝ)) * Complex.I) := by
    rw [expMon]
    congr 1
    push_cast
    ring
  have h2 : expMon (-j) θ = Complex.exp (((-((j : ℝ) * θ) : ℝ)) * Complex.I) := by
    rw [expMon]
    congr 1
    push_cast
    ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I,
    show (((-((j : ℝ) * θ)) : ℝ) : ℂ) = -((((j : ℝ) * θ) : ℝ) : ℂ) by push_cast; ring,
    Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

theorem RealTrigDeg.sum {D : ℕ} {ι : Type*} (s : Finset ι) (G : ι → ℝ → ℝ)
    (hG : ∀ i ∈ s, RealTrigDeg D (G i)) : RealTrigDeg D (fun θ => ∑ i ∈ s, G i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun k _ => rfl, fun θ => ?_⟩
    simp [trigExp]
  | insert i s hi ih =>
    have hGi : RealTrigDeg D (G i) := hG i (Finset.mem_insert_self i s)
    have hrest : RealTrigDeg D (fun θ => ∑ j ∈ s, G j θ) :=
      ih fun j hj => hG j (Finset.mem_insert_of_mem hj)
    refine (hGi.add hrest).congr fun θ => ?_
    rw [Finset.sum_insert hi]

theorem realTrigDeg_cos_natMul (j : ℕ) : RealTrigDeg j (fun θ => Real.cos ((j : ℝ) * θ)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨fun k => if k = 0 then 1 else 0, ?_, fun θ => ?_⟩
    · intro k hk
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0] at hk
        simp at hk
      show (if k = 0 then (1 : ℂ) else 0) = 0
      rw [if_neg hk0]
    · rw [trigExp]
      simp [expMon]
  · have hjpos : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
    refine ⟨fun k => if k = (j : ℤ) then (1 / 2 : ℂ)
      else if k = -(j : ℤ) then (1 / 2 : ℂ) else 0, ?_, fun θ => ?_⟩
    · intro k hk
      have h1 : k ≠ (j : ℤ) := by
        intro h
        rw [h] at hk
        rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (j : ℤ))] at hk
        omega
      have h2 : k ≠ -(j : ℤ) := by
        intro h
        rw [h] at hk
        rw [abs_of_nonpos (by omega : -(j : ℤ) ≤ 0)] at hk
        omega
      show (if k = (j : ℤ) then (1 / 2 : ℂ)
        else if k = -(j : ℤ) then (1 / 2 : ℂ) else 0) = 0
      rw [if_neg h1, if_neg h2]
    · have hne : (j : ℤ) ≠ -(j : ℤ) := by omega
      have hsub : ({(j : ℤ), -(j : ℤ)} : Finset ℤ) ⊆ Finset.Icc (-(j : ℤ)) (j : ℤ) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        simp only [Finset.mem_Icc]
        rcases hk with rfl | rfl <;> omega
      rw [trigExp, ← Finset.sum_subset hsub ?_]
      · rw [Finset.sum_pair hne, if_pos rfl, if_neg hne.symm, if_pos rfl]
        have hsum := expMon_add_neg (j : ℤ) θ
        have hcast : (((j : ℤ) : ℝ)) = (j : ℝ) := by push_cast; ring
        rw [hcast] at hsum
        rw [show (1 / 2 : ℂ) * expMon (j : ℤ) θ + (1 / 2 : ℂ) * expMon (-(j : ℤ)) θ
            = (1 / 2 : ℂ) * (expMon (j : ℤ) θ + expMon (-(j : ℤ)) θ) by ring, hsum]
        ring
      · intro k _ hknot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hknot
        rw [if_neg hknot.1, if_neg hknot.2, zero_mul]


/-! ## Boundedness -/

theorem RealTrigDeg.exists_bound {D : ℕ} {F : ℝ → ℝ} (hF : RealTrigDeg D F) :
    ∃ M : ℝ, ∀ θ : ℝ, |F θ| ≤ M := by
  obtain ⟨f, _, hrep⟩ := hF
  refine ⟨∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), ‖f k‖, fun θ => ?_⟩
  have habs : |F θ| = ‖((F θ : ℝ) : ℂ)‖ := (Complex.norm_real (F θ)).symm
  rw [habs, hrep θ, trigExp]
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_expMon, mul_one]

end GaloisForLFunctions.HTGeometry

end
