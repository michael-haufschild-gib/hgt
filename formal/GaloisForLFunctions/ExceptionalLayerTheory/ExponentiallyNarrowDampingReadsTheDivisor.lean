import GaloisForLFunctions.ExceptionalLayerTheory.DampingFiltersReadTheExceptionalDivisor

/-!
# Exceptional detection in exponentially narrow damping windows

An exponential decrease in damping spacing attenuates a degree-`d` filter by
the `d`th power of the spacing. Supercritical Gaussian growth pays this loss
when its rate exceeds the product of degree and contraction speed.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

open EulerFETransportTheory

/-- The exponentially contracting spacing between logarithmic damping samples. -/
def contractingDampingStep (κ t : ℝ) : ℝ := Real.exp (-κ * t)

/-- The Gaussian mode after the finite filter's contraction loss. -/
def attenuatedGaussianMode (d : ℕ) (κ : ℝ) (ρ : ℂ) (σ a t : ℝ) : ℂ :=
  (contractingDampingStep κ t : ℂ) ^ d *
    gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I))

private theorem norm_attenuatedGaussianMode_inv (d : ℕ) (κ : ℝ)
    (ρ : ℂ) (σ a t : ℝ) :
    ‖(attenuatedGaussianMode d κ ρ σ a t)⁻¹‖ =
      Real.exp ((d : ℝ) * κ * t) *
        ‖(gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)))⁻¹‖ := by
  rw [attenuatedGaussianMode, mul_inv, norm_mul, norm_inv, norm_pow,
    contractingDampingStep, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul, ← Real.exp_neg]
  rw [show -((d : ℝ) * (-κ * t)) = (d : ℝ) * κ * t by ring]

private theorem exists_attenuatedGaussianMode_inverse_bound (d : ℕ) (κ : ℝ)
    (ρ : ℂ) (σ a : ℝ) :
    ∃ (D : ℝ) (M : ℕ), 0 ≤ D ∧ ∀ t : ℝ, |ρ.im| + 2 ≤ t →
      ‖(attenuatedGaussianMode d κ ρ σ a t)⁻¹‖ ≤
        D * t ^ M * Real.exp (-((gaussianObservationRate ρ σ a - d * κ) * t)) := by
  obtain ⟨C, D, N, M, _, hD, hb⟩ := exists_gaussianMode_exponential_bounds ρ σ
  refine ⟨D, M, hD, fun t ht => ?_⟩
  rw [norm_attenuatedGaussianMode_inv]
  calc
    _ ≤ Real.exp ((d : ℝ) * κ * t) *
        (D * t ^ M * Real.exp (-(gaussianObservationRate ρ σ a * t))) :=
      mul_le_mul_of_nonneg_left (hb t ht a).2 (Real.exp_pos _).le
    _ = _ := by
      rw [show -((gaussianObservationRate ρ σ a - d * κ) * t) =
        (d : ℝ) * κ * t + -(gaussianObservationRate ρ σ a * t) by ring,
        Real.exp_add]
      ring

/-- Gaussian growth survives contraction above the degree-weighted rate loss,
despite the polynomial Gamma factors. -/
theorem tendsto_attenuatedGaussianMode_inv_zero (d : ℕ) (κ : ℝ)
    (ρ : ℂ) (σ a : ℝ) (hr : (d : ℝ) * κ < gaussianObservationRate ρ σ a) :
    Tendsto (fun t : ℝ => (attenuatedGaussianMode d κ ρ σ a t)⁻¹) atTop (𝓝 0) := by
  obtain ⟨D, M, _, hb⟩ := exists_attenuatedGaussianMode_inverse_bound d κ ρ σ a
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp (sub_pos.mpr hr)
  filter_upwards [eventually_ge_atTop (|ρ.im| + 2)] with t ht
  exact hb t ht

/-- Above the degree-weighted contraction threshold, even the attenuated
mode has norm tending to infinity. -/
theorem tendsto_norm_attenuatedGaussianMode_atTop (d : ℕ) {κ : ℝ}
    (hκ : 0 ≤ κ) (ρ : ℂ) (σ a : ℝ)
    (hr : (d : ℝ) * κ < gaussianObservationRate ρ σ a) :
    Tendsto (fun t : ℝ => ‖attenuatedGaussianMode d κ ρ σ a t‖) atTop atTop := by
  have hrate : 0 < gaussianObservationRate ρ σ a :=
    (mul_nonneg (Nat.cast_nonneg d) hκ).trans_lt hr
  have hK := tendsto_norm_gaussianMode_atTop_of_positive_rate ρ σ a hrate
  have hi := (tendsto_attenuatedGaussianMode_inv_zero d κ ρ σ a hr).norm
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < ‖(attenuatedGaussianMode d κ ρ σ a t)⁻¹‖ := by
    filter_upwards [hK.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    apply norm_pos_iff.mpr
    apply inv_ne_zero
    exact mul_ne_zero
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)))
      (norm_pos_iff.mp ht)
  have hright := tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [norm_zero] using hi, hpos⟩
  simpa only [norm_inv, inv_inv, Function.comp_def] using
    tendsto_inv_nhdsGT_zero.comp hright

private theorem tendsto_logDeriv_div_attenuatedGaussianMode (F : Finset XiZeroCopy)
    {θ σ a : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hgap : θ < σ)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (d : ℕ) (κ : ℝ) (ρ : ℂ) (hr : (d : ℝ) * κ < gaussianObservationRate ρ σ a) :
    Tendsto (fun t : ℝ => logDeriv riemannZeta ((σ : ℂ) + t * I) /
      attenuatedGaussianMode d κ ρ σ a t) atTop (𝓝 0) := by
  obtain ⟨H, C, D, hH, _, hD, hb⟩ := finite_layer_prime_current_bounds F hσ hσ1 hgap hrest
  obtain ⟨B, M, hB, hmode⟩ := exists_attenuatedGaussianMode_inverse_bound d κ ρ σ a
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := D * B) (N := M + 1) (sub_pos.mpr hr)
  filter_upwards [eventually_ge_atTop (max H (|ρ.im| + 2))] with t ht
  have htH : H ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := by linarith only [htH, hH]
  have hlarge : |ρ.im| + 2 ≤ t := (le_max_right _ _).trans ht
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (D * t) * (B * t ^ M *
        Real.exp (-((gaussianObservationRate ρ σ a - d * κ) * t))) :=
      mul_le_mul (hb t htH).1 (hmode t hlarge) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

private theorem tendsto_contractingDampingStep {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (contractingDampingStep κ) atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp (-κ * t)) atTop (𝓝 0)
  simpa only [pow_zero, one_mul, neg_mul] using
    HTGeometry.tendsto_pow_mul_exp_neg_scaled 0 hκ

private theorem tendsto_exp_difference_div_contractingStep {κ : ℝ}
    (hκ : 0 < κ) (z w : ℂ) :
    Tendsto (fun t : ℝ =>
      (Complex.exp ((contractingDampingStep κ t : ℂ) * z) -
        Complex.exp ((contractingDampingStep κ t : ℂ) * w)) /
          (contractingDampingStep κ t : ℂ)) atTop (𝓝 (z - w)) := by
  have hderiv := (((hasDerivAt_id (x := (0 : ℂ))).mul_const z).cexp.sub
    (((hasDerivAt_id (x := (0 : ℂ))).mul_const w).cexp))
  have hstep : Tendsto (fun t : ℝ => (contractingDampingStep κ t : ℂ)) atTop
      (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_contractingDampingStep hκ)
    · exact Eventually.of_forall fun t => by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero,
          contractingDampingStep]
          using Real.exp_ne_zero (-κ * t)
  have hs := hderiv.tendsto_slope_zero.comp hstep
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_add, zero_mul, mul_zero,
    Complex.exp_zero, one_mul, mul_one, sub_self, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hs

private theorem divisorDampingFilter_degree (F : Finset XiZeroCopy)
    (ρ : ℂ) (β h : ℝ) :
    (divisorDampingFilter F ρ β h).natDegree =
      1 + (F.filter (fun q => xiZero q ≠ ρ)).card := by
  classical
  rw [divisorDampingFilter, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
    (Finset.prod_ne_zero_iff.mpr (fun q _ => Polynomial.X_sub_C_ne_zero _)),
    Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_prod_of_monic _ _ (fun q _ => Polynomial.monic_X_sub_C _)]
  simp

private theorem tendsto_polynomial_product_coeff {ι : Type*} {l : Filter ι}
    {P Q : ι → Polynomial ℂ} {P₀ Q₀ : Polynomial ℂ}
    (hP : ∀ j : ℕ, Tendsto (fun t => (P t).coeff j) l (𝓝 (P₀.coeff j)))
    (hQ : ∀ j : ℕ, Tendsto (fun t => (Q t).coeff j) l (𝓝 (Q₀.coeff j)))
    (j : ℕ) : Tendsto (fun t => (P t * Q t).coeff j) l (𝓝 ((P₀ * Q₀).coeff j)) := by
  simp only [Polynomial.coeff_mul]
  exact tendsto_finsetSum _ fun k _ => (hP k.1).mul (hQ k.2)

private theorem tendsto_damping_linear_factor_coeff {κ : ℝ} (hκ : 0 < κ)
    (z : ℂ) (j : ℕ) :
    Tendsto (fun t : ℝ => (Polynomial.X - Polynomial.C
      (Complex.exp ((contractingDampingStep κ t : ℂ) * z))).coeff j) atTop
      (𝓝 ((Polynomial.X - Polynomial.C (1 : ℂ)).coeff j)) := by
  have hz : Tendsto (fun t : ℝ =>
      Complex.exp ((contractingDampingStep κ t : ℂ) * z)) atTop (𝓝 1) := by
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_contractingDampingStep hκ)).mul_const z
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using
      Complex.continuous_exp.continuousAt.tendsto.comp hh
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C]
  by_cases hj : j = 0
  · simp only [hj, ite_true]
    exact tendsto_const_nhds.sub hz
  · simp only [hj, ite_false, sub_zero]
    exact tendsto_const_nhds

private theorem tendsto_divisorDampingFilter_coeff (F : Finset XiZeroCopy)
    (ρ : ℂ) (β : ℝ) {κ : ℝ} (hκ : 0 < κ) (j : ℕ) :
    Tendsto (fun t : ℝ =>
      (divisorDampingFilter F ρ β (contractingDampingStep κ t)).coeff j) atTop
      (𝓝 ((divisorDampingFilter F ρ β 0).coeff j)) := by
  classical
  have hprod (S : Finset XiZeroCopy) : ∀ k : ℕ,
      Tendsto (fun t : ℝ => (∏ q ∈ S, (Polynomial.X - Polynomial.C
        (Complex.exp ((contractingDampingStep κ t : ℂ) * (xiZero q - β))))).coeff k) atTop
        (𝓝 ((∏ _q ∈ S, (Polynomial.X - Polynomial.C (1 : ℂ))).coeff k)) := by
    induction S using Finset.induction_on with
    | empty => intro k; simp only [Finset.prod_empty]; exact tendsto_const_nhds
    | @insert q S hq ih =>
      intro k
      simp only [Finset.prod_insert hq]
      exact tendsto_polynomial_product_coeff
        (tendsto_damping_linear_factor_coeff hκ (xiZero q - β)) ih k
  simpa only [divisorDampingFilter, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using
    tendsto_polynomial_product_coeff (tendsto_damping_linear_factor_coeff hκ (1 - β))
      (hprod (F.filter (fun q => xiZero q ≠ ρ))) j

/-- Dividing by the exact contraction order exposes the product of differences
between the selected zero and the pole and every deleted zero copy. -/
theorem tendsto_divisorDampingFilter_scaled_value (F : Finset XiZeroCopy)
    (ρ : ℂ) (β : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ =>
      (divisorDampingFilter F ρ β (contractingDampingStep κ t)).eval
        (Complex.exp ((contractingDampingStep κ t : ℂ) * (ρ - β))) /
          (contractingDampingStep κ t : ℂ) ^
            (1 + (F.filter (fun q => xiZero q ≠ ρ)).card)) atTop
      (𝓝 ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q))) := by
  classical
  have hfactor (z : ℂ) := tendsto_exp_difference_div_contractingStep hκ (ρ - β) (z - β)
  have hfactor' (z : ℂ) : Tendsto (fun t : ℝ =>
      (Complex.exp ((contractingDampingStep κ t : ℂ) * (ρ - β)) -
        Complex.exp ((contractingDampingStep κ t : ℂ) * (z - β))) /
          (contractingDampingStep κ t : ℂ)) atTop (𝓝 (ρ - z)) := by
    have he : (ρ - (β : ℂ)) - (z - β) = ρ - z := by ring
    simpa only [he] using hfactor z
  have hlim := (hfactor' 1).mul
    (tendsto_finsetProd (F.filter (fun q => xiZero q ≠ ρ)) fun q _ => hfactor' (xiZero q))
  apply hlim.congr
  intro t
  simp only [divisorDampingFilter, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_div_distrib, Finset.prod_const, ← mul_div_mul_comm, pow_add, pow_one]

/-- The complete arithmetic current survives an exponentially contracting
damping grid after division by its exact attenuation. -/
theorem contracting_prime_filter_reads_selected_zero (F : Finset XiZeroCopy)
    {θ σ β a κ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hgap : θ < σ)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (hσβ : σ ≤ β) (ha : 0 < a) (hκ : 0 < κ) (ρ : ℂ)
    (hr : ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card : ℕ) : ℝ) * κ <
      gaussianObservationRate ρ σ a) :
    Tendsto (fun t : ℝ =>
      primeDampingFilter (divisorDampingFilter F ρ β (contractingDampingStep κ t))
        σ β a (contractingDampingStep κ t) t /
          attenuatedGaussianMode (1 + (F.filter (fun q => xiZero q ≠ ρ)).card)
            κ ρ σ a t) atTop
      (𝓝 (-((F.filter (fun q => xiZero q = ρ)).card : ℂ) *
        ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q)))) := by
  classical
  let d : ℕ := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let h : ℝ → ℝ := contractingDampingStep κ
  let P : ℝ → Polynomial ℂ := fun t => divisorDampingFilter F ρ β (h t)
  let D : ℝ → ℂ := attenuatedGaussianMode d κ ρ σ a
  let m : ℂ := (F.filter (fun q => xiZero q = ρ)).card
  let E : ℝ → ℂ := fun t => ∑ j ∈ Finset.range (d + 1),
    (P t).coeff j * (dampingSampleWeight β (h t) ((σ : ℂ) + t * I) j *
      exceptionalGaussianExpansionError F ((σ : ℂ) + t * I)
        (geometricGaussianDamping a (h t) t j))
  have hh (t : ℝ) : 0 < h t := Real.exp_pos _
  have hdegree (t : ℝ) : (P t).natDegree = d := divisorDampingFilter_degree F ρ β (h t)
  have hcoeff := tendsto_divisorDampingFilter_coeff F ρ β hκ
  have hDinv : Tendsto (fun t => (D t)⁻¹) atTop (𝓝 0) :=
    tendsto_attenuatedGaussianMode_inv_zero d κ ρ σ a hr
  have hDnorm : Tendsto (fun t => ‖D t‖) atTop atTop :=
    tendsto_norm_attenuatedGaussianMode_atTop d hκ.le ρ σ a hr
  have hEterm (j : ℕ) : Tendsto (fun t : ℝ =>
      (P t).coeff j * (dampingSampleWeight β (h t) ((σ : ℂ) + t * I) j *
        exceptionalGaussianExpansionError F ((σ : ℂ) + t * I)
          (geometricGaussianDamping a (h t) t j))) atTop (𝓝 0) := by
    have he := tendsto_variable_geometric_expansion_error F hσ hσ1 hgap hrest ha
      (Eventually.of_forall fun t => (hh t).le) j
    have hw := tendsto_bounded_weight_mul_zero
      (fun t => norm_dampingSampleWeight_le_one hσβ (hh t).le t j) he
    simpa only [mul_zero] using (hcoeff j).mul hw
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.range (d + 1)) (fun j _ => hEterm j)
  have hEdiv : Tendsto (fun t => E t / D t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hE.mul hDinv
  have hlog := tendsto_logDeriv_div_attenuatedGaussianMode F hσ hσ1 hgap hrest d κ ρ hr
  have hLterm (j : ℕ) : Tendsto (fun t : ℝ =>
      (P t).coeff j * (dampingSampleWeight β (h t) ((σ : ℂ) + t * I) j *
        (Real.exp (-geometricGaussianDamping a (h t) t j) : ℂ) *
          (logDeriv riemannZeta ((σ : ℂ) + t * I) / D t))) atTop (𝓝 0) := by
    have hw (t : ℝ) : ‖dampingSampleWeight β (h t) ((σ : ℂ) + t * I) j *
        (Real.exp (-geometricGaussianDamping a (h t) t j) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-geometricGaussianDamping a (h t) t j) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos _).le)
      exact (mul_le_mul (norm_dampingSampleWeight_le_one hσβ (hh t).le t j) he
        (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
    simpa only [mul_zero] using (hcoeff j).mul (tendsto_bounded_weight_mul_zero hw hlog)
  have hL : Tendsto (fun t => continuedDampingCorrection (P t) σ β a (h t) t / D t)
      atTop (𝓝 0) := by
    have hs := tendsto_finsetSum (Finset.range (d + 1)) (fun j _ => hLterm j)
    simp only [Finset.sum_const_zero] at hs
    apply hs.congr
    intro t
    rw [continuedDampingCorrection, hdegree, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hselected := (tendsto_divisorDampingFilter_scaled_value F ρ β hκ).const_mul m
  have hfinal := (hEdiv.sub hL).sub hselected
  simp only [sub_zero, zero_sub] at hfinal
  have hanswer : Tendsto (fun t : ℝ => primeDampingFilter (P t) σ β a (h t) t / D t)
      atTop (𝓝 (-(m * ((ρ - 1) *
        ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q))))) := by
    apply hfinal.congr'
    filter_upwards [hDnorm.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    have hDne : D t ≠ 0 := norm_pos_iff.mp ht
    have hKne : gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)) ≠ 0 :=
      (mul_ne_zero_iff.mp hDne).2
    have hexp := primeDampingFilter_expansion (P t) F σ β a (h t) t
    rw [divisorDampingFilter_pole, zero_mul, sub_zero,
      filtered_divisor_eq_selected_mode F (P t) σ β a (h t) t ρ
        (fun q hq hne => divisorDampingFilter_kills F ρ β (h t) hq hne), hdegree] at hexp
    have hexp' : primeDampingFilter (P t) σ β a (h t) t +
        continuedDampingCorrection (P t) σ β a (h t) t +
          m * (P t).eval (Complex.exp ((h t : ℂ) * (ρ - β))) *
            gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)) = E t := by
      simpa only [E, m, mul_assoc] using hexp
    have heq := congrArg (fun z : ℂ => z / D t) hexp'
    simp only [add_div] at heq
    have hcancel : m * (P t).eval (Complex.exp ((h t : ℂ) * (ρ - β))) *
        gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)) / D t =
          m * ((P t).eval (Complex.exp ((h t : ℂ) * (ρ - β))) / (h t : ℂ) ^ d) := by
      change _ / ((h t : ℂ) ^ d *
        gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I))) = _
      generalize hk : gaussianMBKernel (Real.exp (-a * t))
        (ρ - ((σ : ℂ) + t * I)) = K at hKne ⊢
      field_simp [hKne, pow_ne_zero d (Complex.ofReal_ne_zero.mpr (hh t).ne')]
    rw [hcancel] at heq
    change E t / D t - continuedDampingCorrection (P t) σ β a (h t) t / D t -
      m * ((P t).eval (Complex.exp ((h t : ℂ) * (ρ - β))) / (h t : ℂ) ^ d) = _
    rw [← heq]
    ring
  simpa only [P, D, d, h, m, neg_mul] using hanswer

/-- An actual finite exceptional layer remains arithmetically visible in
exponentially narrowing damping windows. Every top zero gives a nonzero
divisor-separation limit and all-height growth whenever the observation rate
exceeds the degree-weighted contraction rate. -/
theorem not_asymptoticAbscissaLaw_has_contracting_prime_filters :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ q ∈ F, (xiZero q).re = β →
          let d := 1 + (F.filter (fun p => xiZero p ≠ xiZero q)).card
          let c : ℂ := -((F.filter (fun p => xiZero p = xiZero q)).card : ℂ) *
            ((xiZero q - 1) *
              ∏ p ∈ F.filter (fun p => xiZero p ≠ xiZero q), (xiZero q - xiZero p))
          c ≠ 0 ∧ ∀ a : ℝ, 0 < a → ∀ κ : ℝ, 0 < κ →
            (d : ℝ) * κ < gaussianObservationRate (xiZero q) σ a →
              Tendsto (fun t : ℝ =>
                primeDampingFilter
                  (divisorDampingFilter F (xiZero q) β (contractingDampingStep κ t))
                    σ β a (contractingDampingStep κ t) t /
                      attenuatedGaussianMode d κ (xiZero q) σ a t) atTop (𝓝 c) ∧
              Tendsto (fun t : ℝ =>
                ‖primeDampingFilter
                  (divisorDampingFilter F (xiZero q) β (contractingDampingStep κ t))
                    σ β a (contractingDampingStep κ t) t‖) atTop atTop := by
  classical
  intro hnot
  obtain ⟨F, θ, σ, β, hθ, hgap, hσβ, hβ1, htop, hmax, hrest, _⟩ :=
    not_asymptoticAbscissaLaw_has_escaping_layer_profile hnot
  have hσ : 1 / 2 < σ := by linarith only [hθ, hgap]
  have hσ1 : σ < 1 := hσβ.trans hβ1
  have hall : ∀ q : XiZeroCopy, (xiZero q).re ≤ β := by
    intro q
    by_cases hq : q ∈ F
    · exact hmax q hq
    · exact (hrest q hq).trans (hgap.trans hσβ).le
  refine ⟨F, σ, β, hσ, hσβ, hβ1, htop, hall, ?_⟩
  intro q hq hqβ
  dsimp only
  have hm : 0 < (F.filter (fun p => xiZero p = xiZero q)).card :=
    Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
  have hpole : xiZero q - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hr := congrArg Complex.re he
    rw [hqβ, Complex.one_re] at hr
    exact (ne_of_lt hβ1) hr
  have hprod : (∏ p ∈ F.filter (fun p => xiZero p ≠ xiZero q),
      (xiZero q - xiZero p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hp).2.symm
  have hc : -((F.filter (fun p => xiZero p = xiZero q)).card : ℂ) *
      ((xiZero q - 1) * ∏ p ∈ F.filter (fun p => xiZero p ≠ xiZero q),
        (xiZero q - xiZero p)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)))
      (mul_ne_zero hpole hprod)
  refine ⟨hc, ?_⟩
  intro a ha κ hκ hr
  have hlim := contracting_prime_filter_reads_selected_zero F hσ hσ1 hgap hrest
    hσβ.le ha hκ (xiZero q) hr
  exact ⟨hlim, norm_tendsto_atTop_of_ratio hc hlim
    (tendsto_norm_attenuatedGaussianMode_atTop _ hκ.le (xiZero q) σ a hr)⟩

#print axioms tendsto_attenuatedGaussianMode_inv_zero
#print axioms tendsto_norm_attenuatedGaussianMode_atTop
#print axioms tendsto_divisorDampingFilter_scaled_value
#print axioms contracting_prime_filter_reads_selected_zero
#print axioms not_asymptoticAbscissaLaw_has_contracting_prime_filters

end GaloisForLFunctions.ExceptionalLayerTheory
