import GaloisForLFunctions.SignedArithmeticEnergyIncidence.PaleyWienerSourcesPayAtTheNyquistDensity

/-!
# Off-line configurations are paid by their kernel Gram

On a companion lattice `t₀ + hℤ` at or above the Nyquist density (`A h ≤ π`) the companion energy
of a Paley–Wiener source of aperture `A` is its completion norm, `Σ_k |f(t₀ + kh)|² = (2π/h)∫|F|²`
(`hasSum_sq_pwSource_lattice`).  The off-line depth of a finite configuration of clusters at
heights `t_j` with masses `w_j` is the polar charge `Σ_j w_j |f'(t_j)|² = Σ_j w_j |⟨F, K_j⟩|²` of
the derivative kernels `K_j(ξ) = iξ e^{it_jξ}` on `(−A, A)` (`pwDeriv_eq_integral_kernel`).  So the
signed floor of the whole configuration is a polar defect law (mechanism 22):

`Σ_j w_j |f'(t_j)|² ≤ Σ_k |f(t₀ + kh)|²` for every source of aperture `A`
`⟺` `Q(c) = Σ_{j,l} c̄_j c_l √(w_j w_l) S(t_j − t_l) ≤ (2π/h) Σ_j |c_j|²` for every `c`

(`pwConfiguration_pay_iff_gram`), where `S(u) = ∫_{−A}^{A} ξ² e^{iuξ} dξ` is the kernel Gram
(`integral_pwKernel_mul_conj`).  Sufficiency (`pwConfiguration_pay_of_gram`) pairs `F` with the
synthesis `Ψ = Σ_j c̄_j √w_j K_j` of the derivative values; necessity
(`gram_of_pwConfiguration_pay`) tests the synthesized density itself.  The criterion does not see
the companion offset `t₀`; for one cluster it is the Nyquist price `w A³h/(3π) ≤ 1`, and nearby
clusters pay jointly through the off-diagonal Gram entries.
-/

open MeasureTheory Complex Set Filter

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {F : ℝ → ℂ} {A : ℝ}

/-! ### Derivative kernels and their Gram -/

/-- The derivative kernel `K_τ(ξ) = iξ e^{iτξ}` on `(−A, A)`. -/
def pwKernel (A τ : ℝ) : ℝ → ℂ :=
  (Ioo (-A) A).indicator fun ξ => ((ξ : ℂ) * I) * exp (((τ * ξ : ℝ) : ℂ) * I)

/-- The kernel Gram `S(u) = ∫_{−A}^{A} ξ² e^{iuξ} dξ`. -/
def pwGram (A u : ℝ) : ℂ :=
  ∫ ξ in Ioo (-A) A, ((ξ ^ 2 : ℝ) : ℂ) * exp (((u * ξ : ℝ) : ℂ) * I)

/-- The configuration form `Q(c) = Σ_{j,l} c̄_j c_l √w_j √w_l S(t_j − t_l)`. -/
def configurationForm {J : Type*} [Fintype J] (A : ℝ) (t w : J → ℝ) (c : J → ℂ) : ℂ :=
  ∑ j, ∑ l, (starRingEnd ℂ) (c j) * c l *
    ((Real.sqrt (w j) * Real.sqrt (w l) : ℝ) : ℂ) * pwGram A (t j - t l)

theorem norm_pwKernel_le (hA : 0 ≤ A) (τ ξ : ℝ) : ‖pwKernel A τ ξ‖ ≤ A := by
  unfold pwKernel
  by_cases hξ : ξ ∈ Ioo (-A) A
  · rw [indicator_of_mem hξ, norm_mul, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, mul_one, mul_one]
    exact (abs_lt.mpr ⟨hξ.1, hξ.2⟩).le
  · rw [indicator_of_notMem hξ, norm_zero]; exact hA

theorem continuous_pwKernelProfile (τ : ℝ) :
    Continuous fun ξ : ℝ => ((ξ : ℂ) * I) * exp (((τ * ξ : ℝ) : ℂ) * I) := by fun_prop

theorem aestronglyMeasurable_pwKernel (A τ : ℝ) : AEStronglyMeasurable (pwKernel A τ) volume :=
  ((continuous_pwKernelProfile τ).aestronglyMeasurable).indicator measurableSet_Ioo

theorem memLp_pwKernel (A τ : ℝ) : MemLp (pwKernel A τ) 2 volume := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (-A) A)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  unfold pwKernel
  rw [memLp_indicator_iff_restrict measurableSet_Ioo]
  refine MemLp.of_bound (continuous_pwKernelProfile τ).aestronglyMeasurable A ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact ae_of_all _ fun ξ hξ => by
    rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, mul_one]
    exact (abs_lt.mpr ⟨hξ.1, hξ.2⟩).le

theorem pwKernel_eq_zero {τ ξ : ℝ} (hξ : ξ ∉ Ioo (-A) A) : pwKernel A τ ξ = 0 :=
  indicator_of_notMem hξ _

/-- A kernel against an integrable density is integrable. -/
theorem integrable_pwKernel_mul (hA : 0 ≤ A) (τ : ℝ) {G : ℝ → ℂ} (hG : Integrable G) :
    Integrable fun ξ => pwKernel A τ ξ * G ξ :=
  (hG.norm.const_mul A).mono' ((aestronglyMeasurable_pwKernel A τ).mul hG.1)
    (ae_of_all _ fun ξ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (norm_pwKernel_le hA τ ξ) (norm_nonneg _))

/-- Two kernels against each other are integrable. -/
theorem integrable_pwKernel_mul_conj (A τ σ : ℝ) :
    Integrable fun ξ => pwKernel A τ ξ * (starRingEnd ℂ) (pwKernel A σ ξ) :=
  (memLp_pwKernel A τ).integrable_mul ((memLp_pwKernel A σ).star)

/-- **The derivative is the kernel pairing**: `f'(τ) = ∫ K_τ F` for a density of aperture `A`. -/
theorem pwDeriv_eq_integral_kernel (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0) (τ : ℝ) :
    pwDeriv F τ = ∫ ξ : ℝ, pwKernel A τ ξ * F ξ := by
  unfold pwDeriv
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  by_cases hξ : ξ ∈ Ioo (-A) A
  · simp only [pwKernel, indicator_of_mem hξ]; ring
  · have : A ≤ |ξ| := by
      simp only [mem_Ioo, not_and_or, not_lt] at hξ
      rcases hξ with h | h
      · linarith [neg_le_abs ξ]
      · linarith [le_abs_self ξ]
    simp only [hsupp ξ this, pwKernel_eq_zero hξ, mul_zero, zero_mul]

/-- **The kernel Gram**: `∫ K_τ conj(K_σ) = S(τ − σ)`. -/
theorem integral_pwKernel_mul_conj (A τ σ : ℝ) :
    ∫ ξ : ℝ, pwKernel A τ ξ * (starRingEnd ℂ) (pwKernel A σ ξ) = pwGram A (τ - σ) := by
  have e : (fun ξ : ℝ => pwKernel A τ ξ * (starRingEnd ℂ) (pwKernel A σ ξ)) =
      (Ioo (-A) A).indicator fun ξ => ((ξ ^ 2 : ℝ) : ℂ) * exp ((((τ - σ) * ξ : ℝ) : ℂ) * I) := by
    funext ξ
    by_cases hξ : ξ ∈ Ioo (-A) A
    · simp only [pwKernel, indicator_of_mem hξ, map_mul, Complex.conj_ofReal, Complex.conj_I]
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      have e1 : exp (((τ * ξ : ℝ) : ℂ) * I) * exp (((σ * ξ : ℝ) : ℂ) * -I) =
          exp ((((τ - σ) * ξ : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      calc (ξ : ℂ) * I * exp (((τ * ξ : ℝ) : ℂ) * I) * ((ξ : ℂ) * -I * exp (((σ * ξ : ℝ) : ℂ) * -I))
          = -((ξ : ℂ) ^ 2 * (I * I)) * (exp (((τ * ξ : ℝ) : ℂ) * I) *
              exp (((σ * ξ : ℝ) : ℂ) * -I)) := by ring
        _ = _ := by rw [e1, Complex.I_mul_I]; push_cast; ring
    · simp only [pwKernel, indicator_of_notMem hξ, zero_mul]
  rw [e, integral_indicator measurableSet_Ioo]
  rfl

/-! ### Cauchy–Schwarz -/

/-- `‖∫ u v‖ ≤ √(∫ |u|²) √(∫ |v|²)` for `u, v ∈ L²`. -/
theorem norm_integral_mul_le_sqrt_mul_sqrt' {u v : ℝ → ℂ} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) :
    ‖∫ ξ : ℝ, u ξ * v ξ‖ ≤ Real.sqrt (∫ ξ : ℝ, ‖u ξ‖ ^ 2) * Real.sqrt (∫ ξ : ℝ, ‖v ξ‖ ^ 2) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (f := fun ξ => ‖u ξ‖) (g := fun ξ => ‖v ξ‖)
    Real.HolderConjugate.two_two (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _) (by simpa using hu.norm) (by simpa using hv.norm)
  have hholder' : (∫ ξ : ℝ, ‖u ξ‖ * ‖v ξ‖) ≤
      Real.sqrt (∫ ξ : ℝ, ‖u ξ‖ ^ 2) * Real.sqrt (∫ ξ : ℝ, ‖v ξ‖ ^ 2) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using hholder
  calc ‖∫ ξ : ℝ, u ξ * v ξ‖ ≤ ∫ ξ : ℝ, ‖u ξ * v ξ‖ := norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖u ξ‖ * ‖v ξ‖ := by simp only [norm_mul]
    _ ≤ _ := hholder'

/-- The `L²` energy of a function is the real part of `∫ u ū`. -/
theorem integral_norm_sq_eq_re {u : ℝ → ℂ} (hu : Integrable fun ξ => u ξ * (starRingEnd ℂ) (u ξ)) :
    ∫ ξ : ℝ, ‖u ξ‖ ^ 2 = (∫ ξ : ℝ, u ξ * (starRingEnd ℂ) (u ξ)).re := by
  have hre := integral_re hu
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact (Complex.ofReal_re _).symm

/-! ### The global signed sampling law -/

/-- **Sufficiency**: if the configuration form is at most `2π/h` times the coefficient energy,
the companion lattice pays the configuration for every source of aperture `A`. -/
theorem pwConfiguration_pay_of_gram (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0)
    (hA : 0 ≤ A) {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (t₀ : ℝ)
    {J : Type*} [Fintype J] (t w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hgram : ∀ c : J → ℂ, (configurationForm A t w c).re ≤ 2 * Real.pi / h * ∑ j, ‖c j‖ ^ 2) :
    ∑ j, w j * ‖pwDeriv F (t j)‖ ^ 2 ≤ ∑' k : ℤ, ‖pwSource F (t₀ + k * h)‖ ^ 2 := by
  rw [(hasSum_sq_pwSource_lattice hF hsupp hh hAh t₀).tsum_eq]
  have hFi := integrable_of_aperture hF hsupp
  set a : J → ℂ := fun j => ((Real.sqrt (w j) : ℝ) : ℂ) * pwDeriv F (t j) with ha
  have hna : ∀ j, ‖a j‖ ^ 2 = w j * ‖pwDeriv F (t j)‖ ^ 2 := fun j => by
    simp only [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (hw j)]
  set Ψ : ℝ → ℂ := fun ξ => ∑ j, (starRingEnd ℂ) (a j) * ((Real.sqrt (w j) : ℝ) : ℂ) *
    pwKernel A (t j) ξ with hΨ
  -- `Σ |a_j|² = ∫ Ψ F`
  have hpair : ((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) = ∫ ξ : ℝ, Ψ ξ * F ξ := by
    have hterm : ∀ j, (((‖a j‖ ^ 2 : ℝ)) : ℂ) = ∫ ξ : ℝ, (starRingEnd ℂ) (a j) *
        ((Real.sqrt (w j) : ℝ) : ℂ) * (pwKernel A (t j) ξ * F ξ) := by
      intro j
      rw [integral_const_mul, ← pwDeriv_eq_integral_kernel hsupp]
      have : (starRingEnd ℂ) (a j) * ((Real.sqrt (w j) : ℝ) : ℂ) * pwDeriv F (t j) =
          (starRingEnd ℂ) (a j) * a j := by simp only [ha]; ring
      rw [this, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.ofReal_sum, Finset.sum_congr rfl fun j _ => hterm j, ← integral_finsetSum _ fun j _ =>
      ((integrable_pwKernel_mul hA (t j) hFi).const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [hΨ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- `∫ |Ψ|² = Re Q(a)`
  have hΨ2 : MemLp Ψ 2 volume := by
    simp only [hΨ]
    exact memLp_finsetSum _ fun j _ => (memLp_pwKernel A (t j)).const_mul _
  have hΨconj : ∀ ξ, Ψ ξ * (starRingEnd ℂ) (Ψ ξ) = ∑ j, ∑ l, (starRingEnd ℂ) (a j) * a l *
      ((Real.sqrt (w j) * Real.sqrt (w l) : ℝ) : ℂ) *
        (pwKernel A (t j) ξ * (starRingEnd ℂ) (pwKernel A (t l) ξ)) := by
    intro ξ
    have hc : (starRingEnd ℂ) (Ψ ξ) = ∑ l, a l * ((Real.sqrt (w l) : ℝ) : ℂ) *
        (starRingEnd ℂ) (pwKernel A (t l) ξ) := by
      simp only [hΨ, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [hc]
    simp only [hΨ]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  have hint : ∀ j l, Integrable fun ξ => (starRingEnd ℂ) (a j) * a l *
      ((Real.sqrt (w j) * Real.sqrt (w l) : ℝ) : ℂ) *
        (pwKernel A (t j) ξ * (starRingEnd ℂ) (pwKernel A (t l) ξ)) :=
    fun j l => (integrable_pwKernel_mul_conj A (t j) (t l)).const_mul _
  have hQ : ∫ ξ : ℝ, ‖Ψ ξ‖ ^ 2 = (configurationForm A t w a).re := by
    rw [integral_norm_sq_eq_re ((hΨ2.integrable_mul hΨ2.star).congr (ae_of_all _ fun ξ => rfl))]
    congr 1
    rw [integral_congr_ae (ae_of_all _ hΨconj), integral_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun l _ => hint j l]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => hint j l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_pwKernel_mul_conj]
  -- Cauchy–Schwarz and the Gram bound
  set S := ∑ j, ‖a j‖ ^ 2
  set V := ∫ ξ : ℝ, ‖F ξ‖ ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hV0 : 0 ≤ V := integral_nonneg fun ξ => sq_nonneg _
  have hcs : S ≤ Real.sqrt ((configurationForm A t w a).re) * Real.sqrt V := by
    have h1 := norm_integral_mul_le_sqrt_mul_sqrt' hΨ2 hF
    rw [← hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0, hQ] at h1
    exact h1
  have hg := hgram a
  have hQ0 : 0 ≤ (configurationForm A t w a).re := by rw [← hQ]; exact integral_nonneg fun ξ => sq_nonneg _
  have hsq : S ^ 2 ≤ (2 * Real.pi / h * S) * V := by
    have h2 := pow_le_pow_left₀ hS0 hcs 2
    rw [mul_pow, Real.sq_sqrt hQ0, Real.sq_sqrt hV0] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right hg hV0)
  have hfin : S ≤ 2 * Real.pi / h * V := by
    rcases hS0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  rw [← Finset.sum_congr rfl fun j _ => hna j]
  exact hfin

/-- **Necessity**: if the companion lattice pays the configuration for every source of aperture
`A`, the configuration form is at most `2π/h` times the coefficient energy. -/
theorem gram_of_pwConfiguration_pay {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi)
    (t₀ : ℝ) {J : Type*} [Fintype J] (t w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hpay : ∀ F : ℝ → ℂ, MemLp F 2 volume → (∀ ξ, A ≤ |ξ| → F ξ = 0) →
      ∑ j, w j * ‖pwDeriv F (t j)‖ ^ 2 ≤ ∑' k : ℤ, ‖pwSource F (t₀ + k * h)‖ ^ 2)
    (c : J → ℂ) : (configurationForm A t w c).re ≤ 2 * Real.pi / h * ∑ j, ‖c j‖ ^ 2 := by
  set Fc : ℝ → ℂ := fun ξ => ∑ l, c l * ((Real.sqrt (w l) : ℝ) : ℂ) *
    (starRingEnd ℂ) (pwKernel A (t l) ξ) with hFc
  have hFc2 : MemLp Fc 2 volume := by
    simp only [hFc]
    exact memLp_finsetSum _ fun l _ => (memLp_pwKernel A (t l)).star.const_mul _
  have hFcs : ∀ ξ, A ≤ |ξ| → Fc ξ = 0 := by
    intro ξ hξ
    have hn : ξ ∉ Ioo (-A) A := fun hm => by
      have := abs_lt.mpr ⟨hm.1, hm.2⟩; linarith
    simp only [hFc, pwKernel_eq_zero hn, map_zero, mul_zero, Finset.sum_const_zero]
  -- `√w_j f'(t_j) = (Mc)_j`
  set Mc : J → ℂ := fun j => ∑ l, ((Real.sqrt (w j) * Real.sqrt (w l) : ℝ) : ℂ) *
    pwGram A (t j - t l) * c l with hMc
  have hint : ∀ j l, Integrable fun ξ => c l * ((Real.sqrt (w l) : ℝ) : ℂ) *
      (pwKernel A (t j) ξ * (starRingEnd ℂ) (pwKernel A (t l) ξ)) :=
    fun j l => (integrable_pwKernel_mul_conj A (t j) (t l)).const_mul _
  have hderiv : ∀ j, ((Real.sqrt (w j) : ℝ) : ℂ) * pwDeriv Fc (t j) = Mc j := by
    intro j
    rw [pwDeriv_eq_integral_kernel hFcs]
    have e : (fun ξ => pwKernel A (t j) ξ * Fc ξ) = fun ξ => ∑ l, c l *
        ((Real.sqrt (w l) : ℝ) : ℂ) * (pwKernel A (t j) ξ * (starRingEnd ℂ) (pwKernel A (t l) ξ)) := by
      funext ξ
      simp only [hFc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e, integral_finsetSum _ fun l _ => hint j l, Finset.mul_sum]
    simp only [hMc]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_pwKernel_mul_conj]
    push_cast; ring
  -- `∫ |F_c|² = Re Q(c)`
  have hconj : ∀ ξ, Fc ξ * (starRingEnd ℂ) (Fc ξ) = ∑ m, ∑ l, c m * (starRingEnd ℂ) (c l) *
      ((Real.sqrt (w m) * Real.sqrt (w l) : ℝ) : ℂ) *
        (pwKernel A (t l) ξ * (starRingEnd ℂ) (pwKernel A (t m) ξ)) := by
    intro ξ
    have hc : (starRingEnd ℂ) (Fc ξ) = ∑ l, (starRingEnd ℂ) (c l) * ((Real.sqrt (w l) : ℝ) : ℂ) *
        pwKernel A (t l) ξ := by
      simp only [hFc, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [hc]
    simp only [hFc]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  have hint2 : ∀ m l, Integrable fun ξ => c m * (starRingEnd ℂ) (c l) *
      ((Real.sqrt (w m) * Real.sqrt (w l) : ℝ) : ℂ) *
        (pwKernel A (t l) ξ * (starRingEnd ℂ) (pwKernel A (t m) ξ)) :=
    fun m l => (integrable_pwKernel_mul_conj A (t l) (t m)).const_mul _
  have hQ : ∫ ξ : ℝ, ‖Fc ξ‖ ^ 2 = (configurationForm A t w c).re := by
    rw [integral_norm_sq_eq_re ((hFc2.integrable_mul hFc2.star).congr (ae_of_all _ fun ξ => rfl))]
    congr 1
    rw [integral_congr_ae (ae_of_all _ hconj), integral_finsetSum _ fun m _ =>
      integrable_finsetSum _ fun l _ => hint2 m l]
    have hin : ∀ m l, ∫ ξ : ℝ, c m * (starRingEnd ℂ) (c l) *
        ((Real.sqrt (w m) * Real.sqrt (w l) : ℝ) : ℂ) *
          (pwKernel A (t l) ξ * (starRingEnd ℂ) (pwKernel A (t m) ξ)) =
        c m * (starRingEnd ℂ) (c l) * ((Real.sqrt (w m) * Real.sqrt (w l) : ℝ) : ℂ) *
          pwGram A (t l - t m) := fun m l => by
      rw [integral_const_mul, integral_pwKernel_mul_conj]
    rw [Finset.sum_congr rfl fun m _ => (integral_finsetSum _ fun l _ => hint2 m l).trans
      (Finset.sum_congr rfl fun l _ => hin m l), Finset.sum_comm]
    unfold configurationForm
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  -- the hypothesis at `F_c`
  have hp := hpay Fc hFc2 hFcs
  rw [(hasSum_sq_pwSource_lattice hFc2 hFcs hh hAh t₀).tsum_eq, hQ] at hp
  have hMc2 : ∑ j, ‖Mc j‖ ^ 2 = ∑ j, w j * ‖pwDeriv Fc (t j)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hderiv j, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (hw j)]
  -- `Q(c) = Σ_j c̄_j (Mc)_j ≤ |c| |Mc|`
  set Q := (configurationForm A t w c).re
  have hQ0 : 0 ≤ Q := by rw [← hQ]; exact integral_nonneg fun ξ => sq_nonneg _
  have hQM : configurationForm A t w c = ∑ j, (starRingEnd ℂ) (c j) * Mc j := by
    unfold configurationForm
    simp only [hMc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hcs : Q ≤ Real.sqrt (∑ j, ‖c j‖ ^ 2) * Real.sqrt (∑ j, ‖Mc j‖ ^ 2) := by
    calc Q ≤ ‖configurationForm A t w c‖ := Complex.re_le_norm _
      _ = ‖∑ j, (starRingEnd ℂ) (c j) * Mc j‖ := by rw [hQM]
      _ ≤ ∑ j, ‖c j‖ * ‖Mc j‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          rw [norm_mul, Complex.norm_conj]
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  set Λ := 2 * Real.pi / h
  set C := ∑ j, ‖c j‖ ^ 2
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hMQ : ∑ j, ‖Mc j‖ ^ 2 ≤ Λ * Q := by rw [hMc2]; exact hp
  have hsq : Q ^ 2 ≤ C * (Λ * Q) := by
    have h2 := pow_le_pow_left₀ hQ0 hcs 2
    rw [mul_pow, Real.sq_sqrt hC0, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hMQ hC0)
  rcases hQ0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- **The global signed sampling law**: a companion lattice at or above the Nyquist density pays
a finite off-line configuration for every source of aperture `A` iff the configuration form is at
most `2π/h` times the coefficient energy. -/
theorem pwConfiguration_pay_iff_gram (hA : 0 ≤ A) {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi)
    (t₀ : ℝ) {J : Type*} [Fintype J] (t w : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (∀ F : ℝ → ℂ, MemLp F 2 volume → (∀ ξ, A ≤ |ξ| → F ξ = 0) →
      ∑ j, w j * ‖pwDeriv F (t j)‖ ^ 2 ≤ ∑' k : ℤ, ‖pwSource F (t₀ + k * h)‖ ^ 2) ↔
    ∀ c : J → ℂ, (configurationForm A t w c).re ≤ 2 * Real.pi / h * ∑ j, ‖c j‖ ^ 2 :=
  ⟨fun hpay => gram_of_pwConfiguration_pay hh hAh t₀ t w hw hpay,
    fun hgram _F hF hsupp => pwConfiguration_pay_of_gram hF hsupp hA hh hAh t₀ t w hw hgram⟩

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
