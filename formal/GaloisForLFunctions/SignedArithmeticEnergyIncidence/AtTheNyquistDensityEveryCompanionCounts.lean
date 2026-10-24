import GaloisForLFunctions.SignedArithmeticEnergyIncidence.OffLineConfigurationsArePaidByTheirKernelGram

/-!
# At the Nyquist density every companion counts

At the critical density `A h = π` the companion lattice `x_k = t₀ + kh` has no redundancy, and
removing one companion reproduces the one-short count law (`oneShort_companions_pay_iff`) in the
Paley–Wiener class: with `x₀ = t₀` removed, a positive depth mass at `t` is paid for every source
of aperture `A` iff `t` is a critical point of the sinc of the missing companion,
`s(u) = ∫_{−A}^{A} e^{iuξ} dξ`, `s'(t − t₀) = 0` (`nyquistMinusOne_pay_iff`).

* **Polarized lattice Parseval** (`hasSum_pwSource_conj_mul`): for densities of aperture `A`
  with `A h ≤ π`, `Σ_k conj(g(x_k)) f(x_k) = (2π/h) ∫ F conj(G)`.
* **The derivative sampling formula** (`hasSum_pwDeriv_eq`): at `A h = π`,
  `f'(t) = (1/2A) Σ_k σ_k(t) f(x_k)` with `σ_k(t) = ∫ K_t e^{−ix_kξ} = s'(t − x_k)`, and
  `Σ_k |σ_k(t)|² = 4A⁴/3` (`hasSum_sq_pwSampleWeight`).
* **Pays at the critical points** (`nyquistMinusOne_pays`): if `σ₀(t) = 0` the remaining samples
  give `|f'(t)|² ≤ (A²/3) Σ_{k ≠ 0} |f(x_k)|²`.
* **Never elsewhere** (`nyquistMinusOne_never_pays`): the sinc density `e^{−it₀ξ}` vanishes at
  every remaining companion and has derivative `σ₀(t) ≠ 0` at `t`.
-/

open MeasureTheory Complex Set Filter

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {A : ℝ}

/-! ### Linearity and polarization -/

theorem pwSource_add {F G : ℝ → ℂ} (hF : Integrable F) (hG : Integrable G) (x : ℝ) :
    pwSource (fun ξ => F ξ + G ξ) x = pwSource F x + pwSource G x := by
  unfold pwSource
  rw [← integral_add]
  · exact integral_congr_ae (ae_of_all _ fun ξ => by ring)
  · exact hF.norm.mono' (hF.1.mul (by fun_prop : Continuous fun ξ : ℝ =>
      exp (((x * ξ : ℝ) : ℂ) * I)).aestronglyMeasurable) (ae_of_all _ fun ξ => by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one])
  · exact hG.norm.mono' (hG.1.mul (by fun_prop : Continuous fun ξ : ℝ =>
      exp (((x * ξ : ℝ) : ℂ) * I)).aestronglyMeasurable) (ae_of_all _ fun ξ => by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one])

theorem pwSource_smul (z : ℂ) (F : ℝ → ℂ) (x : ℝ) :
    pwSource (fun ξ => z * F ξ) x = z * pwSource F x := by
  unfold pwSource
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun ξ => by ring)

/-- `conj(a) b = ¼(|a+b|² − |a−b|² − i|a+ib|² + i|a−ib|²)`. -/
theorem conj_mul_eq_polarization (a b : ℂ) :
    (starRingEnd ℂ) a * b = (1 / 4 : ℂ) * (((‖a + b‖ ^ 2 : ℝ) : ℂ) - ((‖a - b‖ ^ 2 : ℝ) : ℂ) -
      I * ((‖a + I * b‖ ^ 2 : ℝ) : ℂ) + I * ((‖a - I * b‖ ^ 2 : ℝ) : ℂ)) := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) z * z := fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn, hn, hn, hn]
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * ((starRingEnd ℂ) a * b - (starRingEnd ℂ) b * a) * Complex.I_sq

/-- **Polarized lattice Parseval**: `Σ_k conj(g(x_k)) f(x_k) = (2π/h) ∫ F conj(G)`. -/
theorem hasSum_pwSource_conj_mul {F G : ℝ → ℂ} (hF : MemLp F 2 volume)
    (hFs : ∀ ξ, A ≤ |ξ| → F ξ = 0) (hG : MemLp G 2 volume) (hGs : ∀ ξ, A ≤ |ξ| → G ξ = 0)
    {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (t₀ : ℝ) :
    HasSum (fun k : ℤ => (starRingEnd ℂ) (pwSource G (t₀ + k * h)) * pwSource F (t₀ + k * h))
      (((2 * Real.pi / h : ℝ) : ℂ) * ∫ ξ : ℝ, F ξ * (starRingEnd ℂ) (G ξ)) := by
  have hFi := integrable_of_aperture hF hFs
  have hGi := integrable_of_aperture hG hGs
  set Λ : ℝ := 2 * Real.pi / h
  have hcomb : ∀ z : ℂ, MemLp (fun ξ => G ξ + z * F ξ) 2 volume ∧
      ∀ ξ, A ≤ |ξ| → G ξ + z * F ξ = 0 := fun z =>
    ⟨hG.add (hF.const_mul z), fun ξ hξ => by rw [hGs ξ hξ, hFs ξ hξ, mul_zero, add_zero]⟩
  have hval : ∀ (z : ℂ) (x : ℝ), pwSource (fun ξ => G ξ + z * F ξ) x =
      pwSource G x + z * pwSource F x := fun z x => by
    rw [pwSource_add hGi (hFi.const_mul z), pwSource_smul]
  -- the four lattice energies
  have hS : ∀ z : ℂ, HasSum (fun k : ℤ =>
      ((‖pwSource G (t₀ + k * h) + z * pwSource F (t₀ + k * h)‖ ^ 2 : ℝ) : ℂ))
      ((Λ * ∫ ξ : ℝ, ‖G ξ + z * F ξ‖ ^ 2 : ℝ) : ℂ) := fun z => by
    have := (hasSum_sq_pwSource_lattice (hcomb z).1 (hcomb z).2 hh hAh t₀).mapL Complex.ofRealCLM
    simpa only [hval, Complex.ofRealCLM_apply] using this
  have hsum := ((((hS 1).sub (hS (-1))).sub ((hS I).mul_left I)).add
    ((hS (-I)).mul_left I)).mul_left (1 / 4 : ℂ)
  -- the integral side, pointwise polarization
  have hint : ∀ z : ℂ, Integrable fun ξ => ‖G ξ + z * F ξ‖ ^ 2 := fun z =>
    (memLp_two_iff_integrable_sq_norm (hcomb z).1.1).mp (hcomb z).1
  have hpol : ∫ ξ : ℝ, F ξ * (starRingEnd ℂ) (G ξ) = (1 / 4 : ℂ) *
      (((∫ ξ : ℝ, ‖G ξ + 1 * F ξ‖ ^ 2 : ℝ) : ℂ) - ((∫ ξ : ℝ, ‖G ξ + -1 * F ξ‖ ^ 2 : ℝ) : ℂ) -
        I * ((∫ ξ : ℝ, ‖G ξ + I * F ξ‖ ^ 2 : ℝ) : ℂ) +
          I * ((∫ ξ : ℝ, ‖G ξ + -I * F ξ‖ ^ 2 : ℝ) : ℂ)) := by
    have hpt : ∀ ξ, F ξ * (starRingEnd ℂ) (G ξ) = (1 / 4 : ℂ) *
        (((‖G ξ + 1 * F ξ‖ ^ 2 : ℝ) : ℂ) - ((‖G ξ + -1 * F ξ‖ ^ 2 : ℝ) : ℂ) -
          I * ((‖G ξ + I * F ξ‖ ^ 2 : ℝ) : ℂ) + I * ((‖G ξ + -I * F ξ‖ ^ 2 : ℝ) : ℂ)) := by
      intro ξ
      rw [mul_comm, conj_mul_eq_polarization]
      simp only [one_mul, neg_mul, ← sub_eq_add_neg]
    rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul]
    congr 1
    have j1 : Integrable (fun ξ => ((‖G ξ + 1 * F ξ‖ ^ 2 : ℝ) : ℂ)) := (hint 1).ofReal
    have j2 : Integrable (fun ξ => ((‖G ξ + -1 * F ξ‖ ^ 2 : ℝ) : ℂ)) := (hint (-1)).ofReal
    have j3 : Integrable (fun ξ => I * ((‖G ξ + I * F ξ‖ ^ 2 : ℝ) : ℂ)) :=
      ((hint I).ofReal).const_mul I
    have j4 : Integrable (fun ξ => I * ((‖G ξ + -I * F ξ‖ ^ 2 : ℝ) : ℂ)) :=
      ((hint (-I)).ofReal).const_mul I
    have j12 : Integrable (fun ξ => ((‖G ξ + 1 * F ξ‖ ^ 2 : ℝ) : ℂ) -
        ((‖G ξ + -1 * F ξ‖ ^ 2 : ℝ) : ℂ)) := j1.sub j2
    have j123 : Integrable (fun ξ => ((‖G ξ + 1 * F ξ‖ ^ 2 : ℝ) : ℂ) -
        ((‖G ξ + -1 * F ξ‖ ^ 2 : ℝ) : ℂ) - I * ((‖G ξ + I * F ξ‖ ^ 2 : ℝ) : ℂ)) := j12.sub j3
    rw [integral_add j123 j4, integral_sub j12 j3, integral_sub j1 j2, integral_const_mul,
      integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      integral_complex_ofReal, integral_complex_ofReal]
  have hv : ((Λ : ℝ) : ℂ) * ∫ ξ : ℝ, F ξ * (starRingEnd ℂ) (G ξ) = (1 / 4 : ℂ) *
      (((Λ * ∫ ξ : ℝ, ‖G ξ + 1 * F ξ‖ ^ 2 : ℝ) : ℂ) - ((Λ * ∫ ξ : ℝ, ‖G ξ + -1 * F ξ‖ ^ 2 : ℝ) : ℂ) -
        I * ((Λ * ∫ ξ : ℝ, ‖G ξ + I * F ξ‖ ^ 2 : ℝ) : ℂ) +
          I * ((Λ * ∫ ξ : ℝ, ‖G ξ + -I * F ξ‖ ^ 2 : ℝ) : ℂ)) := by
    rw [hpol]; push_cast; ring
  rw [hv]
  refine hsum.congr_fun fun k => ?_
  rw [conj_mul_eq_polarization]
  simp only [one_mul, neg_mul, ← sub_eq_add_neg]

/-! ### The derivative sampling formula -/

/-- The sample weight `σ(t, x) = ∫ K_t e^{−ixξ} = s'(t − x)`. -/
def pwSampleWeight (A t x : ℝ) : ℂ :=
  ∫ ξ : ℝ, pwKernel A t ξ * exp (((-(x * ξ) : ℝ) : ℂ) * I)

/-- The conjugate kernel `conj K_t` is a density of aperture `A`. -/
theorem conjKernel_aperture (A t : ℝ) :
    MemLp (fun ξ => (starRingEnd ℂ) (pwKernel A t ξ)) 2 volume ∧
      ∀ ξ, A ≤ |ξ| → (starRingEnd ℂ) (pwKernel A t ξ) = 0 := by
  refine ⟨(memLp_pwKernel A t).star, fun ξ hξ => ?_⟩
  have hn : ξ ∉ Ioo (-A) A := fun hm => by have := abs_lt.mpr ⟨hm.1, hm.2⟩; linarith
  rw [pwKernel_eq_zero hn, map_zero]

theorem pwSource_conjKernel (A t x : ℝ) :
    pwSource (fun ξ => (starRingEnd ℂ) (pwKernel A t ξ)) x = (starRingEnd ℂ) (pwSampleWeight A t x) := by
  unfold pwSource pwSampleWeight
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  show (starRingEnd ℂ) (pwKernel A t ξ) * exp (((x * ξ : ℝ) : ℂ) * I) =
    (starRingEnd ℂ) (pwKernel A t ξ * exp (((-(x * ξ) : ℝ) : ℂ) * I))
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast; ring

theorem integral_norm_sq_pwKernel {A : ℝ} (hA : 0 ≤ A) (t : ℝ) :
    ∫ ξ : ℝ, ‖pwKernel A t ξ‖ ^ 2 = 2 * A ^ 3 / 3 := by
  have e : (fun ξ => ‖pwKernel A t ξ‖ ^ 2) = (Ioo (-A) A).indicator fun ξ => ξ ^ 2 := by
    funext ξ
    by_cases hξ : ξ ∈ Ioo (-A) A
    · simp only [pwKernel, indicator_of_mem hξ]
      rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, mul_one, mul_one, sq_abs]
    · simp only [pwKernel, indicator_of_notMem hξ, norm_zero]; ring
  rw [e, integral_indicator measurableSet_Ioo, integral_sq_Ioo_eq hA]

/-- **The derivative sampling formula**: `Σ_k σ_k(t) f(x_k) = (2π/h) f'(t)`. -/
theorem hasSum_pwDeriv_eq {F : ℝ → ℂ} (hF : MemLp F 2 volume) (hFs : ∀ ξ, A ≤ |ξ| → F ξ = 0)
    {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (t₀ t : ℝ) :
    HasSum (fun k : ℤ => pwSampleWeight A t (t₀ + k * h) * pwSource F (t₀ + k * h))
      (((2 * Real.pi / h : ℝ) : ℂ) * pwDeriv F t) := by
  obtain ⟨hG, hGs⟩ := conjKernel_aperture A t
  have h1 := hasSum_pwSource_conj_mul hF hFs hG hGs hh hAh t₀
  simp only [pwSource_conjKernel, Complex.conj_conj] at h1
  convert h1 using 2
  rw [pwDeriv_eq_integral_kernel hFs]
  exact integral_congr_ae (ae_of_all _ fun ξ => mul_comm _ _)

/-- **The sample weights**: `Σ_k |σ_k(t)|² = (2π/h)(2A³/3)`. -/
theorem hasSum_sq_pwSampleWeight (hA : 0 ≤ A) {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi)
    (t₀ t : ℝ) :
    HasSum (fun k : ℤ => ‖pwSampleWeight A t (t₀ + k * h)‖ ^ 2)
      (2 * Real.pi / h * (2 * A ^ 3 / 3)) := by
  obtain ⟨hG, hGs⟩ := conjKernel_aperture A t
  have h1 := hasSum_sq_pwSource_lattice hG hGs hh hAh t₀
  simp only [pwSource_conjKernel, Complex.norm_conj] at h1
  rwa [integral_norm_sq_pwKernel hA t] at h1

/-! ### Cauchy–Schwarz for lattice sums -/

/-- `‖Σ a_k b_k‖² ≤ (Σ |a_k|²)(Σ |b_k|²)` for sums over `ℤ`. -/
theorem norm_sq_hasSum_mul_le {a b : ℤ → ℂ} {S' : ℂ} {P Q : ℝ} (hab : HasSum (fun k => a k * b k) S')
    (ha : HasSum (fun k => ‖a k‖ ^ 2) P) (hb : HasSum (fun k => ‖b k‖ ^ 2) Q) :
    ‖S'‖ ^ 2 ≤ P * Q := by
  have hP0 : 0 ≤ P := ha.nonneg fun k => sq_nonneg _
  have hQ0 : 0 ≤ Q := hb.nonneg fun k => sq_nonneg _
  have hfin : ∀ s : Finset ℤ, ‖∑ k ∈ s, a k * b k‖ ≤ Real.sqrt P * Real.sqrt Q := by
    intro s
    calc ‖∑ k ∈ s, a k * b k‖ ≤ ∑ k ∈ s, ‖a k‖ * ‖b k‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
      _ ≤ Real.sqrt (∑ k ∈ s, ‖a k‖ ^ 2) * Real.sqrt (∑ k ∈ s, ‖b k‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt P * Real.sqrt Q :=
          mul_le_mul (Real.sqrt_le_sqrt (sum_le_hasSum s (fun k _ => sq_nonneg _) ha))
            (Real.sqrt_le_sqrt (sum_le_hasSum s (fun k _ => sq_nonneg _) hb))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hlim : ‖S'‖ ≤ Real.sqrt P * Real.sqrt Q :=
    le_of_tendsto' ((continuous_norm.tendsto S').comp hab) hfin
  calc ‖S'‖ ^ 2 ≤ (Real.sqrt P * Real.sqrt Q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlim 2
    _ = P * Q := by rw [mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt hQ0]

/-! ### One companion short at the Nyquist density -/

/-- The sinc density `e^{−it₀ξ}` on `(−A, A)` of the companion `x₀ = t₀`. -/
def sincDensity (A t₀ : ℝ) : ℝ → ℂ :=
  (Ioo (-A) A).indicator fun ξ => exp (((-(t₀ * ξ) : ℝ) : ℂ) * I)

theorem sincDensity_aperture (A t₀ : ℝ) :
    MemLp (sincDensity A t₀) 2 volume ∧ ∀ ξ, A ≤ |ξ| → sincDensity A t₀ ξ = 0 := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (-A) A)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  refine ⟨?_, fun ξ hξ => indicator_of_notMem (fun hm => by
    have := abs_lt.mpr ⟨hm.1, hm.2⟩; linarith) _⟩
  unfold sincDensity
  rw [memLp_indicator_iff_restrict measurableSet_Ioo]
  exact MemLp.of_bound (by fun_prop : Continuous fun ξ : ℝ =>
    exp (((-(t₀ * ξ) : ℝ) : ℂ) * I)).aestronglyMeasurable 1
    (ae_of_all _ fun ξ => by rw [norm_exp_ofReal_mul_I])

/-- **The sinc of `x₀` vanishes at every other companion** of a critical lattice. -/
theorem pwSource_sincDensity_lattice (hA : 0 < A) {h : ℝ} (hAh : A * h = Real.pi) (t₀ : ℝ)
    {k : ℤ} (hk : k ≠ 0) : pwSource (sincDensity A t₀) (t₀ + k * h) = 0 := by
  have hh : 0 < h := by
    by_contra hneg; push Not at hneg
    have : A * h ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le hneg
    linarith [Real.pi_pos]
  set c : ℂ := ((k * h : ℝ) : ℂ) * I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast mul_ne_zero (Int.cast_ne_zero.mpr hk) hh.ne'
  unfold pwSource sincDensity
  have e : (fun ξ : ℝ => (Ioo (-A) A).indicator (fun ξ => exp (((-(t₀ * ξ) : ℝ) : ℂ) * I)) ξ *
      exp ((((t₀ + k * h) * ξ : ℝ) : ℂ) * I)) =
      (Ioo (-A) A).indicator fun ξ => exp (c * ξ) := by
    funext ξ
    by_cases hξ : ξ ∈ Ioo (-A) A
    · rw [indicator_of_mem hξ, indicator_of_mem hξ, ← Complex.exp_add, hc]
      congr 1; push_cast; ring
    · rw [indicator_of_notMem hξ, indicator_of_notMem hξ, zero_mul]
  rw [e, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), integral_exp_mul_complex hc0]
  have hper : exp (c * A) = exp (c * (-A : ℝ)) := by
    have h2 : c * A = c * (-A : ℝ) + (k : ℂ) * (2 * Real.pi * I) := by
      rw [hc]; push_cast
      have : (A : ℂ) * h = Real.pi := by exact_mod_cast hAh
      linear_combination (2 * (k : ℂ) * I) * this
    rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper, sub_self, zero_div]

theorem pwDeriv_sincDensity (A t₀ t : ℝ) :
    pwDeriv (sincDensity A t₀) t = pwSampleWeight A t t₀ := by
  rw [pwDeriv_eq_integral_kernel (sincDensity_aperture A t₀).2]
  unfold pwSampleWeight sincDensity
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  show pwKernel A t ξ * (Ioo (-A) A).indicator (fun ξ => exp (((-(t₀ * ξ) : ℝ) : ℂ) * I)) ξ =
    pwKernel A t ξ * exp (((-(t₀ * ξ) : ℝ) : ℂ) * I)
  by_cases hξ : ξ ∈ Ioo (-A) A
  · rw [indicator_of_mem hξ]
  · rw [pwKernel_eq_zero hξ, zero_mul, zero_mul]

/-- **Never off the critical points**: if `σ₀(t) ≠ 0`, the sinc of the missing companion vanishes
at every remaining companion and defeats every positive depth mass at `t`. -/
theorem nyquistMinusOne_never_pays (hA : 0 < A) {h : ℝ} (hAh : A * h = Real.pi) (t₀ t : ℝ)
    (hσ : pwSampleWeight A t t₀ ≠ 0) {w : ℝ} (hw : 0 < w) :
    ∃ F : ℝ → ℂ, MemLp F 2 volume ∧ (∀ ξ, A ≤ |ξ| → F ξ = 0) ∧
      ∑' k : ℤ, (if k = 0 then 0 else ‖pwSource F (t₀ + k * h)‖ ^ 2) < w * ‖pwDeriv F t‖ ^ 2 := by
  refine ⟨sincDensity A t₀, (sincDensity_aperture A t₀).1, (sincDensity_aperture A t₀).2, ?_⟩
  have h0 : (fun k : ℤ => if k = 0 then (0 : ℝ) else ‖pwSource (sincDensity A t₀) (t₀ + k * h)‖ ^ 2) =
      fun _ => 0 := by
    funext k
    split_ifs with hk
    · rfl
    · rw [pwSource_sincDensity_lattice hA hAh t₀ hk, norm_zero, zero_pow two_ne_zero]
  rw [h0, tsum_zero, pwDeriv_sincDensity]
  have : 0 < ‖pwSampleWeight A t t₀‖ := norm_pos_iff.mpr hσ
  positivity

/-- **Pays at the critical points**: if `σ₀(t) = 0`, the remaining companions of a critical
lattice give `|f'(t)|² ≤ (A²/3) Σ_{k ≠ 0} |f(x_k)|²` for every source of aperture `A`. -/
theorem nyquistMinusOne_pays (hA : 0 < A) {h : ℝ} (hh : 0 < h) (hAh : A * h = Real.pi)
    (t₀ t : ℝ) (hσ : pwSampleWeight A t t₀ = 0) {F : ℝ → ℂ} (hF : MemLp F 2 volume)
    (hFs : ∀ ξ, A ≤ |ξ| → F ξ = 0) :
    ‖pwDeriv F t‖ ^ 2 ≤
      A ^ 2 / 3 * ∑' k : ℤ, (if k = 0 then 0 else ‖pwSource F (t₀ + k * h)‖ ^ 2) := by
  have hD := hasSum_pwDeriv_eq hF hFs hh hAh.le t₀ t
  have hW := hasSum_sq_pwSampleWeight hA.le hh hAh.le t₀ t
  set b : ℤ → ℂ := fun k => if k = 0 then 0 else pwSource F (t₀ + k * h)
  have hab : (fun k : ℤ => pwSampleWeight A t (t₀ + k * h) * pwSource F (t₀ + k * h)) =
      fun k : ℤ => pwSampleWeight A t (t₀ + k * h) * b k := by
    funext k
    simp only [b]
    split_ifs with hk
    · rw [hk]; simp [hσ]
    · rfl
  rw [hab] at hD
  have hbn : ∀ k, ‖b k‖ ^ 2 = if k = 0 then 0 else ‖pwSource F (t₀ + k * h)‖ ^ 2 := fun k => by
    simp only [b]; split_ifs <;> simp
  have hlat := hasSum_sq_pwSource_lattice hF hFs hh hAh.le t₀
  have hbs : Summable fun k => ‖b k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => by rw [hbn]; split_ifs <;> simp) hlat.summable
  have hcs := norm_sq_hasSum_mul_le hD hW hbs.hasSum
  simp only [hbn] at hcs
  -- `Λ = 2π/h = 2A`
  have hΛ : 2 * Real.pi / h = 2 * A := by
    rw [div_eq_iff hh.ne', ← hAh]; ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hΛ, abs_of_pos (by positivity), mul_pow] at hcs
  have hS0 : 0 ≤ ∑' k : ℤ, (if k = 0 then 0 else ‖pwSource F (t₀ + k * h)‖ ^ 2) :=
    tsum_nonneg fun k => by split_ifs <;> positivity
  have hA2 : 0 < (2 * A) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  nlinarith

/-- **At the Nyquist density every companion counts**: with the companion `x₀ = t₀` removed from
a critical lattice, a positive depth mass at `t` is paid for every source of aperture `A` iff `t`
is a critical point of the sinc of `x₀`, `s'(t − t₀) = σ₀(t) = 0`. -/
theorem nyquistMinusOne_pay_iff (hA : 0 < A) {h : ℝ} (hh : 0 < h) (hAh : A * h = Real.pi)
    (t₀ t : ℝ) :
    (∃ w : ℝ, 0 < w ∧ ∀ F : ℝ → ℂ, MemLp F 2 volume → (∀ ξ, A ≤ |ξ| → F ξ = 0) →
      w * ‖pwDeriv F t‖ ^ 2 ≤
        ∑' k : ℤ, (if k = 0 then 0 else ‖pwSource F (t₀ + k * h)‖ ^ 2)) ↔
      pwSampleWeight A t t₀ = 0 := by
  constructor
  · rintro ⟨w, hw, hpay⟩
    by_contra hσ
    obtain ⟨F, hF, hFs, hlt⟩ := nyquistMinusOne_never_pays hA hAh t₀ t hσ hw
    exact absurd (hpay F hF hFs) (not_le.mpr hlt)
  · intro hσ
    refine ⟨3 / A ^ 2, by positivity, fun F hF hFs => ?_⟩
    have := nyquistMinusOne_pays hA hh hAh t₀ t hσ hF hFs
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
