import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation

/-!
# The trace certificate across the entry of the prime 2

For an aperture `b` with `log 2 ≤ 2b < log 3` the restricted Weil form contains exactly one prime
term, the translation by `L = log 2`.  On the pole-vanishing subspace it is a Fourier multiplier:

`Q_b(f) = ∫ (W(ξ) - √2 log 2 · cos(2π L ξ)) |𝓕 f(ξ)|² dξ`,

because `Re ⟨f(· + h), f⟩ = ∫ cos(2π h ξ) |𝓕 f(ξ)|² dξ` (translation is modulation on the Fourier
side).  A translation by the full diameter `2b` has null overlap on the aperture, so
`∫ cos(2π · 2b · ξ) |𝓕 f|² = 0` and the term `√2 log 2 · cos(2π · 2b · ξ)` may be added for free:

`Q_b(f) = ∫ (W(ξ) - √2 log 2 · (cos(2π L ξ) - cos(2π · 2b · ξ))) |𝓕 f(ξ)|² dξ`.

The difference of cosines is `2 sin(π(2b + L)ξ) sin(π(2b - L)ξ)`: it is small at frequencies below
`1/(2b - L)` and nonpositive on `[1/(2b+L), 2/(2b+L)]`.  This is the positive-definite (Krein)
extension freedom of the compressed Weil kernel: only lags in `[-2b, 2b]` are seen by the form.

The grid certificate of `PoleVanishingWeilTraceCertificate` is restated for a general symbol.
-/

open MeasureTheory Complex Set
open scoped FourierTransform InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Translation pairings as Fourier multipliers -/

theorem logTranslationCLM_eq_translateL2 (h : ℝ) (f : SoninL2) :
    logTranslationCLM h f = translateL2 h f := by
  apply Lp.ext
  filter_upwards [logTranslationCLM_ae h f, coeFn_translateL2 h f] with x h1 h2
  rw [h1, h2]

/-- **Translation pairing on the Fourier side.**  For a form-domain vector with aperture
realization `f`, `Re ⟨f(· + h), f⟩ = ∫ cos(2π h ξ) ‖u(ξ)‖² dξ`. -/
theorem re_inner_logTranslation_eq_integral_cos (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (h : ℝ) :
    (inner ℂ (logTranslationCLM h (ccmArchimedeanFormToAperture a u).1)
        (ccmArchimedeanFormToAperture a u).1).re =
      ∫ ξ : ℝ, Real.cos (2 * Real.pi * h * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
  set f : SoninL2 := (ccmArchimedeanFormToAperture a u).1 with hf
  have hF : fourierUnitary f = ccmArchimedeanWeightedToL2 u.1 :=
    fourierUnitary_ccmArchimedeanFourierToTime u.1
  have hmod : fourierUnitary (translateL2 h f) = modulationMul h (fourierUnitary f) :=
    fourierTransform_translateL2 h f
  rw [logTranslationCLM_eq_translateL2, ← fourierUnitary.inner_map_map, hmod, hF,
    MeasureTheory.L2.inner_def]
  have hre : (∫ ξ : ℝ, inner ℂ ((modulationMul h (ccmArchimedeanWeightedToL2 u.1) :
      SoninL2) ξ) ((ccmArchimedeanWeightedToL2 u.1 : SoninL2) ξ)).re =
      ∫ ξ : ℝ, (inner ℂ ((modulationMul h (ccmArchimedeanWeightedToL2 u.1) : SoninL2) ξ)
        ((ccmArchimedeanWeightedToL2 u.1 : SoninL2) ξ)).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm]
    · rfl
    · exact (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) _ _)
  rw [hre]
  apply integral_congr_ae
  filter_upwards [coeFn_modulationMul h (ccmArchimedeanWeightedToL2 u.1),
    ccmArchimedeanWeightedToL2_coeFn u.1] with ξ hm hw
  rw [hm, hw, RCLike.inner_apply]
  unfold modulationSymbol
  rw [map_mul, ← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) (((2 * Real.pi * (h * ξ) : ℝ) : ℂ) * I) =
      ((-(2 * Real.pi * (h * ξ)) : ℝ) : ℂ) * I := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hconj, mul_comm, ← mul_assoc, mul_assoc, Complex.conj_mul']
  rw [show ((‖(u.1 : ℝ → ℂ) ξ‖ : ℂ) ^ 2) = (((‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-! ## The symbol past the prime-2 entry -/

/-- `W(ξ) - √2 log 2 · (cos(2π log 2 · ξ) - cos(2π · 2a · ξ))`. -/
def primeTwoShiftSymbol (a ξ : ℝ) : ℝ :=
  archimedeanWeilSymbol ξ - Real.sqrt 2 * Real.log 2 *
    (Real.cos (2 * Real.pi * Real.log 2 * ξ) - Real.cos (2 * Real.pi * (2 * a) * ξ))

theorem integrable_cos_mul_norm_sq_ccmFormDomain (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (h : ℝ) :
    Integrable (fun ξ : ℝ => Real.cos (2 * Real.pi * h * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
  refine (integrable_norm_sq_ccmFormDomain a u).bdd_mul (c := 1) ?_ ?_
  · exact (by fun_prop : Continuous fun ξ : ℝ => Real.cos (2 * Real.pi * h * ξ)).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _

theorem integrable_primeTwoShiftSymbol_mul (a b : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ : ℝ => primeTwoShiftSymbol b.1 ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
  have hW : Integrable (fun ξ : ℝ => archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    have := integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1
    simpa [archimedeanWeilSymbol] using this
  have h1 := integrable_cos_mul_norm_sq_ccmFormDomain a u (Real.log 2)
  have h2 := integrable_cos_mul_norm_sq_ccmFormDomain a u (2 * b.1)
  refine (hW.sub ((h1.sub h2).const_mul (Real.sqrt 2 * Real.log 2))).congr ?_
  filter_upwards with ξ
  simp only [Pi.sub_apply, primeTwoShiftSymbol]
  ring

/-- **The form past the prime-2 entry is a Fourier multiplier.**  For `log 2 ≤ 2b < log 3`, on the
pole-vanishing subspace, the restricted Weil form is `∫ (W - √2 log 2 (cos(2πLξ) -
cos(2π·2b·ξ))) ‖u‖²`. -/
theorem ccmRestrictedWeilSourceQuadratic_primeTwo_eq (b : SuzukiPositiveAperture)
    (hb1 : Real.log 2 ≤ 2 * b.1) (hb2 : 2 * b.1 < Real.log 3)
    (u : CCMArchimedeanFormDomain b) (hu : IsPolarConstrained b u) :
    ccmRestrictedWeilSourceQuadratic b u =
      ∫ ξ : ℝ, primeTwoShiftSymbol b.1 ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
  have hfloor : Nat.floor (Real.exp (2 * b.1)) = 2 := by
    rw [Nat.floor_eq_iff (Real.exp_pos _).le]
    constructor
    · have := Real.exp_le_exp.mpr hb1
      rw [Real.exp_log (by norm_num)] at this
      push_cast
      linarith
    · have := Real.exp_lt_exp.mpr hb2
      rw [Real.exp_log (by norm_num)] at this
      push_cast
      linarith
  have hpos := re_inner_logTranslation_eq_integral_cos b u (Real.log 2)
  have hneg := re_inner_logTranslation_eq_integral_cos b u (-Real.log 2)
  have hzero : inner ℂ (logTranslationCLM (2 * b.1) (ccmArchimedeanFormToAperture b u).1)
      (ccmArchimedeanFormToAperture b u).1 = 0 :=
    inner_logTranslationCLM_two_aperture_eq_zero b _
  have hdiam := re_inner_logTranslation_eq_integral_cos b u (2 * b.1)
  rw [hzero, Complex.zero_re] at hdiam
  have hcos : (fun ξ : ℝ => Real.cos (2 * Real.pi * -Real.log 2 * ξ) *
      ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) = fun ξ => Real.cos (2 * Real.pi * Real.log 2 * ξ) *
      ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
    funext ξ
    rw [show 2 * Real.pi * -Real.log 2 * ξ = -(2 * Real.pi * Real.log 2 * ξ) by ring,
      Real.cos_neg]
  rw [hcos] at hneg
  have hΛ : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  unfold ccmRestrictedWeilSourceQuadratic
  simp only
  rw [hfloor, hu.1, hu.2]
  simp only [mul_zero, add_zero, Complex.zero_re, Finset.Icc_self, Finset.sum_singleton,
    Nat.cast_ofNat]
  rw [Complex.add_re, hpos, hneg]
  have hW : Integrable (fun ξ : ℝ => archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    have := integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1
    simpa [archimedeanWeilSymbol] using this
  have h1 := integrable_cos_mul_norm_sq_ccmFormDomain b u (Real.log 2)
  have h2 := integrable_cos_mul_norm_sq_ccmFormDomain b u (2 * b.1)
  have hsplit : ∫ ξ : ℝ, primeTwoShiftSymbol b.1 ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 =
      (∫ ξ : ℝ, archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) -
        Real.sqrt 2 * Real.log 2 *
          ((∫ ξ : ℝ, Real.cos (2 * Real.pi * Real.log 2 * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) -
            ∫ ξ : ℝ, Real.cos (2 * Real.pi * (2 * b.1) * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    have hfun : (fun ξ : ℝ => primeTwoShiftSymbol b.1 ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) =
        fun ξ => archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 -
          Real.sqrt 2 * Real.log 2 *
            (Real.cos (2 * Real.pi * Real.log 2 * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 -
              Real.cos (2 * Real.pi * (2 * b.1) * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
      funext ξ
      simp only [primeTwoShiftSymbol]
      ring
    have h12 : Integrable (fun ξ : ℝ => Real.cos (2 * Real.pi * Real.log 2 * ξ) *
        ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 - Real.cos (2 * Real.pi * (2 * b.1) * ξ) *
        ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := h1.sub h2
    have hc12 : Integrable (fun ξ : ℝ => Real.sqrt 2 * Real.log 2 *
        (Real.cos (2 * Real.pi * Real.log 2 * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 -
          Real.cos (2 * Real.pi * (2 * b.1) * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2)) :=
      h12.const_mul _
    rw [hfun, integral_sub hW hc12, integral_const_mul, integral_sub h1 h2]
  rw [hsplit, ← hdiam, hΛ]
  have hsqrt : (1 / Real.sqrt 2) * 2 = Real.sqrt 2 := by
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    linarith
  have hWform : (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
      ‖(u.1 : ℝ → ℂ) xi‖ ^ 2) = ∫ ξ : ℝ, archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
    rfl
  rw [hWform]
  have : Real.log 2 * (1 / Real.sqrt 2) *
      ((∫ ξ : ℝ, Real.cos (2 * Real.pi * Real.log 2 * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) +
        ∫ ξ : ℝ, Real.cos (2 * Real.pi * Real.log 2 * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) =
      Real.sqrt 2 * Real.log 2 *
        ∫ ξ : ℝ, Real.cos (2 * Real.pi * Real.log 2 * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
    set I := ∫ ξ : ℝ, Real.cos (2 * Real.pi * Real.log 2 * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2
    rw [show Real.log 2 * (1 / Real.sqrt 2) * (I + I) =
      Real.log 2 * I * ((1 / Real.sqrt 2) * 2) by ring, hsqrt]
    ring
  rw [this]
  ring

/-! ## The grid certificate for a general symbol -/

theorem sub_gridStepWeight_le_of_shells {α h : ℝ} (hh : 0 < h) {K : ℕ} {G : ℕ → ℝ}
    (hG : ∀ k, 0 ≤ G k) {M : ℝ → ℝ}
    (hshell : ∀ k < K, ∀ ξ : ℝ, (k : ℝ) * h ≤ |ξ| → |ξ| < ((k : ℝ) + 1) * h → α - G k ≤ M ξ)
    (htail : ∀ ξ : ℝ, (K : ℝ) * h ≤ |ξ| → α ≤ M ξ) (ξ : ℝ) :
    α - gridStepWeight h K G ξ ≤ M ξ := by
  by_cases hbig : (K : ℝ) * h ≤ |ξ|
  · have := gridStepWeight_nonneg (h := h) (K := K) hG ξ
    linarith [htail ξ hbig]
  · push Not at hbig
    set j := Nat.floor (|ξ| / h) with hj
    have hjle : (j : ℝ) * h ≤ |ξ| := by
      have := Nat.floor_le (div_nonneg (abs_nonneg ξ) hh.le)
      rw [← hj] at this
      calc (j : ℝ) * h ≤ |ξ| / h * h := mul_le_mul_of_nonneg_right this hh.le
        _ = |ξ| := div_mul_cancel₀ _ hh.ne'
    have hjlt : |ξ| < ((j : ℝ) + 1) * h := by
      have := Nat.lt_floor_add_one (|ξ| / h)
      rw [← hj] at this
      calc |ξ| = |ξ| / h * h := (div_mul_cancel₀ _ hh.ne').symm
        _ < ((j : ℝ) + 1) * h := mul_lt_mul_of_pos_right this hh
    have hjK : j < K := by
      by_contra hcon
      push Not at hcon
      have : (K : ℝ) * h ≤ (j : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcon) hh.le
      linarith
    have hterm : G j ≤ gridStepWeight h K G ξ := by
      unfold gridStepWeight
      have hmem : G j ≤ G j *
          ((Ico (j * h) ((j + 1) * h)).indicator (fun _ => (1 : ℝ)) ξ +
            (Ioc (-((j + 1) * h)) (-(j * h))).indicator (fun _ => (1 : ℝ)) ξ) := by
        rcases le_or_gt 0 ξ with hξ | hξ
        · rw [abs_of_nonneg hξ] at hjle hjlt
          rw [Set.indicator_of_mem (show ξ ∈ Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h) from
            ⟨hjle, hjlt⟩)]
          have : 0 ≤ (Ioc (-(((j : ℝ) + 1) * h)) (-((j : ℝ) * h))).indicator
            (fun _ => (1 : ℝ)) ξ := Set.indicator_nonneg (fun _ _ => by norm_num) _
          nlinarith [hG j]
        · rw [abs_of_neg hξ] at hjle hjlt
          rw [Set.indicator_of_mem (show ξ ∈ Ioc (-(((j : ℝ) + 1) * h)) (-((j : ℝ) * h)) from
            ⟨by linarith, by linarith⟩)]
          have : 0 ≤ (Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h)).indicator
            (fun _ => (1 : ℝ)) ξ := Set.indicator_nonneg (fun _ _ => by norm_num) _
          nlinarith [hG j]
      refine hmem.trans ?_
      apply Finset.single_le_sum (f := fun k => G k *
        ((Ico (k * h) ((k + 1) * h)).indicator (fun _ => (1 : ℝ)) ξ +
          (Ioc (-((k + 1) * h)) (-(k * h))).indicator (fun _ => (1 : ℝ)) ξ))
      · intro k _
        apply mul_nonneg (hG k)
        apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => by norm_num) _
      · exact Finset.mem_range.mpr hjK
    have := hshell j hjK ξ hjle hjlt
    linarith

/-- **The trace certificate for a general symbol.**  If on the pole-vanishing subspace of the
aperture `a` the restricted Weil form is `∫ M ‖u‖²`, the symbol is at least `α - G k` on the shell
`k h ≤ |ξ| < (k+1) h` and at least `α` beyond `K h`, and the Fourier mass density of
pole-vanishing aperture vectors is at most `R k ‖f‖²` on the shells, then the pole-vanishing
ground energy is at least `α - Σ_k 2 h G_k R_k`. -/
theorem le_ccmRestrictedWeilPolarGroundEnergy_of_symbol_grid {a : SuzukiPositiveAperture}
    (M : ℝ → ℝ)
    (hQ : ∀ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u →
      ccmRestrictedWeilSourceQuadratic a u = ∫ ξ : ℝ, M ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2)
    (hMint : ∀ u : CCMArchimedeanFormDomain a,
      Integrable (fun ξ : ℝ => M ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2))
    {α h : ℝ} (hh : 0 < h) {K : ℕ} {G R : ℕ → ℝ} (hG : ∀ k, 0 ≤ G k)
    (hshell : ∀ k < K, ∀ ξ : ℝ, (k : ℝ) * h ≤ |ξ| → |ξ| < ((k : ℝ) + 1) * h → α - G k ≤ M ξ)
    (htail : ∀ ξ : ℝ, (K : ℝ) * h ≤ |ξ| → α ≤ M ξ)
    (hR : ∀ k : ℕ, k < K → ∀ f : suzukiApertureHilbert a,
      inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0 →
      inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0 →
      ∀ ξ : ℝ, (k : ℝ) * h ≤ |ξ| → |ξ| < ((k : ℝ) + 1) * h →
        ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ R k * ‖f‖ ^ 2) :
    α - ∑ k ∈ Finset.range K, 2 * h * G k * R k ≤ ccmRestrictedWeilPolarGroundEnergy a := by
  apply le_ccmRestrictedWeilPolarGroundEnergy_of_floor
  intro u hu
  set f := ccmArchimedeanFormToAperture a u with hfdef
  have hplus : inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0 := hu.1
  have hminus : inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0 := hu.2
  rw [hQ u hu]
  set φ : ℝ → ℝ := fun ξ => ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 with hφ
  have hφint : Integrable φ := integrable_norm_sq_ccmFormDomain _ u
  have hφnn : ∀ ξ, 0 ≤ φ ξ := fun ξ => by positivity
  have hφF : φ =ᵐ[volume] fun ξ => ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 := by
    filter_upwards [ccmFormDomain_ae_eq_fourier a u] with ξ hξ
    simp only [hφ, hξ, hfdef]
  set g := gridStepWeight h K G
  have hgmeas : Measurable g := measurable_gridStepWeight h K G
  have hgbdd : ∀ ξ, ‖g ξ‖ ≤ ∑ k ∈ Finset.range K, 2 * |G k| := by
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (gridStepWeight_nonneg hG ξ)]
    exact gridStepWeight_le ξ
  have hgφint : Integrable (fun ξ => g ξ * φ ξ) :=
    hφint.bdd_mul hgmeas.aestronglyMeasurable (Filter.Eventually.of_forall hgbdd)
  have hWint : Integrable (fun ξ => M ξ * φ ξ) := hMint u
  have hstep1 : ∫ ξ, (α - g ξ) * φ ξ ≤ ∫ ξ, M ξ * φ ξ := by
    apply integral_mono ((hφint.const_mul α).sub hgφint |>.congr
      (Filter.Eventually.of_forall fun ξ => by simp only [Pi.sub_apply]; ring)) hWint
    intro ξ
    exact mul_le_mul_of_nonneg_right
      (sub_gridStepWeight_le_of_shells hh hG hshell htail ξ) (hφnn ξ)
  have hsplit : ∫ ξ, (α - g ξ) * φ ξ = (α * ∫ ξ, φ ξ) - ∫ ξ, g ξ * φ ξ := by
    have hfun : (fun ξ => (α - g ξ) * φ ξ) = fun ξ => α * φ ξ - g ξ * φ ξ := by
      funext ξ
      ring
    rw [hfun, integral_sub (hφint.const_mul α) hgφint, integral_const_mul]
  have hshellInt : ∀ k < K, ∀ S : Set ℝ, MeasurableSet S →
      (∀ ξ ∈ S, (k : ℝ) * h ≤ |ξ| ∧ |ξ| < ((k : ℝ) + 1) * h) → volume S ≤ ENNReal.ofReal h →
      ∫ ξ in S, φ ξ ≤ h * (R k * ‖f‖ ^ 2) := by
    intro k hk S hS hSmem hvol
    have hR0 : 0 ≤ R k * ‖f‖ ^ 2 := by
      have hpt := hR k hk f hplus hminus (k * h) (by
        rw [abs_of_nonneg (by positivity)]) (by
        rw [abs_of_nonneg (by positivity)]; nlinarith)
      exact (sq_nonneg _).trans hpt
    have hle : ∫ ξ in S, φ ξ ≤ ∫ ξ in S, R k * ‖f‖ ^ 2 := by
      have hfin : volume S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
      apply setIntegral_mono_ae_restrict hφint.integrableOn (integrableOn_const hfin)
      rw [Filter.EventuallyLE, ae_restrict_iff' hS]
      filter_upwards [hφF] with ξ hξ hmem
      rw [hξ]
      exact hR k hk f hplus hminus ξ (hSmem ξ hmem).1 (hSmem ξ hmem).2
    refine hle.trans ?_
    rw [setIntegral_const, smul_eq_mul]
    have hvolr : volume.real S ≤ h := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hh.le hvol
    exact mul_le_mul_of_nonneg_right hvolr hR0
  have hstep2 : ∫ ξ, g ξ * φ ξ ≤
      ∑ k ∈ Finset.range K, 2 * h * G k * R k * ‖f‖ ^ 2 := by
    have hexp : (fun ξ => g ξ * φ ξ) = fun ξ => ∑ k ∈ Finset.range K,
        (G k * ((Ico (k * h) ((k + 1) * h)).indicator φ ξ +
          (Ioc (-((k + 1) * h)) (-(k * h))).indicator φ ξ)) := by
      funext ξ
      simp only [g, gridStepWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Set.indicator_apply]
      split_ifs <;> ring
    rw [hexp, integral_finsetSum]
    · apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [integral_const_mul, integral_add (hφint.indicator measurableSet_Ico)
        (hφint.indicator measurableSet_Ioc), integral_indicator measurableSet_Ico,
        integral_indicator measurableSet_Ioc]
      have hpos := hshellInt k hk' (Ico (k * h) ((k + 1) * h)) measurableSet_Ico
        (fun ξ hξ => by
          have h0 : 0 ≤ (k : ℝ) * h := by positivity
          rw [abs_of_nonneg (h0.trans hξ.1)]
          exact ⟨hξ.1, hξ.2⟩)
        (by rw [Real.volume_Ico]; apply le_of_eq; congr 1; ring)
      have hneg := hshellInt k hk' (Ioc (-((k + 1) * h)) (-(k * h))) measurableSet_Ioc
        (fun ξ hξ => by
          have h0 : 0 ≤ (k : ℝ) * h := by positivity
          by_cases hz : ξ = 0
          · subst hz
            have hk0 : (k : ℝ) * h = 0 := by
              have := hξ.2
              linarith
            simp only [abs_zero]
            exact ⟨hk0.le, by nlinarith⟩
          · have hξneg : ξ ≤ 0 := hξ.2.trans (by linarith)
            rw [abs_of_nonpos hξneg]
            exact ⟨by linarith [hξ.2], by linarith [hξ.1]⟩)
        (by rw [Real.volume_Ioc]; apply le_of_eq; congr 1; ring)
      have hGk := hG k
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hpos hneg) hGk]
    · intro k _
      exact ((hφint.indicator measurableSet_Ico).add
        (hφint.indicator measurableSet_Ioc)).const_mul _
  have hnorm : ∫ ξ, φ ξ = ‖f‖ ^ 2 := integral_norm_sq_ccmFormDomain _ u
  rw [hsplit, hnorm] at hstep1
  have hsum : ∑ k ∈ Finset.range K, 2 * h * G k * R k * ‖f‖ ^ 2 =
      (∑ k ∈ Finset.range K, 2 * h * G k * R k) * ‖f‖ ^ 2 := by
    rw [Finset.sum_mul]
  have hfin : (α - ∑ k ∈ Finset.range K, 2 * h * G k * R k) * ‖f‖ ^ 2 =
      α * ‖f‖ ^ 2 - (∑ k ∈ Finset.range K, 2 * h * G k * R k) * ‖f‖ ^ 2 := by ring
  rw [hfin]
  linarith [hstep1, hstep2, hsum]

end RHTower
