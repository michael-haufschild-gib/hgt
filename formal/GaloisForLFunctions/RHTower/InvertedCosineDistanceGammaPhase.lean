import GaloisForLFunctions.RHTower.DoublyBlindCorePoleDistance
import GaloisForLFunctions.RHTower.PrimeBlindPoleCuspIdentity
import GaloisForLFunctions.HTGeometry.MellinPlancherelBound
import GaloisForLFunctions.HTGeometry.MellinConjugate
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# The distance to cosine self-duality is the Riemann–Siegel phase defect

Let `f` be smooth and supported in `[α, β]`, `0 < α ≤ β`, with half-line cosine transform `Cf`,
inverted cosine transform `JCf(y) = Cf(1/y)/y` and cosine–dilation kernel `Ψ_f = Cf ⋆ f`.  On the
critical line write `M(t) = 𝓜f(½+it)` and `r(t) = Γ_ℝ(½+it)/Γ_ℝ(½−it)`, the archimedean phase:
`|r(t)| = 1` and `r(t) = e^{2iθ(t)}` with `θ` the Riemann–Siegel phase.

**Theorem** (`integral_sq_sub_invertedCosTransform_eq_gammaPhase`).
`∫_0^∞ (f − JCf)² = (1/2π) ∫ |M(t)|² |1 − r(t)|² dt`.

Since `|1 − e^{2iθ}|² = 4 sin² θ`, the squared distance of `f` from its inverted cosine transform is
the spectral mass of `f` weighted by `4 sin² θ(t)`.  It vanishes exactly on spectra carried by the
Gram set `θ(t) ∈ πℤ`.

**Corollary** (`cosDilationKernel_zero_eq_gammaPhase_of_doublyBlind`,
`pole_eq_gammaPhase_of_doublyBlind`).  If `f` is doubly blind (`A_f(n) = 0` and `Ψ_f(n) = 0` for
every integer `|n| ≥ 2`), its Weil pole term is an on-line multiplier form:
`2 (∫ f)(∫ f(y)/y dy) = Ψ_f(0) = (1/2π) ∫ |M(t)|² |1 − r(t)|² dt`.
Adding the archimedean term `(1/2π) ∫ |M|² 2θ'`, the prime-blind energy of a doubly blind test is
`(1/2π) ∫ |M(t)|² (4 sin² θ(t) + 2θ'(t)) dt`.  The multiplier is negative only on two bounded
windows of low frequency, so doubly blind tests cannot detect zeros at large height.

**Proof.**
* *Plancherel.* `∫_0^∞ f² = (1/2π) ∫ |M|²` (`integral_Ioi_sq_eq_integral_norm_mellin_sq`), from the
  Mellin–Plancherel identity and the substitution `y = e^{−v}`.
* *Phase form of `Ψ_f(1)`.* The corpus Mellin inversion of `Ψ_f` at `x = 1`, with
  `𝓜f(1 − s) = conj 𝓜f(s)` on the line, gives `Ψ_f(1) = (1/2π) ∫ Re r(t) |M(t)|² dt`
  (`cosDilationKernel_one_eq_integral_gammaPhase`).
* *Expansion.* `∫ (f − JCf)² = 2∫ f² − 2Ψ_f(1)`, because `∫ (JCf)² = ∫ (Cf)² = ∫ f²` and
  `∫ f · JCf = Ψ_f(1)`.  Finally `|1 − r|² = 2 − 2 Re r` as `|r| = 1`.
-/

open MeasureTheory Set Real Complex
open scoped ContDiff ComplexConjugate

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-- The critical-line point `½ + iy`. -/
def phaseLinePt (y : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I

/-- The archimedean phase `Γ_ℝ(½+iy)/Γ_ℝ(½−iy) = e^{2iθ(y)}`. -/
def gammaPhaseRatio (y : ℝ) : ℂ :=
  Complex.Gammaℝ (phaseLinePt y) / Complex.Gammaℝ (1 - phaseLinePt y)

theorem one_sub_phaseLinePt (y : ℝ) : 1 - phaseLinePt y = conj (phaseLinePt y) := by
  apply Complex.ext <;> norm_num [phaseLinePt]

/-- Conjugation equivariance of `Γ_ℝ`. -/
theorem gammaℝ_conj_eq (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  have hπ : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Ne.symm Real.pi_ne_zero
  congr 1
  · have hx : (Real.pi : ℂ) ^ (conj (-s / 2)) = conj ((Real.pi : ℂ) ^ (-s / 2)) := by
      have h := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) hπ
      rwa [Complex.conj_ofReal] at h
    rw [← hx]
    congr 1
    rw [map_div₀, map_neg, map_ofNat]
  · rw [← Complex.Gamma_conj]
    congr 1
    rw [map_div₀, map_ofNat]

/-- The archimedean phase is unimodular on the critical line. -/
theorem norm_gammaPhaseRatio (y : ℝ) : ‖gammaPhaseRatio y‖ = 1 := by
  have hne : Complex.Gammaℝ (phaseLinePt y) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [phaseLinePt])
  rw [gammaPhaseRatio, one_sub_phaseLinePt, gammaℝ_conj_eq, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hne)]

/-- `|1 − r|² = 2 − 2 Re r` for the unimodular phase `r`. -/
theorem norm_one_sub_gammaPhaseRatio_sq (y : ℝ) :
    ‖1 - gammaPhaseRatio y‖ ^ 2 = 2 - 2 * (gammaPhaseRatio y).re := by
  have h1 := Complex.normSq_eq_norm_sq (gammaPhaseRatio y)
  rw [norm_gammaPhaseRatio, Complex.normSq_apply] at h1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith

/-- Reflection of the Mellin transform of a real function across the critical line. -/
theorem mellin_one_sub_phaseLinePt (f : ℝ → ℝ) (y : ℝ) :
    mellin (fun t => (f t : ℂ)) (1 - phaseLinePt y) =
      conj (mellin (fun t => (f t : ℂ)) (phaseLinePt y)) := by
  rw [one_sub_phaseLinePt]
  exact GaloisForLFunctions.HTGeometry.mellin_conj_of_conj_invariant
    (fun t => Complex.conj_ofReal _) _

/-- The Mellin transform of a compactly supported continuous function converges on every line. -/
theorem mellinConvergent_ofReal_of_support (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (s : ℂ) :
    MellinConvergent (fun t => (f t : ℂ)) s := by
  unfold MellinConvergent
  refine (ContinuousOn.integrableOn_compact (isCompact_Icc (a := α) (b := β))
    fun t ht => ?_).of_forall_sdiff_eq_zero measurableSet_Ioi fun t ht => ?_
  · have ht0 : t ≠ 0 := (lt_of_lt_of_le hα ht.1).ne'
    exact ((Complex.continuousAt_ofReal_cpow_const t _ (Or.inr ht0)).smul
      (Complex.continuous_ofReal.comp hf).continuousAt).continuousWithinAt
  · simp [eq_zero_of_not_mem_Icc hsupp ht.2]

/-- The squared Mellin modulus is integrable along the critical line. -/
theorem integrable_norm_mellin_phaseLinePt_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Integrable fun y : ℝ => ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := (isTest_ofReal_of_support hf hα hαβ hsupp).exists_norm_mellin_le_decay 1
  have hcont := continuous_mellin_verticalLine_of_continuous
    (Complex.continuous_ofReal.comp hf.continuous)
    (mellinConvergent_ofReal_of_support hf.continuous hα hsupp ((1 / 2 : ℝ) : ℂ))
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (C ^ 2))
    (hcont.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hb : ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ≤ C / (1 + y ^ 2) := by
    have h := hC (phaseLinePt y) (by simp [phaseLinePt]; norm_num [abs_of_neg])
    simpa [phaseLinePt] using h
  have hy : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 ≤ (C / (1 + y ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = C ^ 2 / (1 + y ^ 2) ^ 2 := by rw [div_pow]
    _ ≤ C ^ 2 / (1 + y ^ 2) :=
        div_le_div_of_nonneg_left (sq_nonneg C) (by positivity) (by nlinarith)
    _ = C ^ 2 * (1 + y ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- **Mellin–Plancherel on the critical line**: `∫_0^∞ f² = (1/2π) ∫ |𝓜f(½+it)|² dt`. -/
theorem integral_Ioi_sq_eq_integral_norm_mellin_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ y in Ioi 0, f y ^ 2 =
      1 / (2 * π) * ∫ y : ℝ, ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 := by
  have hF : ContDiff ℝ ∞ (fun t => (f t : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hsF : Function.support (fun t => (f t : ℂ)) ⊆ Icc α β := fun y hy => by
    have : f y ≠ 0 := by simpa using hy
    exact hsupp y this
  have hP := GaloisForLFunctions.HTGeometry.MellinPlancherel.integral_norm_sq_mellin_eq hF hα hsF
    (1 / 2)
  have hlog : ∀ v : ℝ,
      ‖GaloisForLFunctions.HTGeometry.MellinPlancherel.logPull (fun t => (f t : ℂ)) (1 / 2) v‖ ^ 2
        = Real.exp (-v) * f (Real.exp (-v)) ^ 2 := by
    intro v
    simp only [GaloisForLFunctions.HTGeometry.MellinPlancherel.logPull, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_real]
    rw [mul_pow, sq_abs, sq (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  simp_rw [hlog] at hP
  have hneg : ∫ v : ℝ, Real.exp (-v) * f (Real.exp (-v)) ^ 2 =
      ∫ v : ℝ, Real.exp v * f (Real.exp v) ^ 2 :=
    integral_neg_eq_self (fun v : ℝ => Real.exp v * f (Real.exp v) ^ 2) volume
  rw [hneg, ← GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp (fun z => f z ^ 2)] at hP
  have hM : (fun y : ℝ => ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2) =
      fun t : ℝ => ‖mellin (fun t => (f t : ℂ)) (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 := rfl
  rw [hM, hP]
  field_simp

/-- The integrand of the inverse Mellin transform of `Ψ_f` on the critical line. -/
theorem gammaRatio_mellin_mul_eq (f : ℝ → ℝ) (y : ℝ) :
    Complex.Gammaℝ (phaseLinePt y) / Complex.Gammaℝ (1 - phaseLinePt y) *
        mellin (fun t => (f t : ℂ)) (phaseLinePt y) *
        mellin (fun t => (f t : ℂ)) (1 - phaseLinePt y) =
      gammaPhaseRatio y * ((‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 : ℝ) : ℂ) := by
  rw [mellin_one_sub_phaseLinePt, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    gammaPhaseRatio]

/-- The phase-weighted Mellin modulus is integrable along the critical line. -/
theorem integrable_gammaPhaseRatio_mul_norm_mellin_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Integrable fun y : ℝ =>
      gammaPhaseRatio y * ((‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 : ℝ) : ℂ) := by
  have hv := verticalIntegrable_mellin_cosDilationKernel hf hα hαβ hsupp
  unfold Complex.VerticalIntegrable at hv
  refine hv.congr (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mellin_cosDilationKernel_eq_gammaRatio hf hα hsupp y]
  exact gammaRatio_mellin_mul_eq f y

/-- **The phase form of `Ψ_f(1)`**: `Ψ_f(1) = (1/2π) ∫ Re r(t) |𝓜f(½+it)|² dt`. -/
theorem cosDilationKernel_one_eq_integral_gammaPhase (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    cosDilationKernel f 1 = 1 / (2 * π) *
      ∫ y : ℝ, (gammaPhaseRatio y).re * ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 := by
  have h := mellinInv_gammaRatio_mellin_eq_cosDilationKernel hf hα hαβ hsupp one_pos
  unfold mellinInv at h
  simp only [Complex.ofReal_one, Complex.one_cpow, one_smul] at h
  have hI : ∀ y : ℝ,
      Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + y * Complex.I) /
          Complex.Gammaℝ (1 - (((1 / 2 : ℝ) : ℂ) + y * Complex.I)) *
          mellin (fun y => (f y : ℂ)) (((1 / 2 : ℝ) : ℂ) + y * Complex.I) *
          mellin (fun y => (f y : ℂ)) (1 - (((1 / 2 : ℝ) : ℂ) + y * Complex.I)) =
        gammaPhaseRatio y * ((‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 : ℝ) : ℂ) :=
    fun y => gammaRatio_mellin_mul_eq f y
  simp_rw [hI] at h
  have hre := congrArg Complex.re h
  have hcomm := integral_re (integrable_gammaPhaseRatio_mul_norm_mellin_sq hf hα hαβ hsupp)
  simp only [RCLike.re_to_complex] at hcomm
  rw [Complex.ofReal_re, Complex.smul_re, smul_eq_mul, ← hcomm] at hre
  rw [← hre]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Complex.re_mul_ofReal]

/-- **The distance to cosine self-duality** (general form):
`∫_0^∞ (f − JCf)² = 2 ∫_0^∞ f² − 2 Ψ_f(1)`. -/
theorem integral_sq_sub_invertedCosTransform_eq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ y in Ioi 0, (f y - invertedCosTransform f y) ^ 2 =
      2 * ∫ y in Ioi 0, f y ^ 2 - 2 * cosDilationKernel f 1 := by
  have h1 := integrableOn_sq_of_support hf hsupp
  have h2 := integrableOn_mul_invertedCosTransform hf hα hsupp
  have h3 := integrableOn_invertedCosTransform_sq hf hα hsupp
  have hexp : ∀ y, (f y - invertedCosTransform f y) ^ 2 =
      f y ^ 2 - 2 * (f y * invertedCosTransform f y) + invertedCosTransform f y ^ 2 :=
    fun y => by ring
  have h12 : IntegrableOn (fun y => f y ^ 2 - 2 * (f y * invertedCosTransform f y)) (Ioi 0) :=
    h1.sub (h2.const_mul 2)
  have h2' : IntegrableOn (fun y => 2 * (f y * invertedCosTransform f y)) (Ioi 0) :=
    h2.const_mul 2
  simp only [hexp]
  rw [integral_add h12 h3, integral_sub h1 h2', integral_const_mul,
    ← cosDilationKernel_one_eq_integral_mul_inverted, integral_Ioi_invertedCosTransform_sq,
    integral_Ioi_halfLineCosTransform_sq hf hα hsupp]
  linarith

/-- **The distance to cosine self-duality is the phase defect**:
`∫_0^∞ (f − JCf)² = (1/2π) ∫ |𝓜f(½+it)|² |1 − r(t)|² dt`, with `|1 − r|² = 4 sin² θ`. -/
theorem integral_sq_sub_invertedCosTransform_eq_gammaPhase (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ y in Ioi 0, (f y - invertedCosTransform f y) ^ 2 =
      1 / (2 * π) * ∫ y : ℝ, ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 *
        ‖1 - gammaPhaseRatio y‖ ^ 2 := by
  have hM := integrable_norm_mellin_phaseLinePt_sq hf hα hαβ hsupp
  have hR : Integrable fun y : ℝ =>
      (gammaPhaseRatio y).re * ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 :=
    (integrable_gammaPhaseRatio_mul_norm_mellin_sq hf hα hαβ hsupp).re.congr
      (Filter.Eventually.of_forall fun y => by
        simp only [RCLike.re_to_complex, Complex.re_mul_ofReal])
  have e : ∀ y : ℝ, ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 *
      ‖1 - gammaPhaseRatio y‖ ^ 2 =
        2 * ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 -
          2 * ((gammaPhaseRatio y).re * ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2) :=
    fun y => by rw [norm_one_sub_gammaPhaseRatio_sq]; ring
  simp_rw [e]
  rw [integral_sub (hM.const_mul 2) (hR.const_mul 2), integral_const_mul, integral_const_mul,
    integral_sq_sub_invertedCosTransform_eq hf hα hsupp,
    integral_Ioi_sq_eq_integral_norm_mellin_sq hf hα hsupp,
    cosDilationKernel_one_eq_integral_gammaPhase hf hα hαβ hsupp]
  ring

/-- **The zeroth null-face coefficient of a doubly blind core is the phase defect**:
`Ψ_f(0) = (1/2π) ∫ |𝓜f(½+it)|² |1 − r(t)|² dt`. -/
theorem cosDilationKernel_zero_eq_gammaPhase_of_doublyBlind (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0)
    (hΨ : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) :
    cosDilationKernel f 0 = 1 / (2 * π) * ∫ y : ℝ,
      ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 * ‖1 - gammaPhaseRatio y‖ ^ 2 := by
  rw [cosDilationKernel_zero_eq_integral_sq_sub_inverted hf hα hαβ hsupp hA hΨ,
    integral_sq_sub_invertedCosTransform_eq_gammaPhase hf hα hαβ hsupp]

/-- **The Weil pole term of a doubly blind core is an on-line multiplier form**:
`2 (∫ f)(∫ f(y)/y dy) = (1/2π) ∫ |𝓜f(½+it)|² |1 − r(t)|² dt`. -/
theorem pole_eq_gammaPhase_of_doublyBlind (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0)
    (hΨ : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) :
    2 * (∫ y in Ioi (0 : ℝ), f y) * (∫ y in Ioi (0 : ℝ), f y / y) = 1 / (2 * π) * ∫ y : ℝ,
      ‖mellin (fun t => (f t : ℂ)) (phaseLinePt y)‖ ^ 2 * ‖1 - gammaPhaseRatio y‖ ^ 2 := by
  rw [← cosDilationKernel_zero_eq,
    cosDilationKernel_zero_eq_gammaPhase_of_doublyBlind hf hα hαβ hsupp hA hΨ]

end

end RHTower
