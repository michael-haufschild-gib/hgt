import GaloisForLFunctions.RHTower.GaussianCentralGapBohrSpectrum
import GaloisForLFunctions.RHTower.GaussianGapSignAbscissa

/-!
# The extremal Bohr spectrum of the Gaussian prime gap

Let `G(y) = Σ Λ(n) n^{-1/2} e^{-yn²} − ∫₁^∞ u^{-1/2} e^{-yu²} du` and let `Θ = sup Re ρ` be the
zero abscissa.  No hypothesis on the zeros is made.

* **Germ expansion for every zero** (`norm_zeroGerm_sub_gamma_le`).  For `Re a > −2`, `a ≠ 0`,
  `‖e^{-y}/a + E(y, a) − ½ Γ(a/2) y^{-a/2}‖ ≤ (2y + 2y²)/(‖a‖‖a+2‖)`.
* **Unconditional expansion** (`gaussianCentralGap_eq_archimedean_sub_zeroSeries`).
  `G(y) = A_y(½) − Σ_ρ ½ Γ((ρ−½)/2) y^{-(ρ−½)/2} − O(y)`, with `Σ_ρ ‖Γ((ρ−½)/2)‖ < ∞`.
* **Extremal Bohr spectrum** (`tendsto_gaussianWindowAverage_weightedGap`).  If every zero has
  `Re ρ ≤ θ`, then for every real `τ` the window averages of
  `e^{-(θ−½)u/2} G(e^{-u}) e^{-iτu}` converge to
  `A(½)·[θ = ½, τ = 0] − Σ_{Re ρ = θ, Im ρ = 2τ} ½ Γ((ρ−½)/2)`.
  Zeros strictly left of `θ` are damped out; the zeros on the line `Re ρ = θ` are read exactly.
* **Visibility of the extremal line** (`exists_weightedBohrCoefficient_ne_zero_iff`).  For
  `θ = Θ > ½`, some `Θ`-weighted Bohr coefficient is nonzero iff some zero lies on `Re ρ = Θ`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-! ## Germs of arbitrary zeros -/

/-- **Germ expansion.**  For `Re a > −2`, `a ≠ 0`, `y > 0`,
`‖e^{-y}/a + E(y, a) − ½ Γ(a/2) y^{-a/2}‖ ≤ (2y + 2y²)/(‖a‖‖a+2‖)`. -/
theorem norm_zeroGerm_sub_gamma_le {y : ℝ} (hy : 0 < y) {a : ℂ} (ha : -2 < a.re)
    (ha0 : a ≠ 0) :
    ‖(Real.exp (-y) : ℂ) / a + gaussianIncompleteMellin y a -
        (1 / 2 : ℂ) * Complex.Gamma (a / 2) * (y : ℂ) ^ (-(a / 2))‖ ≤
      (2 * y + 2 * y ^ 2) / (‖a‖ * ‖a + 2‖) := by
  have ha2 : a + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hb : 2 < (a + 2 + 2).re := by simp; linarith
  have hE4 := norm_gaussianIncompleteMellin_sub_gamma_le hy (by linarith)
  have hE4' : ‖gaussianIncompleteMellin y (a + 2 + 2) - (1 / 2 : ℂ) * (y : ℂ) ^ (-((a + 2 + 2) / 2)) *
      Complex.Gamma ((a + 2 + 2) / 2)‖ ≤ 1 / 2 :=
    hE4.trans (by rw [div_le_div_iff₀ (by linarith) two_pos]; linarith)
  rw [gaussianIncompleteMellin_recursion hy ha0, gaussianIncompleteMellin_recursion hy ha2]
  set e : ℂ := (Real.exp (-y) : ℂ) with he
  set E4 : ℂ := gaussianIncompleteMellin y (a + 2 + 2) with hE4def
  set M4 : ℂ := (1 / 2 : ℂ) * (y : ℂ) ^ (-((a + 2 + 2) / 2)) * Complex.Gamma ((a + 2 + 2) / 2)
    with hM4
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hpow : (y : ℂ) ^ (-((a + 2 + 2) / 2)) = (y : ℂ) ^ (-(a / 2)) * ((y : ℂ) ^ 2)⁻¹ := by
    rw [show -((a + 2 + 2) / 2) = -(a / 2) + (-2 : ℂ) by ring, Complex.cpow_add _ _ hy0]
    congr 1
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have ha2' : a / 2 ≠ 0 := div_ne_zero ha0 two_ne_zero
  have ha21 : a / 2 + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hgam : Complex.Gamma ((a + 2 + 2) / 2) = (a / 2 + 1) * (a / 2) * Complex.Gamma (a / 2) := by
    rw [show (a + 2 + 2) / 2 = (a / 2 + 1) + 1 by ring, Complex.Gamma_add_one _ ha21,
      Complex.Gamma_add_one _ ha2']
    ring
  have hmain : 2 * (y : ℂ) / a * (2 * (y : ℂ) / (a + 2) * M4) =
      (1 / 2 : ℂ) * Complex.Gamma (a / 2) * (y : ℂ) ^ (-(a / 2)) := by
    rw [hM4, hpow, hgam]
    field_simp
  have hexp : e / a + (-e / a + 2 * (y : ℂ) / a * (-e / (a + 2) + 2 * (y : ℂ) / (a + 2) * E4)) -
      (1 / 2 : ℂ) * Complex.Gamma (a / 2) * (y : ℂ) ^ (-(a / 2)) =
      -(2 * (y : ℂ) * e / (a * (a + 2))) + 4 * (y : ℂ) ^ 2 / (a * (a + 2)) * (E4 - M4) := by
    rw [← hmain]
    field_simp
    ring
  rw [hexp]
  have he1 : ‖e‖ ≤ 1 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hprod : 0 < ‖a‖ * ‖a + 2‖ := mul_pos (norm_pos_iff.2 ha0) (norm_pos_iff.2 ha2)
  have h1 : ‖-(2 * (y : ℂ) * e / (a * (a + 2)))‖ ≤ 2 * y / (‖a‖ * ‖a + 2‖) := by
    rw [norm_neg, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy, Complex.norm_two]
    apply div_le_div_of_nonneg_right _ hprod.le
    have := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ 2 * y)
    linarith
  have h2 : ‖4 * (y : ℂ) ^ 2 / (a * (a + 2)) * (E4 - M4)‖ ≤ 2 * y ^ 2 / (‖a‖ * ‖a + 2‖) := by
    rw [norm_mul, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    calc 4 * y ^ 2 / (‖a‖ * ‖a + 2‖) * ‖E4 - M4‖ ≤ 4 * y ^ 2 / (‖a‖ * ‖a + 2‖) * (1 / 2) := by
          gcongr
      _ = 2 * y ^ 2 / (‖a‖ * ‖a + 2‖) := by ring
  calc _ ≤ ‖-(2 * (y : ℂ) * e / (a * (a + 2)))‖ + ‖4 * (y : ℂ) ^ 2 / (a * (a + 2)) * (E4 - M4)‖ :=
        norm_add_le _ _
    _ ≤ 2 * y / (‖a‖ * ‖a + 2‖) + 2 * y ^ 2 / (‖a‖ * ‖a + 2‖) := add_le_add h1 h2
    _ = (2 * y + 2 * y ^ 2) / (‖a‖ * ‖a + 2‖) := by ring

/-- The amplitude `½ Γ((ρ−½)/2)` of a zero copy. -/
def zeroBohrAmplitude (q : XiZeroCopy) : ℂ := (1 / 2 : ℂ) * Complex.Gamma ((xiZero q - 1 / 2) / 2)

theorem re_xiZero_sub_half_bounds (q : XiZeroCopy) :
    -(1 / 2) < (xiZero q - 1 / 2).re ∧ (xiZero q - 1 / 2).re < 1 / 2 := by
  have h0 : 0 < (xiZero q).re := xiZeroCopy_re_pos q
  have h1 : (xiZero q).re < 1 := by
    by_contra h
    push Not at h
    exact xi_ne_zero_of_one_le_re h (xi_xiZero q)
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  constructor <;> linarith

theorem xiZero_sub_half_ne_zero (q : XiZeroCopy) : xiZero q - 1 / 2 ≠ 0 := by
  intro h
  have him : (xiZero q - 1 / 2).im = 0 := by rw [h, Complex.zero_im]
  simp at him
  exact xi_ne_zero_of_abs_im_le_one (by rw [him, abs_zero]; norm_num) (xi_xiZero q)

/-- **Germ = Bohr term + O(y) for every zero.** -/
theorem norm_criticalZeroGerm_sub_zeroBohr_le {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    ‖criticalZeroGerm y q - zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ ≤
      (2 * y + 2 * y ^ 2) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  set a : ℂ := xiZero q - 1 / 2 with ha
  have hcast : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have hb := re_xiZero_sub_half_bounds q
  rw [← ha] at hb
  have ha0 : a ≠ 0 := xiZero_sub_half_ne_zero q
  have h := norm_zeroGerm_sub_gamma_le hy (by linarith [hb.1]) ha0
  have hgerm : criticalZeroGerm y q = (Real.exp (-y) : ℂ) / a + gaussianIncompleteMellin y a := by
    rw [criticalZeroGerm, hcast]
  rw [hgerm, zeroBohrAmplitude, ← ha, mul_assoc]
  rw [mul_assoc] at h
  refine h.trans ?_
  have hnab : ‖a‖ ≤ ‖a + 2‖ := by
    have h1 : ‖a‖ ^ 2 ≤ ‖a + 2‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat]
      nlinarith [hb.1]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  rw [norm_inv, inv_pow, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity [norm_pos_iff.2 ha0])
  rw [sq]
  exact mul_le_mul_of_nonneg_left hnab (norm_nonneg _)

theorem xiZero_re_le_one (q : XiZeroCopy) : (xiZero q).re ≤ 1 := by
  have h := (re_xiZero_sub_half_bounds q).2
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at h
  linarith

/-- Every germ is `O(‖(ρ−½)⁻¹‖²)` at `y = 1`. -/
theorem exists_norm_criticalZeroGerm_one_le :
    ∃ W : ℝ, ∀ q : XiZeroCopy, ‖criticalZeroGerm 1 q‖ ≤ W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
  ⟨_, fun q => norm_zeroGerm_le_of_re_le (θ := 1) (σ := 1 / 2) one_pos (by norm_num) q
    (xiZero_re_le_one q)⟩

/-- The zero amplitudes are absolutely summable. -/
theorem summable_norm_zeroBohrAmplitude :
    Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := by
  obtain ⟨W, hW⟩ := exists_norm_criticalZeroGerm_one_le
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (summable_norm_inv_xiZero_sub_half_sq.mul_left (W + 4))
  have h1 := norm_criticalZeroGerm_sub_zeroBohr_le one_pos q
  rw [Complex.ofReal_one, Complex.one_cpow, mul_one] at h1
  have h3 : ‖zeroBohrAmplitude q‖ ≤ ‖criticalZeroGerm 1 q‖ +
      ‖criticalZeroGerm 1 q - zeroBohrAmplitude q‖ := by
    have := norm_sub_le (criticalZeroGerm 1 q) (criticalZeroGerm 1 q - zeroBohrAmplitude q)
    rwa [sub_sub_cancel] at this
  have h2 := hW q
  nlinarith

/-! ## The unconditional expansion -/

theorem summable_criticalZeroGerm {y : ℝ} (hy : 0 < y) :
    Summable fun q : XiZeroCopy => criticalZeroGerm y q := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ, ∀ q : XiZeroCopy,
      ‖criticalZeroGerm y q‖ ≤ W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    ⟨_, fun q => norm_zeroGerm_le_of_re_le (θ := 1) (σ := 1 / 2) hy (by norm_num) q
      (xiZero_re_le_one q)⟩
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _) hW
    (summable_norm_inv_xiZero_sub_half_sq.mul_left W))

theorem summable_zeroGermRemainder {y : ℝ} (hy : 0 < y) :
    Summable fun q : XiZeroCopy => criticalZeroGerm y q -
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2)) :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => norm_criticalZeroGerm_sub_zeroBohr_le hy q)
    (summable_norm_inv_xiZero_sub_half_sq.mul_left _))

/-- **Unconditional expansion.**  For `y > 0`,
`G(y) = A_y(½) − Σ_ρ ½ Γ((ρ−½)/2) y^{-(ρ−½)/2} − Σ_ρ R_ρ(y)` with `|R_ρ(y)| ≤ (2y+2y²)|ρ−½|^{-2}`. -/
theorem gaussianCentralGap_eq_archimedean_sub_zeroSeries {y : ℝ} (hy : 0 < y) :
    ((gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y : ℝ) : ℂ) =
      gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ) -
        (∑' q : XiZeroCopy, zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))) -
        ∑' q : XiZeroCopy, (criticalZeroGerm y q -
          zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))) := by
  have hgap := gaussianWeightedGap_eq_MB_sub_germField (σ := 1 / 2) (by norm_num) hy
  have hR := summable_zeroGermRemainder hy
  have hS : Summable fun q : XiZeroCopy =>
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2)) :=
    ((summable_criticalZeroGerm hy).sub hR).congr fun q => by ring
  rw [hgap, sub_sub, ← hS.tsum_add hR]
  congr 1
  refine tsum_congr fun q => ?_
  rw [add_sub_cancel, criticalZeroGerm]

theorem exp_neg_cpow_eq_cexp_mul (u : ℝ) (z : ℂ) :
    ((Real.exp (-u) : ℝ) : ℂ) ^ z = Complex.exp (-(u : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  push_cast
  ring_nf

/-! ## The weighted Bohr spectrum -/

/-- The `θ`-weighted Bohr term of a zero copy at `u`. -/
def weightedZeroTerm (θ u : ℝ) (q : XiZeroCopy) : ℂ :=
  zeroBohrAmplitude q * Complex.exp (((xiZero q - 1 / 2) - ((θ - 1 / 2 : ℝ) : ℂ)) * (u : ℂ) / 2)

theorem norm_weightedZeroTerm (θ u : ℝ) (q : XiZeroCopy) :
    ‖weightedZeroTerm θ u q‖ = ‖zeroBohrAmplitude q‖ * Real.exp (((xiZero q).re - θ) * u / 2) := by
  rw [weightedZeroTerm, norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, mul_zero, sub_zero]
  ring

theorem weightedZeroTerm_of_re_eq {θ : ℝ} (u : ℝ) {q : XiZeroCopy} (hq : (xiZero q).re = θ) :
    weightedZeroTerm θ u q =
      zeroBohrAmplitude q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) := by
  rw [weightedZeroTerm, xiZeroHalfOrdinate]
  congr 2
  have hz : xiZero q - 1 / 2 - ((θ - 1 / 2 : ℝ) : ℂ) = (((xiZero q).im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hq]
  rw [hz]
  push_cast
  ring

theorem summable_weightedZeroTerm (θ u : ℝ) :
    Summable fun q : XiZeroCopy => weightedZeroTerm θ u q := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (summable_norm_zeroBohrAmplitude.mul_right (Real.exp ((1 + |θ|) * |u| / 2))))
  rw [norm_weightedZeroTerm]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
  have h0 : 0 < (xiZero q).re := xiZeroCopy_re_pos q
  have h1 := xiZero_re_le_one q
  have hβ : |(xiZero q).re - θ| ≤ 1 + |θ| := by
    rw [abs_le]; constructor <;> cases abs_cases θ <;> linarith
  have h2 : ((xiZero q).re - θ) * u ≤ (1 + |θ|) * |u| := by
    calc ((xiZero q).re - θ) * u ≤ |((xiZero q).re - θ) * u| := le_abs_self _
      _ = |(xiZero q).re - θ| * |u| := abs_mul _ _
      _ ≤ (1 + |θ|) * |u| := by gcongr
  linarith

/-- **Extremal decomposition.**  If every zero has `Re ρ ≤ θ`, then
`e^{-(θ−½)u/2} G(e^{-u}) + Σ_{Re ρ = θ} ½ Γ((ρ−½)/2) e^{i (Im ρ/2) u} − [θ = ½] A(½) → 0` as `u → ∞`. -/
theorem tendsto_weightedGap_add_extremalSeries {θ : ℝ} (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) :
    Tendsto (fun u : ℝ =>
        ((Real.exp (-((θ - 1 / 2) * u / 2)) * (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) : ℝ) : ℂ) +
        (∑' q : XiZeroCopy, (if (xiZero q).re = θ then zeroBohrAmplitude q else 0) *
          Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) -
        (((if θ = 1 / 2 then 1 else 0 : ℝ)) : ℂ) * gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ))
      atTop (𝓝 0) := by
  have hθh := half_le_of_zero_bound hθ
  set A : ℂ := gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) with hA
  set L : ℝ := if θ = 1 / 2 then 1 else 0 with hL
  set w : ℝ → ℝ := fun u => Real.exp (-((θ - 1 / 2) * u / 2)) with hw
  set c : XiZeroCopy → ℂ := fun q => if (xiZero q).re = θ then zeroBohrAmplitude q else 0 with hc
  set S : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, c q *
    Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) with hSdef
  set G : ℝ → ℝ := fun u => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
    gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) with hGdef
  set f : ℝ → ℂ := fun u => ((w u * G u : ℝ) : ℂ) with hfdef
  set Rs : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, (criticalZeroGerm (Real.exp (-u)) q -
    zeroBohrAmplitude q * ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZero q - 1 / 2) / 2))) with hRs
  set D : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, (weightedZeroTerm θ u q -
    c q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) with hDdef
  have hcnorm : ∀ q, ‖c q‖ ≤ ‖zeroBohrAmplitude q‖ := fun q => by
    simp only [hc]; split_ifs <;> simp
  have hcsum : Summable fun q => ‖c q‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcnorm summable_norm_zeroBohrAmplitude
  have hcexp : ∀ u : ℝ, Summable fun q : XiZeroCopy =>
      c q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) := fun u =>
    Summable.of_norm (hcsum.congr fun q => by rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one])
  -- continuity
  have hScont : Continuous S := by
    refine continuous_tsum (fun q => by fun_prop) hcsum (fun q u => ?_)
    rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  have hGcont : Continuous G := by
    have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
    have heq : G = gaussianBudgetProfile (-1) (1 / 2) 0 0 := by
      funext u; simp [hGdef, gaussianBudgetProfile]
    rw [heq]; exact h
  have hfcont : Continuous f :=
    Complex.continuous_ofReal.comp ((by fun_prop : Continuous w).mul hGcont)
  -- the weight
  have hwL : Tendsto w atTop (𝓝 L) := by
    by_cases h12 : θ = 1 / 2
    · rw [hL, if_pos h12]
      refine tendsto_const_nhds.congr fun u => ?_
      simp [hw, h12]
    · rw [hL, if_neg h12]
      have hpos : 0 < (θ - 1 / 2) / 2 := by
        have : 1 / 2 < θ := lt_of_le_of_ne hθh (Ne.symm h12)
        linarith
      have h1 : Tendsto (fun u : ℝ => -((θ - 1 / 2) * u / 2)) atTop atBot := by
        have := (tendsto_id (α := ℝ)).const_mul_atTop hpos
        refine tendsto_neg_atTop_atBot.comp (this.congr fun u => ?_)
        simp only [id]; ring
      exact Real.tendsto_exp_atBot.comp h1
  have hwC : Tendsto (fun u => ((w u : ℝ) : ℂ)) atTop (𝓝 (L : ℂ)) :=
    (Complex.continuous_ofReal.tendsto L).comp hwL
  -- the expansion
  have hterm : ∀ u : ℝ, ∀ q : XiZeroCopy, ((w u : ℝ) : ℂ) *
      (zeroBohrAmplitude q * ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZero q - 1 / 2) / 2))) =
      weightedZeroTerm θ u q := by
    intro u q
    rw [exp_neg_cpow_eq_cexp_mul, weightedZeroTerm, hw]
    simp only
    rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hexpand : ∀ u : ℝ, f u = ((w u : ℝ) : ℂ) * gaussianArchimedeanMB (Real.exp (-u)) 2
      ((1 / 2 : ℝ) : ℂ) - (S u + D u) - ((w u : ℝ) : ℂ) * Rs u := by
    intro u
    have he := gaussianCentralGap_eq_archimedean_sub_zeroSeries (Real.exp_pos (-u))
    have hsum : ∑' q : XiZeroCopy, weightedZeroTerm θ u q = S u + D u := by
      rw [hSdef, hDdef, ← (hcexp u).tsum_add]
      · exact tsum_congr fun q => by ring
      · exact ((summable_weightedZeroTerm θ u).sub (hcexp u))
    have hmul : ((w u : ℝ) : ℂ) * ∑' q : XiZeroCopy, zeroBohrAmplitude q *
        ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZero q - 1 / 2) / 2)) =
        ∑' q : XiZeroCopy, weightedZeroTerm θ u q := by
      rw [← tsum_mul_left]
      exact tsum_congr fun q => hterm u q
    simp only [hfdef, hGdef]
    rw [Complex.ofReal_mul, he, ← hsum, ← hmul]
    ring
  -- the remainders vanish
  have hexp0 : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ Real.tendsto_exp_neg_atTop_nhds_zero
      (Eventually.of_forall fun u => Real.exp_pos _)
  have hMB : Tendsto (fun u : ℝ => gaussianArchimedeanMB (Real.exp (-u)) 2 ((1 / 2 : ℝ) : ℂ))
      atTop (𝓝 A) := by
    have h1 := (tendsto_gaussianArchimedeanCurrent_sub_MB two_pos
      (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num)).comp hexp0
    have h2 := (tendsto_const_nhds (x := A)).sub h1
    rw [sub_zero] at h2
    exact h2.congr fun u => by simp only [Function.comp, hA]; ring
  have hRs0 : Tendsto Rs atTop (𝓝 0) := by
    set K : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hK
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun u : ℝ => (2 * Real.exp (-u) + 2 * Real.exp (-u) ^ 2) * K) atTop
        (𝓝 0) := by
      have h0 := Real.tendsto_exp_neg_atTop_nhds_zero
      simpa using ((h0.const_mul 2).add ((h0.pow 2).const_mul 2)).mul_const K
    refine squeeze_zero (fun u => norm_nonneg _) (fun u => ?_) hlim
    have hy := Real.exp_pos (-u)
    have hsn : Summable fun q : XiZeroCopy => ‖criticalZeroGerm (Real.exp (-u)) q -
        zeroBohrAmplitude q * ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun q => norm_criticalZeroGerm_sub_zeroBohr_le hy q)
        (summable_norm_inv_xiZero_sub_half_sq.mul_left _)
    refine (norm_tsum_le_tsum_norm hsn).trans ?_
    rw [hK, ← tsum_mul_left]
    exact hsn.tsum_le_tsum (fun q => norm_criticalZeroGerm_sub_zeroBohr_le hy q)
      (summable_norm_inv_xiZero_sub_half_sq.mul_left _)
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have hlim : (0 : ℂ) = ∑' q : XiZeroCopy, (0 : ℂ) := tsum_zero.symm
    rw [hlim]
    refine tendsto_tsum_of_dominated_convergence
      (summable_norm_zeroBohrAmplitude.mul_left 2) (fun q => ?_) ?_
    · by_cases hq : (xiZero q).re = θ
      · refine tendsto_const_nhds.congr fun u => ?_
        rw [weightedZeroTerm_of_re_eq u hq]
        simp [hc, hq]
      · have hlt : (xiZero q).re < θ := lt_of_le_of_ne (hθ _ (xi_xiZero q)) hq
        have hc0 : c q = 0 := by simp [hc, hq]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hdecay : Tendsto (fun u : ℝ => ‖zeroBohrAmplitude q‖ *
            Real.exp (((xiZero q).re - θ) * u / 2)) atTop (𝓝 0) := by
          have hneg : ((xiZero q).re - θ) / 2 < 0 := by linarith
          have h1 : Tendsto (fun u : ℝ => ((xiZero q).re - θ) * u / 2) atTop atBot := by
            have := (tendsto_id (α := ℝ)).const_mul_atTop_of_neg hneg
            exact this.congr fun u => by simp only [id]; ring
          simpa using (Real.tendsto_exp_atBot.comp h1).const_mul ‖zeroBohrAmplitude q‖
        refine hdecay.congr fun u => ?_
        rw [hc0, zero_mul, sub_zero, norm_weightedZeroTerm]
    · filter_upwards [eventually_ge_atTop 0] with u hu q
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one, norm_weightedZeroTerm]
      have h1 : Real.exp (((xiZero q).re - θ) * u / 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := hθ _ (xi_xiZero q)
        nlinarith
      have h2 := hcnorm q
      have h3 := norm_nonneg (zeroBohrAmplitude q)
      nlinarith
  have h1 := ((hwC.mul hMB).sub hD0).sub (hwC.mul hRs0)
  rw [sub_zero, mul_zero, sub_zero] at h1
  have h2 := h1.sub (tendsto_const_nhds (x := (L : ℂ) * A))
  rw [sub_self] at h2
  refine h2.congr fun u => ?_
  have he := hexpand u
  simp only [hfdef] at he
  rw [he]
  ring

/-- **Weighted Bohr spectrum.**  If every zero has `Re ρ ≤ θ`, then for every real `τ`,
`T⁻¹ ∫₀^T e^{-(θ−½)u/2} G(e^{-u}) e^{-iτu} du → A(½)·[θ = ½ ∧ τ = 0] − Σ_{Re ρ = θ, Im ρ = 2τ} ½ Γ((ρ−½)/2)`.
-/
theorem tendsto_gaussianWindowAverage_weightedGap {θ : ℝ} (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ)
    (τ : ℝ) :
    Tendsto (gaussianWindowAverage fun u =>
        ((Real.exp (-((θ - 1 / 2) * u / 2)) * (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) : ℝ) : ℂ) *
          Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) atTop
      (𝓝 ((if θ = 1 / 2 ∧ τ = 0 then gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) else 0) -
        ∑' q : XiZeroCopy, if (xiZero q).re = θ ∧ xiZeroHalfOrdinate q = τ then
          zeroBohrAmplitude q else 0)) := by
  have hθh := half_le_of_zero_bound hθ
  set A : ℂ := gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) with hA
  set L : ℝ := if θ = 1 / 2 then 1 else 0 with hL
  set w : ℝ → ℝ := fun u => Real.exp (-((θ - 1 / 2) * u / 2)) with hw
  set c : XiZeroCopy → ℂ := fun q => if (xiZero q).re = θ then zeroBohrAmplitude q else 0 with hc
  set S : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, c q *
    Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) with hSdef
  set G : ℝ → ℝ := fun u => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
    gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) with hGdef
  set f : ℝ → ℂ := fun u => ((w u * G u : ℝ) : ℂ) with hfdef
  set E : ℝ → ℂ := fun u => Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ)) with hEdef
  set Rs : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, (criticalZeroGerm (Real.exp (-u)) q -
    zeroBohrAmplitude q * ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZero q - 1 / 2) / 2))) with hRs
  set D : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, (weightedZeroTerm θ u q -
    c q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) with hDdef
  have hcnorm : ∀ q, ‖c q‖ ≤ ‖zeroBohrAmplitude q‖ := fun q => by
    simp only [hc]; split_ifs <;> simp
  have hcsum : Summable fun q => ‖c q‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcnorm summable_norm_zeroBohrAmplitude
  have hcexp : ∀ u : ℝ, Summable fun q : XiZeroCopy =>
      c q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) := fun u =>
    Summable.of_norm (hcsum.congr fun q => by rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one])
  -- continuity
  have hScont : Continuous S := by
    refine continuous_tsum (fun q => by fun_prop) hcsum (fun q u => ?_)
    rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  have hGcont : Continuous G := by
    have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
    have heq : G = gaussianBudgetProfile (-1) (1 / 2) 0 0 := by
      funext u; simp [hGdef, gaussianBudgetProfile]
    rw [heq]; exact h
  have hfcont : Continuous f :=
    Complex.continuous_ofReal.comp ((by fun_prop : Continuous w).mul hGcont)
  have hEcont : Continuous E := by fun_prop
  -- the remainder after the archimedean constant and the extremal Bohr series
  set h : ℝ → ℂ := fun u => f u + S u - (L : ℂ) * A with hhdef
  have hhcont : Continuous h := (hfcont.add hScont).sub continuous_const
  have hh0 : Tendsto h atTop (𝓝 0) := tendsto_weightedGap_add_extremalSeries hθ
  have hhE0 : Tendsto (fun u => h u * E u) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_zero_iff_norm_tendsto_zero.1 hh0).congr fun u => ?_
    rw [norm_mul, hEdef]
    simp only
    rw [norm_cexp_ofReal_mul_I_mul, mul_one]
  -- split the window average
  have hsplit : ∀ T : ℝ, gaussianWindowAverage (fun u => f u * E u) T =
      gaussianWindowAverage (fun u => h u * E u) T + ((L : ℂ) * A) * gaussianWindowAverage E T -
        gaussianWindowAverage (fun u => S u * E u) T := by
    intro T
    have hpt : (fun u => f u * E u) = fun u => (h u * E u + ((L : ℂ) * A) * E u) - S u * E u := by
      funext u; simp only [hhdef]; ring
    have i1 : IntervalIntegrable (fun u => h u * E u + ((L : ℂ) * A) * E u) volume 0 T :=
      ((hhcont.mul hEcont).add (continuous_const.mul hEcont)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => S u * E u) volume 0 T :=
      (hScont.mul hEcont).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun u => h u * E u) volume 0 T :=
      (hhcont.mul hEcont).intervalIntegrable _ _
    have i4 : IntervalIntegrable (fun u => ((L : ℂ) * A) * E u) volume 0 T :=
      (continuous_const.mul hEcont).intervalIntegrable _ _
    rw [gaussianWindowAverage, hpt, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_add i3 i4, intervalIntegral.integral_const_mul]
    simp only [gaussianWindowAverage]
    ring
  have hfun : (gaussianWindowAverage fun u => f u * E u) = fun T =>
      gaussianWindowAverage (fun u => h u * E u) T + ((L : ℂ) * A) * gaussianWindowAverage E T -
        gaussianWindowAverage (fun u => S u * E u) T := funext hsplit
  have hlim1 : Tendsto (gaussianWindowAverage fun u => h u * E u) atTop (𝓝 0) :=
    tendsto_gaussianWindowAverage_of_tendsto_zero (hhcont.mul hEcont) hhE0
  have hlim2 := (tendsto_gaussianWindowAverage_cexp (-τ)).const_mul ((L : ℂ) * A)
  have hlim3 := tendsto_gaussianWindowAverage_tsum_cexp c hcsum xiZeroHalfOrdinate τ
  have htot := (hlim1.add hlim2).sub hlim3
  have hval : (if θ = 1 / 2 ∧ τ = 0 then A else 0) - ∑' q : XiZeroCopy,
      (if (xiZero q).re = θ ∧ xiZeroHalfOrdinate q = τ then zeroBohrAmplitude q else 0) =
      (0 + ((L : ℂ) * A) * (if -τ = 0 then 1 else 0)) - ∑' q : XiZeroCopy,
      (if xiZeroHalfOrdinate q = τ then c q else 0) := by
    congr 1
    · rw [hL]
      by_cases h12 : θ = 1 / 2
      · rw [if_pos h12]
        by_cases hτ : τ = 0
        · rw [if_pos ⟨h12, hτ⟩, if_pos (by rw [hτ, neg_zero])]; push_cast; ring
        · rw [if_neg (fun h => hτ h.2), if_neg (fun h => hτ (neg_eq_zero.1 h))]; ring
      · rw [if_neg h12, if_neg (fun h => h12 h.1)]; push_cast; ring
    · refine tsum_congr fun q => ?_
      simp only [hc]
      by_cases h1 : (xiZero q).re = θ <;> by_cases h2 : xiZeroHalfOrdinate q = τ <;> simp [h1, h2]
  rw [hfun, hval]
  exact htot

/-! ## The extremal line -/

/-- The zero part of the `θ`-weighted Bohr coefficient at frequency `τ`. -/
def weightedBohrCoefficient (θ τ : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, if (xiZero q).re = θ ∧ xiZeroHalfOrdinate q = τ then zeroBohrAmplitude q else 0

/-- **Extremal Bohr spectrum (unconditional).**  With `Θ = sup Re ρ`, for every real `τ` the window
averages of `e^{-(Θ−½)u/2} G(e^{-u}) e^{-iτu}` converge to
`A(½)·[Θ = ½ ∧ τ = 0] − Σ_{Re ρ = Θ, Im ρ = 2τ} ½ Γ((ρ−½)/2)`. -/
theorem tendsto_gaussianWindowAverage_extremalGap (τ : ℝ) :
    Tendsto (gaussianWindowAverage fun u =>
        ((Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
          (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
            gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) : ℝ) : ℂ) *
          Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) atTop
      (𝓝 ((if xiZeroAbscissa = 1 / 2 ∧ τ = 0 then gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)
        else 0) - weightedBohrCoefficient xiZeroAbscissa τ)) :=
  tendsto_gaussianWindowAverage_weightedGap (fun _ hρ => re_le_xiZeroAbscissa hρ) τ

theorem summable_indicator_xiZero_eq (ρ : ℂ) :
    Summable fun q : XiZeroCopy => if xiZero q = ρ then (1 : ℝ) else 0 := by
  refine Summable.of_nonneg_of_le (fun q => by split_ifs <;> norm_num) (fun q => ?_)
    (summable_norm_inv_xiZero_sub_half_sq.mul_left (‖ρ - 1 / 2‖ ^ 2))
  split_ifs with h
  · have h0 := xiZero_sub_half_ne_zero q
    rw [h] at h0
    rw [h, norm_inv, inv_pow, mul_inv_cancel₀ (by positivity [norm_pos_iff.2 h0])]
  · positivity

/-- **A zero on the line `Re ρ = θ` is visible**: its `θ`-weighted Bohr coefficient at
`τ = Im ρ / 2` is `½ Γ((ρ−½)/2)` times its multiplicity, hence nonzero. -/
theorem weightedBohrCoefficient_ne_zero_of_xi_eq_zero {θ : ℝ} {ρ : ℂ} (hρ : xi ρ = 0)
    (hre : ρ.re = θ) : weightedBohrCoefficient θ (ρ.im / 2) ≠ 0 := by
  set K : ℂ := (1 / 2 : ℂ) * Complex.Gamma ((ρ - 1 / 2) / 2) with hK
  have hcount := summable_indicator_xiZero_eq ρ
  have heq : weightedBohrCoefficient θ (ρ.im / 2) =
      K * ((∑' q : XiZeroCopy, if xiZero q = ρ then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    rw [weightedBohrCoefficient, Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    by_cases h : xiZero q = ρ
    · have h1 : (xiZero q).re = θ ∧ xiZeroHalfOrdinate q = ρ.im / 2 := by
        rw [xiZeroHalfOrdinate, h]; exact ⟨hre, rfl⟩
      rw [if_pos h1, if_pos h, zeroBohrAmplitude, h, hK]; push_cast; ring
    · have h1 : ¬ ((xiZero q).re = θ ∧ xiZeroHalfOrdinate q = ρ.im / 2) := by
        rintro ⟨h1, h2⟩
        apply h
        rw [xiZeroHalfOrdinate] at h2
        apply Complex.ext
        · rw [h1, hre]
        · linarith
      rw [if_neg h1, if_neg h]; simp
  rw [heq]
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_eq_of_xi_eq_zero hρ
  have hle : (1 : ℝ) ≤ ∑' q : XiZeroCopy, if xiZero q = ρ then (1 : ℝ) else 0 := by
    have := hcount.le_tsum q₀ (fun j _ => by split_ifs <;> norm_num)
    rwa [if_pos hq₀] at this
  have hΓ : Complex.Gamma ((ρ - 1 / 2) / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    have him := congrArg Complex.im hm
    simp at him
    have hz := hρ
    have hlow : |ρ.im| ≤ 1 := by rw [him, abs_zero]; norm_num
    exact xi_ne_zero_of_abs_im_le_one hlow hz
  refine mul_ne_zero (mul_ne_zero (by norm_num) hΓ) ?_
  exact_mod_cast (show (∑' q : XiZeroCopy, if xiZero q = ρ then (1 : ℝ) else 0) ≠ 0 by linarith)

/-- A nonzero `θ`-weighted Bohr coefficient at `τ` exhibits the zero `θ + 2iτ`. -/
theorem exists_xi_zero_of_weightedBohrCoefficient_ne_zero {θ τ : ℝ}
    (h : weightedBohrCoefficient θ τ ≠ 0) : xi ((θ : ℂ) + 2 * (τ : ℂ) * I) = 0 := by
  by_contra hz
  apply h
  rw [weightedBohrCoefficient]
  have hall : ∀ q : XiZeroCopy, ¬ ((xiZero q).re = θ ∧ xiZeroHalfOrdinate q = τ) := by
    rintro q ⟨h1, h2⟩
    apply hz
    have hq : xiZero q = (θ : ℂ) + 2 * (τ : ℂ) * I := by
      rw [xiZeroHalfOrdinate] at h2
      apply Complex.ext
      · simp [h1]
      · simp; linarith
    rw [← hq]
    exact xi_xiZero q
  simp [hall]

/-- **Visibility of the extremal line.**  Some `θ`-weighted Bohr coefficient is nonzero iff `ξ` has
a zero on the line `Re ρ = θ`; at `θ = Θ` these are exactly the frequencies of
`e^{-(Θ−½)u/2} G(e^{-u})` beyond the archimedean mean. -/
theorem exists_weightedBohrCoefficient_ne_zero_iff (θ : ℝ) :
    (∃ τ : ℝ, weightedBohrCoefficient θ τ ≠ 0) ↔ ∃ ρ : ℂ, xi ρ = 0 ∧ ρ.re = θ := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨_, exists_xi_zero_of_weightedBohrCoefficient_ne_zero hτ, by simp⟩
  · rintro ⟨ρ, hρ, hre⟩
    exact ⟨ρ.im / 2, weightedBohrCoefficient_ne_zero_of_xi_eq_zero hρ hre⟩

end

end RHTower
