import GaloisForLFunctions.RHTower.EvenLandauSharpOffLineExclusion
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowThresholdLaw
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity

/-!
# A heat Hankel window certifies the critical line up to the Nyquist height

**Theorem** (`heatWindow_forces_critical_line_below_landau`). Suppose the heat Hankel form is
eventually nonnegative on the pole hyperplane in the window `aN ≤ K`. Then even Weil positivity
holds at every level `a < 2√K`. Consequently every separated zero of bounded multiplicity with
ordinate in `[8, (1 - η) 2πe^{2a}]` lies on the critical line, for all large `a`, under the depth
condition of `evenHodgeIndex_forces_critical_line_below_landau`.

The window `K` is worth the height `2πe^{4√K}`. This is the height where the β=2 log-gas of the heat
determinants saturates the zero sites.

Proof.
* The sharp witness (`evenPoleWeilNonneg_of_heatWindowNonneg`) gives positivity on smooth even
  real pole-free sources of half-width `< 2√K`.
* A smooth even complex test splits into real and imaginary parts, whose Weil energies add.
* A `C²` test is the limit of its mollifications by even bumps. They stay pole-free, because
  `(f ⋆ φ)^ = f̂ φ̂`, and their Weil energies converge by dominated convergence with
  `|f̂(z)| ≤ 4(N₀ + N₂)/(1 + |Re z|)²` on the strip.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## Decay of the transform of a `C²` test -/

/-- On the strip, `|f̂(z)| ≤ 4(N₀ + N₂)/(1 + |Re z|)²`. -/
theorem norm_paperFT_le_of_strip {f f' f'' : ℝ → ℂ} (hf : Continuous f)
    (hf' : Continuous f') (hf'' : Continuous f'') (hd : ∀ x, HasDerivAt f (f' x) x)
    (hd' : ∀ x, HasDerivAt f' (f'' x) x)
    (hint : Integrable (fun x => ‖f x‖ * Real.exp (|x| / 2)))
    (hint' : Integrable (fun x => ‖f' x‖ * Real.exp (|x| / 2)))
    (hint'' : Integrable (fun x => ‖f'' x‖ * Real.exp (|x| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT f z‖ ≤ 4 * ((∫ x, ‖f x‖ * Real.exp (|x| / 2)) +
      ∫ x, ‖f'' x‖ * Real.exp (|x| / 2)) / (1 + |z.re|) ^ 2 := by
  set N₀ := ∫ x, ‖f x‖ * Real.exp (|x| / 2) with hN₀
  set N₂ := ∫ x, ‖f'' x‖ * Real.exp (|x| / 2) with hN₂
  have hN₀0 : 0 ≤ N₀ := integral_nonneg fun _ => by positivity
  have hN₂0 : 0 ≤ N₂ := integral_nonneg fun _ => by positivity
  have h0 : ‖paperFT f z‖ ≤ N₀ := norm_heatStripTransform_le hint hz
  have h2 : ‖z‖ ^ 2 * ‖paperFT f z‖ ≤ N₂ :=
    sq_norm_mul_norm_heatStripTransform_le hf hf' hf'' hd hd' hint hint' hint'' hz
  have hD : 0 < (1 + |z.re|) ^ 2 := by positivity
  rw [le_div_iff₀ hD]
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  rcases le_total ‖z‖ 1 with hz1 | hz1
  · have : (1 + |z.re|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg z.re]
    have hF0 := norm_nonneg (paperFT f z)
    nlinarith
  · have hzz : (1 + |z.re|) ^ 2 ≤ 4 * ‖z‖ ^ 2 := by nlinarith [abs_nonneg z.re]
    have hF0 := norm_nonneg (paperFT f z)
    have : ‖paperFT f z‖ * (1 + |z.re|) ^ 2 ≤ ‖paperFT f z‖ * (4 * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hzz hF0
    nlinarith

theorem integrable_norm_mul_exp_of_compact {g : ℝ → ℂ} (hg : Continuous g)
    (hcpt : HasCompactSupport g) : Integrable (fun x => ‖g x‖ * Real.exp (|x| / 2)) :=
  (hg.norm.mul (Real.continuous_exp.comp (continuous_abs.div_const 2))).integrable_of_hasCompactSupport
    hcpt.norm.mul_right

/-- A `C²` compactly supported test has `|f̂(z)| ≤ C/(1 + |Re z|)²` on the strip. -/
theorem exists_norm_paperFT_le_of_contDiff_two {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hcpt : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT f z‖ ≤ C / (1 + |z.re|) ^ 2 := by
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)
  have h2 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv f) from h1.2.2)
  have hdf : Differentiable ℝ f := h1.1
  have hddf : Differentiable ℝ (deriv f) := h2.1
  have hc2 : Continuous (deriv (deriv f)) := h2.2.2.continuous
  have hcpt1 : HasCompactSupport (deriv f) := hcpt.deriv
  have hcpt2 : HasCompactSupport (deriv (deriv f)) := hcpt1.deriv
  refine ⟨4 * ((∫ x, ‖f x‖ * Real.exp (|x| / 2)) + ∫ x, ‖deriv (deriv f) x‖ * Real.exp (|x| / 2)),
    by positivity, fun z hz => ?_⟩
  exact norm_paperFT_le_of_strip hf.continuous hddf.continuous hc2
    (fun x => (hdf x).hasDerivAt) (fun x => (hddf x).hasDerivAt)
    (integrable_norm_mul_exp_of_compact hf.continuous hcpt)
    (integrable_norm_mul_exp_of_compact hddf.continuous hcpt1)
    (integrable_norm_mul_exp_of_compact hc2 hcpt2) hz

theorem strip_gammaOf {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    |(gammaOf ρ).im| ≤ 1 / 2 ∧ |((starRingEnd ℂ) (gammaOf ρ)).im| ≤ 1 / 2 ∧
      |(gammaOf ρ).re| = |ρ.im| ∧ |((starRingEnd ℂ) (gammaOf ρ)).re| = |ρ.im| := by
  have h : IsNontrivialZero ρ := hρ
  have hIm := (WeilEF.abs_gammaOf_im_lt ⟨h.2.1, h.2.2⟩).le
  exact ⟨hIm, by rw [Complex.conj_im, abs_neg]; exact hIm, by rw [WeilEF.gammaOf_re],
    by rw [Complex.conj_re, WeilEF.gammaOf_re]⟩

/-- The Weil summands of `C²` compactly supported tests are dominated by `C m_ρ/(1+|γ_ρ|)³`. -/
theorem exists_norm_Wsummand_le_of_contDiff_two {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand f g ρ‖ ≤
      C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3) := by
  obtain ⟨Cf, hCf0, hCf⟩ := exists_norm_paperFT_le_of_contDiff_two hf hfc
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_paperFT_le_of_contDiff_two hg hgc
  refine ⟨Cf * Cg, mul_nonneg hCf0 hCg0, fun ρ => ?_⟩
  obtain ⟨hi1, hi2, hr1, hr2⟩ := strip_gammaOf ρ.2
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have b1 := hCf _ hi1
  have b2 := hCg _ hi2
  rw [hr1] at b1; rw [hr2] at b2
  have hD : 1 ≤ 1 + |(ρ : ℂ).im| := by linarith [abs_nonneg (ρ : ℂ).im]
  simp only [ZeroConfig.Wsummand, norm_mul, Complex.norm_natCast, RCLike.norm_conj, sub_zero]
  calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ *
        ‖paperFT g ((starRingEnd ℂ) (gammaOf ρ))‖
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (Cf / (1 + |(ρ : ℂ).im|) ^ 2) *
          (Cg / (1 + |(ρ : ℂ).im|) ^ 2) := by
        gcongr
    _ ≤ Cf * Cg * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im|) ^ 3) := by
        rw [show (zetaZeroConfig.mult ρ : ℝ) * (Cf / (1 + |(ρ : ℂ).im|) ^ 2) *
            (Cg / (1 + |(ρ : ℂ).im|) ^ 2) = Cf * Cg * ((zetaZeroConfig.mult ρ : ℝ) /
              (1 + |(ρ : ℂ).im|) ^ 4) by field_simp]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_left hm (by positivity)
        exact pow_le_pow_right₀ hD (by norm_num)

/-- **Absolute convergence of the Weil series of `C²` compactly supported tests.** -/
theorem summable_Wsummand_of_contDiff_two {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f g ρ) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨hs, -⟩ := window_tsum_le zetaZeroConfig hA₀ hloc 0
  obtain ⟨Cf, hCf0, hCf⟩ := exists_norm_paperFT_le_of_contDiff_two hf hfc
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_paperFT_le_of_contDiff_two hg hgc
  refine Summable.of_norm_bounded (hs.mul_left (Cf * Cg)) fun ρ => ?_
  obtain ⟨hi1, hi2, hr1, hr2⟩ := strip_gammaOf ρ.2
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have b1 := hCf _ hi1
  have b2 := hCg _ hi2
  rw [hr1] at b1; rw [hr2] at b2
  have hD : 1 ≤ 1 + |(ρ : ℂ).im| := by linarith [abs_nonneg (ρ : ℂ).im]
  simp only [ZeroConfig.Wsummand, norm_mul, Complex.norm_natCast, RCLike.norm_conj, sub_zero]
  calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ *
        ‖paperFT g ((starRingEnd ℂ) (gammaOf ρ))‖
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (Cf / (1 + |(ρ : ℂ).im|) ^ 2) *
          (Cg / (1 + |(ρ : ℂ).im|) ^ 2) := by
        gcongr
    _ ≤ Cf * Cg * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im|) ^ 3) := by
        rw [show (zetaZeroConfig.mult ρ : ℝ) * (Cf / (1 + |(ρ : ℂ).im|) ^ 2) *
            (Cg / (1 + |(ρ : ℂ).im|) ^ 2) = Cf * Cg * ((zetaZeroConfig.mult ρ : ℝ) /
              (1 + |(ρ : ℂ).im|) ^ 4) by field_simp]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_left hm (by positivity)
        exact pow_le_pow_right₀ hD (by norm_num)

/-! ## Real and imaginary parts of an even test -/

theorem conj_paperFT_ofReal (u : ℝ → ℝ) (z : ℂ) :
    conj (paperFT (fun x => (u x : ℂ)) z) = paperFT (fun x => (u x : ℂ)) (-conj z) := by
  unfold paperFT
  rw [← integral_conj]
  congr 1
  funext x
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem paperFT_ofReal_neg_of_even {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) (z : ℂ) :
    paperFT (fun x => (u x : ℂ)) (-z) = paperFT (fun x => (u x : ℂ)) z := by
  rw [← paperFT_comp_neg]
  simp only [heven]

theorem conj_paperFT_ofReal_conj_of_even {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) (z : ℂ) :
    conj (paperFT (fun x => (u x : ℂ)) (conj z)) = paperFT (fun x => (u x : ℂ)) z := by
  rw [conj_paperFT_ofReal, Complex.conj_conj, paperFT_ofReal_neg_of_even heven]

theorem paperFT_eq_re_add_im {f : ℝ → ℂ} (hf : Continuous f) (hcpt : HasCompactSupport f)
    (z : ℂ) : paperFT f z = paperFT (fun x => ((f x).re : ℂ)) z +
      I * paperFT (fun x => ((f x).im : ℂ)) z := by
  have hre : Continuous (fun x => ((f x).re : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp hf)
  have him : Continuous (fun x => ((f x).im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp hf)
  have hrec : HasCompactSupport (fun x => ((f x).re : ℂ)) :=
    hcpt.comp_left (g := fun w : ℂ => ((w.re : ℝ) : ℂ)) (by simp)
  have himc : HasCompactSupport (fun x => ((f x).im : ℂ)) :=
    hcpt.comp_left (g := fun w : ℂ => ((w.im : ℝ) : ℂ)) (by simp)
  unfold paperFT
  rw [← integral_const_mul, ← integral_add (integrable_mul_cexp_of_continuous_compact hre hrec z)
    ((integrable_mul_cexp_of_continuous_compact him himc z).const_mul I)]
  congr 1
  funext x
  conv_lhs => rw [← Complex.re_add_im (f x)]
  ring

theorem Wsummand_eq_re_add_im {f : ℝ → ℂ} (hf : Continuous f) (hcpt : HasCompactSupport f)
    (heven : ∀ x, f (-x) = f x) (ρ : ℂ) :
    zetaZeroConfig.Wsummand f f ρ =
      zetaZeroConfig.Wsummand (fun x => ((f x).re : ℂ)) (fun x => ((f x).re : ℂ)) ρ +
        zetaZeroConfig.Wsummand (fun x => ((f x).im : ℂ)) (fun x => ((f x).im : ℂ)) ρ := by
  have e1 : conj (paperFT (fun x => ((f x).re : ℂ)) (conj (gammaOf ρ))) =
      paperFT (fun x => ((f x).re : ℂ)) (gammaOf ρ) :=
    conj_paperFT_ofReal_conj_of_even (u := fun x => (f x).re) (fun x => by simp only [heven]) _
  have e2 : conj (paperFT (fun x => ((f x).im : ℂ)) (conj (gammaOf ρ))) =
      paperFT (fun x => ((f x).im : ℂ)) (gammaOf ρ) :=
    conj_paperFT_ofReal_conj_of_even (u := fun x => (f x).im) (fun x => by simp only [heven]) _
  simp only [ZeroConfig.Wsummand, paperFT_eq_re_add_im hf hcpt, map_add, map_mul, Complex.conj_I,
    e1, e2]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem contDiff_ofReal_re {n : ℕ∞} {f : ℝ → ℂ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => ((f x).re : ℂ)) :=
  (Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hf))

theorem contDiff_ofReal_im {n : ℕ∞} {f : ℝ → ℂ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => ((f x).im : ℂ)) :=
  (Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hf))

/-- **The Weil energy of an even test is the sum of those of its real and imaginary parts.** -/
theorem W_eq_re_add_im {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hcpt : HasCompactSupport f)
    (heven : ∀ x, f (-x) = f x) :
    zetaZeroConfig.W f f =
      zetaZeroConfig.W (fun x => ((f x).re : ℂ)) (fun x => ((f x).re : ℂ)) +
        zetaZeroConfig.W (fun x => ((f x).im : ℂ)) (fun x => ((f x).im : ℂ)) := by
  have hrec : HasCompactSupport (fun x => ((f x).re : ℂ)) :=
    hcpt.comp_left (g := fun w : ℂ => ((w.re : ℝ) : ℂ)) (by simp)
  have himc : HasCompactSupport (fun x => ((f x).im : ℂ)) :=
    hcpt.comp_left (g := fun w : ℂ => ((w.im : ℝ) : ℂ)) (by simp)
  have h1 := summable_Wsummand_of_contDiff_two (contDiff_ofReal_re hf) hrec
    (contDiff_ofReal_re hf) hrec
  have h2 := summable_Wsummand_of_contDiff_two (contDiff_ofReal_im hf) himc
    (contDiff_ofReal_im hf) himc
  unfold ZeroConfig.W
  simp_rw [Wsummand_eq_re_add_im hf.continuous hcpt heven]
  exact h1.tsum_add h2

/-! ## Smooth even tests from the window -/

/-- For a smooth even real source supported in `(-A, A)`, the zeta Weil energy is the zero-side sum
of squares. -/
theorem re_W_ofReal_eq_tsum_sq {u : ℝ → ℝ} (hsmooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) {A : ℝ} (hA : 0 < A)
    (hsupp : tsupport u ⊆ Ioo (-A) A) :
    (zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ))).re =
      (∑' q : XiZeroCopy, heatStripTransform (fun x => (u x : ℂ)) (xiSpectralPoint q) ^ 2).re := by
  have h1 := ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil
    (realEvenSource ⟨A, hA⟩ u hsmooth hcpt hsupp)
  have h2 := ccmRestrictedWeilSourceQuadratic_realEven (A := ⟨A, hA⟩) (u := u)
    (hsmooth := hsmooth) (hcpt := hcpt) (hsupp := hsupp) heven
  rw [h1] at h2
  exact h2

theorem paperFT_ofReal_I_half_eq_integral (u : ℝ → ℝ) :
    paperFT (fun x => (u x : ℂ)) (I / 2) = ((∫ x, u x * Real.exp (-(x / 2)) : ℝ) : ℂ) := by
  unfold paperFT
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  push_cast
  congr 1
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integral_mul_exp_half_of_even {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) :
    ∫ x, u x * Real.exp (x / 2) = ∫ x, u x * Real.exp (-(x / 2)) := by
  rw [← integral_neg_eq_self]
  congr 1
  funext x
  rw [heven]
  ring_nf

/-- **Smooth even tests are Weil-positive below the window aperture.** -/
theorem re_W_nonneg_of_evenPoleWeilNonneg {A : ℝ} (hW : EvenPoleWeilNonneg A) {a : ℝ}
    (ha : a ≤ A) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (heven : ∀ x, f (-x) = f x)
    (hsupp : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0) :
    0 ≤ (zetaZeroConfig.W f f).re := by
  have hcpt : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.2 le_top)
  rw [W_eq_re_add_im hf2 hcpt heven, Complex.add_re]
  have hsplit := paperFT_eq_re_add_im hf.continuous hcpt (I / 2)
  rw [hp, paperFT_ofReal_I_half_eq_integral (fun x => (f x).re),
    paperFT_ofReal_I_half_eq_integral (fun x => (f x).im)] at hsplit
  have hre0 : (∫ x, (f x).re * Real.exp (-(x / 2))) = 0 := by
    have := congrArg Complex.re hsplit
    simpa using this.symm
  have him0 : (∫ x, (f x).im * Real.exp (-(x / 2))) = 0 := by
    have := congrArg Complex.im hsplit
    simpa using this.symm
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → (∀ x, g (-x) = g x) →
      (∀ x, f x = 0 → g x = 0) → ∫ x, g x * Real.exp (-(x / 2)) = 0 →
      0 ≤ (zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ))).re := by
    intro g hg hge hgz hgp
    have hgs : Function.support g ⊆ Function.support f := fun x hx hfx => hx (hgz x hfx)
    have hgts : tsupport g ⊆ Icc (-a) a :=
      (closure_mono hgs).trans hsupp
    have hgc : HasCompactSupport g :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hgts
    have hgs' : ∀ t : ℝ, A < |t| → g t = 0 := fun t ht => by
      by_contra hne
      have := hgts (subset_tsupport g hne)
      have : |t| ≤ a := abs_le.2 ⟨this.1, this.2⟩
      linarith
    have hgpole : ∫ x, g x * Real.exp (x / 2) = 0 := by
      rw [integral_mul_exp_half_of_even hge]; exact hgp
    have hpos := hW g hg hgc hgs' hge hgpole
    have hgI : tsupport g ⊆ Ioo (-(|a| + 1)) (|a| + 1) := fun x hx => by
      have := hgts hx
      exact ⟨by linarith [this.1, le_abs_self a], by linarith [this.2, le_abs_self a]⟩
    rw [re_W_ofReal_eq_tsum_sq hg hgc hge (by positivity) hgI]
    exact hpos
  have hre := key (fun x => (f x).re) (Complex.reCLM.contDiff.comp hf)
    (fun x => by simp only [heven]) (fun x hx => by simp [hx]) hre0
  have him := key (fun x => (f x).im) (Complex.imCLM.contDiff.comp hf)
    (fun x => by simp only [heven]) (fun x hx => by simp [hx]) him0
  exact add_nonneg hre him

/-! ## Mollification -/

/-- The even bump of radius `r`. -/
def evenBump {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r / 2, r, by positivity, by linarith⟩

/-- The normalized bump of radius `r`, as a complex function. -/
def bumpC {r : ℝ} (hr : 0 < r) (t : ℝ) : ℂ := ((evenBump hr).normed volume t : ℂ)

/-- The mollification of `f` at radius `r`. -/
def mollify {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) : ℝ → ℂ :=
  MeasureTheory.convolution (bumpC hr) f (ContinuousLinearMap.mul ℝ ℂ) volume

theorem bumpC_eq_zero {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : r ≤ |t|) : bumpC hr t = 0 := by
  have h : t ∉ Function.support ((evenBump hr).normed volume) := by
    rw [(evenBump hr).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact not_lt.2 ht
  simp only [bumpC, Function.notMem_support.1 h, Complex.ofReal_zero]

theorem contDiff_bumpC {r : ℝ} (hr : 0 < r) : ContDiff ℝ (⊤ : ℕ∞) (bumpC hr) :=
  Complex.ofRealCLM.contDiff.comp (evenBump hr).contDiff_normed

theorem hasCompactSupport_bumpC {r : ℝ} (hr : 0 < r) : HasCompactSupport (bumpC hr) :=
  (evenBump hr).hasCompactSupport_normed.comp_left Complex.ofReal_zero

theorem bumpC_neg {r : ℝ} (hr : 0 < r) (t : ℝ) : bumpC hr (-t) = bumpC hr t := by
  simp only [bumpC, (evenBump hr).normed_neg]

theorem integral_bumpC {r : ℝ} (hr : 0 < r) : ∫ t, bumpC hr t = 1 := by
  simp only [bumpC]
  rw [integral_complex_ofReal, (evenBump hr).integral_normed, Complex.ofReal_one]

theorem mollify_apply {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) (x : ℝ) :
    mollify hr f x = ∫ t, bumpC hr t * f (x - t) := by
  rw [mollify, convolution_def]
  rfl

theorem contDiff_mollify {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ} (hf : Continuous f) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify hr f) :=
  (hasCompactSupport_bumpC hr).contDiff_convolution_left _ (contDiff_bumpC hr)
    hf.locallyIntegrable

theorem mollify_neg {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ} (heven : ∀ x, f (-x) = f x) (x : ℝ) :
    mollify hr f (-x) = mollify hr f x := by
  rw [mollify_apply, mollify_apply, ← integral_neg_eq_self]
  congr 1
  funext t
  rw [bumpC_neg, show -x - -t = -(x - t) by ring, heven]

theorem mollify_eq_zero {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ} {a : ℝ}
    (hsupp : tsupport f ⊆ Icc (-a) a) {x : ℝ} (hx : a + r < |x|) : mollify hr f x = 0 := by
  rw [mollify_apply]
  have : ∀ t, bumpC hr t * f (x - t) = 0 := by
    intro t
    by_cases ht : r ≤ |t|
    · rw [bumpC_eq_zero hr ht, zero_mul]
    · push Not at ht
      have hxt : a < |x - t| := by
        have := abs_sub_abs_le_abs_sub x t
        linarith
      have hnot : x - t ∉ tsupport f := fun h => by
        have := hsupp h
        have : |x - t| ≤ a := abs_le.2 ⟨this.1, this.2⟩
        linarith
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  simp only [this, integral_zero]

theorem tsupport_mollify_subset {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ} {a : ℝ}
    (hsupp : tsupport f ⊆ Icc (-a) a) : tsupport (mollify hr f) ⊆ Icc (-(a + r)) (a + r) := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc
  have h : a + r < |x| := by
    rw [Set.mem_Icc, not_and_or] at hc
    rcases hc with h | h
    · push Not at h; exact lt_abs.2 (Or.inr (by linarith))
    · push Not at h; exact lt_abs.2 (Or.inl h)
  exact hx (mollify_eq_zero hr hsupp h)

/-- `(f ⋆ φ)^ = φ̂ f̂`. -/
theorem paperFT_mollify {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ} (hf : Continuous f)
    (hcpt : HasCompactSupport f) (z : ℂ) :
    paperFT (mollify hr f) z = paperFT (bumpC hr) z * paperFT f z := by
  set φz : ℝ → ℂ := fun t => bumpC hr t * Complex.exp (I * z * t) with hφz
  set fz : ℝ → ℂ := fun y => f y * Complex.exp (I * z * y) with hfz
  have hφi : Integrable φz := integrable_mul_cexp_of_continuous_compact
    (contDiff_bumpC hr).continuous (hasCompactSupport_bumpC hr) z
  have hfi : Integrable fz := integrable_mul_cexp_of_continuous_compact hf hcpt z
  have hconv : ∀ x : ℝ, mollify hr f x * Complex.exp (I * z * x) =
      MeasureTheory.convolution φz fz (ContinuousLinearMap.mul ℂ ℂ) volume x := by
    intro x
    rw [convolution_def, mollify_apply, ← integral_mul_const]
    congr 1
    funext t
    simp only [hφz, hfz, ContinuousLinearMap.mul_apply']
    have e : Complex.exp (I * z * t) * Complex.exp (I * z * ((x - t : ℝ) : ℂ)) =
        Complex.exp (I * z * x) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← e]
    ring
  unfold paperFT
  simp_rw [hconv]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hφi hfi, ContinuousLinearMap.mul_apply']

theorem norm_paperFT_bumpC_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (bumpC hr) z‖ ≤ Real.exp (r / 2) := by
  unfold paperFT
  calc ‖∫ t, bumpC hr t * Complex.exp (I * z * t)‖
      ≤ ∫ t, ‖bumpC hr t * Complex.exp (I * z * t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, (evenBump hr).normed volume t * Real.exp (r / 2) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        · exact ((evenBump hr).integrable_normed).mul_const _
        · refine Filter.Eventually.of_forall fun t => ?_
          by_cases ht : r ≤ |t|
          · simp only [bumpC_eq_zero hr ht, zero_mul, norm_zero]
            exact mul_nonneg ((evenBump hr).nonneg_normed t) (Real.exp_pos _).le
          · push Not at ht
            dsimp only
            rw [norm_mul, bumpC, Complex.norm_real, Real.norm_of_nonneg
              ((evenBump hr).nonneg_normed t)]
            apply mul_le_mul_of_nonneg_left _ ((evenBump hr).nonneg_normed t)
            rw [Complex.norm_exp]
            apply Real.exp_le_exp.2
            have : (I * z * (t : ℂ)).re = -(z.im * t) := by simp [Complex.mul_re]
            rw [this]
            have h1 : |z.im * t| ≤ 1 / 2 * r := by
              rw [abs_mul]; exact mul_le_mul hz ht.le (abs_nonneg _) (by norm_num)
            linarith [neg_abs_le (z.im * t), abs_nonneg (z.im * t)]
    _ = Real.exp (r / 2) := by
        rw [integral_mul_const, (evenBump hr).integral_normed, one_mul]

theorem norm_paperFT_bumpC_sub_one_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hzr : ‖z‖ * r ≤ 1) :
    ‖paperFT (bumpC hr) z - 1‖ ≤ 2 * ‖z‖ * r := by
  have hint : Integrable (fun t => bumpC hr t * Complex.exp (I * z * t)) :=
    integrable_mul_cexp_of_continuous_compact (contDiff_bumpC hr).continuous
      (hasCompactSupport_bumpC hr) z
  have hint1 : Integrable (bumpC hr) :=
    (contDiff_bumpC hr).continuous.integrable_of_hasCompactSupport (hasCompactSupport_bumpC hr)
  have e : paperFT (bumpC hr) z - 1 =
      ∫ t, bumpC hr t * (Complex.exp (I * z * t) - 1) := by
    unfold paperFT
    conv_lhs => rw [← integral_bumpC hr, ← integral_sub hint hint1]
    congr 1; funext t; ring
  rw [e]
  calc ‖∫ t, bumpC hr t * (Complex.exp (I * z * t) - 1)‖
      ≤ ∫ t, ‖bumpC hr t * (Complex.exp (I * z * t) - 1)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, (evenBump hr).normed volume t * (2 * ‖z‖ * r) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        · exact ((evenBump hr).integrable_normed).mul_const _
        · refine Filter.Eventually.of_forall fun t => ?_
          by_cases ht : r ≤ |t|
          · simp only [bumpC_eq_zero hr ht, zero_mul, norm_zero]
            exact mul_nonneg ((evenBump hr).nonneg_normed t) (by positivity)
          · push Not at ht
            dsimp only
            rw [norm_mul, bumpC, Complex.norm_real, Real.norm_of_nonneg
              ((evenBump hr).nonneg_normed t)]
            apply mul_le_mul_of_nonneg_left _ ((evenBump hr).nonneg_normed t)
            have hn : ‖I * z * (t : ℂ)‖ = ‖z‖ * |t| := by
              rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
            have h1 : ‖z‖ * |t| ≤ ‖z‖ * r := mul_le_mul_of_nonneg_left ht.le (norm_nonneg _)
            have hb := Complex.norm_exp_sub_one_le (x := I * z * t) (by rw [hn]; linarith)
            rw [hn] at hb
            linarith
    _ = 2 * ‖z‖ * r := by
        rw [integral_mul_const, (evenBump hr).integral_normed, one_mul]

theorem invSucc_pos (k : ℕ) : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity

theorem Wsummand_mollify {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ} (hf : Continuous f)
    (hcpt : HasCompactSupport f) (ρ : ℂ) :
    zetaZeroConfig.Wsummand (mollify hr f) (mollify hr f) ρ =
      paperFT (bumpC hr) (gammaOf ρ) * conj (paperFT (bumpC hr) (conj (gammaOf ρ))) *
        zetaZeroConfig.Wsummand f f ρ := by
  simp only [ZeroConfig.Wsummand, paperFT_mollify hr hf hcpt, map_mul]
  ring

theorem tendsto_paperFT_bumpC (z : ℂ) :
    Tendsto (fun k : ℕ => paperFT (bumpC (invSucc_pos k)) z) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun k : ℕ => 2 * ‖z‖ * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 * ‖z‖)
    simpa using this
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  have hev : ∀ᶠ k : ℕ in atTop, ‖z‖ * (1 / ((k : ℝ) + 1)) ≤ 1 := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ‖z‖).eventually
      (ge_mem_nhds (show ‖z‖ * 0 < 1 by simp))
    exact this
  filter_upwards [hev] with k hk
  exact norm_paperFT_bumpC_sub_one_le (invSucc_pos k) hk

/-- **The Weil energies of the mollifications converge.** -/
theorem tendsto_W_mollify {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hcpt : HasCompactSupport f) :
    Tendsto (fun k : ℕ => zetaZeroConfig.W (mollify (invSucc_pos k) f)
      (mollify (invSucc_pos k) f)) atTop (𝓝 (zetaZeroConfig.W f f)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨hs, -⟩ := window_tsum_le zetaZeroConfig hA₀ hloc 0
  obtain ⟨C, hC0, hC⟩ := exists_norm_Wsummand_le_of_contDiff_two hf hcpt hf hcpt
  unfold ZeroConfig.W
  refine tendsto_tsum_of_dominated_convergence (hs.mul_left (Real.exp 1 * C)) (fun ρ => ?_)
    (Filter.Eventually.of_forall fun k ρ => ?_)
  · simp only [Wsummand_mollify _ hf.continuous hcpt]
    have h1 := tendsto_paperFT_bumpC (gammaOf ρ)
    have h2 := (Complex.continuous_conj.tendsto _).comp
      (tendsto_paperFT_bumpC (conj (gammaOf (ρ : ℂ))))
    have h := (h1.mul h2).mul_const (zetaZeroConfig.Wsummand f f ρ)
    simpa only [map_one, one_mul, Function.comp_def] using h
  · rw [Wsummand_mollify _ hf.continuous hcpt, norm_mul, norm_mul, RCLike.norm_conj]
    obtain ⟨hi1, hi2, -, -⟩ := strip_gammaOf ρ.2
    have hr1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have b1 := norm_paperFT_bumpC_le (invSucc_pos k) hi1
    have b2 := norm_paperFT_bumpC_le (invSucc_pos k) hi2
    have he : Real.exp (1 / ((k : ℝ) + 1) / 2) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.2 (by linarith)
    have hprod : ‖paperFT (bumpC (invSucc_pos k)) (gammaOf ρ)‖ *
        ‖paperFT (bumpC (invSucc_pos k)) (conj (gammaOf (ρ : ℂ)))‖ ≤ Real.exp 1 := by
      have : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
        rw [← Real.exp_add]; norm_num
      rw [this]
      exact mul_le_mul (b1.trans he) (b2.trans he) (norm_nonneg _) (Real.exp_pos _).le
    calc ‖paperFT (bumpC (invSucc_pos k)) (gammaOf ρ)‖ *
          ‖paperFT (bumpC (invSucc_pos k)) (conj (gammaOf (ρ : ℂ)))‖ *
          ‖zetaZeroConfig.Wsummand f f ρ‖
        ≤ Real.exp 1 * (C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3)) :=
          mul_le_mul hprod (hC ρ) (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp 1 * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3) := by ring

/-- **Even Weil positivity at level `a` from smooth sources at a larger half-width.** -/
theorem evenHodgeIndexAtLevel_of_evenPoleWeilNonneg {A a : ℝ} (ha : a < A)
    (hW : EvenPoleWeilNonneg A) : EvenHodgeIndexAtLevel zetaZeroConfig a := by
  intro f hf2 heven hsupp hp1 _
  have hcpt : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
  have hev : ∀ᶠ k : ℕ in atTop, 0 ≤ (zetaZeroConfig.W (mollify (invSucc_pos k) f)
      (mollify (invSucc_pos k) f)).re := by
    have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim.eventually (ge_mem_nhds (show (0 : ℝ) < A - a by linarith))] with k hk
    refine re_W_nonneg_of_evenPoleWeilNonneg hW (a := a + 1 / ((k : ℝ) + 1)) (by linarith)
      (contDiff_mollify _ hf2.continuous) (mollify_neg _ heven)
      (tsupport_mollify_subset _ hsupp) ?_
    rw [paperFT_mollify _ hf2.continuous hcpt, hp1, mul_zero]
  have hlim := (Complex.continuous_re.tendsto _).comp (tendsto_W_mollify hf2 hcpt)
  exact ge_of_tendsto hlim hev

/-! ## The window certifies the critical line -/

/-- **A nonnegative window `K` gives even Weil positivity at every level `a < 2√K`.** -/
theorem evenHodgeIndexAtLevel_of_heatWindowNonneg {K : ℝ} (hK0 : 0 < K)
    (hW : HeatWindowNonneg K) {a : ℝ} (ha : a < 2 * Real.sqrt K) :
    EvenHodgeIndexAtLevel zetaZeroConfig a := by
  have hs := Real.sqrt_pos.2 hK0
  have hs2 := Real.sq_sqrt hK0.le
  set A := max 0 ((a + 2 * Real.sqrt K) / 2) with hA
  have hA0 : 0 ≤ A := le_max_left _ _
  have haA : a < A := by
    rcases lt_or_ge a 0 with h | h
    · exact h.trans_le hA0
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hA2 : A < 2 * Real.sqrt K := max_lt (by linarith) (by linarith)
  have hAK : A ^ 2 < 4 * K := by
    have := pow_lt_pow_left₀ hA2 hA0 two_ne_zero
    rw [mul_pow, hs2] at this
    linarith
  exact evenHodgeIndexAtLevel_of_evenPoleWeilNonneg haA
    (evenPoleWeilNonneg_of_heatWindowNonneg hK0 hW hAK)

/-- **A heat Hankel window certifies the critical line up to the Nyquist height.** For
`0 < η ≤ 1/2` and every multiplicity bound `M` there is `a₀` such that, whenever `a₀ ≤ a < 2√K` and
the heat Hankel form is eventually nonnegative on the pole hyperplane in the window `aN ≤ K`, every
zero `ρ₀` with `mult ρ₀ ≤ M`, `8 ≤ t₀ ≤ (1 - η)·2πe^{2a}`, ordinate separation `δ ≤ 1/2` from every
zero other than `ρ₀` and `1 - ρ̄₀`, `|β₀ - 1/2| ≤ δ/2`, and
`12C log(t₀+1)/δ + 6 log(1/|β₀ - 1/2|) ≤ (π/2)η^{3/2}e^{2a}` lies on the critical line. -/
theorem heatWindow_forces_critical_line_below_landau :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ M : ℕ, ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a → ∀ K : ℝ, 0 < K →
      a < 2 * Real.sqrt K → HeatWindowNonneg K →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, zetaZeroConfig.mult ρ₀ ≤ M →
      8 ≤ ρ₀.im → ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * a)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → |ρ₀.re - 1 / 2| ≤ δ / 2 →
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ → δ ≤ |ρ.im - ρ₀.im|) →
      12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ +
        6 * Real.log (1 / |ρ₀.re - 1 / 2|) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) →
      ρ₀.re = 1 / 2 := by
  intro η hη0 hη2 M
  obtain ⟨a₀, ha₀⟩ := evenHodgeIndex_forces_critical_line_below_landau η hη0 hη2 M
  exact ⟨a₀, fun a ha K hK haK hW => ha₀ a ha (evenHodgeIndexAtLevel_of_heatWindowNonneg hK hW haK)⟩

end

end RHTower
