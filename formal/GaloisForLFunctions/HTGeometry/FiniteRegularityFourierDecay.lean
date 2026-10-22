import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFourierDecay

/-!
# Weighted decay of a Fourier transform from finitely many derivatives

The admissible families of the clock construction ask for a density decaying like `⟨η⟩⁻ᴷ`. For a
Schwartz function that is supplied by the Schwartz axioms; but the decay is really a statement about
*finitely many* derivatives, and a compactly supported function of class `C^n` already has it.

The mechanism is the transform of an iterated derivative. Evaluating the multilinear map
`𝓕(D^n f)(w)` at `n` copies of the unit vector along `w` returns `(2π‖w‖)^n ‖𝓕f(w)‖`, so that
quantity is bounded by the operator norm of the transform, hence by the `L¹` norm of `D^n f`. With
`⟨w⟩^{2j} ≤ 2^j(1 + ‖w‖^{2j})` this gives

`⟨w⟩^{2j} ‖𝓕f(w)‖ ≤ 2^j (‖f‖₁ + (2π)^{-2j} ‖D^{2j}f‖₁)`,

an explicit functional of two finite-order norms — which is what a curve of potentials can be
required to bound uniformly in time.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped FourierTransform RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The `L¹` norms of the derivatives -/

/-- The `L¹` norm of the `n`-th iterated derivative. -/
noncomputable def derivL1 (n : ℕ) (f : E → ℂ) : ℝ := ∫ v : E, ‖iteratedFDeriv ℝ n f v‖

theorem derivL1_nonneg (n : ℕ) (f : E → ℂ) : 0 ≤ derivL1 n f :=
  integral_nonneg fun _ => norm_nonneg _

theorem derivL1_zero (f : E → ℂ) : derivL1 0 f = ∫ v : E, ‖f v‖ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show ‖iteratedFDeriv ℝ 0 f v‖ = ‖f v‖
  rw [norm_iteratedFDeriv_zero]

/-- Every derivative of a compactly supported `C^n` function is integrable. -/
theorem integrable_iteratedFDeriv_of_hasCompactSupport {n : ℕ} {f : E → ℂ}
    (hf : ContDiff ℝ n f) (hsupp : HasCompactSupport f) {i : ℕ} (hi : i ≤ n) :
    Integrable (iteratedFDeriv ℝ i f) (volume : Measure E) :=
  (hf.continuous_iteratedFDeriv (by exact_mod_cast hi)).integrable_of_hasCompactSupport
    (hsupp.iteratedFDeriv i)

/-! ## The transform is bounded by the `L¹` norm -/

theorem norm_fourier_le_integral_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {g : E → F} (hg : Integrable g (volume : Measure E)) (w : E) :
    ‖𝓕 g w‖ ≤ ∫ v : E, ‖g v‖ := by
  rw [Real.fourier_eq]
  refine norm_integral_le_of_norm_le hg.norm (Filter.Eventually.of_forall fun v => ?_)
  exact le_of_eq (Circle.norm_smul _ _)

/-! ## Decay from `n` derivatives -/

/-- **The transform of a compactly supported `C^n` function decays like `‖w‖⁻ⁿ`**, with the `L¹`
norm of the `n`-th derivative as the explicit constant. -/
theorem norm_pow_mul_norm_fourier_le {n : ℕ} {f : E → ℂ}
    (hf : ContDiff ℝ n f) (hsupp : HasCompactSupport f) (w : E) :
    (2 * Real.pi) ^ n * ‖w‖ ^ n * ‖𝓕 f w‖ ≤ derivL1 n f := by
  have hint : ∀ i : ℕ, (i : ℕ∞) ≤ (n : ℕ∞) → Integrable (iteratedFDeriv ℝ i f) (volume : Measure E) :=
    fun i hi => integrable_iteratedFDeriv_of_hasCompactSupport hf hsupp (by exact_mod_cast hi)
  have hbase : ‖𝓕 (iteratedFDeriv ℝ n f) w‖ ≤ derivL1 n f :=
    norm_fourier_le_integral_norm (hint n le_rfl) w
  have hfint : Integrable f (volume : Measure E) :=
    hf.continuous.integrable_of_hasCompactSupport hsupp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ‖𝓕 f w‖ ≤ derivL1 0 f := by
      rw [derivL1_zero]
      exact norm_fourier_le_integral_norm hfint w
    simpa using h0
  rcases eq_or_ne w 0 with rfl | hw
  · have : (0 : ℝ) ^ n = 0 := zero_pow hn.ne'
    simp only [norm_zero, this, mul_zero, zero_mul]
    exact derivL1_nonneg n f
  -- the transform of the `n`-th derivative, evaluated at `n` copies of the unit vector along `w`
  have hkey : 𝓕 (iteratedFDeriv ℝ n f)
      = fun v : E => VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 f) v n :=
    Real.fourier_iteratedFDeriv (N := (n : ℕ∞)) (by exact_mod_cast hf) hint le_rfl
  set u : E := ‖w‖⁻¹ • w with hu
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt hwpos)
  have hinner : ((-innerSL ℝ) w) u = -‖w‖ := by
    show -(innerSL ℝ w u) = -‖w‖
    rw [innerSL_apply_apply, hu, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hprod : (∏ _i : Fin n, ((-innerSL ℝ) w) u) = (-‖w‖) ^ n := by
    rw [Finset.prod_const, hinner]
    simp
  have hval : VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n (fun _ : Fin n => u)
      = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ n • ((-‖w‖) ^ n • 𝓕 f w) := by
    rw [VectorFourier.fourierPowSMulRight_apply, hprod]
  have hnormval : ‖VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n (fun _ : Fin n => u)‖
      = (2 * Real.pi) ^ n * ‖w‖ ^ n * ‖𝓕 f w‖ := by
    rw [hval, norm_smul, norm_smul, norm_pow, norm_pow, norm_neg, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg w)]
    have hc : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg, mul_one]
    rw [hc, mul_assoc]
  have hop := (VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n).le_opNorm
    (fun _ : Fin n => u)
  rw [hnormval] at hop
  have hprod1 : (∏ _i : Fin n, ‖u‖) = 1 := by
    rw [Finset.prod_const, hunorm, one_pow]
  rw [hprod1, mul_one] at hop
  have hnormeq : ‖VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n‖
      = ‖𝓕 (iteratedFDeriv ℝ n f) w‖ := by
    rw [hkey]
  rw [hnormeq] at hop
  exact hop.trans hbase

/-! ## The weight -/

theorem one_add_pow_le_two_pow_mul {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    (1 + a) ^ j ≤ 2 ^ j * (1 + a ^ j) := by
  rcases le_total a 1 with h | h
  · have h1 : (1 + a) ^ j ≤ 2 ^ j := by
      refine pow_le_pow_left₀ (by linarith) (by linarith) j
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ j * (1 + a ^ j) := by
      have hone : (1 : ℝ) ≤ 1 + a ^ j := by nlinarith [pow_nonneg ha j]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) j]
    exact h1.trans h2
  · have h1 : (1 + a) ^ j ≤ (2 * a) ^ j := by
      refine pow_le_pow_left₀ (by linarith) (by linarith) j
    have h2 : (2 * a) ^ j = 2 ^ j * a ^ j := by rw [mul_pow]
    have h3 : (2 : ℝ) ^ j * a ^ j ≤ 2 ^ j * (1 + a ^ j) := by
      have hpj : (0 : ℝ) ≤ 2 ^ j := by positivity
      have : a ^ j ≤ 1 + a ^ j := by nlinarith [pow_nonneg ha j]
      exact mul_le_mul_of_nonneg_left this hpj
    rw [h2] at h1
    exact h1.trans h3

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgFreq_pow_two_mul (w : E) (j : ℕ) : kgFreq w ^ (2 * j) = (1 + ‖w‖ ^ (2 : ℕ)) ^ j := by
  have hsq : kgFreq w ^ (2 : ℕ) = 1 + ‖w‖ ^ (2 : ℕ) := by
    rw [kgFreq, Real.sq_sqrt]
    positivity
  rw [pow_mul, hsq]

/-- The explicit decay functional of a compactly supported `C^{2j}` function. -/
noncomputable def contDiffDecay (j : ℕ) (f : E → ℂ) : ℝ :=
  2 ^ j * (derivL1 0 f + ((2 * Real.pi) ^ (2 * j))⁻¹ * derivL1 (2 * j) f)

theorem contDiffDecay_nonneg (j : ℕ) (f : E → ℂ) : 0 ≤ contDiffDecay j f := by
  refine mul_nonneg (by positivity) (add_nonneg (derivL1_nonneg 0 f) ?_)
  exact mul_nonneg (by positivity) (derivL1_nonneg (2 * j) f)

/-- **The weighted bound the admissible families ask for, from `2j` derivatives.** -/
theorem kgFreq_pow_mul_norm_fourier_le {j : ℕ} {f : E → ℂ}
    (hf : ContDiff ℝ ((2 * j : ℕ) : WithTop ℕ∞) f) (hsupp : HasCompactSupport f) (w : E) :
    kgFreq w ^ (2 * j) * ‖𝓕 f w‖ ≤ contDiffDecay j f := by
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (2 * j) := by positivity
  have h0 : ‖𝓕 f w‖ ≤ derivL1 0 f := by
    rw [derivL1_zero]
    exact norm_fourier_le_integral_norm
      (hf.continuous.integrable_of_hasCompactSupport hsupp) w
  have hn : (2 * Real.pi) ^ (2 * j) * ‖w‖ ^ (2 * j) * ‖𝓕 f w‖ ≤ derivL1 (2 * j) f :=
    norm_pow_mul_norm_fourier_le hf hsupp w
  have hn' : ‖w‖ ^ (2 * j) * ‖𝓕 f w‖ ≤ ((2 * Real.pi) ^ (2 * j))⁻¹ * derivL1 (2 * j) f := by
    have hid : ((2 * Real.pi) ^ (2 * j))⁻¹ *
        ((2 * Real.pi) ^ (2 * j) * ‖w‖ ^ (2 * j) * ‖𝓕 f w‖)
        = ‖w‖ ^ (2 * j) * ‖𝓕 f w‖ := by
      field_simp
    calc ‖w‖ ^ (2 * j) * ‖𝓕 f w‖
        = ((2 * Real.pi) ^ (2 * j))⁻¹ *
            ((2 * Real.pi) ^ (2 * j) * ‖w‖ ^ (2 * j) * ‖𝓕 f w‖) := hid.symm
      _ ≤ ((2 * Real.pi) ^ (2 * j))⁻¹ * derivL1 (2 * j) f :=
          mul_le_mul_of_nonneg_left hn (le_of_lt (inv_pos.mpr hpi))
  have hweight : kgFreq w ^ (2 * j) ≤ 2 ^ j * (1 + (‖w‖ ^ (2 : ℕ)) ^ j) := by
    rw [kgFreq_pow_two_mul]
    exact one_add_pow_le_two_pow_mul (by positivity) j
  have hpow : (‖w‖ ^ (2 : ℕ)) ^ j = ‖w‖ ^ (2 * j) := by rw [← pow_mul]
  have hfour : (0 : ℝ) ≤ ‖𝓕 f w‖ := norm_nonneg _
  calc kgFreq w ^ (2 * j) * ‖𝓕 f w‖
      ≤ (2 ^ j * (1 + ‖w‖ ^ (2 * j))) * ‖𝓕 f w‖ := by
        rw [← hpow]
        exact mul_le_mul_of_nonneg_right hweight hfour
    _ = 2 ^ j * (‖𝓕 f w‖ + ‖w‖ ^ (2 * j) * ‖𝓕 f w‖) := by ring
    _ ≤ 2 ^ j * (derivL1 0 f + ((2 * Real.pi) ^ (2 * j))⁻¹ * derivL1 (2 * j) f) := by
        refine mul_le_mul_of_nonneg_left (add_le_add h0 hn') (by positivity)
    _ = contDiffDecay j f := rfl

end GaloisForLFunctions.HTGeometry
