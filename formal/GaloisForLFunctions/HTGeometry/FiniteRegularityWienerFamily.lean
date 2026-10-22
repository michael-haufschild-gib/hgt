import GaloisForLFunctions.HTGeometry.FiniteRegularityFourierDecay
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonRealProbe

/-!
# Admissible families from curves of finitely differentiable potentials

The weighted decay of the previous file is exactly the hypothesis of the corpus's
`WienerFamily.ofWeightedBounds`. So a curve of compactly supported `C^{2j}` functions whose decay
functional is bounded uniformly in time and Lipschitz in time is an admissible family — the Schwartz
hypothesis of the earlier construction was never needed.

Fourier inversion identifies the potential of the resulting family with the curve itself, and a real
curve gives a real family.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped FourierTransform RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Elementary properties of the transform of an integrable function -/

theorem continuous_fourier_of_integrable {f : E → ℂ} (hf : Integrable f (volume : Measure E)) :
    Continuous (𝓕 f) := by
  refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_ hf
  exact continuous_inner

theorem fourier_sub_apply {f g : E → ℂ} (hf : Integrable f (volume : Measure E))
    (hg : Integrable g (volume : Measure E)) (w : E) :
    𝓕 (f - g) w = 𝓕 f w - 𝓕 g w := by
  have hfw := (Real.fourierIntegral_convergent_iff (f := f) w).2 hf
  have hgw := (Real.fourierIntegral_convergent_iff (f := g) w).2 hg
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_sub hfw hgw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Pi.sub_apply, smul_sub]

/-- **The transform of a real function satisfies the reality condition.** -/
theorem fourier_neg_eq_conj {f : E → ℂ}
    (hreal : ∀ x : E, (starRingEnd ℂ) (f x) = f x) (η : E) :
    𝓕 f (-η) = (starRingEnd ℂ) (𝓕 f η) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show (Real.fourierChar (-⟪v, -η⟫) : ℂ) • f v
    = (starRingEnd ℂ) ((Real.fourierChar (-⟪v, η⟫) : ℂ) • f v)
  rw [smul_eq_mul, smul_eq_mul, map_mul, hreal v, inner_neg_right, neg_neg]
  congr 1
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

/-! ## The family -/

section Curve

variable {N : ℕ}

/-- The density of a compactly supported finitely differentiable function decays at the rate the
admissible families ask for. -/
theorem norm_fourier_le_weight_of_contDiff {j m : ℕ} {M : ℝ} (hj : N + m ≤ 2 * j) {f : E → ℂ}
    (hf : ContDiff ℝ ((2 * j : ℕ) : WithTop ℕ∞) f) (hsupp : HasCompactSupport f)
    (hM : contDiffDecay j f ≤ M) (η : E) :
    ‖𝓕 f η‖ ≤ (kgFreq η ^ (N + m))⁻¹ * M := by
  have hpos : (0 : ℝ) < kgFreq η ^ (2 * j) := pow_pos (kgFreq_pos η) (2 * j)
  have hbound : kgFreq η ^ (2 * j) * ‖𝓕 f η‖ ≤ M :=
    (kgFreq_pow_mul_norm_fourier_le hf hsupp η).trans hM
  have hstep : ‖𝓕 f η‖ ≤ (kgFreq η ^ (2 * j))⁻¹ * M := by
    rw [← le_div_iff₀' hpos, div_eq_inv_mul] at hbound
    exact hbound
  have hmono : (kgFreq η ^ (2 * j))⁻¹ ≤ (kgFreq η ^ (N + m))⁻¹ :=
    inv_pow_le_inv_pow_of_le hj η
  have hM0 : 0 ≤ M := le_trans (contDiffDecay_nonneg j f) hM
  exact hstep.trans (mul_le_mul_of_nonneg_right hmono hM0)

/-- **A curve of compactly supported finitely differentiable potentials is an admissible family.** -/
noncomputable def WienerFamily.ofContDiffCurve {Φ : ℝ → E → ℂ} {j m : ℕ} {M L : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hj : N + m ≤ 2 * j)
    (hcd : ∀ t : ℝ, ContDiff ℝ ((2 * j : ℕ) : WithTop ℕ∞) (Φ t))
    (hsupp : ∀ t : ℝ, HasCompactSupport (Φ t))
    (hM : ∀ t : ℝ, contDiffDecay j (Φ t) ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, contDiffDecay j (Φ t - Φ t') ≤ L * |t - t'|) :
    WienerFamily E N := by
  have hint : ∀ t : ℝ, Integrable (Φ t) (volume : Measure E) :=
    fun t => (hcd t).continuous.integrable_of_hasCompactSupport (hsupp t)
  refine WienerFamily.ofWeightedBounds (N := N) (m := m) (M := M) (L := L)
    (a := fun t => 𝓕 (Φ t)) hdim
    (fun t => (continuous_fourier_of_integrable (hint t)).aestronglyMeasurable)
    (fun t η => norm_fourier_le_weight_of_contDiff hj (hcd t) (hsupp t) (hM t) η) hL0
    (fun t t' η => ?_)
  have hsub : 𝓕 (Φ t) η - 𝓕 (Φ t') η = 𝓕 (Φ t - Φ t') η :=
    (fourier_sub_apply (hint t) (hint t') η).symm
  rw [hsub]
  exact norm_fourier_le_weight_of_contDiff hj ((hcd t).sub (hcd t')) ((hsupp t).sub (hsupp t'))
    (hL t t') η

theorem WienerFamily.ofContDiffCurve_density {Φ : ℝ → E → ℂ} {j m : ℕ} {M L : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hj : N + m ≤ 2 * j)
    (hcd : ∀ t : ℝ, ContDiff ℝ ((2 * j : ℕ) : WithTop ℕ∞) (Φ t))
    (hsupp : ∀ t : ℝ, HasCompactSupport (Φ t))
    (hM : ∀ t : ℝ, contDiffDecay j (Φ t) ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, contDiffDecay j (Φ t - Φ t') ≤ L * |t - t'|) (t : ℝ) (η : E) :
    (WienerFamily.ofContDiffCurve (N := N) hdim hj hcd hsupp hM hL0 hL).density t η
      = 𝓕 (Φ t) η := rfl

/-- The transform of a member of such a curve is integrable, so Fourier inversion applies. -/
theorem integrable_fourier_of_contDiff {j m : ℕ} {M : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hj : m ≤ 2 * j) {f : E → ℂ}
    (hf : ContDiff ℝ ((2 * j : ℕ) : WithTop ℕ∞) f) (hsupp : HasCompactSupport f)
    (hM : contDiffDecay j f ≤ M) :
    Integrable (𝓕 f) (volume : Measure E) := by
  have hint : Integrable f (volume : Measure E) :=
    hf.continuous.integrable_of_hasCompactSupport hsupp
  refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := E) hdim).const_mul M)
    (continuous_fourier_of_integrable hint).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  have hb := norm_fourier_le_weight_of_contDiff (N := 0) (m := m) (by simpa using hj) hf hsupp hM η
  rw [mul_comm]
  simpa using hb

/-- **Fourier inversion: the potential of the family is the curve itself.** -/
theorem kgPotential_fourier_of_contDiff {j m : ℕ} {M : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hj : m ≤ 2 * j) {f : E → ℂ}
    (hf : ContDiff ℝ ((2 * j : ℕ) : WithTop ℕ∞) f) (hsupp : HasCompactSupport f)
    (hM : contDiffDecay j f ≤ M) {a : WienerDensity E N} (ha : ∀ η : E, a η = 𝓕 f η) (x : E) :
    kgPotential a x = f x := by
  have hint : Integrable f (volume : Measure E) :=
    hf.continuous.integrable_of_hasCompactSupport hsupp
  have hfour : Integrable (𝓕 f) (volume : Measure E) :=
    integrable_fourier_of_contDiff hdim hj hf hsupp hM
  have hinv := hf.continuous.fourierInv_fourier_eq hint hfour
  have hval : kgPotential a x = 𝓕⁻ (𝓕 f) x := by
    rw [kgPotential, Real.fourierInv_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show kgChar x η * a η = (Real.fourierChar ⟪η, x⟫ : ℂ) • 𝓕 f η
    rw [ha η, smul_eq_mul, kgChar]
  rw [hval, hinv]

end Curve

end GaloisForLFunctions.HTGeometry
