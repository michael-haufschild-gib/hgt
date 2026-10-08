import GaloisForLFunctions.RHTower.WeilWorkExposingRayPacketCoercivity
import GaloisForLFunctions.RHTower.WeilWorkExposingRayMassMargin

/-!
# The retained quarter and the exact primitive-surrogate boundary

The archimedean primitive estimate has a uniform quarter of Fourier mass
available beyond its former statement. Retaining it gives an optimized
logarithmic mass-ratio bound for every compact complex C² source. The former
surrogate fails at the exact exposing threshold on actual matched families,
for every choice of a separate tuning parameter for each row.

This excludes the former estimate, not the sharpened estimate or WP02.
Paper proof: docs/reports/weil-work/results/02-exposing-ray/PRIMITIVE-SHARPNESS-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real Zeta23
noncomputable section
namespace RHTower.ExposingRayPrimitive

/-- Fourier mass with this corpus's unnormalized transform. -/
def fourierMass (f : ℝ → ℂ) : ℝ := ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2

/-- Spectral mass of the inverse of `D²-1/4`. -/
def primitiveMass (f : ℝ → ℂ) : ℝ :=
  ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 / (τ ^ 2 + 1 / 4) ^ 2

/-- The explicit constant in the proved digamma lower estimate. -/
def coercivityConst : ℝ :=
  digammaVerticalCoercivityConst (1 / 4) + log 2 + log π

/-- The former primitive estimate, before restoring its quarter of mass. -/
def surrogate (b : ℝ) (f : ℝ → ℂ) : ℝ :=
  (b-coercivityConst)*fourierMass f-exp b^4/4*primitiveMass f

private theorem primitive_density_le {z : ℝ} (hz : 0 ≤ z) (τ : ℝ) :
    z/(τ^2+(1:ℝ)/4)^2 ≤ 16*z := by
  have hd : 0 < (τ^2+(1:ℝ)/4)^2 := by positivity
  have hb : (1:ℝ)/16 ≤ (τ^2+1/4)^2 := by nlinarith [sq_nonneg τ]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hb hz]

private theorem integrable_primitive {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 / (τ ^ 2 + 1 / 4) ^ 2) := by
  have hi := integrable_normSq_paperFT hf hs
  have hc : Continuous (fun τ : ℝ => ((τ ^ 2 + 1 / 4) ^ 2)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro τ
    positivity
  simp_rw [div_eq_mul_inv]
  apply (hi.const_mul 16).mono' (hi.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  filter_upwards [] with τ
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv]
  exact primitive_density_le (sq_nonneg _) τ

/-- The inverse polar multiplier is bounded on the full Fourier mass space. -/
theorem primitiveMass_le {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) :
    primitiveMass f ≤ 16*fourierMass f := by
  have h := integral_mono (integrable_primitive hf hs)
    ((integrable_normSq_paperFT hf hs).const_mul 16)
    (fun τ => primitive_density_le (sq_nonneg _) τ)
  rw [integral_const_mul] at h
  exact h

/-- On the existing compact polar-multiplier interface this is exactly the
original primitive's Fourier mass, not a replacement penalty. -/
theorem primitiveMass_polarMultiplier (a : SuzukiPositiveAperture)
    (g : CCMComplexSmoothInteriorSource a) :
    primitiveMass (g.polarMultiplier : ℝ → ℂ)=fourierMass (g : ℝ → ℂ) := by
  unfold primitiveMass fourierMass
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [exposingCompact_fourier_multiplier, norm_mul, norm_neg]
  have he : ((τ : ℂ)^2+1/4)=((τ^2+1/4 : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hd : (τ^2+(1:ℝ)/4)^2 ≠ 0 := by positivity
  field_simp

/-- Every compact complex C² source retains the quarter, without a polar premise. -/
theorem quarter_bound {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) (b : ℝ) :
    surrogate b f + fourierMass f/4 ≤ archEnergy f := by
  have hiM := integrable_normSq_paperFT hf hs
  have hiP := integrable_primitive hf hs
  have hiE := integrable_normSq_paperFT_mul_arch hf hs
  have hp : ∀ τ : ℝ, (b-coercivityConst+1/4)*‖paperFT f τ‖^2 ≤
      ‖paperFT f τ‖^2*archimedeanWeilSymbol (τ/(2*π)) +
        exp b^4/4*(‖paperFT f τ‖^2/(τ^2+1/4)^2) := by
    intro τ
    have hd : (τ^2+(1:ℝ)/4)^2 ≠ 0 := by positivity
    have h := mul_le_mul_of_nonneg_right
      (exposing_archimedean_scalar_quarter (exp_pos b) τ)
      (div_nonneg (sq_nonneg ‖paperFT f τ‖) (sq_nonneg (τ^2+1/4)))
    rw [log_exp] at h
    dsimp [coercivityConst]
    convert h using 1 <;> first | rfl | field_simp [hd]
  have h := integral_mono (hiM.const_mul _) (hiE.add (hiP.const_mul _)) hp
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hiE (hiP.const_mul _), integral_const_mul] at h
  change (b-coercivityConst+1/4)*fourierMass f ≤
    archEnergy f+exp b^4/4*primitiveMass f at h
  dsimp [surrogate]
  linarith

/-- A nonzero Fourier mass has strictly positive primitive mass. -/
theorem primitiveMass_pos {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a)
    (hm : 0 < fourierMass f) : 0 < primitiveMass f := by
  have hp : 0 ≤ primitiveMass f := integral_nonneg fun τ => by positivity
  by_contra hn
  have hz : primitiveMass f = 0 := by linarith
  have h := quarter_bound hf hs (coercivityConst+archEnergy f/fourierMass f+1)
  dsimp [surrogate] at h
  rw [hz, mul_zero, sub_zero] at h
  have he : archEnergy f/fourierMass f*fourierMass f=archEnergy f :=
    div_mul_cancel₀ _ hm.ne'
  nlinarith

/-- Optimizing the restored estimate cancels the entire primitive penalty. -/
private theorem logarithmic_mass_ratio_bound_of_pos {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a)
    (hm : 0 < fourierMass f) :
    (log (fourierMass f/primitiveMass f)/4-coercivityConst)*fourierMass f ≤
      archEnergy f := by
  have hp := primitiveMass_pos hf hs hm
  have hx : exp (log (fourierMass f/primitiveMass f)/4)^4 =
      fourierMass f/primitiveMass f := by
    rw [← exp_nat_mul]
    norm_num
    rw [show 4*(log (fourierMass f/primitiveMass f)/4)=
      log (fourierMass f/primitiveMass f) by ring, exp_log (div_pos hm hp)]
  have h := quarter_bound hf hs (log (fourierMass f/primitiveMass f)/4)
  dsimp [surrogate] at h
  rw [hx] at h
  have he : (fourierMass f/primitiveMass f)/4*primitiveMass f=fourierMass f/4 := by
    field_simp [hp.ne']
  linarith

/-- The optimized bound also includes zero sources; no nonzero-mass premise remains. -/
theorem logarithmic_mass_ratio_bound {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) :
    (log (fourierMass f/primitiveMass f)/4-coercivityConst)*fourierMass f ≤
      archEnergy f := by
  have hm : 0 ≤ fourierMass f := integral_nonneg fun τ => sq_nonneg _
  rcases lt_or_eq_of_le hm with hm | hm
  · exact logarithmic_mass_ratio_bound_of_pos hf hs hm
  · have hz : fourierMass f=0 := hm.symm
    have hp : primitiveMass f=0 := by
      have hlo : 0 ≤ primitiveMass f := integral_nonneg fun τ => by positivity
      have hhi := primitiveMass_le hf hs
      rw [hz, mul_zero] at hhi
      exact le_antisymm hhi hlo
    have h := quarter_bound hf hs 0
    simpa [surrogate, hz, hp] using h

/-- The physical/Fourier mass conversion keeps the literal factor `2*pi`. -/
theorem fourierMass_eq {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) :
    fourierMass f=2*π*ExposingRayMass.mass f := by
  have h := integral_normSq_paperFT_mul_cos_eq hf hs 0
  simp only [mul_zero, cos_zero, mul_one, neg_zero, weilTest_self_zero,
    Complex.add_re, Complex.ofReal_re] at h
  dsimp [fourierMass, ExposingRayMass.mass]
  rw [h]
  ring

/-- One exact matched family defeats all row-dependent choices of the former
primitive parameter, with any fixed box-tail slack. No energy-positivity premise. -/
theorem adaptive_surrogate_counterexample :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, ∀ᶠ N : ℕ in atTop,
      N ≤ ⌊exp (2*(log N/2+C))⌋₊ ∧
      ∃ (m : ℕ) (a : Fin m → ℝ) (f : Fin m → ℝ → ℂ) (α : Fin m → ℝ),
        (∀ i, a i ≤ log N/2+C) ∧ (∀ i, IsPolarTest (a i) (f i)) ∧
        (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=exposingWeightTrunc N n) ∧
        ∀ b : Fin m → ℝ, (∑ i, α i*surrogate (b i) (f i)) <
          archimedeanExposingThreshold-c*exposingTail N := by
  obtain ⟨C,hC,hfam⟩ := ExposingRayMass.mass_margin_counterexample
  refine ⟨C,hC,fun c => ?_⟩
  filter_upwards [hfam (π/2) (by positivity) c] with N hN
  obtain ⟨hfloor,m,a,f,α,ha,hf,hα,hm,hE⟩ := hN
  refine ⟨hfloor,m,a,f,α,ha,hf,hα,hm,fun b => ?_⟩
  have hb : ∀ i, α i*surrogate (b i) (f i) ≤
      α i*archEnergy (f i)-(π/2)*(α i*ExposingRayMass.mass (f i)) := by
    intro i
    have h := quarter_bound (hf i).2.1 (hf i).2.2.1 (b i)
    rw [fourierMass_eq (hf i).2.1 (hf i).2.2.1] at h
    have hh := mul_le_mul_of_nonneg_left h (hα i)
    nlinarith only [hh]
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ => hb i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  exact h.trans_lt hE

end RHTower.ExposingRayPrimitive
