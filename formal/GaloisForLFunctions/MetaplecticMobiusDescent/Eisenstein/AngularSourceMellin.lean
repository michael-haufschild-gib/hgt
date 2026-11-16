import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.HigherSourceFourier
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CuspReflectionOfTheSource
import GaloisForLFunctions.FamilyContinuationTheory.AngularMellinTransform

/-!
# Mellin factors of angular cubic source jets

The radial norm power introduced by a `6k+1` jet cancels its height Mellin shift.
The Dirichlet exponent remains `1/2-s`; only the two Gamma arguments shift by `3k`.
The reflected Gamma ratio has polynomial vertical growth of degree independent of `k`.
-/

open Complex MeasureTheory Set
open scoped ContDiff ComplexConjugate Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open GaloisForLFunctions.FamilyContinuationTheory
noncomputable section

private lemma radial_jet_norm_cancel (r : ℝ) (hr : 0 < r) (a s : ℂ) (m : ℕ) :
    ‖(r : ℂ) ^ m * a‖ * r ^ (1 / 2 - (s + m).re) =
      ‖a‖ * r ^ (1 / 2 - s.re) := by
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg hr.le]
  simp only [Complex.add_re, Complex.natCast_re]
  rw [← Real.rpow_natCast]
  calc
    _ = ‖a‖ * (r ^ (m : ℝ) * r ^ (1 / 2 - (s.re + m))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hr]
      congr 2
      ring

private lemma radial_jet_cpow_cancel (r : ℝ) (hr : 0 < r) (a s : ℂ) (m : ℕ) :
    ((r : ℂ) ^ m * a) * (r : ℂ) ^ (1 / 2 - (s + m)) =
      a * (r : ℂ) ^ (1 / 2 - s) := by
  rw [← Complex.cpow_natCast]
  calc
    _ = a * ((r : ℂ) ^ (m : ℂ) * (r : ℂ) ^ (1 / 2 - (s + m))) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
      congr 2
      ring

/-- The height and frequency powers cancel in the Dirichlet exponent of the Mellin transform. -/
theorem angularRadialBesselProfile_mellin {ι : Type*} [Countable ι]
    (k : ℕ) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (a : ι → ℂ) (q : ℝ) (hq : 0 < q)
    (s : ℂ) (hs : -(1 / 3) < (s + (3 * k : ℕ)).re)
    (ha : Summable (fun i => ‖a i‖ * (r i) ^ (1 / 2 - s.re))) :
    mellin (angularRadialBesselProfile k r a q) (2 * s) =
      besselMellinFactor q (s + (3 * k : ℕ)) *
        (∑' i, a i * (r i : ℂ) ^ (1 / 2 - s)) := by
  have has : Summable (fun i => ‖(r i : ℂ) ^ (3 * k) * a i‖ *
      (r i) ^ (1 / 2 - (s + (3 * k : ℕ)).re)) := by
    apply ha.congr
    intro i
    exact (radial_jet_norm_cancel (r i) (hr i) (a i) s (3 * k)).symm
  change mellin (angularPowerProfile (6 * k)
    (radialBesselProfile r (fun i => (r i : ℂ) ^ (3 * k) * a i) q)) (2 * s) = _
  rw [mellin_angularPowerProfile]
  have he : 2 * s + (6 * k : ℕ) = 2 * (s + (3 * k : ℕ)) := by push_cast; ring
  rw [he, radialBesselProfile_mellin r hr _ q hq _ hs has]
  congr 1
  apply tsum_congr
  intro i
  exact radial_jet_cpow_cancel (r i) (hr i) (a i) s (3 * k)

/-- The exact reflected Gamma ratio for the normalized `6k+1` source jets. -/
def angularCubicReflectionGamma (k : ℕ) (w : ℂ) : ℂ :=
  (Complex.Gamma (7 / 6 + (3 * k : ℕ) + w) *
    Complex.Gamma (5 / 6 + (3 * k : ℕ) + w)) /
  (Complex.Gamma (7 / 6 + (3 * k : ℕ) - w) *
    Complex.Gamma (5 / 6 + (3 * k : ℕ) - w))

@[simp]
lemma angularCubicReflectionGamma_zero (w : ℂ) :
    angularCubicReflectionGamma 0 w = cubicReflectionGamma w := by
  simp only [angularCubicReflectionGamma, cubicReflectionGamma, mul_zero, Nat.cast_zero, add_zero]

/-- The elementary part of higher cusp Mellin reflection. -/
def angularBesselReflectionFactor (k : ℕ) (q d : ℝ) (s : ℂ) : ℂ :=
  ((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + (6 * k : ℕ) + 1) *
    (2 : ℂ) ^ (2 - 4 * s) /
  ((4 * Real.pi * d : ℝ) : ℂ) ^ (3 - 2 * s + (6 * k : ℕ))

/-- Shifting both Mellin factors produces the shifted cubic Gamma ratio. -/
theorem angular_besselMellinFactor_reflection (k : ℕ) (q d : ℝ) (s : ℂ) :
    inverseBesselMellinFactor q (s + (3 * k : ℕ)) *
      besselMellinFactor d (1 - s + (3 * k : ℕ)) =
        angularBesselReflectionFactor k q d s * angularCubicReflectionGamma k (1 / 2 - s) := by
  have hp : (2 : ℂ) ^ (1 - 2 * (s + (3 * k : ℕ))) *
      (2 : ℂ) ^ (2 * (1 - s + (3 * k : ℕ)) - 1) = (2 : ℂ) ^ (2 - 4 * s) := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    ring
  unfold inverseBesselMellinFactor besselMellinFactor angularBesselReflectionFactor
    angularCubicReflectionGamma
  have h6 : ((6 * k : ℕ) : ℂ) = 2 * (3 * k : ℕ) := by push_cast; ring
  rw [show 2 * (s + (3 * k : ℕ)) + 1 = 2 * s + (6 * k : ℕ) + 1 by rw [h6]; ring,
    show (2 : ℂ) * (1 - s + (3 * k : ℕ)) + 1 = 3 - 2 * s + (6 * k : ℕ) by rw [h6]; ring,
    show (1 : ℂ) - s + (3 * k : ℕ) + 1 / 3 = 4 / 3 + (3 * k : ℕ) - s by ring,
    show (1 : ℂ) - s + (3 * k : ℕ) + 2 / 3 = 5 / 3 + (3 * k : ℕ) - s by ring,
    show (7 / 6 : ℂ) + (3 * k : ℕ) + (1 / 2 - s) = 5 / 3 + (3 * k : ℕ) - s by ring,
    show (5 / 6 : ℂ) + (3 * k : ℕ) + (1 / 2 - s) = 4 / 3 + (3 * k : ℕ) - s by ring,
    show (7 / 6 : ℂ) + (3 * k : ℕ) - (1 / 2 - s) = s + (3 * k : ℕ) + 2 / 3 by ring,
    show (5 / 6 : ℂ) + (3 * k : ℕ) - (1 / 2 - s) = s + (3 * k : ℕ) + 1 / 3 by ring]
  have he := congrArg (fun x : ℂ =>
    (((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + (6 * k : ℕ) + 1) *
      (Complex.Gamma (s + (3 * k : ℕ) + 1 / 3))⁻¹ *
      (Complex.Gamma (s + (3 * k : ℕ) + 2 / 3))⁻¹ *
      Complex.Gamma (4 / 3 + (3 * k : ℕ) - s) *
      Complex.Gamma (5 / 3 + (3 * k : ℕ) - s) *
      (((4 * Real.pi * d : ℝ) : ℂ) ^ (3 - 2 * s + (6 * k : ℕ)))⁻¹) * x) hp
  simp only [div_eq_mul_inv, mul_inv_rev] at he ⊢
  linear_combination he

/-- All extra archimedean scale powers are an ordinary integer power of `q/d`. -/
lemma angularBesselReflectionFactor_eq (k : ℕ) (q d : ℝ) (hq : 0 < q) (hd : 0 < d)
    (s : ℂ) :
    angularBesselReflectionFactor k q d s = ((q / d : ℝ) : ℂ) ^ (6 * k) *
      besselReflectionFactor q d s := by
  have hq0 : ((4 * Real.pi * q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hd0 : ((4 * Real.pi * d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have he : ((4 * Real.pi * q : ℝ) : ℂ) / ((4 * Real.pi * d : ℝ) : ℂ) =
      ((q / d : ℝ) : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.ofReal_ne_zero.mpr hd.ne']
  rw [angularBesselReflectionFactor,
    show (2 : ℂ) * s + (6 * k : ℕ) + 1 = (2 * s + 1) + (6 * k : ℕ) by ring,
    Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hd0, Complex.cpow_natCast,
    Complex.cpow_natCast, ← he, div_pow, besselReflectionFactor]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The higher Fourier normalization cancels the extra radial scale powers exactly. -/
lemma angular_source_reflection_scale_cancel (k : ℕ) (j : Fin 3) (s : ℂ) :
    ((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale j : ℂ)) ^ (6 * k) *
        angularBesselReflectionFactor k (sourceCuspRadialScale 0) (sourceCuspRadialScale j) s =
      conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k) *
        besselReflectionFactor (sourceCuspRadialScale 0) (sourceCuspRadialScale j) s := by
  have hratio : sourceCuspRadialScale 0 / sourceCuspRadialScale j = sourceCuspScale j := by
    rw [sourceCuspRadialScale, sourceCuspRadialScale, show sourceCuspScale 0 = 1 from rfl, div_one]
    field_simp [thetaBesselScale_pos.ne', (sourceCuspScale_pos j).ne']
  rw [angularBesselReflectionFactor_eq k _ _ (sourceCuspRadialScale_pos 0)
    (sourceCuspRadialScale_pos j), hratio, ← mul_assoc, sourceCuspAngularNormalization_cancel]

/-- The higher reflected Gamma ratio is holomorphic to the left of the spherical boundary. -/
theorem angularCubicReflectionGamma_differentiableAt (k : ℕ) (s : ℂ)
    (hs : -(5 / 6 : ℝ) - (3 * k : ℕ) < s.re) :
    DifferentiableAt ℂ (angularCubicReflectionGamma k) s := by
  push_cast at hs
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + (3 * k : ℕ) + s) (by
    simp only [Complex.add_re, Complex.natCast_re]
    norm_num
    linarith only [hs])).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + (3 * k : ℕ) + s) (by
    simp only [Complex.add_re, Complex.natCast_re]
    norm_num
    linarith only [hs])).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) + (3 * k : ℕ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) + (3 * k : ℕ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert! ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [angularCubicReflectionGamma, Function.comp_def, div_eq_mul_inv, mul_inv_rev,
    Pi.mul_apply]
  ring

/-- The vertical polynomial degree is independent of angular weight. -/
theorem angularCubicReflectionGamma_strip_bound (k A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖angularCubicReflectionGamma k ((σ : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (4 * A + 4) := by
  have hk : (0 : ℝ) ≤ (3 * k : ℕ) := Nat.cast_nonneg _
  obtain ⟨C₁, hC₁, h1⟩ := Gamma_pair_strip_bound (7 / 6 + (3 * k : ℕ)) (by linarith) A
  obtain ⟨C₂, hC₂, h2⟩ := Gamma_pair_strip_bound (5 / 6 + (3 * k : ℕ)) (by linarith) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  have heq : angularCubicReflectionGamma k ((σ : ℂ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 + (3 * k : ℕ) : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((7 / 6 + (3 * k : ℕ) : ℝ) : ℂ) - (σ + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 + (3 * k : ℕ) : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((5 / 6 + (3 * k : ℕ) : ℝ) : ℂ) - (σ + t * Complex.I))) := by
    simp only [angularCubicReflectionGamma, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.ofReal_natCast]
    exact (div_mul_div_comm _ _ _ _).symm
  rw [heq, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2 * A + 2)) * (C₂ * (1 + |t|) ^ (2 * A + 2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

/-- Every angular reflected Gamma ratio is unitary on the imaginary axis. -/
lemma angularCubicReflectionGamma_axis_norm (k : ℕ) (t : ℝ) :
    ‖angularCubicReflectionGamma k (t * Complex.I)‖ = 1 := by
  have h₁ := Gamma_vertical_conj (7 / 6 + (3 * k : ℕ)) t
  have h₂ := Gamma_vertical_conj (5 / 6 + (3 * k : ℕ)) t
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast] at h₁ h₂
  have hn₁ : Complex.Gamma ((7 / 6 : ℂ) + (3 * k : ℕ) + t * Complex.I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      norm_num
      positivity)
  have hn₂ : Complex.Gamma ((5 / 6 : ℂ) + (3 * k : ℕ) + t * Complex.I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      norm_num
      positivity)
  rw [angularCubicReflectionGamma, h₁, h₂, norm_div, norm_mul, norm_mul, norm_star, norm_star,
    div_self (mul_ne_zero (norm_ne_zero_iff.mpr hn₁) (norm_ne_zero_iff.mpr hn₂))]

/-- Every actual higher cusp reflection has the same Mellin involution. -/
theorem SourceCuspDatum.mellin_reflection_higher (d : SourceCuspDatum) (n : ℕ) (s : ℂ) :
    mellin (higherSourceBarProfile n d.point) (2 * s) =
      d.jetMultiplier n * (d.heightScale : ℂ) ^ (2 - 2 * s) *
        mellin (higherSourceZFamily n d.index d.dualPoint) (2 - 2 * s) := by
  apply cusp_mellin_reflection_of_identity (higherSourceBarProfile n d.point)
    (higherSourceZFamily n d.index d.dualPoint) (d.jetMultiplier n) (2 * s)
    d.heightScale d.heightScale_pos
  intro v hv
  rw [d.reflection_higher n v hv, reflectedCuspProfile]
  rw [Complex.cpow_neg, Complex.cpow_ofNat]
  simp only [div_eq_mul_inv]
  ring

/-- Bounded angular twisting preserves the original radial summability threshold. -/
lemma angular_source_radial_summable (a : O → ℂ) (Ψ : O → ℂ) (hΨ : ∀ h, ‖Ψ h‖ ≤ 1)
    (σ : ℝ) (ha : Summable (fun h => ‖a h‖ * sourceCuspRadialLength h ^ (1 / 2 - σ))) :
    Summable (fun h => ‖Ψ h * a h‖ * sourceCuspRadialLength h ^ (1 / 2 - σ)) := by
  apply ha.of_nonneg_of_le
    (fun h => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (sourceCuspRadialLength_pos h).le _))
  intro h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hΨ h) (norm_nonneg (a h)))
    (Real.rpow_nonneg (sourceCuspRadialLength_pos h).le _)

/-- The angular initial Dirichlet coefficients are the actual sextic twist. -/
def angularSourceBarDirichlet (k : ℕ) (z s : ℂ) : ℂ :=
  ∑' h : O, (elemPsiSix h ^ k * sourceBarRadialCoefficient z h) *
    (sourceCuspRadialLength h : ℂ) ^ (1 / 2 - s)

/-- The reflected Dirichlet coefficients have opposite angular orientation. -/
def angularSourceZDirichlet (k : ℕ) (j : Fin 3) (z s : ℂ) : ℂ :=
  ∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient j z h) *
    (sourceCuspRadialLength h : ℂ) ^ (1 / 2 - s)

@[simp]
lemma angularSourceBarDirichlet_zero (z s : ℂ) :
    angularSourceBarDirichlet 0 z s = sourceBarRadialDirichlet z s := by
  simp only [angularSourceBarDirichlet, sourceBarRadialDirichlet, pow_zero, one_mul]

@[simp]
lemma angularSourceZDirichlet_zero (j : Fin 3) (z s : ℂ) :
    angularSourceZDirichlet 0 j z s = sourceCuspRadialDirichlet j z s := by
  simp only [angularSourceZDirichlet, sourceCuspRadialDirichlet, pow_zero, one_mul]

private lemma mellin_eq_const_mul_of_eqOn (f g : ℝ → ℂ) (C s : ℂ)
    (he : ∀ v : ℝ, 0 < v → f v = C * g v) :
    mellin f s = C * mellin g s := by
  have hm : mellin (fun v => C * g v) s = C * mellin g s := by
    simpa only [smul_eq_mul] using mellin_const_smul g s C
  rw [← hm]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [he v hv]

/-- The initial angular jet has an actual, absolutely convergent Dirichlet expansion. -/
theorem higherSourceBarProfile_mellin (k : ℕ) (z s : ℂ) (hs : 2 ≤ s.re) :
    mellin (higherSourceBarProfile (6 * k) z) (2 * s) =
      conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k) *
        besselMellinFactor (sourceCuspRadialScale 0) (s + (3 * k : ℕ)) *
          angularSourceBarDirichlet k z s := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hm := mellin_eq_const_mul_of_eqOn (higherSourceBarProfile (6 * k) z)
    (angularRadialBesselProfile k sourceCuspRadialLength
      (fun h => elemPsiSix h ^ k * sourceBarRadialCoefficient z h) (sourceCuspRadialScale 0))
    (conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k)) (2 * s)
    (higherSourceBarProfile_eq_angularRadial k z)
  rw [hm]
  have hΨ (h : O) : ‖elemPsiSix h ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one h)
  have hshift : -(1 / 3) < (s + (3 * k : ℕ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have hk : (0 : ℝ) ≤ (3 * k : ℕ) := Nat.cast_nonneg _
    linarith only [hs, hk]
  rw [angularRadialBesselProfile_mellin k sourceCuspRadialLength sourceCuspRadialLength_pos
    _ _ (sourceCuspRadialScale_pos 0) s hshift
    (angular_source_radial_summable _ _ hΨ s.re (sourceBarRadialCoefficient_summable z s.re hs))]
  simp only [angularSourceBarDirichlet, mul_assoc]

/-- The reflected angular jet has the opposite, absolutely convergent Dirichlet expansion. -/
theorem higherSourceZFamily_mellin (k : ℕ) (j : Fin 3) (z s : ℂ) (hs : 2 ≤ s.re) :
    mellin (higherSourceZFamily (6 * k) j z) (2 * s) =
      ((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale j : ℂ)) ^ (6 * k) *
        besselMellinFactor (sourceCuspRadialScale j) (s + (3 * k : ℕ)) *
          angularSourceZDirichlet k j z s := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hm := mellin_eq_const_mul_of_eqOn (higherSourceZFamily (6 * k) j z)
    (angularRadialBesselProfile k sourceCuspRadialLength
      (fun h => conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient j z h) (sourceCuspRadialScale j))
    (((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale j : ℂ)) ^ (6 * k))
    (2 * s) (higherSourceZFamily_eq_angularRadial k j z)
  rw [hm]
  have hΨ (h : O) : ‖conj (elemPsiSix h) ^ k‖ ≤ 1 := by
    rw [norm_pow, Complex.norm_conj]
    exact pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one h)
  have hshift : -(1 / 3) < (s + (3 * k : ℕ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have hk : (0 : ℝ) ≤ (3 * k : ℕ) := Nat.cast_nonneg _
    linarith only [hs, hk]
  rw [angularRadialBesselProfile_mellin k sourceCuspRadialLength sourceCuspRadialLength_pos
    _ _ (sourceCuspRadialScale_pos j) s hshift
    (angular_source_radial_summable _ _ hΨ s.re
      (sourceCuspRadialCoefficient_summable j z s.re hs))]
  simp only [angularSourceZDirichlet, mul_assoc]

/-- Removing the shifted Bessel factor from a source Mellin transform. -/
def angularBesselDirichletTransform (k : ℕ) (F : ℝ → ℂ) (q : ℝ) (s : ℂ) : ℂ :=
  inverseBesselMellinFactor q (s + (3 * k : ℕ)) * mellin F (2 * s)

/-- Initial agreement with the angular arithmetic Dirichlet series. -/
theorem angularBesselDirichletTransform_source_initial (k : ℕ) (z s : ℂ) (hs : 2 ≤ s.re) :
    angularBesselDirichletTransform k (higherSourceBarProfile (6 * k) z)
        (sourceCuspRadialScale 0) s =
      conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k) *
        angularSourceBarDirichlet k z s := by
  have hshift : -(1 / 3) < (s + (3 * k : ℕ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have hk : (0 : ℝ) ≤ (3 * k : ℕ) := Nat.cast_nonneg _
    linarith only [hs, hk]
  rw [angularBesselDirichletTransform, higherSourceBarProfile_mellin k z s hs]
  have hi := inverseBesselMellinFactor_mul (sourceCuspRadialScale 0)
    (sourceCuspRadialScale_pos 0) (s + (3 * k : ℕ)) hshift
  calc
    _ = conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k) *
        (inverseBesselMellinFactor (sourceCuspRadialScale 0) (s + (3 * k : ℕ)) *
          besselMellinFactor (sourceCuspRadialScale 0) (s + (3 * k : ℕ))) *
        angularSourceBarDirichlet k z s := by ring
    _ = _ := by rw [hi, mul_one]

/-- Actual higher cusp reflection gives an absolutely convergent angular dual Dirichlet series. -/
theorem SourceCuspDatum.angular_dirichlet_reflection (d : SourceCuspDatum) (k : ℕ)
    (q : ℝ) (s : ℂ) (hs : s.re ≤ -1) :
    angularBesselDirichletTransform k (higherSourceBarProfile (6 * k) d.point) q s =
      (d.jetMultiplier (6 * k) * (d.heightScale : ℂ) ^ (2 - 2 * s) *
        ((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale d.index : ℂ)) ^ (6 * k) *
        angularBesselReflectionFactor k q (sourceCuspRadialScale d.index) s) *
        angularCubicReflectionGamma k (1 / 2 - s) *
        angularSourceZDirichlet k d.index d.dualPoint (1 - s) := by
  have hs' : 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith only [hs]
  have hm := higherSourceZFamily_mellin k d.index d.dualPoint (1 - s) hs'
  rw [show (2 : ℂ) * (1 - s) = 2 - 2 * s by ring] at hm
  rw [angularBesselDirichletTransform, d.mellin_reflection_higher, hm]
  calc
    _ = (d.jetMultiplier (6 * k) * (d.heightScale : ℂ) ^ (2 - 2 * s) *
        ((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale d.index : ℂ)) ^ (6 * k)) *
        (inverseBesselMellinFactor q (s + (3 * k : ℕ)) *
          besselMellinFactor (sourceCuspRadialScale d.index) (1 - s + (3 * k : ℕ))) *
        angularSourceZDirichlet k d.index d.dualPoint (1 - s) := by ring
    _ = _ := by rw [angular_besselMellinFactor_reflection]; ring

/-- The source Mellin transform normalized to its actual angular Dirichlet coefficients. -/
def angularSourceDirichletTransform (k : ℕ) (z s : ℂ) : ℂ :=
  (conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k))⁻¹ *
    angularBesselDirichletTransform k (higherSourceBarProfile (6 * k) z)
      (sourceCuspRadialScale 0) s

/-- Exact agreement with the angular source Dirichlet series in its absolute half-plane. -/
theorem angularSourceDirichletTransform_initial (k : ℕ) (z s : ℂ) (hs : 2 ≤ s.re) :
    angularSourceDirichletTransform k z s = angularSourceBarDirichlet k z s := by
  rw [angularSourceDirichletTransform, angularBesselDirichletTransform_source_initial k z s hs,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ sourceAngularNormalization_ne_zero), one_mul]

/-- Higher angular reflection has the original conductor scale and only a shifted Gamma ratio. -/
theorem SourceCuspDatum.angular_source_reflection (d : SourceCuspDatum) (k : ℕ)
    (s : ℂ) (hs : s.re ≤ -1) :
    angularSourceDirichletTransform k d.point s =
      (d.jetMultiplier (6 * k) * (d.heightScale : ℂ) ^ (2 - 2 * s) *
        besselReflectionFactor (sourceCuspRadialScale 0) (sourceCuspRadialScale d.index) s) *
        angularCubicReflectionGamma k (1 / 2 - s) *
        angularSourceZDirichlet k d.index d.dualPoint (1 - s) := by
  have hc : (conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k))⁻¹ *
      (((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale d.index : ℂ)) ^ (6 * k) *
        angularBesselReflectionFactor k (sourceCuspRadialScale 0) (sourceCuspRadialScale d.index) s) =
      besselReflectionFactor (sourceCuspRadialScale 0) (sourceCuspRadialScale d.index) s := by
    rw [angular_source_reflection_scale_cancel, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ sourceAngularNormalization_ne_zero), one_mul]
  rw [angularSourceDirichletTransform, d.angular_dirichlet_reflection k _ s hs]
  calc
    _ = (d.jetMultiplier (6 * k) * (d.heightScale : ℂ) ^ (2 - 2 * s)) *
        ((conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k))⁻¹ *
          (((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale d.index : ℂ)) ^ (6 * k) *
            angularBesselReflectionFactor k (sourceCuspRadialScale 0) (sourceCuspRadialScale d.index) s)) *
        angularCubicReflectionGamma k (1 / 2 - s) *
        angularSourceZDirichlet k d.index d.dualPoint (1 - s) := by ring
    _ = _ := by rw [hc]

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
