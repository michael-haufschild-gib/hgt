import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularSourceEntire
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularKernelData

/-!
# Contour shifting for actual angular cubic sources

Entire higher-source Mellin transforms and reciprocal Gamma growth permit contour shifting
between the initial and reflected absolute-convergence lines. The reflected line has the
original radial scale and a multiplier of modulus equal to the squared cusp width.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped ContDiff ComplexConjugate Classical Topology FourierTransform SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open GaloisForLFunctions.FamilyContinuationTheory
noncomputable section

lemma angularBesselDirichletTransform_strip_bound (k : ℕ) (F : ℝ → ℂ) (q : ℝ) (hq : 0 < q)
    (a b : ℝ) (ha : MellinConvergent F ((2 * a : ℝ) : ℂ))
    (hb : MellinConvergent F ((2 * b : ℝ) : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b →
      ‖angularBesselDirichletTransform k F q s‖ ≤ C * Real.exp (2 * Real.pi * |s.im|) := by
  obtain ⟨Ci, hCi, hi⟩ := inverseBesselMellinFactor_strip_bound q hq
    (a + (3 * k : ℕ)) (b + (3 * k : ℕ))
  obtain ⟨Cm, hCm, hm⟩ := mellin_uniform_strip_bound F (2 * a) (2 * b) ha hb
  refine ⟨Ci * Cm, mul_nonneg hCi hCm, ?_⟩
  intro s hs
  have hms : ‖mellin F (2 * s)‖ ≤ Cm := hm (2 * s)
    (by simp; linarith only [hs.1]) (by simp; linarith only [hs.2])
  have his : ‖inverseBesselMellinFactor q (s + (3 * k : ℕ))‖ ≤
      Ci * Real.exp (2 * Real.pi * |s.im|) := by
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      hi (s + (3 * k : ℕ)) (by simpa only [Complex.add_re, Complex.natCast_re] using
        show s.re + (3 * k : ℕ) ∈ Icc (a + (3 * k : ℕ)) (b + (3 * k : ℕ)) from
          ⟨by linarith only [hs.1], by linarith only [hs.2]⟩)
  rw [angularBesselDirichletTransform, norm_mul]
  calc
    _ ≤ (Ci * Real.exp (2 * Real.pi * |s.im|)) * Cm :=
      mul_le_mul his hms (norm_nonneg _) (mul_nonneg hCi (Real.exp_pos _).le)
    _ = _ := by ring

lemma SourceCuspDatum.angularSourceDirichletTransform_strip_bound (d : SourceCuspDatum)
    (k : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b →
      ‖angularSourceDirichletTransform k d.point s‖ ≤ C * Real.exp (2 * Real.pi * |s.im|) := by
  obtain ⟨C, hC, hb⟩ := angularBesselDirichletTransform_strip_bound k
    (higherSourceBarProfile (6 * k) d.point) (sourceCuspRadialScale 0) (sourceCuspRadialScale_pos 0)
    a b ((d.higher_mellin_entire (6 * k)).1.1 _) ((d.higher_mellin_entire (6 * k)).1.1 _)
  let B := ‖(conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k))⁻¹‖
  refine ⟨B * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro s hs
  rw [angularSourceDirichletTransform, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hb s hs) (norm_nonneg _)).trans_eq (by dsimp [B]; ring)

def angularSourceSmoothingIntegrand (k : ℕ) (z : ℂ) (V : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin V (s - 1 / 2) * (X : ℂ) ^ (s - 1 / 2) * angularSourceDirichletTransform k z s

lemma SourceCuspDatum.angularSourceSmoothingIntegrand_differentiable (d : SourceCuspDatum) (k : ℕ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) : Differentiable ℂ (angularSourceSmoothingIntegrand k d.point V X) := by
  have hm := (compact_source_mellin_differentiable V a b ha hVs hV).comp
    (show Differentiable ℂ (fun s : ℂ => s - 1 / 2) from by fun_prop)
  have hp : Differentiable ℂ (fun s : ℂ => (X : ℂ) ^ (s - 1 / 2)) :=
    (show Differentiable ℂ (fun s : ℂ => s - 1 / 2) from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (hm.mul hp).mul (d.angularSourceDirichletTransform_differentiable k)

lemma SourceCuspDatum.angularSourceSmoothingIntegrand_strip_bound (d : SourceCuspDatum) (k : ℕ)
    (lo hi : ℝ)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    ∃C : ℝ,0 ≤ C ∧ ∀s : ℂ,s.re∈Set.Icc lo hi →
      ‖angularSourceSmoothingIntegrand k d.point V X s‖ ≤ C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cd,hCd,hd⟩ := d.angularSourceDirichletTransform_strip_bound k lo hi
  have hVc (s : ℂ) := compact_source_mellin_convergent V a b ha hVs hV s
  obtain ⟨Cv,hCv,hv⟩ := mellin_uniform_strip_bound V (lo-1/2) (hi-1/2)
    (hVc _) (hVc _)
  let Cx : ℝ := X^(lo-1/2)+X^(hi-1/2)
  have hCx : 0 ≤ Cx := by dsimp [Cx];positivity
  refine ⟨Cv*Cx*Cd,mul_nonneg (mul_nonneg hCv hCx) hCd,?_⟩
  intro s hs
  have hvb : ‖mellin V (s-1/2)‖ ≤ Cv := hv (s-1/2)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  have hxb : ‖(X:ℂ)^(s-1/2)‖ ≤ Cx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have he : (s-1/2).re=s.re-1/2 := by simp
    rw [he]
    exact rpow_between_endpoints X (lo-1/2) (hi-1/2) (s.re-1/2) hX
      (by linarith [hs.1]) (by linarith [hs.2])
  rw [angularSourceSmoothingIntegrand,norm_mul,norm_mul]
  calc
    _ ≤ (Cv*Cx)*(Cd*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hvb hxb (norm_nonneg _) hCv) (hd s hs)
        (norm_nonneg _) (mul_nonneg hCv hCx)
    _=_ := by ring

theorem SourceCuspDatum.angularSourceSmoothingIntegrand_contour_eq (d : SourceCuspDatum) (k : ℕ)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) (lo hi : ℝ) (hlh : lo ≤ hi)
    (hl : Integrable (fun t : ℝ=>angularSourceSmoothingIntegrand k d.point V X ((lo:ℂ)+t*Complex.I)))
    (hh : Integrable (fun t : ℝ=>angularSourceSmoothingIntegrand k d.point V X ((hi:ℂ)+t*Complex.I))) :
    (∫t : ℝ,angularSourceSmoothingIntegrand k d.point V X ((lo:ℂ)+t*Complex.I))=
      ∫t : ℝ,angularSourceSmoothingIntegrand k d.point V X ((hi:ℂ)+t*Complex.I) := by
  obtain ⟨C,hC,hb⟩ := d.angularSourceSmoothingIntegrand_strip_bound k lo hi V a b ha hVs hV X hX
  apply VerticalContourShift.integral_eq_of_exponential_strip_growth
    (angularSourceSmoothingIntegrand k d.point V X) lo hi (2*Real.pi) C hlh (by positivity) hC
  · intro z hz1 hz2
    exact (d.angularSourceSmoothingIntegrand_differentiable k V a b ha hVs hV X hX) z
  · exact hl
  · exact hh
  · intro σ hσ t
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,mul_one,zero_add] using
      hb ((σ:ℂ)+t*Complex.I) (by simpa using hσ)


/-- The higher-jet multiplier retains the original absolute cusp-width factor. -/
def SourceCuspDatum.angularSmoothingMultiplier (d : SourceCuspDatum) (k : ℕ) : ℂ :=
  d.jetMultiplier (6 * k) * ((d.heightScale * (sourceCuspRadialScale 0 / sourceCuspRadialScale d.index) ^ 2 : ℝ) : ℂ)

/-- Higher jets retain the original reflected amplitude at every cusp. -/
lemma SourceCuspDatum.angularSmoothingMultiplier_norm (d : SourceCuspDatum) (k : ℕ) :
    ‖d.angularSmoothingMultiplier k‖ = (sourceCuspScale d.index) ^ 2 := by
  rw [SourceCuspDatum.angularSmoothingMultiplier, sourceCuspRadialScale_ratio,
    norm_mul, d.jetMultiplier_norm, Complex.norm_of_nonneg
      (mul_nonneg d.heightScale_pos.le (sq_nonneg _)), ← mul_assoc,
    inv_mul_cancel₀ d.heightScale_pos.ne', one_mul]

lemma SourceCuspDatum.angularSmoothing_reflected_line (d : SourceCuspDatum) (k : ℕ)
    (V : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (t : ℝ) :
    angularSourceSmoothingIntegrand k d.point V X ((-1 : ℂ) + (-t) * Complex.I) =
      d.angularSmoothingMultiplier k *
        ((∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) *
          (sourceCuspRadialLength h : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) *
          (((paperScale * d.smoothingScale X : ℝ) : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I)) *
            angularMellinEulerData k V 0 ((3 / 2 : ℂ) + t * Complex.I))) := by
  let s : ℂ := (-1 : ℂ) + (-t) * Complex.I
  let w : ℂ := (3 / 2 : ℂ) + t * Complex.I
  have hw : 1 / 2 - s = w := by dsimp [s, w]; ring
  have hsw : s - 1 / 2 = -w := by dsimp [s, w]; ring
  have hws : 1 / 2 - w = s := by dsimp [s, w]; ring
  have hp := bessel_reflection_scale (sourceCuspRadialScale 0) (sourceCuspRadialScale d.index)
    d.heightScale X 1 (sourceCuspRadialScale_pos 0) (sourceCuspRadialScale_pos d.index)
    d.heightScale_pos hX (by norm_num) w
  simp only [hws, Complex.ofReal_one, Complex.one_cpow, mul_one] at hp
  have hd : angularSourceZDirichlet k d.index d.dualPoint (1 - s) =
      ∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) *
        (sourceCuspRadialLength h : ℂ) ^ (-w) := by
    unfold angularSourceZDirichlet
    rw [show (1 / 2 : ℂ) - (1 - s) = -w by rw [← hsw]; ring]
  change angularSourceSmoothingIntegrand k d.point V X s = _
  rw [angularSourceSmoothingIntegrand, d.angular_source_reflection k s (by dsimp [s]; norm_num), hw, hsw, hd]
  change _ = d.angularSmoothingMultiplier k *
    ((∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) *
      (sourceCuspRadialLength h : ℂ) ^ (-w)) *
      (((paperScale * d.smoothingScale X : ℝ) : ℂ) ^ (-w) * angularMellinEulerData k V 0 w))
  rw [angularMellinEulerData, pow_zero, one_mul, angularMellinData]
  calc
    _ = (d.jetMultiplier (6 * k) * mellin V (-w) * angularCubicReflectionGamma k w *
          (∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) *
            (sourceCuspRadialLength h : ℂ) ^ (-w))) *
        ((d.heightScale : ℂ) ^ (2 - 2 * s) *
          besselReflectionFactor (sourceCuspRadialScale 0) (sourceCuspRadialScale d.index) s *
          (X : ℂ) ^ (-w)) := by ring
    _ = _ := by
      rw [hp]
      unfold SourceCuspDatum.angularSmoothingMultiplier SourceCuspDatum.smoothingScale
      ring

lemma angularSourceSmoothing_initial_line (k : ℕ) (z : ℂ) (V : ℝ → ℂ) (X : ℝ) (t : ℝ) :
    angularSourceSmoothingIntegrand k z V X ((2 : ℂ) + t * Complex.I) =
      mellin V ((3 / 2 : ℂ) + t * Complex.I) * (X : ℂ) ^ ((3 / 2 : ℂ) + t * Complex.I) *
        (∑' h : O, (elemPsiSix h ^ k * sourceBarRadialCoefficient z h) *
          (sourceCuspRadialLength h : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) := by
  rw [angularSourceSmoothingIntegrand, angularSourceDirichletTransform_initial k z _ (by norm_num), angularSourceBarDirichlet]
  rw [show (2 : ℂ) + t * Complex.I - 1 / 2 = 3 / 2 + t * Complex.I by ring,
    show (1 / 2 : ℂ) - (2 + t * Complex.I) = -(3 / 2 + t * Complex.I) by ring]


end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
