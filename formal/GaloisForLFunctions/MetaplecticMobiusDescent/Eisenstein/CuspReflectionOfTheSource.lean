/-
Cusp reflection of the cubic source adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.ReflectedLogarithmicKernel
import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.GammaBoundsAndContourShifts

/-!
# Cusp reflection of the cubic source

Exact smoothed reflection of the cubic source at every rational cusp. Finite Fourier inversion
gives a dual formula for the arithmetic Gauss sum; moving the Mellin contour gives polynomial
decay uniform in the radial scale. Cusp symbols at fixed and Weyl cusps.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics

theorem inverseBesselMellinFactor_strip_bound (q : ℝ) (hq : 0<q) (a b : ℝ) :
    ∃C : ℝ,0 ≤ C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖inverseBesselMellinFactor q s‖ ≤ C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cg,hCg,hg⟩ := CubicGammaExponential.inverse_cubic_Gamma_pair_strip_bound a b
  let Ca := (4*Real.pi*q)^(2*a+1)+(4*Real.pi*q)^(2*b+1)
  let Cb := (2:ℝ)^(1-2*b)+(2:ℝ)^(1-2*a)
  have hqpos : 0<4*Real.pi*q := by positivity
  have hCa : 0 ≤ Ca := by dsimp [Ca];positivity
  have hCb : 0 ≤ Cb := by dsimp [Cb];positivity
  refine ⟨Ca*Cb*Cg,by positivity,?_⟩
  intro s hs
  have hp1 : ‖((4*Real.pi*q:ℝ):ℂ)^(2*s+1)‖ ≤ Ca := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    have hr : (2*s+1).re=2*s.re+1 := by simp
    rw [hr]
    exact rpow_between_endpoints _ _ _ _ hqpos
      (by linarith [hs.1]) (by linarith [hs.2])
  have hp2 : ‖(2:ℂ)^(1-2*s)‖ ≤ Cb := by
    change ‖((2:ℝ):ℂ)^(1-2*s)‖ ≤ Cb
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ))]
    have hr : (1-2*s).re=1-2*s.re := by simp
    rw [hr]
    exact rpow_between_endpoints _ _ _ _ (by norm_num)
      (by linarith [hs.2]) (by linarith [hs.1])
  simp only [inverseBesselMellinFactor,norm_mul]
  calc
    _ ≤ (Ca*Cb)*(Cg*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hp1 hp2 (norm_nonneg _) hCa) (hg s hs)
        (norm_nonneg _) (mul_nonneg hCa hCb)
    _=_ := by ring

theorem continuedBesselDirichlet_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (a b : ℝ) (ha : MellinConvergent F ((2*a:ℝ):ℂ))
    (hb : MellinConvergent F ((2*b:ℝ):ℂ)) :
    ∃C : ℝ,0 ≤ C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖continuedBesselDirichlet F q s‖ ≤ C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Ci,hCi,hi⟩ := inverseBesselMellinFactor_strip_bound q hq a b
  obtain ⟨Cm,hCm,hm⟩ := mellin_uniform_strip_bound F (2*a) (2*b) ha hb
  refine ⟨Ci*Cm,mul_nonneg hCi hCm,?_⟩
  intro s hs
  have hms : ‖mellin F (2*s)‖ ≤ Cm := hm (2*s)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  rw [continuedBesselDirichlet,norm_mul]
  calc
    _ ≤ (Ci*Real.exp (2*Real.pi*|s.im|))*Cm :=
      mul_le_mul (hi s hs) hms (norm_nonneg _) (mul_nonneg hCi (Real.exp_pos _).le)
    _=_ := by ring

open scoped ContDiff FourierTransform SchwartzMap

theorem Gamma_pair_strip_bound (a : ℝ) (ha : 1 / 4 < a) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
        Complex.Gamma ((a : ℂ) - (σ + t * Complex.I))‖ ≤ C * (1 + |t|) ^ (2 * A + 2) := by
  let n : ℕ := 2 * A + 2
  let I : Set ℝ := Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)
  have hapos (σ : ℝ) (hσ : σ ∈ I) : 0 < a + σ := by
    have := hσ.1
    linarith
  have hdpos (σ : ℝ) (hσ : σ ∈ I) : 0 < (n : ℝ) - 2 * σ := by
    have := hσ.2
    dsimp [n]
    push_cast
    linarith
  have hdenpos (σ : ℝ) (hσ : σ ∈ I) : 0 < a - σ + n := by
    have h1 := hapos σ hσ
    have h2 := hdpos σ hσ
    linarith
  have hc1 : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_const.add continuous_id).continuousOn hapos
  have hc2 : ContinuousOn (fun σ : ℝ => Real.Gamma (a - σ + n)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      ((continuous_const.sub continuous_id).add continuous_const).continuousOn hdenpos
  have hc : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ) / Real.Gamma (a - σ + n)) I :=
    hc1.div hc2 (fun σ hσ => (Real.Gamma_pos_of_pos (hdenpos σ hσ)).ne')
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hc
  let C₁ : ℝ := |C₀| + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal (σ : ℝ) (hσ : σ ∈ I) :
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) ≤ C₁ := by
    exact (hC₀ (Set.mem_image_of_mem _ hσ)).trans (by dsimp [C₁]; linarith [le_abs_self C₀])
  let B : ℝ := |a| + A + 1 + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ n * C₁, mul_pos (pow_pos hB n) hC₁, ?_⟩
  intro σ hσ t
  have hσ' : σ ∈ I := hσ
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(a : ℂ) - (σ + t * Complex.I)‖ ≤ |a| + A + 1 + |t| := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(σ : ℂ) + t * Complex.I‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ = |a| + (|σ| + |t|) := by simp
      _ ≤ _ := by linarith
  have hzB : ‖(a : ℂ) - (σ + t * Complex.I)‖ + n ≤ B * (1 + |t|) := by
    dsimp [B]
    nlinarith [abs_nonneg a, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hprod : ‖∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)‖ ≤ B ^ n * (1 + |t|) ^ n := by
    apply (norm_Gamma_shift_factor _ n).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hzB n
  have hratio := (Gamma_shifted_pair_bound a σ t n (hapos σ hσ') (hdpos σ hσ')).trans
    (hreal σ hσ')
  have heq : Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I)) =
      (∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)) *
      (Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)) := by
    rw [div_eq_mul_inv, CubicGammaExponential.inverse_Gamma_shift _ n, div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ (B ^ n * (1 + |t|) ^ n) * C₁ :=
      mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [n]; ring

theorem cubicReflectionGamma_strip_bound (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖cubicReflectionGamma ((σ : ℂ) + t * Complex.I)‖ ≤ C * (1 + |t|) ^ (4 * A + 4) := by
  obtain ⟨C₁, hC₁, h1⟩ := Gamma_pair_strip_bound (7 / 6) (by norm_num) A
  obtain ⟨C₂, hC₂, h2⟩ := Gamma_pair_strip_bound (5 / 6) (by norm_num) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  have heq : cubicReflectionGamma ((σ : ℂ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) := by
    simp only [cubicReflectionGamma, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2 * A + 2)) * (C₂ * (1 + |t|) ^ (2 * A + 2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

open scoped ContDiff FourierTransform SchwartzMap

lemma besselSmoothingIntegrand_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (lo hi : ℝ) (hF : ∀s : ℂ,MellinConvergent F s)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    ∃C : ℝ,0 ≤ C ∧ ∀s : ℂ,s.re∈Set.Icc lo hi →
      ‖besselSmoothingIntegrand F q V X s‖ ≤ C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cd,hCd,hd⟩ := continuedBesselDirichlet_strip_bound F q hq lo hi (hF _) (hF _)
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
  rw [besselSmoothingIntegrand,norm_mul,norm_mul]
  calc
    _ ≤ (Cv*Cx)*(Cd*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hvb hxb (norm_nonneg _) hCv) (hd s hs)
        (norm_nonneg _) (mul_nonneg hCv hCx)
    _=_ := by ring

theorem besselSmoothingIntegrand_contour_eq (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent F s) (hFe : Differentiable ℂ (mellin F))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) (lo hi : ℝ) (hlh : lo ≤ hi)
    (hl : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I)))
    (hh : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I))) :
    (∫t : ℝ,besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I))=
      ∫t : ℝ,besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I) := by
  obtain ⟨C,hC,hb⟩ := besselSmoothingIntegrand_strip_bound F q hq lo hi hF V a b ha hVs hV X hX
  apply VerticalContourShift.integral_eq_of_exponential_strip_growth
    (besselSmoothingIntegrand F q V X) lo hi (2*Real.pi) C hlh (by positivity) hC
  · intro z hz1 hz2
    exact (besselSmoothingIntegrand_differentiable F q hq hFe V a b ha hVs hV X hX) z
  · exact hl
  · exact hh
  · intro σ hσ t
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,mul_one,zero_add] using
      hb ((σ:ℂ)+t*Complex.I) (by simpa using hσ)

theorem mellinData_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellinData V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := cubicReflectionGamma_strip_bound A
  obtain ⟨CV, hCV, hVb⟩ := compact_source_mellin_strip_decay V a b ha hsupp hV
    (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖cubicReflectionGamma ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        ‖cubicReflectionGamma ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmb hCγ.le

theorem mellinEulerData_strip_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinData_strip_decay V a b ha hsupp hV A (j + 2)
  refine ⟨((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by
      gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ t) (by positivity)

theorem mellinEulerData_vertical_integrable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    Integrable (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mellinEulerData_differentiableAt V a b ha hsupp hV j _ ?_).continuousAt.comp
    · fun_prop
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hσ.1]
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [div_eq_mul_inv] using hb σ hσ t)

theorem inverseMellinIntegrand_vertical_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)) := by
  apply (mellinEulerData_vertical_integrable V a b ha hsupp hV A j σ hσ).bdd_mul
    (c := y ^ (-σ))
  · exact ((show Continuous (fun t : ℝ => -((σ : ℂ) + t * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp

theorem inverseMellinIntegrand_strip_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun σ : ℝ => y ^ (-σ)) :=
    (Real.continuous_const_rpow hy.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))).bddAbove_image hc.continuousOn
  refine ⟨(|B| + 1) * C, by positivity, ?_⟩
  intro σ hσ t
  have hby : y ^ (-σ) ≤ |B| + 1 :=
    (hB (Set.mem_image_of_mem _ hσ)).trans (by linarith [le_abs_self B])
  rw [inverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (|B| + 1) * (C / (1 + t ^ 2)) :=
      mul_le_mul hby (hb σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_shift
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    mellinInv 0 (mellinEulerData V j) y = mellinInv σ (mellinEulerData V j) y := by
  obtain ⟨C, hC, hb⟩ := inverseMellinIntegrand_strip_bound V a b ha hsupp hV A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · norm_num
    · exact Nat.cast_nonneg A
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      (∫ t : ℝ, inverseMellinIntegrand V j y ((-(1 / 4) : ℝ) + t * Complex.I)) =
      ∫ t : ℝ, inverseMellinIntegrand V j y ((ρ : ℂ) + t * Complex.I) := by
    apply VerticalContourShift.integral_eq_of_strip_decay
      (inverseMellinIntegrand V j y) (-(1 / 4)) ρ C hρ.1
    · intro z hzlo hzhi
      apply inverseMellinIntegrand_differentiableAt V a b ha hsupp hV j y hy z
      linarith
    · apply inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j
        (-(1 / 4)) ⟨le_rfl, hρ.1.trans hρ.2⟩ y hy
    · exact inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j ρ hρ y hy
    · intro r hr t
      exact hb r ⟨hr.1, hr.2.trans hρ.2⟩ t
  have heq := (hshift 0 h0).symm.trans (hshift σ hσ)
  simpa only [mellinInv, smul_eq_mul, inverseMellinIntegrand] using
    congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) heq

theorem mellinInv_euler_line_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ),
      ∀ y : ℝ, 0 < y → ‖mellinInv σ (mellinEulerData V j) y‖ ≤ C * y ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ hσ y hy
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤ (y ^ (-σ) * C) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * C) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * C) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by field_simp

lemma paperKernel_three_halves (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (x:ℝ) (hx:0<x) :
    paperKernel V x=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      ((paperScale*x:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
        mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I) := by
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  change paperKernel V x=_
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*cubicReflectionGamma s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using he

lemma paperKernel_three_halves_bound (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V) :
    ∃C:ℝ,0<C ∧ ∀x:ℝ,0<x→‖paperKernel V x‖ ≤ C*(paperScale*x)^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩:=mellinInv_euler_line_bound V v0 v1 hv0 hVs hV 2 0
  refine ⟨C,hC,?_⟩
  intro x hx
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*cubicReflectionGamma s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  rw [he]
  exact hb (3/2) (by norm_num) (paperScale*x) (mul_pos paperScale_pos hx)

lemma paperKernel_weighted_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>a i*paperKernel V (c*r i)) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound V v0 v1 hv0 hVs hV
  apply Summable.of_norm
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _ ≤ ‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

theorem paperKernel_weighted_mellin {α:Type*} [Countable α]
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) :
    (∑'i,a i*paperKernel V (c*r i))=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      (∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
        (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
          mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)) := by
  let M:ℝ→ℂ:=fun t=>((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
    mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)
  have hM:Integrable M:=by
    simpa only [M,inverseMellinIntegrand,Complex.ofReal_div,Complex.ofReal_ofNat] using
      inverseMellinIntegrand_vertical_integrable V v0 v1 hv0 hVs hV 2 0 (3/2)
        (by norm_num) (paperScale*c) (mul_pos paperScale_pos hc)
  have hi (i:α) : a i*paperKernel V (c*r i)=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I))*M t := by
    rw [paperKernel_three_halves V v0 v1 hv0 hVs hV _ (mul_pos hc (hr i))]
    rw [←mul_assoc,mul_comm (a i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_pos paperScale_pos hc).le (hr i).le]
    dsimp only [M]
    ring
  simp_rw [hi]
  rw [tsum_mul_left]
  congr 1
  simpa only [M,Complex.ofReal_div,Complex.ofReal_ofNat] using
    weighted_vertical_sum_integral r hr a (3/2) has M hM

theorem paperKernel_weighted_norm_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>‖a i*paperKernel V (c*r i)‖) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound V v0 v1 hv0 hVs hV
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _ ≤ ‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

lemma SourceCuspDatum.smoothing_left_integrable (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => besselSmoothingIntegrand
      (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
      (sourceCuspRadialScale 0) V X ((-1 : ℂ) + t * Complex.I)) := by
  let M : ℝ → ℂ := fun t =>
    (∑' h : O, sourceCuspRadialCoefficient d.index d.dualPoint h *
      (sourceCuspRadialLength h : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) *
      (((paperScale * d.smoothingScale X : ℝ) : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I)) *
        mellinEulerData V 0 ((3 / 2 : ℂ) + t * Complex.I))
  have hK := inverseMellinIntegrand_vertical_integrable V a b ha hVs hV 2 0 (3 / 2)
    (by norm_num) (paperScale * d.smoothingScale X) (mul_pos paperScale_pos (d.smoothingScale_pos X hX))
  have hc : Summable (fun h : O => ‖sourceCuspRadialCoefficient d.index d.dualPoint h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [neg_div] using
      sourceCuspRadialCoefficient_weighted_summable d.index d.dualPoint
  have hi : Integrable M := by
    simpa only [M, inverseMellinIntegrand, Complex.ofReal_div, Complex.ofReal_ofNat] using
      weighted_vertical_sum_mul_integrable sourceCuspRadialLength sourceCuspRadialLength_pos
        (sourceCuspRadialCoefficient d.index d.dualPoint) (3 / 2)
        hc
        (fun t : ℝ => inverseMellinIntegrand V 0 (paperScale * d.smoothingScale X)
          (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) hK
  apply ((hi.comp_neg).const_mul d.smoothingMultiplier).congr
  filter_upwards with t
  simpa only [M, Complex.ofReal_neg, neg_neg] using (d.smoothing_reflected_line V X hX (-t)).symm

theorem SourceCuspDatum.smoothing_left_kernel (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, besselSmoothingIntegrand
      (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
      (sourceCuspRadialScale 0) V X ((-1 : ℂ) + t * Complex.I)) =
      d.smoothingMultiplier * ∑' h : O, sourceCuspRadialCoefficient d.index d.dualPoint h *
        paperKernel V (d.smoothingScale X * sourceCuspRadialLength h) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hc : Summable (fun h : O => ‖sourceCuspRadialCoefficient d.index d.dualPoint h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [neg_div] using
      sourceCuspRadialCoefficient_weighted_summable d.index d.dualPoint
  have hk := paperKernel_weighted_mellin sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient d.index d.dualPoint)
    hc V a b ha hVs hV
    (d.smoothingScale X) (d.smoothingScale_pos X hX)
  rw [hk]
  rw [← integral_neg_eq_self (fun t : ℝ => besselSmoothingIntegrand
    (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
    (sourceCuspRadialScale 0) V X ((-1 : ℂ) + t * Complex.I)) volume]
  simp only [Complex.ofReal_neg, d.smoothing_reflected_line V X hX]
  rw [integral_const_mul]
  ring

/-- Exact smoothed reflection of the actual cubic source at every rational cusp. -/
theorem SourceCuspDatum.smoothed_reflection (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (∑' h : O, sourceBarRadialCoefficient d.point h * V (sourceCuspRadialLength h / X)) =
      d.smoothingMultiplier * ∑' h : O, sourceCuspRadialCoefficient d.index d.dualPoint h *
        paperKernel V (d.smoothingScale X * sourceCuspRadialLength h) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hc : Summable (fun h : O => ‖sourceBarRadialCoefficient d.point h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num] using
      sourceBarRadialCoefficient_summable d.point 2 le_rfl
  have hm := weightedMellin_inversion sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceBarRadialCoefficient d.point) (3 / 2) hc V a b ha hVs hV X hX
  have hmi := compactMellin_vertical_integrable V a b ha hVs hV (3 / 2)
  have hbase := vertical_power_mul_integrable _ hmi X (3 / 2) hX
  have hi := weighted_vertical_sum_mul_integrable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceBarRadialCoefficient d.point) (3 / 2) hc
    (fun t : ℝ => (X : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + t * Complex.I) *
      mellin V (((3 / 2 : ℝ) : ℂ) + t * Complex.I)) hbase
  have hright : Integrable (fun t : ℝ => besselSmoothingIntegrand
      (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
      (sourceCuspRadialScale 0) V X ((2 : ℂ) + t * Complex.I)) := by
    simp_rw [sourceBar_smoothing_initial_line]
    apply hi.congr
    filter_upwards with t
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hleft' : Integrable (fun t : ℝ => besselSmoothingIntegrand
      (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
      (sourceCuspRadialScale 0) V X (((-1 : ℝ) : ℂ) + t * Complex.I)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
      d.smoothing_left_integrable V a b ha hVs hV X hX
  have hright' : Integrable (fun t : ℝ => besselSmoothingIntegrand
      (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
      (sourceCuspRadialScale 0) V X (((2 : ℝ) : ℂ) + t * Complex.I)) := by
    simpa only [Complex.ofReal_ofNat] using hright
  have hshift := besselSmoothingIntegrand_contour_eq
    (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
    (sourceCuspRadialScale 0) (sourceCuspRadialScale_pos 0)
    d.mellin_entire.1.1 d.mellin_entire.1.2 V a b ha hVs hV X hX (-1) 2 (by norm_num)
    hleft' hright'
  simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat] at hshift
  have hm' : (∑' h : O, sourceBarRadialCoefficient d.point h * V (sourceCuspRadialLength h / X)) =
      (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, besselSmoothingIntegrand
        (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
        (sourceCuspRadialScale 0) V X ((2 : ℂ) + t * Complex.I)) := by
    simpa only [sourceBar_smoothing_initial_line, Complex.ofReal_div, Complex.ofReal_ofNat] using hm
  rw [hm', ← hshift]
  exact d.smoothing_left_kernel V a b ha hVs hV X hX

/-- Finite Fourier inversion and cusp reflection give an exact dual formula for the arithmetic Gauss sum. -/
theorem thetaSmoothedGaussSum_finite_reflection (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    thetaSmoothedGaussSum (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) V X =
      rationalSourceThetaScalar⁻¹ *
        ∑ i, finiteAdditiveFourierCoeff
          (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ) i *
          ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingMultiplier *
            ∑' h : O, sourceCuspRadialCoefficient
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).index
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).dualPoint h *
              paperKernel V ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingScale X *
                sourceCuspRadialLength h)) := by
  let χ := Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom
  let W : O → ℂ := fun h => V (sourceCuspRadialLength h / X)
  have hcoef : Summable (fun h : O => ‖sourceBarRadialCoefficient 0 h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num] using
      sourceBarRadialCoefficient_summable 0 2 le_rfl
  have hW : Summable (fun h : O => ‖sourceBarRadialCoefficient 0 h * W h‖) :=
    weighted_compact_test_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
      (sourceBarRadialCoefficient 0) (3 / 2) hcoef V a b ha hVs hV X hX
  have hf := sourceBar_smoothed_finite_translation (9 * c) (mul_ne_zero (by norm_num) hc)
    (finiteThetaTwist c Ψ) W hW
  calc
    _ = ∑' h : O, (rationalSourceThetaScalar⁻¹ * star (rationalSourceResidualFourierCoefficient h) *
        fixedThetaTwist χ h) *
        (((-2 * Real.pi * Complex.I * star (cuspFrequency h)) /
          (sourceCuspRadialLength h : ℂ)) * W h) := (fixedThetaTwist_source_tsum χ _).symm
    _ = rationalSourceThetaScalar⁻¹ *
        ∑' h : O, finiteThetaTwist c Ψ (Ideal.Quotient.mk _ h) * sourceBarRadialCoefficient 0 h * W h := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro h
      rw [sourceBarRadialCoefficient_at_zero, finiteThetaTwist_mk]
      ring
    _ = rationalSourceThetaScalar⁻¹ *
        ∑ i, finiteAdditiveFourierCoeff
          (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ) i *
          ∑' h : O, sourceBarRadialCoefficient (thetaFourierTranslation (9 * c) i) h * W h := by rw [hf]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [← finiteTwistCusp_point (9 * c) (mul_ne_zero (by norm_num) hc) i]
      exact (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothed_reflection V a b ha hVs hV X hX

/-- Exact cubic reflection of the completed squarefree–cube sum at a finite character. -/
theorem completedT_finite_smoothed_reflection (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W X =
      thetaDerivativeScalar⁻¹ *
        ∑ i, finiteAdditiveFourierCoeff
          (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ) i *
          ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingMultiplier *
            ∑' h : O, sourceCuspRadialCoefficient
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).index
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).dualPoint h *
              paperKernel (Vstar W)
                ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingScale X *
                  sourceCuspRadialLength h)) := by
  have he := thetaSmoothedGaussSum_finite_reflection c hc Ψ (Vstar W) a b ha
    (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) X hX
  rw [thetaSmoothedGaussSum_eq_completedT] at he
  apply (mul_left_cancel₀ thetaRadialDerivativeScalar_ne_zero)
  rw [he, thetaDerivativeScalar, mul_inv_rev]
  field_simp [thetaRadialDerivativeScalar_ne_zero]

/-- Moving the Mellin contour gives arbitrarily high polynomial decay. -/
theorem paperKernel_power_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → ‖paperKernel V x‖ ≤ C * x ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := mellinInv_euler_line_bound V a b ha hs hV N 0
  refine ⟨C * paperScale ^ (-(N : ℝ)), mul_pos hC (Real.rpow_pos_of_pos paperScale_pos _), ?_⟩
  intro x hx
  have hN : (N : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (N : ℝ) :=
    ⟨by linarith [Nat.cast_nonneg (α := ℝ) N], le_rfl⟩
  have he := mellinInv_euler_shift V a b ha hs hV N 0 (N : ℝ) hN
    (paperScale * x) (mul_pos paperScale_pos hx)
  have hl : mellinInv 0 (mellinEulerData V 0) (paperScale * x) = paperKernel V x := by
    have hf : mellinEulerData V 0 = (fun s : ℂ => mellin V (-s) * cubicReflectionGamma s) := by
      funext s
      simp only [mellinEulerData, pow_zero, one_mul, mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  rw [he]
  simpa only [Real.mul_rpow paperScale_pos.le hx.le, mul_assoc] using
    hb (N : ℝ) hN (paperScale * x) (mul_pos paperScale_pos hx)

/-- All three reflected series have the same polynomial bound in their radial scale. -/
theorem sourceCusp_kernel_uniform_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin 3) (z : ℂ) (c : ℝ), 0 < c →
      ‖∑' h : O, sourceCuspRadialCoefficient j z h * paperKernel V (c * sourceCuspRadialLength h)‖ ≤
        C * c ^ (-(N : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := paperKernel_power_bound V a b ha hs hV N
  let S : ℝ := ∑ j : Fin 3, sourceCuspRadialMass j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => sourceCuspRadialMass_nonneg j)
  refine ⟨B * (S + 1), mul_pos hB (by linarith), ?_⟩
  intro j z c hc
  have hm : Summable (fun h : O => ‖sourceCuspRadialCoefficient j z h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [neg_div] using sourceCuspRadialCoefficient_weighted_summable j z
  have hi := paperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient j z) hm V a b ha hs hV c hc
  have hp : ∀ h : O, sourceCuspRadialLength h ^ (-(N : ℝ)) ≤
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ)) := by
    intro h
    apply Real.rpow_le_rpow_of_exponent_le (sourceCuspRadialLength_one_le h)
    have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  calc
    _ ≤ ∑' h : O, ‖sourceCuspRadialCoefficient j z h * paperKernel V (c * sourceCuspRadialLength h)‖ :=
      norm_tsum_le_tsum_norm hi
    _ ≤ ∑' h : O, (B * c ^ (-(N : ℝ))) *
        (‖sourceCuspRadialCoefficient j z h‖ * sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
      apply Summable.tsum_le_tsum _ hi (hm.mul_left _)
      intro h
      rw [norm_mul]
      calc
        _ ≤ ‖sourceCuspRadialCoefficient j z h‖ * (B * (c * sourceCuspRadialLength h) ^ (-(N : ℝ))) :=
          mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (sourceCuspRadialLength_pos h))) (norm_nonneg _)
        _ = (B * c ^ (-(N : ℝ))) *
            (‖sourceCuspRadialCoefficient j z h‖ * sourceCuspRadialLength h ^ (-(N : ℝ))) := by
          rw [Real.mul_rpow hc.le (sourceCuspRadialLength_pos h).le]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hp h) (norm_nonneg _)) (by positivity)
    _ = (B * c ^ (-(N : ℝ))) * sourceCuspRadialMass j := by
      rw [tsum_mul_left, sourceCuspRadialMass_sum]
    _ ≤ (B * c ^ (-(N : ℝ))) * (S + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hj : sourceCuspRadialMass j ≤ S :=
        Finset.single_le_sum (fun k _ => sourceCuspRadialMass_nonneg k) (Finset.mem_univ j)
      linarith
    _ = _ := by ring

theorem sourceBar_smoothed_uniform_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : SourceCuspDatum) (X : ℝ), 0 < X →
      ‖∑' h : O, sourceBarRadialCoefficient d.point h * V (sourceCuspRadialLength h / X)‖ ≤
        C * d.smoothingScale X ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := sourceCusp_kernel_uniform_bound V a b ha hs hV N hN
  refine ⟨9 * C, by positivity, ?_⟩
  intro d X hX
  rw [d.smoothed_reflection V a b ha hs hV X hX, norm_mul]
  calc
    _ ≤ 9 * (C * d.smoothingScale X ^ (-(N : ℝ))) :=
      mul_le_mul d.smoothingMultiplier_norm_le
        (hb d.index d.dualPoint (d.smoothingScale X) (d.smoothingScale_pos X hX))
        (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Uniform finite-character reflection bound, with every cusp scale explicit. -/
theorem completedT_finite_reflection_bound (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : O) (hc : c ≠ 0)
      [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ),
      (∀ x, ‖Ψ x‖ ≤ 1) → ∀ X : ℝ, 0 < X →
      ‖completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W X‖ ≤
        C * ∑ i : O ⧸ Ideal.span {9 * c},
          (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingScale X ^ (-(N : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := sourceCusp_kernel_uniform_bound (Vstar W) a b ha
    (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) N hN
  refine ⟨‖thetaDerivativeScalar⁻¹‖ * (9 * B),
    mul_pos (norm_pos_iff.mpr (inv_ne_zero thetaDerivativeScalar_ne_zero)) (by positivity), ?_⟩
  intro c hc _ Ψ hΨ X hX
  rw [completedT_finite_smoothed_reflection c hc Ψ W a b ha hs hW X hX, norm_mul]
  calc
    _ ≤ ‖thetaDerivativeScalar⁻¹‖ * ∑ i, ‖finiteAdditiveFourierCoeff
        (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ) i *
        ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingMultiplier *
          ∑' h : O, sourceCuspRadialCoefficient
            (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).index
            (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).dualPoint h *
            paperKernel (Vstar W)
              ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingScale X *
                sourceCuspRadialLength h))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖thetaDerivativeScalar⁻¹‖ * ∑ i : O ⧸ Ideal.span {9 * c},
        (9 * B) * (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingScale X ^ (-(N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      let d := finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i
      rw [norm_mul, norm_mul]
      have hf := finiteAdditiveFourierCoeff_norm_le_one
        (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
        (finiteThetaTwist c Ψ) (finiteThetaTwist_norm_le_one c Ψ hΨ) i
      calc
        _ ≤ 1 * (9 * (B * d.smoothingScale X ^ (-(N : ℝ)))) :=
          mul_le_mul hf (mul_le_mul d.smoothingMultiplier_norm_le
            (hb d.index d.dualPoint (d.smoothingScale X) (d.smoothingScale_pos X hX))
            (norm_nonneg _) (by norm_num)) (by positivity) (by norm_num)
        _ = _ := by ring
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The reflected Gauss sum decays uniformly once the smoothing scale exceeds the fourth power of the conductor. -/
theorem completedT_conductor_bound (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : O) (hc : c ≠ 0)
      [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ),
      (∀ x, ‖Ψ x‖ ≤ 1) → ∀ X : ℝ, 0 < X →
      ‖completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W X‖ ≤
        C * (Fintype.card (O ⧸ Ideal.span {9 * c}) : ℝ) *
          (sourceReflectionScale * X / ‖ringComplex (9 * c)‖ ^ 4) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := completedT_finite_reflection_bound W a b ha hs hW N hN
  refine ⟨C, hC, ?_⟩
  intro c hc _ Ψ hΨ X hX
  apply (hb c hc Ψ hΨ X hX).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC.le
  calc
    _ ≤ ∑ i : O ⧸ Ideal.span {9 * c},
        (sourceReflectionScale * X / ‖ringComplex (9 * c)‖ ^ 4) ^ (-(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hc9 : 9 * c ≠ 0 := mul_ne_zero (by norm_num) hc
      apply Real.rpow_le_rpow_of_nonpos
        (div_pos (mul_pos sourceReflectionScale_pos hX)
          (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hc9)) 4))
      · exact (finiteTwistCusp (9 * c) hc9 i).smoothingScale_lower
          (-3 * Quotient.out i) (9 * c) hc9 (rationalSourceCusp_point _ _ hc9) X hX
      · exact neg_nonpos.mpr (Nat.cast_nonneg N)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Full-frequency reflection keeps the arithmetic squarefree–cube indexing on every cusp. -/
theorem SourceCuspDatum.smoothed_reflection_full_index (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (∑' h : O, sourceBarRadialCoefficient d.point h * V (sourceCuspRadialLength h / X)) =
      d.smoothingMultiplier * ∑' p : ThetaFullIndex,
        sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p) *
          paperKernel V (d.smoothingScale X *
            (‖ringComplex lambda‖ ^ (2 * p.2.1) * completedMellinLength p.2.2)) := by
  rw [d.smoothed_reflection V a b ha hs hV X hX,
    sourceCuspRadial_tsum_full_index d.index d.dualPoint
      (fun h => paperKernel V (d.smoothingScale X * sourceCuspRadialLength h))]
  simp only [thetaFullFrequency_radialLength]

/-- Every logarithmic derivative has arbitrary polynomial decay at infinity. -/
theorem paperKernelLogDerivative_power_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      ‖paperKernelLogDerivative V j x‖ ≤ C * x ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := mellinInv_euler_line_bound V a b ha hs hV N j
  refine ⟨C * paperScale ^ (-(N : ℝ)), mul_pos hC (Real.rpow_pos_of_pos paperScale_pos _), ?_⟩
  intro x hx
  have hN : (N : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (N : ℝ) :=
    ⟨by linarith [Nat.cast_nonneg (α := ℝ) N], le_rfl⟩
  rw [paperKernelLogDerivative, mellinInv_euler_shift V a b ha hs hV N j (N : ℝ) hN
    (paperScale * x) (mul_pos paperScale_pos hx)]
  simpa only [Real.mul_rpow paperScale_pos.le hx.le, mul_assoc] using
    hb (N : ℝ) hN (paperScale * x) (mul_pos paperScale_pos hx)

/-- Polynomially weighted logarithmic derivatives remain bounded on the positive axis. -/
theorem paperKernelLogDerivative_weighted_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      (1 + x) ^ N * ‖paperKernelLogDerivative V j x‖ ≤ C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := paperKernelLogDerivative_power_bound V a b ha hs hV 0 j
  obtain ⟨Cₙ, hCₙ, hbₙ⟩ := paperKernelLogDerivative_power_bound V a b ha hs hV N j
  refine ⟨2 ^ N * (C₀ + Cₙ), by positivity, ?_⟩
  intro x hx
  have hzero : ‖paperKernelLogDerivative V j x‖ ≤ C₀ := by
    simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hb₀ x hx
  have hhigh : ‖paperKernelLogDerivative V j x‖ ≤ Cₙ / x ^ N := by
    simpa only [Real.rpow_neg hx.le, Real.rpow_natCast, div_eq_mul_inv] using hbₙ x hx
  by_cases hx1 : x ≤ 1
  · have hp : (1 + x) ^ N ≤ (2 : ℝ) ^ N := by gcongr; linarith
    calc
      _ ≤ 2 ^ N * C₀ := mul_le_mul hp hzero (norm_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hp : (1 + x) ^ N ≤ (2 : ℝ) ^ N * x ^ N := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ N * x ^ N) * (Cₙ / x ^ N) :=
        mul_le_mul hp hhigh (norm_nonneg _) (by positivity)
      _ = 2 ^ N * Cₙ := by field_simp [hx.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- On any fixed logarithmic interval, all kernel derivatives have uniform decay in the radial parameter. -/
theorem paperKernel_exp_local_derivative_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (M : ℝ) (hM : 0 ≤ M) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ u : ℝ, |u| ≤ M →
      (1 + R) ^ N * ‖iteratedDeriv j (fun v : ℝ => paperKernel V (R * Real.exp v)) u‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := paperKernelLogDerivative_weighted_bound V a b ha hs hV N j
  refine ⟨Real.exp M ^ N * C, by positivity, ?_⟩
  intro R hR u hu
  have hMu : 0 ≤ M + u := by linarith [(abs_le.mp hu).1]
  have hE : 1 ≤ Real.exp M := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hM
  have hEu : 1 ≤ Real.exp M * Real.exp u := by
    rw [← Real.exp_add]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hMu
  have hbase : 1 + R ≤ Real.exp M * (1 + R * Real.exp u) := by
    have hRu := mul_le_mul_of_nonneg_left hEu hR.le
    nlinarith only [hE, hRu]
  have hp : (1 + R) ^ N ≤ Real.exp M ^ N * (1 + R * Real.exp u) ^ N := by
    rw [← mul_pow]
    gcongr
  rw [iteratedDeriv_paperKernel_exp V a b ha hs hV R hR j u]
  calc
    _ ≤ (Real.exp M ^ N * (1 + R * Real.exp u) ^ N) *
        ‖paperKernelLogDerivative V j (R * Real.exp u)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = Real.exp M ^ N * ((1 + R * Real.exp u) ^ N *
        ‖paperKernelLogDerivative V j (R * Real.exp u)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb _ (mul_pos hR (Real.exp_pos u))) (by positivity)

/-- Localization in a fixed logarithmic interval preserves uniform radial decay of every derivative. -/
theorem localized_paperKernel_derivative_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ) (hM : 0 ≤ M)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ u : ℝ,
      (1 + R) ^ N * ‖iteratedDeriv j (fun v : ℝ => χ v * paperKernel V (R * Real.exp v)) u‖ ≤ C := by
  have hχb (i : ℕ) : ∃ D : ℝ, 0 < D ∧ ∀ u ∈ Set.Icc (-M) M, ‖iteratedDeriv i χ u‖ ≤ D := by
    obtain ⟨D, hD⟩ := isCompact_Icc.bddAbove_image
      (hχ.continuous_iteratedDeriv i (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))).norm.continuousOn
    exact ⟨|D| + 1, by positivity, fun u hu =>
      (hD (Set.mem_image_of_mem _ hu)).trans (by linarith [le_abs_self D])⟩
  choose D hD hDb using hχb
  have hkb (i : ℕ) := paperKernel_exp_local_derivative_bound V a b ha hs hV M hM N i
  choose C hC hCb using hkb
  let B := ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ)‖ * D i * C (j - i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (hD i).le) (hC (j - i)).le)
  refine ⟨B + 1, by positivity, ?_⟩
  intro R hR u
  by_cases hu : u ∈ Set.Icc (-M) M
  · have hprod := iteratedDeriv_mul (n := j) (x := u)
      (hχ.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
      ((paperKernel_exp_smooth V a b ha hs hV R hR).of_le
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
    change (1 + R) ^ N * ‖iteratedDeriv j (χ * (fun v : ℝ => paperKernel V (R * Real.exp v))) u‖ ≤ _
    rw [hprod]
    calc
      _ ≤ (1 + R) ^ N * ∑ i ∈ Finset.range (j + 1),
          ‖(j.choose i : ℂ) * iteratedDeriv i χ u *
            iteratedDeriv (j - i) (fun v : ℝ => paperKernel V (R * Real.exp v)) u‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ B := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hDi := (hD i).le
        have hCi := (hC (j - i)).le
        rw [norm_mul, norm_mul]
        calc
          _ = (‖(j.choose i : ℂ)‖ * ‖iteratedDeriv i χ u‖) *
              ((1 + R) ^ N * ‖iteratedDeriv (j - i) (fun v : ℝ => paperKernel V (R * Real.exp v)) u‖) := by ring
          _ ≤ (‖(j.choose i : ℂ)‖ * D i) * C (j - i) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hDb i u hu) (norm_nonneg _))
              (hCb (j - i) R hR u (abs_le.mpr hu)) (by positivity) (by positivity)
      _ ≤ B + 1 := by linarith
  · have hsprod : Function.support (fun v : ℝ => χ v * paperKernel V (R * Real.exp v)) ⊆ Set.Icc (-M) M := by
      intro v hv
      apply hχs
      intro hz
      exact hv (by simp only [hz, zero_mul])
    have hsd := (subset_tsupport (iteratedDeriv j (fun v : ℝ => χ v * paperKernel V (R * Real.exp v)))).trans
      ((tsupport_iteratedDeriv_subset _ j).trans (closure_minimal hsprod isClosed_Icc))
    have hz : iteratedDeriv j (fun v : ℝ => χ v * paperKernel V (R * Real.exp v)) u = 0 := by
      by_contra hn
      exact hu (hsd hn)
    rw [hz, norm_zero, mul_zero]
    positivity

/-- The Fourier transform of a localized reflected kernel decays uniformly in both parameters. -/
theorem localized_paperKernel_fourier_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ) (hM : 0 ≤ M)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (N J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ t : ℝ,
      (1 + R) ^ N * (1 + |t|) ^ J *
        ‖𝓕 (fun u : ℝ => χ u * paperKernel V (R * Real.exp u)) t‖ ≤ C := by
  let F := fun R u : ℝ => χ u * paperKernel V (R * Real.exp u)
  have hFs (R : ℝ) (_ : 0 < R) : Function.support (F R) ⊆ Set.Icc (-M) M := by
    intro u hu
    apply hχs
    intro hz
    exact hu (by simp only [F, hz, zero_mul])
  have hbase (j : ℕ) := compact_weighted_family_fourier_power_bound F (fun R => (1 + R) ^ N)
    (fun R hR => by positivity) (fun R hR => hχ.mul (paperKernel_exp_smooth V a b ha hs hV R hR))
    (Set.Icc (-M) M) isCompact_Icc hFs
    (localized_paperKernel_derivative_bound V a b ha hs hV χ hχ M hM hχs N) j
  obtain ⟨C₀, hC₀, hb₀⟩ := hbase 0
  obtain ⟨Cj, hCj, hbj⟩ := hbase J
  refine ⟨2 ^ J * (C₀ + Cj), by positivity, ?_⟩
  intro R hR t
  have hzero : (1 + R) ^ N * ‖𝓕 (F R) t‖ ≤ C₀ := by simpa only [pow_zero, one_mul] using hb₀ R hR t
  change (1 + R) ^ N * (1 + |t|) ^ J * ‖𝓕 (F R) t‖ ≤ _
  by_cases ht : |t| ≤ 1
  · have hp : (1 + |t|) ^ J ≤ (2 : ℝ) ^ J := by gcongr; linarith
    calc
      _ ≤ (1 + R) ^ N * 2 ^ J * ‖𝓕 (F R) t‖ := by gcongr
      _ = 2 ^ J * ((1 + R) ^ N * ‖𝓕 (F R) t‖) := by ring
      _ ≤ 2 ^ J * C₀ := mul_le_mul_of_nonneg_left hzero (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hp : (1 + |t|) ^ J ≤ (2 * |t|) ^ J := by gcongr; linarith
    calc
      _ ≤ (1 + R) ^ N * (2 * |t|) ^ J * ‖𝓕 (F R) t‖ := by gcongr
      _ = 2 ^ J * ((1 + R) ^ N * (|t| ^ J * ‖𝓕 (F R) t‖)) := by rw [mul_pow]; ring
      _ ≤ 2 ^ J * Cj := mul_le_mul_of_nonneg_left (hbj R hR t) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- A fixed smooth cutoff turns the reflected kernel into a uniformly rapidly decaying Fourier coefficient. -/
theorem localized_paperKernel_fourier_envelope
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ) (hM : 0 ≤ M)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (N J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∃ B : SchwartzMap ℝ ℂ,
      (∀ u : ℝ, χ u * paperKernel V (R * Real.exp u) = 𝓕⁻ (B : ℝ → ℂ) u) ∧
      Integrable (fun t : ℝ => (1 + |t|) ^ J * ‖B t‖) ∧
      (1 + R) ^ N * (∫ t : ℝ, (1 + |t|) ^ J * ‖B t‖) ≤ C ∧
      ∀ t : ℝ, (1 + R) ^ N * (1 + |t|) ^ J * ‖B t‖ ≤ C := by
  obtain ⟨C₁, hC₁, hb₁⟩ := localized_paperKernel_fourier_bound V a b ha hs hV χ hχ M hM hχs N J
  obtain ⟨C₂, hC₂, hb₂⟩ := localized_paperKernel_fourier_bound V a b ha hs hV χ hχ M hM hχs N (J + 2)
  let I : ℝ := ∫ t : ℝ, ((1 + |t|) ^ (2 : ℕ))⁻¹
  have hI : 0 ≤ I := integral_nonneg (fun _ => by positivity)
  refine ⟨C₁ + C₂ * (I + 1), by positivity, ?_⟩
  intro R hR
  have hc : HasCompactSupport (fun u : ℝ => χ u * paperKernel V (R * Real.exp u)) := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-M) M) isCompact_Icc
    intro u hu
    apply hχs
    intro hz
    exact hu (by simp only [hz, zero_mul])
  let S : SchwartzMap ℝ ℂ := hc.toSchwartzMap (hχ.mul (paperKernel_exp_smooth V a b ha hs hV R hR))
  refine ⟨𝓕 S, ?_⟩
  have he (u : ℝ) : χ u * paperKernel V (R * Real.exp u) = 𝓕⁻ (𝓕 (S : ℝ → ℂ)) u :=
    (S.integrable.fourierInv_fourier_eq (𝓕 S).integrable S.continuous.continuousAt).symm
  have hbound := weighted_fourier_L1_bound (𝓕 (S : ℝ → ℂ)) (𝓕 S).continuous ((1 + R) ^ N) C₂
    (by positivity) hC₂.le J (hb₂ R hR)
  refine ⟨he, hbound.1, ?_, ?_⟩
  · exact hbound.2.trans (by change C₂ * I ≤ _; nlinarith only [hC₁, hC₂, hI])
  · intro t
    exact (hb₁ R hR t).trans (by nlinarith only [hC₂, hI])

/-- The unitary logarithmic Fourier character. -/
def kernelLogPhase (t u : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t * u : ℝ) : ℂ) * Complex.I)

lemma kernelLogPhase_sum {ι : Type*} (s : Finset ι) (t : ℝ) (u : ι → ℝ) :
    kernelLogPhase t (∑ i ∈ s, u i) = ∏ i ∈ s, kernelLogPhase t (u i) := by
  unfold kernelLogPhase
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]

lemma kernelLogPhase_norm (t u : ℝ) : ‖kernelLogPhase t u‖ = 1 := by
  rw [kernelLogPhase, Complex.norm_exp]
  simp

/-- Coupled logarithmic factors separate into unitary characters with a uniform integrable Fourier envelope. -/
theorem paperKernel_log_separation
    {ι : Type*} [Fintype ι] (W : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i u, W i u ≠ 0 → |u| ≤ M i)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (N J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∃ B : SchwartzMap ℝ ℂ,
      (∀ y : ι → ℝ, (∏ i, W i (y i)) * paperKernel V (R * Real.exp (∑ i, slope i * y i)) =
        ∫ t : ℝ, (∏ i, W i (y i) * kernelLogPhase t (slope i * y i)) * B t) ∧
      Integrable (fun t : ℝ => (1 + |t|) ^ J * ‖B t‖) ∧
      (1 + R) ^ N * (∫ t : ℝ, (1 + |t|) ^ J * ‖B t‖) ≤ C ∧
      ∀ t : ℝ, (1 + R) ^ N * (1 + |t|) ^ J * ‖B t‖ ≤ C := by
  classical
  let L : ℝ := ∑ i, |slope i| * M i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i))
  let χ₀ : ContDiffBump (0 : ℝ) :=
    ⟨L + 1, L + 2, by linarith, by linarith⟩
  let χ : ℝ → ℂ := fun u => (χ₀ u : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp χ₀.contDiff
  have hχs : Function.support χ ⊆ Set.Icc (-(L + 2)) (L + 2) := by
    intro u hu
    have hu₀ : u ∈ Function.support χ₀ := by
      change χ₀ u ≠ 0
      intro hz
      exact hu (by simp only [χ, hz, Complex.ofReal_zero])
    rw [χ₀.support_eq] at hu₀
    have habs : |u| < L + 2 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hu₀
    exact abs_le.mp habs.le
  have hχone (u : ℝ) (hu : |u| ≤ L) : χ u = 1 := by
    have hu₀ : u ∈ Metric.closedBall (0 : ℝ) χ₀.rIn := by
      change dist u 0 ≤ L + 1
      rw [Real.dist_eq, sub_zero]
      linarith
    simp only [χ, χ₀.one_of_mem_closedBall hu₀, Complex.ofReal_one]
  obtain ⟨C, hC, hb⟩ := localized_paperKernel_fourier_envelope V a b ha hs hV
    χ hχ (L + 2) (by linarith) hχs N J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨B, hsep, hi, hI, hpt⟩ := hb R hR
  refine ⟨B, ?_, hi, hI, hpt⟩
  intro y
  have hprod (t : ℝ) : (∏ i, W i (y i) * kernelLogPhase t (slope i * y i)) =
      (∏ i, W i (y i)) * kernelLogPhase t (∑ i, slope i * y i) := by
    rw [Finset.prod_mul_distrib, kernelLogPhase_sum]
  simp_rw [hprod, mul_assoc]
  rw [integral_const_mul]
  by_cases hz : (∏ i, W i (y i)) = 0
  · simp only [hz, zero_mul]
  · congr 1
    have hwy (i : ι) : W i (y i) ≠ 0 := by
      exact (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hys : |∑ i, slope i * y i| ≤ L := by
      calc
        _ ≤ ∑ i, |slope i * y i| := by
          simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ) (f := fun i => slope i * y i)
        _ ≤ L := Finset.sum_le_sum (fun i _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hW i (y i) (hwy i)) (abs_nonneg _))
    have he := hsep (∑ i, slope i * y i)
    rw [hχone _ hys, one_mul, Real.fourierInv_eq'] at he
    simp only [smul_eq_mul] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    congr 1
    unfold kernelLogPhase
    congr 1
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring

/-- Cusp representatives and triangular coordinate changes are chosen once modulo three. -/
def fixedCuspIndex : FixedCuspSector → Fin 3 := exists_fixed_cusp_decomposition.choose

def fixedCuspTriangular : FixedCuspSector → SL(2, O) :=
  exists_fixed_cusp_decomposition.choose_spec.choose

def fixedCuspGamma : SL(2, O) → rationalExtension :=
  exists_fixed_cusp_decomposition.choose_spec.choose_spec.choose

lemma fixedCuspTriangular_properties (s : FixedCuspSector) :
    fixedCuspTriangular s 1 0 = 0 ∧ IsUnit (fixedCuspTriangular s 0 0) ∧
      IsUnit (fixedCuspTriangular s 1 1) :=
  exists_fixed_cusp_decomposition.choose_spec.choose_spec.choose_spec.1 s

lemma fixedCusp_factorization (M : SL(2, O)) :
    M = (fixedCuspGamma M : SL(2, O)) * cuspRepresentative (fixedCuspIndex (fixedCuspSector M)) *
      fixedCuspTriangular (fixedCuspSector M) :=
  exists_fixed_cusp_decomposition.choose_spec.choose_spec.choose_spec.2 M

lemma fixedCusp_lower_ne_zero (M : SL(2, O)) (hc : M 1 0 ≠ 0) :
    (integralComplexMatrix (fixedCuspGamma M : SL(2, O)) *
      integralComplexMatrix (cuspRepresentative (fixedCuspIndex (fixedCuspSector M)))) 1 0 ≠ 0 := by
  let g := integralComplexMatrix (fixedCuspGamma M : SL(2, O)) *
    integralComplexMatrix (cuspRepresentative (fixedCuspIndex (fixedCuspSector M)))
  let T := integralComplexMatrix (fixedCuspTriangular (fixedCuspSector M))
  have he : integralComplexMatrix M = g * T := by
    rw [fixedCusp_factorization M, map_mul, map_mul]
  have ht : T 1 0 = 0 := by
    change ringComplex (fixedCuspTriangular (fixedCuspSector M) 1 0) = 0
    rw [(fixedCuspTriangular_properties _).1, map_zero]
  exact (upperTriangular_right_cusp_ratio g T ht (by rw [← he]; exact ringComplex_ne_zero hc)).1

def fixedMatrixCusp (M : SL(2, O)) (hc : M 1 0 ≠ 0) : SourceCuspDatum :=
  ⟨fixedCuspGamma M, fixedCuspIndex (fixedCuspSector M), fixedCusp_lower_ne_zero M hc⟩

lemma fixedMatrixCusp_factorization (M : SL(2, O)) (hc : M 1 0 ≠ 0) :
    integralComplexMatrix M = (fixedMatrixCusp M hc).matrix *
      integralComplexMatrix (fixedCuspTriangular (fixedCuspSector M)) := by
  change integralComplexMatrix M =
    (integralComplexMatrix (fixedCuspGamma M : SL(2, O)) *
      integralComplexMatrix (cuspRepresentative (fixedCuspIndex (fixedCuspSector M)))) * _
  have he := congrArg integralComplexMatrix (fixedCusp_factorization M)
  simpa only [map_mul] using he

lemma fixedMatrixCusp_point (M : SL(2, O)) (hc : M 1 0 ≠ 0) :
    (fixedMatrixCusp M hc).point = ringComplex (M 0 0) / ringComplex (M 1 0) := by
  let T := integralComplexMatrix (fixedCuspTriangular (fixedCuspSector M))
  have ht : T 1 0 = 0 := by
    change ringComplex (fixedCuspTriangular (fixedCuspSector M) 1 0) = 0
    rw [(fixedCuspTriangular_properties _).1, map_zero]
  have he := fixedMatrixCusp_factorization M hc
  exact (upperTriangular_right_cusp_ratio (fixedMatrixCusp M hc).matrix T ht
    (by rw [← he]; exact ringComplex_ne_zero hc)).2.symm.trans (by rw [← he]; rfl)

/-- Integral units leave the radial height unchanged under the fixed triangular coordinate change. -/
lemma fixedMatrixCusp_heightScale (M : SL(2, O)) (hc : M 1 0 ≠ 0) :
    (fixedMatrixCusp M hc).heightScale = ‖ringComplex (M 1 0)‖ ^ 2 := by
  let T := fixedCuspTriangular (fixedCuspSector M)
  have hT : T 1 0 = 0 := (fixedCuspTriangular_properties _).1
  have hunit : IsUnit (T 0 0) := (fixedCuspTriangular_properties _).2.1
  have hn : ‖ringComplex (T 0 0)‖ = 1 := by
    rw [← hunit.unit_spec]
    exact norm_ringComplex_unit hunit.unit
  have he := congrArg (fun A : SL(2, ℂ) => A 1 0) (fixedMatrixCusp_factorization M hc)
  have hcol : ringComplex (M 1 0) = (fixedMatrixCusp M hc).matrix 1 0 * ringComplex (T 0 0) := by
    change ringComplex (M 1 0) = ∑ k : Fin 2,
      (fixedMatrixCusp M hc).matrix 1 k * ringComplex (T k 0) at he
    simpa only [Fin.sum_univ_two, hT, map_zero, mul_zero, add_zero] using he
  rw [SourceCuspDatum.heightScale, hcol, norm_mul, hn, mul_one]

lemma upperTriangular_right_dualPoint (g T : SL(2, ℂ)) (hT : T 1 0 = 0)
    (hc : (g * T) 1 0 ≠ 0) :
    -g 1 1 / g 1 0 = (T 0 0) ^ 2 * (-(g * T) 1 1 / (g * T) 1 0) + T 0 0 * T 0 1 := by
  have hcol : (g * T) 1 0 = g 1 0 * T 0 0 := by
    change (∑ k : Fin 2, g 1 k * T k 0) = _
    rw [Fin.sum_univ_two, hT, mul_zero, add_zero]
  have hrow : (g * T) 1 1 = g 1 0 * T 0 1 + g 1 1 * T 1 1 := by
    change (∑ k : Fin 2, g 1 k * T k 1) = _
    rw [Fin.sum_univ_two]
  have ht0 : T 0 0 ≠ 0 := (mul_ne_zero_iff.mp (hcol ▸ hc)).2
  have hdet : T 0 0 * T 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hT, mul_zero, sub_zero] using T.property
  have hg : (g * T) 1 0 / T 0 0 = g 1 0 := by rw [hcol, mul_div_cancel_right₀ _ ht0]
  have hd : (g * T) 1 1 * T 0 0 - (g * T) 1 0 * T 0 1 = g 1 1 := by
    rw [hrow, hcol]
    calc
      _ = g 1 1 * (T 0 0 * T 1 1) := by ring
      _ = _ := by rw [hdet, mul_one]
  calc
    _ = -((g * T) 1 1 * T 0 0 - (g * T) 1 0 * T 0 1) /
        ((g * T) 1 0 / T 0 0) := by rw [hg, hd]
    _ = _ := by field_simp [hc, ht0]; ring

/-- The dual coordinate varies by a unit rotation and a translation fixed by the matrix modulo three. -/
lemma fixedMatrixCusp_dualPoint (M : SL(2, O)) (hc : M 1 0 ≠ 0) :
    (fixedMatrixCusp M hc).dualPoint =
      ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) ^ 2 *
        (-ringComplex (M 1 1) / ringComplex (M 1 0)) +
      ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0 *
        fixedCuspTriangular (fixedCuspSector M) 0 1) := by
  let T := integralComplexMatrix (fixedCuspTriangular (fixedCuspSector M))
  have ht : T 1 0 = 0 := by
    change ringComplex (fixedCuspTriangular (fixedCuspSector M) 1 0) = 0
    rw [(fixedCuspTriangular_properties _).1, map_zero]
  have he := fixedMatrixCusp_factorization M hc
  have hd := upperTriangular_right_dualPoint (fixedMatrixCusp M hc).matrix T ht
    (by rw [← he]; exact ringComplex_ne_zero hc)
  rw [← he] at hd
  change (fixedMatrixCusp M hc).dualPoint =
    ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) ^ 2 *
      (-ringComplex (M 1 1) / ringComplex (M 1 0)) +
    ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) *
      ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 1) at hd
  rw [map_mul]
  exact hd

/-- Reflection is independent of the chosen coordinates at each finite cusp. -/
theorem completedT_finite_cusp_reflection (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum)
    (hd : ∀ i, (d i).point = thetaFourierTranslation (9 * c) i)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W X =
      thetaDerivativeScalar⁻¹ * ∑ i,
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) i *
        ((d i).smoothingMultiplier * ∑' h : O, sourceCuspRadialCoefficient (d i).index (d i).dualPoint h *
          paperKernel (Vstar W) ((d i).smoothingScale X * sourceCuspRadialLength h)) := by
  rw [completedT_finite_smoothed_reflection c hc Ψ W a b ha hs hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← (d i).smoothed_reflection (Vstar W) a b ha (Vstar_support W a b hs)
      (Vstar_contDiff W a b ha hs hW) X hX,
    ← (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothed_reflection
      (Vstar W) a b ha (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) X hX,
    hd i, finiteTwistCusp_point]

/-- Fixed cusp coordinates retain the exact unit, ramified, squarefree, and cube decomposition. -/
theorem completedT_finite_cusp_full_reflection (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum)
    (hd : ∀ i, (d i).point = thetaFourierTranslation (9 * c) i)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W X =
      thetaDerivativeScalar⁻¹ * ∑ i,
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) i *
        ((d i).smoothingMultiplier * ∑' p : ThetaFullIndex,
          sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p) *
          paperKernel (Vstar W) ((d i).smoothingScale X *
            (‖ringComplex lambda‖ ^ (2 * p.2.1) * completedMellinLength p.2.2))) := by
  rw [completedT_finite_cusp_reflection c hc Ψ d hd W a b ha hs hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [sourceCuspRadial_tsum_full_index]
  simp only [thetaFullFrequency_radialLength]

/-- The fixed cusp array includes the bounded translation phase. -/
def fixedCuspRadialArray (s : FixedCuspSector) (h : O) : ℂ :=
  sourceCuspRadialBaseCoefficient (fixedCuspIndex s) h *
    tracePhase (-cuspFrequency h *
      (ringComplex (fixedCuspTriangular s 0 0 * fixedCuspTriangular s 0 1) /
        (sourceCuspScale (fixedCuspIndex s) : ℂ)))

lemma fixedCuspRadialArray_norm (s : FixedCuspSector) (h : O) :
    ‖fixedCuspRadialArray s h‖ = ‖sourceCuspRadialBaseCoefficient (fixedCuspIndex s) h‖ := by
  rw [fixedCuspRadialArray, norm_mul, tracePhase_norm, mul_one]

/-- The moving part of a cusp coefficient is an inverse-denominator additive phase. -/
lemma fixedMatrixCusp_radialCoefficient (M : SL(2, O)) (hc : M 1 0 ≠ 0) (h : O) :
    sourceCuspRadialCoefficient (fixedMatrixCusp M hc).index (fixedMatrixCusp M hc).dualPoint h =
      fixedCuspRadialArray (fixedCuspSector M) h *
        tracePhase (cuspFrequency h * ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) ^ 2 *
          ringComplex (M 1 1) / ((sourceCuspScale (fixedCuspIndex (fixedCuspSector M)) : ℂ) *
            ringComplex (M 1 0))) := by
  rw [sourceCuspRadialCoefficient, fixedMatrixCusp_dualPoint]
  rw [show (fixedMatrixCusp M hc).index = fixedCuspIndex (fixedCuspSector M) from rfl]
  have he : -cuspFrequency h *
      ((ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) ^ 2 *
          (-ringComplex (M 1 1) / ringComplex (M 1 0)) +
        ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0 *
          fixedCuspTriangular (fixedCuspSector M) 0 1)) /
        (sourceCuspScale (fixedCuspIndex (fixedCuspSector M)) : ℂ)) =
      -cuspFrequency h *
        (ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0 *
          fixedCuspTriangular (fixedCuspSector M) 0 1) /
          (sourceCuspScale (fixedCuspIndex (fixedCuspSector M)) : ℂ)) +
      cuspFrequency h * ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) ^ 2 *
        ringComplex (M 1 1) / ((sourceCuspScale (fixedCuspIndex (fixedCuspSector M)) : ℂ) *
          ringComplex (M 1 0)) := by ring
  rw [he, AddChar.map_add_eq_mul]
  simp only [fixedCuspRadialArray, mul_assoc]

lemma fixedMatrixCusp_lower (M : SL(2, O)) (hc : M 1 0 ≠ 0) :
    (fixedMatrixCusp M hc).matrix 1 0 = ringComplex (M 1 0) /
      ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) := by
  have hu := (fixedCuspTriangular_properties (fixedCuspSector M)).2.1
  have ht0 : ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) ≠ 0 :=
    ringComplex_ne_zero hu.ne_zero
  apply (eq_div_iff ht0).mpr
  have he := congrArg (fun A : SL(2, ℂ) => A 1 0) (fixedMatrixCusp_factorization M hc)
  change ringComplex (M 1 0) = ∑ k : Fin 2, (fixedMatrixCusp M hc).matrix 1 k *
    ringComplex (fixedCuspTriangular (fixedCuspSector M) k 0) at he
  simpa only [Fin.sum_univ_two, (fixedCuspTriangular_properties _).1, map_zero, mul_zero, add_zero] using he.symm

/-- The radial reflection scale is determined by the denominator norm and a fixed cusp class. -/
lemma fixedMatrixCusp_smoothingScale (M : SL(2, O)) (hc : M 1 0 ≠ 0) (X : ℝ) :
    (fixedMatrixCusp M hc).smoothingScale X =
      27 * (sourceCuspRadialScale 0) ^ 2 *
        (sourceCuspRadialScale (fixedCuspIndex (fixedCuspSector M))) ^ 2 * X /
        ‖ringComplex (M 1 0)‖ ^ 4 := by
  rw [SourceCuspDatum.smoothingScale, fixedMatrixCusp_heightScale, ← pow_mul]
  rfl

/-- The reflected prefactor separates the cubic character and a unit-modulus denominator phase. -/
lemma fixedMatrixCusp_smoothingMultiplier (M : SL(2, O)) (hc : M 1 0 ≠ 0) :
    (fixedMatrixCusp M hc).smoothingMultiplier =
      -star (extendedComplexCharacter (fixedCuspGamma M)) *
        ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) ^ 2 *
        (star (ringComplex (M 1 0)) / ringComplex (M 1 0)) *
        (sourceCuspScale (fixedCuspIndex (fixedCuspSector M)) : ℂ) ^ 2 := by
  have hc0 := ringComplex_ne_zero hc
  have ht0 := ringComplex_ne_zero (fixedCuspTriangular_properties (fixedCuspSector M)).2.1.ne_zero
  have hn : star (ringComplex (M 1 0)) * ringComplex (M 1 0) =
      (‖ringComplex (M 1 0)‖ : ℂ) ^ 2 := by
    simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' (ringComplex (M 1 0))
  rw [SourceCuspDatum.smoothingMultiplier, SourceCuspDatum.multiplier,
    fixedMatrixCusp_lower, fixedMatrixCusp_heightScale, sourceCuspRadialScale_ratio]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← hn]
  change -star (extendedComplexCharacter (fixedCuspGamma M)) /
      (ringComplex (M 1 0) / ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0)) ^ 2 *
      ((star (ringComplex (M 1 0)) * ringComplex (M 1 0)) *
        (sourceCuspScale (fixedCuspIndex (fixedCuspSector M)) : ℂ) ^ 2) = _
  field_simp

lemma sourceCusp_translation_phase_congr (j : Fin 3) (a h k : O) (hmod : (9 : O) ∣ h - k) :
    tracePhase (-cuspFrequency h * (ringComplex a / (sourceCuspScale j : ℂ))) =
      tracePhase (-cuspFrequency k * (ringComplex a / (sourceCuspScale j : ℂ))) := by
  fin_cases j
  · change tracePhase (-cuspFrequency h * (ringComplex a / (1 : ℂ))) =
      tracePhase (-cuspFrequency k * (ringComplex a / (1 : ℂ)))
    simp only [div_one]
    have he (x : O) : -cuspFrequency x * ringComplex a =
        cuspFrequency x * (ringComplex (-3 * a) / 3) := by
      simp only [map_mul, map_neg, map_ofNat]
      ring
    rw [he h, he k]
    exact cuspFrequency_div_three_phase_congr (-3 * a) h k hmod
  · change tracePhase (-cuspFrequency h * (ringComplex a / 3)) =
      tracePhase (-cuspFrequency k * (ringComplex a / 3))
    simpa only [map_neg, neg_div, mul_neg, neg_mul] using cuspFrequency_div_three_phase_congr (-a) h k hmod
  · change tracePhase (-cuspFrequency h * (ringComplex a / 3)) =
      tracePhase (-cuspFrequency k * (ringComplex a / 3))
    simpa only [map_neg, neg_div, mul_neg, neg_mul] using cuspFrequency_div_three_phase_congr (-a) h k hmod

/-- The fixed translation phase requires only the frequency residue modulo nine. -/
lemma fixedCusp_translation_phase_congr (s : FixedCuspSector) (h k : O) (hmod : (9 : O) ∣ h - k) :
    tracePhase (-cuspFrequency h *
      (ringComplex (fixedCuspTriangular s 0 0 * fixedCuspTriangular s 0 1) /
        (sourceCuspScale (fixedCuspIndex s) : ℂ))) =
    tracePhase (-cuspFrequency k *
      (ringComplex (fixedCuspTriangular s 0 0 * fixedCuspTriangular s 0 1) /
        (sourceCuspScale (fixedCuspIndex s) : ℂ))) :=
  sourceCusp_translation_phase_congr _ _ h k hmod

lemma sourceCusp_full_kernel_norm_summable (j : Fin 3) (z : ℂ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (R : ℝ) (hR : 0 < R) :
    Summable (fun p : ThetaFullIndex => ‖sourceCuspRadialCoefficient j z (thetaFullFrequency p) *
      paperKernel V (R * sourceCuspRadialLength (thetaFullFrequency p))‖) := by
  have hc : Summable (fun h : O => ‖sourceCuspRadialCoefficient j z h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [neg_div] using sourceCuspRadialCoefficient_weighted_summable j z
  exact (paperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient j z) hc V a b ha hs hV R hR).comp_injective thetaFullFrequency_injective

/-- Fourier coefficients of a multiplicative character at unit frequencies are Gauss sums. -/
lemma finiteAdditiveFourierCoeff_mulChar_unit {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (χ : MulChar F ℂ) (h : Fˣ) :
    finiteAdditiveFourierCoeff ψ χ (h : F) =
      (Fintype.card F : ℂ)⁻¹ * χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by
  have he : (∑ t : F, χ t * ψ (-(h * t))) = χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by
    simpa only [gaussSum, AddChar.mulShift_apply, neg_one_mul, mul_neg] using
      gaussSum_mulShift_eq χ (ψ.mulShift (-1)) h
  rw [finiteAdditiveFourierCoeff]
  simp only [neg_mul] at *
  rw [he]
  ring

lemma finiteGauss_sum_units {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
  classical
  calc
    gaussSum χ ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, χ x * ψ x := by
      simpa only [gaussSum, MulChar.map_zero, zero_mul, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset F) (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))).symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x * ψ x := by
      apply Finset.sum_subtype
      intro x
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    _ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) :=
      (Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)).symm

/-- The local reflected row retains the zero output and the cubic automorphy factor. -/
def finiteReflectionGauss {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (x : F) : ℂ :=
  ∑ h : Fˣ, finiteAdditiveFourierCoeff ψ (χ ^ j : MulChar F ℂ) (h : F) * ((χ⁻¹) ^ 2) h *
    ψ (x * ((h⁻¹ : Fˣ) : F))

/-- Local reflection is exactly a product of two Gauss sums, including exceptional powers. -/
theorem finiteReflectionGauss_product {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (x : F) :
    finiteReflectionGauss χ ψ j x = (Fintype.card F : ℂ)⁻¹ *
      gaussSum (χ ^ j) (ψ.mulShift (-1)) * gaussSum (χ ^ (j + 2)) (ψ.mulShift x) := by
  classical
  have hinv : (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) * ψ (x * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ (j + 2)) (ψ.mulShift x) := by
    calc
      _ = ∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) (h⁻¹)) * ψ (x * (h : F)) := by
        apply Fintype.sum_equiv (Equiv.inv Fˣ)
        intro h
        simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
      _ = ∑ h : Fˣ, (χ ^ (j + 2)) h * ψ (x * (h : F)) := by
        apply Finset.sum_congr rfl
        intro h hh
        have he : (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2)⁻¹) = χ ^ (j + 2) := by group
        rw [← MulChar.inv_apply', he]
      _ = _ := by rw [finiteGauss_sum_units]; rfl
  rw [finiteReflectionGauss]
  simp_rw [finiteAdditiveFourierCoeff_mulChar_unit]
  calc
    _ = ((Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1))) *
        ∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) * ψ (x * ((h⁻¹ : Fˣ) : F)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [MulChar.mul_apply]
      ring
    _ = _ := by rw [hinv]

lemma finiteGauss_mulShift_all {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (x : F) :
    gaussSum χ (ψ.mulShift x) = χ⁻¹ x * gaussSum χ ψ := by
  by_cases hx : x = 0
  · subst x
    have he : ψ.mulShift (0 : F) = 1 := by ext t; simp
    rw [he, gaussSum_one_right hχ, MulChar.map_zero, zero_mul]
  · simpa only [Units.val_mk0] using gaussSum_mulShift_eq χ ψ (Units.mk0 x hx)

/-- A sextic row becomes its quadratic third power after the reflected cubic multiplier. -/
theorem finiteReflectionGauss_sextic {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ^ 6 = 1) (hχ3 : χ ^ 3 ≠ 1) (x : F) :
    finiteReflectionGauss χ ψ 1 x =
      ((Fintype.card F : ℂ)⁻¹ * gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ) * (χ ^ 3) x := by
  have hinv : (χ ^ 3)⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_add] using hχ
  rw [finiteReflectionGauss_product, pow_one, show 1 + 2 = 3 from rfl,
    finiteGauss_mulShift_all _ _ hχ3, hinv]
  ring

/-- The exceptional fourth-power row has a distinct zero-frequency contribution. -/
theorem finiteReflectionGauss_fourth {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ^ 6 = 1) (hψ : ψ.IsPrimitive) (x : F) :
    finiteReflectionGauss χ ψ 4 x =
      ((Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1))) *
        (if x = 0 then (Nat.card Fˣ : ℂ) else -1) := by
  rw [finiteReflectionGauss_product, show 4 + 2 = 6 from rfl, hχ]
  by_cases hx : x = 0
  · subst x
    have he : ψ.mulShift (0 : F) = 1 := by ext t; simp
    rw [he, gaussSum_one_one, if_pos rfl]
  · rw [gaussSum_one_left (hψ hx), if_neg hx]

lemma finiteReflectionGauss_phase_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (j : ℕ)
    (hj : χ ^ j ≠ 1) (hj2 : χ ^ (j + 2) ≠ 1) :
    ‖(Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) * gaussSum (χ ^ (j + 2)) ψ‖ = 1 := by
  have hneg : (ψ.mulShift (-1)).IsPrimitive := by
    intro a ha
    rw [AddChar.mulShift_mulShift]
    exact hψ (mul_ne_zero (neg_ne_zero.mpr one_ne_zero) ha)
  have hnorm (χ₀ : MulChar F ℂ) (ψ₀ : AddChar F ℂ) (hc : χ₀ ≠ 1) (hp : ψ₀.IsPrimitive) :
      ‖gaussSum χ₀ ψ₀‖ ^ 2 = (Fintype.card F : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, ArithmeticEffectivityTheory.normSq_gaussSum_eq_card hc hp]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow, one_pow,
    hnorm _ _ hj hneg, hnorm _ _ hj2 hψ]
  field_simp

/-- The reflected sextic row is exactly a unit phase times the actual quadratic residue character. -/
theorem finiteReflectionGauss_actual_quadratic
    (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (hchar : ringChar (O ⧸ P) ≠ 2) (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ x : O ⧸ P,
      finiteReflectionGauss (complexSexticChar P hg) ψ 1 x = ε * complexQuadraticChar P x := by
  have hp := complexSexticChar_powers P hg
  have hq : complexSexticChar P hg ^ 3 ≠ 1 := by
    rw [hp.2.1]
    exact complexQuadraticChar_ne_one P hchar
  refine ⟨(Fintype.card (O ⧸ P) : ℂ)⁻¹ * gaussSum (complexSexticChar P hg) (ψ.mulShift (-1)) *
    gaussSum (complexSexticChar P hg ^ 3) ψ, ?_, ?_⟩
  · simpa only [pow_one, show 1 + 2 = 3 from rfl] using
      finiteReflectionGauss_phase_norm (complexSexticChar P hg) ψ hψ 1
        (by simpa only [pow_one] using complexSexticChar_ne_one P hg) hq
  · intro x
    rw [finiteReflectionGauss_sextic _ _ hp.2.2 hq, hp.2.1]

/-- The exceptional row separates into a divisibility term and its exact constant correction. -/
theorem finiteReflectionGauss_fourth_indicator {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ^ 6 = 1) (hψ : ψ.IsPrimitive) (x : F) :
    finiteReflectionGauss χ ψ 4 x =
      ((Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1))) *
        ((if x = 0 then (Fintype.card F : ℂ) else 0) - 1) := by
  classical
  have hcard : (Nat.card Fˣ : ℂ) = (Fintype.card F : ℂ) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units,
      Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos), Nat.cast_one]
  rw [finiteReflectionGauss_fourth χ ψ hχ hψ]
  by_cases hx : x = 0
  · simp only [if_pos hx, hcard]
  · simp only [if_neg hx, zero_sub]

/-- Independent local reflected rows factor without discarding their phases or exceptional terms. -/
theorem finiteReflectionGauss_product_family
    {ι : Type*} [Fintype ι] {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (ψ : ∀ i, AddChar (F i) ℂ) (j : ι → ℕ) (x : ∀ i, F i) :
    (∑ h : ∀ i, (F i)ˣ, ∏ i,
      finiteAdditiveFourierCoeff (ψ i) (χ i ^ j i : MulChar (F i) ℂ) (h i : F i) * ((χ i)⁻¹ ^ 2) (h i) *
        ψ i (x i * (((h i)⁻¹ : (F i)ˣ) : F i))) =
      ∏ i, ((Fintype.card (F i) : ℂ)⁻¹ * gaussSum (χ i ^ j i) ((ψ i).mulShift (-1)) *
        gaussSum (χ i ^ (j i + 2)) ((ψ i).mulShift (x i))) := by
  classical
  let f := fun (i : ι) (h : (F i)ˣ) =>
    finiteAdditiveFourierCoeff (ψ i) (χ i ^ j i : MulChar (F i) ℂ) (h : F i) *
      ((χ i)⁻¹ ^ 2) h * ψ i (x i * ((h⁻¹ : (F i)ˣ) : F i))
  change (∑ h : ∀ i, (F i)ˣ, ∏ i, f i (h i)) = _
  rw [← Fintype.prod_sum f]
  apply Finset.prod_congr rfl
  intro i hi
  exact finiteReflectionGauss_product (χ i) (ψ i) (j i) (x i)

/-- At good primes the full product reflection is a unit phase times the quadratic row. -/
theorem finiteReflectionGauss_actual_quadratic_family
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (O ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ x : ∀ i, O ⧸ P i,
      (∑ h : ∀ i, (O ⧸ P i)ˣ, ∏ i,
        finiteAdditiveFourierCoeff (ψ i) (complexSexticChar (P i) (hg i)) (h i : O ⧸ P i) *
          ((complexSexticChar (P i) (hg i))⁻¹ ^ 2) (h i) *
          ψ i (x i * (((h i)⁻¹ : (O ⧸ P i)ˣ) : O ⧸ P i))) =
      ε * ∏ i, complexQuadraticChar (P i) (x i) := by
  classical
  choose ε hε he using fun i => finiteReflectionGauss_actual_quadratic (P i) (hg i) (hchar i) (ψ i) (hψ i)
  refine ⟨∏ i, ε i, by simp only [norm_prod, hε, Finset.prod_const_one], ?_⟩
  intro x
  let f := fun (i : ι) (h : (O ⧸ P i)ˣ) =>
    finiteAdditiveFourierCoeff (ψ i) (complexSexticChar (P i) (hg i)) (h : O ⧸ P i) *
      ((complexSexticChar (P i) (hg i))⁻¹ ^ 2) h *
      ψ i (x i * ((h⁻¹ : (O ⧸ P i)ˣ) : O ⧸ P i))
  change (∑ h : ∀ i, (O ⧸ P i)ˣ, ∏ i, f i (h i)) = _
  rw [← Fintype.prod_sum f, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [finiteReflectionGauss, pow_one, f] using he i (x i)

/-- Reciprocity separates a fixed denominator factor from a moving primary factor. -/
lemma cuspSymbol_principal_factor (a c r : O)
    (ha : lambda ^ 2 ∣ a - 1) (hr : lambda ^ 2 ∣ r - 1) :
    symbol (c * r) a = symbol c a * symbol a r := by
  rw [symbol_mul_numerator, symbol_reciprocity r a hr ha]

/-- The determinant relation separates the ramified cusp multiplier without division by symbols. -/
lemma cuspSymbol_ramified (a b c d u : O)
    (hdet : a * d - b * (u * c) = 1)
    (ha : lambda ^ 2 ∣ a - 1) (hA : lambda ^ 2 ∣ (a - u * b) - 1) :
    symbol (u * c - u * d) (a - u * b) = symbol (-u) (a - u * b) * symbol c a := by
  have h1 : symbol a (a - u * b) * symbol (u * c - u * d) (a - u * b) =
      symbol (-u) (a - u * b) := by
    rw [← symbol_mul_numerator]
    apply symbol_congr
    refine ⟨u * c, ?_⟩
    linear_combination -u * hdet
  have h2 : symbol (a - u * b) a * symbol c a = 1 := by
    rw [← symbol_mul_numerator, ← symbol_one_numerator a ha]
    apply symbol_congr
    refine ⟨c - d, ?_⟩
    linear_combination hdet
  rw [symbol_reciprocity a (a - u * b) ha hA] at h1
  calc
    _ = (symbol (a - u * b) a * symbol c a) * symbol (u * c - u * d) (a - u * b) := by rw [h2, one_mul]
    _ = (symbol (a - u * b) a * symbol (u * c - u * d) (a - u * b)) * symbol c a := by ring
    _ = _ := by rw [h1]

lemma cuspSymbol_ramified_factor (a b c r d u : O)
    (hdet : a * d - b * (u * (c * r)) = 1)
    (ha : lambda ^ 2 ∣ a - 1) (hA : lambda ^ 2 ∣ (a - u * b) - 1)
    (hr : lambda ^ 2 ∣ r - 1) :
    symbol (u * (c * r) - u * d) (a - u * b) =
      (symbol (-u) (a - u * b) * symbol c a) * symbol a r := by
  rw [cuspSymbol_ramified a b (c * r) d u hdet ha hA, cuspSymbol_principal_factor a c r ha hr]
  ring

/-- In the Weyl chart, denominator congruence supplies the exact global cubic factor. -/
lemma cuspSymbol_weyl (a b c d : O) (hdet : a * d - b * c = 1)
    (hb : lambda ^ 2 ∣ (-b) - 1) (hc : lambda ^ 2 ∣ c - 1) (h9 : (9 : O) ∣ a * d) :
    symbol (-d) (-b) = symbol a c := by
  have hp : lambda ^ 2 ∣ (-b) * c - 1 := primary_mul (-b) c hb hc
  have hprod : symbol d (-b) * symbol d c = 1 := by
    rw [← symbol_mul_denominator]
    have hnine : (9 : O) ∣ (-b) * c - 1 := by
      convert dvd_neg.mpr h9 using 1
      linear_combination hdet
    have hd : d ∣ (-b) * c - 1 := by
      refine ⟨-a, ?_⟩
      linear_combination hdet
    rw [symbol_denominator_congr d ((-b) * c) 1 hp (by simp) hnine hd, symbol_one]
  have hother : symbol a c * symbol d c = 1 := by
    rw [← symbol_mul_numerator, ← symbol_one_numerator c hc]
    apply symbol_congr
    refine ⟨b, ?_⟩
    linear_combination hdet
  rw [symbol_neg_numerator _ _ hb]
  calc
    symbol d (-b) = symbol d (-b) * (symbol a c * symbol d c) := by rw [hother, mul_one]
    _ = (symbol d (-b) * symbol d c) * symbol a c := by ring
    _ = _ := by rw [hprod, one_mul]

lemma cuspSymbol_weyl_factor (a b c r d : O) (hdet : a * d - b * (c * r) = 1)
    (hb : lambda ^ 2 ∣ (-b) - 1) (hc : lambda ^ 2 ∣ c * r - 1) (h9 : (9 : O) ∣ a * d) :
    symbol (-d) (-b) = symbol a c * symbol a r := by
  rw [cuspSymbol_weyl a b (c * r) d hdet hb hc h9, symbol_mul_denominator]

/-- The ramified fixed factor is constant on a fixed matrix residue class. -/
lemma cuspSymbol_ramified_fixed_congr (N c u a a₀ b b₀ : O)
    (h9 : (9 : O) ∣ N) (hc : c ∣ N) (hu : u ∣ N)
    (ha : lambda ^ 2 ∣ a - 1) (ha₀ : lambda ^ 2 ∣ a₀ - 1)
    (hA : lambda ^ 2 ∣ a - u * b - 1) (hA₀ : lambda ^ 2 ∣ a₀ - u * b₀ - 1)
    (hNa : N ∣ a - a₀) (hNb : N ∣ b - b₀) :
    symbol (-u) (a - u * b) * symbol c a =
      symbol (-u) (a₀ - u * b₀) * symbol c a₀ := by
  have hdiff : N ∣ (a - u * b) - (a₀ - u * b₀) := by
    convert dvd_sub hNa (dvd_mul_of_dvd_right hNb u) using 1
    ring
  rw [symbol_denominator_congr (-u) (a - u * b) (a₀ - u * b₀) hA hA₀
      (h9.trans hdiff) (neg_dvd.mpr (hu.trans hdiff)),
    symbol_denominator_congr c a a₀ ha ha₀ (h9.trans hNa) (hc.trans hNa)]

lemma cuspSymbol_weyl_fixed_congr (N c a a₀ : O) (hc : c ∣ N) (hNa : N ∣ a - a₀) :
    symbol a c = symbol a₀ c := symbol_congr (hc.trans hNa)

lemma norm_cuspSymbol_of_coprime (a c : O) (hc : lambda ^ 2 ∣ c - 1) (hcop : IsCoprime a c) :
    ‖ringComplex (symbol a c)‖ = 1 := by
  have hcube : ringComplex (symbol a c) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime a c hc hcop, map_one]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
  simpa only [norm_pow, norm_one] using congrArg norm hcube

lemma cuspSymbol_principal_fixed_norm (a b c r d : O)
    (hdet : a * d - b * (c * r) = 1) (ha : lambda ^ 2 ∣ a - 1) :
    ‖ringComplex (symbol c a)‖ = 1 := by
  apply norm_cuspSymbol_of_coprime c a ha
  refine ⟨-b * r, d, ?_⟩
  linear_combination hdet

lemma cuspSymbol_weyl_fixed_norm (a b c r d : O)
    (hdet : a * d - b * (c * r) = 1) (hc : lambda ^ 2 ∣ c - 1) :
    ‖ringComplex (symbol a c)‖ = 1 := by
  apply norm_cuspSymbol_of_coprime a c hc
  refine ⟨d, -b * r, ?_⟩
  linear_combination hdet

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
