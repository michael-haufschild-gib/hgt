import GaloisForLFunctions.RHTower.ChiCubicExteriorMellinEnergy
import Mathlib.Analysis.Fourier.Convolution

/-!
# Actual Mellin trace control from common compact log support

A fixed smooth compact logarithmic cutoff is one on the support of every
actual localized Mellin profile. Its Fourier transform reproduces each test
by literal convolution. Submultiplicativity of the full planar weight and
weighted Cauchy–Schwarz turn the proved energy into uniform pointwise decay.
All polynomial-weight integrability is derived before the integral estimates.

The actual selected family has a uniform weighted trace for every order
between one and three halves. A second theorem controls differences of any
two localized profiles, including different Mellin parameters, by the energy
of their exact difference. This is the input needed for shrinking arithmetic
axis bands; full moving-test signed transfer remains open.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ENNReal ContDiff
namespace RHTower.BAGTrace
private abbrev E := HTGeometry.QuadrantLogSpace

private theorem fourier_twice (f : SchwartzMap E ℂ) (x : E) :
    (𝓕 (𝓕 f)) x=f (-x) := by
  have hh := congrArg (fun g : SchwartzMap E ℂ => g (-x))
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap E ℂ) f)
  change (𝓕 (𝓕 f)) (-(-x))=f (-x) at hh
  simpa only [neg_neg] using hh


private theorem compact_fourier_reproduces (b f : SchwartzMap E ℂ)
    (hb : ∀x : E, b x*f x=f x) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 b) (𝓕 f)=𝓕 f := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap E ℂ)).injective
  ext x
  simp only [FourierTransform.fourierEquiv_apply]
  rw [SchwartzMap.fourier_convolution,SchwartzMap.pairing_apply_apply]
  simp only [ContinuousLinearMap.mul_apply',fourier_twice]
  exact hb (-x)

private def weight (x : E) : ℝ := 1+|x 0|+|x 1|
private theorem weight_pos (x : E) : 0<weight x := by dsimp only [weight]; positivity
private theorem weight_ge_one (x : E) : 1 ≤ weight x := by dsimp only [weight]; linarith [abs_nonneg (x 0),abs_nonneg (x 1)]
private theorem weight_submultiplicative (x y : E) :
    weight x ≤ weight (x-y)*weight y := by
  have h0 : |x 0| ≤ |(x-y) 0|+|y 0| := by
    have hh := abs_add_le ((x-y) 0) (y 0)
    simpa only [PiLp.sub_apply,sub_add_cancel] using hh
  have h1 : |x 1| ≤ |(x-y) 1|+|y 1| := by
    have hh := abs_add_le ((x-y) 1) (y 1)
    simpa only [PiLp.sub_apply,sub_add_cancel] using hh
  dsimp only [weight]
  nlinarith [abs_nonneg ((x-y) 0),abs_nonneg ((x-y) 1),abs_nonneg (y 0),abs_nonneg (y 1),
    mul_nonneg (abs_nonneg ((x-y) 0)) (abs_nonneg (y 0)),
    mul_nonneg (abs_nonneg ((x-y) 0)) (abs_nonneg (y 1)),
    mul_nonneg (abs_nonneg ((x-y) 1)) (abs_nonneg (y 0)),
    mul_nonneg (abs_nonneg ((x-y) 1)) (abs_nonneg (y 1))]

private theorem weight_rpow_bound (s : {r : ℝ // r∈Icc (0 : ℝ) 2}) (x : E) :
    weight x^(2*s.1) ≤ 81*(1+‖x‖^4) := by
  have hx0 : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  have hx1 : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1
  let M := max 1 ‖x‖
  have hM1 : 1 ≤ M := le_max_left _ _
  have hxM : ‖x‖ ≤ M := le_max_right _ _
  have hw : weight x ≤ 3*M := by dsimp only [weight]; linarith
  have hM : M^4 ≤ 1+‖x‖^4 := by
    by_cases hx : ‖x‖ ≤ 1
    · rw [show M=1 from max_eq_left hx]
      nlinarith [pow_nonneg (norm_nonneg x) 4]
    · rw [show M=‖x‖ from max_eq_right (le_of_not_ge hx)]
      linarith
  calc weight x^(2*s.1) ≤ weight x^(4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (weight_ge_one x) (by linarith [s.2.2])
    _ = weight x^4 := Real.rpow_ofNat _ _
    _ ≤ (3*M)^4 := pow_le_pow_left₀ (weight_pos x).le hw 4
    _ = 81*M^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (by norm_num)

private theorem weighted_square_integrable (s : {r : ℝ // r∈Icc (0 : ℝ) 2})
    (g : SchwartzMap E ℂ) : Integrable (fun x : E => weight x^(2*s.1)*‖g x‖^2) := by
  obtain ⟨C,hC,hCb⟩ := g.decay 0 0
  have hg (x : E) : ‖g x‖ ≤ C := by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using hCb x
  have hi : Integrable (fun x : E => 81*C*(‖g x‖+‖x‖^4*‖g x‖)) :=
    (g.integrable.norm.add (g.integrable_pow_mul volume 4)).const_mul (81*C)
  refine hi.mono' ?_ (Eventually.of_forall (fun x => ?_))
  · have hg := g.continuous.measurable
    apply Measurable.aestronglyMeasurable
    dsimp only [weight]
    fun_prop
  · rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (weight_pos x).le _) (sq_nonneg _))]
    have hsq : ‖g x‖^2 ≤ C*‖g x‖ := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hg x) (norm_nonneg _)
    calc weight x^(2*s.1)*‖g x‖^2 ≤ (81*(1+‖x‖^4))*(C*‖g x‖) :=
        mul_le_mul (weight_rpow_bound s x) hsq (sq_nonneg _) (by positivity)
      _ = _ := by ring

private def weightedNorm (s : ℝ) (g : SchwartzMap E ℂ) (x : E) : ℝ :=
  weight x^s*‖g x‖

private theorem weightedNorm_square (s : ℝ) (g : SchwartzMap E ℂ) (x : E) :
    (weightedNorm s g x)^2=weight x^(2*s)*‖g x‖^2 := by
  simp only [weightedNorm,mul_pow]
  rw [←Real.rpow_mul_natCast (weight_pos x).le]
  congr 2
  ring

private theorem weightedNorm_memLp (s : {r : ℝ // r∈Icc (0 : ℝ) 2}) (g : SchwartzMap E ℂ) :
    MemLp (weightedNorm s.1 g) 2 := by
  have hm : AEStronglyMeasurable (weightedNorm s.1 g) := by
    have hg := g.continuous.measurable
    apply Measurable.aestronglyMeasurable
    change Measurable (fun x : E => (1+|x 0|+|x 1|)^s.1*‖g x‖)
    fun_prop
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [weightedNorm_square] using weighted_square_integrable s g

private theorem weighted_reproducing_bound
    (s : {r : ℝ // r∈Icc (0 : ℝ) 2}) (K g : SchwartzMap E ℂ)
    (hrep : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K g=g) (x : E) :
    weightedNorm s.1 g x ≤
      Real.sqrt (∫y : E, (weightedNorm s.1 K y)^2)*
        Real.sqrt (∫y : E, (weightedNorm s.1 g y)^2) := by
  have hK := weightedNorm_memLp s K
  have hg := (weightedNorm_memLp s g).comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hKi := hK.integrable_mul hg
  have hnonneg (h : SchwartzMap E ℂ) (y : E) : 0 ≤ weightedNorm s.1 h y := by
    dsimp only [weightedNorm]
    exact mul_nonneg (Real.rpow_nonneg (weight_pos y).le _) (norm_nonneg _)
  have hpoint (y : E) : weight x^s.1*‖K y*g (x-y)‖ ≤
      weightedNorm s.1 K y*weightedNorm s.1 g (x-y) := by
    have hw := Real.rpow_le_rpow (weight_pos x).le (weight_submultiplicative x y) s.2.1
    rw [Real.mul_rpow (weight_pos (x-y)).le (weight_pos y).le] at hw
    have hh := mul_le_mul_of_nonneg_right hw (mul_nonneg (norm_nonneg (K y)) (norm_nonneg (g (x-y))))
    simpa only [weightedNorm,norm_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  have hleft : Integrable (fun y : E => weight x^s.1*‖K y*g (x-y)‖) := by
    refine hKi.mono' ?_ (Eventually.of_forall (fun y => ?_))
    · have hkc := K.continuous.measurable
      have hgc := g.continuous.measurable
      fun_prop
    · rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (weight_pos x).le _) (norm_nonneg _))]
      exact hpoint y
  have hnorm : weightedNorm s.1 g x ≤ ∫y : E, weightedNorm s.1 K y*weightedNorm s.1 g (x-y) := by
    have he : g x=∫y : E, K y*g (x-y) := by
      calc g x=(SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K g) x := by rw [hrep]
        _ = _ := by rw [SchwartzMap.convolution_apply]; rfl
    dsimp only [weightedNorm]
    rw [he]
    calc weight x^s.1*‖∫y : E, K y*g (x-y)‖ ≤
        weight x^s.1*(∫y : E, ‖K y*g (x-y)‖) :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.rpow_nonneg (weight_pos x).le _)
      _ = ∫y : E, weight x^s.1*‖K y*g (x-y)‖ := (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono hleft hKi hpoint
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    (Eventually.of_forall (hnonneg K))
    (Eventually.of_forall (fun y : E => hnonneg g (x-y)))
    (by simpa only [ENNReal.ofReal_ofNat] using hK)
    (by simpa only [ENNReal.ofReal_ofNat,Function.comp_def] using hg)
  have hC : (∫y : E, weightedNorm s.1 K y*weightedNorm s.1 g (x-y)) ≤
      Real.sqrt (∫y : E, (weightedNorm s.1 K y)^2)*
        Real.sqrt (∫y : E, (weightedNorm s.1 g (x-y))^2) := by
    simpa only [Real.sqrt_eq_rpow,Real.rpow_two,one_div] using hc
  have he := integral_sub_left_eq_self (fun y : E => (weightedNorm s.1 g y)^2) volume x
  rw [he] at hC
  exact hnorm.trans hC

private def logBox : Set E := {u | ∀i, u i∈Icc (-Real.log 8) (Real.log 8)}

private theorem compact_logBox : IsCompact logBox := by
  have hh := (isCompact_univ_pi (fun _ : Fin 2 =>
    isCompact_Icc (a := -Real.log 8) (b := Real.log 8))).image
      (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ))
  convert hh using 1
  ext x
  constructor
  · intro hx
    refine ⟨WithLp.ofLp x,?_,?_⟩
    · exact fun i _ => hx i
    · exact WithLp.toLp_ofLp 2 x
  · rintro ⟨y,hy,rfl⟩
    exact fun i => hy i (mem_univ i)

private theorem log_cutoff_exists :
    ∃ b : SchwartzMap E ℂ, ∀u∈logBox, b u=1 := by
  obtain ⟨b,hbs,hbc,-,V,-,hBV,hVb⟩ :=
    RHTower.D4BMRetardedCompactWeakRealization.exists_contDiff_cutoff
      compact_logBox isOpen_univ (subset_univ logBox)
  let B : SchwartzMap E ℂ := (hbc.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hbs)
  refine ⟨B,fun u hu => ?_⟩
  change (b u : ℂ)=1
  rw [hVb u (hBV hu),Complex.ofReal_one]

private def logCutoff : SchwartzMap E ℂ := Classical.choose log_cutoff_exists
private theorem logCutoff_eq (u : E) (hu : u∈logBox) : logCutoff u=1 :=
  Classical.choose_spec log_cutoff_exists u hu

private theorem logNode_cutoff_support (u : E)
    (hu : GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff (HTGeometry.quadrantLogNode u) ≠ 0) :
    u∈logBox := by
  have hs := GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff_spec.2.2.1
    (HTGeometry.quadrantLogNode u) (subset_tsupport _ hu)
  intro i
  have hi := hs i
  rw [HTGeometry.quadrantLogNode_apply] at hi
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ)<1/8) hi.1.le
  have hhi := Real.log_le_log (Real.exp_pos _) hi.2.le
  simp only [one_div,Real.log_inv,Real.log_exp] at hlo hhi
  constructor <;> linarith

private theorem localized_reproduction
    (q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 logCutoff)
      (𝓕 (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f))=
        𝓕 (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f) := by
  apply compact_fourier_reproduces
  intro u
  by_cases hu : GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff (HTGeometry.quadrantLogNode u)=0
  · simp only [GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz_apply,
      GaloisForLFunctions.HTGeometry.compactLocalizedMellinProfile_eq,hu,Complex.ofReal_zero,mul_zero,zero_mul]
  · rw [logCutoff_eq u (logNode_cutoff_support u hu),one_mul]

/-- Complete weighted pointwise Mellin-frequency control for the actual selected
local profile. Fixed common log support supplies the trace estimate from the
proved physical energy; no uniform Schwartz seminorm is a premise. -/
theorem bagCubicSelectedNormalizedCone_uniform_local_mellin_trace
    (s : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}, ∀ξ : E,
        (1+|ξ 0|+|ξ 1|)^(1+s.1)*
          ‖(𝓕 (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q
            (bagCubicSelectedNormalizedCone N))) ξ‖ ≤ C := by
  let r : {r : ℝ // r∈Icc (0 : ℝ) 2} := ⟨1+s.1,by constructor <;> linarith [s.2.1,s.2.2]⟩
  let K := 𝓕 logCutoff
  let D := Real.sqrt (∫y : E, (weightedNorm r.1 K y)^2)
  obtain ⟨A,hA,hAb⟩ := bagCubicSelectedNormalizedCone_uniform_local_mellin_energy s
  refine ⟨D*Real.sqrt A+1,by dsimp only [D]; positivity,?_⟩
  filter_upwards [hAb] with N hn
  intro q ξ
  let f := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q
    (bagCubicSelectedNormalizedCone N)
  let g := 𝓕 f
  have hi : Integrable (fun y : E => (weightedNorm r.1 g y)^2) := by
    simpa only [weightedNorm_square] using weighted_square_integrable r g
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun y : E => sq_nonneg (weightedNorm r.1 g y)))
  have hb : ENNReal.ofReal (∫y : E, (weightedNorm r.1 g y)^2) ≤ ENNReal.ofReal A := by
    rw [he]
    have hp : 2*r.1=2+2*s.1 := by dsimp only [r]; ring
    simpa only [weightedNorm_square,hp,weight] using hn q
  have hreal : (∫y : E, (weightedNorm r.1 g y)^2) ≤ A :=
    (ENNReal.ofReal_le_ofReal_iff hA.le).mp hb
  have hr := weighted_reproducing_bound r K g
    (localized_reproduction q (bagCubicSelectedNormalizedCone N)) ξ
  change weightedNorm r.1 g ξ ≤ D*Real.sqrt A+1
  refine hr.trans ?_
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hreal) hD
  change D*Real.sqrt (∫y : E, (weightedNorm r.1 g y)^2) ≤ D*Real.sqrt A+1
  linarith

/-- One trace constant for differences of ANY two actual localized Mellin
profiles, including different moving-line parameters. The energy on the right
is that of their exact difference, so this estimate preserves strong Cauchy
control when passing to the shrinking arithmetic axes. -/
theorem bagLocalizedMellin_difference_weighted_trace
    (s : {r : ℝ // r∈Icc (0 : ℝ) 2}) :
    ∃ C : ℝ, 0<C ∧
      ∀q r : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}, ∀f g : SchwartzMap E ℂ, ∀ξ : E,
        let h := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f-
          GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz r g
        (1+|ξ 0|+|ξ 1|)^s.1*‖(𝓕 h) ξ‖ ≤
          C*Real.sqrt (∫y : E, (1+|y 0|+|y 1|)^(2*s.1)*‖(𝓕 h) y‖^2) := by
  let K := 𝓕 logCutoff
  let D := Real.sqrt (∫y : E, (weightedNorm s.1 K y)^2)
  refine ⟨D+1,by dsimp only [D]; positivity,?_⟩
  intro q r f g ξ
  let h := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f-
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz r g
  have hrep : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K (𝓕 h)=𝓕 h := by
    apply compact_fourier_reproduces
    intro u
    by_cases hu : GaloisForLFunctions.HTGeometry.mellinLocalizationCutoff (HTGeometry.quadrantLogNode u)=0
    · simp only [h,sub_apply,
        GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz_apply,
        GaloisForLFunctions.HTGeometry.compactLocalizedMellinProfile_eq,hu,
        Complex.ofReal_zero,mul_zero,zero_mul,sub_self]
    · rw [logCutoff_eq u (logNode_cutoff_support u hu),one_mul]
  have hb := weighted_reproducing_bound s K (𝓕 h) hrep ξ
  simp only [weightedNorm_square] at hb
  change weightedNorm s.1 (𝓕 h) ξ ≤
    (D+1)*Real.sqrt (∫y : E, weight y^(2*s.1)*‖(𝓕 h) y‖^2)
  have hD : Real.sqrt (∫y : E, weight y^(2*s.1)*‖K y‖^2)=D := by
    simp only [D,weightedNorm_square]
  rw [hD] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith : D ≤ D+1) (Real.sqrt_nonneg _))

end RHTower.BAGTrace
