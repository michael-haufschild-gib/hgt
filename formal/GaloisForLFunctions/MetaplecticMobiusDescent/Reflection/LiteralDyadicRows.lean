/-
Literal dyadic rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.KernelSectorArithmetic
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.TerminalWidths

/-!
# Literal dyadic rows

Family raw scales, retained dyads and surviving frozen branches; literal dyadic and whole rows
and blocks; shape-weight norms of frozen strata.
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
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory JointLogSeparation InverseKernelSourceUniform
noncomputable section

def kernelCoordinateWeight (w : ℝ→ℂ) (slope Q t q : ℝ) : ℂ :=
  w (Real.log (q/Q))*kernelLogPhase t (slope*Real.log (q/Q))

def kernelDualWeight (windows : Fin 4→ℝ→ℂ) (Qn Qb t n b : ℝ) : ℂ :=
  kernelCoordinateWeight (windows 2) 1 Qn t n * kernelCoordinateWeight (windows 3) 3 Qb t b

lemma kernelCoordinateWeight_norm (w : ℝ→ℂ) (slope Q t q : ℝ) :
    ‖kernelCoordinateWeight w slope Q t q‖ = ‖w (Real.log (q/Q))‖ := by
  simp only [kernelCoordinateWeight,norm_mul,kernelLogPhase_norm,mul_one]

lemma kernelDualWeight_norm_le_one (windows : Fin 4→ℝ→ℂ)
    (hw : ∀ i y, ‖windows i y‖≤1) (Qn Qb t n b : ℝ) :
    ‖kernelDualWeight windows Qn Qb t n b‖≤1 := by
  rw [kernelDualWeight,norm_mul,kernelCoordinateWeight_norm,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ _)).trans (hw _ _)

lemma kernelCoordinateWeight_continuous (w : ℝ→ℂ) (slope Q q : ℝ) :
    Continuous (fun t => kernelCoordinateWeight w slope Q t q) :=
  (kernelLogPhase_continuous_left _).const_mul _

lemma kernel_mode_separation (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb k p n b t : ℝ) :
    (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i) *
      kernelLogPhase t (kernelSlope i*kernelLogCoordinates QK QP Qn Qb k p n b i)) =
    kernelCoordinateWeight (windows 0) (-2) QK t k *
      kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b := by
  simp only [kernelCoordinateWeight,kernelDualWeight,kernelSlope,kernelLogCoordinates,
    Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  norm_num
  simp only [show (⟨2, by decide⟩ : Fin 4) = 2 from rfl,
    show (⟨3, by decide⟩ : Fin 4) = 3 from rfl]
  ring

theorem reflected_kernel_uniform_separation (a b : ℝ) (ha : 0<a)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter C QK QP Qn Qb
      (∀ k p n q : ℝ, 0<k → 0<p → 0<n → 0<q →
        (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n q i)) *
          paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
            (C*n*q^3/(k^2*p^2)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (kernelCoordinateWeight (windows 0) (-2) QK t k *
            kernelCoordinateWeight (windows 1) (-2) QP t p *
            kernelDualWeight windows Qn Qb t n q) * twistedDensity U W θ R t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := normTwistedSource_uniform_separation
    a b ha windows kernelSlope M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  obtain ⟨he,hi,hm,hp⟩ := hsep θ _ hR
  refine ⟨?_,hi,hm,hp⟩
  intro k p n q hk hp hn hq
  rw [actual_annular_kernel_identity C QK QP Qn Qb k p n q hQK hQP hQn hQb hk hp hn hq]
  rw [he]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [kernel_mode_separation])

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory JointLogSeparation InverseKernelSourceUniform
noncomputable section

def reciprocalWindow (w : ℝ→ℂ) (α M : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (-α*M):ℂ)*(w y*(Real.exp (-α*y):ℂ))

lemma reciprocalWindow_norm_le_one (w : ℝ→ℂ) (α M : ℝ) (hα : 0≤α)
    (hw : ∀ y, ‖w y‖≤1) (hs : ∀ y, w y≠0 → -M≤y) (y : ℝ) :
    ‖reciprocalWindow w α M y‖≤1 := by
  by_cases hy : w y=0
  · simp [reciprocalWindow,hy]
  · have he : Real.exp (-α*M)*Real.exp (-α*y) ≤ 1 := by
      rw [← Real.exp_add,← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα (show 0≤M+y by linarith [hs y hy])]
    simp only [reciprocalWindow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-α*M)*(1*Real.exp (-α*y)) := by gcongr; exact hw y
      _ ≤ 1 := by simpa only [one_mul] using he

lemma reciprocalWindow_support (w : ℝ→ℂ) (α M y : ℝ) :
    reciprocalWindow w α M y≠0 → w y≠0 := by
  intro h hw
  apply h
  simp [reciprocalWindow,hw]

lemma reciprocalWindow_reconstruct (w : ℝ→ℂ) (α M y : ℝ) :
    w y*(Real.exp (-α*y):ℂ) =
      (Real.exp (α*M):ℂ)*reciprocalWindow w α M y := by
  unfold reciprocalWindow
  rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp

lemma reciprocal_norm_log (Q q : ℝ) (hQ : 0<Q) (hq : 0<q) :
    Real.exp (-(1/2:ℝ)*Real.log (q/Q)) = Real.sqrt Q/Real.sqrt q := by
  rw [show -(1/2:ℝ)*Real.log (q/Q) = Real.log (q/Q)*(-(1/2:ℝ)) by ring,
    ← Real.rpow_def_of_pos (div_pos hq hQ),Real.div_rpow hq.le hQ.le,
    Real.rpow_neg hq.le,Real.rpow_neg hQ.le,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow]
  field_simp

lemma reciprocal_cube_log (Q q : ℝ) (hQ : 0<Q) (hq : 0<q) :
    Real.exp (-Real.log (q/Q)) = Q/q := by
  rw [Real.exp_neg,Real.exp_log (div_pos hq hQ),inv_div]

def reciprocalKernelWindows (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) : Fin 4→ℝ→ℂ :=
  ![windows 0,windows 1,reciprocalWindow (windows 2) (1/2) (M 2),
    reciprocalWindow (windows 3) 1 (M 3)]

lemma reciprocalKernelWindows_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1)
    (hs : ∀ i y, windows i y≠0 → |y|≤M i) :
    ∀ i y, ‖reciprocalKernelWindows windows M i y‖≤1 := by
  intro i y
  fin_cases i
  · exact hw 0 y
  · exact hw 1 y
  · exact reciprocalWindow_norm_le_one _ _ _ (by norm_num) (hw 2)
      (fun y hy => (abs_le.mp (hs 2 y hy)).1) y
  · exact reciprocalWindow_norm_le_one _ _ _ (by norm_num) (hw 3)
      (fun y hy => (abs_le.mp (hs 3 y hy)).1) y

lemma reciprocalKernelWindows_support (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hs : ∀ i y, windows i y≠0 → |y|≤M i) :
    ∀ i y, reciprocalKernelWindows windows M i y≠0 → |y|≤M i := by
  intro i y hy
  fin_cases i
  · exact hs 0 y hy
  · exact hs 1 y hy
  · exact hs 2 y (reciprocalWindow_support _ _ _ _ hy)
  · exact hs 3 y (reciprocalWindow_support _ _ _ _ hy)

lemma reciprocal_window_product (windows : Fin 4→ℝ→ℂ) (M y : Fin 4→ℝ) :
    (∏ i, windows i (y i)) *
      ((Real.exp (-(1/2:ℝ)*y 2):ℂ)*(Real.exp (-y 3):ℂ)) =
    (Real.exp (M 2/2+M 3):ℂ)*(∏ i, reciprocalKernelWindows windows M i (y i)) := by
  have h2 := reciprocalWindow_reconstruct (windows 2) (1/2) (M 2) (y 2)
  have h3 := reciprocalWindow_reconstruct (windows 3) 1 (M 3) (y 3)
  have hp : (Real.exp (M 2/2+M 3):ℂ) =
      (Real.exp ((1/2:ℝ)*M 2):ℂ)*(Real.exp (1*M 3):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  rw [hp]
  simp only [reciprocalKernelWindows,Fin.prod_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  simp only [one_mul,neg_one_mul] at h3 ⊢
  change (windows 0 (y 0)*(windows 1 (y 1)*(windows 2 (y 2)*windows 3 (y 3)))) *
    ((Real.exp (-(1/2:ℝ)*y 2):ℂ)*(Real.exp (-y 3):ℂ)) =
    ((Real.exp ((1/2:ℝ)*M 2):ℂ)*(Real.exp (M 3):ℂ))*
      (windows 0 (y 0)*(windows 1 (y 1)*
        (reciprocalWindow (windows 2) (1/2) (M 2) (y 2)*
         reciprocalWindow (windows 3) 1 (M 3) (y 3))))
  calc
    _ = windows 0 (y 0)*windows 1 (y 1)*
      (windows 2 (y 2)*(Real.exp (-(1/2:ℝ)*y 2):ℂ))*
      (windows 3 (y 3)*(Real.exp (-y 3):ℂ)) := by ring
    _ = _ := by rw [h2,h3]; ring

theorem reciprocal_source_window_identity (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (QK QP Qn Qb k p n b r : ℝ) (hQn : 0<Qn) (hQb : 0<Qb)
    (hn : 0<n) (hb : 0<b) (hr : 0<r) :
    (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i)) /
      ((r*Real.sqrt n*b:ℝ):ℂ) =
    ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb):ℝ):ℂ) *
      (∏ i, reciprocalKernelWindows windows M i (kernelLogCoordinates QK QP Qn Qb k p n b i)) := by
  have hp := reciprocal_window_product windows M (kernelLogCoordinates QK QP Qn Qb k p n b)
  change (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i))*
      ((Real.exp (-(1/2:ℝ)*Real.log (n/Qn)):ℂ)*(Real.exp (-Real.log (b/Qb)):ℂ)) = _ at hp
  rw [reciprocal_norm_log Qn n hQn hn,reciprocal_cube_log Qb b hQb hb] at hp
  have he := congrArg (fun z : ℂ => z/((r*Real.sqrt Qn*Qb:ℝ):ℂ)) hp
  have hn0 := (Real.sqrt_pos.mpr hn).ne'
  have hQn0 := (Real.sqrt_pos.mpr hQn).ne'
  simp only [Complex.ofReal_mul,Complex.ofReal_div] at he ⊢
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hbC : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hQbC : (Qb:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQb.ne'
  have hnC : (Real.sqrt n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn0
  have hQnC : (Real.sqrt Qn:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQn0
  convert he using 1 <;> field_simp

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory JointLogSeparation InverseKernelSourceUniform
noncomputable section

lemma reflected_density_integrable (U W : ℝ→ℂ) (hU : Measurable U)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (θ R : ℝ) (hR : 0<R) (J : ℕ)
    (hi : Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖)) :
    Integrable (twistedDensity U W θ R) := by
  have hm := (twistedDensity_joint_stronglyMeasurable U W hU a b ha hWs hW R hR).comp_measurable
    (measurable_const.prodMk measurable_id : Measurable (fun t : ℝ => (θ,t)))
  apply hi.mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg t]))

lemma kernel_mode_integrable (density : ℝ→ℂ) (hi : Integrable density)
    (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb k p n b : ℝ) :
    Integrable (fun t : ℝ => density t *
      (kernelCoordinateWeight (windows 0) (-2) QK t k *
        kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b)) := by
  have hc : Continuous (fun t : ℝ => kernelCoordinateWeight (windows 0) (-2) QK t k *
      kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b) :=
    ((kernelCoordinateWeight_continuous _ _ _ _).mul (kernelCoordinateWeight_continuous _ _ _ _)).mul
      ((kernelCoordinateWeight_continuous _ _ _ _).mul (kernelCoordinateWeight_continuous _ _ _ _))
  apply hi.mul_bdd (c := ‖windows 0 (Real.log (k/QK))‖*‖windows 1 (Real.log (p/QP))‖*
    (‖windows 2 (Real.log (n/Qn))‖*‖windows 3 (Real.log (b/Qb))‖)) hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  exact le_of_eq (by simp only [kernelDualWeight,norm_mul,kernelCoordinateWeight_norm])

theorem kernel_finite_contraction {κ : Type*} (source : Finset κ) (coeff value : κ→ℂ)
    (density : ℝ→ℂ) (hi : Integrable density) (scalar : ℂ)
    (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ) (k p n b : κ→ℝ)
    (he : ∀ j ∈ source, value j = scalar*∫ t : ℝ,
      (kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j))*density t) :
    (∑ j ∈ source, coeff j*value j) = scalar*∫ t : ℝ, density t*
      ∑ j ∈ source, coeff j*(kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j)) := by
  have hint (j : κ) : Integrable (fun t : ℝ => density t*
      (coeff j*(kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j)))) := by
    convert (kernel_mode_integrable density hi windows QK QP Qn Qb (k j) (p j) (n j) (b j)).const_mul (coeff j) using 1
    funext t
    ring
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum source (fun j _ => hint j),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  rw [← mul_assoc,mul_comm (coeff j) scalar,mul_assoc]
  apply congrArg (fun z : ℂ => scalar*z)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; ring)

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory JointLogSeparation InverseKernelSourceUniform
noncomputable section
universe u

theorem reflected_finite_source_uniform
    (a b : ℝ) (ha : 0<a) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb r : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb → 0<r →
      let R := kernelCenter C QK QP Qn Qb
      (∀ {κ : Type u} (source : Finset κ) (coeff : κ→ℂ) (k p n q : κ→ℝ),
        (∀ j ∈ source, 0<k j ∧ 0<p j ∧ 0<n j ∧ 0<q j) →
        (∑ j ∈ source, coeff j *
          ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (k j) (p j) (n j) (q j) i)) /
            ((r*Real.sqrt (n j)*q j:ℝ):ℂ) *
            paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
              (C*n j*(q j)^3/((k j)^2*(p j)^2)))) =
        ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            ∑ j ∈ source, coeff j *
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (k j)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (p j)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (n j) (q j))) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_kernel_uniform_separation
    a b ha (reciprocalKernelWindows windows M) M hM
      (reciprocalKernelWindows_support windows M hwindows) W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb r hC hQK hQP hQn hQb hr
  obtain ⟨he,hi,hm,hp⟩ := hsep θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  have hdi := reflected_density_integrable U W hUs.continuous.measurable
    a b ha hWsupport hW θ _ hR J hi
  refine ⟨?_,hdi,hi,hm,hp⟩
  intro κ source coeff k p n q hn
  apply kernel_finite_contraction source coeff _ _ hdi _
    (reciprocalKernelWindows windows M) QK QP Qn Qb k p n q
  intro j hj
  rw [reciprocal_source_window_identity windows M QK QP Qn Qb
    (k j) (p j) (n j) (q j) r hQn hQb (hn j hj).2.2.1 (hn j hj).2.2.2 hr]
  rw [mul_assoc,he (k j) (p j) (n j) (q j) (hn j hj).1 (hn j hj).2.1 (hn j hj).2.2.1 (hn j hj).2.2.2,
    Complex.ofReal_mul]
  ring

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory JointLogSeparation InverseKernelSourceUniform CompletedDyadic
open Eisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def finitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

def weightedFinitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    (r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val)*actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X


end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory JointLogSeparation
noncomputable section
local notation "Eis" => Eisenstein.O

lemma weightedKernelCoordinate_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (i : Fin 4) (slope Q t q : ℝ) :
    ‖a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q‖≤1 := by
  rw [norm_mul,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (reciprocalKernelWindows_norm windows M hw hs i _)

lemma weightedKernelDual_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (Qn Qb t n b : ℝ) :
    ‖a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b‖≤1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans
    (kernelDualWeight_norm_le_one _ (reciprocalKernelWindows_norm windows M hw hs) Qn Qb t n b)

lemma weightedKernelCoordinate_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (i : Fin 4) (slope Q q : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q) :=
  ((kernelCoordinateWeight_continuous _ _ _ _).const_mul a).aestronglyMeasurable

lemma weightedKernelDual_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (Qn Qb n b : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b) := by
  exact (((kernelCoordinateWeight_continuous _ _ _ _).mul
    (kernelCoordinateWeight_continuous _ _ _ _)).const_mul a).aestronglyMeasurable

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {a c : Eis} {mode : Bool}

def survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) : Finset (φ→Fin 3) :=
  Finset.univ.filter (fun e => ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0)

lemma mem_survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (e : φ→Fin 3) :
    e∈survivingFrozenBranches F jF A nset bset ↔
      ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0 := by
  simp [survivingFrozenBranches]

lemma frozenBranchColumn_weight (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (A w : Ideal Eis→Ideal Eis→ℂ) (n b : Ideal Eis) :
    frozenBranchColumn F jF e (fun n b => A n b*w n b) n b =
      w n b*frozenBranchColumn F jF e A n b := by
  unfold frozenBranchColumn
  ring

lemma weighted_branch_zero_of_not_surviving (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (S : Ideal Eis→PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis→Ideal Eis→ℂ)
    (r aw : Ideal Eis→ℂ) (w : Ideal Eis→Ideal Eis→ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis)
    (he : e∉survivingFrozenBranches F jF A nset bset) :
    weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K=0 := by
  have hz : ∀ n∈nset, ∀ b∈bset, frozenBranchColumn F jF e A n b=0 := by
    intro n hn b hb
    by_contra h
    exact he ((mem_survivingFrozenBranches F jF A nset bset e).mpr ⟨n,hn,b,hb,h⟩)
  unfold weightedReflectedBranchHybridRow hybridRow hybridInner
  simp only [frozenBranchColumn_weight]
  have hi (P : Ideal Eis) : (∑ n∈nset, ∑ b∈bset,
      w n b*frozenBranchColumn F jF e A n b * canonicalQuadraticRowOfIdeal K (primaryIdealGenerator (n*b))*
        inverseCubicKernel P n*(if IsCoprime P b then 1 else 0))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro b hb
    simp [hz n hn b hb]
  simp only [hi,mul_zero,Finset.sum_const_zero]

lemma sum_branches_eq_surviving (F : PrimeFamily φ) (jF : φ→ℕ)
    (S : Ideal Eis→PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis→Ideal Eis→ℂ)
    (r aw : Ideal Eis→ℂ) (w : Ideal Eis→Ideal Eis→ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) :
    (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K)=
    ∑ e∈survivingFrozenBranches F jF A nset bset,
      weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K := by
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro e _ he
  exact weighted_branch_zero_of_not_surviving F jF e S s κ A r aw w u m Pset nset bset K he

theorem surviving_forced_norms (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (Y B : ℝ)
    (hn : ∀ n∈nset, primaryIdealGenerator n≠0 ∧ (Ideal.absNorm n:ℝ)≤Y)
    (hb : ∀ b∈bset, primaryIdealGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B)
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)≤Y ∧
    (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)≤B := by
  obtain ⟨n,hn',b,hb',hz⟩ := (mem_survivingFrozenBranches F jF A nset bset e).mp he
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b (hn n hn').1 (hb b hb').1 hz
  have hn0 : n≠0 := by intro h; exact (hn n hn').1 (by rw [h,primaryIdealGenerator_zero])
  have hb0 : b≠0 := by intro h; exact (hb b hb').1 (by rw [h,primaryIdealGenerator_zero])
  have hnpos : 0<Ideal.absNorm n := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn0)
  have hbpos : 0<Ideal.absNorm b := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb0)
  constructor
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm hd1)) (hn n hn').2
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hbpos (map_dvd Ideal.absNorm hd2)) (hb b hb').2

theorem surviving_extracted_scales (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (Y B : ℝ)
    (hn : ∀ n∈nset, primaryIdealGenerator n≠0 ∧ (Ideal.absNorm n:ℝ)≤Y)
    (hb : ∀ b∈bset, primaryIdealGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B)
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    extractedDualScale (frozenExtracted F jF e 1) Y = Y/Ideal.absNorm (frozenExtracted F jF e 1) ∧
    extractedDualScale (frozenExtracted F jF e 2) B = B/Ideal.absNorm (frozenExtracted F jF e 2) := by
  have h := surviving_forced_norms F hF jF A nset bset Y B hn hb e he
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact ⟨max_eq_right ((one_le_div (hp 1)).mpr h.1),
    max_eq_right ((one_le_div (hp 2)).mpr h.2)⟩

theorem surviving_frozen_local_assignments (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis))
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    ∃ n∈nset, ∃ b∈bset, ∀ i,
      (jF i≠4 → e i=0) ∧
      (jF i=4 → e i=1 → primaryIdealGenerator n∈F.ideal i) ∧
      (jF i=4 → e i=2 → primaryIdealGenerator n∉F.ideal i ∧ primaryIdealGenerator b∈F.ideal i) := by
  obtain ⟨n,hn,b,hb,hz⟩ := (mem_survivingFrozenBranches F jF A nset bset e).mp he
  refine ⟨n,hn,b,hb,?_⟩
  have hh := (mul_ne_zero_iff.mp hz).2
  intro i
  have hi := (Finset.prod_ne_zero_iff.mp hh) i (Finset.mem_univ i)
  simpa only [PrimeFamily.generator_span] using
    InverseTerminalWidths.surviving_local_piece (Ideal.span {F.generator i}) (F.generator_good i)
      (jF i) (e i) (primaryIdealGenerator n) (primaryIdealGenerator b) hi

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma sqrt_extraction_identity (A B C r U V : ℝ)
    (hA : 0<A) (hB : 0<B) (hC : 0<C) (hr : 0<r) (hU : 0<U) (hV : 0<V) :
    (Real.sqrt A*Real.sqrt B/Real.sqrt C) /
      (r*Real.sqrt (A*U)*(B*V)) =
      1/(r*Real.sqrt U*V*Real.sqrt (C*B)) := by
  rw [Real.sqrt_mul hA.le,Real.sqrt_mul hC.le]
  have hsa := (Real.sqrt_pos.mpr hA).ne'
  have hsb := (Real.sqrt_pos.mpr hB).ne'
  have hsc := (Real.sqrt_pos.mpr hC).ne'
  have hsu := (Real.sqrt_pos.mpr hU).ne'
  field_simp
  nlinarith [Real.sq_sqrt hB.le]

def extractedOutsideScalar (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) : ℝ :=
  smallScalar R / (r*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
    ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B))

theorem extractedOutsideScalar_scale (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) (hr : 0<r) (hU : 0<U) (hB : 0<B) :
    extractedOutsideScalar F jF e r U B R * frozenBranchScale F jF e =
      smallScalar R / (r*Real.sqrt U*B*
        Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 0):ℝ)*
          (Ideal.absNorm (frozenExtracted F jF e 2):ℝ))) := by
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  unfold extractedOutsideScalar frozenBranchScale
  have hh := sqrt_extraction_identity _ _ _ r U B (hn 1) (hn 2) (hn 0) hr hU hB
  calc
    _ = smallScalar R * ((Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 0):ℝ))/
      (r*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
        ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B))) := by ring
    _ = _ := by rw [hh]; ring

lemma power_normalizer {Z : ℝ} (hZ : 1≤Z) (v ell el S₀ B₀ Td : ℝ) :
    smallScalar (Z^(v+3*ell+el-Td)) /
      (Z^(el/3)*Real.sqrt (Z^v)*Z^ell*Real.sqrt (Z^S₀*Z^B₀)) =
      outsideScalar Z v ell el S₀ B₀ Td := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_add hZ0,
    ← Real.rpow_mul hZ0.le,← Real.rpow_mul hZ0.le,
    ← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0]
  unfold outsideScalar
  rw [div_eq_mul_inv,← Real.rpow_neg hZ0.le]
  have he : -(el/3+v*(1/2:ℝ)+ell+(S₀+B₀)*(1/2:ℝ)) =
      -v/2-ell-el/3-(S₀+B₀)/2 := by ring
  rw [he,mul_comm]

theorem extractedOutsideScalar_log_widths (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (Z r U B R : ℝ) (hZ : 1<Z) (hr : 0<r) (hU : 0<U) (hB : 0<B) (hR : 0<R) :
    extractedOutsideScalar F jF e r U B R * frozenBranchScale F jF e =
      outsideScalar Z (Real.logb Z U) (Real.logb Z B) (3*Real.logb Z r)
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) := by
  have hz0 : 0<Z := lt_trans zero_lt_one hZ
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  rw [extractedOutsideScalar_scale F jF e r U B R hr hU hB]
  symm
  rw [← power_normalizer hZ.le]
  unfold InverseTerminalWidths.normWidth
  rw [show 3*Real.logb Z r/3=Real.logb Z r by ring,
    show Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-
      (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R)=Real.logb Z R by ring]
  rw [Real.rpow_logb hz0 (ne_of_gt hZ) hr,Real.rpow_logb hz0 (ne_of_gt hZ) hU,
    Real.rpow_logb hz0 (ne_of_gt hZ) hB,Real.rpow_logb hz0 (ne_of_gt hZ) hR,
    Real.rpow_logb hz0 (ne_of_gt hZ) (hn 0),Real.rpow_logb hz0 (ne_of_gt hZ) (hn 2)]

lemma extractedOutsideScalar_pos (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) (hr : 0<r) (hU : 0<U) (hB : 0<B) (hR : 0<R) :
    0 < extractedOutsideScalar F jF e r U B R := by
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact div_pos (smallScalar_pos hR)
    (mul_pos (mul_pos hr (Real.sqrt_pos.mpr (mul_pos (hn 1) hU))) (mul_pos (hn 2) hB))

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma reciprocal_annulus_normalization (r Qn Qb kn kb : ℝ)
    (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb) :
    1/(r*Real.sqrt Qn*Qb) = Real.sqrt kn*kb/(r*Real.sqrt (kn*Qn)*(kb*Qb)) := by
  rw [Real.sqrt_mul hkn.le]
  have hs : Real.sqrt kn≠0 := (Real.sqrt_pos.mpr hkn).ne'
  field_simp

theorem physical_scalar_extracted (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r Qn Qb kn kb R A : ℝ)
    (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb) :
    A/(r*Real.sqrt Qn*Qb)*smallScalar R =
      (A*Real.sqrt kn*kb)*extractedOutsideScalar F jF e r
        (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))
        (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)) R := by
  have hp (v : Fin 3) : (Ideal.absNorm (frozenExtracted F jF e v):ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v)
  unfold extractedOutsideScalar
  rw [mul_div_cancel₀ _ (hp 1),mul_div_cancel₀ _ (hp 2)]
  have h := reciprocal_annulus_normalization r Qn Qb kn kb hr hn hb hkn hkb
  calc
    _ = A*(1/(r*Real.sqrt Qn*Qb))*smallScalar R := by ring
    _ = _ := by rw [h]; ring

theorem annular_kernel_threshold (Z T tau C r QK QP Qn Qb kn kb D1 D2 : ℝ)
    (hT : 0<T) (htau : 0<tau) (hC : 0<C) (hr : 0<r)
    (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) (h1 : 0<D1) (h2 : 0<D2) :
    Real.logb Z (kn*Qn/D1)+3*Real.logb Z (kb*Qb/D2)+3*Real.logb Z r-
      Real.logb Z (kernelCenter (T/(27*tau^2*C ^ 2)*r^3) QK QP Qn Qb) =
    Real.logb Z (27*tau^2*C ^ 2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3)) := by
  have hR : 0<kernelCenter (T/(27*tau^2*C ^ 2)*r^3) QK QP Qn Qb := by
    unfold kernelCenter
    positivity
  have hv : 0<kn*Qn/D1 := by positivity
  have hl : 0<kb*Qb/D2 := by positivity
  have heq : (kn*Qn/D1)*(kb*Qb/D2)^3*r^3 /
      kernelCenter (T/(27*tau^2*C ^ 2)*r^3) QK QP Qn Qb =
      27*tau^2*C ^ 2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3) := by
    unfold kernelCenter
    field_simp
  rw [← heq,Real.logb_div (by positivity) hR.ne',
    Real.logb_mul (by positivity) (pow_ne_zero _ hr.ne'),
    Real.logb_mul hv.ne' (pow_ne_zero _ hl.ne'),Real.logb_pow,Real.logb_pow]
  norm_num

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss Eisenstein CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

lemma frozenExtracted_eq_ideal (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v = reflectionExtractedDivisor F.ideal jF e v := by
  simp only [frozenExtracted,PrimeFamily.generator_span]

theorem actual_kernel_terminal_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z QP) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3) := by
  have hr : 0<ramifiedScale 1 completedRamifiedStep m := ramifiedScale_pos _ _
    (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have htau := sourceCuspScale_pos s.index
  have hp (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hcn := hp (Ideal.span {c}) (Ideal.span_singleton_eq_bot.not.mpr hc)
  have hfn := hp (∏ i, F.ideal i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i)))
  have hd (v : Fin 3) := hp (frozenExtracted F jF e v) (frozenExtracted_ne_zero F jF e v)
  have hcc : actualKernelCoefficient F s m T =
      T/(27*(sourceCuspScale s.index)^2*
        ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))^2)*
      (ramifiedScale 1 completedRamifiedStep m)^3 := by
    simp only [actualKernelCoefficient,fixedKernelCoefficient,map_one,Nat.cast_one,one_pow,mul_one,map_mul,Nat.cast_mul]
  rw [hcc,annular_kernel_threshold Z T (sourceCuspScale s.index)
    ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))
    _ QK QP Qn Qb kn kb _ _ hT htau (mul_pos hcn hfn) hr hK hP hn hb hkn hkb (hd 1) (hd 2)]
  unfold InverseTerminalWidths.terminalDualWidth InverseTerminalWidths.normWidth
  rw [← frozenExtracted_eq_ideal F jF e 1,← frozenExtracted_eq_ideal F jF e 2]
  have hd1 := hd 1
  have hd2 := hd 2
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

lemma literal_ramified_log_width (Z : ℝ) (m : ℕ) :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      (m:ℝ)*Real.logb Z 3 := by
  rw [ramifiedScale,one_mul,Real.logb_pow,completedRamifiedStep,
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<3)]
  ring

lemma literal_ramified_width_offset (Z : ℝ) (m : ℕ) :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      InverseTerminalWidths.ramifiedWidth Z m + 4*Real.logb Z 3 := by
  rw [literal_ramified_log_width]
  unfold InverseTerminalWidths.ramifiedWidth
  ring

lemma reflectedExponent_ramified_shift (O₀ H S₀ B₀ za v ell el Td δ : ℝ) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td =
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell (el-δ) (Td-δ)-2*δ/3 := by
  unfold InverseTerminalWidths.reflectedExponent
  rw [show Td-δ-v-3*ell-(el-δ)=Td-v-3*ell-el by ring]
  ring

theorem literal_reflectedExponent_le_signed (Z : ℝ) (hZ : 1<Z) (m : ℕ)
    (O₀ H S₀ B₀ za v ell Td : ℝ) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) Td ≤
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (InverseTerminalWidths.ramifiedWidth Z m) (Td-4*Real.logb Z 3) := by
  have hδ : 0≤4*Real.logb Z 3 := mul_nonneg (by norm_num) (Real.logb_nonneg hZ (by norm_num))
  rw [reflectedExponent_ramified_shift O₀ H S₀ B₀ za v ell _ Td (4*Real.logb Z 3),
    literal_ramified_width_offset]
  rw [add_sub_cancel_right]
  linarith

theorem ramified_offset_threshold (η : ℝ) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z →
      0≤4*Real.logb Z 3 ∧ 4*Real.logb Z 3≤η := by
  obtain ⟨Z₀,hZ₀,hw⟩ := InverseTerminalWidths.ramified_width_threshold η hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have he := hw Z hZ 0
  unfold InverseTerminalWidths.ramifiedWidth at he
  norm_num at he
  exact ⟨mul_nonneg (by norm_num) (Real.logb_nonneg hz (by norm_num)),by linarith⟩

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

lemma fixed_abs_log_threshold (C η : ℝ) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z → |Real.logb Z C|≤η := by
  obtain ⟨Z₀,hZ₀,h⟩ := InverseTerminalWidths.constant_log_error
    (Real.exp |Real.log C|) η (Real.exp_pos _) hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ
  have hz : 0<Real.log Z := Real.log_pos (lt_of_lt_of_le hZ₀ hZ)
  have hh := h Z hZ
  simpa only [Real.logb,Real.log_exp,abs_div,abs_of_pos hz] using hh

lemma reflectedExponent_threshold_error (O₀ H S₀ B₀ za v ell el Td err η : ℝ)
    (herr : |err|≤η) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el (Td+err) ≤
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td+η/2 := by
  have hη : 0≤η := (abs_nonneg err).trans herr
  have he : -η≤err := (abs_le.mp herr).1
  have hh : max 0 (Td-v-3*ell-el) ≤ max 0 (Td+err-v-3*ell-el)+η := by
    apply max_le
    · linarith [le_max_left (0:ℝ) (Td+err-v-3*ell-el)]
    · linarith [le_max_right (0:ℝ) (Td+err-v-3*ell-el)]
  unfold InverseTerminalWidths.reflectedExponent
  linarith

theorem literal_threshold_error_uniform (C η : ℝ) (hC : 0<C) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z → ∀ (m : ℕ) (O₀ H S₀ B₀ za v ell Td : ℝ),
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) (Td+Real.logb Z C) ≤
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
        (InverseTerminalWidths.ramifiedWidth Z m) Td+η/2 := by
  obtain ⟨Z₀,hZ₀,herr⟩ := fixed_abs_log_threshold (C/81) η hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ m O₀ H S₀ B₀ za v ell Td
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hid : Td+Real.logb Z C-4*Real.logb Z 3=Td+Real.logb Z (C/81) := by
    rw [Real.logb_div hC.ne' (by norm_num)]
    have hp := Real.logb_pow Z 3 4
    norm_num at hp
    linarith
  have hh := literal_reflectedExponent_le_signed Z hz m O₀ H S₀ B₀ za v ell (Td+Real.logb Z C)
  rw [hid] at hh
  exact hh.trans (reflectedExponent_threshold_error O₀ H S₀ B₀ za v ell
    (InverseTerminalWidths.ramifiedWidth Z m) Td (Real.logb Z (C/81)) η (herr Z hZ))

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

theorem physical_scalar_hybrid_shape (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (Z r Qn Qb kn kb R A C X L ε : ℝ)
    (hZ : 1<Z) (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb)
    (hR : 0<R) (hC : 0≤C) (hX : 0<X) (hL : 0<L) :
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2 * (frozenBranchScale F jF e)^2 *
      (C*(X*U*B*L)^ε*(X+U*B)*B*(U+L+(U*L)^(2/3:ℝ))) ≤
      (A*Real.sqrt kn*kb)^2*(6*C)*Z^(
        InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
          (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
          (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
          (Real.logb Z L) (Real.logb Z U) (Real.logb Z B) (3*Real.logb Z r)
          (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) +
        ε*(Real.logb Z X+Real.logb Z U+Real.logb Z B+Real.logb Z L)) := by
  let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
  let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  have hU : 0<U := div_pos (mul_pos hkn hn) (hp 1)
  have hB : 0<B := div_pos (mul_pos hkb hb) (hp 2)
  have hs := physical_scalar_extracted F jF e r Qn Qb kn kb R A hr hn hb hkn hkb
  have he := extractedOutsideScalar_log_widths F jF e Z r U B R hZ hr hU hB hR
  have hz0 : 0<Z := lt_trans zero_lt_one hZ
  have hpow (Q : ℝ) (hQ : 0<Q) : Z^(Real.logb Z Q)=Q := Real.rpow_logb hz0 (ne_of_gt hZ) hQ
  have hh := normalized_hybrid_shape hZ.le (Real.logb Z X) (Real.logb Z U) (Real.logb Z B)
    (3*Real.logb Z r) (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
    (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) (Real.logb Z L) ε
  rw [hpow X hX,hpow U hU,hpow B hB,hpow L hL,← he] at hh
  have hbnd := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hC)
    (sq_nonneg (A*Real.sqrt kn*kb))
  dsimp only
  rw [hs]
  convert hbnd using 1 <;> first | rfl | ring

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss Eisenstein CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

theorem actual_kernel_upper_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kK kP kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)) := by
  rw [actual_kernel_terminal_threshold F jF e s hc m Z T QK QP Qn Qb kn kb hT hK hP hn hb hkn hkb]
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  unfold InverseTerminalWidths.terminalDualWidth
  rw [Real.logb_div (by positivity) (by positivity),Real.logb_mul hkK.ne' hK.ne',
    Real.logb_mul hkP.ne' hP.ne',Real.logb_mul (pow_ne_zero _ hkK.ne') (pow_ne_zero _ hkP.ne'),
    Real.logb_pow,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory JointLogSeparation InverseKernelSourceUniform CompletedDyadic
open Eisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => Eisenstein.O
universe u v
variable {N a c : Eis} {mode : Bool}

theorem actual_physical_shape_uniform_type_uniform
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (m : ℕ)
      (T QK QP Qn Qb A C ε : ℝ), 0<T → 0<QK → 0<QP → 0<Qn → 0<Qb → 0≤C →
    let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
    let r := ramifiedScale 1 completedRamifiedStep m
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2*(frozenBranchScale F jF e)^2*
      (C*((kK*QK)*U*B*(kP*QP))^ε*((kK*QK)+U*B)*B*
        (U+(kP*QP)+(U*(kP*QP))^(2/3:ℝ))) ≤
    (A*Real.sqrt kn*kb)^2*(6*C)*Z^(
      InverseTerminalWidths.reflectedExponent 0 (Real.logb Z (kK*QK))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
        (InverseTerminalWidths.ramifiedWidth Z m)
        (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK))
          (Real.logb Z (kP*QP)) (Real.logb Z T) F.ideal jF e) +
      ε*(Real.logb Z (kK*QK)+Real.logb Z U+Real.logb Z B+Real.logb Z (kP*QP))+η/2) := by
  let Cf := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  have hCf : 0<Cf := by dsimp only [Cf]; positivity
  obtain ⟨Z₀,hZ₀,he⟩ := literal_threshold_error_uniform Cf η hCf hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro φ _ Z hZ F jF e m T QK QP Qn Qb A C ε hT hK hP hn hb hC
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let r := ramifiedScale 1 completedRamifiedStep m
  let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
  let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hr : 0<r := ramifiedScale_pos _ _ (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have hR : 0<R := by
    have hcc := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hh := physical_scalar_hybrid_shape F jF e Z r Qn Qb kn kb R A C (kK*QK) (kP*QP) ε
    hz hr hn hb hkn hkb hR hC (mul_pos hkK hK) (mul_pos hkP hP)
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hC))
  apply Real.rpow_le_rpow_of_exponent_le hz.le
  have hthreshold := actual_kernel_upper_threshold F jF e s hc m Z T QK QP Qn Qb kK kP kn kb
    hT hK hP hn hb hkK hkP hkn hkb
  have hexp := he Z hZ m 0 (Real.logb Z (kK*QK))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
    (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
    (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP))
      (Real.logb Z T) F.ideal jF e)
  change Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R = _ at hthreshold
  rw [hthreshold]
  linarith


end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalDyadicBlock (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (u : Eisˣ) (i : ℕ×ℕ×ℕ) : ℂ :=
  ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
    literalRawSeries G D s hc j S W X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)

theorem mixedReflectedValue_eq_dyadic (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then lambda^2∣a-1 else lambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0< X) :
    mixedReflectedValue D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        ∑' u : Eisˣ, ∑' i : ℕ×ℕ×ℕ, literalDyadicBlock G D s hc j S W X u i := by
  have hs := (literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm
  rw [mixedReflectedValue_eq_fullRaw,hs.tsum_prod]
  congr 1
  apply tsum_congr
  intro u
  exact tsum_dualIdealDyads _ (hs.prod_factor u)

lemma dyadic_kernel_argument_lower (scale rho q : ℝ) (hs : 0≤ scale)
    (hr : 0≤ rho) (hq : 0≤ q) (i : ℕ×ℕ×ℕ)
    (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
    scale*(ramifiedScale rho q i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3/16 ≤
      scale*(ramifiedScale rho q i.1)^3*(Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ)^3 := by
  have hn := (dualIdealDyad_bounds _ _ n.property).2.1
  have hb := (dualIdealDyad_bounds _ _ b.property).2.1
  have hp : 0≤ scale*(ramifiedScale rho q i.1)^3 := by
    unfold ramifiedScale
    positivity
  have hh := mul_le_mul hn (pow_le_pow_left₀ (by positivity) hb 3) (by positivity)
    (Nat.cast_nonneg (Ideal.absNorm n.val))
  have hh' := mul_le_mul_of_nonneg_left hh hp
  nlinarith only [hh']

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def rawDyadicLabel (x : RawTailIndex) : ℕ×ℕ×ℕ :=
  (x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val))

def rawDyadicCenter (scale : ℝ) (i : ℕ×ℕ×ℕ) : ℝ :=
  scale*(ramifiedScale 1 completedRamifiedStep i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3

lemma rawDyadicCenter_lower (scale : ℝ) (hs : 0≤ scale) (x : RawTailIndex) :
    rawDyadicCenter scale (rawDyadicLabel x)/16 ≤
      scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3 := by
  exact dyadic_kernel_argument_lower scale 1 completedRamifiedStep hs (by norm_num)
    (le_trans zero_le_one completedRamifiedStep_gt_one.le) (rawDyadicLabel x)
    ⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩
    ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩

theorem tsum_cut_dyadic (f : RawTailIndex→ℂ) (cut : (ℕ×ℕ×ℕ)→Prop)
    (hf : Summable (fun x => if cut (rawDyadicLabel x) then f x else 0)) :
    (∑' x, if cut (rawDyadicLabel x) then f x else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
            ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0 := by
  rw [tsum_dualIdealDyads _ hf]
  apply tsum_congr
  intro i
  have hl (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
      rawDyadicLabel (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=i := by
    simp only [rawDyadicLabel,((mem_dualIdealDyad _ _).mp n.property).2,
      ((mem_dualIdealDyad _ _).mp b.property).2]
  by_cases hi : cut i
  · simp only [hl,if_pos hi]
  · simp only [hl,if_neg hi,Finset.sum_const_zero]


end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma ramifiedScale_one_cube (m : ℕ) : (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  have hs : completedRamifiedStep^3=(3:ℝ) := by
    unfold completedRamifiedStep
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  simp only [ramifiedScale,one_mul]
  rw [← pow_mul,Nat.mul_comm m 3,pow_mul,hs]

lemma rawDyadicCenter_pow_lower (scale : ℝ) (hs : 0≤ scale) (i : ℕ×ℕ×ℕ) :
    scale*(2:ℝ)^(i.1+i.2.2+3*i.2.1)≤ rawDyadicCenter scale i := by
  unfold rawDyadicCenter
  rw [ramifiedScale_one_cube,pow_add,pow_add,Nat.mul_comm 3 i.2.1,pow_mul]
  simp only [mul_assoc]
  have hm : (2:ℝ)^i.1≤(3:ℝ)^i.1 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  gcongr

def retainedDyadicBox (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  let n := columnDyadicLength (max 1 (B/scale))
  (Finset.range (n+1)) ×ˢ ((Finset.range (n+1)) ×ˢ (Finset.range (n+1)))

lemma center_mem_retainedDyadicBox (scale B : ℝ) (hs : 0< scale)
    (i : ℕ×ℕ×ℕ) (hi : rawDyadicCenter scale i≤ B) : i∈retainedDyadicBox scale B := by
  let R := max 1 (B/scale)
  have hR : 1≤ R := le_max_left _ _
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤ R :=
    ((le_div_iff₀ hs).mpr (by nlinarith only [rawDyadicCenter_pow_lower scale hs.le i,hi])).trans (le_max_right _ _)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(i.1+i.2.2+3*i.2.1)) hp
  rw [Real.log_pow] at hl
  have hc : ((i.1+i.2.2+3*i.2.1:ℕ):ℝ)≤ columnDyadicLength R := by
    apply le_trans ((le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr hl)
    exact Nat.le_ceil _
  have hc' : i.1+i.2.2+3*i.2.1≤ columnDyadicLength R := by exact_mod_cast hc
  simp only [retainedDyadicBox,Finset.mem_product,Finset.mem_range]
  change i.1< columnDyadicLength R+1 ∧ i.2.1< columnDyadicLength R+1 ∧ i.2.2< columnDyadicLength R+1
  omega

lemma retainedDyadicBox_card (scale B : ℝ) :
    (retainedDyadicBox scale B).card=(columnDyadicLength (max 1 (B/scale))+1)^3 := by
  simp only [retainedDyadicBox,Finset.card_product,Finset.card_range]
  ring

theorem retainedDyadicBox_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ scale B : ℝ,
      ((retainedDyadicBox scale B).card:ℝ)^2≤ C*(max 1 (B/scale))^ε := by
  refine ⟨(2+1/((ε/6)*Real.log 2))^6,by positivity,?_⟩
  intro scale B
  have hR : 1≤ max 1 (B/scale) := le_max_left _ _
  have hp : 0< max 1 (B/scale) := lt_of_lt_of_le zero_lt_one hR
  have hh := columnDyadicLength_small_power (ε/6) (by positivity) _ hR
  rw [retainedDyadicBox_card]
  push_cast
  rw [← pow_mul]
  norm_num only [show (3:ℕ)*2=6 by norm_num]
  apply (pow_le_pow_left₀ (by positivity) hh 6).trans_eq
  rw [mul_pow,← Real.rpow_mul_natCast hp.le]
  congr 2
  ring
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def retainedDyads (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  (retainedDyadicBox scale B).filter (fun i => rawDyadicCenter scale i≤ B)

lemma mem_retainedDyads (scale B : ℝ) (hs : 0< scale) (i : ℕ×ℕ×ℕ) :
    i∈retainedDyads scale B ↔ rawDyadicCenter scale i≤ B := by
  simp only [retainedDyads,Finset.mem_filter]
  exact ⟨And.right,fun hi => ⟨center_mem_retainedDyadicBox scale B hs i hi,hi⟩⟩

lemma retainedDyads_card_le (scale B : ℝ) :
    (retainedDyads scale B).card≤(retainedDyadicBox scale B).card := Finset.card_filter_le _ _

lemma literalDyadicBlock_summable (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then lambda^2∣a-1 else lambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0< X) (u : Eisˣ) :
    Summable (literalDyadicBlock G D s hc j S W X u) := by
  have hs := ((literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm).prod_factor u
  have hh := (dualDyadicIndexEquiv.symm.summable_iff.mpr hs).sigma
  apply hh.congr
  intro i
  simp only [tsum_fintype,Fintype.sum_prod_type,literalDyadicBlock,Function.comp_apply]
  rfl

lemma tsum_sub_finset_eq_tail {α : Type*} (f : α→ℂ) (hf : Summable f) (A : Finset α) :
    (∑' i,f i)-(∑ i∈A,f i)=∑' i,if i∉A then f i else 0 := by
  have hh := hf.sum_add_tsum_subtype_compl A
  have ht : (∑' x : {x // x∉A}, f x.val)=∑' i,if i∉A then f i else 0 := by
    calc
      _ = ∑' x, ({x | x∉A} : Set α).indicator f x := tsum_subtype {x | x∉A} f
      _ = _ := by
        apply tsum_congr
        intro i
        by_cases hi : i∈A <;> simp [hi]
  rw [ht] at hh
  exact eq_sub_of_add_eq' hh |>.symm


end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma shell_windows_one (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (K P : Ideal Eis) (hK : K≠0) (hP : P≠0)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hPr : QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP)
    (j k : ℕ) (n : dualIdealDyad k) (b : dualIdealDyad j) :
    (∏ i : Fin 4, completedShellWindow (kernelLogCoordinates QK QP ((2:ℝ)^k) ((2:ℝ)^j)
      (Ideal.absNorm K:ℝ) (Ideal.absNorm P:ℝ) (Ideal.absNorm n.val:ℝ) (Ideal.absNorm b.val:ℝ) i))=1 := by
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hn := dualIdealDyad_bounds k n.val n.property
  have hb := dualIdealDyad_bounds j b.val b.property
  apply Finset.prod_eq_one
  intro i hi
  fin_cases i <;> dsimp only [kernelLogCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact completedShellWindow_log _ _ (hnorm K hK) hQK hKr.1 hKr.2
  · exact completedShellWindow_log _ _ (hnorm P hP) hQP hPr.1 hPr.2
  · exact completedShellWindow_log _ _ (hnorm n.val hn.1) (by positivity) hn.2.1 hn.2.2
  · exact completedShellWindow_log _ _ (hnorm b.val hb.1) (by positivity) hb.2.1 hb.2.2

theorem literalRawSeries_eq_shell_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1)
    (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalRawSeries (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=
    if CubicSieve.Admissible n.val ∧ primaryIdealGenerator b.val≠0 then
      actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  have hw := shell_windows_one QK QP hQK hQP K (∏ i,S.ideal i) hK.1
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))) hKr hPr i.2.1 i.2.2 n b
  by_cases hp : CubicSieve.Admissible n.val ∧ primaryIdealGenerator b.val≠0
  · have hp' : Squarefree n.val ∧ primaryIdealGenerator n.val≠0 ∧ primaryIdealGenerator b.val≠0 :=
      ⟨hp.1.1,hp.1.2,hp.2⟩
    rw [if_pos hp]
    unfold literalRawSeries rawDualKernelTerm literalRawCoefficient actualKernelSourceTerm actualMixedCoefficient literalRawScale
    rw [if_pos hp',hw]
    dsimp only
    simp only [ramifiedScale,one_mul]
    ring
  · have hp' : ¬(Squarefree n.val ∧ primaryIdealGenerator n.val≠0 ∧ primaryIdealGenerator b.val≠0) :=
      fun h => hp ⟨⟨h.1,h.2.1⟩,h.2.2⟩
    simp only [if_neg hp,literalRawSeries,rawDualKernelTerm,literalRawCoefficient,if_neg hp',zero_mul]

theorem literalDyadicBlock_eq_shell_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
        if CubicSieve.Admissible n.val ∧ primaryIdealGenerator b.val≠0 then
          actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
            (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  exact literalRawSeries_eq_shell_source F K hK S jF D s hc u i n b QK QP hQK hQP hKr hPr W θ X
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def reflectedNDyad (k : ℕ) : Finset (Ideal Eis) :=
  (dualIdealDyad k).filter CubicSieve.Admissible

def reflectedBDyad (j : ℕ) : Finset (Ideal Eis) :=
  (dualIdealDyad j).filter (fun b => primaryIdealGenerator b≠0)

lemma reflectedNDyad_bounds (k : ℕ) : ∀ n∈reflectedNDyad k,
    CubicSieve.Admissible n ∧ (2:ℝ)^k/2≤(Ideal.absNorm n:ℝ) ∧ (Ideal.absNorm n:ℝ)≤(2:ℝ)^k := by
  intro n hn
  exact ⟨(Finset.mem_filter.mp hn).2,(dualIdealDyad_bounds k n (Finset.mem_filter.mp hn).1).2⟩

lemma reflectedBDyad_bounds (j : ℕ) : ∀ b∈reflectedBDyad j,
    primaryIdealGenerator b≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm b:ℝ) ∧ (Ideal.absNorm b:ℝ)≤(2:ℝ)^j := by
  intro b hb
  exact ⟨(Finset.mem_filter.mp hb).2,(dualIdealDyad_bounds j b (Finset.mem_filter.mp hb).1).2⟩

lemma double_sum_coe (A B : Finset (Ideal Eis)) (f : Ideal Eis→Ideal Eis→ℂ) :
    (∑ n : A, ∑ b : B, f n.val b.val)=∑ n∈A, ∑ b∈B, f n b := by
  rw [Finset.sum_coe_sort A (fun n : Ideal Eis => ∑ b : B, f n b.val)]
  apply Finset.sum_congr rfl
  intro n hn
  exact Finset.sum_coe_sort B (f n)

lemma sum_dual_mask (j k : ℕ) (f : Ideal Eis→Ideal Eis→ℂ) :
    (∑ n : dualIdealDyad k, ∑ b : dualIdealDyad j,
      if CubicSieve.Admissible n.val ∧ primaryIdealGenerator b.val≠0 then f n.val b.val else 0)=
      ∑ n : reflectedNDyad k, ∑ b : reflectedBDyad j, f n.val b.val := by
  rw [double_sum_coe (dualIdealDyad k) (dualIdealDyad j)
    (fun n b => if CubicSieve.Admissible n ∧ primaryIdealGenerator b≠0 then f n b else 0),
    double_sum_coe (reflectedNDyad k) (reflectedBDyad j) f]
  simp only [reflectedNDyad,reflectedBDyad,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn' : CubicSieve.Admissible n
  · simp only [hn',true_and,if_pos]
  · simp only [hn',false_and,ite_false,Finset.sum_const_zero]

theorem literalDyadicBlock_eq_filtered_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : reflectedNDyad i.2.2, ∑ b : reflectedBDyad i.2.1,
        actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
          (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X := by
  rw [literalDyadicBlock_eq_shell_source F K hK S jF D s hc u i QK QP hQK hQP hKr hPr W θ X]
  exact sum_dual_mask i.2.1 i.2.2 (fun n b => actualKernelSourceTerm F K hK S jF D s hc u i.1 n b
    (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X)
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalDyadicRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    literalDyadicBlock (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) X u i

theorem literalDyadicRow_eq_physical (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hprod : ∀ P∈Pset, (∏ j,(S P).ideal j)=P)
    (hPr : ∀ P∈Pset, QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) :
    literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw=
      weightedFinitePhysicalKernelRow F K hK S jF Pset (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
        D s hc u i.1 (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
        W θ X r aw (fun _ _ => 1) := by
  unfold literalDyadicRow weightedFinitePhysicalKernelRow CoprimeSourceIndex
  simp only [Fintype.sum_prod_type,mul_one]
  apply Finset.sum_congr rfl
  intro P hP
  have hp : QP/2≤(Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ) ∧
      (Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ)≤ QP := by
    rw [hprod P.val.val P.val.property]
    exact hPr P.val.val P.val.property
  rw [literalDyadicBlock_eq_filtered_source F K hK (S P.val.val) jF (D P.val P.property)
    s hc u i QK QP hQK hQP hKr hp W θ X]
  simp only [Finset.mul_sum]
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CubicKubota  CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => Eisenstein.O

def shapeArgument (z : Eis) : ℂ := ((Ideal.absNorm (Ideal.span {z}):ℝ):ℂ)/(ringComplex z)^2

lemma shapeArgument_mul (x y : Eis) : shapeArgument (x*y) = shapeArgument x*shapeArgument y := by
  unfold shapeArgument
  rw [← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,Complex.ofReal_mul,map_mul,mul_pow]
  exact mul_div_mul_comm _ _ _ _

lemma shapeArgument_norm (z : Eis) (hz : z ≠ 0) : ‖shapeArgument z‖ = 1 := by
  have hne : ‖ringComplex z‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (ringComplex_ne_zero hz))
  rw [shapeArgument,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ← ringComplex_norm_sq_eq_absNorm_span]
  exact div_self hne

lemma stratumShapeFactor_mul {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r P : Eis) :
    s.stratumShapeFactor (c*r*P) = s.stratumShapeFactor c*shapeArgument r*shapeArgument P := by
  have he (z : Eis) : s.stratumShapeFactor z =
      (-star (extendedComplexCharacter s.gamma)*ringComplex (s.upper 0 0)^2)*shapeArgument z := by
    unfold FixedCuspShape.stratumShapeFactor shapeArgument
    ring
  rw [he (c*r*P),he c,shapeArgument_mul,shapeArgument_mul]
  ring

lemma actual_shape_separation {φ σ : Type*} [Fintype φ] [Fintype σ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H)
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    s.stratumShapeFactor (c*∏ i, (F.reflected K hK S).generator i) =
      s.stratumShapeFactor (c*primaryIdealGenerator (∏ i, F.ideal i))*
        shapeArgument (primaryIdealGenerator K)*shapeArgument (primaryIdealGenerator (∏ i, S.ideal i)) := by
  rw [(F.reflected K hK S).generator_product,F.reflected_product K hK S,
    primaryIdealGenerator_mul,primaryIdealGenerator_mul]
  rw [show c*(primaryIdealGenerator (∏ i, F.ideal i)*primaryIdealGenerator K*primaryIdealGenerator (∏ i, S.ideal i)) =
    (c*primaryIdealGenerator (∏ i, F.ideal i))*primaryIdealGenerator K*primaryIdealGenerator (∏ i, S.ideal i) by ring]
  exact stratumShapeFactor_mul s _ _ _

end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalWholeRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
      (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X

lemma sum_tsum_tsum_finite_middle {α β γ : Type*} [Fintype β]
    (L : Finset α) (f : α→β→γ→ℂ) (hf : ∀ p∈L, ∀ u, Summable (f p u)) :
    (∑ p∈L,∑' u,∑' i,f p u i)=∑' u,∑' i,∑ p∈L,f p u i := by
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact (Summable.tsum_finsetSum (fun p hp => hf p hp u)).symm

theorem literalWholeRow_eq_dyadic (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then lambda^2∣a-1 else lambda^2∣c-1)
    (hchar : ∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2)
    (hj : ∀ i,jF i<6) (hprod : ∀ P∈Pset,(∏ j,(S P).ideal j)=P)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo) (hWs : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (θ X : ℝ) (hX : 0< X) (r aw : Ideal Eis→ℂ) :
    literalWholeRow F K hK S jF Pset D s hc W θ X r aw=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryIdealGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X
            (fun K => r K*shapeArgument (primaryIdealGenerator K))
            (fun P => aw P*shapeArgument (primaryIdealGenerator P)) := by
  let : Finite Eisˣ := cubic_units_finite
  let : Fintype Eisˣ := Fintype.ofFinite _
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hts := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) u i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let wt := fun P : L => (r K*shapeArgument (primaryIdealGenerator K))*(aw P.val.val*shapeArgument (primaryIdealGenerator P.val.val))
  have hs (P : L) (u : Eisˣ) : Summable (fun i => wt P*block P u i) :=
    (literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX u).mul_left _
  have hp (P : L) : r K*aw P.val.val*
      mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
        (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
        (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryIdealGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,wt P*block P u i := by
    rw [mixedReflectedValue_eq_dyadic (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX,
      actual_shape_separation,hprod P.val.val P.val.property]
    simp only [tsum_mul_left]
    dsimp only [wt,block]
    ring
  unfold literalWholeRow
  simp_rw [hp]
  rw [←Finset.mul_sum,sum_tsum_tsum_finite_middle Finset.univ (fun P u i => wt P*block P u i) (fun P _ u => hs P u)]
  rfl
end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def familyRawScale (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X QK QP : ℝ) : ℝ :=
  actualKernelCoefficient F s 0 X/(QK^2*QP^2)

lemma familyRawScale_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0< X) (hQK : 0< QK) (hQP : 0< QP) : 0< familyRawScale F s X QK QP :=
  div_pos (actualKernelCoefficient_pos F s hc 0 X hX) (mul_pos (sq_pos_of_pos hQK) (sq_pos_of_pos hQP))

lemma literalRawScale_reflected (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X : ℝ) :
    literalRawScale (F.reflected K hK S) s X=
      actualKernelCoefficient F s 0 X/((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i,S.ideal i):ℝ)^2) := by
  have hh := actual_theta_kernel_argument F K hK S s 0 X 1 1
  simpa only [map_one,Nat.cast_one,one_pow,mul_one,ramifiedScale,pow_zero,literalRawScale] using hh

lemma familyRawScale_le_literal (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0< X)
    (hKr : (Ideal.absNorm K:ℝ)≤ QK) (hPr : (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP) :
    familyRawScale F s X QK QP≤ literalRawScale (F.reflected K hK S) s X := by
  rw [literalRawScale_reflected]
  have hk : (0:ℝ)< Ideal.absNorm K := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hK.1)
  have hp : (0:ℝ)< Ideal.absNorm (∏ i,S.ideal i) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))))
  apply div_le_div_of_nonneg_left (actualKernelCoefficient_pos F s hc 0 X hX).le (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ hk.le hKr 2) (pow_le_pow_left₀ hp.le hPr 2) (sq_nonneg _) (sq_nonneg _)

lemma reflected_norm_le_centers (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (QK QP : ℝ) (hKr : (Ideal.absNorm K:ℝ)≤ QK)
    (hPr : (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP) :
    (Ideal.absNorm (∏ i,(F.reflected K hK S).ideal i):ℝ)≤
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP := by
  rw [F.reflected_product]
  simp only [map_mul,Nat.cast_mul]
  have hk : 0≤ QK := le_trans (Nat.cast_nonneg _) hKr
  exact mul_le_mul (mul_le_mul_of_nonneg_left hKr (Nat.cast_nonneg _)) hPr
    (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hk)


end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open Eisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma finite_weighted_truncation {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β)
    (hf : ∀ p, Summable (f p)) :
    (∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)=
      ∑ p,w p*((∑' i,f p i)-∑ i∈J,f p i) := by
  rw [Summable.tsum_finsetSum (fun p _ => (hf p).mul_left (w p)),Finset.sum_comm]
  simp only [tsum_mul_left,←Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]

lemma finite_weighted_truncation_norm {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β) (E : ℝ)
    (hf : ∀ p, Summable (f p)) (hw : ∀ p,‖w p‖≤1)
    (he : ∀ p, ‖(∑' i,f p i)-∑ i∈J,f p i‖≤ E) :
    ‖(∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)‖≤ Fintype.card α*E := by
  rw [finite_weighted_truncation f w J hf]
  calc
    _ ≤ ∑ p,‖w p*((∑' i,f p i)-∑ i∈J,f p i)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : α,E := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw p) (norm_nonneg _)).trans (by simpa using he p)
    _ = _ := by simp


end
end InverseReflectedPhase

end

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power)
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace InverseReflectedPhase
open scoped Classical BigOperators
open Eisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => Eisenstein.O

@[simp] lemma shapeArgument_one : shapeArgument (1:Eis)=1 := by
  simp [shapeArgument,Ideal.span_singleton_one]

lemma stratumShapeFactor_mul_one {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r : Eis) :
    s.stratumShapeFactor (c*r)=s.stratumShapeFactor c*shapeArgument r := by
  simpa only [mul_one,shapeArgument_one] using stratumShapeFactor_mul s c r 1

lemma primeFamily_primary_product_ne_zero {φ : Type*} [Fintype φ] (F : PrimeFamily φ) :
    primaryIdealGenerator (∏ i,F.ideal i)≠0 := by
  rw [←F.generator_product]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => F.generator_ne_zero i)

lemma stratumShapeFactor_frozen_norm {φ : Type*} [Fintype φ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H) (c : Eis) (F : PrimeFamily φ) :
    ‖s.stratumShapeFactor (c*primaryIdealGenerator (∏ i,F.ideal i))‖=‖s.stratumShapeFactor c‖ := by
  rw [stratumShapeFactor_mul_one,norm_mul,shapeArgument_norm _ (primeFamily_primary_product_ne_zero F),mul_one]

lemma row_shape_weight_norm (r : Ideal Eis→ℂ) (K : Ideal Eis) (hK : Admissible K) :
    ‖r K*shapeArgument (primaryIdealGenerator K)‖=‖r K‖ := by
  have hk := primaryIdealGenerator_ne_zero_of_good_factors K hK.1 (fun P hP => (hK.2.2 P hP).1)
  rw [norm_mul,shapeArgument_norm _ hk,mul_one]

lemma slot_shape_weight_norm (aw : Ideal Eis→ℂ) (P : Ideal Eis) (hP : CubicSieve.Admissible P) :
    ‖aw P*shapeArgument (primaryIdealGenerator P)‖=‖aw P‖ := by
  rw [norm_mul,shapeArgument_norm _ hP.2,mul_one]
end
end InverseReflectedPhase

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
