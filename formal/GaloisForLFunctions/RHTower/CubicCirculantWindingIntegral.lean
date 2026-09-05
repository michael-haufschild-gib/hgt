import GaloisForLFunctions.RHTower.CubicCirculantHardyAdmission
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exact winding charge of the faithful circulant Hardy source

The graph/circulant first jet is proved to be the actual matrix derivative.
Its polynomial primitive and real-logarithmic amplitude primitive have equal
endpoints, so the admitted source current integrates to integral f'/f. Two
identical channels and reversal of the last two projection labels give genuine
orthogonal projections with ordinary cubic trace (2*pi*i)^-1 integral f'/f.

The constants are chosen before the input function. Exact pointwise source
recovery and trace-class corrections to the doubled source compressions are
retained. No winding, zero count, trace value, RH, or arithmetic budget is assumed.
This closes source-loop normalization, not arithmetic zero-charge conservation.
-/

open MeasureTheory ContinuousLinearMap
open scoped BigOperators ComplexConjugate Kronecker ContDiff
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace RHTower

/-- Compact deviation from one constant gives an integrable derivative with zero total mass. -/
theorem cubic_compact_derivative_integral (f : ℝ → ℂ) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport (fun x => f x-c)) :
    Integrable (deriv f) ∧ (∫ x : ℝ, deriv f x)=0 := by
  let g : SchwartzMap ℝ ℂ := hc.toSchwartzMap (hf.sub contDiff_const)
  have hd (x : ℝ) : deriv (g : ℝ → ℂ) x = deriv f x := by
    exact (HasDerivAt.sub_const c (hf.differentiable (by simp) x).hasDerivAt).deriv
  have hfun : (SchwartzMap.derivCLM ℂ ℂ g : ℝ → ℂ) = deriv f := funext hd
  constructor
  · rw [← hfun]
    exact (SchwartzMap.derivCLM ℂ ℂ g).integrable
  · simpa only [hd] using integral_deriv_schwartz_eq_zero g

theorem hasDerivAt_cyclicAmplitudeGraph {a : ℝ → ℝ} {da s : ℝ}
    (ha : HasDerivAt a da s) :
    HasDerivAt (fun x => cyclicAmplitudeGraph (a x)) (cyclicAmplitudeGraphJet (a s) da) s := by
  have haC := ha.ofReal_comp
  have hden : HasDerivAt (fun x => 1+(a x:ℂ)^2) (2*(a s:ℂ)*da) s := by
    convert (haC.pow 2).const_add 1 using 1 <;> norm_num
    congr
  have hne : 1+(a s:ℂ)^2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0:ℝ)<1+a s^2))
  have h00 : HasDerivAt (fun x => 1/(1+(a x:ℂ)^2))
      (-2*(a s:ℂ)*da/(1+(a s:ℂ)^2)^2) s := by
    convert (hasDerivAt_const s (1:ℂ)).div hden hne using 1 <;> try congr <;> ring
  have h01 : HasDerivAt (fun x => (a x:ℂ)/(1+(a x:ℂ)^2))
      ((1-(a s:ℂ)^2)*da/(1+(a s:ℂ)^2)^2) s := by
    convert haC.div hden hne using 1 <;> try congr <;> ring
  have h11 : HasDerivAt (fun x => (a x:ℂ)^2/(1+(a x:ℂ)^2))
      (2*(a s:ℂ)*da/(1+(a s:ℂ)^2)^2) s := by
    convert (haC.pow 2).div hden hne using 1 <;> try congr <;> norm_num <;> ring
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · convert h00 using 1 <;> congr
  · convert h01 using 1 <;> congr
  · convert h01 using 1 <;> congr
  · convert h11 using 1 <;> congr

/-- The graph/circulant first jet is the derivative of the actual tensor current. -/
theorem hasDerivAt_cyclicGraphCurrent {a : ℝ → ℝ} {x y : ℝ → ℂ}
    {da s : ℝ} {dx dy : ℂ} (ha : HasDerivAt a da s)
    (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) :
    HasDerivAt (fun w => cyclicAmplitudeGraph (a w) ⊗ₖ cyclicSourceCurrent (x w) (y w))
      (cyclicAmplitudeGraphJet (a s) da ⊗ₖ cyclicSourceCurrent (x s) (y s) +
        cyclicAmplitudeGraph (a s) ⊗ₖ cyclicSourceCurrentJet (x s) (y s) dx dy) s := by
  have hE := hasDerivAt_cyclicAmplitudeGraph ha
  have hK := hasDerivAt_cyclicSourceCurrent hx hy
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i.1) j.1).fun_mul
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hK i.2) j.2))

def cyclicLoopPhase (f : ℝ → ℂ) (x : ℝ) : ℂ := f x/(‖f x‖:ℂ)

theorem cyclicLoopPhase_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hz : ∀ x, f x ≠ 0) : ContDiff ℝ ∞ (cyclicLoopPhase f) := by
  have hn : ContDiff ℝ ∞ (fun x => (‖f x‖:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf.norm ℂ hz)
  have hne (x : ℝ) : (‖f x‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hz x)
  change ContDiff ℝ ∞ (fun x => f x/(‖f x‖:ℂ))
  simp only [div_eq_mul_inv]
  convert hf.mul (hn.inv hne) using 1 <;> congr

theorem cyclicLoopPhase_ne_zero {f : ℝ → ℂ} (hz : ∀ x, f x ≠ 0) (x : ℝ) :
    cyclicLoopPhase f x ≠ 0 :=
  div_ne_zero (hz x) (by exact_mod_cast norm_ne_zero_iff.mpr (hz x))

/-- Phase logarithmic derivative retains the literal source logarithmic derivative,
apart from the exact real-logarithm derivative. No zero count enters this identity. -/
theorem cyclicLoopPhase_logarithmic_derivative {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0) (x : ℝ) :
    deriv (cyclicLoopPhase f) x / cyclicLoopPhase f x =
      deriv f x/f x - deriv (fun w => (Real.log ‖f w‖:ℂ)) x := by
  have ha := ((hf.norm ℂ hz).differentiable (by simp) x).hasDerivAt
  have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr (hz x)
  have hnc : (‖f x‖:ℂ) ≠ 0 := by exact_mod_cast hn
  have hphase : deriv (cyclicLoopPhase f) x =
      (deriv f x*(‖f x‖:ℂ)-f x*((deriv (fun w => ‖f w‖) x:ℝ):ℂ))/(‖f x‖:ℂ)^2 :=
    ((hf.differentiable (by simp) x).hasDerivAt.div ha.ofReal_comp hnc).deriv
  have hlog : HasDerivAt (fun w => (Real.log ‖f w‖:ℂ))
      (((‖f x‖⁻¹ * deriv (fun w => ‖f w‖) x):ℝ):ℂ) x := by
    convert ((Real.hasDerivAt_log hn).comp x ha).ofReal_comp using 1
    rfl
  rw [hphase, hlog.deriv]
  dsimp only [cyclicLoopPhase]
  push_cast
  field_simp [hz x]

/-- Removing amplitude is winding-neutral because its real logarithm has equal endpoints. -/
theorem integral_cyclicLoopPhase_logarithmic_derivative {f : ℝ → ℂ} {c : ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) :
    (∫ x : ℝ, deriv (cyclicLoopPhase f) x / cyclicLoopPhase f x) =
      ∫ x : ℝ, deriv f x/f x := by
  have hlogsm : ContDiff ℝ ∞ (fun x => (Real.log ‖f x‖:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((hf.norm ℂ hz).log
      (fun x => norm_ne_zero_iff.mpr (hz x)))
  have hlogc : HasCompactSupport (fun x => (Real.log ‖f x‖:ℂ)-(Real.log ‖c‖:ℂ)) :=
    cubic_source_compact_deviation hc (fun z => (Real.log ‖z‖:ℂ))
  have hlog := cubic_compact_derivative_integral _ _ hlogsm hlogc
  have hdfc : HasCompactSupport (deriv f) := by
    have heq : deriv (fun x => f x-c) = deriv f := by
      funext x
      exact (HasDerivAt.sub_const c (hf.differentiable (by simp) x).hasDerivAt).deriv
    rw [← heq]
    exact hc.deriv
  have hquotc : HasCompactSupport (fun x => deriv f x/f x) := by
    simp only [div_eq_mul_inv]
    convert hdfc.mul_right (f' := fun x => (f x)⁻¹) using 1 <;> congr
  have hquoti : Integrable (fun x => deriv f x/f x) := by
    apply Continuous.integrable_of_hasCompactSupport _ hquotc
    exact (hf.continuous_deriv (by simp)).div hf.continuous hz
  simp_rw [cyclicLoopPhase_logarithmic_derivative hf hz]
  rw [integral_sub hquoti hlog.1, hlog.2, sub_zero]

def cyclicLoopMatrixCurrent (r : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  cyclicAmplitudeGraph ‖f x‖ ⊗ₖ
    cyclicSourceCurrent ((r:ℂ)*cyclicLoopPhase f x) ((r:ℂ)*conj (cyclicLoopPhase f x))

def cyclicLoopPrimitive (r : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  2*(((r:ℂ)*cyclicLoopPhase f x)^3-((r:ℂ)*conj (cyclicLoopPhase f x))^3)

def cyclicLoopTraceDensity (r : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Matrix.trace (cyclicFaithfulSourceAggregate r (f x) * deriv (cyclicLoopMatrixCurrent r f) x)

/-- Single-copy, literal derivative formula; the normalization is source-independent. -/
theorem cyclicLoopTraceDensity_eq (r : ℝ) (hr : 6*r^2=1) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0) (x : ℝ) :
    cyclicLoopTraceDensity r f x =
      deriv (cyclicLoopPrimitive r f) x + deriv (cyclicLoopPhase f) x/cyclicLoopPhase f x := by
  let q := cyclicLoopPhase f
  let v := fun w => conj (q w)
  have hqsm := cyclicLoopPhase_smooth hf hz
  have hvsm : ContDiff ℝ ∞ v := Complex.conjCLE.contDiff.comp hqsm
  have hq : HasDerivAt q (deriv q x) x := (hqsm.differentiable (by simp) x).hasDerivAt
  have hv : HasDerivAt v (deriv v x) x := (hvsm.differentiable (by simp) x).hasDerivAt
  have huv (w : ℝ) : q w*v w=1 := cyclicSource_phase_unit (hz w)
  have hprod := hq.fun_mul hv
  have hfun : (fun w => q w*v w) = fun _ => (1:ℂ) := funext huv
  rw [hfun] at hprod
  have htangent : q x*deriv v x+v x*deriv q x=0 := by
    have ht := hprod.unique (hasDerivAt_const x (1:ℂ))
    linear_combination ht
  have ha := ((hf.norm ℂ hz).differentiable (by simp) x).hasDerivAt
  have hX := hq.const_mul (r:ℂ)
  have hY := hv.const_mul (r:ℂ)
  have hK := hasDerivAt_cyclicGraphCurrent ha hX hY
  have hprim : HasDerivAt (cyclicLoopPrimitive r f)
      (6*((r:ℂ)*q x)^2*((r:ℂ)*deriv q x)-
        6*((r:ℂ)*v x)^2*((r:ℂ)*deriv v x)) x := by
    convert ((hX.pow 3).sub (hY.pow 3)).const_mul (2:ℂ) using 1 <;> try congr <;> norm_num <;> ring
  have hrc : (6:ℂ)*(r:ℂ)^2=1 := by exact_mod_cast hr
  have hnorm := cyclicSource_twoCopy_unit_normalization (r:ℂ) (q x) (v x)
    (deriv q x) (deriv v x) hrc (huv x) htangent
  unfold cyclicLoopTraceDensity
  rw [show deriv (cyclicLoopMatrixCurrent r f) x = _ from hK.deriv]
  change Matrix.trace ((cyclicAmplitudeGraph ‖f x‖ ⊗ₖ
      cyclicSourceGram ((r:ℂ)*q x) ((r:ℂ)*v x)) * _) = _
  rw [cyclicAmplitudeGraph_preserves_boundary_current, hprim.deriv]
  linear_combination (1/2:ℂ)*hnorm

theorem cyclicLoopPrimitive_smooth (r : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0) :
    ContDiff ℝ ∞ (cyclicLoopPrimitive r f) := by
  have hq := cyclicLoopPhase_smooth hf hz
  have hv := Complex.conjCLE.contDiff.comp hq
  exact contDiff_const.mul
    (((contDiff_const.mul hq).pow 3).sub ((contDiff_const.mul hv).pow 3))

/-- The literal amplitude-retaining six-channel current integrates to the source logarithmic
derivative. This identity is proved before choosing an arithmetic contour or its zero count. -/
theorem integral_cyclicLoopTraceDensity (r : ℝ) (hr : 6*r^2=1) {f : ℝ → ℂ} {c : ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) :
    (∫ x : ℝ, cyclicLoopTraceDensity r f x) = ∫ x : ℝ, deriv f x/f x := by
  let pc : ℂ := 2*(((r:ℂ)*(c/(‖c‖:ℂ)))^3-((r:ℂ)*conj (c/(‖c‖:ℂ)))^3)
  have hpc : HasCompactSupport (fun x => cyclicLoopPrimitive r f x-pc) :=
    cubic_source_compact_deviation hc
      (fun z => 2*(((r:ℂ)*(z/(‖z‖:ℂ)))^3-((r:ℂ)*conj (z/(‖z‖:ℂ)))^3))
  have hp := cubic_compact_derivative_integral _ pc (cyclicLoopPrimitive_smooth r hf hz) hpc
  have hqc : HasCompactSupport (fun x => cyclicLoopPhase f x-c/(‖c‖:ℂ)) :=
    cubic_source_compact_deviation hc (fun z => z/(‖z‖:ℂ))
  have hqsm := cyclicLoopPhase_smooth hf hz
  have hdqc : HasCompactSupport (deriv (cyclicLoopPhase f)) := by
    have heq : deriv (fun x => cyclicLoopPhase f x-c/(‖c‖:ℂ)) = deriv (cyclicLoopPhase f) := by
      funext x
      exact (HasDerivAt.sub_const _ (hqsm.differentiable (by simp) x).hasDerivAt).deriv
    rw [← heq]
    exact hqc.deriv
  have hqi : Integrable (fun x => deriv (cyclicLoopPhase f) x/cyclicLoopPhase f x) := by
    have hqcompact : HasCompactSupport
        (fun x => deriv (cyclicLoopPhase f) x/cyclicLoopPhase f x) := by
      simp only [div_eq_mul_inv]
      convert hdqc.mul_right (f' := fun x => (cyclicLoopPhase f x)⁻¹) using 1 <;> congr
    apply Continuous.integrable_of_hasCompactSupport _ hqcompact
    exact (hqsm.continuous_deriv (by simp)).div hqsm.continuous (cyclicLoopPhase_ne_zero hz)
  simp_rw [cyclicLoopTraceDensity_eq r hr hf hz]
  rw [integral_add hp.1 hqi, hp.2, zero_add]
  exact integral_cyclicLoopPhase_logarithmic_derivative hf hz hc

theorem cyclicFaithfulSourceProjection_current (t b : ℝ) (hnorm : t^2+b^2=1)
    {z : ℂ} (hz : z ≠ 0) :
    let P := cyclicFaithfulSourceProjection t b z
    (P 0*P 1-P 1*P 0)+(P 1*P 2-P 2*P 1)+(P 2*P 0-P 0*P 2) =
      cyclicAmplitudeGraph ‖z‖ ⊗ₖ
        cyclicSourceCurrent (((t*b:ℝ):ℂ)*(z/(‖z‖:ℂ)))
          (((t*b:ℝ):ℂ)*conj (z/(‖z‖:ℂ))) := by
  let E := cyclicAmplitudeGraph ‖z‖
  let u : ℂ := (b:ℂ)*(z/(‖z‖:ℂ))
  have hncomplex : (t:ℂ)^2+(b:ℂ)^2=1 := by exact_mod_cast hnorm
  have hu : (t:ℂ)^2+u*conj u=1 := by
    dsimp [u]
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination hncomplex + (b:ℂ)^2*(cyclicSource_phase_unit hz)
  have hm (M N : Matrix (Fin 3) (Fin 3) ℂ) : (E⊗ₖM)*(E⊗ₖN)=E⊗ₖ(M*N) := by
    rw [← Matrix.mul_kronecker_mul, cyclicAmplitudeGraph_idempotent]
  have hs (M N : Matrix (Fin 3) (Fin 3) ℂ) : E⊗ₖ(M-N)=E⊗ₖM-E⊗ₖN := by
    ext i j
    simp [Matrix.kroneckerMap_apply, mul_sub]
  dsimp only [E] at hm hs
  dsimp only [cyclicFaithfulSourceProjection]
  simp only [hm, ← hs, ← Matrix.kronecker_add]
  change E⊗ₖ(cyclicTripleCurrent (cyclicFrameProjection (t:ℂ) u (conj u) 0)
    (cyclicFrameProjection (t:ℂ) u (conj u) 1)
    (cyclicFrameProjection (t:ℂ) u (conj u) 2)) = _
  rw [cyclicFrameProjection_current _ _ _ hu]
  simp [E, u, Complex.ofReal_mul, mul_assoc]

theorem cyclicLoopMatrixCurrent_differentiable (r : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0) :
    Differentiable ℝ (cyclicLoopMatrixCurrent r f) := by
  intro x
  have hq := cyclicLoopPhase_smooth hf hz
  have hv := Complex.conjCLE.contDiff.comp hq
  have ha := ((hf.norm ℂ hz).differentiable (by simp) x).hasDerivAt
  exact (hasDerivAt_cyclicGraphCurrent ha
    (((hq.differentiable (by simp) x).hasDerivAt).const_mul (r:ℂ))
    (((hv.differentiable (by simp) x).hasDerivAt).const_mul (r:ℂ))).differentiableAt

theorem cyclicFaithfulSourceSymbol_current_value (t b : ℝ) (hnorm : t^2+b^2=1)
    (f : ℝ → ℂ) (c : ℂ) (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) (x : ℝ) :
    let A := cyclicFaithfulSourceSymbol t b f c hf hz hc
    cubicFiniteSymbolValue (cubicFiniteSourceCurrent (A 0) (A 1) (A 2)) x =
      cyclicLoopMatrixCurrent (t*b) f x := by
  have heval (j : Fin 3) :
      cubicFiniteSymbolValue (cyclicFaithfulSourceSymbol t b f c hf hz hc j) x =
        cyclicFaithfulSourceProjection t b (f x) j := by
    ext i k
    exact cyclicFaithfulSourceSymbol_apply _ _ _ _ _ _ _ _ _ _ _
  dsimp only
  simp only [cubicFiniteSourceCurrent, cubicFiniteSymbolValue_sub,
    cubicFiniteSymbolValue_add, cubicFiniteSymbolValue_mul, heval]
  exact cyclicFaithfulSourceProjection_current t b hnorm (hz x)

theorem cyclicFaithfulSourceSymbol_current_jet (t b : ℝ) (hnorm : t^2+b^2=1)
    (f : ℝ → ℂ) (c : ℂ) (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) (x : ℝ) :
    let A := cyclicFaithfulSourceSymbol t b f c hf hz hc
    cubicFiniteSymbolJet (cubicFiniteSourceCurrent (A 0) (A 1) (A 2)) x =
      deriv (cyclicLoopMatrixCurrent (t*b) f) x := by
  let A := cyclicFaithfulSourceSymbol t b f c hf hz hc
  let M := cubicFiniteSourceCurrent (A 0) (A 1) (A 2)
  have hk := (cyclicLoopMatrixCurrent_differentiable (t*b) hf hz x).hasDerivAt
  apply Matrix.ext
  intro i j
  have heq : (fun w => M i j w) = fun w => cyclicLoopMatrixCurrent (t*b) f w i j := by
    funext w
    exact congrFun (congrFun (cyclicFaithfulSourceSymbol_current_value t b hnorm f c hf hz hc w) i) j
  change deriv (fun w => M i j w) x = _
  rw [heq]
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hk i) j).deriv

/-- The already-admitted literal source matrices, not a replacement current, carry this winding. -/
theorem integral_cyclicFaithfulSourceSymbol_current (t b : ℝ)
    (hnorm : t^2+b^2=1) (hunit : 6*(t*b)^2=1)
    (f : ℝ → ℂ) (c : ℂ) (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) :
    let A := cyclicFaithfulSourceSymbol t b f c hf hz hc
    (∫ x : ℝ, Matrix.trace (cubicFiniteSymbolValue (A 0+A 1+A 2) x *
      cubicFiniteSymbolJet (cubicFiniteSourceCurrent (A 0) (A 1) (A 2)) x)) =
        ∫ x : ℝ, deriv f x/f x := by
  have heval (j : Fin 3) (x : ℝ) :
      cubicFiniteSymbolValue (cyclicFaithfulSourceSymbol t b f c hf hz hc j) x =
        cyclicFaithfulSourceProjection t b (f x) j := by
    ext i k
    exact cyclicFaithfulSourceSymbol_apply _ _ _ _ _ _ _ _ _ _ _
  dsimp only
  simp_rw [cyclicFaithfulSourceSymbol_current_jet t b hnorm f c hf hz hc,
    cubicFiniteSymbolValue_add, heval, cyclicFaithfulSourceProjection_sum t b hnorm (hz _)]
  exact integral_cyclicLoopTraceDensity (t*b) hunit hf hz hc

section DoubleOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Two identical channels; no source-dependent scaling or prescribed index. -/
def cubicDoubleOperator : (H →L[ℂ] H) →+* (CubicTwoChannel H →L[ℂ] CubicTwoChannel H) :=
  cubicBlockHom.comp (Matrix.scalar (Fin 2))

omit [CompleteSpace H] in
theorem cubicDoubleOperator_eq (T : H →L[ℂ] H) :
    cubicDoubleOperator T = cubicBlock !![T,0;0,T] := by
  change cubicBlock _ = cubicBlock _
  congr 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]

theorem cubicDoubleOperator_orthogonal (T : H →L[ℂ] H)
    (hs : IsSelfAdjoint T) (hi : IsIdempotentElem T) :
    IsSelfAdjoint (cubicDoubleOperator T) ∧ IsIdempotentElem (cubicDoubleOperator T) := by
  constructor
  · change adjoint (cubicDoubleOperator T) = cubicDoubleOperator T
    rw [cubicDoubleOperator_eq, cubicBlock_adjoint]
    congr 1
    apply Matrix.ext
    intro i j
    have ht : adjoint T=T := hs
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, ContinuousLinearMap.star_eq_adjoint, ht]
  · change cubicDoubleOperator T*cubicDoubleOperator T=cubicDoubleOperator T
    rw [← map_mul, hi.eq]

theorem cubicDoubleOperator_nuclear_trace (T : H →L[ℂ] H) (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (cubicDoubleOperator T) ∧
      opTrace (cubicDoubleOperator T) = 2*opTrace T := by
  rw [cubicDoubleOperator_eq]
  obtain ⟨hn,ht⟩ := cubicBlock_diagonal_trace T T hT hT
  exact ⟨hn, by linear_combination ht⟩

omit [CompleteSpace H] in
theorem cubicDoubleOperator_cubic (R Q P : H →L[ℂ] H) :
    cubicDoubleOperator (formationAnchoredCubicAssociator R Q P) =
      formationAnchoredCubicAssociator (cubicDoubleOperator R)
        (cubicDoubleOperator Q) (cubicDoubleOperator P) := by
  simp [formationAnchoredCubicAssociator, formationAnchoredCubicDefect,
    restrictedProjectionCubicDefect, restrictedProjectionDisplacement]

omit [CompleteSpace H] in
theorem cubicAssociator_reverse_last_two (P Q R : H →L[ℂ] H) :
    formationAnchoredCubicAssociator Q R P = -formationAnchoredCubicAssociator R Q P := by
  dsimp [formationAnchoredCubicAssociator, formationAnchoredCubicDefect,
    restrictedProjectionCubicDefect, restrictedProjectionDisplacement]
  noncomm_ring

end DoubleOperator

/-- Fixed constants, exact source recovery, genuine doubled/reversed source compression,
and ordinary cubic winding charge. This produces no arithmetic zero-charge estimate. -/
theorem exists_faithful_circulant_winding_cubic :
    ∃ t b : ℝ, t^2+b^2=1 ∧ 6*(t*b)^2=1 ∧ t*b ≠ 0 ∧
    ∀ (f : ℝ → ℂ) (c : ℂ) (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
      (hc : HasCompactSupport (fun x => f x-c)),
    let A := cyclicFaithfulSourceSymbol t b f c hf hz hc
    (∀ x, cyclicFaithfulSourceRecover (t*b) (cubicFiniteSymbolValue (A 0+A 1+A 2) x) = f x) ∧
    ∃ P Q R : CubicTwoChannel (CubicFiniteChannel (Fin 2 × Fin 3) SoninL2) →L[ℂ]
        CubicTwoChannel (CubicFiniteChannel (Fin 2 × Fin 3) SoninL2),
      IsSelfAdjoint P ∧ IsSelfAdjoint Q ∧ IsSelfAdjoint R ∧
      IsIdempotentElem P ∧ IsIdempotentElem Q ∧ IsIdempotentElem R ∧
      MemSchattenClass 1 (P-cubicDoubleOperator
        (cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 0)*cubicFiniteHardyCutoff)) ∧
      MemSchattenClass 1 (Q-cubicDoubleOperator
        (cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 2)*cubicFiniteHardyCutoff)) ∧
      MemSchattenClass 1 (R-cubicDoubleOperator
        (cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 1)*cubicFiniteHardyCutoff)) ∧
      MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) ∧
      opTrace (formationAnchoredCubicAssociator R Q P) =
        (2*(Real.pi:ℂ)*Complex.I)⁻¹ * ∫ x : ℝ, deriv f x/f x := by
  obtain ⟨t,b,hnorm,hunit,hne⟩ := exists_cyclicSource_unit_constants
  refine ⟨t,b,hnorm,hunit,hne,?_⟩
  intro f c hf hz hc
  obtain ⟨hrec,P,Q,R,hPs,hQs,hRs,hPi,hQi,hRi,hP,hQ,hR,hN,ht⟩ :=
    exists_rounded_faithful_circulant_source t b hnorm hne f c hf hz hc
  refine ⟨hrec,cubicDoubleOperator P,cubicDoubleOperator R,cubicDoubleOperator Q,
    (cubicDoubleOperator_orthogonal P hPs hPi).1,
    (cubicDoubleOperator_orthogonal R hRs hRi).1,
    (cubicDoubleOperator_orthogonal Q hQs hQi).1,
    (cubicDoubleOperator_orthogonal P hPs hPi).2,
    (cubicDoubleOperator_orthogonal R hRs hRi).2,
    (cubicDoubleOperator_orthogonal Q hQs hQi).2,?_,?_,?_,?_,?_⟩
  · rw [← map_sub]
    exact (cubicDoubleOperator_nuclear_trace _ hP).1
  · rw [← map_sub]
    exact (cubicDoubleOperator_nuclear_trace _ hR).1
  · rw [← map_sub]
    exact (cubicDoubleOperator_nuclear_trace _ hQ).1
  · rw [← cubicDoubleOperator_cubic, cubicAssociator_reverse_last_two]
    exact (cubicDoubleOperator_nuclear_trace _ hN.one_neg).1
  · rw [← cubicDoubleOperator_cubic, cubicAssociator_reverse_last_two,
      (cubicDoubleOperator_nuclear_trace _ hN.one_neg).2, opTrace_neg]
    rw [integral_cyclicFaithfulSourceSymbol_current t b hnorm hunit f c hf hz hc] at ht
    rw [ht]
    have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hconst : -2*(Complex.I/(4*(Real.pi:ℂ))) = (2*(Real.pi:ℂ)*Complex.I)⁻¹ := by
      field_simp
      norm_num [Complex.I_sq]
    linear_combination hconst * (∫ x : ℝ, deriv f x/f x)

end RHTower

