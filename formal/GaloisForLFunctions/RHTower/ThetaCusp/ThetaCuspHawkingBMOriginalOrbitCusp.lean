import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalNullCusp
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalOrbitCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCausalAdmission
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
The original principal subtraction commutes with the physical orbit derivatives
up to an explicitly reconstructed cusp remainder. Continuous Goursat partials
supply joint differentiability of the actual principal coefficients. The original
coordinate map and radius factor then identify both genuine orbit remainders.
They vanish uniformly across the cusp, including after width-one integration,
with every complex height weight at fixed positive time and exterior radius.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMOriginalOrbitCusp
open D4BMOriginalCausalAdmission D4BMOriginalCausalPotential D4BMOriginalCuspJets
open D4BMNativeResponse D4BMJointSource D4BMModularCore D4BMHorizon
open D4BMIngoingCoordinates D4BMOriginalAngularCurrent D4BMOriginalOrbitCurrent
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev P := Fin 4 → ℝ

private theorem odd_continuous (s amp : ℂ) : Continuous (fun z : ℝ × ℝ => oddSource s amp z.1 z.2) := by
  have h1 := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h2 := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  exact h1.sub h2

private theorem nullValue_continuous (nu s amp : ℂ) : Continuous (fun z : ℝ × ℝ => nullValue nu s amp z.1 z.2) := by
  have h := (radialResponse_continuous nu s amp).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  simpa only [Function.comp_def,nullValue] using h

private theorem nullDensity_continuous (nu s amp : ℂ) : Continuous (fun z : ℝ × ℝ => nullDensity nu s amp z.1 z.2) := by
  have hs := (odd_continuous s amp).comp (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  have hv : Continuous (fun z : ℝ × ℝ => nu*(nu+1)/(4*(Real.cosh ((z.1-z.2)/2):ℂ)^(2 : ℕ))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  exact (continuous_const.mul hs).add (hv.mul (nullValue_continuous nu s amp))

private theorem nullValue_differentiable (nu s amp : ℂ) (z : ℝ × ℝ)
    (hp : 0<z.1) (hr : 0<z.2) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ => nullValue nu s amp z.1 z.2) z := by
  let A (p r : ℝ) : ℂ := ∫ b in (0:ℝ)..r, nullDensity nu s amp p b
  let B (p r : ℝ) : ℂ := ∫ a in (0:ℝ)..p, nullDensity nu s amp a r
  have hAc : Continuous (fun z : (ℝ × ℝ) × ℝ => nullDensity nu s amp z.1.1 z.2) := by
    have h := (nullDensity_continuous nu s amp).comp
      (show Continuous (fun z : (ℝ × ℝ) × ℝ => (z.1.1,z.2)) by fun_prop)
    simpa only [Function.comp_def] using h
  have hBc : Continuous (fun z : (ℝ × ℝ) × ℝ => nullDensity nu s amp z.2 z.1.2) := by
    have h := (nullDensity_continuous nu s amp).comp
      (show Continuous (fun z : (ℝ × ℝ) × ℝ => (z.2,z.1.2)) by fun_prop)
    simpa only [Function.comp_def] using h
  have hA : Continuous (fun z : ℝ × ℝ => A z.1 z.2) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ:=volume) (a₀:=0) (f:=fun z : ℝ × ℝ => fun b => nullDensity nu s amp z.1 b) hAc continuous_snd
  have hB : Continuous (fun z : ℝ × ℝ => B z.1 z.2) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ:=volume) (a₀:=0) (f:=fun z : ℝ × ℝ => fun a => nullDensity nu s amp a z.2) hBc continuous_fst
  have hp' : ∀ᶠ v : ℝ × ℝ in 𝓝 z, 0<v.1 :=
    continuous_fst.continuousAt.eventually (lt_mem_nhds hp)
  have hr' : ∀ᶠ v : ℝ × ℝ in 𝓝 z, 0<v.2 :=
    continuous_snd.continuousAt.eventually (lt_mem_nhds hr)
  have hd := hasStrictFDerivAt_uncurry_coprod (𝕜:=ℝ) (u:=z)
    (f:=nullValue nu s amp)
    (f₁:=fun p r => (1:ℝ →L[ℝ] ℝ).smulRight (A p r))
    (f₂:=fun p r => (1:ℝ →L[ℝ] ℝ).smulRight (B p r))
    (by filter_upwards [hp',hr'] with v hvp hvr
        exact (original_null_first nu s amp hvp hvr.le).hasFDerivAt)
    (by filter_upwards [hp',hr'] with v hvp hvr
        exact (original_null_second nu s amp hvp.le hvr).hasFDerivAt)
    (((ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1:ℝ →L[ℝ] ℝ)).continuous.comp hA).continuousAt)
    (((ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1:ℝ →L[ℝ] ℝ)).continuous.comp hB).continuousAt)
  exact hd.hasFDerivAt.differentiableAt

private theorem coefficient_differentiable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (i : Fin 3) (x : P) (hp : 0<x 0) (hr : 0<x 1) :
    DifferentiableAt ℝ (fun z : P => coefficient q branch amp (z 0) (z 1) i) x := by
  have hcoords : DifferentiableAt ℝ (fun z : P => (z 0,z 1)) x := by fun_prop
  have hn := (nullValue_differentiable (-principalExponent q i)
    (physicalRate q branch) amp (x 0,x 1) hp hr).comp x hcoords
  have hh : DifferentiableAt ℝ (fun z : P => (z 0-z 1)/2) x := by fun_prop
  have hL := (radialLift_hasDerivAt (physicalRate q branch) 0 amp 1 ((x 0-x 1)/2)).differentiableAt.comp x hh
  have hO := (timeOnset_hasDerivAt (2*physicalRate q branch) (x 0)).differentiableAt.comp x
    (show DifferentiableAt ℝ (fun z : P => z 0) x by fun_prop)
  exact (hn.const_mul (principalAmplitude q i)).add ((hL.mul hO).mul_const (principalAmplitude q i))

private def nullPrincipal (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P) : ℂ :=
  D4BMOriginalCuspJets.principal q branch amp (x 0) (x 1) ![x 2,x 3]

private def nullRemainder (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P) : ℂ :=
  remainder q branch amp (x 0) (x 1) ![x 2,x 3]

private theorem nullPrincipal_differentiable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 0<x 1) :
    DifferentiableAt ℝ (nullPrincipal q branch amp) x := by
  unfold nullPrincipal D4BMOriginalCuspJets.principal
  apply DifferentiableAt.fun_sum
  intro i _
  exact (coefficient_differentiable q branch amp i x hp hr).mul
    ((differentiableAt_const _).mul
      (Complex.ofRealCLM.differentiableAt.comp x (differentiableAt_apply 3 x))).cexp

private theorem nullRemainder_differentiable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hpr : x 0<x 1) :
    DifferentiableAt ℝ (nullRemainder q branch amp) x :=
  ((D4BMOriginalSpacetimeRegularity.originalPotential_smooth q branch amp x hp hpr).differentiableAt
    (by simp)).sub (nullPrincipal_differentiable q branch amp x hp (hp.trans hpr))

private def chart (x : P) : P :=
  ![x 0,x 0-2*tortoise (x 1),x 2,Real.log (x 3)]

private def chartDifferential (x : P) : P →L[ℝ] P :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    ContinuousLinearMap.proj 0-(2/(x 1^(2 : ℕ)-1)) • ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2,(x 3)⁻¹ • ContinuousLinearMap.proj 3]

private theorem chart_hasFDerivAt (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    HasFDerivAt chart (chartDifferential x) x := by
  have ht := (tortoise_hasDerivAt (x 1) hr).comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) x
    (hasFDerivAt_apply 1 x)
  have hl := (Real.hasDerivAt_log hy.ne').comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) x
    (hasFDerivAt_apply 3 x)
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply 0 x
  · convert! (hasFDerivAt_apply 0 x).sub (ht.const_mul 2) using 1
    ext v
    simp [div_eq_mul_inv,mul_assoc]
  · exact hasFDerivAt_apply 2 x
  · simpa [chartDifferential] using! hl

private theorem chart_basis (x : P) (i : Fin 4) :
    chartDifferential x (Pi.single i 1) =
      ![Pi.single 0 1+Pi.single 1 1,(-2/(x 1^(2 : ℕ)-1)) • Pi.single 1 1,
        Pi.single 2 1,(x 3)⁻¹ • Pi.single 3 1] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [chartDifferential,neg_div]

private def pullFirst (f : P → ℂ) (i : Fin 4) (x : P) : ℂ :=
  ![coordDeriv 0 f (chart x)+coordDeriv 1 f (chart x),
    (-2/((x 1:ℂ)^(2 : ℕ)-1))*coordDeriv 1 f (chart x),
    coordDeriv 2 f (chart x),(x 3:ℂ)⁻¹*coordDeriv 3 f (chart x)] i

private theorem chart_first {f : P → ℂ} {x : P} (hr : 1<x 1) (hy : 0<x 3)
    (hf : DifferentiableAt ℝ f (chart x)) (i : Fin 4) :
    coordDeriv i (fun z => f (chart z)) x=pullFirst f i x := by
  change (fderiv ℝ (f ∘ chart) x) (Pi.single i 1)=_
  rw [(hf.hasFDerivAt.comp x (chart_hasFDerivAt x hr hy)).fderiv,
    ContinuousLinearMap.comp_apply,chart_basis]
  fin_cases i <;> simp [pullFirst,coordDeriv,Complex.real_smul]


private theorem chart_order (x : P) (hr : 1<x 1) : (chart x) 0<(chart x) 1 := by
  have h := Real.log_lt_log (show 0<x 1-1 by linarith) (show x 1-1<x 1+1 by linarith)
  dsimp [chart,tortoise]
  linarith

private theorem coordinate_update (f : P → ℂ) (x : P) (i : Fin 4)
    (hf : DifferentiableAt ℝ f x) :
    coordDeriv i f x=deriv (fun a => f (Function.update x i a)) (x i) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  simpa only [Function.update_eq_self,coordDeriv,Function.comp_def] using h.deriv.symm

private theorem null_first (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P)
    (hp : 0<x 0) (hpr : x 0<x 1) :
    coordDeriv 0 (nullRemainder q branch amp) x =
      deriv (fun p => remainder q branch amp p (x 1) ![x 2,x 3]) (x 0) := by
  rw [coordinate_update _ _ _ (nullRemainder_differentiable q branch amp x hp hpr)]
  simp only [nullRemainder,Function.update_self,Function.update_of_ne (by decide : (1:Fin 4)≠0),
    Function.update_of_ne (by decide : (2:Fin 4)≠0),Function.update_of_ne (by decide : (3:Fin 4)≠0)]

private theorem null_second (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P)
    (hp : 0<x 0) (hpr : x 0<x 1) :
    coordDeriv 1 (nullRemainder q branch amp) x =
      deriv (fun r => remainder q branch amp (x 0) r ![x 2,x 3]) (x 1) := by
  rw [coordinate_update _ _ _ (nullRemainder_differentiable q branch amp x hp hpr)]
  simp only [nullRemainder,Function.update_self,Function.update_of_ne (by decide : (0:Fin 4)≠1),
    Function.update_of_ne (by decide : (2:Fin 4)≠1),Function.update_of_ne (by decide : (3:Fin 4)≠1)]

/-- The three original principal terms in the physical reconstructed stream. -/
def principalStream (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P) : ℂ :=
  (x 1:ℂ)*nullPrincipal q branch amp (chart x)

private def remainderStream (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P) : ℂ :=
  (x 1:ℂ)*nullRemainder q branch amp (chart x)

private theorem stream_difference (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    (fun x => sourceScalar q branch amp x-principalStream q branch amp x)=
      remainderStream q branch amp := by
  funext x
  simp only [sourceScalar,D4BMActualIngoingCurrent.originalIngoingPotential,
    principalStream,remainderStream,nullRemainder,remainder,nullPrincipal,chart,Matrix.cons_val]
  ring

private theorem principalStream_differentiable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    DifferentiableAt ℝ (principalStream q branch amp) x := by
  have hn := (nullPrincipal_differentiable q branch amp (chart x) hp
    (hp.trans (chart_order x hr))).comp x (chart_hasFDerivAt x hr hy).differentiableAt
  exact (show DifferentiableAt ℝ (fun z : P => (z 1:ℂ)) x by fun_prop).mul hn

private theorem radius_first {f : P → ℂ} (x : P) (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    coordDeriv i (fun z => (z 1:ℂ)*f z) x =
      (if i=1 then f x else 0)+(x 1:ℂ)*coordDeriv i f x := by
  have hR := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply 1 x)
  change HasFDerivAt (fun z : P => (z 1:ℂ)) _ x at hR
  rw [coordDeriv_mul hR.differentiableAt hf,coordDeriv,hR.fderiv]
  by_cases hi : i=1
  · subst i; simp [coordDeriv]
  · simp [coordDeriv,hi,Ne.symm hi]

private theorem remainder_first (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (i : Fin 4) :
    coordDeriv i (remainderStream q branch amp) x =
      (if i=1 then nullRemainder q branch amp (chart x) else 0)+
      (x 1:ℂ)*pullFirst (nullRemainder q branch amp) i x := by
  have hf := nullRemainder_differentiable q branch amp (chart x) hp (chart_order x hr)
  have hF : DifferentiableAt ℝ (fun z => nullRemainder q branch amp (chart z)) x := by
    simpa only [Function.comp_def] using hf.comp x (chart_hasFDerivAt x hr hy).differentiableAt
  unfold remainderStream
  rw [radius_first x hF i,chart_first hr hy hf i]

private theorem orbit_sub {U V : P → ℂ} {x : P}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) (j : Fin 2) :
    orbitDerivative (fun z => U z-V z) j x=orbitDerivative U j x-orbitDerivative V j x := by
  simp only [orbitDerivative,coordDeriv_sub hU hV]
  split_ifs <;> ring

/-- Exact orbit derivatives of the original stream after its original principal subtraction.
The undifferentiated remainder is retained when the radius reconstruction is differentiated. -/
theorem original_orbit_remainder (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    let v := x 0-2*tortoise (x 1)
    let E := fun p r => remainder q branch amp p r ![x 2,Real.log (x 3)]
    let f : ℂ := (x 1:ℂ)^(2 : ℕ)-1
    orbitDerivative (sourceScalar q branch amp) j x-orbitDerivative (principalStream q branch amp) j x =
      if j=0 then E (x 0) v-(2*(x 1:ℂ)/f)*deriv (E (x 0)) v
      else f*E (x 0) v+(x 1:ℂ)*(deriv (fun p => E p v) (x 0)-deriv (E (x 0)) v) := by
  have hU := (D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q branch amp x hp hr hy).differentiableAt (by simp)
  have hV := principalStream_differentiable q branch amp x hp hr hy
  have hs := orbit_sub hU hV j
  rw [stream_difference] at hs
  rw [← hs]
  have h0 := remainder_first q branch amp x hp hr hy 0
  have h1 := remainder_first q branch amp x hp hr hy 1
  simp only [pullFirst,Matrix.cons_val,show (0:Fin 4)≠1 from by decide,ite_false,ite_true,zero_add] at h0 h1
  rw [null_first q branch amp (chart x) hp (chart_order x hr),
      null_second q branch amp (chart x) hp (chart_order x hr)] at h0
  rw [null_second q branch amp (chart x) hp (chart_order x hr)] at h1
  have hf : (x 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show x 1^(2 : ℕ)-1≠0 by nlinarith)
  by_cases hj : j=0
  · simp only [orbitDerivative,if_pos hj]
    rw [h1]
    dsimp only [nullRemainder,chart,Matrix.cons_val]
    field_simp
    ring
  · simp only [orbitDerivative,if_neg hj]
    rw [h1,h0]
    dsimp only [nullRemainder,chart,Matrix.cons_val]
    field_simp [hf]
    ring

/-- Both genuine orbit derivatives have precisely the original principal cusp terms:
the difference vanishes with any complex height weight, along any horizontal path. -/
theorem original_orbit_cusp_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hR : 1<R) (X : ℝ → ℝ) (w : ℂ) (j : Fin 2) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (orbitDerivative (sourceScalar q branch amp) j ![p,R,X k,Real.exp k]-
       orbitDerivative (principalStream q branch amp) j ![p,R,X k,Real.exp k])) atTop (𝓝 0) := by
  let v := p-2*tortoise R
  have hpv : p<v := chart_order ![p,R,0,1] hR
  have hv : 0<v := hp.trans hpv
  let T : Ici (0:ℝ) := ⟨max p v,hp.le.trans (le_max_left _ _)⟩
  let pp : Ioc 0 T.val := ⟨p,⟨hp,le_max_left _ _⟩⟩
  let vv : Ioc 0 T.val := ⟨v,⟨hv,le_max_right _ _⟩⟩
  have hN := D4BMOriginalNullCusp.original_null_cusp_limit q branch amp T
    (fun _ => pp) (fun _ => vv) X w
  have hE := original_remainder_jet_tendsto_zero q branch amp ⟨p,hp.le⟩ ⟨v,hv.le⟩ [] X w
  simp only [D4BMSquareCuspJets.coordinateJet] at hE
  by_cases hj : j=0
  · have ht := hE.sub (hN.2.const_mul (2*(R:ℂ)/((R:ℂ)^(2 : ℕ)-1)))
    simp only [mul_zero,sub_zero] at ht
    apply ht.congr'
    filter_upwards [] with k
    rw [original_orbit_remainder q branch amp ![p,R,X k,Real.exp k] hp hR (Real.exp_pos k) j]
    dsimp only [pp,vv]
    simp only [Matrix.cons_val,Real.log_exp,if_pos hj]
    dsimp only [v]
    ring
  · have ht := (hE.const_mul ((R:ℂ)^(2 : ℕ)-1)).add ((hN.1.sub hN.2).const_mul (R:ℂ))
    simp only [mul_zero,sub_zero,add_zero] at ht
    apply ht.congr'
    filter_upwards [] with k
    rw [original_orbit_remainder q branch amp ![p,R,X k,Real.exp k] hp hR (Real.exp_pos k) j]
    dsimp only [pp,vv]
    simp only [Matrix.cons_val,Real.log_exp,if_neg hj]
    dsimp only [v]
    ring

private theorem uniform_of_arbitrary_paths (F : ℝ → ℝ → ℂ)
    (h : ∀ X : ℝ → ℝ, Tendsto (fun k => F k (X k)) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ k : ℝ in atTop, ∀ x : ℝ, ‖F k x‖ < epsilon := by
  classical
  let X : ℝ → ℝ := fun k => if hx : ∃ x, epsilon ≤ ‖F k x‖ then hx.choose else 0
  have ht := Metric.tendsto_nhds.mp (h X) epsilon hepsilon
  filter_upwards [ht] with k hk x
  rw [dist_zero_right] at hk
  by_contra hx
  have he : ∃ x, epsilon ≤ ‖F k x‖ := ⟨x,le_of_not_gt hx⟩
  have hb : epsilon ≤ ‖F k (X k)‖ := by
    dsimp only [X]
    rw [dif_pos he]
    exact he.choose_spec
  exact (not_lt_of_ge hb) hk

/-- The actual orbit remainder is uniformly negligible across the full cusp width. -/
theorem original_orbit_cusp_uniform (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hR : 1<R) (w : ℂ) (j : Fin 2) (epsilon : Ioi (0:ℝ)) :
    ∀ᶠ k : ℝ in atTop, ∀ X : ℝ,
      ‖Complex.exp (w*(k:ℂ))*
        (orbitDerivative (sourceScalar q branch amp) j ![p,R,X,Real.exp k]-
         orbitDerivative (principalStream q branch amp) j ![p,R,X,Real.exp k])‖ < epsilon :=
  uniform_of_arbitrary_paths _ (fun X => original_orbit_cusp_limit q branch amp p R hp hR X w j)
    epsilon epsilon.property

/-- The width-one integral of the actual orbit remainder has zero weighted cusp limit. -/
theorem original_orbit_cusp_integral (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hR : 1<R) (w : ℂ) (j : Fin 2) :
    Tendsto (fun k : ℝ => ∫ X in (-1/2:ℝ)..1/2,
      Complex.exp (w*(k:ℂ))*
        (orbitDerivative (sourceScalar q branch amp) j ![p,R,X,Real.exp k]-
         orbitDerivative (principalStream q branch amp) j ![p,R,X,Real.exp k])) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [original_orbit_cusp_uniform q branch amp p R hp hR w j
    ⟨epsilon/2,half_pos hepsilon⟩] with k hk
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun X _ => (hk X).le)
  norm_num only [sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one] at hi
  rw [dist_zero_right]
  simpa only [neg_div] using hi.trans_lt (half_lt_self hepsilon)

/-- The unchanged causal principal coefficient after radius reconstruction. -/
def principalCoefficient (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p R : ℝ) (i : Fin 3) : ℂ :=
  (R:ℂ)*coefficient q branch amp p (p-2*tortoise R) i

private theorem physicalCoefficient_differentiable (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (i : Fin 3) (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    DifferentiableAt ℝ (fun z : P => principalCoefficient q branch amp (z 0) (z 1) i) x := by
  have hn := (coefficient_differentiable q branch amp i (chart x) hp
    (hp.trans (chart_order x hr))).comp x (chart_hasFDerivAt x hr hy).differentiableAt
  have hR : DifferentiableAt ℝ (fun z : P => (z 1:ℂ)) x := by fun_prop
  change DifferentiableAt ℝ ((fun z : P => (z 1:ℂ))*
    ((fun z : P => coefficient q branch amp (z 0) (z 1) i) ∘ chart)) x
  exact hR.mul hn

/-- The reconstructed principal stream keeps exactly its original three exponents. -/
theorem principalStream_expansion (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P) :
    principalStream q branch amp x=∑ i : Fin 3,
      principalCoefficient q branch amp (x 0) (x 1) i*
        Complex.exp (principalExponent q i*(Real.log (x 3):ℂ)) := by
  simp only [principalStream,nullPrincipal,D4BMOriginalCuspJets.principal,chart,Matrix.cons_val,
    principalCoefficient,Finset.mul_sum,mul_assoc]

private theorem principalCoefficient_time_diff (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) (i : Fin 3) :
    DifferentiableAt ℝ (fun t => principalCoefficient q branch amp t R i) p := by
  have hpath : DifferentiableAt ℝ (fun t : ℝ => (![t,R,0,1] : P)) p := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have h := (physicalCoefficient_differentiable q branch amp i ![p,R,0,1] hp hr
    (show (0:ℝ)<1 from zero_lt_one)).comp p hpath
  simpa only [Function.comp_def,Matrix.cons_val] using h

private theorem principalCoefficient_radius_diff (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) (i : Fin 3) :
    DifferentiableAt ℝ (fun r => principalCoefficient q branch amp p r i) R := by
  have hpath : DifferentiableAt ℝ (fun r : ℝ => (![p,r,0,1] : P)) R := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have h := (physicalCoefficient_differentiable q branch amp i ![p,R,0,1] hp hr
    (show (0:ℝ)<1 from zero_lt_one)).comp R hpath
  simpa only [Function.comp_def,Matrix.cons_val] using h

private theorem principal_time (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P)
    (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 0 (principalStream q branch amp) x=∑ i : Fin 3,
      deriv (fun t => principalCoefficient q branch amp t (x 1) i) (x 0)*
        Complex.exp (principalExponent q i*(Real.log (x 3):ℂ)) := by
  rw [coordinate_update _ _ _ (principalStream_differentiable q branch amp x hp hr hy)]
  simp_rw [principalStream_expansion]
  simp only [Function.update_self,Function.update_of_ne (by decide : (1:Fin 4)≠0),
    Function.update_of_ne (by decide : (3:Fin 4)≠0)]
  exact (HasDerivAt.fun_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) =>
    (principalCoefficient_time_diff q branch amp (x 0) (x 1) hp hr i).hasDerivAt.mul_const
      (Complex.exp (principalExponent q i*(Real.log (x 3):ℂ))))).deriv

private theorem principal_radius (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P)
    (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 1 (principalStream q branch amp) x=∑ i : Fin 3,
      deriv (fun r => principalCoefficient q branch amp (x 0) r i) (x 1)*
        Complex.exp (principalExponent q i*(Real.log (x 3):ℂ)) := by
  rw [coordinate_update _ _ _ (principalStream_differentiable q branch amp x hp hr hy)]
  simp_rw [principalStream_expansion]
  simp only [Function.update_self,Function.update_of_ne (by decide : (0:Fin 4)≠1),
    Function.update_of_ne (by decide : (3:Fin 4)≠1)]
  exact (HasDerivAt.fun_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) =>
    (principalCoefficient_radius_diff q branch amp (x 0) (x 1) hp hr i).hasDerivAt.mul_const
      (Complex.exp (principalExponent q i*(Real.log (x 3):ℂ))))).deriv

/-- Orbit coefficients are the genuine time and radius derivatives of the original coefficients. -/
def principalOrbitCoefficient (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (j : Fin 2) (p R : ℝ) (i : Fin 3) : ℂ :=
  if j=0 then deriv (fun r => principalCoefficient q branch amp p r i) R
  else ((R:ℂ)^(2 : ℕ)-1)*deriv (fun r => principalCoefficient q branch amp p r i) R+
    deriv (fun t => principalCoefficient q branch amp t R i) p

/-- Both physical principal orbit derivatives retain the same three cusp powers. -/
theorem principal_orbit_expansion (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P)
    (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    orbitDerivative (principalStream q branch amp) j x=∑ i : Fin 3,
      principalOrbitCoefficient q branch amp j (x 0) (x 1) i*
        Complex.exp (principalExponent q i*(Real.log (x 3):ℂ)) := by
  by_cases hj : j=0
  · simp only [orbitDerivative,principalOrbitCoefficient,if_pos hj]
    exact principal_radius q branch amp x hp hr hy
  · simp only [orbitDerivative,principalOrbitCoefficient,if_neg hj]
    rw [principal_radius q branch amp x hp hr hy,principal_time q branch amp x hp hr hy]
    simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]

/-- Original orbit derivatives have the derived principal expansion with a rapidly vanishing remainder. -/
theorem original_orbit_expansion (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) (X : ℝ → ℝ) (w : ℂ) (j : Fin 2) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (orbitDerivative (sourceScalar q branch amp) j ![p,R,X k,Real.exp k]-
        ∑ i : Fin 3, principalOrbitCoefficient q branch amp j p R i*
          Complex.exp (principalExponent q i*(k:ℂ)))) atTop (𝓝 0) := by
  have h := original_orbit_cusp_limit q branch amp p R hp hr X w j
  apply h.congr'
  filter_upwards [] with k
  rw [principal_orbit_expansion q branch amp ![p,R,X k,Real.exp k] hp hr (Real.exp_pos k) j]
  simp only [Matrix.cons_val,Real.log_exp]

end
end RHTower.D4BMOriginalOrbitCusp
