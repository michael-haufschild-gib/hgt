import GaloisForLFunctions.RHTower.ThetaCuspC5InverseReserveGrowth
import GaloisForLFunctions.RHTower.ThetaCuspC5InverseForceQuadrature
/-! Complete second-order clock operator for the actual intrinsic inverse source.
The third and fourth curvature derivatives enter with strictly negative
coefficients on the physical chamber. Actual affine source inequalities
eliminate both, producing a strict lower force depending only on curvature
through order two. Positivity of that remaining force is not asserted. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "w" => quadratureCurvatureThird
local notation "v" => supersolutionCurvatureFourth

private abbrev EulerDerivAt (f : ℝ → ℝ) (q t : ℝ) : Prop := HasDerivAt f (q/t) t
private theorem eConst (a t : ℝ) : EulerDerivAt (fun _ => a) 0 t := by
  simpa only [EulerDerivAt,zero_div] using hasDerivAt_const t a
private theorem eAdd {f g : ℝ → ℝ} {a b t : ℝ} (hf : EulerDerivAt f a t) (hg : EulerDerivAt g b t) :
    EulerDerivAt (fun s => f s+g s) (a+b) t := by
  unfold EulerDerivAt at *
  convert! hf.add hg using 1
  ring
private theorem eSub {f g : ℝ → ℝ} {a b t : ℝ} (hf : EulerDerivAt f a t) (hg : EulerDerivAt g b t) :
    EulerDerivAt (fun s => f s-g s) (a-b) t := by
  unfold EulerDerivAt at *
  convert! hf.sub hg using 1
  ring
private theorem eMul {f g : ℝ → ℝ} {a b t : ℝ} (hf : EulerDerivAt f a t) (hg : EulerDerivAt g b t) :
    EulerDerivAt (fun s => f s*g s) (a*g t+f t*b) t := by
  unfold EulerDerivAt at *
  convert! hf.mul hg using 1
  ring
private theorem eScale {f : ℝ → ℝ} {a t : ℝ} (hf : EulerDerivAt f a t) (r : ℝ) :
    EulerDerivAt (fun s => r*f s) (r*a) t := by
  unfold EulerDerivAt at *
  convert! hf.const_mul r using 1
  ring
private theorem eOfEvolution {f : ℝ → ℝ} {a b t : ℝ} (ht : t ≠ 0)
    (hf : HasDerivAt f a t) (hb : t*deriv f t=b) : EulerDerivAt f b t := by
  apply hf.congr_deriv
  rw [hf.deriv] at hb
  exact (eq_div_iff ht).mpr (by nlinarith only [hb])

/-- The next actual normalized source derivative in the Euler flow. -/
def curvatureShapeZeta (u t : ℝ) : ℝ := t^5*v u t/E u t

private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)

theorem hasDerivAt_curvatureShapeEpsilon (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (curvatureShapeEpsilon u)
      (((4-curvatureShapeAlpha u t)*curvatureShapeEpsilon u t+curvatureShapeZeta u t)/t) t := by
  have hd := (((hasDerivAt_id t).pow 4).mul (hasDerivAt_quadratureCurvatureThird u t)).div
    (hasDerivAt_completedDecayEvenPrimitive u t) (E_pos u ht).ne'
  convert! hd using 1
  dsimp only [id_eq,Pi.mul_apply,Pi.pow_apply]
  unfold curvatureShapeAlpha curvatureShapeEpsilon curvatureShapeZeta
  field_simp [ht.ne',(E_pos u ht).ne']
  ring

private def inverseSecondFlowKernel (Z a g b d ep ze : ℝ) : ℝ :=
  let x := a+b-a^2
  let y := (2-a)*b+d
  let vg := g*(1+a-2*g)
  let z := Z*(1+a)
  let dd := (3-a)*d+ep
  let xx := (1-2*a)*x+y
  let yy := -x*b+(2-a)*y+dd
  let vv := vg*(1+a-4*g)+g*x
  let zz := z*(1+a)+Z*x
  let ddd := -x*d+(3-a)*dd+(4-a)*ep+ze
  let D := 2*a+b
  let M := 3*b+d
  let A := 9+12*Z+16*g
  let P := 144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b
  let Dz := 2*x+y
  let Mz := 3*y+dd
  let Az := 12*z+16*vg
  let Pg := 384*Z+192*g+208
  let Pz := 288*Z+384*g+156
  let Pd := Pz*z+Pg*vg+5*x+25*y
  ((2*Pd+5*Dz)*x+(2*P+5*D)*xx+
    (Pd+25*Dz-15*Az)*y+(P+25*D-15*A)*yy+
    (Dz*Pg+D*(384*z+192*vg)-80*Mz)*vg+(D*Pg-80*M)*vv+
    (Dz*Pz+D*(288*z+384*vg)-60*Mz)*z+(D*Pz-60*M)*zz-
    5*Az*dd-5*A*ddd)/25

/-- Exact second Euler derivative of the normalized inverse reserve. -/
def normalizedInverseReserveSecondFlow (u t : ℝ) : ℝ :=
  inverseSecondFlowKernel (curvatureShapeAction u t) (curvatureShapeAlpha u t)
    (curvatureShapeGamma u t) (curvatureShapeBeta u t) (curvatureShapeDelta u t)
    (curvatureShapeEpsilon u t) (curvatureShapeZeta u t)

/-- Part of the second Euler flow independent of the fourth curvature. -/
def normalizedInverseReserveSecondCore (u t : ℝ) : ℝ :=
  inverseSecondFlowKernel (curvatureShapeAction u t) (curvatureShapeAlpha u t)
    (curvatureShapeGamma u t) (curvatureShapeBeta u t) (curvatureShapeDelta u t)
    (curvatureShapeEpsilon u t) 0

theorem normalizedInverseReserveSecondFlow_eq_core (u t : ℝ) :
    normalizedInverseReserveSecondFlow u t=normalizedInverseReserveSecondCore u t-
      ((9+12*curvatureShapeAction u t+16*curvatureShapeGamma u t)/5)*curvatureShapeZeta u t := by
  dsimp only [normalizedInverseReserveSecondFlow,normalizedInverseReserveSecondCore,inverseSecondFlowKernel]
  ring

theorem hasDerivAt_normalizedInverseReserveFlow (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (normalizedInverseReserveFlow u) (normalizedInverseReserveSecondFlow u t/t) t := by
  let Z := curvatureShapeAction u
  let a := curvatureShapeAlpha u
  let g := curvatureShapeGamma u
  let b := curvatureShapeBeta u
  let d := curvatureShapeDelta u
  let ep := curvatureShapeEpsilon u
  let ze := curvatureShapeZeta u
  let x := fun s => a s+b s-(a s)^2
  let y := fun s => (2-a s)*b s+d s
  let vg := fun s => g s*(1+a s-2*g s)
  let z := fun s => Z s*(1+a s)
  let dd := fun s => (3-a s)*d s+ep s
  have ha : EulerDerivAt a (x t) t := eOfEvolution ht.ne'
    (hasDerivAt_curvatureShapeAlpha u ht) (curvatureShapeAlpha_evolution u ht)
  have hb : EulerDerivAt b (y t) t := eOfEvolution ht.ne'
    (hasDerivAt_curvatureShapeBeta u ht) (curvatureShapeBeta_evolution u ht)
  have hg : EulerDerivAt g (vg t) t := eOfEvolution ht.ne'
    (hasDerivAt_curvatureShapeGamma u ht) (curvatureShapeGamma_evolution u ht)
  have hZ : EulerDerivAt Z (z t) t := eOfEvolution ht.ne'
    (hasDerivAt_mul_completedDecayEvenPrimitive u t) (curvatureShapeAction_evolution u ht)
  have hd : EulerDerivAt d (dd t) t := eOfEvolution ht.ne'
    (hasDerivAt_curvatureShapeDelta u ht) (curvatureShapeDelta_evolution u ht)
  have hep : EulerDerivAt ep ((4-a t)*ep t+ze t) t := hasDerivAt_curvatureShapeEpsilon u ht
  have hx : EulerDerivAt x ((1-2*a t)*x t+y t) t := by
    convert! eSub (eAdd ha hb) (eMul ha ha) using 1 <;> dsimp only [x] <;> ring
  have hy : EulerDerivAt y (-x t*b t+(2-a t)*y t+dd t) t := by
    convert! eAdd (eMul (eSub (eConst 2 t) ha) hb) hd using 1 <;> ring
  have hvg : EulerDerivAt vg (vg t*(1+a t-4*g t)+g t*x t) t := by
    convert! eMul hg (eSub (eAdd (eConst 1 t) ha) (eScale hg 2)) using 1 <;> ring
  have hz : EulerDerivAt z (z t*(1+a t)+Z t*x t) t := by
    convert! eMul hZ (eAdd (eConst 1 t) ha) using 1 <;> ring
  have hdd : EulerDerivAt dd (-x t*d t+(3-a t)*dd t+(4-a t)*ep t+ze t) t := by
    convert! eAdd (eMul (eSub (eConst 3 t) ha) hd) hep using 1 <;> ring
  let D := fun s => 2*a s+b s
  let M := fun s => 3*b s+d s
  let A := fun s => 9+12*Z s+16*g s
  let P := fun s => 144*(Z s)^2+384*Z s*g s+96*(g s)^2+156*Z s+208*g s-9+5*a s+25*b s
  let Pg := fun s => 384*Z s+192*g s+208
  let Pz := fun s => 288*Z s+384*g s+156
  let Dz := fun s => 2*x s+y s
  let Mz := fun s => 3*y s+dd s
  let Az := fun s => 12*z s+16*vg s
  let Pd := fun s => Pz s*z s+Pg s*vg s+5*x s+25*y s
  have hD : EulerDerivAt D (Dz t) t := eAdd (eScale ha 2) hb
  have hM : EulerDerivAt M (Mz t) t := eAdd (eScale hb 3) hd
  have hA : EulerDerivAt A (Az t) t := by
    convert! eAdd (eAdd (eConst 9 t) (eScale hZ 12)) (eScale hg 16) using 1 <;> ring
  have hP : EulerDerivAt P (Pd t) t := by
    have hh := eAdd (eAdd (eSub (eAdd (eAdd (eAdd (eAdd
      (eScale (eMul hZ hZ) 144) (eScale (eMul hZ hg) 384))
      (eScale (eMul hg hg) 96)) (eScale hZ 156)) (eScale hg 208)) (eConst 9 t))
      (eScale ha 5)) (eScale hb 25)
    convert! hh using 1 <;> dsimp only [P,Pd,Pg,Pz] <;> ring
  have hPg : EulerDerivAt Pg (384*z t+192*vg t) t := by
    convert! eAdd (eAdd (eScale hZ 384) (eScale hg 192)) (eConst 208 t) using 1 <;> ring
  have hPz : EulerDerivAt Pz (288*z t+384*vg t) t := by
    convert! eAdd (eAdd (eScale hZ 288) (eScale hg 384)) (eConst 156 t) using 1 <;> ring
  let Ca := fun s => 2*P s+5*D s
  let Cb := fun s => P s+25*D s-15*A s
  let Cg := fun s => D s*Pg s-80*M s
  let Cz := fun s => D s*Pz s-60*M s
  have hCa := eAdd (eScale hP 2) (eScale hD 5)
  have hCb := eSub (eAdd hP (eScale hD 25)) (eScale hA 15)
  have hCg := eSub (eMul hD hPg) (eScale hM 80)
  have hCz := eSub (eMul hD hPz) (eScale hM 60)
  have hh := eScale (eSub (eAdd (eAdd (eAdd (eMul hCa hx) (eMul hCb hy))
    (eMul hCg hvg)) (eMul hCz hz)) (eScale (eMul hA hdd) 5)) (1/25)
  unfold EulerDerivAt at hh
  convert! hh using 1
  · funext s
    dsimp only [normalizedInverseReserveFlow,Z,a,g,b,d,ep,x,y,vg,z,dd,D,M,A,P,Pg,Pz]
    ring
  · dsimp only [normalizedInverseReserveSecondFlow,inverseSecondFlowKernel,Z,a,g,b,d,ep,ze,x,y,vg,z,dd,D,M,A,P,Pg,Pz,Dz,Mz,Az,Pd]
    ring

theorem iteratedDeriv_two_normalizedActionInverseReserve (u : ℝ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (normalizedActionInverseReserve u) t=
      (normalizedInverseReserveSecondFlow u t-normalizedInverseReserveFlow u t)/t^2 := by
  have hd := (hasDerivAt_normalizedInverseReserveFlow u ht).div (hasDerivAt_id t) ht.ne'
  simp only [Pi.div_def,id_eq] at hd
  have he : deriv (normalizedActionInverseReserve u)=ᶠ[nhds t]
      (fun s => normalizedInverseReserveFlow u s/s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hasDerivAt_normalizedActionInverseReserve u hs).deriv
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq,hd.deriv]
  field_simp [ht.ne']
  ring


local notation "F" => intrinsicActionProfile
local notation "J" => intrinsicActionInverseSource
local notation "R" => normalizedActionInverseReserve
local notation "N" => normalizedInverseReserveFlow
local notation "N2" => normalizedInverseReserveSecondFlow
local notation "d" => completedLocalDenominator
local notation "d1" => descentDenominatorJet
local notation "k" => denominatorClockRate
private def inversePrefactor (u t : ℝ) : ℝ := F u t/(4*t^4)
private def inversePrefactorLogRate (u t : ℝ) : ℝ := actionProfileLogRate u t-4/t
private def inversePrefactorLogJet (u t : ℝ) : ℝ := actionProfileLogRateJet u t+4/t^2
local notation "G" => inversePrefactor
local notation "l" => inversePrefactorLogRate
local notation "lp" => inversePrefactorLogJet

private theorem prefactor_deriv (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (G u) (G u t*l u t) t := by
  have hh := (hasDerivAt_intrinsicActionProfile u ht).div
    (((hasDerivAt_id t).pow 4).const_mul 4) (by positivity : (4:ℝ)*t^4 ≠ 0)
  convert! hh using 1
  dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply]
  unfold inversePrefactor inversePrefactorLogRate
  field_simp [ht.ne']
  ring
private theorem prefactorLog_deriv (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (l u) (lp u t) t := by
  have hh := (hasDerivAt_actionProfileLogRate u ht).sub
    ((hasDerivAt_const t (4:ℝ)).div (hasDerivAt_id t) ht.ne')
  convert! hh using 1
  dsimp only [id_eq]
  unfold inversePrefactorLogJet
  ring
private theorem inverse_source_factor (u : ℝ) {t : ℝ} (ht : 0 < t) :
    J u t=G u t*R u t := by
  rw [intrinsicActionInverseSource_eq_normalized u ht]
  unfold inversePrefactor
  ring

theorem hasDerivAt_intrinsicActionInverseSource (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (J u) (G u t*(l u t*R u t+N u t/t)) t := by
  have hh := (prefactor_deriv u ht).mul (hasDerivAt_normalizedActionInverseReserve u ht)
  have he : J u=ᶠ[nhds t] (fun s => G u s*R u s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact inverse_source_factor u hs
  apply (hh.congr_of_eventuallyEq he).congr_deriv
  ring
private theorem inverseSourceJet_deriv (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => G u s*(l u s*R u s+N u s/s))
      (G u t*(((l u t)^2+lp u t)*R u t+2*l u t*N u t/t+(N2 u t-N u t)/t^2)) t := by
  have hh := (prefactor_deriv u ht).mul (((prefactorLog_deriv u ht).mul
    (hasDerivAt_normalizedActionInverseReserve u ht)).add
    ((hasDerivAt_normalizedInverseReserveFlow u ht).div (hasDerivAt_id t) ht.ne'))
  convert! hh using 1
  dsimp only [id_eq,Pi.mul_apply,Pi.add_apply,Pi.div_apply]
  field_simp [ht.ne']
  ring

theorem iteratedDeriv_two_intrinsicActionInverseSource (u : ℝ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (J u) t=
      G u t*(((l u t)^2+lp u t)*R u t+2*l u t*N u t/t+(N2 u t-N u t)/t^2) := by
  have he : deriv (J u)=ᶠ[nhds t] (fun s => G u s*(l u s*R u s+N u s/s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hasDerivAt_intrinsicActionInverseSource u hs).deriv
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  exact (inverseSourceJet_deriv u ht).deriv

/-- Complete actual normalized clock forcing, retaining every source term. -/
def intrinsicClockForce (u t : ℝ) : ℝ :=
  t^2*((l u t)^2+lp u t-(d1 u t/d u t)*l u t-(k u)^2*(d u t)^2)*R u t+
    (2*t*l u t-t*d1 u t/d u t-1)*N u t+N2 u t

/-- Exact second-order clock operator on the original inverse source. -/
theorem intrinsicClockForce_operator_identity (u : ℝ) {t : ℝ} (ht : 0 < t) :
    4*t^6*(iteratedDeriv 2 (J u) t-(d1 u t/d u t)*deriv (J u) t-
      (k u)^2*(d u t)^2*J u t)=F u t*intrinsicClockForce u t := by
  rw [iteratedDeriv_two_intrinsicActionInverseSource u ht,
    (hasDerivAt_intrinsicActionInverseSource u ht).deriv,inverse_source_factor u ht]
  unfold intrinsicClockForce inversePrefactor
  field_simp [ht.ne']
  ring

/-- The highest new derivative retains the exact affine source defect. -/
theorem curvatureShapeZeta_affine_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    curvatureShapeZeta u t < 166*t^2*curvatureShapeDelta u t-648*t^4*curvatureShapeAlpha u t := by
  have hE := E_pos u ht
  have hh := mul_lt_mul_of_pos_left (supersolutionCurvatureFourth_affine_upper ht.le htu)
    (show 0 < t^5/E u t by positivity)
  convert! hh using 1 <;> simp only [curvatureShapeZeta,curvatureShapeDelta,curvatureShapeAlpha] <;> ring



/-- Complete forcing with the actual affine fourth-curvature bound substituted.
This expression contains source derivatives only through order three. -/
def intrinsicClockAffineForce (u t : ℝ) : ℝ :=
  t^2*((l u t)^2+lp u t-(d1 u t/d u t)*l u t-(k u)^2*(d u t)^2)*R u t+
    (2*t*l u t-t*d1 u t/d u t-1)*N u t+normalizedInverseReserveSecondCore u t-
    ((9+12*curvatureShapeAction u t+16*curvatureShapeGamma u t)/5)*
      (166*t^2*curvatureShapeDelta u t-648*t^4*curvatureShapeAlpha u t)

/-- The actual complete source strictly exceeds the explicit lower-jet forcing.
No sign assumption on a source jet or on the remaining forcing is used. -/
theorem intrinsicClockForce_gt_affine {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    intrinsicClockAffineForce u t < intrinsicClockForce u t := by
  have hE := E_pos u ht
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hA : 0 < (9+12*curvatureShapeAction u t+16*curvatureShapeGamma u t)/5 := by
    unfold curvatureShapeAction curvatureShapeGamma
    positivity
  have hh := mul_lt_mul_of_pos_left (curvatureShapeZeta_affine_upper ht htu) hA
  unfold intrinsicClockForce intrinsicClockAffineForce
  rw [normalizedInverseReserveSecondFlow_eq_core]
  linarith only [hh]


local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "Q" => thetaCuspReflectedLogAction
private theorem p_nonneg (u : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ p u t := by
  unfold shapeCurvatureSlope
  exact div_nonneg (sub_nonneg.mpr
    (thetaCuspLogCurvatureJet_strictMono.monotone (by linarith))) (by norm_num)
private theorem hp_deriv (u t : ℝ) : HasDerivAt (p u) (r u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring
private theorem r_pos (u t : ℝ) : 0 < r u t := by
  unfold shapeCurvatureSecond
  exact div_pos (add_pos (thetaCuspLogCurvatureJetTwo_pos_all (u+t))
    (thetaCuspLogCurvatureJetTwo_pos_all (u-t))) (by norm_num)
private theorem r_upper {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) : r u t < 9*e u t := by
  have hp := source_projective_upper (show 0 ≤ u+t by linarith)
  have hm := source_projective_upper (show 0 ≤ u-t by linarith)
  unfold shapeCurvatureSecond completedCurvatureEven
  linarith

private theorem chamber_nonneg {f g : ℝ → ℝ} {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u)
    (h0 : f 0=0) (hd : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, 0 < s → s < u → 0 ≤ g s) : 0 ≤ f t := by
  have hm : MonotoneOn f (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 u := by simpa only [interior_Icc] using hs
      rw [(hd s).deriv]
      exact hg s hs'.1 hs'.2
  simpa only [h0] using hm ⟨le_rfl,ht.trans htu⟩ ⟨ht,htu⟩ ht

private theorem alpha_lower {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : 1 ≤ curvatureShapeAlpha u t := by
  have hd (s : ℝ) : HasDerivAt (fun s => s*e u s-E u s) (s*p u s) s := by
    convert! ((hasDerivAt_id s).mul (hasDerivAt_completedCurvatureEven u s)).sub
      (hasDerivAt_completedDecayEvenPrimitive u s) using 1
    dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    change s*p u s=1*e u s+s*p u s-e u s
    ring
  have hh : 0 ≤ t*e u t-E u t := by
    apply chamber_nonneg ht.le htu (by simp [completedDecayEvenPrimitive_zero]) hd
    intro s hs _; exact mul_nonneg hs.le (p_nonneg u hs.le)
  unfold curvatureShapeAlpha
  exact (le_div_iff₀ (E_pos u ht)).mpr (by linarith only [hh])

private theorem action_lower {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : 18*t^2 ≤ curvatureShapeAction u t := by
  have hd (s : ℝ) : HasDerivAt (fun s => E u s-18*s) (e u s-18) s := by
    convert! (hasDerivAt_completedDecayEvenPrimitive u s).sub ((hasDerivAt_id s).const_mul 18) using 1
    ring
  have hh : 0 ≤ E u t-18*t := by
    apply chamber_nonneg ht.le htu (by simp [completedDecayEvenPrimitive_zero]) hd
    intro s hs hsu
    have hp := sourceCurvature_gt_eighteen (show 0 ≤ u+s by linarith)
    have hm := sourceCurvature_gt_eighteen (show 0 ≤ u-s by linarith)
    unfold completedCurvatureEven
    linarith
  have hmul := mul_nonneg ht.le hh
  unfold curvatureShapeAction
  nlinarith only [hmul]

private theorem beta_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : curvatureShapeBeta u t ≤ 9*t^2 := by
  have hd (s : ℝ) : HasDerivAt (fun s => 9*E u s-p u s) (9*e u s-r u s) s :=
    ((hasDerivAt_completedDecayEvenPrimitive u s).const_mul 9).sub (hp_deriv u s)
  have hh : 0 ≤ 9*E u t-p u t := by
    apply chamber_nonneg ht.le htu (by simp [completedDecayEvenPrimitive_zero,shapeCurvatureSlope]) hd
    intro s hs hsu; exact sub_nonneg.mpr (r_upper hs.le hsu.le).le
  unfold curvatureShapeBeta
  apply (div_le_iff₀ (E_pos u ht)).mpr
  have hmul := mul_nonneg (sq_nonneg t) hh
  nlinarith only [hmul]

private theorem gamma_bounds {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    1 ≤ curvatureShapeGamma u t ∧ curvatureShapeGamma u t ≤ curvatureShapeAlpha u t := by
  have hE := E_pos u ht
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hg0 : 0 < curvatureShapeGamma u t := by unfold curvatureShapeGamma; positivity
  have ha := alpha_lower ht htu
  constructor
  · have hh := two_mul_action_le_velocity_of_jetTwo_nonneg ht htu
      (fun x _ => (thetaCuspLogCurvatureJetTwo_pos_all x).le)
    unfold thetaCuspReflectedActionVelocity at hh
    rw [show thetaCuspReflectedLogJetOne u t=2*E u t by rw [completedDecayEvenPrimitive_eq]; ring] at hh
    unfold curvatureShapeGamma
    exact (le_div_iff₀ hQ).mpr (by linarith only [hh])
  · have hd : 0 < t*deriv (curvatureShapeGamma u) t := by
      rw [(hasDerivAt_curvatureShapeGamma u ht).deriv]
      exact mul_pos ht (div_pos (curvatureShapeGamma_current_pos ht htu) (sq_pos_of_pos hQ))
    rw [curvatureShapeGamma_evolution u ht] at hd
    have hinner : 0 < 1+curvatureShapeAlpha u t-2*curvatureShapeGamma u t := by
      by_contra hn
      have hh := mul_nonpos_of_nonneg_of_nonpos hg0.le (le_of_not_gt hn)
      linarith only [hd,hh]
    linarith only [ha,hinner]

private theorem normalized_denominator_budget {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    3*curvatureShapeBeta u t+curvatureShapeDelta u t <
      (2*curvatureShapeAlpha u t+curvatureShapeBeta u t)*(1+3*curvatureShapeAction u t/8) := by
  have hh := mul_lt_mul_of_pos_left (actionProfile_denominator_budget ht htu) (div_pos ht (E_pos u ht))
  unfold curvatureShapeBeta curvatureShapeDelta curvatureShapeAlpha curvatureShapeAction
  convert! hh using 1 <;>
    dsimp [descentDenominatorJet,completedLocalDenominator,shapeCurvatureSlope,shapeCurvatureSecond] <;>
    field_simp [(E_pos u ht).ne']

private def inverseFirstFlowKernel (Z a g b q ep : ℝ) : ℝ :=
  let D := 2*a+b
  let M := 3*b+q
  let A := 9+12*Z+16*g
  let P := 144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b
  ((2*P+5*D)*(a+b-a^2)+(P+25*D-15*A)*((2-a)*b+q)+
    (D*(384*Z+192*g+208)-80*M)*(g*(1+a-2*g))+
    (D*(288*Z+384*g+156)-60*M)*Z*(1+a)-5*A*((3-a)*q+ep))/25

/-- Algebraic form of the full clock forcing, with its actual clock mass retained. -/
def intrinsicClockForceKernel (Z a g b q ep ze kap : ℝ) : ℝ :=
  let D := 2*a+b
  let M := 3*b+q
  let A := 9+12*Z+16*g
  let P := A/5-4
  let Adot := 12*Z*(1+a)+16*g*(1+a-2*g)
  let Rp := D*(144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b)/25-M*A/5
  (P^2-P+Adot/5-(M/D)*P-kap)*Rp+
    (2*P-1-M/D)*inverseFirstFlowKernel Z a g b q ep+
    inverseSecondFlowKernel Z a g b q ep ze

/-- The coefficient of the third curvature derivative in the complete operator. -/
def inverseClockThirdCoefficient (Z a g b q : ℝ) : ℝ :=
  let D := 2*a+b
  let M := 3*b+q
  let A := 9+12*Z+16*g
  let Adot := 12*Z*(1+a)+16*g*(1+a-2*g)
  let P := 144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b
  (P+25*D-15*A)/25-2*Adot/5-(A/5)*(2*A/5-2-2*a-M/D)

theorem intrinsicClockForceKernel_third_difference (Z a g b q ep ep' ze kap : ℝ) :
    intrinsicClockForceKernel Z a g b q ep ze kap-
      intrinsicClockForceKernel Z a g b q ep' ze kap=
        inverseClockThirdCoefficient Z a g b q*(ep-ep') := by
  dsimp only [intrinsicClockForceKernel,inverseFirstFlowKernel,inverseSecondFlowKernel,
    inverseClockThirdCoefficient]
  ring

private theorem thirdCoefficient_neg {t Z a g b q : ℝ}
    (ht : 0 < t) (hZ : 18*t^2 ≤ Z) (hg : 1 ≤ g) (ha : a ≤ 2+t^2)
    (hb : b ≤ 9*t^2) (hD : 0 < 2*a+b)
    (hM : 3*b+q < (2*a+b)*(1+3*Z/8)) :
    inverseClockThirdCoefficient Z a g b q < 0 := by
  have hZ0 : 0 < Z := (mul_pos (by norm_num) (sq_pos_of_pos ht)).trans_le hZ
  have hA : 0 < 9+12*Z+16*g := by linarith
  have hratio : (3*b+q)/(2*a+b)<1+3*Z/8 :=
    (div_lt_iff₀ hD).mpr (by simpa only [mul_comm] using hM)
  have hpay := mul_lt_mul_of_pos_left hratio (show 0 < 5*(9+12*Z+16*g) by positivity)
  have hid : 25*inverseClockThirdCoefficient Z a g b q-
      5*(9+12*Z+16*g)*((3*b+q)/(2*a+b)-(1+3*Z/8))=
      -(243/2)*Z^2-354*Z*g-96*g^2-(3033/8)*Z-528*g+145*a+50*b-171 := by
    dsimp only [inverseClockThirdCoefficient]
    ring
  have hZg : Z ≤ Z*g := by nlinarith only [mul_nonneg hZ0.le (sub_nonneg.mpr hg)]
  have hg2 : 1 ≤ g^2 := by nlinarith only [sq_nonneg (g-1),hg]
  have hupper : -(243/2)*Z^2-354*Z*g-96*g^2-(3033/8)*Z-528*g+145*a+50*b-171<0 := by
    nlinarith only [sq_nonneg Z,hZg,hg2,hg,ha,hb,hZ,sq_nonneg t]
  linarith only [hid,hpay,hupper]

/-- The third-source coefficient is strictly negative on the actual physical chamber. -/
theorem inverseClockThirdCoefficient_neg {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    inverseClockThirdCoefficient (curvatureShapeAction u t) (curvatureShapeAlpha u t)
      (curvatureShapeGamma u t) (curvatureShapeBeta u t) (curvatureShapeDelta u t)<0 := by
  have ha := curvatureShapeAlpha_lt ht htu
  have ha' : curvatureShapeAlpha u t ≤ 2+t^2 := by nlinarith only [ha,sq_nonneg (t-1)]
  have hapos : 0 < curvatureShapeAlpha u t := by
    unfold curvatureShapeAlpha
    exact div_pos (mul_pos ht (completedCurvatureEven_pos u t)) (E_pos u ht)
  have hbpos : 0 ≤ curvatureShapeBeta u t := by
    unfold curvatureShapeBeta
    exact div_nonneg (mul_nonneg (sq_nonneg t) (p_nonneg u ht.le)) (E_pos u ht).le
  exact thirdCoefficient_neg ht (action_lower ht htu) (gamma_bounds ht htu).1 ha'
    (beta_upper ht htu) (by positivity) (normalized_denominator_budget ht htu)

private theorem prefactorLog_scaled (u : ℝ) {t : ℝ} (ht : 0 < t) :
    t*l u t=(9+12*curvatureShapeAction u t+16*curvatureShapeGamma u t)/5-4 := by
  unfold inversePrefactorLogRate actionProfileLogRate curvatureShapeAction curvatureShapeGamma
  field_simp [ht.ne']

private theorem prefactorLogJet_scaled (u : ℝ) {t : ℝ} (ht : 0 < t) :
    t^2*lp u t=
      (12*curvatureShapeAction u t*(1+curvatureShapeAlpha u t)+
        16*curvatureShapeGamma u t*(1+curvatureShapeAlpha u t-2*curvatureShapeGamma u t))/5-
      ((9+12*curvatureShapeAction u t+16*curvatureShapeGamma u t)/5-4) := by
  unfold inversePrefactorLogJet actionProfileLogRateJet curvatureShapeAction curvatureShapeAlpha curvatureShapeGamma
  field_simp [ht.ne',(E_pos u ht).ne',(thetaCuspReflectedLogAction_pos (u := u) ht).ne']
  <;> ring

private theorem denominatorJet_scaled (u : ℝ) {t : ℝ} (ht : 0 < t) :
    t*d1 u t/d u t=(3*curvatureShapeBeta u t+curvatureShapeDelta u t)/
      (2*curvatureShapeAlpha u t+curvatureShapeBeta u t) := by
  have hh : 2*curvatureShapeAlpha u t+curvatureShapeBeta u t=t*d u t/E u t := by
    dsimp only [curvatureShapeAlpha,curvatureShapeBeta,completedLocalDenominator,shapeCurvatureSlope]
    ring
  rw [hh]
  dsimp only [curvatureShapeBeta,curvatureShapeDelta,descentDenominatorJet,shapeCurvatureSlope,shapeCurvatureSecond]
  field_simp [ht.ne',(E_pos u ht).ne',(completedLocalDenominator_pos_nonneg u ht.le).ne']

theorem intrinsicClockForce_eq_kernel (u : ℝ) {t : ℝ} (ht : 0 < t) :
    intrinsicClockForce u t=intrinsicClockForceKernel
      (curvatureShapeAction u t) (curvatureShapeAlpha u t) (curvatureShapeGamma u t)
      (curvatureShapeBeta u t) (curvatureShapeDelta u t) (curvatureShapeEpsilon u t)
      (curvatureShapeZeta u t) (t^2*(k u)^2*(d u t)^2) := by
  have h1 := prefactorLog_scaled u ht
  have h2 := prefactorLogJet_scaled u ht
  have h3 := denominatorJet_scaled u ht
  unfold intrinsicClockForce intrinsicClockForceKernel
  rw [normalizedActionInverseReserve_polynomial u ht]
  have h4 : N u t=inverseFirstFlowKernel (curvatureShapeAction u t) (curvatureShapeAlpha u t)
      (curvatureShapeGamma u t) (curvatureShapeBeta u t) (curvatureShapeDelta u t)
      (curvatureShapeEpsilon u t) := rfl
  rw [h4]
  unfold normalizedInverseReserveSecondFlow
  have hc : t^2*((l u t)^2+lp u t-(d1 u t/d u t)*l u t-(k u)^2*(d u t)^2)=
      ((t*l u t)^2+t^2*lp u t-(t*d1 u t/d u t)*(t*l u t)-t^2*(k u)^2*(d u t)^2) := by ring
  have hc' : 2*t*l u t-t*d1 u t/d u t-1=2*(t*l u t)-1-t*d1 u t/d u t := by ring
  rw [hc,hc',h1,h2,h3]
  ring

/-- A complete lower forcing involving curvature only through its second derivative.
The actual center-dependent clock mass is retained. -/
def intrinsicClockSecondSourceForce (u t : ℝ) : ℝ :=
  intrinsicClockForceKernel (curvatureShapeAction u t) (curvatureShapeAlpha u t)
    (curvatureShapeGamma u t) (curvatureShapeBeta u t) (curvatureShapeDelta u t)
    (166*t^2*curvatureShapeBeta u t-648*t^4)
    (166*t^2*curvatureShapeDelta u t-648*t^4*curvatureShapeAlpha u t)
    (t^2*(k u)^2*(d u t)^2)

theorem intrinsicClockForce_gt_secondSource {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    intrinsicClockSecondSourceForce u t < intrinsicClockForce u t := by
  have hep := curvatureShapeEpsilon_affine_upper ht htu
  have hze := curvatureShapeZeta_affine_upper ht htu
  have hc := inverseClockThirdCoefficient_neg ht htu
  have hA : 0 < (9+12*curvatureShapeAction u t+16*curvatureShapeGamma u t)/5 := by
    unfold curvatureShapeAction curvatureShapeGamma
    have hE := E_pos u ht
    have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
    positivity
  have hp := mul_pos_of_neg_of_neg hc (sub_neg.mpr hep)
  have hz := mul_pos hA (sub_pos.mpr hze)
  rw [intrinsicClockForce_eq_kernel u ht]
  unfold intrinsicClockSecondSourceForce
  have hi := intrinsicClockForceKernel_third_difference
    (curvatureShapeAction u t) (curvatureShapeAlpha u t) (curvatureShapeGamma u t)
    (curvatureShapeBeta u t) (curvatureShapeDelta u t) (curvatureShapeEpsilon u t)
    (166*t^2*curvatureShapeBeta u t-648*t^4) (curvatureShapeZeta u t)
    (t^2*(k u)^2*(d u t)^2)
  have hzid : intrinsicClockForceKernel (curvatureShapeAction u t) (curvatureShapeAlpha u t)
      (curvatureShapeGamma u t) (curvatureShapeBeta u t) (curvatureShapeDelta u t)
      (166*t^2*curvatureShapeBeta u t-648*t^4) (curvatureShapeZeta u t)
      (t^2*(k u)^2*(d u t)^2)-intrinsicClockSecondSourceForce u t=
      ((9+12*curvatureShapeAction u t+16*curvatureShapeGamma u t)/5)*
        (166*t^2*curvatureShapeDelta u t-648*t^4*curvatureShapeAlpha u t-curvatureShapeZeta u t) := by
    dsimp only [intrinsicClockForceKernel,intrinsicClockSecondSourceForce,inverseSecondFlowKernel]
    ring
  unfold intrinsicClockSecondSourceForce at hzid
  linarith only [hi,hzid,hp,hz]

end
end RHTower.ThetaCuspDefect
