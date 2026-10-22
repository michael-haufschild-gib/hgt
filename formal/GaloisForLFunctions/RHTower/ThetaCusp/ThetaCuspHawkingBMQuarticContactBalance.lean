import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSquareCuspJets
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules

/-! Exact pointwise contact balance of the complete theta source.
The proof uses the actual scalar equation and two-jet product rule, retaining
both Laplacians of the spin-two source and the bilinear contact gradient.
Pointwise elimination keeps source fields opaque inside unmatched derivatives. -/

open Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMQuarticContactBalance
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMSquareCuspJets
noncomputable section
set_option autoImplicit false

private abbrev Field := (Fin 2 → ℝ) → ℂ
private def gamma (f g : Field) (z : Fin 2 → ℝ) : ℂ :=
  (z 1:ℂ)^(2 : ℕ)*(coordDeriv 0 f z*coordDeriv 0 g z+coordDeriv 1 f z*coordDeriv 1 g z)

private theorem lap_mul {f g : Field} {z : Fin 2 → ℝ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    hyperbolicLaplacian (fun w => f w*g w) z=
      f z*hyperbolicLaplacian g z+g z*hyperbolicLaplacian f z+2*gamma f g z := by
  change (z 1:ℂ)^(2 : ℕ)*((ofField (fun w => f w*g w) z).second 0 0+
    (ofField (fun w => f w*g w) z).second 1 1)=_
  rw [ofField_mul hf hg]
  simp only [ScalarTwoJet.mul,ofField,hyperbolicLaplacian,gamma]
  ring

private theorem half_square_first {f : Field} {z : Fin 2 → ℝ}
    (hf : ContDiffAt ℝ 2 f z) (i : Fin 2) :
    coordDeriv i (fun w => (1/2:ℂ)*(f w*f w)) z=f z*coordDeriv i f z := by
  have hj := ofField_mul contDiffAt_const (hf.mul hf)
    (f := fun _ : Fin 2 → ℝ => (1/2:ℂ))
  rw [ofField_constant,ofField_mul hf hf] at hj
  have h := congrArg (fun J => J.first i) hj
  simp only [ScalarTwoJet.mul,ofField,constant] at h
  linear_combination h

private theorem lap_smooth {f : Field} {z : Fin 2 → ℝ}
    (hf : ContDiffAt ℝ 4 f z) : ContDiffAt ℝ 2 (hyperbolicLaplacian f) z := by
  have h₁ (i : Fin 2) : ContDiffAt ℝ 3 (coordDeriv i f) z :=
    coordDeriv_contDiffAt hf (by norm_num) i
  have h₂ (i : Fin 2) : ContDiffAt ℝ 2 (coordDeriv i (coordDeriv i f)) z :=
    coordDeriv_contDiffAt (h₁ i) (by norm_num) i
  have hy : ContDiffAt ℝ 2 (fun w : Fin 2 → ℝ => (w 1:ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
  exact (hy.pow 2).mul ((h₂ 0).add (h₂ 1))

private def thetaField (u : ℂ) : Field := fun z =>
  d4BMCompletedEisensteinCuspLeg .scalar u (z 0) (z 1)
private def Qfield (u : ℂ) : Field := fun z => (1/2:ℂ)*(thetaField u z*thetaField u z)
private def Jfield (u : ℂ) : Field := fun z =>
  (1/8:ℂ)*((7*(u^(2 : ℕ)-1/4)-2)*Qfield u z+(-2)*hyperbolicLaplacian (Qfield u) z)
private def Rfield (u : ℂ) : Field := fun z =>
  (-1)*hyperbolicLaplacian (hyperbolicLaplacian (Qfield u)) z+
    2*hyperbolicLaplacian (Qfield u) z
private def Hfield (u : ℂ) : Field := fun z =>
  2*(Jfield u z*Jfield u z)+
    ((7*(u^(2 : ℕ)-1/4)-2)*((7*(u^(2 : ℕ)-1/4)-2)-4)/96)*(Qfield u z*Qfield u z)

private theorem Q_smooth (u : ℂ) (z : Fin 2 → ℝ) (hz : 0<z 1) (n : ℕ) :
    ContDiffAt ℝ n (Qfield u) z :=
  contDiffAt_const.mul ((cuspLeg_contDiffAt .scalar u n z hz).mul
    (cuspLeg_contDiffAt .scalar u n z hz))
private theorem J_smooth (u : ℂ) (z : Fin 2 → ℝ) (hz : 0<z 1) :
    ContDiffAt ℝ 2 (Jfield u) z :=
  contDiffAt_const.mul ((contDiffAt_const.mul (Q_smooth u z hz 2)).add
    (contDiffAt_const.mul (lap_smooth (Q_smooth u z hz 4))))

private theorem Q_square_equation (u : ℂ) (z : Fin 2 → ℝ) (hz : 0<z 1) :
    hyperbolicLaplacian (fun w => Qfield u w*Qfield u w) z=
      6*Qfield u z*hyperbolicLaplacian (Qfield u) z-8*(u^(2 : ℕ)-1/4)*(Qfield u z)^(2 : ℕ) := by
  have hf : ContDiffAt ℝ 2 (thetaField u) z := cuspLeg_contDiffAt .scalar u 2 z hz
  have hE : hyperbolicLaplacian (thetaField u) z=(u^(2 : ℕ)-1/4)*thetaField u z :=
    scalarCusp_hyperbolicLaplacian u z hz
  have hQ : hyperbolicLaplacian (Qfield u) z=
      (u^(2 : ℕ)-1/4)*(thetaField u z)^(2 : ℕ)+gamma (thetaField u) (thetaField u) z := by
    unfold Qfield
    rw [hyperbolicLaplacian_const_mul (hf.mul hf),lap_mul hf hf,hE]
    ring
  have hG : gamma (Qfield u) (Qfield u) z=
      (thetaField u z)^(2 : ℕ)*gamma (thetaField u) (thetaField u) z := by
    unfold gamma Qfield
    rw [half_square_first hf,half_square_first hf]
    ring
  rw [lap_mul (Q_smooth u z hz 2) (Q_smooth u z hz 2),hG,hQ]
  unfold Qfield
  ring

private theorem Q_contact_equation (u : ℂ) (z : Fin 2 → ℝ) (hz : 0<z 1) :
    24*Qfield u z*Jfield u z=
      (13*(u^(2 : ℕ)-1/4)-6)*(Qfield u z*Qfield u z)-
        hyperbolicLaplacian (fun w => Qfield u w*Qfield u w) z := by
  rw [Q_square_equation u z hz]
  unfold Jfield
  ring

private theorem J_laplacian (u : ℂ) (z : Fin 2 → ℝ) (hz : 0<z 1) :
    hyperbolicLaplacian (Jfield u) z=
      (1/8:ℂ)*((7*(u^(2 : ℕ)-1/4)-2)*hyperbolicLaplacian (Qfield u) z+
        (-2)*hyperbolicLaplacian (hyperbolicLaplacian (Qfield u)) z) := by
  have hq := Q_smooth u z hz 2
  have hl := lap_smooth (Q_smooth u z hz 4)
  unfold Jfield
  rw [hyperbolicLaplacian_const_mul ((contDiffAt_const.mul hq).add (contDiffAt_const.mul hl)),
    hyperbolicLaplacian_add (contDiffAt_const.mul hq) (contDiffAt_const.mul hl),
    hyperbolicLaplacian_const_mul hq,hyperbolicLaplacian_const_mul hl]

private theorem H_laplacian (u : ℂ) (z : Fin 2 → ℝ) (hz : 0<z 1) :
    hyperbolicLaplacian (Hfield u) z=
      2*hyperbolicLaplacian (fun w => Jfield u w*Jfield u w) z+
        ((7*(u^(2 : ℕ)-1/4)-2)*((7*(u^(2 : ℕ)-1/4)-2)-4)/96)*
          hyperbolicLaplacian (fun w => Qfield u w*Qfield u w) z := by
  have hq := Q_smooth u z hz 2
  have hj := J_smooth u z hz
  unfold Hfield
  rw [hyperbolicLaplacian_add (contDiffAt_const.mul (hj.mul hj))
      (contDiffAt_const.mul (hq.mul hq)),
    hyperbolicLaplacian_const_mul (hj.mul hj),hyperbolicLaplacian_const_mul (hq.mul hq)]

private theorem R_laplacian (u : ℂ) (z : Fin 2 → ℝ) (hz : 0<z 1) :
    Rfield u z = 4*hyperbolicLaplacian (Jfield u) z+
      2*((7*(u^(2 : ℕ)-1/4)-2)-4)*Jfield u z-
      ((7*(u^(2 : ℕ)-1/4)-2)*((7*(u^(2 : ℕ)-1/4)-2)-4)/4)*Qfield u z := by
  rw [J_laplacian u z hz]
  unfold Rfield Jfield
  ring

/-- Literal theta-field contact balance, with both retained spin-two Laplacians. -/
private theorem theta_contact_balance (u : ℂ) (z : UpperHalfPlane) :
    let p : Fin 2 → ℝ := ![z.re,z.im]
    let c := 7*(u^(2 : ℕ)-1/4)-2
    let a := c*(c-4)/96
    Jfield u p*Rfield u p=
      hyperbolicLaplacian (Hfield u) p+2*(c-4)*(Jfield u p*Jfield u p)-
        4*((1/2:ℂ)*hyperbolicLaplacian (fun w => Jfield u w*Jfield u w) p+
          (-1)*(Jfield u p*hyperbolicLaplacian (Jfield u) p))-
        a*(13*(u^(2 : ℕ)-1/4)-6)*(Qfield u p*Qfield u p) := by
  let p : Fin 2 → ℝ := ![z.re,z.im]
  have hz : 0<p 1 := z.im_pos
  dsimp only
  rw [H_laplacian u _ hz,R_laplacian u _ hz]
  have hq := Q_contact_equation u p hz
  have hq' : hyperbolicLaplacian (fun w => Qfield u w*Qfield u w) p=
      (13*(u^(2 : ℕ)-1/4)-6)*(Qfield u p*Qfield u p)-24*Qfield u p*Jfield u p := by
    linear_combination hq
  rw [hq']
  ring

/-- Exact complete-theta contact balance in the original six quartic fields.
Both retained spin-two Laplacians and the complex bilinear gradient survive. -/
theorem quarticContactField_balance (q : XiZeroCopy) (z : UpperHalfPlane) :
    let c := 7*((center q)^(2 : ℕ)-1/4)-2
    let a := c*(c-4)/96
    quarticContactField q 3 (coordinates z)=
      quarticContactField q 5 (coordinates z)+
        2*(c-4)*quarticContactField q 1 (coordinates z)-
        4*quarticContactField q 2 (coordinates z)-
        a*(13*((center q)^(2 : ℕ)-1/4)-6)*quarticContactField q 0 (coordinates z) := by
  exact theta_contact_balance (center q) z

end
end RHTower.D4BMQuarticContactBalance
