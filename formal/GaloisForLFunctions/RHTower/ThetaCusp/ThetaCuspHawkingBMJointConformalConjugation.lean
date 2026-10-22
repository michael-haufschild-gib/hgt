import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointConformalJetContraction

/-! Exact conjugation of the actual joint wave to a Euclidean inverse-square-potential equation. -/
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMJointConformal
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def liftedField (F : Point3 → ℂ) (p : Point3) : ℂ := weight p*F (chart p)

def jointSpatial (U : Point3 → ℂ) (p : Point3) : ℂ :=
  ∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*coordDeriv i (coordDeriv i U) p

def flatLaplacian (F : Point3 → ℂ) (p : Point3) : ℂ :=
  ∑ i : Fin 3, coordDeriv i (coordDeriv i F) p

theorem liftedField_smooth (F : Point3 → ℂ) (p : Point3) (hp : 0 < p 2)
    (hF : ContDiffAt ℝ 2 F (chart p)) : ContDiffAt ℝ 2 (liftedField F) p :=
  ((contDiffAt_infty.mp (weight_smooth p hp)) 2).mul
    (hF.comp p (((contDiff_infty.mp chart_smooth) 2).contDiffAt))

/-- Each weighted coordinate second derivative uses the actual chart and field jets. -/
theorem liftedField_second (F : Point3 → ℂ) (p : Point3) (hp : 0 < p 2)
    (hF : ContDiffAt ℝ 2 F (chart p)) (i : Fin 3) :
    coordDeriv i (coordDeriv i (liftedField F)) p =
      weightSecond p i*F (chart p)+2*weightFirst p i*(fderiv ℝ F (chart p) (chartFirst p i))+
      weight p*((fderiv ℝ (fderiv ℝ F) (chart p)) (chartFirst p i) (chartFirst p i)+
        fderiv ℝ F (chart p) (chartSecond p i)) := by
  rw [coordinate_secondDerivative _ p i (liftedField_smooth F p hp hF)]
  have hline : ContDiffAt ℝ 2 (coordinateLine p i) (p i) :=
    ((contDiff_infty.mp (coordinateLine_smooth p i)) 2).contDiffAt
  have hm : ContDiffAt ℝ 2 (fun s => weight (coordinateLine p i s)) (p i) := by
    have hm0 : ContDiffAt ℝ 2 weight (coordinateLine p i (p i)) := by
      simpa [coordinateLine_base] using (contDiffAt_infty.mp (weight_smooth p hp)) 2
    exact hm0.comp (p i) hline
  have hg : ContDiffAt ℝ 2 (fun s => chart (coordinateLine p i s)) (p i) :=
    ((contDiff_infty.mp chart_smooth) 2).contDiffAt.comp _ hline
  have he := weightedCurve_second F (fun s => weight (coordinateLine p i s))
    (fun s => chart (coordinateLine p i s)) (p i)
    (by simpa [coordinateLine_base] using hF) hm hg
  rw [(weightCurve_derivatives p hp i).1,(weightCurve_derivatives p hp i).2,
    (chartCurve_derivatives p i).1,(chartCurve_derivatives p i).2,coordinateLine_base] at he
  exact he

/-- The Frechet Hessian trace equals the actual coordinate Laplacian. -/
theorem flatLaplacian_hessian (F : Point3 → ℂ) (p : Point3) (hF : ContDiffAt ℝ 2 F p) :
    flatLaplacian F p = ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ F) p) (Pi.single i 1) (Pi.single i 1) := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L => L (Pi.single i 1)) (coordDeriv_hasFDerivAt hF i).fderiv

/-- The original joint spatial differential expression loses every drift term and gains exactly
one quarter under the actual nonzero field weight and Euclidean chart. -/
theorem jointSpatial_conjugation (F : Point3 → ℂ) (p : Point3) (hp : 0 < p 2)
    (hF : ContDiffAt ℝ 2 F (chart p)) :
    jointSpatial (liftedField F) p =
      weight p*((chart p 1:ℂ)^(2 : ℕ)*flatLaplacian F (chart p)+F (chart p)/4) := by
  let L := fderiv ℝ F (chart p)
  let B := fderiv ℝ (fderiv ℝ F) (chart p)
  have hd := drift_contraction p hp L
  have hb := principal_contraction p B
  have hc : (∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*(secondRatio p i:ℂ)) = 1/4 := by
    have hr := congrArg Complex.ofReal (chart_potential p hp)
    push_cast at hr
    exact hr
  rw [flatLaplacian_hessian F (chart p) hF]
  unfold jointSpatial
  simp_rw [liftedField_second F p hp hF,weightFirst_ratio,weightSecond_ratio]
  change (∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*
    (weight p*(secondRatio p i:ℂ)*F (chart p)+2*(weight p*(firstRatio p i:ℂ))*L (chartFirst p i)+
      weight p*(B (chartFirst p i) (chartFirst p i)+L (chartSecond p i)))) = _
  have he : (∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*
      (weight p*(secondRatio p i:ℂ)*F (chart p)+2*(weight p*(firstRatio p i:ℂ))*L (chartFirst p i)+
        weight p*(B (chartFirst p i) (chartFirst p i)+L (chartSecond p i)))) =
      weight p*((∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*(secondRatio p i:ℂ))*F (chart p)+
        (∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*(2*(firstRatio p i:ℂ)*L (chartFirst p i)+L (chartSecond p i)))+
        (∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*B (chartFirst p i) (chartFirst p i))) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    ring
  rw [he,hc,hd,hb]
  dsimp only [B]
  ring

/-- The independent-frequency wave becomes the exact Euclidean inverse-square-potential equation. -/
theorem jointWave_conjugation (F : Point3 → ℂ) (w : ℂ) (p : Point3) (hp : 0 < p 2)
    (hF : ContDiffAt ℝ 2 F (chart p)) :
    w^(2 : ℕ)*liftedField F p-jointSpatial (liftedField F) p =
      weight p*((w^(2 : ℕ)-1/4)*F (chart p)-(chart p 1:ℂ)^(2 : ℕ)*flatLaplacian F (chart p)) := by
  rw [jointSpatial_conjugation F p hp hF,liftedField]
  ring

end
end RHTower.D4BMJointConformal
