import GaloisForLFunctions.HTGeometry.CoordinateEinsteinActionVariation
import GaloisForLFunctions.HTGeometry.ComplexMatrixDerivativeRules

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace GaloisForLFunctions.HTGeometry.ComplexMetricActionBoundary
open ScalarTwoJet ComplexMetricField CoordinateMetricTwoJet.Linearization
open EinsteinActionBoundary ComplexCoordinateConnection
noncomputable section
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ
local notation "Point" => Fin d → ℝ

private theorem inverse_diff (g : ComplexMetricField.Field d) (x : Point)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (hdet : (g x).det ≠ 0) (i j : Fin d) :
    DifferentiableAt ℝ (fun y => (g y)⁻¹ i j) x := by
  have hd (F : ComplexMetricField.Field d) (hF : ∀ a b, DifferentiableAt ℝ (fun y => F y a b) x) :
      DifferentiableAt ℝ (fun y => (F y).det) x := by
    simp only [Matrix.det_apply']
    exact DifferentiableAt.fun_sum (u := Finset.univ) fun σ _ =>
      ((HasFDerivAt.finsetProd (u := Finset.univ) (fun a _ => (hF (σ a) a).hasFDerivAt)).differentiableAt).const_mul _
  have ha : DifferentiableAt ℝ (fun y => (g y).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    apply hd
    intro a b
    by_cases ha : a = j
    · simp [Matrix.updateRow_apply, ha]
    · simpa [Matrix.updateRow_apply, ha] using hg a b
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((hd g hg).inv hdet).mul ha

private theorem mul_diff (M N : ComplexMetricField.Field d) (x : Point)
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hN : ∀ i j, DifferentiableAt ℝ (fun y => N y i j) x) (i j : Fin d) :
    DifferentiableAt ℝ (fun y => (M y * N y) i j) x := by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum (u := Finset.univ) fun a _ => (hM i a).mul (hN a j)

private theorem inverseVariation_diff (g h : ComplexMetricField.Field d) (x : Point)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (i j : Fin d) :
    DifferentiableAt ℝ (fun y => inverse (twoJet g y) (twoJet h y) i j) x := by
  exact (mul_diff _ _ x (mul_diff _ _ x (inverse_diff g x hg hdet) hh)
    (inverse_diff g x hg hdet) i j).neg

private theorem inverseVariation_partial (g h : ComplexMetricField.Field d) (x : Point)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k : Fin d) :
    matrixPartial (fun y => inverse (twoJet g y) (twoJet h y)) x k =
      inverseSpatial (twoJet g x) (twoJet h x) k := by
  have hgd (i j : Fin d) := (hg i j).differentiableAt (by norm_num)
  have hhd (i j : Fin d) := (hh i j).differentiableAt (by norm_num)
  have hgi := inverse_diff g x hgd hdet
  have he : matrixPartial (fun y => inverse (twoJet g y) (twoJet h y)) x k =
      -matrixPartial (fun y => (g y)⁻¹ * h y * (g y)⁻¹) x k := by
    ext i j
    simp only [inverse, twoJet, Matrix.neg_apply, matrixPartial, coordDeriv,
      fderiv_fun_neg, neg_apply]
  rw [he, matrixPartial_mul _ _ x (mul_diff _ _ x hgi hhd) hgi,
    matrixPartial_mul _ _ x hgi hhd, ComplexMetricField.inverse_partial g x hg hdet]
  change -(((twoJet g x).inverseDerivative k * h x + (g x)⁻¹ * (twoJet h x).first k) * (g x)⁻¹ +
    (g x)⁻¹ * h x * (twoJet g x).inverseDerivative k) = _
  simp only [inverseSpatial, inverse, CoordinateMetricTwoJet.inverseDerivative, twoJet]
  noncomm_ring

private theorem connectionVariation_diff (g h : ComplexMetricField.Field d) (x : Point)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (u i j : Fin d) :
    DifferentiableAt ℝ (fun y => connection (twoJet g y) (twoJet h y) u i j) x := by
  have hgd (a b : Fin d) := (hg a b).differentiableAt (by norm_num)
  have hhd (a b : Fin d) := (hh a b).differentiableAt (by norm_num)
  have hg1 (a b c : Fin d) := (coordDeriv_contDiffAt (m := 1) (hg b c) (by norm_num) a).differentiableAt (by norm_num)
  have hh1 (a b c : Fin d) := (coordDeriv_contDiffAt (m := 1) (hh b c) (by norm_num) a).differentiableAt (by norm_num)
  dsimp only [CoordinateMetricTwoJet.Linearization.connection, twoJet]
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro m _
  exact ((inverseVariation_diff g h x hgd hhd hdet u m).mul
    (((hg1 i m j).add (hg1 j m i)).sub (hg1 m i j))).add
    ((inverse_diff g x hgd hdet u m).mul (((hh1 i m j).add (hh1 j m i)).sub (hh1 m i j)))

/-- The actual coordinate derivative of the linearized connection is its complete spatial variation. -/
theorem connectionVariation_coordDeriv (g h : ComplexMetricField.Field d) (x : Point)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k u i j : Fin d) :
    coordDeriv k (fun y => connection (twoJet g y) (twoJet h y) u i j) x =
      connectionSpatial (twoJet g x) (twoJet h x) k u i j := by
  have hgd (a b : Fin d) := (hg a b).differentiableAt (by norm_num)
  have hhd (a b : Fin d) := (hh a b).differentiableAt (by norm_num)
  have hg1 (a b c : Fin d) := (coordDeriv_contDiffAt (m := 1) (hg b c) (by norm_num) a).differentiableAt (by norm_num)
  have hh1 (a b c : Fin d) := (coordDeriv_contDiffAt (m := 1) (hh b c) (by norm_num) a).differentiableAt (by norm_num)
  have hdg := inverse_diff g x hgd hdet
  have hdv := inverseVariation_diff g h x hgd hhd hdet
  let Pg (m : Fin d) := fun y => coordDeriv i (fun z => g z m j) y +
    coordDeriv j (fun z => g z m i) y - coordDeriv m (fun z => g z i j) y
  let Ph (m : Fin d) := fun y => coordDeriv i (fun z => h z m j) y +
    coordDeriv j (fun z => h z m i) y - coordDeriv m (fun z => h z i j) y
  have hPg (m : Fin d) : DifferentiableAt ℝ (Pg m) x := ((hg1 i m j).add (hg1 j m i)).sub (hg1 m i j)
  have hPh (m : Fin d) : DifferentiableAt ℝ (Ph m) x := ((hh1 i m j).add (hh1 j m i)).sub (hh1 m i j)
  have ht (m : Fin d) : DifferentiableAt ℝ (fun y => inverse (twoJet g y) (twoJet h y) u m * Pg m y + (g y)⁻¹ u m * Ph m y) x :=
    ((hdv u m).mul (hPg m)).add ((hdg u m).mul (hPh m))
  change coordDeriv k (fun y => (1 / 2 : ℂ) * ∑ m,
    (inverse (twoJet g y) (twoJet h y) u m * Pg m y + (g y)⁻¹ u m * Ph m y)) x = _
  rw [coordDeriv_mul (differentiableAt_const _) (DifferentiableAt.fun_sum (u := Finset.univ) fun m _ => ht m)]
  have hz : coordDeriv k (fun _ : Point => (1 / 2 : ℂ)) x = 0 := by simp [coordDeriv]
  rw [hz, zero_mul, zero_add, coordDeriv_sum (s := Finset.univ) (fun m _ => ht m)]
  unfold connectionSpatial
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  erw [coordDeriv_add ((hdv u m).mul (hPg m)) ((hdg u m).mul (hPh m)),
    coordDeriv_mul (hdv u m) (hPg m), coordDeriv_mul (hdg u m) (hPh m)]
  have hiv := congrArg (fun A : Mat => A u m) (inverseVariation_partial g h x hg hh hdet k)
  have hig := congrArg (fun A : Mat => A u m) (ComplexMetricField.inverse_partial g x hg hdet k)
  change coordDeriv k (fun y => inverse (twoJet g y) (twoJet h y) u m) x = _ at hiv
  change coordDeriv k (fun y => (g y)⁻¹ u m) x = _ at hig
  rw [hiv, hig]
  dsimp only [Pg, Ph]
  erw [coordDeriv_sub ((hg1 i m j).add (hg1 j m i)) (hg1 m i j),
    coordDeriv_add (hg1 i m j) (hg1 j m i),
    coordDeriv_sub ((hh1 i m j).add (hh1 j m i)) (hh1 m i j),
    coordDeriv_add (hh1 i m j) (hh1 j m i)]
  simp only [twoJet]
  ring

/-- Regularity of the original connection-variation current on actual metric fields. -/
theorem current_differentiableAt (g h : ComplexMetricField.Field d) (x : Point)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (a : Fin d) :
    DifferentiableAt ℝ (fun y => current (twoJet g y) (twoJet h y) a) x := by
  have hi := inverse_diff g x (fun i j => (hg i j).differentiableAt (by norm_num)) hdet
  have hc := connectionVariation_diff g h x hg hh hdet
  unfold current
  exact (DifferentiableAt.fun_sum (u := Finset.univ) fun i _ => DifferentiableAt.fun_sum (u := Finset.univ) fun j _ =>
    (hi i j).mul (hc a j i)).sub
    (DifferentiableAt.fun_sum (u := Finset.univ) fun i _ => DifferentiableAt.fun_sum (u := Finset.univ) fun u _ => (hi i a).mul (hc u u i))

/-- Every jet term in the boundary current is an actual spatial derivative. -/
theorem current_coordDeriv (g h : ComplexMetricField.Field d) (x : Point)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k a : Fin d) :
    coordDeriv k (fun y => current (twoJet g y) (twoJet h y) a) x =
      currentPartial (twoJet g x) (twoJet h x) k a := by
  have hi := inverse_diff g x (fun i j => (hg i j).differentiableAt (by norm_num)) hdet
  have hc := connectionVariation_diff g h x hg hh hdet
  have hp (i j : Fin d) : DifferentiableAt ℝ (fun y => (g y)⁻¹ i j *
      CoordinateMetricTwoJet.Linearization.connection (twoJet g y) (twoJet h y) a j i) x :=
    (hi i j).mul (hc a j i)
  have hq (i u : Fin d) : DifferentiableAt ℝ (fun y => (g y)⁻¹ i a *
      CoordinateMetricTwoJet.Linearization.connection (twoJet g y) (twoJet h y) u u i) x :=
    (hi i a).mul (hc u u i)
  unfold current
  erw [coordDeriv_sub (DifferentiableAt.fun_sum (u := Finset.univ) fun i _ => DifferentiableAt.fun_sum (u := Finset.univ) fun j _ => hp i j)
    (DifferentiableAt.fun_sum (u := Finset.univ) fun i _ => DifferentiableAt.fun_sum (u := Finset.univ) fun u _ => hq i u)]
  rw [coordDeriv_sum (s := Finset.univ) (fun i _ => DifferentiableAt.fun_sum (u := Finset.univ) fun j _ => hp i j),
    coordDeriv_sum (s := Finset.univ) (fun i _ => DifferentiableAt.fun_sum (u := Finset.univ) fun u _ => hq i u)]
  simp_rw [coordDeriv_sum (s := Finset.univ) (fun j _ => hp _ j),
    coordDeriv_sum (s := Finset.univ) (fun u _ => hq _ u)]
  unfold currentPartial
  have hentry (i j u v w : Fin d) :
      coordDeriv k (fun y => (g y)⁻¹ i j *
        CoordinateMetricTwoJet.Linearization.connection (twoJet g y) (twoJet h y) u v w) x =
      (twoJet g x).inverseDerivative k i j *
        CoordinateMetricTwoJet.Linearization.connection (twoJet g x) (twoJet h x) u v w +
        (g x)⁻¹ i j * connectionSpatial (twoJet g x) (twoJet h x) k u v w := by
    rw [coordDeriv_mul (hi i j) (hc u v w), connectionVariation_coordDeriv g h x hg hh hdet]
    have hgi := congrArg (fun A : Mat => A i j) (ComplexMetricField.inverse_partial g x hg hdet k)
    change coordDeriv k (fun y => (g y)⁻¹ i j) x = _ at hgi
    rw [hgi]
  simp_rw [hentry]
  rfl

end
end GaloisForLFunctions.HTGeometry.ComplexMetricActionBoundary
