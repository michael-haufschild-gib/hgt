import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexLinearization

/-!
# Actual mixed complex Einstein variation

Differentiate the full first variation along an independent metric-jet direction.
Every inverse, spatial inverse, connection, curvature and scalar contraction term
is retained. The resulting Einstein contraction equals the actual second Frechet
variation. This supplies a direct bilinear source formula without expanding three
diagonal quadratic variations.
-/

open Complex Set Filter Topology
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet.MixedQuadratic
noncomputable section
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ
local notation "Jet" => CoordinateMetricTwoJet d ℂ

private theorem matrix_mul {F G : ℂ → Mat} {F' G' : Mat} {t : ℂ}
    (hF : ∀ i j, HasDerivAt (fun z => F z i j) (F' i j) t)
    (hG : ∀ i j, HasDerivAt (fun z => G z i j) (G' i j) t) :
    ∀ i j, HasDerivAt (fun z => (F z * G z) i j)
      ((F' * G t + F t * G') i j) t := by
  intro i j
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hF i k).mul (hG k j))
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using h

private theorem first_deriv (J V : Jet) (k i j : Fin d) :
    HasDerivAt (fun t => (Linearization.affine J V t).first k i j) (V.first k i j) 0 := by
  simpa [Linearization.affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (V.first k i j)).const_add (J.first k i j)

private theorem second_deriv (J V : Jet) (k l i j : Fin d) :
    HasDerivAt (fun t => (Linearization.affine J V t).second k l i j) (V.second k l i j) 0 := by
  simpa [Linearization.affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (V.second k l i j)).const_add (J.second k l i j)

/-- Mixed inverse variation, retaining both perturbation orders. -/
def inverse (J K V : Jet) : Mat :=
  -(Linearization.inverse J V * K.metric * J.metric⁻¹ +
    J.metric⁻¹ * K.metric * Linearization.inverse J V)

/-- Mixed variation of the actual spatial inverse derivative. -/
def inverseSpatial (J K V : Jet) (k : Fin d) : Mat :=
  -(((inverse J K V * J.first k + Linearization.inverse J K * V.first k) * J.metric⁻¹ +
        Linearization.inverse J K * J.first k * Linearization.inverse J V) +
      (Linearization.inverse J V * K.first k * J.metric⁻¹ + J.metric⁻¹ * K.first k * Linearization.inverse J V) +
      ((Linearization.inverse J V * J.first k + J.metric⁻¹ * V.first k) * Linearization.inverse J K +
        J.metric⁻¹ * J.first k * inverse J K V))

/-- Mixed Christoffel variation with independent metric jets. -/
def connection (J K V : Jet) (u i j : Fin d) : ℂ :=
  (1/2 : ℂ) * ∑ m,
    ((inverse J K V u m * (J.first i m j + J.first j m i - J.first m i j) +
      Linearization.inverse J K u m * (V.first i m j + V.first j m i - V.first m i j)) +
      Linearization.inverse J V u m * (K.first i m j + K.first j m i - K.first m i j))

/-- Mixed spatial Christoffel variation, including both first variations. -/
def connectionSpatial (J K V : Jet) (k u i j : Fin d) : ℂ :=
  (1/2 : ℂ) * ∑ m,
    (((inverseSpatial J K V k u m * (J.first i m j + J.first j m i - J.first m i j) +
        Linearization.inverseSpatial J K k u m * (V.first i m j + V.first j m i - V.first m i j)) +
        Linearization.inverseSpatial J V k u m * (K.first i m j + K.first j m i - K.first m i j)) +
      (inverse J K V u m * (J.second k i m j + J.second k j m i - J.second k m i j) +
        Linearization.inverse J K u m * (V.second k i m j + V.second k j m i - V.second k m i j)) +
        Linearization.inverse J V u m * (K.second k i m j + K.second k j m i - K.second k m i j))

/-- Mixed curvature variation with both ordered connection products. -/
def curvature (J K V : Jet) (u i k l : Fin d) : ℂ :=
  connectionSpatial J K V k u l i - connectionSpatial J K V l u k i +
    ∑ m, ((connection J K V u k m * J.christoffel m l i +
        Linearization.connection J K u k m * Linearization.connection J V m l i) +
        (Linearization.connection J V u k m * Linearization.connection J K m l i +
          J.christoffel u k m * connection J K V m l i) -
        (connection J K V u l m * J.christoffel m k i +
          Linearization.connection J K u l m * Linearization.connection J V m k i) -
        (Linearization.connection J V u l m * Linearization.connection J K m k i +
          J.christoffel u l m * connection J K V m k i))

/-- Mixed Ricci contraction. -/
def ricci (J K V : Jet) (i j : Fin d) : ℂ := ∑ u, curvature J K V u i u j

/-- Mixed scalar contraction, retaining the two inverse--Ricci cross terms. -/
def scalar (J K V : Jet) : ℂ :=
  ∑ i, ∑ j, ((inverse J K V i j * J.ricci i j +
    Linearization.inverse J K i j * Linearization.ricci J V i j) +
    (Linearization.inverse J V i j * Linearization.ricci J K i j +
      J.metric⁻¹ i j * ricci J K V i j))

/-- Actual mixed Einstein variation before any background equation is imposed. -/
def einstein (J K V : Jet) (i j : Fin d) : ℂ :=
  ricci J K V i j - (1/2 : ℂ) *
    (scalar J K V * J.metric i j + Linearization.scalar J K * V.metric i j) -
    (1/2 : ℂ) * Linearization.scalar J V * K.metric i j

/-- Derivative of one inverse variation along the independent metric direction. -/
theorem inverse_hasDerivAt (J K V : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => Linearization.inverse (Linearization.affine J V t) K i j)
      (inverse J K V i j) 0 := by
  have hc := fun a b => hasDerivAt_const (0 : ℂ) (K.metric a b)
  have hd := matrix_mul (matrix_mul (Linearization.inverse_hasDerivAt J V hJ) hc)
    (Linearization.inverse_hasDerivAt J V hJ)
  simpa [Linearization.inverse, inverse, show (fun i j : Fin d => (0 : ℂ)) = (0 : Mat) from rfl] using! (hd i j).neg

/-- Derivative of every spatial inverse term along the independent direction. -/
theorem inverseSpatial_hasDerivAt (J K V : Jet) (hJ : J.metric.det ≠ 0) (k i j : Fin d) :
    HasDerivAt (fun t => Linearization.inverseSpatial (Linearization.affine J V t) K k i j)
      (inverseSpatial J K V k i j) 0 := by
  have h0 := Linearization.inverse_hasDerivAt J V hJ
  have h1 := inverse_hasDerivAt J K V hJ
  have hf := first_deriv J V k
  have hc := fun a b => hasDerivAt_const (0 : ℂ) (K.first k a b)
  have hA := matrix_mul (matrix_mul h1 hf) h0
  have hB := matrix_mul (matrix_mul h0 hc) h0
  have hC := matrix_mul (matrix_mul h0 hf) h1
  simpa [Linearization.inverseSpatial, inverseSpatial, show (fun i j : Fin d => (0 : ℂ)) = (0 : Mat) from rfl] using! (((hA i j).add (hB i j)).add (hC i j)).neg

/-- Actual mixed connection derivative. -/
theorem connection_hasDerivAt (J K V : Jet) (hJ : J.metric.det ≠ 0) (u i j : Fin d) :
    HasDerivAt (fun t => Linearization.connection (Linearization.affine J V t) K u i j)
      (connection J K V u i j) 0 := by
  have hf (m : Fin d) := ((first_deriv J V i m j).add
    (first_deriv J V j m i)).sub (first_deriv J V m i j)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
    ((inverse_hasDerivAt J K V hJ u m).mul (hf m)).add
      ((Linearization.inverse_hasDerivAt J V hJ u m).mul_const
        (K.first i m j + K.first j m i - K.first m i j)))).const_mul (1/2 : ℂ)
  simpa [Linearization.connection, connection] using hd

/-- Actual mixed spatial connection derivative. -/
theorem connectionSpatial_hasDerivAt (J K V : Jet) (hJ : J.metric.det ≠ 0)
    (k u i j : Fin d) :
    HasDerivAt (fun t => Linearization.connectionSpatial (Linearization.affine J V t) K k u i j)
      (connectionSpatial J K V k u i j) 0 := by
  have hf (m : Fin d) := ((first_deriv J V i m j).add
    (first_deriv J V j m i)).sub (first_deriv J V m i j)
  have hs (m : Fin d) := ((second_deriv J V k i m j).add
    (second_deriv J V k j m i)).sub (second_deriv J V k m i j)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
    ((((inverseSpatial_hasDerivAt J K V hJ k u m).mul (hf m)).add
        ((Linearization.inverseSpatial_hasDerivAt J V hJ k u m).mul_const
          (K.first i m j + K.first j m i - K.first m i j))).add
        ((inverse_hasDerivAt J K V hJ u m).mul (hs m))).add
        ((Linearization.inverse_hasDerivAt J V hJ u m).mul_const
          (K.second k i m j + K.second k j m i - K.second k m i j)))).const_mul (1/2 : ℂ)
  simpa [Linearization.connectionSpatial, connectionSpatial, add_assoc] using hd

/-- Actual mixed curvature derivative. -/
theorem curvature_hasDerivAt (J K V : Jet) (hJ : J.metric.det ≠ 0) (u i k l : Fin d) :
    HasDerivAt (fun t => Linearization.curvature (Linearization.affine J V t) K u i k l)
      (curvature J K V u i k l) 0 := by
  have h0 := Linearization.connection_hasDerivAt J V hJ
  have h1 := connection_hasDerivAt J K V hJ
  have hd := ((connectionSpatial_hasDerivAt J K V hJ k u l i).sub
    (connectionSpatial_hasDerivAt J K V hJ l u k i)).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
      ((((h1 u k m).mul (h0 m l i)).add ((h0 u k m).mul (h1 m l i))).sub
        ((h1 u l m).mul (h0 m k i))).sub ((h0 u l m).mul (h1 m k i))))
  convert! hd using 1
  · funext t
    simp only [Linearization.curvature, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    ring
  · simp only [curvature, Linearization.affine_zero]

/-- Actual mixed Ricci derivative. -/
theorem ricci_hasDerivAt (J K V : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => Linearization.ricci (Linearization.affine J V t) K i j)
      (ricci J K V i j) 0 := by
  simpa [Linearization.ricci, ricci] using HasDerivAt.fun_sum (u := Finset.univ)
    (fun u _ => curvature_hasDerivAt J K V hJ u i u j)

/-- Actual mixed scalar derivative. -/
theorem scalar_hasDerivAt (J K V : Jet) (hJ : J.metric.det ≠ 0) :
    HasDerivAt (fun t => Linearization.scalar (Linearization.affine J V t) K)
      (scalar J K V) 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((inverse_hasDerivAt J K V hJ i j).mul (Linearization.ricci_hasDerivAt J V hJ i j)).add
        ((Linearization.inverse_hasDerivAt J V hJ i j).mul (ricci_hasDerivAt J K V hJ i j))))
  simpa [Linearization.scalar, scalar] using hd

/-- Actual mixed Einstein derivative. -/
theorem einstein_hasDerivAt (J K V : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => Linearization.einstein (Linearization.affine J V t) K i j)
      (einstein J K V i j) 0 := by
  have hm : HasDerivAt (fun t => (Linearization.affine J V t).metric i j) (V.metric i j) 0 := by
    simpa [Linearization.affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (V.metric i j)).const_add (J.metric i j)
  have hd := ((ricci_hasDerivAt J K V hJ i j).sub
    (((scalar_hasDerivAt J K V hJ).mul hm).const_mul (1/2 : ℂ))).sub
      (((Linearization.scalar_hasDerivAt J V hJ).const_mul (1/2 : ℂ)).mul_const (K.metric i j))
  simpa [Linearization.einstein, einstein, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using! hd

/-- The finite mixed contraction equals the original Einstein function's Hessian. -/
theorem einstein_eq_secondVariation (J K V : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    einstein J K V i j = ComplexCoordinateMetricTwoJet.secondVariation
      (ComplexCoordinateMetricTwoJet.toSpace J) i j
      (ComplexCoordinateMetricTwoJet.toSpace V) (ComplexCoordinateMetricTwoJet.toSpace K) := by
  let q := ComplexCoordinateMetricTwoJet.toSpace J
  let v := ComplexCoordinateMetricTwoJet.toSpace V
  let k := ComplexCoordinateMetricTwoJet.toSpace K
  let E := ComplexCoordinateMetricTwoJet.einsteinComponent i j
  have hline : HasDerivAt (fun t : ℂ => q + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add q
  have hs := (ComplexCoordinateMetricTwoJet.contDiffAt_einsteinComponent
    (n := 2) q hJ i j).fderiv_right (m := 1) (by norm_num)
  have hdf : HasFDerivAt (fderiv ℂ E) (fderiv ℂ (fderiv ℂ E) q) (q + (0 : ℂ) • v) := by
    simpa only [zero_smul, add_zero] using (hs.differentiableAt (by norm_num)).hasFDerivAt
  have hd0 : HasDerivAt (fun t : ℂ => fderiv ℂ E (q + t • v))
      (fderiv ℂ (fderiv ℂ E) q v) 0 := hdf.comp_hasDerivAt 0 hline
  have hd := hd0.clm_apply (hasDerivAt_const (0 : ℂ) k)
  have hd' : HasDerivAt (fun t : ℂ => fderiv ℂ E (q + t • v) k)
      (ComplexCoordinateMetricTwoJet.secondVariation q i j v k) 0 := by
    simpa [ComplexCoordinateMetricTwoJet.secondVariation, E] using hd
  have hc : Continuous (fun t : ℂ => (Linearization.affine J V t).metric.det) := by
    simp only [Matrix.det_apply', Linearization.affine]
    fun_prop
  have he : (fun t => Linearization.einstein (Linearization.affine J V t) K i j) =ᶠ[𝓝 0]
      (fun t : ℂ => fderiv ℂ E (q + t • v) k) := by
    filter_upwards [hc.continuousAt.eventually_ne (by simpa using hJ)] with t ht
    exact Linearization.einstein_eq_fderiv (Linearization.affine J V t) K ht i j
  exact (einstein_hasDerivAt J K V hJ i j).unique (hd'.congr_of_eventuallyEq he)

end
end GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet.MixedQuadratic
