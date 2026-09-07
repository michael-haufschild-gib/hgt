import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexLinearization

/-!
# Actual complex quadratic Einstein coefficient

Differentiate the complete first Einstein variation, retaining both inverse-metric
variations, every spatial derivative and every connection product. The resulting
finite contraction is proved equal to the actual complex Hessian. This supplies
the coefficient evaluated on the full BM scalar/vector jet; no source map or
computed coefficient is assumed.
-/

open Complex Set Filter Topology
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet.Quadratic
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

private theorem first_deriv (J K : Jet) (k i j : Fin d) :
    HasDerivAt (fun t => (Linearization.affine J K t).first k i j) (K.first k i j) 0 := by
  simpa [Linearization.affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (K.first k i j)).const_add (J.first k i j)

private theorem second_deriv (J K : Jet) (k l i j : Fin d) :
    HasDerivAt (fun t => (Linearization.affine J K t).second k l i j) (K.second k l i j) 0 := by
  simpa [Linearization.affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (K.second k l i j)).const_add (J.second k l i j)

/-- Actual second inverse variation, before collecting its two equal products. -/
def inverse (J K : Jet) : Mat :=
  -(Linearization.inverse J K * K.metric * J.metric⁻¹ + J.metric⁻¹ * K.metric * Linearization.inverse J K)

/-- Second variation of the spatial inverse derivative, with every product retained. -/
def inverseSpatial (J K : Jet) (k : Fin d) : Mat :=
  -(((inverse J K * J.first k + Linearization.inverse J K * K.first k) * J.metric⁻¹ +
        Linearization.inverse J K * J.first k * Linearization.inverse J K) +
      (Linearization.inverse J K * K.first k * J.metric⁻¹ + J.metric⁻¹ * K.first k * Linearization.inverse J K) +
      ((Linearization.inverse J K * J.first k + J.metric⁻¹ * K.first k) * Linearization.inverse J K +
        J.metric⁻¹ * J.first k * inverse J K))

/-- Complete second Christoffel variation. -/
def connection (J K : Jet) (u i j : Fin d) : ℂ :=
  (1/2 : ℂ) * ∑ m,
    ((inverse J K u m * (J.first i m j + J.first j m i - J.first m i j) +
      Linearization.inverse J K u m * (K.first i m j + K.first j m i - K.first m i j)) +
      Linearization.inverse J K u m * (K.first i m j + K.first j m i - K.first m i j))

/-- Complete second spatial Christoffel variation. -/
def connectionSpatial (J K : Jet) (k u i j : Fin d) : ℂ :=
  (1/2 : ℂ) * ∑ m,
    (((inverseSpatial J K k u m * (J.first i m j + J.first j m i - J.first m i j) +
        Linearization.inverseSpatial J K k u m * (K.first i m j + K.first j m i - K.first m i j)) +
        Linearization.inverseSpatial J K k u m * (K.first i m j + K.first j m i - K.first m i j)) +
      (inverse J K u m * (J.second k i m j + J.second k j m i - J.second k m i j) +
        Linearization.inverse J K u m * (K.second k i m j + K.second k j m i - K.second k m i j)) +
        Linearization.inverse J K u m * (K.second k i m j + K.second k j m i - K.second k m i j))

/-- Complete second curvature variation, including the two first-connection products. -/
def curvature (J K : Jet) (u i k l : Fin d) : ℂ :=
  connectionSpatial J K k u l i - connectionSpatial J K l u k i +
    ∑ m, ((connection J K u k m * J.christoffel m l i +
        Linearization.connection J K u k m * Linearization.connection J K m l i) +
        (Linearization.connection J K u k m * Linearization.connection J K m l i +
          J.christoffel u k m * connection J K m l i) -
        (connection J K u l m * J.christoffel m k i +
          Linearization.connection J K u l m * Linearization.connection J K m k i) -
        (Linearization.connection J K u l m * Linearization.connection J K m k i +
          J.christoffel u l m * connection J K m k i))

/-- Second Ricci variation from the complete metric two-jet. -/
def ricci (J K : Jet) (i j : Fin d) : ℂ := ∑ u, curvature J K u i u j

/-- Second scalar curvature variation, retaining inverse and mixed contractions. -/
def scalar (J K : Jet) : ℂ :=
  ∑ i, ∑ j, ((inverse J K i j * J.ricci i j + Linearization.inverse J K i j * Linearization.ricci J K i j) +
    (Linearization.inverse J K i j * Linearization.ricci J K i j + J.metric⁻¹ i j * ricci J K i j))

/-- Second Einstein variation; divide by two for the quadratic source coefficient. -/
def einstein (J K : Jet) (i j : Fin d) : ℂ :=
  ricci J K i j - (1/2 : ℂ) * (scalar J K * J.metric i j + Linearization.scalar J K * K.metric i j) -
    (1/2 : ℂ) * Linearization.scalar J K * K.metric i j

/-- Derivative of the first inverse variation along the actual affine metric. -/
theorem inverse_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => Linearization.inverse (Linearization.affine J K t) K i j) (inverse J K i j) 0 := by
  have hc := fun a b => hasDerivAt_const (0 : ℂ) (K.metric a b)
  have hd := matrix_mul (matrix_mul (Linearization.inverse_hasDerivAt J K hJ) hc)
    (Linearization.inverse_hasDerivAt J K hJ)
  simpa [Linearization.inverse, inverse, show (fun i j : Fin d => (0 : ℂ)) = (0 : Mat) from rfl] using! (hd i j).neg

/-- Derivative of every term in the first spatial inverse variation. -/
theorem inverseSpatial_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (k i j : Fin d) :
    HasDerivAt (fun t => Linearization.inverseSpatial (Linearization.affine J K t) K k i j)
      (inverseSpatial J K k i j) 0 := by
  have h0 := Linearization.inverse_hasDerivAt J K hJ
  have h1 := inverse_hasDerivAt J K hJ
  have hf := first_deriv J K k
  have hc := fun a b => hasDerivAt_const (0 : ℂ) (K.first k a b)
  have hA := matrix_mul (matrix_mul h1 hf) h0
  have hB := matrix_mul (matrix_mul h0 hc) h0
  have hC := matrix_mul (matrix_mul h0 hf) h1
  simpa [Linearization.inverseSpatial, inverseSpatial, show (fun i j : Fin d => (0 : ℂ)) = (0 : Mat) from rfl] using! (((hA i j).add (hB i j)).add (hC i j)).neg

/-- Derivative of the complete first Christoffel variation. -/
theorem connection_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (u i j : Fin d) :
    HasDerivAt (fun t => Linearization.connection (Linearization.affine J K t) K u i j)
      (connection J K u i j) 0 := by
  have hf (m : Fin d) := ((first_deriv J K i m j).add
    (first_deriv J K j m i)).sub (first_deriv J K m i j)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
    ((inverse_hasDerivAt J K hJ u m).mul (hf m)).add
      ((Linearization.inverse_hasDerivAt J K hJ u m).mul_const
        (K.first i m j + K.first j m i - K.first m i j)))).const_mul (1/2 : ℂ)
  simpa [Linearization.connection, connection] using hd

/-- Derivative of the complete first spatial Christoffel variation. -/
theorem connectionSpatial_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0)
    (k u i j : Fin d) :
    HasDerivAt (fun t => Linearization.connectionSpatial (Linearization.affine J K t) K k u i j)
      (connectionSpatial J K k u i j) 0 := by
  have hf (m : Fin d) := ((first_deriv J K i m j).add
    (first_deriv J K j m i)).sub (first_deriv J K m i j)
  have hs (m : Fin d) := ((second_deriv J K k i m j).add
    (second_deriv J K k j m i)).sub (second_deriv J K k m i j)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
    ((((inverseSpatial_hasDerivAt J K hJ k u m).mul (hf m)).add
        ((Linearization.inverseSpatial_hasDerivAt J K hJ k u m).mul_const
          (K.first i m j + K.first j m i - K.first m i j))).add
        ((inverse_hasDerivAt J K hJ u m).mul (hs m))).add
        ((Linearization.inverse_hasDerivAt J K hJ u m).mul_const
          (K.second k i m j + K.second k j m i - K.second k m i j)))).const_mul (1/2 : ℂ)
  simpa [Linearization.connectionSpatial, connectionSpatial, add_assoc] using hd

/-- Derivative of the complete first curvature variation. -/
theorem curvature_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (u i k l : Fin d) :
    HasDerivAt (fun t => Linearization.curvature (Linearization.affine J K t) K u i k l)
      (curvature J K u i k l) 0 := by
  have h0 := Linearization.connection_hasDerivAt J K hJ
  have h1 := connection_hasDerivAt J K hJ
  have hd := ((connectionSpatial_hasDerivAt J K hJ k u l i).sub
    (connectionSpatial_hasDerivAt J K hJ l u k i)).add
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

/-- Derivative of the complete first Ricci variation. -/
theorem ricci_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => Linearization.ricci (Linearization.affine J K t) K i j) (ricci J K i j) 0 := by
  simpa [Linearization.ricci, ricci] using HasDerivAt.fun_sum (u := Finset.univ)
    (fun u _ => curvature_hasDerivAt J K hJ u i u j)

/-- Derivative of the complete first scalar curvature variation. -/
theorem scalar_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) :
    HasDerivAt (fun t => Linearization.scalar (Linearization.affine J K t) K) (scalar J K) 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((inverse_hasDerivAt J K hJ i j).mul (Linearization.ricci_hasDerivAt J K hJ i j)).add
        ((Linearization.inverse_hasDerivAt J K hJ i j).mul (ricci_hasDerivAt J K hJ i j))))
  simpa [Linearization.scalar, scalar] using hd

/-- Derivative of the complete first Einstein variation. -/
theorem einstein_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => Linearization.einstein (Linearization.affine J K t) K i j) (einstein J K i j) 0 := by
  have hm : HasDerivAt (fun t => (Linearization.affine J K t).metric i j) (K.metric i j) 0 := by
    simpa [Linearization.affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (K.metric i j)).const_add (J.metric i j)
  have hd := ((ricci_hasDerivAt J K hJ i j).sub
    (((scalar_hasDerivAt J K hJ).mul hm).const_mul (1/2 : ℂ))).sub
      (((Linearization.scalar_hasDerivAt J K hJ).const_mul (1/2 : ℂ)).mul_const (K.metric i j))
  simpa [Linearization.einstein, einstein, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using! hd

/-- The finite contraction is exactly the actual complex Einstein Hessian. -/
theorem einstein_eq_secondVariation (J K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    einstein J K i j = ComplexCoordinateMetricTwoJet.secondVariation
      (ComplexCoordinateMetricTwoJet.toSpace J) i j
      (ComplexCoordinateMetricTwoJet.toSpace K) (ComplexCoordinateMetricTwoJet.toSpace K) := by
  let q := ComplexCoordinateMetricTwoJet.toSpace J
  let v := ComplexCoordinateMetricTwoJet.toSpace K
  let E := ComplexCoordinateMetricTwoJet.einsteinComponent i j
  have hline : HasDerivAt (fun t : ℂ => q + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add q
  have hs := (ComplexCoordinateMetricTwoJet.contDiffAt_einsteinComponent
    (n := 2) q hJ i j).fderiv_right (m := 1) (by norm_num)
  have hdf : HasFDerivAt (fderiv ℂ E) (fderiv ℂ (fderiv ℂ E) q) (q + (0 : ℂ) • v) := by
    simpa only [zero_smul, add_zero] using (hs.differentiableAt (by norm_num)).hasFDerivAt
  have hd0 : HasDerivAt (fun t : ℂ => fderiv ℂ E (q + t • v))
      (fderiv ℂ (fderiv ℂ E) q v) 0 := hdf.comp_hasDerivAt 0 hline
  have hd := hd0.clm_apply (hasDerivAt_const (0 : ℂ) v)
  have hd' : HasDerivAt (fun t : ℂ => fderiv ℂ E (q + t • v) v)
      (ComplexCoordinateMetricTwoJet.secondVariation q i j v v) 0 := by
    simpa [ComplexCoordinateMetricTwoJet.secondVariation, E] using hd
  have hc : Continuous (fun t : ℂ => (Linearization.affine J K t).metric.det) := by
    simp only [Matrix.det_apply', Linearization.affine]
    fun_prop
  have he : (fun t => Linearization.einstein (Linearization.affine J K t) K i j) =ᶠ[𝓝 0]
      (fun t : ℂ => fderiv ℂ E (q + t • v) v) := by
    filter_upwards [hc.continuousAt.eventually_ne (by simpa using hJ)] with t ht
    exact Linearization.einstein_eq_fderiv (Linearization.affine J K t) K ht i j
  exact (einstein_hasDerivAt J K hJ i j).unique (hd'.congr_of_eventuallyEq he)

end
end GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet.Quadratic
