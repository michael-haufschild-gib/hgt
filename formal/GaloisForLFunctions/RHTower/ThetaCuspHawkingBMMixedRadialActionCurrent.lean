import GaloisForLFunctions.HTGeometry.CoordinateEinsteinActionVariation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBackgroundMetricTwoJet

/-!
# Einstein radial action current in the BM mixed sector

Differentiate the volume-weighted Einstein boundary current with respect to
both complete metric-jet directions. The mixed connection variations cancel
by symmetry of the actual second derivative. Evaluation on the original BM
background leaves the antisymmetric contraction of each time-angular metric
block with the other field's time/radial curl.

This supplies the tensor current for testing the onset pulse against the
incoming horizon profile. It does not identify a causal response, integrate
its endpoints, supply the scalar-scalar or vector-vector sectors, or prove
physical extinction.
-/

namespace RHTower.D4BMMixedActionCurrent
open GaloisForLFunctions.HTGeometry
open CoordinateMetricTwoJet CoordinateMetricTwoJet.Linearization
open EinsteinActionBoundary MetricPathDensity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ
local notation "Jet" => CoordinateMetricTwoJet d ℂ

private theorem mat_mul {F G : ℂ → Mat} {F' G' : Mat} {t : ℂ}
    (hF : ∀ i j, HasDerivAt (fun s => F s i j) (F' i j) t)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t) :
    ∀ i j, HasDerivAt (fun s => (F s * G s) i j) ((F' * G t + F t * G') i j) t := by
  intro i j
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hF i k).mul (hG k j))

private def inverseMixed (J H K : Jet) : Mat :=
  -(inverse J H * K.metric * J.metric⁻¹ + J.metric⁻¹ * K.metric * inverse J H)

private theorem inverseMixed_symm (J H K : Jet) : inverseMixed J H K = inverseMixed J K H := by
  unfold inverseMixed inverse
  noncomm_ring

private theorem inverseMixed_derivative (J H K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => inverse (affine J H t) K i j) (inverseMixed J H K i j) 0 := by
  have hi := inverse_hasDerivAt J H hJ
  have hk (i j : Fin d) : HasDerivAt (fun _ : ℂ => K.metric i j) ((0:Mat) i j) 0 := hasDerivAt_const (0:ℂ) (K.metric i j)
  have hp := mat_mul (mat_mul hi hk) hi i j
  simpa [inverse, inverseMixed, affine_zero] using hp.fun_neg

private def connectionMixed (J H K : Jet) (u i j : Fin d) : ℂ :=
  (1/2:ℂ) * ∑ m,
    (inverseMixed J H K u m * (J.first i m j + J.first j m i - J.first m i j) +
     inverse J K u m * (H.first i m j + H.first j m i - H.first m i j) +
     inverse J H u m * (K.first i m j + K.first j m i - K.first m i j))

private theorem connectionMixed_symm (J H K : Jet) (u i j : Fin d) :
    connectionMixed J H K u i j = connectionMixed J K H u i j := by
  unfold connectionMixed
  rw [inverseMixed_symm]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  ring

private theorem connectionMixed_derivative (J H K : Jet) (hJ : J.metric.det ≠ 0) (u i j : Fin d) :
    HasDerivAt (fun t => connection (affine J H t) K u i j)
      (connectionMixed J H K u i j) 0 := by
  have hf (a b c : Fin d) : HasDerivAt (fun t => (affine J H t).first a b c) (H.first a b c) 0 := by
    simpa [affine] using ((hasDerivAt_id (0:ℂ)).mul_const (H.first a b c)).const_add (J.first a b c)
  have hp (m : Fin d) := ((hf i m j).add (hf j m i)).sub (hf m i j)
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
    ((inverseMixed_derivative J H K hJ u m).mul (hp m)).add
      ((inverse_hasDerivAt J H hJ u m).mul_const
        (K.first i m j+K.first j m i-K.first m i j)))).const_mul (1/2:ℂ)
  simpa only [connection, connectionMixed, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, affine_zero] using h

private def currentMixed (J H K : Jet) (a : Fin d) : ℂ :=
  (∑ i, ∑ j, (inverse J H i j * connection J K a j i +
    J.metric⁻¹ i j * connectionMixed J H K a j i)) -
  ∑ i, ∑ u, (inverse J H i a * connection J K u u i +
    J.metric⁻¹ i a * connectionMixed J H K u u i)

private theorem currentMixed_derivative (J H K : Jet) (hJ : J.metric.det ≠ 0) (a : Fin d) :
    HasDerivAt (fun t => current (affine J H t) K a) (currentMixed J H K a) 0 := by
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (inverse_hasDerivAt J H hJ i j).mul (connectionMixed_derivative J H K hJ a j i)))
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun u _ =>
      (inverse_hasDerivAt J H hJ i a).mul (connectionMixed_derivative J H K hJ u u i)))
  simpa only [current, currentMixed, Pi.mul_apply, affine_zero] using h1.fun_sub h2

/-- Actual volume-weighted Einstein boundary current along a full affine metric-jet variation. -/
def actionCurrentPath (J H K : Jet) (a : Fin d) (t : ℂ) : ℂ :=
  volumeRatio J.metric H.metric 0 0 t * current (affine J H t) K a

/-- Antisymmetrized actual first variations of the Einstein boundary current. -/
def actionSymplectic (J H K : Jet) (a : Fin d) : ℂ :=
  deriv (actionCurrentPath J H K a) 0 - deriv (actionCurrentPath J K H a) 0

private def weightedInverse (J H : Jet) : Mat :=
  ((J.metric⁻¹*H.metric).trace/2) • J.metric⁻¹ + inverse J H

private theorem actionSymplectic_eq (J H K : Jet) (hJ : J.metric.det ≠ 0) (a : Fin d) :
    actionSymplectic J H K a =
      (∑ i, ∑ j, (weightedInverse J H i j * connection J K a j i -
        weightedInverse J K i j * connection J H a j i)) -
      ∑ i, ∑ u, (weightedInverse J H i a * connection J K u u i -
        weightedInverse J K i a * connection J H u u i) := by
  have hp (H K : Jet) := ((volumeRatio_hasDerivAt_trace J.metric H.metric 0 0 hJ).mul
    (currentMixed_derivative J H K hJ a)).deriv
  unfold actionSymplectic
  rw [show deriv (actionCurrentPath J H K a) 0 = _ from hp H K,
    show deriv (actionCurrentPath J K H a) 0 = _ from hp K H]
  simp only [affine_zero, volumeRatio_zero _ _ _ _ hJ, one_mul]
  unfold currentMixed current weightedInverse
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, add_mul]
  simp_rw [connectionMixed_symm J K H, mul_assoc]
  ring

/-- Symmetric mixed time/radial-angular block with both angular components retained. -/
def mixedMatrix (T R : Fin 2 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,T 0,T 1; 0,0,R 0,R 1; T 0,R 0,0,0; T 1,R 1,0,0]

/-- Arbitrary complete first metric jet in the mixed sector. The action current does not use its second jet. -/
def mixedJet (T R : Fin 2 → ℂ) (dT dR : Fin 4 → Fin 2 → ℂ) : CoordinateMetricTwoJet 4 ℂ where
  metric := mixedMatrix T R
  first k := mixedMatrix (dT k) (dR k)
  second _ _ := 0

private theorem bg_first (r y : ℂ) (k : Fin 4) :
    (RHTower.D4BMBackground.jet r y).first k = Matrix.diagonal
      (if k = 1 then ![-2*r,-2*r*(r^2-1)⁻¹^2,2*r*y⁻¹^2,2*r*y⁻¹^2]
       else if k = 3 then ![0,0,-2*r^2*y⁻¹^3,-2*r^2*y⁻¹^3] else 0) := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem radial_current_chart (r y : ℂ)
    (T R U V : Fin 2 → ℂ) (dT dR dU dV : Fin 4 → Fin 2 → ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    r^2/y^2 * actionSymplectic (RHTower.D4BMBackground.jet r y)
      (mixedJet T R dT dR) (mixedJet U V dU dV) 1 =
      ∑ a : Fin 2, (T a*(dV 0 a-dU 1 a)-U a*(dR 0 a-dT 1 a)) := by
  have hdet : (RHTower.D4BMBackground.jet r y).metric.det ≠ 0 := by
    change (RHTower.D4BMBackground.metric r y).det ≠ 0
    rw [RHTower.D4BMBackground.metric_det r y hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  rw [actionSymplectic_eq _ _ _ hdet]
  simp only [weightedInverse, connection, inverse, bg_first,
    show (RHTower.D4BMBackground.jet r y).metric = RHTower.D4BMBackground.metric r y from rfl,
    RHTower.D4BMBackground.metric_inverse r y hr hy hf]
  simp [mixedJet, mixedMatrix, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ]
  field_simp [hr,hy,hf]
  ring

/-- Exact Einstein radial symplectic density on the original exterior geometry.
All derivatives of the action current and its volume weight are differentiated;
all mixed metric first jets are free. No field equation or cancellation is assumed. -/
theorem mixed_radial_action_current (p : D4BMBackground.ExteriorPoint)
    (T R U V : Fin 2 → ℂ) (dT dR dU dV : Fin 4 → Fin 2 → ℂ) :
    (p.val 1:ℂ)^2/(p.val 3:ℂ)^2 * actionSymplectic
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (mixedJet T R dT dR) (mixedJet U V dU dV) 1 =
      ∑ a : Fin 2, (T a*(dV 0 a-dU 1 a)-U a*(dR 0 a-dT 1 a)) := by
  have hr : (p.val 1:ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hy : (p.val 3:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hf : (p.val 1:ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^2-1 ≠ 0)
  exact radial_current_chart _ _ T R U V dT dR dU dV hr hy hf

end
end RHTower.D4BMMixedActionCurrent

