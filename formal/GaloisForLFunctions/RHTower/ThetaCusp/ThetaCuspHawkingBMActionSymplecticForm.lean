import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedRadialActionCurrent
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinDiagonalCollapse

/-!
# The Einstein action symplectic current as an explicit bilinear form

The antisymmetrized first variation `actionSymplectic J H K a` of the volume-weighted Einstein
boundary current is expressed as an explicit bilinear form in the two perturbation jets: the
trace-weighted inverse metric variation of one jet contracted with the linearized Christoffel
variation of the other, antisymmetrized (`actionSymplectic_eq_form`). Over a diagonal background
every inverse-metric factor is a reciprocal diagonal entry (`actionSymplectic_diagonal_eq`), so the
current of two explicit jets is a finite rational expression in their entries.
-/

set_option autoImplicit false

namespace RHTower.D4BMActionSymplecticForm
open GaloisForLFunctions.HTGeometry
open CoordinateMetricTwoJet CoordinateMetricTwoJet.Linearization
open EinsteinActionBoundary MetricPathDensity RHTower.D4BMMixedActionCurrent
noncomputable section

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

/-- Mixed second-order inverse-metric variation along two jets. -/
def inverseMixed (J H K : Jet) : Mat :=
  -(inverse J H * K.metric * J.metric⁻¹ + J.metric⁻¹ * K.metric * inverse J H)

theorem inverseMixed_symm (J H K : Jet) : inverseMixed J H K = inverseMixed J K H := by
  unfold inverseMixed inverse
  noncomm_ring

theorem inverseMixed_derivative (J H K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => inverse (affine J H t) K i j) (inverseMixed J H K i j) 0 := by
  have hi := inverse_hasDerivAt J H hJ
  have hk (i j : Fin d) : HasDerivAt (fun _ : ℂ => K.metric i j) ((0:Mat) i j) 0 :=
    hasDerivAt_const (0:ℂ) (K.metric i j)
  have hp := mat_mul (mat_mul hi hk) hi i j
  simpa [inverse, inverseMixed, affine_zero] using hp.fun_neg

/-- Mixed second-order Christoffel variation along two jets. -/
def connectionMixed (J H K : Jet) (u i j : Fin d) : ℂ :=
  (1/2:ℂ) * ∑ m,
    (inverseMixed J H K u m * (J.first i m j + J.first j m i - J.first m i j) +
     inverse J K u m * (H.first i m j + H.first j m i - H.first m i j) +
     inverse J H u m * (K.first i m j + K.first j m i - K.first m i j))

theorem connectionMixed_symm (J H K : Jet) (u i j : Fin d) :
    connectionMixed J H K u i j = connectionMixed J K H u i j := by
  unfold connectionMixed
  rw [inverseMixed_symm]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem connectionMixed_derivative (J H K : Jet) (hJ : J.metric.det ≠ 0) (u i j : Fin d) :
    HasDerivAt (fun t => connection (affine J H t) K u i j) (connectionMixed J H K u i j) 0 := by
  have hf (a b c : Fin d) : HasDerivAt (fun t => (affine J H t).first a b c) (H.first a b c) 0 := by
    simpa [affine] using ((hasDerivAt_id (0:ℂ)).mul_const (H.first a b c)).const_add (J.first a b c)
  have hp (m : Fin d) := ((hf i m j).add (hf j m i)).sub (hf m i j)
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
    ((inverseMixed_derivative J H K hJ u m).mul (hp m)).add
      ((inverse_hasDerivAt J H hJ u m).mul_const
        (K.first i m j+K.first j m i-K.first m i j)))).const_mul (1/2:ℂ)
  simpa only [connection, connectionMixed, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, affine_zero] using h

/-- Mixed first variation of the connection current. -/
def currentMixed (J H K : Jet) (a : Fin d) : ℂ :=
  (∑ i, ∑ j, (inverse J H i j * connection J K a j i +
    J.metric⁻¹ i j * connectionMixed J H K a j i)) -
  ∑ i, ∑ u, (inverse J H i a * connection J K u u i +
    J.metric⁻¹ i a * connectionMixed J H K u u i)

theorem currentMixed_derivative (J H K : Jet) (hJ : J.metric.det ≠ 0) (a : Fin d) :
    HasDerivAt (fun t => current (affine J H t) K a) (currentMixed J H K a) 0 := by
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (inverse_hasDerivAt J H hJ i j).mul (connectionMixed_derivative J H K hJ a j i)))
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun u _ =>
      (inverse_hasDerivAt J H hJ i a).mul (connectionMixed_derivative J H K hJ u u i)))
  simpa only [current, currentMixed, Pi.mul_apply, affine_zero] using h1.fun_sub h2

/-- Trace-weighted inverse-metric variation of a jet. -/
def weightedInverse (J H : Jet) : Mat :=
  ((J.metric⁻¹*H.metric).trace/2) • J.metric⁻¹ + inverse J H

/-- The symplectic current as the antisymmetrized contraction of the weighted inverse variation
with the linearized Christoffel variation. -/
theorem actionSymplectic_eq_form (J H K : Jet) (hJ : J.metric.det ≠ 0) (a : Fin d) :
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

/-- Over a diagonal background the weighted inverse variation is explicit in the entries. -/
theorem weightedInverse_apply_of_diagonal {J : Jet} (h : IsDiagonalJet J) (H : Jet) (i j : Fin d) :
    weightedInverse J H i j =
      (∑ k, H.metric k k / J.metric k k) / 2 * (if i = j then (J.metric i i)⁻¹ else 0) -
        H.metric i j / (J.metric i i * J.metric j j) := by
  unfold weightedInverse
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h.linearization_inverse_apply, h.inv_apply]
  have htr : (J.metric⁻¹ * H.metric).trace = ∑ k, H.metric k k / J.metric k k := by
    rw [h.inv_eq, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.diagonal_mul, div_eq_inv_mul]
  rw [htr]
  ring

end
end RHTower.D4BMActionSymplecticForm
