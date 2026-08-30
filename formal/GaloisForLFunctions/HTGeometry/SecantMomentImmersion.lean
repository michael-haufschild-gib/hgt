import GaloisForLFunctions.HTGeometry.SecantMomentIndependence

/-!
# The moment map is an immersion off the deeper secant stratum

The Jacobian of the first `2r` moments at a configuration of `r` atoms is the confluent Vandermonde
matrix of the nodes with its derivative rows scaled by the amplitudes.  It is therefore invertible
exactly when the nodes are distinct and the amplitudes are nonzero — that is, at every configuration
whose moment sequence has Hankel rank exactly `r`.

So the `r`-th Hankel secant variety is smooth at every point of `C_k` off `C_{k+1}`, which is the
smoothness half of `Sing(C_k) = C_{k+1}`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset
open MvPolynomial (pderiv)

variable {K : Type*} [Field K] {r : ℕ}

/-- The amplitude scaling of the derivative rows. -/
noncomputable def confluentAmplitudeDiagonal (u : Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.diagonal (Sum.elim (fun _ => 1) u)

/-- The confluent Vandermonde matrix with amplitudes: the Jacobian of the moment map at a point. -/
noncomputable def confluentVandermondeAmp (t u : Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.of fun j k => Sum.elim
    (fun j' : Fin r => t j' ^ confluentExp k)
    (fun j' : Fin r => u j' * (((confluentExp k : ℕ) : K) * t j' ^ (confluentExp k - 1))) j

theorem confluentVandermondeAmp_eq (t u : Fin r → K) :
    confluentVandermondeAmp t u = confluentAmplitudeDiagonal u * confluentVandermonde t := by
  classical
  funext j k
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · cases j with
    | inl j' =>
        simp [confluentVandermondeAmp, confluentAmplitudeDiagonal, confluentVandermonde,
          Matrix.diagonal]
    | inr j' =>
        simp [confluentVandermondeAmp, confluentAmplitudeDiagonal, confluentVandermonde,
          Matrix.diagonal]
  · intro p _ hpj
    simp only [confluentAmplitudeDiagonal, Matrix.diagonal, Matrix.of_apply,
      if_neg (Ne.symm hpj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem det_confluentAmplitudeDiagonal (u : Fin r → K) :
    (confluentAmplitudeDiagonal u).det = ∏ j : Fin r, u j := by
  rw [confluentAmplitudeDiagonal, Matrix.det_diagonal, Fintype.prod_sum_type]
  simp

/-- **The moment map is an immersion at distinct nodes with nonzero amplitudes.**  Its Jacobian, the
confluent Vandermonde matrix scaled by the amplitudes, is invertible there. -/
theorem det_confluentVandermondeAmp_ne_zero (t u : Fin r → K) (ht : Function.Injective t)
    (hu : ∀ j, u j ≠ 0) : (confluentVandermondeAmp t u).det ≠ 0 := by
  rw [confluentVandermondeAmp_eq, Matrix.det_mul, det_confluentAmplitudeDiagonal]
  refine mul_ne_zero ?_ (det_confluentVandermonde_ne_zero t ht)
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hu j

/-- The atom configuration with amplitudes `u` and nodes `t`. -/
def secantPoint (t u : Fin r → K) : Fin r × Fin 2 → K :=
  fun p => if p.2 = 0 then u p.1 else t p.1

theorem map_eval_momentJacobian (t u : Fin r → K) :
    (MvPolynomial.polynomialJacobianMinor
        (fun k : Fin r ⊕ Fin r => secantMomentPoly K r (confluentExp k))
        (secantCoordinate r)).map (MvPolynomial.eval (secantPoint t u))
      = confluentVandermondeAmp t u := by
  classical
  funext j k
  cases j with
  | inl j' =>
      simp only [Matrix.map_apply, MvPolynomial.polynomialJacobianMinor, secantCoordinate,
        Sum.elim_inl, confluentVandermondeAmp, Matrix.of_apply, Sum.elim_inl]
      rw [pderiv_amplitude_secantMomentPoly]
      simp [secantPoint]
  | inr j' =>
      simp only [Matrix.map_apply, MvPolynomial.polynomialJacobianMinor, secantCoordinate,
        Sum.elim_inr, confluentVandermondeAmp, Matrix.of_apply, Sum.elim_inr]
      rw [pderiv_node_secantMomentPoly]
      simp [secantPoint]

/-- **The moment map is an immersion at every configuration of distinct nodes with nonzero
amplitudes.**  Its Jacobian determinant does not vanish there, so the Hankel secant variety is
smooth at every point of `C_k` that is not on `C_{k+1}`. -/
theorem det_momentJacobian_eval_ne_zero (t u : Fin r → K) (ht : Function.Injective t)
    (hu : ∀ j, u j ≠ 0) :
    MvPolynomial.eval (secantPoint t u)
        ((MvPolynomial.polynomialJacobianMinor
          (fun k : Fin r ⊕ Fin r => secantMomentPoly K r (confluentExp k))
          (secantCoordinate r)).det) ≠ 0 := by
  intro h
  have hd := RingHom.map_det (MvPolynomial.eval (secantPoint t u))
    (MvPolynomial.polynomialJacobianMinor
      (fun k : Fin r ⊕ Fin r => secantMomentPoly K r (confluentExp k)) (secantCoordinate r))
  rw [RingHom.mapMatrix_apply, map_eval_momentJacobian] at hd
  exact det_confluentVandermondeAmp_ne_zero t u ht hu (hd ▸ h)


end GaloisForLFunctions.HTGeometry
