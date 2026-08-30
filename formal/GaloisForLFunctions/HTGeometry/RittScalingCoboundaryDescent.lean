import GaloisForLFunctions.HTGeometry.TwistedScalingDescent

/-!
# An inhomogeneous shift equation over a scaled generator descends to the coefficient field

Let `Φ` be a ring endomorphism of a field and let the substitution act on the variable by the pure
scaling `X ↦ ρ·X`.  A coprime fraction `P/Q` solving the *inhomogeneous* relation

`Φ-substitution of P/Q  =  P/Q + β·X`

forces the denominator to be an eigenvector: coprimality of `Q` with `P + β·X·Q` turns the cross
identity into `Q ∣ Q^Φ∘ρ`, degrees agree, and a monic `Q` pins the scalar to `ρ ^ deg Q`.  Comparing
the coefficient of `X ^ (deg Q + 1)` in the numerator identity then leaves a relation in the
coefficient field alone:

`Φ(a)·ρ = a + β`.

Only the *inhomogeneous* index matters, so no case distinction on the degree of `P` is needed: if
the numerator has degree below `deg Q + 1` the coefficient is zero and the relation reads `β = 0`.

This is the descent step that reduces the second-order case of Ritt's theorem to the rational
affine-connection equation `a(R)·(R′)² = R′·a − R″`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- **The inhomogeneous coprime descent.**  A coprime fraction solving a first-order inhomogeneous
shift equation over a scaled generator produces a solution of the corresponding scalar equation in
the coefficient field. -/
theorem exists_shift_solution_of_scaling_cross (Φ : K →+* K) {ρ β : K} (hρ : ρ ≠ 0)
    {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C ρ * X) P * Q
      = twistComp Φ (C ρ * X) Q * (P + C β * X * Q)) :
    ∃ a : K, Φ a * ρ = a + β := by
  classical
  have hTdeg : (C ρ * X : K[X]).natDegree = 1 := natDegree_scaleSubst hρ
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  set e : ℕ := Q.natDegree with he
  -- the denominator is an eigenvector
  have hcopQ : IsCoprime Q (P + C β * X * Q) := by
    have h := hcop.symm.add_mul_left_right (C β * X)
    have heq : P + Q * (C β * X) = P + C β * X * Q := by ring
    rwa [heq] at h
  have hdvd : Q ∣ twistComp Φ (C ρ * X) Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨twistComp Φ (C ρ * X) P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  -- the scalar is `ρ ^ deg Q`
  have hde : d = ρ ^ e := by
    have hj := coeff_eigen_of_twistComp_scale Φ hd e
    rw [hQ.coeff_natDegree, map_one, one_mul, mul_one] at hj
    exact hj.symm
  -- cancel the denominator in the cross identity
  have hnum : twistComp Φ (C ρ * X) P = C (ρ ^ e) * (P + C β * X * Q) := by
    refine mul_right_cancel₀ hQ0 ?_
    rw [hcross, hd, hde]
    ring
  -- read off the coefficient one above the degree of the denominator
  have hcoeff := congrArg (fun p : K[X] => p.coeff (e + 1)) hnum
  simp only [coeff_twistComp_scale, coeff_C_mul, coeff_add] at hcoeff
  have hXQ : (C β * X * Q).coeff (e + 1) = β * Q.coeff e := by
    rw [mul_assoc, coeff_C_mul, coeff_X_mul]
  rw [hXQ, hQ.coeff_natDegree] at hcoeff
  refine ⟨P.coeff (e + 1), ?_⟩
  have hρe : (ρ : K) ^ e ≠ 0 := pow_ne_zero _ hρ
  have hexp : Φ (P.coeff (e + 1)) * ρ ^ (e + 1) = ρ ^ e * (P.coeff (e + 1) + β * 1) := hcoeff
  refine mul_left_cancel₀ hρe ?_
  linear_combination hexp

end GaloisForLFunctions.HTGeometry
