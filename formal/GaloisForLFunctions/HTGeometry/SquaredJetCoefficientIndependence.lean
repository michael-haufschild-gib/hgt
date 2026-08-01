import GaloisForLFunctions.HTGeometry.TailCoefficientIndependence

/-!
# The coefficients of the square of a normalised jet are independent coordinates

Write a jet with constant term one as `1 + z_1 t + z_2 t^2 + …`.  The coefficient of `t^k` in its
square is `2 z_k` plus a polynomial in the earlier coefficients, so the change of coordinates from
the jet coefficients to the coefficients of the square is triangular with diagonal two.

In characteristic zero that makes the coefficients of the square algebraically independent: they are
again free coordinates on the jet space.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- The coefficients of a normalised jet: constant term one, then the free variables. -/
noncomputable def jetCoeff (K : Type*) [Field K] (N : ℕ) (a : ℕ) : MvPolynomial (Fin N) K :=
  if a = 0 then 1 else if h : a - 1 < N then MvPolynomial.X ⟨a - 1, h⟩ else 0

/-- The coefficients of the square of a normalised jet. -/
noncomputable def sqJetCoeff (K : Type*) [Field K] (N : ℕ) (k : ℕ) : MvPolynomial (Fin N) K :=
  ∑ a ∈ Finset.range (k + 1), jetCoeff K N a * jetCoeff K N (k - a)

/-- Setting every jet coefficient to zero. -/
noncomputable def jetZero (K : Type*) [Field K] (N : ℕ) : MvPolynomial (Fin N) K →ₐ[K] K :=
  MvPolynomial.aeval (fun _ => 0)

omit [CharZero K] in
theorem jetZero_jetCoeff (a : ℕ) :
    jetZero K N (jetCoeff K N a) = if a = 0 then 1 else 0 := by
  rw [jetCoeff]
  by_cases h : a = 0
  · rw [if_pos h, if_pos h, map_one]
  · rw [if_neg h, if_neg h]
    by_cases h1 : a - 1 < N
    · rw [dif_pos h1, jetZero, MvPolynomial.aeval_X]
    · rw [dif_neg h1, map_zero]

omit [CharZero K] in
theorem jetZero_pderiv_jetCoeff (j : Fin N) (a : ℕ) :
    jetZero K N (MvPolynomial.pderiv j (jetCoeff K N a)) =
      if a = (j : ℕ) + 1 then 1 else 0 := by
  have hj := j.isLt
  rw [jetCoeff]
  by_cases h : a = 0
  · rw [if_pos h, Derivation.map_one_eq_zero, map_zero,
      if_neg (by omega : ¬ a = (j : ℕ) + 1)]
  · rw [if_neg h]
    by_cases h1 : a - 1 < N
    · rw [dif_pos h1]
      by_cases h2 : a = (j : ℕ) + 1
      · have hfin : (⟨a - 1, h1⟩ : Fin N) = j := by
          refine Fin.ext ?_
          show a - 1 = (j : ℕ)
          omega
        rw [hfin, MvPolynomial.pderiv_X_self, map_one, if_pos h2]
      · have hne : (⟨a - 1, h1⟩ : Fin N) ≠ j := by
          intro hcon
          have hval : a - 1 = (j : ℕ) := congrArg Fin.val hcon
          exact h2 (by omega)
        rw [MvPolynomial.pderiv_X_of_ne hne, map_zero, if_neg h2]
    · rw [dif_neg h1, map_zero, map_zero, if_neg (by omega : ¬ a = (j : ℕ) + 1)]


omit [CharZero K] in
/-- **The specialised derivative of a square coefficient.**  At the origin the derivative of the
`m`-th coefficient of the square in the `j`-th jet coefficient is two when `m = j + 1` and zero
otherwise. -/
theorem jetZero_pderiv_sqJetCoeff (j : Fin N) (m : ℕ) :
    jetZero K N (MvPolynomial.pderiv j (sqJetCoeff K N m)) =
      if m = (j : ℕ) + 1 then 2 else 0 := by
  have hterm : ∀ a ∈ Finset.range (m + 1),
      jetZero K N (MvPolynomial.pderiv j (jetCoeff K N a * jetCoeff K N (m - a))) =
        (if a = (j : ℕ) + 1 then 1 else 0) * (if m - a = 0 then 1 else 0) +
          (if a = 0 then 1 else 0) * (if m - a = (j : ℕ) + 1 then 1 else 0) := by
    intro a _
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
      jetZero_pderiv_jetCoeff, jetZero_jetCoeff, jetZero_jetCoeff, jetZero_pderiv_jetCoeff]
    ring
  rw [sqJetCoeff, map_sum, map_sum, Finset.sum_congr rfl hterm]
  by_cases hm : m = (j : ℕ) + 1
  · rw [if_pos hm]
    have hzero : (0 : ℕ) ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hne : (0 : ℕ) ≠ m := by omega
    rw [Finset.sum_eq_add_of_mem 0 m hzero hmem hne ?_]
    · rw [if_neg (by omega : ¬ (0 : ℕ) = (j : ℕ) + 1), if_pos rfl,
        if_pos (by omega : m - m = 0), if_pos hm, if_neg (by omega : ¬ m = 0),
        show m - 0 = m by omega, if_pos hm]
      ring
    · intro a ha ha0
      obtain ⟨ha1, ha2⟩ := ha0
      rw [Finset.mem_range] at ha
      rw [if_neg (by omega : ¬ a = (j : ℕ) + 1), if_neg ha1]
      ring
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mem_range] at ha
    by_cases ha0 : a = 0
    · rw [if_pos ha0, if_neg (by omega : ¬ a = (j : ℕ) + 1),
        if_neg (by omega : ¬ m - a = (j : ℕ) + 1)]
      ring
    · rw [if_neg ha0]
      by_cases haj : a = (j : ℕ) + 1
      · rw [if_pos haj, if_neg (by omega : ¬ m - a = 0)]
        ring
      · rw [if_neg haj]
        ring

/-- The square coefficients indexed by the jet coefficients they replace. -/
noncomputable def sqJetFamily (K : Type*) [Field K] (N : ℕ) (r : Fin N) :
    MvPolynomial (Fin N) K :=
  sqJetCoeff K N ((r : ℕ) + 1)

/-- The Jacobian of the square coefficients against the jet coefficients. -/
noncomputable def sqJetJacobian (K : Type*) [Field K] (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) K) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (sqJetFamily K N j)

omit [CharZero K] in
theorem jetZero_mapMatrix_sqJetJacobian :
    (jetZero K N).toRingHom.mapMatrix (sqJetJacobian K N) =
      Matrix.diagonal (fun _ : Fin N => (2 : K)) := by
  refine Matrix.ext fun i j => ?_
  show jetZero K N (MvPolynomial.pderiv i (sqJetCoeff K N ((j : ℕ) + 1))) = _
  rw [jetZero_pderiv_sqJetCoeff, Matrix.diagonal_apply]
  by_cases h : i = j
  · rw [if_pos (by rw [h]), if_pos h]
  · refine (if_neg ?_).trans (if_neg h).symm
    intro hcon
    exact h (Fin.ext (by omega))

/-- **The Jacobian is nonsingular.** -/
theorem det_sqJetJacobian_ne_zero : (sqJetJacobian K N).det ≠ 0 := by
  intro hcon
  have h : (jetZero K N).toRingHom ((sqJetJacobian K N).det) = 0 := by
    rw [hcon]
    exact map_zero _
  rw [RingHom.map_det, jetZero_mapMatrix_sqJetJacobian, Matrix.det_diagonal] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact pow_ne_zero N (two_ne_zero) h

/-- **The coefficients of the square of a normalised jet are algebraically independent.** -/
theorem algebraicIndependent_sqJetFamily :
    AlgebraicIndependent K (sqJetFamily K N) := by
  classical
  exact algebraicIndependent_of_domain_jacobian
    (K := K) (R := MvPolynomial (Fin N) K)
    (sqJetFamily K N)
    (fun i f => MvPolynomial.pderiv i f)
    (fun i a b => map_add _ a b)
    (fun i a b => by rw [Derivation.leibniz]; simp only [smul_eq_mul])
    (fun i c => Derivation.map_algebraMap _ c)
    (sqJetJacobian K N) det_sqJetJacobian_ne_zero
    (fun i j => rfl)

end GaloisForLFunctions.HTGeometry
