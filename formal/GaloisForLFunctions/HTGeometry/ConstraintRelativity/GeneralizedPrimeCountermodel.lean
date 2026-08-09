import Mathlib

/-!
# The generalized-prime compound countermodel

For a free abelian group of generalized-prime valuations, the group algebra carries a grading, a
radial character action `Γ_c`, valuation derivations `∂_j`, an identity-coefficient trace, and
prime/inverse-prime atoms `u_i` with `τ(u_i) = 1`, `φ_j(u_i) = −δ_ij` and `Γ_c^{⊗2} u_i = u_i`.

On the reciprocal two-leg space the twisted transports preserve the indefinite Stokes form for
*every* real `c`, while the scalar radial defect `1 − P_i^{2c}` is nonzero for every `c ≠ 0`, and
the contracted scalar port defect has rank one while the uncontracted coframe defect is injective.

So the whole organ conjunction is realized at every nonzero drift: no theorem using only these
identities can force `c = 0`.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix

/-! ## The reciprocal two-leg transport preserves the Stokes form -/

/-- The indefinite Stokes form on the reciprocal two-leg space. -/
def stokesForm : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The twisted diagonal transport at generalized prime norm `P` and drift `c`. -/
noncomputable def legTransport (P c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![P ^ c, 0; 0, P ^ (-c)]

/-- **Card `(7)`.**  The twisted transport preserves the indefinite Stokes form for every real
drift. -/
theorem legTransport_stokes (P c : ℝ) (hP : 0 < P) :
    (legTransport P c)ᵀ * stokesForm * legTransport P c = stokesForm := by
  have hpow : P ^ c * P ^ (-c) = 1 := by
    rw [← Real.rpow_add hP]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [legTransport, stokesForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      hpow, mul_comm]

/-! ## The scalar radial defect -/

/-- **Card `(8)`.**  The scalar radial defect `1 − P^{2c}` is nonzero at every nonzero drift. -/
theorem radialDefect_ne_zero {P c : ℝ} (hP : 1 < P) (hc : c ≠ 0) : 1 - P ^ (2 * c) ≠ 0 := by
  intro h
  have hpow : P ^ (2 * c) = 1 := by linarith
  have hlog : (2 * c) * Real.log P = 0 := by
    have := congrArg Real.log hpow
    rwa [Real.log_rpow (lt_trans zero_lt_one hP), Real.log_one] at this
  have hlogP : Real.log P ≠ 0 := ne_of_gt (Real.log_pos hP)
  rcases mul_eq_zero.1 hlog with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · norm_num at h2
    · exact hc h2
  · exact hlogP h1

/-! ## The contracted scalar port defect has rank one -/

variable {ι : Type*} [Fintype ι]

/-- **Card `(8a)`.**  The contracted scalar port defect. -/
noncomputable def scalarPortDefect (P : ι → ℝ) (c : ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ i, a i * (1 - P i ^ (2 * c))
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_mul]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro r x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp]
theorem scalarPortDefect_apply (P : ι → ℝ) (c : ℝ) (a : ι → ℝ) :
    scalarPortDefect P c a = ∑ i, a i * (1 - P i ^ (2 * c)) := rfl

/-- The contracted scalar port defect is nonzero, hence of rank one. -/
theorem scalarPortDefect_ne_zero [DecidableEq ι] {P : ι → ℝ} {c : ℝ} (i₀ : ι)
    (hP : ∀ i, 1 < P i) (hc : c ≠ 0) : scalarPortDefect P c ≠ 0 := by
  intro h
  have hval : scalarPortDefect P c (Pi.single i₀ 1) = 0 := by rw [h]; rfl
  rw [scalarPortDefect_apply] at hval
  rw [Finset.sum_eq_single i₀] at hval
  · simp only [Pi.single_eq_same, one_mul] at hval
    exact radialDefect_ne_zero (hP i₀) hc hval
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hcon
    simp at hcon

omit [Fintype ι] in
/-- **Card, hostile audit item 4.**  The uncontracted coframe defect is diagonal and injective, so
it is not of rank one. -/
noncomputable def coframeDefect (P : ι → ℝ) (c : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun a := fun i => a i * (1 - P i ^ (2 * c))
  map_add' := by intro x y; funext i; simp [add_mul]
  map_smul' := by intro r x; funext i; simp; ring

omit [Fintype ι] in
@[simp]
theorem coframeDefect_apply (P : ι → ℝ) (c : ℝ) (a : ι → ℝ) (i : ι) :
    coframeDefect P c a i = a i * (1 - P i ^ (2 * c)) := rfl

omit [Fintype ι] in
theorem coframeDefect_injective {P : ι → ℝ} {c : ℝ} (hP : ∀ i, 1 < P i) (hc : c ≠ 0) :
    Function.Injective (coframeDefect P c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  funext i
  have hi : a i * (1 - P i ^ (2 * c)) = 0 := congrFun ha i
  rcases mul_eq_zero.1 hi with h | h
  · exact h
  · exact absurd h (radialDefect_ne_zero (hP i) hc)

/-! ## The generalized-prime group algebra -/

section GroupAlgebra

variable (ι : Type*) [DecidableEq ι]

/-- **Card `(1)`.**  The free abelian group of generalized-prime valuations. -/
abbrev PrimeGrades : Type _ := ι →₀ ℤ

/-- **Card `(1)`.**  The generalized-prime group algebra. -/
abbrev PrimeAlgebra : Type _ := AddMonoidAlgebra ℂ (PrimeGrades ι)

variable {ι}

/-- The coefficient linear equivalence of the group algebra. -/
noncomputable def coeffLinearEquiv : PrimeAlgebra ι ≃ₗ[ℂ] (PrimeGrades ι →₀ ℂ) where
  toFun := AddMonoidAlgebra.coeff
  invFun := AddMonoidAlgebra.ofCoeff
  map_add' := AddMonoidAlgebra.coeff_add
  map_smul' := AddMonoidAlgebra.coeff_smul
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq ι] in
@[simp]
theorem coeffLinearEquiv_single (g : PrimeGrades ι) (a : ℂ) :
    coeffLinearEquiv (AddMonoidAlgebra.single g a) = Finsupp.single g a := rfl

/-- **Card `(3)`.**  The valuation derivation `∂_j`. -/
noncomputable def valuationDeriv (j : ι) : PrimeAlgebra ι →ₗ[ℂ] PrimeAlgebra ι :=
  (coeffLinearEquiv (ι := ι)).symm.toLinearMap.comp
    ((Finsupp.lsum ℂ fun g : PrimeGrades ι => ((g j : ℂ)) • Finsupp.lsingle g).comp
      (coeffLinearEquiv (ι := ι)).toLinearMap)

omit [DecidableEq ι] in
@[simp]
theorem valuationDeriv_single (j : ι) (g : PrimeGrades ι) (a : ℂ) :
    valuationDeriv j (AddMonoidAlgebra.single g a)
      = AddMonoidAlgebra.single g ((g j : ℂ) * a) := by
  classical
  apply (coeffLinearEquiv (ι := ι)).injective
  simp [valuationDeriv, coeffLinearEquiv, Finsupp.smul_single]

/-- **Card `(3)`.**  The identity-coefficient trace. -/
noncomputable def gradeTrace : PrimeAlgebra ι →ₗ[ℂ] ℂ :=
  (Finsupp.lapply 0).comp (coeffLinearEquiv (ι := ι)).toLinearMap

@[simp]
theorem gradeTrace_single (g : PrimeGrades ι) (a : ℂ) :
    gradeTrace (AddMonoidAlgebra.single g a) = if g = 0 then a else 0 := by
  simp [gradeTrace, coeffLinearEquiv, Finsupp.single_apply]

omit [DecidableEq ι] in
/-- **Card `(3)`, Leibniz.**  The valuation map is a derivation on the monomial basis. -/
theorem valuationDeriv_single_mul (j : ι) (g h : PrimeGrades ι) (a b : ℂ) :
    valuationDeriv j (AddMonoidAlgebra.single g a * AddMonoidAlgebra.single h b)
      = valuationDeriv j (AddMonoidAlgebra.single g a) * AddMonoidAlgebra.single h b
        + AddMonoidAlgebra.single g a * valuationDeriv j (AddMonoidAlgebra.single h b) := by
  rw [AddMonoidAlgebra.single_mul_single, valuationDeriv_single, valuationDeriv_single,
    valuationDeriv_single, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.single_add]
  congr 1
  simp only [Finsupp.coe_add, Pi.add_apply]
  push_cast
  ring

/-- **Card `(2)`.**  The generalized-prime norm of a grade. -/
noncomputable def gradeNorm (P : ι → ℝ) (g : PrimeGrades ι) : ℝ :=
  g.prod fun i n => P i ^ n

omit [DecidableEq ι] in
@[simp]
theorem gradeNorm_zero (P : ι → ℝ) : gradeNorm P 0 = 1 := by
  simp [gradeNorm]

omit [DecidableEq ι] in
/-- **Card `(2)`.**  The generalized-prime norm is multiplicative on grades, so the radial
character is an algebra map on the monomial basis. -/
theorem gradeNorm_add (P : ι → ℝ) (hP : ∀ i, P i ≠ 0) (g h : PrimeGrades ι) :
    gradeNorm P (g + h) = gradeNorm P g * gradeNorm P h := by
  refine Finsupp.prod_add_index' (fun i => ?_) (fun i m n => ?_)
  · simp
  · exact zpow_add₀ (hP i) m n

omit [DecidableEq ι] in
/-- **Card `(5)`.**  The prime/inverse-prime atom has total grade zero, so the radial character
acts on it trivially at every drift. -/
theorem gradeNorm_primeAtom (P : ι → ℝ) (hP : ∀ i, P i ≠ 0) (i : ι) :
    gradeNorm P (Finsupp.single i (1 : ℤ)) * gradeNorm P (Finsupp.single i (-1 : ℤ)) = 1 := by
  rw [← gradeNorm_add P hP, ← Finsupp.single_add]
  simp

omit [DecidableEq ι] in
/-- **Card `(5)`.**  The prime/inverse-prime atom has identity grade. -/
theorem primeAtom_grade (i : ι) :
    (AddMonoidAlgebra.single (Finsupp.single i (1 : ℤ)) (1 : ℂ) : PrimeAlgebra ι)
        * AddMonoidAlgebra.single (Finsupp.single i (-1 : ℤ)) 1
      = AddMonoidAlgebra.single 0 1 := by
  rw [AddMonoidAlgebra.single_mul_single, ← Finsupp.single_add]
  simp

/-- **Card `(5)`, first identity.**  The trace of a prime atom is one. -/
theorem gradeTrace_primeAtom (i : ι) :
    gradeTrace ((AddMonoidAlgebra.single (Finsupp.single i (1 : ℤ)) (1 : ℂ) : PrimeAlgebra ι)
      * AddMonoidAlgebra.single (Finsupp.single i (-1 : ℤ)) 1) = 1 := by
  rw [primeAtom_grade]
  simp

/-- **Card `(5)`, second identity.**  The valuation pairing on a prime atom is `−δ_ij`. -/
theorem valuationPairing_primeAtom (i j : ι) :
    gradeTrace ((AddMonoidAlgebra.single (Finsupp.single i (1 : ℤ)) (1 : ℂ) : PrimeAlgebra ι)
      * valuationDeriv j (AddMonoidAlgebra.single (Finsupp.single i (-1 : ℤ)) 1))
      = if j = i then -1 else 0 := by
  rw [valuationDeriv_single, AddMonoidAlgebra.single_mul_single, ← Finsupp.single_add]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- **Card `(2)`.**  The dagger: conjugate-linear and grade-reversing. -/
noncomputable def primeDagger (x : PrimeAlgebra ι) : PrimeAlgebra ι :=
  AddMonoidAlgebra.ofCoeff ((x.coeff.mapDomain Neg.neg).mapRange (starRingEnd ℂ) (map_zero _))

omit [DecidableEq ι] in
@[simp]
theorem primeDagger_single (g : PrimeGrades ι) (a : ℂ) :
    primeDagger (AddMonoidAlgebra.single g a)
      = AddMonoidAlgebra.single (-g) (starRingEnd ℂ a) := by
  have h : (((AddMonoidAlgebra.single g a : PrimeAlgebra ι).coeff.mapDomain Neg.neg).mapRange
      (starRingEnd ℂ) (map_zero _)) = Finsupp.single (-g) (starRingEnd ℂ a) := by
    rw [AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single, Finsupp.mapRange_single]
  rw [primeDagger, h]
  rfl

omit [DecidableEq ι] in
/-- **Card `(2)`.**  The dagger is an involution. -/
theorem primeDagger_primeDagger_single (g : PrimeGrades ι) (a : ℂ) :
    primeDagger (primeDagger (AddMonoidAlgebra.single g a)) = AddMonoidAlgebra.single g a := by
  simp

omit [DecidableEq ι] in
/-- **Card `(2)`.**  The dagger reverses the grade, hence is antimultiplicative. -/
theorem primeDagger_mul_single (g h : PrimeGrades ι) (a b : ℂ) :
    primeDagger ((AddMonoidAlgebra.single g a : PrimeAlgebra ι) * AddMonoidAlgebra.single h b)
      = primeDagger (AddMonoidAlgebra.single h b) * primeDagger (AddMonoidAlgebra.single g a) := by
  rw [AddMonoidAlgebra.single_mul_single, primeDagger_single, primeDagger_single,
    primeDagger_single, AddMonoidAlgebra.single_mul_single]
  rw [neg_add, add_comm (-h) (-g), map_mul, mul_comm (starRingEnd ℂ b)]

omit [DecidableEq ι] in
/-- The generalized-prime norm is positive. -/
theorem gradeNorm_pos {P : ι → ℝ} (hP : ∀ i, 0 < P i) (g : PrimeGrades ι) :
    0 < gradeNorm P g :=
  Finset.prod_pos fun i _ => zpow_pos (hP i) _

/-- **Card `(2)`.**  The radial character `Γ_c`. -/
noncomputable def radialChar (P : ι → ℝ) (c : ℝ) : PrimeAlgebra ι →ₗ[ℂ] PrimeAlgebra ι :=
  (coeffLinearEquiv (ι := ι)).symm.toLinearMap.comp
    ((Finsupp.lsum ℂ fun g : PrimeGrades ι =>
        ((gradeNorm P g ^ c : ℝ) : ℂ) • Finsupp.lsingle g).comp
      (coeffLinearEquiv (ι := ι)).toLinearMap)

omit [DecidableEq ι] in
@[simp]
theorem radialChar_single (P : ι → ℝ) (c : ℝ) (g : PrimeGrades ι) (a : ℂ) :
    radialChar P c (AddMonoidAlgebra.single g a)
      = AddMonoidAlgebra.single g (((gradeNorm P g ^ c : ℝ) : ℂ) * a) := by
  classical
  apply (coeffLinearEquiv (ι := ι)).injective
  simp [radialChar, coeffLinearEquiv, Finsupp.smul_single]

omit [DecidableEq ι] in
/-- **Card `(2)`.**  `Γ_c` is multiplicative on the monomial basis: it is an algebra
automorphism of the generalized-prime algebra. -/
theorem radialChar_mul_single {P : ι → ℝ} (hP : ∀ i, 0 < P i) (c : ℝ)
    (g h : PrimeGrades ι) (a b : ℂ) :
    radialChar P c ((AddMonoidAlgebra.single g a : PrimeAlgebra ι) * AddMonoidAlgebra.single h b)
      = radialChar P c (AddMonoidAlgebra.single g a)
        * radialChar P c (AddMonoidAlgebra.single h b) := by
  rw [AddMonoidAlgebra.single_mul_single, radialChar_single, radialChar_single,
    radialChar_single, AddMonoidAlgebra.single_mul_single]
  congr 1
  rw [gradeNorm_add P (fun i => (hP i).ne') g h,
    Real.mul_rpow (gradeNorm_pos hP g).le (gradeNorm_pos hP h).le]
  push_cast
  ring

omit [DecidableEq ι] in
/-- **Card `(5)`, third identity.**  The radial character acts trivially on a prime atom at every
drift: the atom has total grade zero. -/
theorem radialChar_primeAtom {P : ι → ℝ} (hP : ∀ i, 0 < P i) (c : ℝ) (i : ι) :
    ((gradeNorm P (Finsupp.single i (1 : ℤ)) ^ c : ℝ))
        * ((gradeNorm P (Finsupp.single i (-1 : ℤ)) ^ c : ℝ)) = 1 := by
  rw [← Real.mul_rpow (gradeNorm_pos hP _).le (gradeNorm_pos hP _).le,
    ← gradeNorm_add P (fun i => (hP i).ne'), ← Finsupp.single_add]
  simp

end GroupAlgebra

end HTGeometry.ConstraintRelativity
