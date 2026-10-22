import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelSecondPivot
import GaloisForLFunctions.HTGeometry.TriangularMvPolynomialSubstitution
import Mathlib.Algebra.MvPolynomial.Monad

namespace RHTower
noncomputable section


open MvPolynomial

/-- Variables of the image of a polynomial ring hom come from images of source variables,
provided coefficients map to constants. -/
theorem mvPolynomial_mem_vars_ringHom_image_of_C
    {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (F : MvPolynomial σ R →+* MvPolynomial τ S) (c : R →+* S)
    (hC : ∀ a, F (MvPolynomial.C a) = MvPolynomial.C (c a))
    {p : MvPolynomial σ R} {v : τ}
    (hv : v ∈ (F p).vars) :
    ∃ i ∈ p.vars, v ∈ (F (MvPolynomial.X i)).vars := by
  have hF : F = MvPolynomial.eval₂Hom
      ((MvPolynomial.C : S →+* MvPolynomial τ S).comp c)
      (fun i => F (MvPolynomial.X i)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hC]
    · intro i
      simp
  rw [hF] at hv
  rw [← MvPolynomial.eval₂Hom_map_hom c
    (fun i => F (MvPolynomial.X i)) MvPolynomial.C p] at hv
  rw [MvPolynomial.eval₂Hom_C_eq_bind₁] at hv
  obtain ⟨i, hi, hvi⟩ := MvPolynomial.mem_vars_bind₁
    (fun i => F (MvPolynomial.X i)) (MvPolynomial.map c p) hv
  exact ⟨i, MvPolynomial.vars_map p c hi, hvi⟩

/-- Map of integral scalars to the generic leading-divisor field. -/
def deningerHazewinkelBoundaryCoeff (r : ℕ) :
    ℤ →+* DeningerHazewinkelBoundaryField r :=
  (deningerHazewinkelLowToBoundary r).comp
    (MvPolynomial.C : ℤ →+* DeningerHazewinkelLowRing (r + 1))

theorem deningerHazewinkelBoundarySpecialization_C (r : ℕ) (a : ℤ) :
    deningerHazewinkelBoundarySpecialization r (MvPolynomial.C a) =
      MvPolynomial.C (deningerHazewinkelBoundaryCoeff r a) := by
  simp [deningerHazewinkelBoundarySpecialization,
    deningerHazewinkelLowTailEquiv, deningerHazewinkelBoundaryCoeff]

theorem deningerHazewinkelBoundarySpecialization_X_low (r : ℕ)
    (i : Fin (2 * (r + 1) + 1)) :
    deningerHazewinkelBoundarySpecialization r
      (MvPolynomial.X i.val) =
      MvPolynomial.C
        (deningerHazewinkelLowToBoundary r (MvPolynomial.X i)) := by
  change MvPolynomial.map (deningerHazewinkelLowToBoundary r)
      (deningerHazewinkelLowTailEquiv (r + 1) (MvPolynomial.X i.val)) = _
  change MvPolynomial.map (deningerHazewinkelLowToBoundary r)
      (deningerHazewinkelLowTailEquiv (r + 1)
        (MvPolynomial.X (deningerHazewinkelLowEmbedding (r + 1) i))) = _
  rw [deningerHazewinkelLowTailEquiv_X_low, MvPolynomial.map_C]

@[simp] theorem deningerHazewinkelBoundarySpecialization_X_tail (r t : ℕ) :
    deningerHazewinkelBoundarySpecialization r
      (MvPolynomial.X (2 * (r + 1) + 1 + t)) =
      MvPolynomial.X t := by
  change MvPolynomial.map (deningerHazewinkelLowToBoundary r)
      (deningerHazewinkelLowTailEquiv (r + 1)
        (MvPolynomial.X (2 * (r + 1) + 1 + t))) = _
  rw [deningerHazewinkelLowTailEquiv_X_tail, MvPolynomial.map_X]

/-- A source polynomial using only coordinates below `cutoff+t` specializes to a tail
polynomial using only coordinates below `t`. -/
theorem deningerHazewinkelBoundarySpecialization_vars_lt
    {r t : ℕ} {p : MvPolynomial ℕ ℤ}
    (hp : ∀ i, i ∈ p.vars → i < 2 * (r + 1) + 1 + t)
    {v : ℕ}
    (hv : v ∈ (deningerHazewinkelBoundarySpecialization r p).vars) :
    v < t := by
  obtain ⟨i, hi, hvi⟩ := mvPolynomial_mem_vars_ringHom_image_of_C
    (deningerHazewinkelBoundarySpecialization r)
    (deningerHazewinkelBoundaryCoeff r)
    (deningerHazewinkelBoundarySpecialization_C r) hv
  have hiBound := hp i hi
  by_cases hiLow : i < 2 * (r + 1) + 1
  · let j : Fin (2 * (r + 1) + 1) := ⟨i, hiLow⟩
    rw [show i = j.val by rfl,
      deningerHazewinkelBoundarySpecialization_X_low] at hvi
    simp at hvi
  · have hiCutoff : 2 * (r + 1) + 1 ≤ i := Nat.le_of_not_gt hiLow
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hiCutoff
    rw [deningerHazewinkelBoundarySpecialization_X_tail] at hvi
    simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using
      (show v < t by
        have hvu : v = u := by simpa using hvi
        omega)

/-- Nonzero diagonal coefficient of the generic-boundary tail system. -/
def deningerHazewinkelBoundaryDiagonal (r : ℕ) :
    DeningerHazewinkelBoundaryField r :=
  -deningerHazewinkelLowToBoundary r
    (deningerHazewinkelLowNextCofactor r)

theorem deningerHazewinkelBoundaryDiagonal_ne_zero (r : ℕ) :
    deningerHazewinkelBoundaryDiagonal r ≠ 0 := by
  simp only [deningerHazewinkelBoundaryDiagonal, neg_ne_zero]
  exact deningerHazewinkelLowToBoundary_nextCofactor_ne_zero r

/-- Lower term of the boundary-specialized special minor. -/
def deningerHazewinkelBoundaryRemainder (r t : ℕ) :
    MvPolynomial ℕ (DeningerHazewinkelBoundaryField r) :=
  deningerHazewinkelBoundarySpecialization r
    (deningerHazewinkelSecondLaplaceRemainder (r + 1) (r + 3 + t))

theorem deningerHazewinkelBoundaryRemainder_vars_lt
    (r t : ℕ) {v : ℕ}
    (hv : v ∈ (deningerHazewinkelBoundaryRemainder r t).vars) :
    v < t := by
  apply deningerHazewinkelBoundarySpecialization_vars_lt
    (r := r) (t := t) (p :=
      deningerHazewinkelSecondLaplaceRemainder (r + 1) (r + 3 + t))
  · intro i hi
    have hlt := deningerHazewinkelSecondLaplaceRemainder_vars_lt
      (k := r + 1) (s := r + 3 + t) (by omega) hi
    omega
  · exact hv

/-- On the generic leading divisor, special minors become a lower-triangular tail family with
constant nonzero diagonal. -/
theorem deningerHazewinkelBoundarySpecialization_specialMinor (r t : ℕ) :
    deningerHazewinkelBoundarySpecialization r
      (deningerHazewinkelSpecialMinor (r + 2) (r + 3 + t)) =
      MvPolynomial.C (deningerHazewinkelBoundaryDiagonal r) *
          MvPolynomial.X t +
        deningerHazewinkelBoundaryRemainder r t := by
  rw [deningerHazewinkelSpecialMinor_second_pivot (by omega : r + 1 + 2 ≤ r + 3 + t)]
  simp only [map_add, map_sub, map_mul,
    deningerHazewinkelBoundarySpecialization_leading, zero_mul, zero_sub,
    deningerHazewinkelBoundaryRemainder]
  rw [show r + 1 + (r + 3 + t) - 1 =
      2 * (r + 1) + 1 + t by omega,
    deningerHazewinkelBoundarySpecialization_X_tail]
  rw [deningerHazewinkelBoundarySpecialization_nextCofactor]
  rw [deningerHazewinkelBoundaryDiagonal, MvPolynomial.C_neg]
  ring

/-- Polynomial substitution generated by all tail special minors on the generic leading divisor. -/
def deningerHazewinkelBoundarySpecialMinorHom (r : ℕ) :
    MvPolynomial ℕ (DeningerHazewinkelBoundaryField r) →+*
      MvPolynomial ℕ (DeningerHazewinkelBoundaryField r) :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun t =>
    deningerHazewinkelBoundarySpecialization r
      (deningerHazewinkelSpecialMinor (r + 2) (r + 3 + t))

/-- Tail special minors are algebraically independent at the generic point of `D_(r+2)=0`.

This is the constructive replacement for the density/Nullstellensatz step in Hazewinkel's
integral saturation argument. -/
theorem deningerHazewinkelBoundarySpecialMinorHom_injective (r : ℕ) :
    Function.Injective (deningerHazewinkelBoundarySpecialMinorHom r) := by
  have hfamily : (fun t => deningerHazewinkelBoundarySpecialization r
      (deningerHazewinkelSpecialMinor (r + 2) (r + 3 + t))) =
      GaloisForLFunctions.HTGeometry.triangularMvPolynomial
        (deningerHazewinkelBoundaryDiagonal r)
        (deningerHazewinkelBoundaryRemainder r) := by
    funext t
    exact deningerHazewinkelBoundarySpecialization_specialMinor r t
  rw [deningerHazewinkelBoundarySpecialMinorHom, hfamily]
  exact GaloisForLFunctions.HTGeometry.triangularMvPolynomial_eval₂Hom_injective
    (deningerHazewinkelBoundaryDiagonal r)
    (deningerHazewinkelBoundaryDiagonal_ne_zero r)
    (deningerHazewinkelBoundaryRemainder r)
    (deningerHazewinkelBoundaryRemainder_vars_lt r)

end
end RHTower

