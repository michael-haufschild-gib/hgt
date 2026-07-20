import GaloisForLFunctions.HTGeometry.DigammaRationalCarrier
import GaloisForLFunctions.HTGeometry.GammaPoleFormalGermFreeness
import GaloisForLFunctions.HTGeometry.MvPolynomialHomogeneousDehomogenization
import GaloisForLFunctions.HTGeometry.MvPolynomialTopHomogeneousComponent

/-!
# The simple-zero Bell horizon

At a simple zero of a holomorphic section `G`, its logarithmic derivative `g = G'/G` has residue
one.  The complete Bell covariant jets

`B_k(g, g', ..., g^(k-1)) = G^(k) / G`

all have at most a simple pole.  Their principal residues are `1, R₁, ..., Rₙ`, where the `Rᵢ`
record the remaining zero-boundary jets.  This module proves the exact universal algebraic
classification of that boundary.

The principal-profile map sends the covariant variables to

`Z₀ ↦ T`,  `Z_(i+1) ↦ T * Rᵢ`.

For every nonzero polynomial, its exact `T`-degree after this substitution is its multivariate
total degree.  The point requiring proof is that setting the first residue coordinate to `1` is
still injective on each homogeneous sector: the sector degree reconstructs the omitted exponent.
It follows that the at-most-simple-pole horizon is exactly the affine covariant sector.

The module also closes a previously implicit algebraic point: finite complete-Bell substitution is
surjective as well as injective, hence is a polynomial ring automorphism.  Thus the covariant
classification can be pulled back without assuming an inverse.

This is an algebraic boundary theorem.  An application to an analytic carrier separately requires
an unconditional theorem identifying and proving freeness of its actual zero-boundary residues.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The simple-zero principal residues: the logarithmic derivative has fixed residue one, while
the higher covariant jets have free boundary coordinates. -/
def simpleZeroBoundaryResidue (n : ℕ) : Fin (n + 1) → MvPolynomial (Fin n) ℂ :=
  Fin.cases 1 fun j => MvPolynomial.X j

/-- Projective-chart dehomogenization obtained by fixing the first residue coordinate to one. -/
def simpleZeroDehomogenize (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (simpleZeroBoundaryResidue n)

/-- The principal pole profile of the finite Bell-covariant jet algebra.  Polynomial degree in
`T` records pole order. -/
def simpleZeroPrincipalProfile (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial (MvPolynomial (Fin n) ℂ) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp MvPolynomial.C)
    (fun j => Polynomial.X * Polynomial.C (simpleZeroBoundaryResidue n j))

/-- A homogeneous `d`-particle covariant observable has the common pole factor `T^d`; its
coefficient is its projective-chart dehomogenization. -/
theorem simpleZeroPrincipalProfile_factor
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    simpleZeroPrincipalProfile n P =
      Polynomial.X ^ d * Polynomial.C (simpleZeroDehomogenize n P) := by
  change MvPolynomial.eval₂ _
      (fun j => Polynomial.X * Polynomial.C (simpleZeroBoundaryResidue n j)) P = _
  rw [GaloisForLFunctions.isHomogeneous_eval₂_scale hP]
  congr 1
  simpa [simpleZeroDehomogenize] using
    (MvPolynomial.map_eval₂Hom MvPolynomial.C (simpleZeroBoundaryResidue n)
      Polynomial.C P).symm

/-- **Homogeneous projective-chart faithfulness.**  Fixing the first residue coordinate to one
does not kill a nonzero homogeneous polynomial.  The known homogeneous degree reconstructs the
exponent of that coordinate. -/
theorem simpleZeroDehomogenize_ne_zero_of_isHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    simpleZeroDehomogenize n P ≠ 0 := by
  let E := MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv n)
  let Q := E P
  have hQ : Q.IsHomogeneous d := by
    simpa [Q, E] using hP.rename_isHomogeneous
  have hQ0 : Q ≠ 0 := E.injective.ne hP0
  have hdehom : GaloisForLFunctions.optionHeadDehomogenize Q ≠ 0 :=
    GaloisForLFunctions.optionHeadDehomogenize_ne_zero_of_isHomogeneous hQ hQ0
  have heq : simpleZeroDehomogenize n =
      GaloisForLFunctions.optionHeadDehomogenize.comp E.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [simpleZeroDehomogenize, GaloisForLFunctions.optionHeadDehomogenize, E]
    · intro i
      induction i using Fin.cases with
      | zero =>
          simp [simpleZeroDehomogenize, simpleZeroBoundaryResidue,
            GaloisForLFunctions.optionHeadDehomogenize, E, _root_.finSuccEquiv]
      | succ i =>
          simp [simpleZeroDehomogenize, simpleZeroBoundaryResidue,
            GaloisForLFunctions.optionHeadDehomogenize, E, _root_.finSuccEquiv_succ]
  rwa [heq, RingHom.comp_apply]

/-- The grade-`d` boundary trace of a homogeneous sector is its faithful dehomogenization. -/
theorem simpleZeroPrincipalProfile_coeff_of_isHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    (simpleZeroPrincipalProfile n P).coeff d = simpleZeroDehomogenize n P := by
  rw [simpleZeroPrincipalProfile_factor hP]
  simp

/-- For an arbitrary polynomial, the coefficient at its total-degree pole grade is the
dehomogenized top homogeneous component. -/
theorem simpleZeroPrincipalProfile_coeff_totalDegree
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (simpleZeroPrincipalProfile n P).coeff P.totalDegree =
      simpleZeroDehomogenize n (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  let D := P.totalDegree
  have hsum :
      (∑ e ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent e P) = P := by
    simpa [D] using MvPolynomial.sum_homogeneousComponent P
  change (simpleZeroPrincipalProfile n P).coeff D =
    simpleZeroDehomogenize n (MvPolynomial.homogeneousComponent D P)
  calc
    (simpleZeroPrincipalProfile n P).coeff D =
        (simpleZeroPrincipalProfile n
          (∑ e ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent e P)).coeff D := by
      rw [hsum]
    _ = ∑ e ∈ Finset.range (D + 1),
        (simpleZeroPrincipalProfile n (MvPolynomial.homogeneousComponent e P)).coeff D := by
      simp
    _ = simpleZeroDehomogenize n (MvPolynomial.homogeneousComponent D P) := by
      rw [Finset.sum_eq_single D]
      · exact simpleZeroPrincipalProfile_coeff_of_isHomogeneous
          (MvPolynomial.homogeneousComponent_isHomogeneous D P)
      · intro e he hene
        have hed : e ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp he)
        have helt : e < D := lt_of_le_of_ne hed hene
        rw [simpleZeroPrincipalProfile_factor
          (MvPolynomial.homogeneousComponent_isHomogeneous e P)]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt <| by
          refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
          simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
          omega
      · intro hnot
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self D)) hnot

/-- No pole grade above multivariate total degree can occur in the principal profile. -/
theorem simpleZeroPrincipalProfile_natDegree_le_totalDegree
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (simpleZeroPrincipalProfile n P).natDegree ≤ P.totalDegree := by
  classical
  let D := P.totalDegree
  have hsum :
      (∑ e ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent e P) = P := by
    simpa [D] using MvPolynomial.sum_homogeneousComponent P
  change (simpleZeroPrincipalProfile n P).natDegree ≤ D
  rw [← hsum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range (D + 1)) _ ?_
  intro e he
  rw [simpleZeroPrincipalProfile_factor
    (MvPolynomial.homogeneousComponent_isHomogeneous e P)]
  refine Polynomial.natDegree_mul_le.trans ?_
  simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
  exact Nat.add_zero e ▸ Nat.le_of_lt_succ (Finset.mem_range.mp he)

/-- **Exact simple-zero boundary degree law.**  A nonzero covariant observable has pole-profile
degree exactly equal to its particle number / multivariate total degree. -/
theorem simpleZeroPrincipalProfile_natDegree_eq_totalDegree
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP0 : P ≠ 0) :
    (simpleZeroPrincipalProfile n P).natDegree = P.totalDegree := by
  apply le_antisymm (simpleZeroPrincipalProfile_natDegree_le_totalDegree P)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [simpleZeroPrincipalProfile_coeff_totalDegree]
  exact simpleZeroDehomogenize_ne_zero_of_isHomogeneous
    (MvPolynomial.homogeneousComponent_isHomogeneous P.totalDegree P)
    (homogeneousComponent_totalDegree_ne_zero hP0)

/-- **Affine covariant-horizon classification.**  A principal Bell-covariant observable has at
most a simple pole exactly when it has total degree at most one. -/
theorem simpleZeroPrincipalProfile_natDegree_le_one_iff
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (simpleZeroPrincipalProfile n P).natDegree ≤ 1 ↔ P.totalDegree ≤ 1 := by
  by_cases hP0 : P = 0
  · simp [hP0]
  · rw [simpleZeroPrincipalProfile_natDegree_eq_totalDegree hP0]

/-- Each complete-Bell coordinate is its matching raw jet plus a polynomial in strictly lower raw
jets. -/
theorem bellCoefficientMap_X_decomp (n : ℕ) (j : Fin (n + 1)) :
    ∃ T : MvPolynomial (Fin (j : ℕ)) ℂ,
      bellCoefficientMap n (MvPolynomial.X j) = MvPolynomial.X j +
        MvPolynomial.rename
          (fun i : Fin (j : ℕ) => (⟨i, i.isLt.trans j.isLt⟩ : Fin (n + 1))) T := by
  obtain ⟨T, hT⟩ := bellCore_succ_decomp (j : ℕ)
  refine ⟨T, ?_⟩
  rw [show bellCoefficientMap n (MvPolynomial.X j) =
      bellAt n ((j : ℕ) + 1) j.isLt by simp [bellCoefficientMap]]
  rw [bellAt, hT, map_add, MvPolynomial.rename_X, MvPolynomial.rename_rename]
  congr 2

/-- **Polynomial invertibility of complete-Bell substitution.**  Triangular back-substitution
produces a polynomial preimage of every polynomial; no rational inverse or value-level argument is
being assumed. -/
theorem bellCoefficientMap_surjective (n : ℕ) :
    Function.Surjective (bellCoefficientMap n) := by
  have hvar : ∀ k : ℕ, ∀ hk : k < n + 1,
      ∃ Q : MvPolynomial (Fin (n + 1)) ℂ,
        bellCoefficientMap n Q = MvPolynomial.X (⟨k, hk⟩ : Fin (n + 1)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let j : Fin (n + 1) := ⟨k, hk⟩
        obtain ⟨T, hT⟩ := bellCoefficientMap_X_decomp n j
        have hlower : ∃ Q : MvPolynomial (Fin (n + 1)) ℂ,
            bellCoefficientMap n Q =
              MvPolynomial.rename
                (fun i : Fin k => (⟨i, i.isLt.trans hk⟩ : Fin (n + 1))) T := by
          clear hT
          induction T using MvPolynomial.induction_on with
          | C a =>
              refine ⟨MvPolynomial.C a, ?_⟩
              simp [bellCoefficientMap]
          | add p q hp hq =>
              obtain ⟨P, hP⟩ := hp
              obtain ⟨Q, hQ⟩ := hq
              refine ⟨P + Q, ?_⟩
              simp only [map_add, hP, hQ]
          | mul_X p i hp =>
              obtain ⟨P, hP⟩ := hp
              obtain ⟨Qi, hQi⟩ := ih (i : ℕ) i.isLt (i.isLt.trans hk)
              refine ⟨P * Qi, ?_⟩
              rw [map_mul, hP, hQi, map_mul, MvPolynomial.rename_X]
        obtain ⟨Q, hQ⟩ := hlower
        refine ⟨MvPolynomial.X j - Q, ?_⟩
        rw [map_sub, hT, hQ]
        ring
  intro P
  induction P using MvPolynomial.induction_on with
  | C a =>
      refine ⟨MvPolynomial.C a, ?_⟩
      simp [bellCoefficientMap]
  | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hq
      refine ⟨P + Q, ?_⟩
      simp only [map_add, hP, hQ]
  | mul_X p j hp =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hvar (j : ℕ) j.isLt
      refine ⟨P * Q, ?_⟩
      rw [map_mul, hP, hQ]

/-- The complete-Bell coordinate change as an actual finite polynomial ring equivalence. -/
noncomputable def bellCoefficientEquiv (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ ≃+* MvPolynomial (Fin (n + 1)) ℂ :=
  RingEquiv.ofBijective (bellCoefficientMap n)
    ⟨bellCoefficientMap_injective n, bellCoefficientMap_surjective n⟩

theorem bellCoefficientEquiv_apply (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    bellCoefficientEquiv n P = bellCoefficientMap n P := rfl

/-- The raw logarithmic-derivative jet profile: first change polynomially to Bell-covariant
coordinates, then read the simple-zero pole profile. -/
def simpleZeroRawJetPrincipalProfile (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial (MvPolynomial (Fin n) ℂ) :=
  (simpleZeroPrincipalProfile n).comp (bellCoefficientEquiv n).symm.toRingHom

/-- Raw-jet horizon membership is exactly affine degree after the inverse complete-Bell coordinate
change. -/
theorem simpleZeroRawJetPrincipalProfile_natDegree_le_one_iff
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (simpleZeroRawJetPrincipalProfile n P).natDegree ≤ 1 ↔
      ((bellCoefficientEquiv n).symm P).totalDegree ≤ 1 := by
  exact simpleZeroPrincipalProfile_natDegree_le_one_iff _

/-- **Complete raw-jet classification.**  A raw logarithmic-derivative jet polynomial lies on the
at-most-simple-pole principal horizon exactly when it is the Bell substitution of an affine
covariant polynomial. -/
theorem simpleZeroRawJetPrincipalProfile_natDegree_le_one_iff_exists_bellAffine
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (simpleZeroRawJetPrincipalProfile n P).natDegree ≤ 1 ↔
      ∃ Q : MvPolynomial (Fin (n + 1)) ℂ,
        Q.totalDegree ≤ 1 ∧ bellCoefficientMap n Q = P := by
  rw [simpleZeroRawJetPrincipalProfile_natDegree_le_one_iff]
  constructor
  · intro h
    refine ⟨(bellCoefficientEquiv n).symm P, h, ?_⟩
    rw [← bellCoefficientEquiv_apply, RingEquiv.apply_symm_apply]
  · rintro ⟨Q, hQ, hQP⟩
    have hQP' : bellCoefficientEquiv n Q = P := by
      rwa [bellCoefficientEquiv_apply]
    rw [← hQP', RingEquiv.symm_apply_apply]
    exact hQ

end

end GaloisForLFunctions.HTGeometry
