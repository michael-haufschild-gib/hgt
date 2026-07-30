import GaloisForLFunctions.HTGeometry.GammaPoleMovingMaximalWeightReflection

/-!
# Moving-coefficient Gamma affine profile horizon

The symbolic moving-pole profile remembers outer pole grade, signed factorial
scale, and the full regular-unit derivative boundary.  This module proves the
sharp filtration law exposed by those three coordinates.  Outer pole cutoff
`r` forces source particle degree at most `r`; cutoff zero consists exactly of
polynomial coefficients; and cutoff one consists exactly of sources affine in
the undifferentiated Gamma carrier.

The decisive reflection is triangular.  In a linear source, choose the largest
active derivative index `j`.  At outer grade `j + 1` and scale grade `-j`, all
lower indices are excluded by inner-scale purity and all higher indices vanish
by maximality.  The remaining coefficient is exactly the center value of the
`j`th source coefficient times the nonzero factorial `-j!`.  Thus a forbidden
positive derivative coordinate cannot disappear under the moving coefficient
Taylor transform.

This is the complete algebraic profile horizon for polynomial coefficients.  A
global meromorphic application still has to connect the actual local Laurent
expansion of a differential expression to this symbolic boundary profile.
-/

open Polynomial LaurentPolynomial MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- A Laurent polynomial has no grades strictly above the natural cutoff
`r`. -/
def LaurentPoleGradeAtMost {R : Type*} [Semiring R]
    (r : ℕ) (F : LaurentPolynomial R) : Prop :=
  ∀ q : ℤ, (r : ℤ) < q → F.coeff q = 0

namespace LaurentPoleGradeAtMost

theorem zero {R : Type*} [Semiring R] (r : ℕ) :
    LaurentPoleGradeAtMost r (0 : LaurentPolynomial R) := by
  intro q hq
  rfl

theorem one {R : Type*} [Semiring R] :
    LaurentPoleGradeAtMost 0 (1 : LaurentPolynomial R) := by
  intro q hq
  rw [AddMonoidAlgebra.one_def]
  exact Finsupp.single_eq_of_ne (ne_of_gt hq)

theorem add {R : Type*} [Semiring R] {r : ℕ}
    {F G : LaurentPolynomial R}
    (hF : LaurentPoleGradeAtMost r F)
    (hG : LaurentPoleGradeAtMost r G) :
    LaurentPoleGradeAtMost r (F + G) := by
  intro q hq
  change F.coeff q + G.coeff q = 0
  rw [hF q hq, hG q hq, add_zero]

theorem mono {R : Type*} [Semiring R] {r s : ℕ}
    {F : LaurentPolynomial R} (hF : LaurentPoleGradeAtMost r F)
    (hrs : r ≤ s) :
    LaurentPoleGradeAtMost s F := by
  intro q hq
  have hrsInt : (r : ℤ) ≤ (s : ℤ) := by exact_mod_cast hrs
  exact hF q (lt_of_le_of_lt hrsInt hq)

/-- Outer Laurent cutoffs form a multiplicative filtration. -/
theorem mul {R : Type*} [Semiring R] {r s : ℕ}
    {F G : LaurentPolynomial R}
    (hF : LaurentPoleGradeAtMost r F)
    (hG : LaurentPoleGradeAtMost s G) :
    LaurentPoleGradeAtMost (r + s) (F * G) := by
  intro q hq
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  classical
  apply Finset.sum_eq_zero
  intro a ha
  change F.coeff a * G.coeff (-a + q) = 0
  by_cases har : (r : ℤ) < a
  · rw [hF a har, zero_mul]
  · have hsq : (s : ℤ) < -a + q := by
      have hq' : (r : ℤ) + (s : ℤ) < q := by simpa using hq
      omega
    rw [hG _ hsq, mul_zero]

theorem pow {R : Type*} [Semiring R] {r : ℕ}
    {F : LaurentPolynomial R} (hF : LaurentPoleGradeAtMost r F)
    (e : ℕ) :
    LaurentPoleGradeAtMost (e * r) (F ^ e) := by
  induction e with
  | zero => simpa using (one : LaurentPoleGradeAtMost 0 (1 : LaurentPolynomial R))
  | succ e ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hF

end LaurentPoleGradeAtMost

/-- The simple-pole specialization of `LaurentPoleGradeAtMost`. -/
abbrev LaurentPoleGradeAtMostOne {R : Type*} [Semiring R]
    (F : LaurentPolynomial R) : Prop :=
  LaurentPoleGradeAtMost 1 F

/-- The complete symbolic moving Gamma profile has outer pole cutoff `r`. -/
def GammaPoleSymbolicProfilePoleGradeAtMost
    (n r : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) : Prop :=
  LaurentPoleGradeAtMost r
    (gammaPoleSymbolicPolynomialJetLaurentEval n P)

/-- The actual Gamma germ Laurent profile has outer pole cutoff `r`. -/
def GammaPoleProfilePoleGradeAtMost
    (n r : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) : Prop :=
  LaurentPoleGradeAtMost r (gammaPolePolynomialJetLaurentEval n P)

/-- The complete symbolic moving Gamma profile has at most a simple outer
pole. -/
def GammaPoleSymbolicProfileAtMostSimple
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) : Prop :=
  GammaPoleSymbolicProfilePoleGradeAtMost n 1 P

/-- The existing actual Gamma germ Laurent profile has at most a simple outer
pole. -/
def GammaPoleProfileAtMostSimple
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) : Prop :=
  GammaPoleProfilePoleGradeAtMost n 1 P

/-- Coefficientwise form of the symbolic-to-actual Gamma profile value
relation. -/
theorem gammaPolePolynomialJetLaurentEval_coeff_eq_symbolic_eval
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) (q : ℤ) :
    (gammaPolePolynomialJetLaurentEval n P).coeff q =
      gammaPoleScaleAndUnitDerivativeLaurentEval
        ((gammaPoleSymbolicPolynomialJetLaurentEval n P).coeff q) := by
  have h := congrArg (fun F : NatGerm[T;T⁻¹] => F.coeff q)
    (gammaPoleSymbolicToActual_polynomialJetLaurentEval n P)
  simpa [gammaPoleSymbolicToActual,
    AddMonoidAlgebra.coeff_mapRingHom] using! h.symm

/-- Every actual outer pole-cutoff proposition reflects exactly to the
faithful symbolic proposition. -/
theorem gammaPoleProfilePoleGradeAtMost_iff_symbolic
    {n r : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)} :
    GammaPoleProfilePoleGradeAtMost n r P ↔
      GammaPoleSymbolicProfilePoleGradeAtMost n r P := by
  constructor
  · intro h q hq
    apply gammaPoleScaleAndUnitDerivativeLaurentEval_injective
    rw [map_zero, ← gammaPolePolynomialJetLaurentEval_coeff_eq_symbolic_eval]
    exact h q hq
  · intro h q hq
    rw [gammaPolePolynomialJetLaurentEval_coeff_eq_symbolic_eval, h q hq,
      map_zero]

/-- The actual at-most-simple proposition reflects exactly to the faithful
symbolic proposition. -/
theorem gammaPoleProfileAtMostSimple_iff_symbolic
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)} :
    GammaPoleProfileAtMostSimple n P ↔
      GammaPoleSymbolicProfileAtMostSimple n P := by
  exact gammaPoleProfilePoleGradeAtMost_iff_symbolic

/-- **Moving Gamma particle-filtration lower bound.**  If the symbolic profile
has outer pole cutoff `r`, then the source has particle degree at most `r`. -/
theorem gammaPoleSymbolicProfilePoleGradeAtMost_totalDegree_le
    {n r : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hP : GammaPoleSymbolicProfilePoleGradeAtMost n r P) :
    P.totalDegree ≤ r := by
  by_cases hzero : P = 0
  · simp [hzero]
  by_contra hdegree
  have hlt : r < P.totalDegree := Nat.lt_of_not_ge hdegree
  have hdiag :=
    gammaPoleSymbolicPolynomialJetLaurentEval_leadingParticleMaximalWeight_coeff_ne_zero
      n hzero
  apply hdiag
  rw [hP (P.totalDegree : ℤ) (by exact_mod_cast hlt)]
  rfl

/-- The actual faithful Gamma profile obeys the same arbitrary particle-
filtration lower bound. -/
theorem gammaPoleProfilePoleGradeAtMost_totalDegree_le
    {n r : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hP : GammaPoleProfilePoleGradeAtMost n r P) :
    P.totalDegree ≤ r := by
  exact gammaPoleSymbolicProfilePoleGradeAtMost_totalDegree_le
    (gammaPoleProfilePoleGradeAtMost_iff_symbolic.mp hP)

/-- An at-most-simple symbolic moving profile has source particle degree at
most one. -/
theorem gammaPoleSymbolicProfileAtMostSimple_totalDegree_le_one
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hP : GammaPoleSymbolicProfileAtMostSimple n P) :
    P.totalDegree ≤ 1 := by
  exact gammaPoleSymbolicProfilePoleGradeAtMost_totalDegree_le hP

/-- A moving polynomial coefficient has no positive outer pole grades. -/
theorem gammaPoleSymbolicMovingCoefficientLaurent_coeff_pos
    (p : Polynomial ℂ) (q : ℤ) (hq : 0 < q) :
    (gammaPoleSymbolicMovingCoefficientLaurent p).coeff q = 0 := by
  rw [gammaPoleSymbolicMovingCoefficientLaurent, RingHom.comp_apply]
  change (movingPoleTaylorLaurent
    (gammaPoleRationalScaleDerivativeInclude gammaPoleCenterRational)
    gammaPoleSymbolicPhysicalScale
    (p.map gammaPoleComplexScaleDerivativeInclude)).coeff q = 0
  exact movingPoleTaylorLaurent_coeff_pos _ _ _ q hq

/-- **Moving Gamma vacuum horizon.**  A symbolic profile with no positive
outer pole grades is exactly a polynomial coefficient, with no Gamma-jet
variables. -/
theorem gammaPoleSymbolicProfilePoleGradeAtMost_zero_iff_constant
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    GammaPoleSymbolicProfilePoleGradeAtMost n 0 P ↔
      ∃ a : Polynomial ℂ, P = MvPolynomial.C a := by
  constructor
  · intro hP
    have hdegree :=
      gammaPoleSymbolicProfilePoleGradeAtMost_totalDegree_le hP
    have hzero : P.totalDegree = 0 := Nat.eq_zero_of_le_zero hdegree
    exact ⟨P.coeff 0, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero⟩
  · rintro ⟨a, rfl⟩
    intro q hq
    simpa [gammaPoleSymbolicPolynomialJetLaurentEval] using
      gammaPoleSymbolicMovingCoefficientLaurent_coeff_pos a q hq

/-- The actual faithful Gamma profile has the same exact vacuum horizon. -/
theorem gammaPoleProfilePoleGradeAtMost_zero_iff_constant
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    GammaPoleProfilePoleGradeAtMost n 0 P ↔
      ∃ a : Polynomial ℂ, P = MvPolynomial.C a := by
  rw [gammaPoleProfilePoleGradeAtMost_iff_symbolic,
    gammaPoleSymbolicProfilePoleGradeAtMost_zero_iff_constant]

/-- A moving polynomial coefficient has no negative signed-scale grades. -/
theorem gammaPoleSymbolicMovingCoefficientLaurent_inner_coeff_neg
    (p : Polynomial ℂ) (q l : ℤ) (hl : l < 0) :
    ((gammaPoleSymbolicMovingCoefficientLaurent p).coeff q).coeff l = 0 := by
  ext m
  by_contra hcoeff
  have hfilter :=
    (gammaPoleSymbolicMovingCoefficientLaurent_boundaryFiltered p).coeff_weight
      hcoeff
  have htri :=
    (gammaPoleSymbolicMovingCoefficientLaurent_trihomogeneous p).support_weight
      hcoeff
  have hweightNat : gammaPoleBoundaryDerivativeWeightNat m = 0 := by omega
  have hweightInt : gammaPoleBoundaryDerivativeWeight m = 0 := by
    rw [gammaPoleBoundaryDerivativeWeight_eq_natCast, hweightNat]
    rfl
  rw [hweightInt] at htri
  have hq : 0 < q := by omega
  rw [gammaPoleSymbolicMovingCoefficientLaurent_coeff_pos p q hq] at hcoeff
  exact hcoeff rfl

/-- Multiplying a profile with no negative inner grades by an inner-pure
profile cannot create a grade below the pure factor's grade. -/
theorem gammaPoleInnerLower_mul_eq_zero
    {A B : GammaPoleMovingJetSymbolic} {r l : ℤ}
    (hA : ∀ q s : ℤ, s < 0 → (A.coeff q).coeff s = 0)
    (hB : GammaPoleInnerPure r B) (hlr : l < r) (q : ℤ) :
    ((A * B).coeff q).coeff l = 0 := by
  ext m
  by_contra hcoeff
  have hsupp : ((q, l), m) ∈
      (gammaPoleTriFlatten (A * B)).coeff.support := by
    rw [Finsupp.mem_support_iff]
    change MvPolynomial.coeff m (((A * B).coeff q).coeff l) ≠ 0
    exact hcoeff
  rw [map_mul] at hsupp
  have hsupp' := AddMonoidAlgebra.support_coeff_mul_subset
    (gammaPoleTriFlatten A) (gammaPoleTriFlatten B) hsupp
  rcases Finset.mem_add.mp hsupp' with ⟨x, hx, y, hy, hxy⟩
  have hinner := congrArg (fun a : GammaPoleTriIndex => a.1.2) hxy
  change x.1.2 + y.1.2 = l at hinner
  have hxinner : x.1.2 < 0 := by
    rw [hB y hy] at hinner
    omega
  have hxne : (gammaPoleTriFlatten A).coeff x ≠ 0 :=
    Finsupp.mem_support_iff.mp hx
  apply hxne
  rcases x with ⟨⟨xq, xl⟩, xm⟩
  change xl < 0 at hxinner
  simp [gammaPoleTriFlatten_apply, hA xq xl hxinner]

/-- The `j`th normalized Gamma derivative profile has outer pole grade at
most `j + 1`. -/
theorem gammaPoleSymbolicDerivativeLaurentProfile_coeff_eq_zero_of_gt
    (j : ℕ) (q : ℤ) (hq : ((j + 1 : ℕ) : ℤ) < q) :
    (gammaPoleSymbolicDerivativeLaurentProfile j).coeff q = 0 := by
  by_contra hcoeffOuter
  obtain ⟨l, hl⟩ := Finsupp.support_nonempty_iff.mpr
    (show ((gammaPoleSymbolicDerivativeLaurentProfile j).coeff q).coeff ≠ 0 by
      simpa using hcoeffOuter)
  have hlne : ((gammaPoleSymbolicDerivativeLaurentProfile j).coeff q).coeff l ≠ 0 :=
    Finsupp.mem_support_iff.mp hl
  obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hlne
  have htri :=
    (gammaPoleSymbolicDerivativeLaurentProfile_trihomogeneous j).support_weight hm
  have hfilter :=
    (gammaPoleSymbolicDerivativeLaurentProfile_boundaryFiltered j).coeff_weight hm
  have hsupp : ((q, l), m) ∈
      (gammaPoleTriFlatten
        (gammaPoleSymbolicDerivativeLaurentProfile j)).coeff.support := by
    rw [Finsupp.mem_support_iff]
    simpa using hm
  have hpure : l = -(j : ℤ) := by
    simpa using
      gammaPoleSymbolicDerivativeLaurentProfile_innerPure j ((q, l), m) hsupp
  rw [hpure] at htri
  rw [gammaPoleBoundaryDerivativeWeight_eq_natCast] at htri
  have hweightIntLe :
      (gammaPoleBoundaryDerivativeWeightNat m : ℤ) ≤ (j : ℤ) := by
    exact_mod_cast hfilter
  omega

/-- At the top outer grade of the `j`th derivative, only the zero Taylor
slice of a moving coefficient can contribute. -/
theorem gammaPoleSymbolicMovingCoefficient_mul_derivativeProfile_coeff_top
    (p : Polynomial ℂ) (j : ℕ) :
    (gammaPoleSymbolicMovingCoefficientLaurent p *
        gammaPoleSymbolicDerivativeLaurentProfile j).coeff ((j + 1 : ℕ) : ℤ) =
      (gammaPoleSymbolicMovingCoefficientLaurent p).coeff 0 *
        (gammaPoleSymbolicDerivativeLaurentProfile j).coeff ((j + 1 : ℕ) : ℤ) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  classical
  rw [Finsupp.sum_eq_single 0]
  · simp
  · intro q hq hq0
    have hqnonpos : q ≤ 0 := by
      by_contra hqle
      have hqpos : 0 < q := by omega
      have hzero := gammaPoleSymbolicMovingCoefficientLaurent_coeff_pos p q hqpos
      exact hq hzero
    have hgt : (j + 1 : ℕ) < -q + ((j + 1 : ℕ) : ℤ) := by omega
    rw [gammaPoleSymbolicDerivativeLaurentProfile_coeff_eq_zero_of_gt j _ hgt,
      mul_zero]
  · intro hnot
    simp

/-- The joint top outer/scale/boundary coefficient is the center value of the
moving polynomial coefficient times `-j!`. -/
theorem gammaPoleSymbolicMovingCoefficient_mul_derivativeProfile_top_scale_boundary
    (p : Polynomial ℂ) (j : ℕ) :
    MvPolynomial.coeff 0
        (((gammaPoleSymbolicMovingCoefficientLaurent p *
            gammaPoleSymbolicDerivativeLaurentProfile j).coeff
          ((j + 1 : ℕ) : ℤ)).coeff (-(j : ℤ))) =
      gammaPoleCenterRationalEval p * RatFunc.C (-(j.factorial : ℂ)) := by
  rw [gammaPoleSymbolicMovingCoefficient_mul_derivativeProfile_coeff_top,
    gammaPoleSymbolicMovingCoefficientLaurent_coeff_zero]
  change MvPolynomial.coeff 0
    (((LaurentPolynomial.C (MvPolynomial.C
        (gammaPoleCenterRationalEval p)) *
      (gammaPoleSymbolicDerivativeLaurentProfile j).coeff ((j + 1 : ℕ) : ℤ)) :
        GammaPoleScaleDerivativeSymbolic).coeff (-(j : ℤ))) = _
  rw [← LaurentPolynomial.smul_eq_C_mul]
  change MvPolynomial.coeff 0
    (MvPolynomial.C (gammaPoleCenterRationalEval p) *
      ((gammaPoleSymbolicDerivativeLaurentProfile j).coeff
        ((j + 1 : ℕ) : ℤ)).coeff (-(j : ℤ))) = _
  rw [MvPolynomial.coeff_C_mul,
    gammaPoleSymbolicDerivativeLaurentProfile_top_scale_boundary]

/-- A moving coefficient times the `j`th derivative profile still has outer
pole grade at most `j + 1`. -/
theorem gammaPoleSymbolicMovingCoefficient_mul_derivativeProfile_coeff_eq_zero_of_gt
    (p : Polynomial ℂ) (j : ℕ) (q : ℤ)
    (hq : ((j + 1 : ℕ) : ℤ) < q) :
    (gammaPoleSymbolicMovingCoefficientLaurent p *
        gammaPoleSymbolicDerivativeLaurentProfile j).coeff q = 0 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  classical
  apply Finset.sum_eq_zero
  intro r hr
  have hrnonpos : r ≤ 0 := by
    by_contra hrle
    have hrpos : 0 < r := by omega
    exact (Finsupp.mem_support_iff.mp hr)
      (gammaPoleSymbolicMovingCoefficientLaurent_coeff_pos p r hrpos)
  have hderiv : ((j + 1 : ℕ) : ℤ) < -r + q := by omega
  change (gammaPoleSymbolicMovingCoefficientLaurent p).coeff r *
    (gammaPoleSymbolicDerivativeLaurentProfile j).coeff (-r + q) = 0
  rw [gammaPoleSymbolicDerivativeLaurentProfile_coeff_eq_zero_of_gt
      j _ hderiv,
    mul_zero]

private theorem isHomogeneous_zero_eq_C_coeff_zero_polynomial
    {σ : Type*} {P : MvPolynomial σ (Polynomial ℂ)}
    (hP : P.IsHomogeneous 0) :
    P = MvPolynomial.C (P.coeff 0) := by
  have h := MvPolynomial.homogeneousComponent_of_mem (m := 0) hP
  rw [if_pos rfl, MvPolynomial.homogeneousComponent_zero] at h
  exact h.symm

/-- For a linear source whose active jet indices do not exceed `j`, the joint
outer grade `j + 1`, scale grade `-j`, boundary-constant coefficient reads the
`j`th source coefficient exactly. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_linear_maximal_diagonal
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hP : P.IsHomogeneous 1) (j : Fin (n + 1))
    (hmax : ∀ i : Fin (n + 1), (j : ℕ) < (i : ℕ) →
      (MvPolynomial.pderiv i P).coeff 0 = 0) :
    MvPolynomial.coeff 0
        (((gammaPoleSymbolicPolynomialJetLaurentEval n P).coeff
          (((j : ℕ) + 1 : ℕ) : ℤ)).coeff (-((j : ℕ) : ℤ))) =
      gammaPoleCenterRationalEval ((MvPolynomial.pderiv j P).coeff 0) *
        RatFunc.C (-((j : ℕ).factorial : ℂ)) := by
  have hpderivC (i : Fin (n + 1)) :
      MvPolynomial.pderiv i P =
        MvPolynomial.C ((MvPolynomial.pderiv i P).coeff 0) :=
    isHomogeneous_zero_eq_C_coeff_zero_polynomial hP.pderiv
  have hEuler := hP.sum_X_mul_pderiv
  simp only [one_nsmul] at hEuler
  change gammaPoleSymbolicPolynomialJetTriCoefficient n
    (((j : ℕ) + 1 : ℕ) : ℤ) (-((j : ℕ) : ℤ)) 0 P = _
  classical
  have hsum :
      (∑ i, gammaPoleSymbolicPolynomialJetTriCoefficient n
        (((j : ℕ) + 1 : ℕ) : ℤ) (-((j : ℕ) : ℤ)) 0
          (MvPolynomial.X i * MvPolynomial.pderiv i P)) =
        gammaPoleCenterRationalEval ((MvPolynomial.pderiv j P).coeff 0) *
          RatFunc.C (-((j : ℕ).factorial : ℂ)) := by
    rw [Finset.sum_eq_single j]
    · rw [hpderivC]
      change MvPolynomial.coeff 0
        (((gammaPoleSymbolicPolynomialJetLaurentEval n
          (MvPolynomial.X j * MvPolynomial.C
            ((MvPolynomial.pderiv j P).coeff 0))).coeff
          (((j : ℕ) + 1 : ℕ) : ℤ)).coeff (-((j : ℕ) : ℤ))) = _
      rw [map_mul]
      simp only [gammaPoleSymbolicPolynomialJetLaurentEval,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
      change MvPolynomial.coeff 0
        (((gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) *
          gammaPoleSymbolicMovingCoefficientLaurent
          ((MvPolynomial.pderiv j P).coeff 0)).coeff
          (((j : ℕ) + 1 : ℕ) : ℤ)).coeff (-((j : ℕ) : ℤ))) = _
      rw [mul_comm (gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ))
        (gammaPoleSymbolicMovingCoefficientLaurent
          ((MvPolynomial.pderiv j P).coeff 0))]
      simpa using
        gammaPoleSymbolicMovingCoefficient_mul_derivativeProfile_top_scale_boundary
          ((MvPolynomial.pderiv j P).coeff 0) (j : ℕ)
    · intro i hi hij
      rw [hpderivC i]
      change MvPolynomial.coeff 0
        (((gammaPoleSymbolicPolynomialJetLaurentEval n
          (MvPolynomial.X i * MvPolynomial.C
            ((MvPolynomial.pderiv i P).coeff 0))).coeff
          (((j : ℕ) + 1 : ℕ) : ℤ)).coeff (-((j : ℕ) : ℤ))) = 0
      rw [map_mul]
      simp only [gammaPoleSymbolicPolynomialJetLaurentEval,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
      by_cases hijlt : (i : ℕ) < (j : ℕ)
      · have hlower : -((j : ℕ) : ℤ) < -((i : ℕ) : ℤ) := by omega
        have hzero := gammaPoleInnerLower_mul_eq_zero
          (fun q l hl =>
            gammaPoleSymbolicMovingCoefficientLaurent_inner_coeff_neg
              ((MvPolynomial.pderiv i P).coeff 0) q l hl)
          (gammaPoleSymbolicDerivativeLaurentProfile_innerPure (i : ℕ))
          hlower (((j : ℕ) + 1 : ℕ) : ℤ)
        change MvPolynomial.coeff 0
          (((gammaPoleSymbolicDerivativeLaurentProfile (i : ℕ) *
            gammaPoleSymbolicMovingCoefficientLaurent
              ((MvPolynomial.pderiv i P).coeff 0)).coeff
            (((j : ℕ) + 1 : ℕ) : ℤ)).coeff (-((j : ℕ) : ℤ))) = 0
        rw [mul_comm (gammaPoleSymbolicDerivativeLaurentProfile (i : ℕ))
          (gammaPoleSymbolicMovingCoefficientLaurent
            ((MvPolynomial.pderiv i P).coeff 0)), hzero]
        rfl
      · have hjilt : (j : ℕ) < (i : ℕ) := by
          have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
          omega
        rw [hmax i hjilt]
        simp
    · intro hnot
      exact (hnot (Finset.mem_univ j)).elim
  calc
    gammaPoleSymbolicPolynomialJetTriCoefficient n
        (((j : ℕ) + 1 : ℕ) : ℤ) (-((j : ℕ) : ℤ)) 0 P =
      gammaPoleSymbolicPolynomialJetTriCoefficient n
        (((j : ℕ) + 1 : ℕ) : ℤ) (-((j : ℕ) : ℤ)) 0
          (∑ i, MvPolynomial.X i * MvPolynomial.pderiv i P) := by
        rw [hEuler]
    _ = ∑ i, gammaPoleSymbolicPolynomialJetTriCoefficient n
        (((j : ℕ) + 1 : ℕ) : ℤ) (-((j : ℕ) : ℤ)) 0
          (MvPolynomial.X i * MvPolynomial.pderiv i P) := by rw [map_sum]
    _ = _ := hsum

private theorem sum_homogeneousComponent_of_totalDegree_le_polynomial
    {σ : Type*} {P : MvPolynomial σ (Polynomial ℂ)} {N : ℕ}
    (h : P.totalDegree ≤ N) :
    ∑ e ∈ Finset.range (N + 1),
      MvPolynomial.homogeneousComponent e P = P := by
  have hsub : Finset.range (P.totalDegree + 1) ⊆
      Finset.range (N + 1) := by
    intro e he
    rw [Finset.mem_range] at he ⊢
    omega
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent P]
  refine (Finset.sum_subset hsub ?_).symm
  intro e he hne
  refine MvPolynomial.homogeneousComponent_eq_zero e P ?_
  rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hne
  exact hne

/-- **Moving-coefficient Gamma affine horizon.**  The complete symbolic
moving-pole profile has no pole grades above one exactly when the source is
affine in the undifferentiated carrier, with arbitrary polynomial coefficient
functions. -/
theorem gammaPoleSymbolicProfileAtMostSimple_iff_affine
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    GammaPoleSymbolicProfileAtMostSimple n P ↔
      ∃ a b : Polynomial ℂ,
        P = MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 := by
  constructor
  · intro hprofile
    have hdegree :=
      gammaPoleSymbolicProfileAtMostSimple_totalDegree_le_one hprofile
    let P₀ := MvPolynomial.homogeneousComponent 0 P
    let P₁ := MvPolynomial.homogeneousComponent 1 P
    have hdecomp : P₀ + P₁ = P := by
      have hsum := sum_homogeneousComponent_of_totalDegree_le_polynomial
        (P := P) (N := 1) hdegree
      change MvPolynomial.homogeneousComponent 0 P +
        MvPolynomial.homogeneousComponent 1 P = P
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.reduceAdd] using hsum
    have hP₀ : P₀.IsHomogeneous 0 :=
      MvPolynomial.homogeneousComponent_isHomogeneous 0 P
    have hP₁ : P₁.IsHomogeneous 1 :=
      MvPolynomial.homogeneousComponent_isHomogeneous 1 P
    have hpositive (j : Fin (n + 1)) (hj : j ≠ 0) :
        (MvPolynomial.pderiv j P₁).coeff 0 = 0 := by
      by_contra hjcoeff
      let S : Finset (Fin (n + 1)) := Finset.univ.filter fun i =>
        i ≠ 0 ∧ (MvPolynomial.pderiv i P₁).coeff 0 ≠ 0
      have hjS : j ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj, hjcoeff⟩
      let J : Fin (n + 1) := S.max' ⟨j, hjS⟩
      have hJS : J ∈ S := Finset.max'_mem S ⟨j, hjS⟩
      have hJdata := (Finset.mem_filter.mp hJS).2
      have hJne : J ≠ 0 := hJdata.1
      have hJcoeff : (MvPolynomial.pderiv J P₁).coeff 0 ≠ 0 := hJdata.2
      have hJmax (i : Fin (n + 1)) (hJi : (J : ℕ) < (i : ℕ)) :
          (MvPolynomial.pderiv i P₁).coeff 0 = 0 := by
        by_contra hicoeff
        have hi0 : i ≠ 0 := by
          intro hi
          subst i
          simp at hJi
        have hiS : i ∈ S := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi0, hicoeff⟩
        have hiJ : i ≤ J := Finset.le_max' S i hiS
        exact (not_lt_of_ge hiJ) (by exact_mod_cast hJi)
      have hdiag :=
        gammaPoleSymbolicPolynomialJetLaurentEval_linear_maximal_diagonal
          hP₁ J hJmax
      have hfactor : RatFunc.C (-((J : ℕ).factorial : ℂ)) ≠ 0 := by
        have hfactorComplex : ((J : ℕ).factorial : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (J : ℕ))
        simpa using RatFunc.C_injective.ne
          (neg_ne_zero.mpr hfactorComplex)
      have hdiagNe :
          MvPolynomial.coeff 0
              (((gammaPoleSymbolicPolynomialJetLaurentEval n P₁).coeff
                (((J : ℕ) + 1 : ℕ) : ℤ)).coeff (-((J : ℕ) : ℤ))) ≠ 0 := by
        rw [hdiag]
        have hcenter := gammaPoleCenterRationalEval_injective.ne hJcoeff
        exact mul_ne_zero (by simpa using hcenter) hfactor
      have hJpos : 0 < (J : ℕ) := by
        exact Nat.pos_of_ne_zero (fun h => hJne (Fin.ext h))
      have hqpos : (0 : ℤ) < (((J : ℕ) + 1 : ℕ) : ℤ) := by omega
      have hqgt : (1 : ℤ) < (((J : ℕ) + 1 : ℕ) : ℤ) := by omega
      have hPzero :
          (gammaPoleSymbolicPolynomialJetLaurentEval n P).coeff
              (((J : ℕ) + 1 : ℕ) : ℤ) = 0 :=
        hprofile _ hqgt
      have hP₀zero :
          (gammaPoleSymbolicPolynomialJetLaurentEval n P₀).coeff
              (((J : ℕ) + 1 : ℕ) : ℤ) = 0 := by
        rw [isHomogeneous_zero_eq_C_coeff_zero_polynomial hP₀]
        simpa [gammaPoleSymbolicPolynomialJetLaurentEval] using
          gammaPoleSymbolicMovingCoefficientLaurent_coeff_pos
            (P₀.coeff 0) _ hqpos
      have hP₁zero :
          (gammaPoleSymbolicPolynomialJetLaurentEval n P₁).coeff
              (((J : ℕ) + 1 : ℕ) : ℤ) = 0 := by
        have hsum :
            (gammaPoleSymbolicPolynomialJetLaurentEval n P₀).coeff
                (((J : ℕ) + 1 : ℕ) : ℤ) +
              (gammaPoleSymbolicPolynomialJetLaurentEval n P₁).coeff
                (((J : ℕ) + 1 : ℕ) : ℤ) = 0 := by
          change ((gammaPoleSymbolicPolynomialJetLaurentEval n P₀ +
            gammaPoleSymbolicPolynomialJetLaurentEval n P₁).coeff
              (((J : ℕ) + 1 : ℕ) : ℤ)) = 0
          rw [← map_add, hdecomp, hPzero]
        rwa [hP₀zero, zero_add] at hsum
      apply hdiagNe
      rw [hP₁zero]
      rfl
    have hpderivC (j : Fin (n + 1)) :
        MvPolynomial.pderiv j P₁ =
          MvPolynomial.C ((MvPolynomial.pderiv j P₁).coeff 0) :=
      isHomogeneous_zero_eq_C_coeff_zero_polynomial hP₁.pderiv
    have hEuler := hP₁.sum_X_mul_pderiv
    simp only [one_nsmul] at hEuler
    let a := P₀.coeff 0
    let b := (MvPolynomial.pderiv (0 : Fin (n + 1)) P₁).coeff 0
    refine ⟨a, b, ?_⟩
    rw [← hdecomp, isHomogeneous_zero_eq_C_coeff_zero_polynomial hP₀]
    change MvPolynomial.C a + P₁ =
      MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0
    congr 1
    rw [← hEuler]
    classical
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · rw [hpderivC]
      change MvPolynomial.X 0 * MvPolynomial.C b =
        MvPolynomial.C b * MvPolynomial.X 0
      ring
    · intro j hjmem hj0
      rw [hpderivC, hpositive j hj0]
      simp
    · intro hnot
      exact (hnot (Finset.mem_univ (0 : Fin (n + 1)))).elim
  · rintro ⟨a, b, rfl⟩
    intro q hq
    rw [map_add, map_mul]
    simp only [gammaPoleSymbolicPolynomialJetLaurentEval,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    change (gammaPoleSymbolicMovingCoefficientLaurent a).coeff q +
      (gammaPoleSymbolicMovingCoefficientLaurent b *
        gammaPoleSymbolicDerivativeLaurentProfile 0).coeff q = 0
    rw [gammaPoleSymbolicMovingCoefficientLaurent_coeff_pos a q (by omega),
      gammaPoleSymbolicMovingCoefficient_mul_derivativeProfile_coeff_eq_zero_of_gt
        b 0 q (by simpa using hq)]
    simp

/-- **Actual moving-coefficient Gamma affine horizon.**  The actual faithful
Gamma boundary profile has at most a simple outer pole exactly for polynomial-
coefficient sources affine in the undifferentiated carrier. -/
theorem gammaPoleProfileAtMostSimple_iff_affine
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    GammaPoleProfileAtMostSimple n P ↔
      ∃ a b : Polynomial ℂ,
        P = MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 := by
  rw [gammaPoleProfileAtMostSimple_iff_symbolic,
    gammaPoleSymbolicProfileAtMostSimple_iff_affine]

end

end GaloisForLFunctions
