import GaloisForLFunctions.HTGeometry.SimplePoleJetLatticeHorizon
import GaloisForLFunctions.HTGeometry.MvPolynomialTopHomogeneousComponent
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The universal simple-pole jet lattice has an affine horizon

`SimplePoleJetLatticeHorizon` identifies the pole-grade trace of one homogeneous
differential-particle sector.  This file joins those separate traces without allowing distinct
particle sectors to cancel.  The extra grading is the ordinary degree in the regular boundary
jets: every coefficient of a degree-`d` source sector remains homogeneous of boundary degree
`d` at every pole grade.

Consequently an arbitrary finite-order differential polynomial whose universal simple-pole
profile has degree at most one has no nonlinear particle sector.  A second, sharp diagonal
extraction then removes every positive derivative coordinate: the coefficient of `X 0` at pole
grade `j+1` sees only the linear `j`th-jet coordinate.  Thus the complete universal horizon is
exactly `C + C Y₀`.

This is a static associated-graded law.  It assumes neither algebraic independence nor an
analytic carrier; those enter only when the universal boundary coordinates are specialized.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial

noncomputable section

/-- The finite source packet of the universal simple-pole profile.  Boundary jets remain indexed
by `ℕ`, while a source polynomial of order `n` uses `Y₀, ..., Yₙ`. -/
def finiteUniversalSimplePoleProfileEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial UniversalPoleBoundaryRing :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp MvPolynomial.C)
    (fun j => universalSimplePoleJetProfile (j : ℕ))

/-- Canonical inclusion of a finite jet packet into the countable universal jet ring. -/
def simplePoleFinToNat (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial ℕ ℂ :=
  (MvPolynomial.rename fun j : Fin (n + 1) => (j : ℕ)).toRingHom

theorem simplePoleFinToNat_injective (n : ℕ) :
    Function.Injective (simplePoleFinToNat n) :=
  MvPolynomial.rename_injective _ Fin.val_injective

/-- In the flattened polynomial ring, the pole variable has boundary weight zero and every
regular-jet variable has boundary weight one. -/
def simplePoleBoundaryWeight : Option ℕ → ℕ
  | none => 0
  | some _ => 1

/-- The regular profile in the flattened ring with variables `none = T` and `some k = X_k`. -/
def universalSimplePoleRegularProfileMV (j : ℕ) : MvPolynomial (Option ℕ) ℂ :=
  ∑ k ∈ Finset.range (j + 1),
    MvPolynomial.C
        ((j.choose k : ℂ) * (-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ)) *
      MvPolynomial.X (some k) * MvPolynomial.X none ^ (j - k)

/-- The full pole profile in flattened coordinates. -/
def universalSimplePoleJetProfileMV (j : ℕ) : MvPolynomial (Option ℕ) ℂ :=
  MvPolynomial.X none * universalSimplePoleRegularProfileMV j

theorem optionEquivLeft_universalSimplePoleRegularProfileMV (j : ℕ) :
    MvPolynomial.optionEquivLeft ℂ ℕ (universalSimplePoleRegularProfileMV j) =
      universalSimplePoleRegularProfile j := by
  simp only [universalSimplePoleRegularProfileMV, universalSimplePoleRegularProfile,
    map_sum, map_mul, map_pow, MvPolynomial.optionEquivLeft_C,
    MvPolynomial.optionEquivLeft_X_some, MvPolynomial.optionEquivLeft_X_none]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp

theorem optionEquivLeft_universalSimplePoleJetProfileMV (j : ℕ) :
    MvPolynomial.optionEquivLeft ℂ ℕ (universalSimplePoleJetProfileMV j) =
      universalSimplePoleJetProfile j := by
  rw [universalSimplePoleJetProfileMV, map_mul,
    MvPolynomial.optionEquivLeft_X_none,
    optionEquivLeft_universalSimplePoleRegularProfileMV,
    universalSimplePoleJetProfile]

/-- The finite universal profile before flattening the pole variable and the boundary variables. -/
def finiteUniversalSimplePoleProfileEvalMV (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Option ℕ) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j => universalSimplePoleJetProfileMV (j : ℕ))

theorem optionEquivLeft_finiteUniversalSimplePoleProfileEvalMV
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.optionEquivLeft ℂ ℕ
        (finiteUniversalSimplePoleProfileEvalMV n P) =
      finiteUniversalSimplePoleProfileEval n P := by
  let lhs : MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial UniversalPoleBoundaryRing :=
    (MvPolynomial.optionEquivLeft ℂ ℕ).toRingHom.comp
      (finiteUniversalSimplePoleProfileEvalMV n)
  have hlhs : lhs = finiteUniversalSimplePoleProfileEval n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, finiteUniversalSimplePoleProfileEvalMV,
        finiteUniversalSimplePoleProfileEval]
    · intro j
      simp [lhs, finiteUniversalSimplePoleProfileEvalMV,
        finiteUniversalSimplePoleProfileEval,
        optionEquivLeft_universalSimplePoleJetProfileMV]
  exact RingHom.congr_fun hlhs P

theorem universalSimplePoleRegularProfileMV_isWeightedHomogeneous (j : ℕ) :
    MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight
      (universalSimplePoleRegularProfileMV j) 1 := by
  rw [universalSimplePoleRegularProfileMV]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
  intro k hk
  have hc := MvPolynomial.isWeightedHomogeneous_C simplePoleBoundaryWeight
    ((j.choose k : ℂ) * (-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ))
  have hx := MvPolynomial.isWeightedHomogeneous_X ℂ simplePoleBoundaryWeight (some k)
  have hT :=
    (MvPolynomial.isWeightedHomogeneous_X ℂ simplePoleBoundaryWeight none).pow (j - k)
  simpa [simplePoleBoundaryWeight] using (hc.mul hx).mul hT

theorem universalSimplePoleJetProfileMV_isWeightedHomogeneous (j : ℕ) :
    MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight
      (universalSimplePoleJetProfileMV j) 1 := by
  rw [universalSimplePoleJetProfileMV]
  have hT := MvPolynomial.isWeightedHomogeneous_X ℂ simplePoleBoundaryWeight none
  have hR := universalSimplePoleRegularProfileMV_isWeightedHomogeneous j
  simpa [simplePoleBoundaryWeight] using hT.mul hR

/-- Evaluating a degree-`d` homogeneous source on targets of common weighted degree `e` produces
a boundary polynomial of weighted degree `d * e`. -/
theorem isWeightedHomogeneous_eval₂_of_isHomogeneous_mul
    {σ τ : Type*} {d e : ℕ} {P : MvPolynomial σ ℂ} (hP : P.IsHomogeneous d)
    (w : τ → ℕ) (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ i, MvPolynomial.IsWeightedHomogeneous w (g i) e) :
    MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.eval₂ MvPolynomial.C g P) (d * e) := by
  rw [MvPolynomial.eval₂_eq]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
  intro m hm
  rw [← zero_add (d * e)]
  apply (MvPolynomial.isWeightedHomogeneous_C w (P.coeff m)).mul
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod m.support
    (fun i => g i ^ m i) (fun i => m i * e)
      (fun i _ => (hg i).pow (m i))
  convert hprod using 1
  have hdeg : ∑ i ∈ m.support, m i = d := by
    simpa [Finsupp.weight_apply, smul_eq_mul] using
      hP (MvPolynomial.mem_support_iff.mp hm)
  calc
    d * e = (∑ i ∈ m.support, m i) * e := congrArg (· * e) hdeg.symm
    _ = ∑ i ∈ m.support, m i * e := by rw [Finset.sum_mul]

/-- Evaluating a degree-`d` homogeneous source on weight-one targets produces a
weight-`d` boundary polynomial. -/
theorem isWeightedHomogeneous_eval₂_of_isHomogeneous
    {σ : Type*} {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P.IsHomogeneous d)
    (g : σ → MvPolynomial (Option ℕ) ℂ)
    (hg : ∀ i, MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight (g i) 1) :
    MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight
      (MvPolynomial.eval₂ MvPolynomial.C g P) d := by
  simpa using isWeightedHomogeneous_eval₂_of_isHomogeneous_mul hP
    simplePoleBoundaryWeight g hg

theorem finiteUniversalSimplePoleProfileEvalMV_isWeightedHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight
      (finiteUniversalSimplePoleProfileEvalMV n P) d := by
  exact isWeightedHomogeneous_eval₂_of_isHomogeneous hP _
    (fun j => universalSimplePoleJetProfileMV_isWeightedHomogeneous (j : ℕ))

/-- Separating the weight-zero pole/scale coordinate from a weighted-homogeneous boundary
polynomial leaves an ordinary homogeneous polynomial in every coefficient. -/
theorem coeff_isHomogeneous_of_boundaryWeightedHomogeneous
    {p : MvPolynomial (Option ℕ) ℂ} {d : ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight p d) (q : ℕ) :
    ((MvPolynomial.optionEquivLeft ℂ ℕ p).coeff q).IsHomogeneous d := by
  intro m hm
  have hmSupport : m ∈ ((MvPolynomial.optionEquivLeft ℂ ℕ p).coeff q).support :=
    MvPolynomial.mem_support_iff.mpr hm
  have hfull : m.optionElim q ∈ p.support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft ℂ).mp hmSupport
  have hw := hp (MvPolynomial.mem_support_iff.mp hfull)
  rw [Finsupp.weight_apply, Finsupp.sum_option_index_smul] at hw
  change Finsupp.weight (fun _ : ℕ => 1) m = d
  simpa [simplePoleBoundaryWeight, Finsupp.weight_apply,
    smul_eq_mul] using hw

/-- Every pole-grade coefficient of a degree-`d` source sector remains homogeneous of boundary
degree `d`.  This is the second grading that prevents cancellation between particle sectors. -/
theorem finiteUniversalSimplePoleProfileEval_coeff_isHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d)
    (q : ℕ) :
    ((finiteUniversalSimplePoleProfileEval n P).coeff q).IsHomogeneous d := by
  have h := coeff_isHomogeneous_of_boundaryWeightedHomogeneous
    (finiteUniversalSimplePoleProfileEvalMV_isWeightedHomogeneous hP) q
  rwa [optionEquivLeft_finiteUniversalSimplePoleProfileEvalMV] at h

/-- A total-degree bound permits reconstruction from homogeneous components through that bound. -/
theorem sum_homogeneousComponent_of_totalDegree_le
    {σ : Type*} {P : MvPolynomial σ ℂ} {N : ℕ} (h : P.totalDegree ≤ N) :
    ∑ e ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent e P = P := by
  have hsub : Finset.range (P.totalDegree + 1) ⊆ Finset.range (N + 1) := by
    intro e he
    rw [Finset.mem_range] at he ⊢
    omega
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent P]
  refine (Finset.sum_subset hsub ?_).symm
  intro e he hne
  refine MvPolynomial.homogeneousComponent_eq_zero e P ?_
  rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hne
  exact hne

/-- The finite source profile agrees with the existing countable universal profile after the
canonical inclusion of finite jet coordinates. -/
theorem finiteUniversalSimplePoleProfileEval_eq
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    finiteUniversalSimplePoleProfileEval n P =
      universalSimplePoleProfileEval (simplePoleFinToNat n P) := by
  let lhs := finiteUniversalSimplePoleProfileEval n
  let rhs : MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial UniversalPoleBoundaryRing :=
    universalSimplePoleProfileEval.comp (simplePoleFinToNat n)
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, finiteUniversalSimplePoleProfileEval,
        universalSimplePoleProfileEval, simplePoleFinToNat]
    · intro j
      simp [lhs, rhs, finiteUniversalSimplePoleProfileEval,
        universalSimplePoleProfileEval, simplePoleFinToNat]
  exact RingHom.congr_fun h P

/-- The top homogeneous source sector cannot disappear behind a pole-degree-one profile. -/
theorem finiteUniversalSimplePoleProfileEval_totalDegree_le_one
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hprofile : (finiteUniversalSimplePoleProfileEval n P).natDegree ≤ 1) :
    P.totalDegree ≤ 1 := by
  by_cases hP0 : P = 0
  · simp [hP0]
  let D := P.totalDegree
  by_contra hD
  have hD2 : 2 ≤ D := by omega
  have hcoeff0 : (finiteUniversalSimplePoleProfileEval n P).coeff D = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hprofile (by omega))
  have hsum :
      (∑ e ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent e P) = P := by
    simpa [D] using MvPolynomial.sum_homogeneousComponent P
  have hcoeffsum :
      (∑ e ∈ Finset.range (D + 1),
        (finiteUniversalSimplePoleProfileEval n
          (MvPolynomial.homogeneousComponent e P)).coeff D) = 0 := by
    calc
      _ = (finiteUniversalSimplePoleProfileEval n
          (∑ e ∈ Finset.range (D + 1),
            MvPolynomial.homogeneousComponent e P)).coeff D := by simp
      _ = 0 := by rw [hsum, hcoeff0]
  have hcomponent := congrArg (MvPolynomial.homogeneousComponent D) hcoeffsum
  rw [map_sum, map_zero] at hcomponent
  have hsingle :
      (∑ e ∈ Finset.range (D + 1),
        MvPolynomial.homogeneousComponent D
          ((finiteUniversalSimplePoleProfileEval n
            (MvPolynomial.homogeneousComponent e P)).coeff D)) =
        (finiteUniversalSimplePoleProfileEval n
          (MvPolynomial.homogeneousComponent D P)).coeff D := by
    rw [Finset.sum_eq_single D]
    · rw [MvPolynomial.homogeneousComponent_of_mem
        (finiteUniversalSimplePoleProfileEval_coeff_isHomogeneous
          (MvPolynomial.homogeneousComponent_isHomogeneous D P) D), if_pos rfl]
    · intro e he heD
      rw [MvPolynomial.homogeneousComponent_of_mem
        (finiteUniversalSimplePoleProfileEval_coeff_isHomogeneous
          (MvPolynomial.homogeneousComponent_isHomogeneous e P) D), if_neg (Ne.symm heD)]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self D)) hnot
  have htop : MvPolynomial.homogeneousComponent D P ≠ 0 := by
    simpa [D] using homogeneousComponent_totalDegree_ne_zero hP0
  have htopHom :
      (simplePoleFinToNat n (MvPolynomial.homogeneousComponent D P)).IsHomogeneous D := by
    simpa [simplePoleFinToNat] using
      (MvPolynomial.homogeneousComponent_isHomogeneous D P).rename_isHomogeneous
  rw [hsingle, finiteUniversalSimplePoleProfileEval_eq,
    universalSimplePoleProfileEval_coeff_particleNumber htopHom] at hcomponent
  exact htop (simplePoleFinToNat_injective n hcomponent)

/-- The coefficient of `X₀` on the top pole edge of one jet profile. -/
theorem universalSimplePoleJetProfile_coeff_X_zero (i j : ℕ) :
    MvPolynomial.coeff (Finsupp.single 0 1)
        ((universalSimplePoleJetProfile j).coeff (i + 1)) =
      if j = i then (-1 : ℂ) ^ i * (i.factorial : ℂ) else 0 := by
  rw [universalSimplePoleJetProfile, Polynomial.coeff_X_mul]
  rw [universalSimplePoleRegularProfile, Polynomial.finsetSum_coeff]
  by_cases hji : j = i
  · subst j
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.sub_zero, Nat.choose_zero_right, Polynomial.coeff_monomial,
        Nat.cast_one, one_mul]
      change MvPolynomial.coeff (Finsupp.single 0 1)
          (MvPolynomial.C ((-1 : ℂ) ^ i * (i.factorial : ℂ)) *
            MvPolynomial.X 0) = _
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
      simp [mul_comm]
    · intro k hk hk0
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hki : k ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hsub : i - k ≠ i := by omega
      simp [Polynomial.coeff_monomial, hsub]
    · simp
  · simp only [if_neg hji]
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : j - k = i
    · have hk0 : k ≠ 0 := by
        intro hk0
        subst k
        simp only [Nat.sub_zero] at hik
        exact hji hik
      simp only [Polynomial.coeff_monomial, hik, if_pos]
      change MvPolynomial.coeff (Finsupp.single 0 1)
        (MvPolynomial.C
            ((j.choose k : ℂ) * (-1 : ℂ) ^ i * (i.factorial : ℂ)) *
          MvPolynomial.X k) = 0
      rw [MvPolynomial.coeff_C_mul]
      simp [MvPolynomial.coeff_single_X, hk0]
    · simp [Polynomial.coeff_monomial, hik]

/-- A degree-zero homogeneous multivariate polynomial is its constant coefficient. -/
theorem isHomogeneous_zero_eq_C_coeff_zero
    {σ : Type*} {P : MvPolynomial σ ℂ} (hP : P.IsHomogeneous 0) :
    P = MvPolynomial.C (P.coeff 0) := by
  have h := MvPolynomial.homogeneousComponent_of_mem (m := 0) hP
  rw [if_pos rfl, MvPolynomial.homogeneousComponent_zero] at h
  exact h.symm

/-- In a linear source sector, the `X₀` coefficient at pole grade `j+1` reads exactly the
coefficient of the `j`th jet coordinate, with its nonzero factorial sign. -/
theorem finiteUniversalSimplePoleProfileEval_linear_diagonal
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous 1)
    (j : Fin (n + 1)) :
    MvPolynomial.coeff (Finsupp.single 0 1)
        ((finiteUniversalSimplePoleProfileEval n P).coeff ((j : ℕ) + 1)) =
      ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ)) *
        (MvPolynomial.pderiv j P).coeff 0 := by
  have hEuler := hP.sum_X_mul_pderiv
  simp only [one_nsmul] at hEuler
  have heval : finiteUniversalSimplePoleProfileEval n P =
      ∑ i, finiteUniversalSimplePoleProfileEval n
        (MvPolynomial.X i * MvPolynomial.pderiv i P) := by
    rw [← map_sum, hEuler]
  rw [heval, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single j]
  · have hjhom : (MvPolynomial.pderiv j P).IsHomogeneous 0 := hP.pderiv
    rw [isHomogeneous_zero_eq_C_coeff_zero hjhom, map_mul]
    simp only [finiteUniversalSimplePoleProfileEval,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
    change MvPolynomial.coeff (Finsupp.single 0 1)
        ((universalSimplePoleJetProfile (j : ℕ) *
          Polynomial.C (MvPolynomial.C ((MvPolynomial.pderiv j P).coeff 0))).coeff
            ((j : ℕ) + 1)) = _
    rw [Polynomial.coeff_mul_C, mul_comm, MvPolynomial.coeff_C_mul,
      universalSimplePoleJetProfile_coeff_X_zero, if_pos rfl]
    simp
    ring
  · intro i hi hij
    have hihom : (MvPolynomial.pderiv i P).IsHomogeneous 0 := hP.pderiv
    rw [isHomogeneous_zero_eq_C_coeff_zero hihom, map_mul]
    simp only [finiteUniversalSimplePoleProfileEval,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
    change MvPolynomial.coeff (Finsupp.single 0 1)
        ((universalSimplePoleJetProfile (i : ℕ) *
          Polynomial.C (MvPolynomial.C ((MvPolynomial.pderiv i P).coeff 0))).coeff
            ((j : ℕ) + 1)) = 0
    rw [Polynomial.coeff_mul_C, mul_comm, MvPolynomial.coeff_C_mul,
      universalSimplePoleJetProfile_coeff_X_zero, if_neg]
    · simp
    · exact fun h => hij (Fin.ext h)
  · intro hnot
    exact (hnot (Finset.mem_univ j)).elim

/-- **Universal affine simple-pole horizon.**  A finite-order differential polynomial has
universal pole degree at most one exactly when it is affine in the undifferentiated carrier. -/
theorem finiteUniversalSimplePoleProfileEval_natDegree_le_one_iff_affine
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (finiteUniversalSimplePoleProfileEval n P).natDegree ≤ 1 ↔
      ∃ a b : ℂ, P = MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 := by
  constructor
  · intro hprofile
    have hdegree := finiteUniversalSimplePoleProfileEval_totalDegree_le_one P hprofile
    let P₀ := MvPolynomial.homogeneousComponent 0 P
    let P₁ := MvPolynomial.homogeneousComponent 1 P
    have hdecomp : P₀ + P₁ = P := by
      have hsum := sum_homogeneousComponent_of_totalDegree_le (P := P) (N := 1) hdegree
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
      have hjpos : 2 ≤ (j : ℕ) + 1 := by
        have : 0 < (j : ℕ) := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
        omega
      have hcoeffP :
          (finiteUniversalSimplePoleProfileEval n P).coeff ((j : ℕ) + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt hprofile (by omega))
      have hcoeffdecomp :
          (finiteUniversalSimplePoleProfileEval n P₀).coeff ((j : ℕ) + 1) +
              (finiteUniversalSimplePoleProfileEval n P₁).coeff ((j : ℕ) + 1) = 0 := by
        rw [← Polynomial.coeff_add, ← map_add, hdecomp, hcoeffP]
      have hcomponent := congrArg (MvPolynomial.homogeneousComponent 1) hcoeffdecomp
      rw [map_add, map_zero,
        MvPolynomial.homogeneousComponent_of_mem
          (finiteUniversalSimplePoleProfileEval_coeff_isHomogeneous hP₀ ((j : ℕ) + 1)),
        if_neg one_ne_zero,
        MvPolynomial.homogeneousComponent_of_mem
          (finiteUniversalSimplePoleProfileEval_coeff_isHomogeneous hP₁ ((j : ℕ) + 1)),
        if_pos rfl, zero_add] at hcomponent
      have hdiag := finiteUniversalSimplePoleProfileEval_linear_diagonal hP₁ j
      rw [hcomponent, MvPolynomial.coeff_zero] at hdiag
      have hfactor :
          (-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ) ≠ 0 := by
        exact mul_ne_zero (pow_ne_zero _ (by norm_num))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j : ℕ)))
      exact (mul_eq_zero.mp hdiag.symm).resolve_left hfactor
    have hpderivC (j : Fin (n + 1)) :
        MvPolynomial.pderiv j P₁ =
          MvPolynomial.C ((MvPolynomial.pderiv j P₁).coeff 0) :=
      isHomogeneous_zero_eq_C_coeff_zero hP₁.pderiv
    have hEuler := hP₁.sum_X_mul_pderiv
    simp only [one_nsmul] at hEuler
    let a := P₀.coeff 0
    let b := (MvPolynomial.pderiv (0 : Fin (n + 1)) P₁).coeff 0
    refine ⟨a, b, ?_⟩
    rw [← hdecomp, isHomogeneous_zero_eq_C_coeff_zero hP₀]
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
    simp only [map_add, map_mul, finiteUniversalSimplePoleProfileEval,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    change (Polynomial.C (MvPolynomial.C a) +
      Polynomial.C (MvPolynomial.C b) * universalSimplePoleJetProfile 0).natDegree ≤ 1
    rw [show universalSimplePoleJetProfile 0 =
        Polynomial.X * Polynomial.C (MvPolynomial.X 0) by
      simp [universalSimplePoleJetProfile, universalSimplePoleRegularProfile]]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine Polynomial.natDegree_mul_le.trans ?_
    simp

end

end GaloisForLFunctions.HTGeometry
