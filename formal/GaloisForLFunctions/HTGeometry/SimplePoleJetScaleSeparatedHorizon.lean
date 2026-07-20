import GaloisForLFunctions.HTGeometry.SimplePoleJetLatticeAffineHorizon

/-!
# The scale-separated simple-pole horizon

The universal simple-pole profile records pole order and regular boundary jets, but an analytic
moving-pole family also rescales its differentiation coordinate.  At jet ceiling `n`, the `j`th
physical derivative carries the Laurent scale `S⁻ʲ`.  Clearing the common homogeneous denominator
replaces it by the Rees-weighted jet

`Yⱼ ↦ S^(n-j) Jⱼ(T)`.

This module proves that the extra scale cannot create a hidden nonlinear simple-pole sector.
Forgetting the scale by setting `S = 1` recovers the universal profile exactly, so the
scale-separated profile has pole degree at most one precisely for `a + b Y₀`.

The result is the correct algebraic bridge for the factorially rescaled Gamma pole tower.  It does
not make the false claim that a fixed normalized pole germ has an affine horizon: without the
independent moving scale, Riccati-type nonlinear cancellations can occur.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial

noncomputable section

/-- Boundary jets together with one distinguished moving-pole scale variable.  `none` is the
scale and `some k` is the regular `k`th boundary jet. -/
abbrev ScaleSeparatedPoleBoundaryRing := MvPolynomial (Option ℕ) ℂ

/-- Include the regular boundary ring into the scale-separated boundary ring. -/
def simplePoleBoundaryInclude :
    UniversalPoleBoundaryRing →+* ScaleSeparatedPoleBoundaryRing :=
  (MvPolynomial.rename some).toRingHom

/-- Forget the moving scale by setting it to one, while retaining every regular boundary jet. -/
def simplePoleScaleForget :
    ScaleSeparatedPoleBoundaryRing →+* UniversalPoleBoundaryRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun o =>
    match o with
    | none => 1
    | some k => MvPolynomial.X k

@[simp]
theorem simplePoleScaleForget_C (c : ℂ) :
    simplePoleScaleForget (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [simplePoleScaleForget]

/-- Forgetting the scale retracts the boundary inclusion. -/
theorem simplePoleScaleForget_comp_boundaryInclude :
    simplePoleScaleForget.comp simplePoleBoundaryInclude = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [simplePoleScaleForget, simplePoleBoundaryInclude]
  · intro k
    simp [simplePoleScaleForget, simplePoleBoundaryInclude]

/-- The scale-cleared profile of the `j`th jet at finite jet ceiling `n`.  The exponent `n-j` is
nonnegative by construction. -/
def scaleSeparatedSimplePoleJetProfile (n : ℕ) (j : Fin (n + 1)) :
    Polynomial ScaleSeparatedPoleBoundaryRing :=
  Polynomial.C (MvPolynomial.X none ^ (n - (j : ℕ))) *
    (universalSimplePoleJetProfile (j : ℕ)).map simplePoleBoundaryInclude

/-- Evaluation of a finite differential polynomial on all scale-cleared simple-pole jets. -/
def finiteScaleSeparatedSimplePoleProfileEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial ScaleSeparatedPoleBoundaryRing :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp MvPolynomial.C)
    (scaleSeparatedSimplePoleJetProfile n)

/-- Scale-cleared regular factors, after removing the common pole variable from every jet. -/
def scaleSeparatedSimplePoleRegularEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial ScaleSeparatedPoleBoundaryRing :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp MvPolynomial.C)
    (fun j =>
      Polynomial.C (MvPolynomial.X none ^ (n - (j : ℕ))) *
        (universalSimplePoleRegularProfile (j : ℕ)).map simplePoleBoundaryInclude)

/-- The scale-separated grade-one boundary substitution.  It records both the derivative weight
`n-j` and the matching regular `j`-jet. -/
def scaleSeparatedSimplePoleBoundaryTrace (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* ScaleSeparatedPoleBoundaryRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j =>
    MvPolynomial.X none ^ (n - (j : ℕ)) * MvPolynomial.X (some (j : ℕ))

/-- A homogeneous source sector remains homogeneous in the regular boundary variables; the
moving scale has weight zero. -/
theorem scaleSeparatedSimplePoleBoundaryTrace_isWeightedHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight
      (scaleSeparatedSimplePoleBoundaryTrace n P) d := by
  exact isWeightedHomogeneous_eval₂_of_isHomogeneous hP _ fun j => by
    have hS :=
      (MvPolynomial.isWeightedHomogeneous_X ℂ simplePoleBoundaryWeight none).pow
        (n - (j : ℕ))
    have hU := MvPolynomial.isWeightedHomogeneous_X ℂ simplePoleBoundaryWeight
      (some (j : ℕ))
    simpa [simplePoleBoundaryWeight] using hS.mul hU

/-- Forgetting the scale in the boundary trace is exactly the canonical finite-to-countable
inclusion of the source polynomial. -/
theorem simplePoleScaleForget_scaleSeparatedSimplePoleBoundaryTrace
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    simplePoleScaleForget (scaleSeparatedSimplePoleBoundaryTrace n P) =
      simplePoleFinToNat n P := by
  let lhs : MvPolynomial (Fin (n + 1)) ℂ →+* UniversalPoleBoundaryRing :=
    simplePoleScaleForget.comp (scaleSeparatedSimplePoleBoundaryTrace n)
  have h : lhs = simplePoleFinToNat n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, simplePoleScaleForget, scaleSeparatedSimplePoleBoundaryTrace,
        simplePoleFinToNat]
    · intro j
      simp [lhs, simplePoleScaleForget, scaleSeparatedSimplePoleBoundaryTrace,
        simplePoleFinToNat]
  exact RingHom.congr_fun h P

/-- The scale-separated boundary trace cannot annihilate a nonzero source polynomial. -/
theorem scaleSeparatedSimplePoleBoundaryTrace_ne_zero
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP0 : P ≠ 0) :
    scaleSeparatedSimplePoleBoundaryTrace n P ≠ 0 := by
  intro hzero
  apply hP0
  apply simplePoleFinToNat_injective n
  calc
    simplePoleFinToNat n P =
        simplePoleScaleForget (scaleSeparatedSimplePoleBoundaryTrace n P) :=
      (simplePoleScaleForget_scaleSeparatedSimplePoleBoundaryTrace n P).symm
    _ = simplePoleScaleForget 0 := congrArg simplePoleScaleForget hzero
    _ = simplePoleFinToNat n 0 := by simp

/-- A homogeneous `d`-particle source has the common pole factor `T^d` also in the
scale-separated profile. -/
theorem finiteScaleSeparatedSimplePoleProfileEval_factor
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    finiteScaleSeparatedSimplePoleProfileEval n P =
      Polynomial.X ^ d * scaleSeparatedSimplePoleRegularEval n P := by
  change MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
      (fun j : Fin (n + 1) => Polynomial.C (MvPolynomial.X none ^ (n - (j : ℕ))) *
        (universalSimplePoleJetProfile (j : ℕ)).map simplePoleBoundaryInclude) P = _
  have hjet (j : Fin (n + 1)) :
      Polynomial.C (MvPolynomial.X none ^ (n - (j : ℕ))) *
          (universalSimplePoleJetProfile (j : ℕ)).map simplePoleBoundaryInclude =
        Polynomial.X *
          (Polynomial.C (MvPolynomial.X none ^ (n - (j : ℕ))) *
            (universalSimplePoleRegularProfile (j : ℕ)).map simplePoleBoundaryInclude) := by
    rw [universalSimplePoleJetProfile, Polynomial.map_mul,
      Polynomial.map_X]
    ring
  simp_rw [hjet]
  exact GaloisForLFunctions.HTGeometry.isHomogeneous_eval₂_scale hP _ _ _

theorem scaleSeparatedSimplePoleRegularEval_eval_zero
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (scaleSeparatedSimplePoleRegularEval n P).eval 0 =
      scaleSeparatedSimplePoleBoundaryTrace n P := by
  let lhs : MvPolynomial (Fin (n + 1)) ℂ →+* ScaleSeparatedPoleBoundaryRing :=
    (Polynomial.evalRingHom 0).comp (scaleSeparatedSimplePoleRegularEval n)
  have h : lhs = scaleSeparatedSimplePoleBoundaryTrace n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, scaleSeparatedSimplePoleRegularEval,
        scaleSeparatedSimplePoleBoundaryTrace]
    · intro j
      simp [lhs, scaleSeparatedSimplePoleRegularEval,
        scaleSeparatedSimplePoleBoundaryTrace, simplePoleBoundaryInclude,
        universalSimplePoleRegularProfile_eval_zero]
  exact RingHom.congr_fun h P

/-- **Scale-separated particle trace.**  The coefficient at the minimal pole grade `d` is the
source polynomial evaluated on the scale-weighted regular boundary jets. -/
theorem finiteScaleSeparatedSimplePoleProfileEval_coeff_particleNumber
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    (finiteScaleSeparatedSimplePoleProfileEval n P).coeff d =
      scaleSeparatedSimplePoleBoundaryTrace n P := by
  rw [finiteScaleSeparatedSimplePoleProfileEval_factor hP]
  calc
    (Polynomial.X ^ d * scaleSeparatedSimplePoleRegularEval n P).coeff d =
        (scaleSeparatedSimplePoleRegularEval n P).coeff 0 := by
      simpa using Polynomial.coeff_X_pow_mul
        (scaleSeparatedSimplePoleRegularEval n P) d 0
    _ = scaleSeparatedSimplePoleBoundaryTrace n P := by
      rw [Polynomial.coeff_zero_eq_eval_zero,
        scaleSeparatedSimplePoleRegularEval_eval_zero]

/-- Setting the scale to one recovers the original universal profile of each jet. -/
theorem map_scaleForget_scaleSeparatedSimplePoleJetProfile
    (n : ℕ) (j : Fin (n + 1)) :
    (scaleSeparatedSimplePoleJetProfile n j).map simplePoleScaleForget =
      universalSimplePoleJetProfile (j : ℕ) := by
  rw [scaleSeparatedSimplePoleJetProfile, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_map]
  rw [show simplePoleScaleForget.comp simplePoleBoundaryInclude = RingHom.id _ from
    simplePoleScaleForget_comp_boundaryInclude]
  simp [simplePoleScaleForget]

/-- **Scale-forgetful reflection law.**  The complete finite Rees profile specializes exactly to
the universal simple-pole profile. -/
theorem map_scaleForget_finiteScaleSeparatedSimplePoleProfileEval
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (finiteScaleSeparatedSimplePoleProfileEval n P).map simplePoleScaleForget =
      finiteUniversalSimplePoleProfileEval n P := by
  let lhs : MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial UniversalPoleBoundaryRing :=
    (Polynomial.mapRingHom simplePoleScaleForget).comp
      (finiteScaleSeparatedSimplePoleProfileEval n)
  have h : lhs = finiteUniversalSimplePoleProfileEval n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, finiteScaleSeparatedSimplePoleProfileEval,
        finiteUniversalSimplePoleProfileEval]
    · intro j
      simp [lhs, finiteScaleSeparatedSimplePoleProfileEval,
        finiteUniversalSimplePoleProfileEval,
        map_scaleForget_scaleSeparatedSimplePoleJetProfile]
  exact RingHom.congr_fun h P

theorem scaleSeparatedSimplePoleJetProfile_zero_natDegree_le_one (n : ℕ) :
    (scaleSeparatedSimplePoleJetProfile n (0 : Fin (n + 1))).natDegree ≤ 1 := by
  have hprofile :
      ((universalSimplePoleJetProfile 0).map simplePoleBoundaryInclude).natDegree ≤ 1 := by
    rw [show universalSimplePoleJetProfile 0 =
        Polynomial.X * Polynomial.C (MvPolynomial.X 0) by
      simp [universalSimplePoleJetProfile, universalSimplePoleRegularProfile]]
    rw [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    refine Polynomial.natDegree_mul_le.trans ?_
    simp
  rw [scaleSeparatedSimplePoleJetProfile]
  exact Polynomial.natDegree_mul_le.trans (by simpa using hprofile)

/-- **Scale-separated affine simple-pole horizon.**  At every finite jet ceiling, adjoining the
independent moving-pole scale and clearing all derivative denominators preserves and reflects the
universal horizon: pole degree at most one is equivalent to an affine polynomial in the
undifferentiated carrier alone. -/
theorem finiteScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (finiteScaleSeparatedSimplePoleProfileEval n P).natDegree ≤ 1 ↔
      ∃ a b : ℂ, P = MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 := by
  constructor
  · intro h
    apply (finiteUniversalSimplePoleProfileEval_natDegree_le_one_iff_affine P).mp
    rw [← map_scaleForget_finiteScaleSeparatedSimplePoleProfileEval]
    exact Polynomial.natDegree_map_le.trans h
  · rintro ⟨a, b, rfl⟩
    simp only [map_add, map_mul, finiteScaleSeparatedSimplePoleProfileEval,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine Polynomial.natDegree_mul_le.trans ?_
    simpa using scaleSeparatedSimplePoleJetProfile_zero_natDegree_le_one n

end

end GaloisForLFunctions.HTGeometry
