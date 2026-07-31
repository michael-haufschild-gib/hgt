import GaloisForLFunctions.HTGeometry.ProjectiveHorizonTransvectionDensity

/-!
# Transvections with a coefficient in the jet field

A moving-frame normalisation wants to shear by a coefficient that is itself a jet observable, not a
constant.  Such a shear is not an element of the observer group, whose entries are constants, so
invariance under the observer group does not transfer to it for free.

Density supplies the transfer.  The orbit of a jet observable under a one-parameter transvection
family is a polynomial in the coefficient, and over an infinite field of constants a jet observable
fixed by every constant coefficient has constant orbit polynomial.  Evaluating that polynomial
identity at an arbitrary element of the jet field, rather than at a constant, shears by a jet
coefficient and still fixes the observable.

This is what makes a normalisation with entries in the jet field legitimate.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Evaluation of an orbit polynomial in the jet field -/

/-- Evaluation of a polynomial with jet-polynomial coefficients at an element of the jet field. -/
def jetPolyEvalField (s : HomogeneousJetField n K) :
    Polynomial (MvPolynomial (n × ℕ) K) →ₐ[K] HomogeneousJetField n K :=
  { Polynomial.eval₂RingHom
      (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)) s with
    commutes' := fun r => by
      show Polynomial.eval₂ _ s (algebraMap K (Polynomial (MvPolynomial (n × ℕ) K)) r) =
        algebraMap K (HomogeneousJetField n K) r
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K)
        (Polynomial (MvPolynomial (n × ℕ) K)) r, Polynomial.algebraMap_eq, Polynomial.eval₂_C,
        ← IsScalarTower.algebraMap_apply] }

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem jetPolyEvalField_apply (s : HomogeneousJetField n K)
    (q : Polynomial (MvPolynomial (n × ℕ) K)) :
    jetPolyEvalField s q =
      Polynomial.eval₂ (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)) s q :=
  rfl

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem jetPolyEvalField_C (s : HomogeneousJetField n K) (p : MvPolynomial (n × ℕ) K) :
    jetPolyEvalField s (Polynomial.C p) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) p :=
  Polynomial.eval₂_C _ _

/-! ## Shearing by a jet coefficient -/

/-- Substitution by a transvection whose coefficient is an arbitrary jet observable. -/
def transvectionSubstAt (x j : n) (s : HomogeneousJetField n K) :
    MvPolynomial (n × ℕ) K →ₐ[K] HomogeneousJetField n K :=
  MvPolynomial.aeval fun p : n × ℕ =>
    freeCoordinate K (n × ℕ) p -
      (if p.1 = x then s * freeCoordinate K (n × ℕ) ((j, p.2) : n × ℕ) else 0)

omit [Fintype n] in
@[simp]
theorem transvectionSubstAt_X (x j : n) (s : HomogeneousJetField n K) (k : n) (l : ℕ) :
    transvectionSubstAt x j s (MvPolynomial.X ((k, l) : n × ℕ)) =
      freeCoordinate K (n × ℕ) (k, l) -
        (if k = x then s * freeCoordinate K (n × ℕ) ((j, l) : n × ℕ) else 0) := by
  rw [transvectionSubstAt, MvPolynomial.aeval_X]

omit [Fintype n] in
/-- Shearing by a jet coefficient is the orbit polynomial evaluated at that coefficient. -/
theorem transvectionSubstAt_eq_eval (x j : n) (s : HomogeneousJetField n K)
    (p : MvPolynomial (n × ℕ) K) :
    transvectionSubstAt x j s p = jetPolyEvalField s (transvectionOrbitPoly (K := K) x j p) := by
  have h : (jetPolyEvalField s).comp (transvectionOrbitPoly (K := K) x j) =
      transvectionSubstAt x j s := by
    apply MvPolynomial.algHom_ext
    rintro ⟨k, l⟩
    rw [AlgHom.comp_apply, transvectionOrbitPoly_X, transvectionSubstAt_X, map_sub,
      jetPolyEvalField_C]
    simp only [freeCoordinate]
    congr 1
    by_cases hkx : k = x
    · rw [if_pos hkx, if_pos hkx, map_mul, jetPolyEvalField_C, jetPolyEvalField_apply,
        Polynomial.eval₂_X]
    · rw [if_neg hkx, if_neg hkx, map_zero]
  exact (DFunLike.congr_fun h p).symm

/-- Shearing by a constant coefficient is the observer substitution by the transvection with that
coefficient, in the pullback convention. -/
theorem transvectionSubstAt_algebraMap (x j : n) (c : K) (p : MvPolynomial (n × ℕ) K) :
    transvectionSubstAt x j (algebraMap K (HomogeneousJetField n K) c) p =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
        (linearJetSubstPoly (Matrix.transvection x j (-c)) p) := by
  have h : transvectionSubstAt (K := K) x j (algebraMap K (HomogeneousJetField n K) c) =
      (IsScalarTower.toAlgHom K (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)).comp
        (linearJetSubstPoly (Matrix.transvection x j (-c))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨k, l⟩
    rw [transvectionSubstAt_X, AlgHom.comp_apply, linearJetSubstPoly_transvection_X]
    show _ = algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) _
    rw [map_add, sub_eq_add_neg]
    simp only [freeCoordinate]
    congr 1
    by_cases hkx : k = x
    · rw [if_pos hkx, if_pos hkx, map_mul, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, map_neg, neg_mul]
    · rw [if_neg hkx, if_neg hkx, map_zero, neg_zero]
  exact DFunLike.congr_fun h p

/-! ## Generic coefficients -/

/-- **Generic coefficient, polynomial form.**  Over an infinite field of constants, a jet
polynomial fixed by every constant transvection of a fixed row and column is fixed by the shear
with an arbitrary jet coefficient. -/
theorem transvectionSubstAt_eq_of_forall [Infinite K] {x j : n}
    {p : MvPolynomial (n × ℕ) K}
    (h : ∀ c : K, linearJetSubstPoly (Matrix.transvection x j c) p = p)
    (s : HomogeneousJetField n K) :
    transvectionSubstAt x j s p =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) p := by
  rw [transvectionSubstAt_eq_eval, transvectionOrbitPoly_eq_C_of_forall h, jetPolyEvalField_C]

/-- **Generic coefficient, rational form.**  Over an infinite field of constants, a rational jet
observable fixed by every constant transvection of a fixed row and column has numerator and
denominator proportional after shearing by an arbitrary jet coefficient. -/
theorem transvectionSubstAt_cross_of_forall [Infinite K] {x j : n} (hx : x ≠ j)
    {A B : MvPolynomial (n × ℕ) K} (hB : B ≠ 0)
    (h : ∀ c : K, (transvectionSL x j hx c) •
        (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A /
          algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A /
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B)
    (s : HomogeneousJetField n K) :
    transvectionSubstAt x j s A *
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A *
        transvectionSubstAt x j s B := by
  have himg := congrArg (jetPolyEvalField s) (transvectionOrbitPoly_cross_of_forall hx hB h)
  rw [map_mul, map_mul, jetPolyEvalField_C, jetPolyEvalField_C] at himg
  rw [transvectionSubstAt_eq_eval, transvectionSubstAt_eq_eval]
  exact himg

/-- **A horizon observable tolerates a jet coefficient.**  A horizon observable of a covector span,
written as a ratio of jet polynomials, satisfies the sheared cross identity for every transvection
with column in the span and arbitrary jet coefficient. -/
theorem horizonField_transvectionSubstAt_cross [Infinite K] {t : Set n} {i x : n}
    (hi : i ∈ t) (hx : x ≠ i) {A B : MvPolynomial (n × ℕ) K} (hB : B ≠ 0)
    (hf : algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A /
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B ∈
      horizonField (K := K) t)
    (s : HomogeneousJetField n K) :
    transvectionSubstAt x i s A *
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A *
        transvectionSubstAt x i s B :=
  transvectionSubstAt_cross_of_forall hx hB
    (fun c => mem_horizonField_iff.1 hf _
      (transvectionSL_mem_chartSubsetTransvectionSet hi hx c)) s

end

end GaloisForLFunctions.HTGeometry
