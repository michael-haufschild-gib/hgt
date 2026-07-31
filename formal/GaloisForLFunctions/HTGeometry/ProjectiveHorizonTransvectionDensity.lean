import GaloisForLFunctions.HTGeometry.ProjectiveHorizonBaseChange

/-!
# The transvection orbit as a polynomial family, and density of constant coefficients

The substitution attached to an elementary transvection is affine linear in the transvection
coefficient, so the orbit of a polynomial jet observable is a genuine polynomial in that
coefficient, with coefficients again jet polynomials.  Evaluating at a constant recovers the
substitution by that constant.

Over an infinite field of constants this makes the constant coefficients Zariski dense in the
one-parameter family: an observable fixed by every constant transvection has a *constant* orbit
polynomial.  For a rational observable the same holds in cross-multiplied form, since a rational
observable is fixed exactly when its numerator and denominator families are proportional.

This is the step that turns invariance under the observer group with constant entries into an
identity of one-parameter families, which is what a moving-frame normalisation needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Substitution by a transvection -/

/-- An elementary transvection substitutes a single jet coordinate, by a multiple of another jet
coordinate of the same order. -/
theorem linearJetSubstPoly_transvection_X (x j : n) (c : K) (k : n) (l : ℕ) :
    linearJetSubstPoly (Matrix.transvection x j c) (MvPolynomial.X ((k, l) : n × ℕ)) =
      MvPolynomial.X ((k, l) : n × ℕ) +
        (if k = x then MvPolynomial.C c * MvPolynomial.X ((j, l) : n × ℕ) else 0) := by
  classical
  rw [linearJetSubstPoly_X]
  have hone : ∑ m : n, MvPolynomial.C ((1 : Matrix n n K) k m) *
      MvPolynomial.X ((m, l) : n × ℕ) = MvPolynomial.X ((k, l) : n × ℕ) := by
    rw [Finset.sum_eq_single k]
    · rw [Matrix.one_apply_eq, map_one, one_mul]
    · intro m _ hm
      rw [Matrix.one_apply_ne (Ne.symm hm), map_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  by_cases hkx : k = x
  · subst hkx
    rw [if_pos rfl,
      Finset.sum_congr rfl fun m _ => by
        rw [transvection_row_self, map_add, add_mul],
      Finset.sum_add_distrib, hone]
    congr 1
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro m _ hm
      rw [if_neg (Ne.symm hm), map_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  · rw [if_neg hkx, add_zero, ← hone]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 2
    rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply,
      if_neg (fun h => hkx h.1.symm), add_zero]

/-! ## The orbit polynomial -/

/-- Evaluation at a jet polynomial, as a map of algebras over the constants. -/
def jetPolyEval (q : MvPolynomial (n × ℕ) K) :
    Polynomial (MvPolynomial (n × ℕ) K) →ₐ[K] MvPolynomial (n × ℕ) K :=
  { Polynomial.evalRingHom q with
    commutes' := fun r => by
      show Polynomial.eval q (algebraMap K (Polynomial (MvPolynomial (n × ℕ) K)) r) =
        algebraMap K (MvPolynomial (n × ℕ) K) r
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K)
        (Polynomial (MvPolynomial (n × ℕ) K)) r, Polynomial.algebraMap_eq, Polynomial.eval_C] }

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem jetPolyEval_apply (q : MvPolynomial (n × ℕ) K)
    (p : Polynomial (MvPolynomial (n × ℕ) K)) :
    jetPolyEval q p = Polynomial.eval q p := rfl

/-- **The transvection orbit of a jet polynomial.**  The orbit of a polynomial jet observable under
the one-parameter transvection family, recorded as a polynomial in the transvection coefficient. -/
def transvectionOrbitPoly (x j : n) :
    MvPolynomial (n × ℕ) K →ₐ[K] Polynomial (MvPolynomial (n × ℕ) K) :=
  MvPolynomial.aeval fun p : n × ℕ =>
    Polynomial.C (MvPolynomial.X p) -
      (if p.1 = x then
        Polynomial.X * Polynomial.C (MvPolynomial.X ((j, p.2) : n × ℕ)) else 0)

omit [Fintype n] in
@[simp]
theorem transvectionOrbitPoly_X (x j : n) (k : n) (l : ℕ) :
    transvectionOrbitPoly (K := K) x j (MvPolynomial.X ((k, l) : n × ℕ)) =
      Polynomial.C (MvPolynomial.X ((k, l) : n × ℕ)) -
        (if k = x then
          Polynomial.X * Polynomial.C (MvPolynomial.X ((j, l) : n × ℕ)) else 0) := by
  rw [transvectionOrbitPoly, MvPolynomial.aeval_X]

/-- **Evaluation recovers the observer.**  Evaluating the orbit polynomial at a constant is the
substitution by the transvection with that coefficient, in the pullback convention. -/
theorem transvectionOrbitPoly_eval (x j : n) (c : K) (p : MvPolynomial (n × ℕ) K) :
    Polynomial.eval (MvPolynomial.C c) (transvectionOrbitPoly (K := K) x j p) =
      linearJetSubstPoly (Matrix.transvection x j (-c)) p := by
  classical
  have h : (jetPolyEval (MvPolynomial.C c)).comp (transvectionOrbitPoly (K := K) x j) =
      linearJetSubstPoly (Matrix.transvection x j (-c)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨k, l⟩
    rw [AlgHom.comp_apply, transvectionOrbitPoly_X, jetPolyEval_apply,
      linearJetSubstPoly_transvection_X]
    by_cases hkx : k = x
    · rw [if_pos hkx, if_pos hkx]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_neg]
      ring
    · rw [if_neg hkx, if_neg hkx]
      simp
  exact DFunLike.congr_fun h p

/-! ## Density of the constant coefficients -/

/-- **Density, polynomial form.**  Over an infinite field of constants, a jet polynomial fixed by
every constant transvection of a fixed row and column has constant orbit polynomial: the whole
one-parameter family fixes it. -/
theorem transvectionOrbitPoly_eq_C_of_forall [Infinite K] {x j : n}
    {p : MvPolynomial (n × ℕ) K}
    (h : ∀ c : K, linearJetSubstPoly (Matrix.transvection x j c) p = p) :
    transvectionOrbitPoly (K := K) x j p = Polynomial.C p := by
  have hsub : Set.range (MvPolynomial.C : K → MvPolynomial (n × ℕ) K) ⊆
      {y | (transvectionOrbitPoly (K := K) x j p - Polynomial.C p).IsRoot y} := by
    rintro y ⟨c, rfl⟩
    show Polynomial.eval (MvPolynomial.C c) _ = 0
    rw [Polynomial.eval_sub, Polynomial.eval_C, transvectionOrbitPoly_eval, h (-c), sub_self]
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _
    ((Set.infinite_range_of_injective (MvPolynomial.C_injective (n × ℕ) K)).mono hsub))

/-- Substitution by a transvection is injective. -/
theorem linearJetSubstPoly_transvection_injective {x j : n} (hx : x ≠ j) (c : K) :
    Function.Injective (linearJetSubstPoly (Matrix.transvection x j c) :
      MvPolynomial (n × ℕ) K → MvPolynomial (n × ℕ) K) :=
  (linearJetSubstEquiv (transvectionSL x j hx c)).injective

/-- The observer action on a ratio of jet polynomials is the ratio of the substituted polynomials.
-/
theorem linearJetAction_div_algebraMap {x j : n} (hx : x ≠ j) (c : K)
    (A B : MvPolynomial (n × ℕ) K) :
    (transvectionSL x j hx c) •
        (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A /
          algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
          (linearJetSubstPoly (Matrix.transvection x j (-c)) A) /
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
          (linearJetSubstPoly (Matrix.transvection x j (-c)) B) := by
  rw [linearJetAction_apply, map_div₀, linearJetFieldEquiv_algebraMap,
    linearJetFieldEquiv_algebraMap, transvectionSL_inv, coe_transvectionSL]

/-- **Density, rational form.**  Over an infinite field of constants, a rational jet observable
fixed by every constant transvection of a fixed row and column has proportional numerator and
denominator orbit families: the identity holds for the whole one-parameter family at once. -/
theorem transvectionOrbitPoly_cross_of_forall [Infinite K] {x j : n} (hx : x ≠ j)
    {A B : MvPolynomial (n × ℕ) K} (hB : B ≠ 0)
    (h : ∀ c : K, (transvectionSL x j hx c) •
        (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A /
          algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A /
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B) :
    transvectionOrbitPoly (K := K) x j A * Polynomial.C B =
      Polynomial.C A * transvectionOrbitPoly (K := K) x j B := by
  have hinj := IsFractionRing.injective (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
  have hBne : algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B ≠ 0 := fun hc =>
    hB (hinj (by rw [hc, map_zero]))
  have key : ∀ c : K,
      linearJetSubstPoly (Matrix.transvection x j (-c)) A * B =
        A * linearJetSubstPoly (Matrix.transvection x j (-c)) B := by
    intro c
    have hBc : algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
        (linearJetSubstPoly (Matrix.transvection x j (-c)) B) ≠ 0 := by
      intro hcon
      refine hB (linearJetSubstPoly_transvection_injective hx (-c) ?_)
      rw [map_zero]
      exact hinj (by rw [hcon, map_zero])
    have hc := h c
    rw [linearJetAction_div_algebraMap hx c A B, div_eq_div_iff hBc hBne, ← map_mul,
      ← map_mul] at hc
    exact hinj hc
  have hsub : Set.range (MvPolynomial.C : K → MvPolynomial (n × ℕ) K) ⊆
      {y | (transvectionOrbitPoly (K := K) x j A * Polynomial.C B -
        Polynomial.C A * transvectionOrbitPoly (K := K) x j B).IsRoot y} := by
    rintro y ⟨c, rfl⟩
    show Polynomial.eval (MvPolynomial.C c) _ = 0
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, transvectionOrbitPoly_eval, transvectionOrbitPoly_eval, key c,
      sub_self]
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _
    ((Set.infinite_range_of_injective (MvPolynomial.C_injective (n × ℕ) K)).mono hsub))

end

end GaloisForLFunctions.HTGeometry
