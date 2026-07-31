import GaloisForLFunctions.HTGeometry.ProjectiveHorizonGenericCoefficient

/-!
# The infinitesimal observer

A matrix of constants moves the source point linearly, and the infinitesimal version of that motion
is a derivation of the jet field: it sends each jet coordinate to the corresponding linear
combination of jet coordinates of the same order.

For an elementary transvection the infinitesimal motion is the coefficient of the transvection
parameter in the orbit polynomial.  Density therefore transfers invariance to the infinitesimal
level: a horizon observable of a covector span is killed by the infinitesimal transvections whose
column lies in the span.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The derivation attached to a matrix of constants -/

/-- The derivation of the jet polynomial ring induced by a matrix of constants. -/
def jetDerivationPoly (M : Matrix n n K) :
    Derivation K (MvPolynomial (n × ℕ) K) (MvPolynomial (n × ℕ) K) :=
  MvPolynomial.mkDerivation K fun p : n × ℕ =>
    ∑ m, MvPolynomial.C (M p.1 m) * MvPolynomial.X ((m, p.2) : n × ℕ)

omit [DecidableEq n] in
@[simp]
theorem jetDerivationPoly_X (M : Matrix n n K) (k : n) (l : ℕ) :
    jetDerivationPoly M (MvPolynomial.X ((k, l) : n × ℕ)) =
      ∑ m, MvPolynomial.C (M k m) * MvPolynomial.X ((m, l) : n × ℕ) :=
  MvPolynomial.mkDerivation_X _ _ _

omit [DecidableEq n] in
@[simp]
theorem jetDerivationPoly_C (M : Matrix n n K) (a : K) :
    jetDerivationPoly M (MvPolynomial.C a) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]
  exact Derivation.map_algebraMap _ _

/-- The infinitesimal motion of an elementary transvection moves one jet coordinate to another of
the same order. -/
theorem jetDerivationPoly_single_X (x i : n) (k : n) (l : ℕ) :
    jetDerivationPoly (Matrix.single x i (1 : K)) (MvPolynomial.X ((k, l) : n × ℕ)) =
      (if k = x then MvPolynomial.X ((i, l) : n × ℕ) else 0) := by
  rw [jetDerivationPoly_X]
  by_cases hkx : k = x
  · subst hkx
    rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, map_one, one_mul]
    · intro m _ hm
      rw [Matrix.single_apply, if_neg fun h => hm h.2.symm, map_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  · rw [if_neg hkx]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Matrix.single_apply, if_neg fun h => hkx h.1.symm, map_zero, zero_mul]

/-- The infinitesimal observer on the jet field. -/
def jetDerivation (M : Matrix n n K) :
    Derivation K (HomogeneousJetField n K) (HomogeneousJetField n K) :=
  extendFreeCoordinatePolynomialDerivation (jetDerivationPoly M)

omit [DecidableEq n] in
@[simp]
theorem jetDerivation_algebraMap (M : Matrix n n K) (p : MvPolynomial (n × ℕ) K) :
    jetDerivation M (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) p) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) (jetDerivationPoly M p) :=
  extendFreeCoordinatePolynomialDerivation_algebraMap _ _

omit [DecidableEq n] in
theorem jetDerivation_freeCoordinate (M : Matrix n n K) (k : n) (l : ℕ) :
    jetDerivation M (freeCoordinate K (n × ℕ) (k, l)) =
      ∑ m, algebraMap K (HomogeneousJetField n K) (M k m) * freeCoordinate K (n × ℕ) (m, l) := by
  simp only [freeCoordinate]
  rw [jetDerivation_algebraMap, jetDerivationPoly_X, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-! ## The infinitesimal motion is the linear coefficient of the orbit -/

theorem coeff_zero_transvectionOrbitPoly (x i : n) (p : MvPolynomial (n × ℕ) K) :
    (transvectionOrbitPoly (K := K) x i p).coeff 0 = p := by
  have hev := transvectionOrbitPoly_eval (K := K) x i 0 p
  rw [MvPolynomial.C_0, neg_zero] at hev
  have hone : Matrix.transvection x i (0 : K) = 1 := by
    rw [Matrix.transvection, Matrix.single_zero, add_zero]
  rw [Polynomial.coeff_zero_eq_eval_zero, hev, hone, linearJetSubstPoly_one, AlgHom.id_apply]

omit [Fintype n] in
theorem transvectionOrbitPoly_C (x i : n) (a : K) :
    transvectionOrbitPoly (K := K) x i (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
  have h : transvectionOrbitPoly (K := K) x i (algebraMap K (MvPolynomial (n × ℕ) K) a) =
      algebraMap K (Polynomial (MvPolynomial (n × ℕ) K)) a := AlgHom.commutes _ a
  rw [MvPolynomial.algebraMap_eq] at h
  rw [h, IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K)
    (Polynomial (MvPolynomial (n × ℕ) K)) a, Polynomial.algebraMap_eq, MvPolynomial.algebraMap_eq]

/-- **The infinitesimal transvection is the linear coefficient of the orbit polynomial.** -/
theorem coeff_one_transvectionOrbitPoly (x i : n) (p : MvPolynomial (n × ℕ) K) :
    (transvectionOrbitPoly (K := K) x i p).coeff 1 =
      -jetDerivationPoly (Matrix.single x i (1 : K)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [transvectionOrbitPoly_C, Polynomial.coeff_C, if_neg one_ne_zero, jetDerivationPoly_C,
        neg_zero]
  | add p q hp hq =>
      rw [map_add, Polynomial.coeff_add, hp, hq, map_add, neg_add]
  | mul_X p q hp =>
      obtain ⟨k, l⟩ := q
      rw [map_mul, transvectionOrbitPoly_X, mul_sub, Polynomial.coeff_sub,
        Polynomial.coeff_mul_C, hp, Derivation.leibniz, jetDerivationPoly_single_X]
      by_cases hkx : k = x
      · rw [if_pos hkx, if_pos hkx, ← mul_assoc, Polynomial.coeff_mul_C,
          Polynomial.coeff_mul_X, coeff_zero_transvectionOrbitPoly]
        simp only [smul_eq_mul]
        ring
      · rw [if_neg hkx, if_neg hkx, mul_zero, Polynomial.coeff_zero]
        simp only [smul_eq_mul]
        ring

/-! ## Infinitesimal invariance -/

/-- **Infinitesimal invariance, polynomial form.**  A jet polynomial fixed by every constant
transvection of a fixed row and column is killed by the corresponding infinitesimal transvection. -/
theorem jetDerivationPoly_single_eq_zero_of_forall [Infinite K] {x i : n}
    {p : MvPolynomial (n × ℕ) K}
    (h : ∀ c : K, linearJetSubstPoly (Matrix.transvection x i c) p = p) :
    jetDerivationPoly (Matrix.single x i (1 : K)) p = 0 := by
  have hc := congrArg (fun q : Polynomial (MvPolynomial (n × ℕ) K) => q.coeff 1)
    (transvectionOrbitPoly_eq_C_of_forall h)
  rw [coeff_one_transvectionOrbitPoly, Polynomial.coeff_C, if_neg one_ne_zero] at hc
  exact neg_eq_zero.1 hc

/-- **Infinitesimal invariance, rational form.**  The numerator and denominator of a fixed rational
jet observable have proportional infinitesimal motions. -/
theorem jetDerivationPoly_single_cross_of_forall [Infinite K] {x i : n} (hx : x ≠ i)
    {A B : MvPolynomial (n × ℕ) K} (hB : B ≠ 0)
    (h : ∀ c : K, (transvectionSL x i hx c) •
        (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A /
          algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A /
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B) :
    B * jetDerivationPoly (Matrix.single x i (1 : K)) A =
      A * jetDerivationPoly (Matrix.single x i (1 : K)) B := by
  have hc := congrArg (fun q : Polynomial (MvPolynomial (n × ℕ) K) => q.coeff 1)
    (transvectionOrbitPoly_cross_of_forall hx hB h)
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul,
    coeff_one_transvectionOrbitPoly] at hc
  linear_combination -hc

/-- **The infinitesimal observer kills the horizon field.**  A horizon observable of a covector span
is killed by every infinitesimal transvection whose column lies in the span. -/
theorem jetDerivation_single_eq_zero_of_mem_horizonField [Infinite K] {t : Set n} {i x : n}
    (hi : i ∈ t) (hx : x ≠ i) {f : HomogeneousJetField n K}
    (hf : f ∈ horizonField (K := K) t) :
    jetDerivation (Matrix.single x i (1 : K)) f = 0 := by
  obtain ⟨A, B, hBmem, rfl⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial (n × ℕ) K) f
  have hB : B ≠ 0 := nonZeroDivisors.ne_zero hBmem
  have hcross := jetDerivationPoly_single_cross_of_forall hx hB
    (fun c => mem_horizonField_iff.1 hf _
      (transvectionSL_mem_chartSubsetTransvectionSet hi hx c))
  rw [Derivation.leibniz_div, jetDerivation_algebraMap, jetDerivation_algebraMap]
  have hzero : algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) B •
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
          (jetDerivationPoly (Matrix.single x i (1 : K)) A) -
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) A •
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
          (jetDerivationPoly (Matrix.single x i (1 : K)) B) = 0 := by
    rw [smul_eq_mul, smul_eq_mul, ← map_mul, ← map_mul, hcross, sub_self]
  rw [hzero, smul_zero]

end

end GaloisForLFunctions.HTGeometry
