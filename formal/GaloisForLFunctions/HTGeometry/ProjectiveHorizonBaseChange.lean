import GaloisForLFunctions.HTGeometry.ProjectiveHorizonTransvectionOrbit

/-!
# Base change of the homogeneous jet field

Enlarging the constants enlarges the jet field: a field extension induces an embedding of the
homogeneous jet field carrying each jet coordinate to the corresponding one, and an embedding of
the unimodular group, and the two are compatible with the prolonged action.

Base change is what lets a one-parameter family of observers with constant coefficients be compared
with the same family at a generic coefficient, by moving to the constants extended by one
indeterminate.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]
  {K L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## Base change of the jet field -/

/-- Base change of the homogeneous jet polynomial ring. -/
def jetBaseChangePoly (n K L : Type*) [Field K] [Field L] [Algebra K L] :
    MvPolynomial (n × ℕ) K →+* MvPolynomial (n × ℕ) L :=
  MvPolynomial.map (algebraMap K L)

omit [Fintype n] [DecidableEq n] in
theorem jetBaseChangePoly_injective :
    Function.Injective (jetBaseChangePoly n K L) :=
  MvPolynomial.map_injective _ (algebraMap K L).injective

/-- Base change of the homogeneous jet field. -/
def jetBaseChange (n K L : Type*) [Field K] [Field L] [Algebra K L] :
    HomogeneousJetField n K →+* HomogeneousJetField n L :=
  IsFractionRing.lift
    (g := (algebraMap (MvPolynomial (n × ℕ) L) (HomogeneousJetField n L)).comp
      (jetBaseChangePoly n K L))
    (fun _ _ h => jetBaseChangePoly_injective
      ((IsFractionRing.injective (MvPolynomial (n × ℕ) L) (HomogeneousJetField n L)) h))

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem jetBaseChange_algebraMap (p : MvPolynomial (n × ℕ) K) :
    jetBaseChange n K L (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) p) =
      algebraMap (MvPolynomial (n × ℕ) L) (HomogeneousJetField n L)
        (jetBaseChangePoly n K L p) :=
  IsFractionRing.lift_algebraMap _ p

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem jetBaseChange_freeCoordinate (p : n × ℕ) :
    jetBaseChange n K L (freeCoordinate K (n × ℕ) p) = freeCoordinate L (n × ℕ) p := by
  rw [freeCoordinate, jetBaseChange_algebraMap, jetBaseChangePoly, MvPolynomial.map_X]
  rfl

omit [Fintype n] [DecidableEq n] in
theorem jetBaseChange_injective : Function.Injective (jetBaseChange n K L) :=
  (jetBaseChange n K L).injective

omit [Fintype n] [DecidableEq n] in
/-- Base change is the identity on constants, up to the extension of constants itself. -/
theorem jetBaseChange_algebraMap_base (c : K) :
    jetBaseChange n K L (algebraMap K (HomogeneousJetField n K) c) =
      algebraMap L (HomogeneousJetField n L) (algebraMap K L c) := by
  have h1 : algebraMap K (HomogeneousJetField n K) c =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) (MvPolynomial.C c) := by
    rw [← MvPolynomial.algebraMap_eq]
    exact IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) c
  have h2 : algebraMap L (HomogeneousJetField n L) (algebraMap K L c) =
      algebraMap (MvPolynomial (n × ℕ) L) (HomogeneousJetField n L)
        (MvPolynomial.C (algebraMap K L c)) := by
    rw [← MvPolynomial.algebraMap_eq]
    exact IsScalarTower.algebraMap_apply L (MvPolynomial (n × ℕ) L) (HomogeneousJetField n L) _
  rw [h1, h2, jetBaseChange_algebraMap, jetBaseChangePoly, MvPolynomial.map_C]

/-! ## Base change of the observer group -/

/-- Base change of the unimodular group. -/
def slBaseChange (n : Type*) [Fintype n] [DecidableEq n] (K L : Type*) [Field K] [Field L]
    [Algebra K L] : SpecialLinearGroup n K →* SpecialLinearGroup n L where
  toFun g := ⟨(g : Matrix n n K).map (algebraMap K L), by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, g.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    show ((1 : SpecialLinearGroup n K) : Matrix n n K).map (algebraMap K L) =
      ((1 : SpecialLinearGroup n L) : Matrix n n L)
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_one,
      ← RingHom.mapMatrix_apply, map_one]
  map_mul' g h := by
    apply Subtype.ext
    show ((g * h : SpecialLinearGroup n K) : Matrix n n K).map (algebraMap K L) =
      ((g : Matrix n n K).map (algebraMap K L)) * ((h : Matrix n n K).map (algebraMap K L))
    rw [Matrix.SpecialLinearGroup.coe_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← RingHom.mapMatrix_apply, map_mul]

@[simp]
theorem slBaseChange_coe (g : SpecialLinearGroup n K) (a b : n) :
    ((slBaseChange n K L g : SpecialLinearGroup n L) : Matrix n n L) a b =
      algebraMap K L ((g : Matrix n n K) a b) := rfl

/-! ## Compatibility -/

theorem slBaseChange_inv_coe (g : SpecialLinearGroup n K) (a b : n) :
    (((slBaseChange n K L g)⁻¹ : SpecialLinearGroup n L) : Matrix n n L) a b =
      algebraMap K L (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) a b) := by
  rw [← map_inv (slBaseChange n K L) g]
  rfl

theorem jetBaseChange_smul (g : SpecialLinearGroup n K) (f : HomogeneousJetField n K) :
    jetBaseChange n K L (g • f) = (slBaseChange n K L g) • (jetBaseChange n K L f) := by
  have hdiv : ∀ (h : SpecialLinearGroup n K) (u v : HomogeneousJetField n K),
      h • (u / v) = (h • u) / (h • v) := by
    intro h u v
    simp only [linearJetAction_apply, map_div₀]
  have hdivL : ∀ (h : SpecialLinearGroup n L) (u v : HomogeneousJetField n L),
      h • (u / v) = (h • u) / (h • v) := by
    intro h u v
    simp only [linearJetAction_apply, map_div₀]
  have hgen : ∀ p : n × ℕ,
      jetBaseChange n K L (g • freeCoordinate K (n × ℕ) p) =
        (slBaseChange n K L g) • (jetBaseChange n K L (freeCoordinate K (n × ℕ) p)) := by
    rintro ⟨k, l⟩
    rw [linearJetAction_freeCoordinate, map_sum, jetBaseChange_freeCoordinate,
      linearJetAction_freeCoordinate]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, jetBaseChange_freeCoordinate]
    congr 1
    rw [jetBaseChange_algebraMap_base, slBaseChange_inv_coe]
  have hpoly : ∀ p : MvPolynomial (n × ℕ) K,
      jetBaseChange n K L (g • algebraMap (MvPolynomial (n × ℕ) K)
          (HomogeneousJetField n K) p) =
        (slBaseChange n K L g) • (jetBaseChange n K L
          (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) p)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        have h1 : algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
            (MvPolynomial.C c) = algebraMap K (HomogeneousJetField n K) c := by
          rw [← MvPolynomial.algebraMap_eq]
          exact (IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K)
            (HomogeneousJetField n K) c).symm
        rw [h1, linearJetAction_algebraMap, jetBaseChange_algebraMap_base,
          linearJetAction_algebraMap]
    | add p q hp hq =>
        rw [map_add, smul_add, map_add, hp, hq, map_add, smul_add]
    | mul_X p q hp =>
        rw [map_mul, smul_mul', map_mul, hp, map_mul, smul_mul']
        congr 1
        exact hgen q
  obtain ⟨a, b, _, rfl⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial (n × ℕ) K) f
  rw [hdiv, map_div₀, hpoly, hpoly, map_div₀, hdivL]

end

end GaloisForLFunctions.HTGeometry
