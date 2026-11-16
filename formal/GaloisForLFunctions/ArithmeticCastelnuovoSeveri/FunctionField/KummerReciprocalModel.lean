import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerReflectionIdentities
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityCoordinate

/-!
# Reciprocal three-point Kummer models

The branch-exponent identity `(S+1)(T+1)=1+kN` produces an explicit
isomorphism between the corresponding three-point radical fields.
Coordinate inversion and radical recovery prove the isomorphism over
its original constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial

private theorem reciprocal_div_div {F : Type*} [Field F] {a b : F} (ha : a ≠ 0) :
    a / (a / b) = b := by field_simp [ha]

variable {K : Type*} [Field K] (c : Kˣ) (S T n k : ℕ)

/-- The coefficient forced by inversion of the three-point coordinate. -/
def kummerReciprocalCoefficient : Kˣ := (-1) ^ T / c ^ (T + 1)

private def reciprocalBaseHom :
    FractionRing K[X] →ₐ[K] KummerBranchField c 0 S n :=
  (IsScalarTower.toAlgHom K (FractionRing K[X]) _).comp
    (kummerCoordinateInversion K).toAlgHom

private theorem reciprocalBaseHom_coordinate :
    reciprocalBaseHom c S (n := n) (algebraMap K[X] (FractionRing K[X]) X) =
      (algebraMap K[X] (KummerBranchField c 0 S n) X)⁻¹ := by
  change algebraMap (FractionRing K[X]) (KummerBranchField c 0 S n)
    (kummerCoordinateInversion K (algebraMap K[X] (FractionRing K[X]) X)) = _
  rw [kummerCoordinateInversion_X, map_inv₀, ← IsScalarTower.algebraMap_apply]

/-- The reciprocal radical giving the complementary three-point branch exponent. -/
def kummerReciprocalRadical : KummerBranchField c 0 S n :=
  (1 - algebraMap K[X] (KummerBranchField c 0 S n) X) ^ k /
    AdjoinRoot.root (kummerBranchFieldPolynomial c 0 S n) ^ (T + 1)

private theorem reciprocal_polynomial_eval
    (hrel : (S + 1) * (T + 1) = 1 + k * (n + 1)) :
    (kummerBranchFieldPolynomial (kummerReciprocalCoefficient c T) 0 T n).eval₂
      (reciprocalBaseHom c S (n := n)) (kummerReciprocalRadical c S T n k) = 0 := by
  let L := KummerBranchField c 0 S n
  let t := algebraMap K[X] L X
  let z := AdjoinRoot.root (kummerBranchFieldPolynomial c 0 S n)
  have hinj : Function.Injective (algebraMap K[X] L) := by
    rw [IsScalarTower.algebraMap_eq K[X] (FractionRing K[X]) L]
    exact (algebraMap (FractionRing K[X]) L).injective.comp (IsFractionRing.injective K[X] _)
  have ht : t ≠ 0 := fun h => X_ne_zero (hinj (h.trans (map_zero _).symm))
  have hh : 1 - t ≠ 0 := by
    intro h
    have hp : (1 - X : K[X]) = 0 := hinj (by simpa only [map_sub, map_one, map_zero] using h)
    exact kummerBranchFactor_ne_zero (K := K) 0 (by simpa only [zero_add, pow_one] using hp)
  have heq : z ^ (n + 1) = algebraMap K L c * t * (1 - t) ^ S := by
    rw [kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply,
      kummerBranch, map_mul, map_mul, map_pow, map_sub, map_one, map_pow]
    simp only [zero_add, pow_one]
    rw [show algebraMap K[X] L (C (c : K)) = algebraMap K L c from
      (IsScalarTower.algebraMap_apply K K[X] L c).symm]
  have hc0 : algebraMap K L c ≠ 0 := fun h =>
    c.ne_zero ((algebraMap K L).injective (h.trans (map_zero _).symm))
  have hpow := reciprocalRadical_pow hc0 ht hh
    (n + 1) S T k hrel heq
  change (X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X])
    (kummerBranch (kummerReciprocalCoefficient c T) 0 T))).eval₂
      (reciprocalBaseHom c S (n := n)) (kummerReciprocalRadical c S T n k) = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
  change kummerReciprocalRadical c S T n k ^ (n + 1) =
    reciprocalBaseHom c S (n := n)
      (algebraMap K[X] (FractionRing K[X]) (kummerBranch (kummerReciprocalCoefficient c T) 0 T))
  rw [kummerBranch]
  simp only [map_mul, map_pow, map_sub, map_one, zero_add, pow_one]
  rw [reciprocalBaseHom_coordinate]
  have hc : reciprocalBaseHom c S (n := n)
      (algebraMap K[X] (FractionRing K[X]) (C (kummerReciprocalCoefficient c T : K))) =
        algebraMap K L (kummerReciprocalCoefficient c T : K) := by
    have hcbase : algebraMap K[X] (FractionRing K[X]) (C (kummerReciprocalCoefficient c T : K)) =
        algebraMap K (FractionRing K[X]) (kummerReciprocalCoefficient c T : K) :=
      (IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X])
        (kummerReciprocalCoefficient c T : K)).symm
    rw [hcbase]
    exact (reciprocalBaseHom c S (n := n)).commutes _
  rw [hc]
  simpa only [kummerReciprocalRadical, kummerReciprocalCoefficient,
    Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    map_div₀, map_pow, map_neg, map_one] using hpow

/-- The reciprocal model maps by coordinate inversion and explicit radical rescaling. -/
def kummerReciprocalHom (hrel : (S + 1) * (T + 1) = 1 + k * (n + 1)) :
    KummerBranchField (kummerReciprocalCoefficient c T) 0 T n →ₐ[K]
      KummerBranchField c 0 S n :=
  AdjoinRoot.liftAlgHom _ (reciprocalBaseHom c S (n := n))
    (kummerReciprocalRadical c S T n k) (reciprocal_polynomial_eval c S T n k hrel)

/-- The reciprocal model's rational coordinate is the inverse of the original coordinate. -/
theorem kummerReciprocalHom_coordinate
    (hrel : (S + 1) * (T + 1) = 1 + k * (n + 1)) :
    kummerReciprocalHom c S T n k hrel
      (algebraMap K[X] (KummerBranchField (kummerReciprocalCoefficient c T) 0 T n) X) =
        (algebraMap K[X] (KummerBranchField c 0 S n) X)⁻¹ := by
  rw [IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]), AdjoinRoot.algebraMap_eq,
    kummerReciprocalHom, AdjoinRoot.liftAlgHom_of, reciprocalBaseHom_coordinate]

/-- The reciprocal model's radical is the specified quotient of powers. -/
theorem kummerReciprocalHom_root
    (hrel : (S + 1) * (T + 1) = 1 + k * (n + 1)) :
    kummerReciprocalHom c S T n k hrel
      (AdjoinRoot.root (kummerBranchFieldPolynomial (kummerReciprocalCoefficient c T) 0 T n)) =
        kummerReciprocalRadical c S T n k :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The exponent identity recovers both generators, so the reciprocal map is surjective. -/
theorem kummerReciprocalHom_surjective
    (hrel : (S + 1) * (T + 1) = 1 + k * (n + 1)) :
    Function.Surjective (kummerReciprocalHom c S T n k hrel) := by
  let f := kummerReciprocalHom c S T n k hrel
  let L := KummerBranchField c 0 S n
  let t := algebraMap K[X] L X
  let z := AdjoinRoot.root (kummerBranchFieldPolynomial c 0 S n)
  have ht : t ∈ f.fieldRange := by
    have h : t⁻¹ ∈ f.fieldRange := ⟨_, kummerReciprocalHom_coordinate c S T n k hrel⟩
    simpa only [inv_inv] using f.fieldRange.inv_mem h
  have hh : 1 - t ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap K[X] L) := by
      rw [IsScalarTower.algebraMap_eq K[X] (FractionRing K[X]) L]
      exact (algebraMap (FractionRing K[X]) L).injective.comp (IsFractionRing.injective K[X] _)
    exact kummerBranchFactor_ne_zero (K := K) 0
      (hinj (by simpa only [map_sub, map_one, map_zero, map_pow, zero_add, pow_one] using h))
  have hw : kummerReciprocalRadical c S T n k ∈ f.fieldRange :=
    ⟨_, kummerReciprocalHom_root c S T n k hrel⟩
  have hza : z ^ (T + 1) ∈ f.fieldRange := by
    have h := f.fieldRange.div_mem (pow_mem (f.fieldRange.sub_mem f.fieldRange.one_mem ht) k) hw
    have he : (1 - t) ^ k / kummerReciprocalRadical c S T n k = z ^ (T + 1) := by
      change (1 - t) ^ k / ((1 - t) ^ k / z ^ (T + 1)) = z ^ (T + 1)
      exact reciprocal_div_div (pow_ne_zero k hh)
    rw [he] at h
    exact h
  have hzN : z ^ (n + 1) ∈ f.fieldRange := by
    rw [kummerBranchField_root_pow]
    exact kummerBranchField_base_mem_of_coordinate_mem c 0 S n f.fieldRange ht _
  have hz : z ∈ f.fieldRange :=
    intermediateField_mem_of_power_relation f.fieldRange
      (kummerBranchField_root_ne_zero c 0 S n)
      (a := T + 1) (b := S + 1) (N := n + 1) (k := k)
      (by simpa only [Nat.mul_comm (T + 1) (S + 1)] using hrel) hza hzN
  have htop := kummerBranchField_eq_top_of_coordinate_root_mem c 0 S n f.fieldRange ht hz
  intro x
  have hx : x ∈ f.fieldRange := by rw [htop]; trivial
  exact hx

/-- Complementary three-point branch exponents define isomorphic function fields over constants. -/
def kummerReciprocalEquiv (hrel : (S + 1) * (T + 1) = 1 + k * (n + 1)) :
    KummerBranchField (kummerReciprocalCoefficient c T) 0 T n ≃ₐ[K]
      KummerBranchField c 0 S n :=
  AlgEquiv.ofBijective (kummerReciprocalHom c S T n k hrel)
    ⟨(kummerReciprocalHom c S T n k hrel).injective,
      kummerReciprocalHom_surjective c S T n k hrel⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
