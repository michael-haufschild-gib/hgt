import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.ReflectionEnergy

/-!
# The rank-powered central port in the local ring at the identity wall

The identity ideal `I = (q-1)` is maximal, because `R/I ≅ k`.  In the local ring `R_I` the
characteristic-zero cofactors become units, so the rank-`M` central port has the same Cartier
support as the identity wall and only rescales the conormal coordinate:

* `identityIdeal_isMaximal` — `I` is maximal, hence prime;
* `portCofactor_notMem_identityIdeal` — `1 + q + ⋯ + q^{M-1} ∉ I` in characteristic zero;
* `span_pow_sub_one_localized` — `(q^M - 1) = (q-1)` in `R_I`;
* `span_energyPow_localized` — `(E_M) = I²` in `R_I`;
* `span_curvature_localized` — `(K) = I` in `R_I`, where `K = q - q⁻¹`.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open LaurentPolynomial

universe u

variable {k : Type u} [Field k]

theorem isField_identityFibre : IsField (MonodromyRing k ⧸ identityIdeal k) :=
  MulEquiv.isField (Field.toIsField k) (identityFibreEquiv k).toMulEquiv

instance identityIdeal_isMaximal : (identityIdeal k).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ isField_identityFibre

instance identityIdeal_isPrime : (identityIdeal k).IsPrime :=
  Ideal.IsMaximal.isPrime identityIdeal_isMaximal

theorem notMem_identityIdeal_iff {f : MonodromyRing k} :
    f ∉ identityIdeal k ↔ evalOne k f ≠ 0 := by
  rw [← ker_evalOne, RingHom.mem_ker]

/-- In characteristic zero the rank-`M` cofactor `1 + q + ⋯ + q^{M-1}` does not vanish on the
identity wall. -/
theorem portCofactor_notMem_identityIdeal [CharZero k] {M : ℕ} (hM : M ≠ 0) :
    (portCofactor M : MonodromyRing k) ∉ identityIdeal k := by
  rw [notMem_identityIdeal_iff, evalOne_portCofactor]
  exact_mod_cast hM

/-- In characteristic zero `q + 1` does not vanish on the identity wall. -/
theorem monodromyParam_add_one_notMem_identityIdeal [CharZero k] :
    (monodromyParam k + 1) ∉ identityIdeal k := by
  rw [notMem_identityIdeal_iff, map_add, evalOne_monodromyParam, map_one]
  norm_num

section Localized

/-- The local ring `R_I` at the identity wall. -/
abbrev WallLocalization (k : Type u) [Field k] : Type u :=
  Localization.AtPrime (identityIdeal k)

/-- Elements off the identity wall become units in `R_I`. -/
theorem isUnit_localized {f : MonodromyRing k} (hf : f ∉ identityIdeal k) :
    IsUnit (algebraMap (MonodromyRing k) (WallLocalization k) f) :=
  IsLocalization.map_units (WallLocalization k) (⟨f, hf⟩ : (identityIdeal k).primeCompl)

/-- **Corollary 5.2 (5.5), support half.**  In `R_I` the rank-`M` port equation generates the same
ideal as the identity wall equation. -/
theorem span_pow_sub_one_localized [CharZero k] {M : ℕ} (hM : M ≠ 0) :
    (Ideal.span {algebraMap (MonodromyRing k) (WallLocalization k)
        (monodromyParam k ^ M - 1)} : Ideal (WallLocalization k))
      = Ideal.span {algebraMap (MonodromyRing k) (WallLocalization k) (wallEquation k)} := by
  have hfac : monodromyParam k ^ M - 1 = wallEquation k * portCofactor M :=
    (wallEquation_mul_portCofactor M).symm
  rw [hfac, map_mul]
  exact Ideal.span_singleton_mul_right_unit
    (isUnit_localized (portCofactor_notMem_identityIdeal hM)) _

/-- **Corollary 5.2 (5.5), energy half.**  In `R_I` the rank-`M` energy generates `I²`. -/
theorem span_energyPow_localized [CharZero k] {M : ℕ} (hM : M ≠ 0) :
    (Ideal.span {algebraMap (MonodromyRing k) (WallLocalization k)
        (monodromyEnergyPow M)} : Ideal (WallLocalization k))
      = (Ideal.span {algebraMap (MonodromyRing k) (WallLocalization k) (wallEquation k)}) ^ 2 := by
  have h1 : (Ideal.span {algebraMap (MonodromyRing k) (WallLocalization k)
      (monodromyEnergyPow M)} : Ideal (WallLocalization k))
      = Ideal.map (algebraMap (MonodromyRing k) (WallLocalization k))
        (Ideal.span {monodromyEnergyPow (k := k) M}) := by
    rw [Ideal.map_span]; simp
  have h2 : ∀ f : MonodromyRing k,
      Ideal.map (algebraMap (MonodromyRing k) (WallLocalization k)) (Ideal.span {f})
        = Ideal.span {algebraMap (MonodromyRing k) (WallLocalization k) f} := by
    intro f; rw [Ideal.map_span]; simp
  rw [h1, span_monodromyEnergyPow_eq, Ideal.map_pow, h2, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow, ← map_pow, ← Ideal.span_singleton_pow,
    ← span_pow_sub_one_localized hM, Ideal.span_singleton_pow, map_pow]

/-- **Corollary 5.3 (5.7).**  In `R_I` the ambidexterity curvature generates the identity wall
ideal itself, so its square generates the Fitting energy ideal. -/
theorem span_curvature_localized [CharZero k] :
    (Ideal.span {algebraMap (MonodromyRing k) (WallLocalization k)
        monodromyCurvature} : Ideal (WallLocalization k))
      = Ideal.span {algebraMap (MonodromyRing k) (WallLocalization k) (wallEquation k)} := by
  have hfac : (monodromyCurvature : MonodromyRing k)
      = wallEquation k * ((monodromyParam k + 1) * monodromyInv) := by
    rw [monodromyCurvature, ambiCurvature_eq monodromy_mul_inv, wallEquation]
    ring
  have hunit : IsUnit (algebraMap (MonodromyRing k) (WallLocalization k)
      ((monodromyParam k + 1) * monodromyInv)) := by
    rw [map_mul]
    refine IsUnit.mul (isUnit_localized monodromyParam_add_one_notMem_identityIdeal) ?_
    exact (isUnit_T (-1 : ℤ)).map (algebraMap (MonodromyRing k) (WallLocalization k))
  rw [hfac, map_mul]
  exact Ideal.span_singleton_mul_right_unit hunit _

end Localized

end GaloisForLFunctions.HTGeometry.DerivedSelection
