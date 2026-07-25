/-
# Quadratic representations inject into Eisenstein divisors

If `z` has Eisenstein norm `K`, then `z * conj z = K`; hence `z` divides
the scalar Eisenstein integer `K`.  This turns the finite
`u² + 3v² = K` representation problem into divisor counting in the
Euclidean domain constructed above.
-/
import GaloisForLFunctions.RHTower.BourgainEisensteinUnits
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

namespace RHTower

open BourgainEisensteinInt

noncomputable section

theorem eisenstein_natCast_ne_zero {K : ℕ} (hK : K ≠ 0) :
    (K : BourgainEisensteinInt) ≠ 0 := by
  exact_mod_cast hK

/-- An Eisenstein integer of norm `K` divides the scalar `K`. -/
theorem eisenstein_dvd_natCast_of_norm_eq
    (z : BourgainEisensteinInt) (K : ℕ)
    (hnorm : norm z = K) :
    z ∣ (K : BourgainEisensteinInt) := by
  refine ⟨conj z, ?_⟩
  rw [mul_conj, hnorm]
  rfl

/-- Zero has at most one bounded representation by `u² + 3v²`. -/
theorem card_bourgainParabolaRepresentationFinset_le_one_of_discriminant_zero
    (H : ℕ) (y : ℕ × ℕ)
    (hy : bourgainParabolaDiscriminant y = 0) :
    (bourgainParabolaRepresentationFinset H y).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro uv xy huv hxy
  have huvEq :
      uv.1 ^ (2 : ℕ) + 3 * uv.2 ^ (2 : ℕ) = 0 := by
    have := (Finset.mem_filter.mp huv).2
    rwa [hy] at this
  have hxyEq :
      xy.1 ^ (2 : ℕ) + 3 * xy.2 ^ (2 : ℕ) = 0 := by
    have := (Finset.mem_filter.mp hxy).2
    rwa [hy] at this
  have huvZero : uv = (0, 0) := by
    apply Prod.ext <;> dsimp
    · nlinarith [sq_nonneg uv.1, sq_nonneg uv.2]
    · nlinarith [sq_nonneg uv.1, sq_nonneg uv.2]
  have hxyZero : xy = (0, 0) := by
    apply Prod.ext <;> dsimp
    · nlinarith [sq_nonneg xy.1, sq_nonneg xy.2]
    · nlinarith [sq_nonneg xy.1, sq_nonneg xy.2]
  exact huvZero.trans hxyZero.symm

/-- For positive discriminant, the bounded quadratic representation set
injects into the divisor type of the corresponding scalar Eisenstein
integer. -/
theorem card_bourgainParabolaRepresentationFinset_le_eisensteinDivisors
    (H : ℕ) (y : ℕ × ℕ)
    (hy : 0 < bourgainParabolaDiscriminant y) :
    (bourgainParabolaRepresentationFinset H y).card ≤
      @Fintype.card
        {z : BourgainEisensteinInt //
          z ∣ ((bourgainParabolaDiscriminant y).natAbs :
            BourgainEisensteinInt)}
        (UniqueFactorizationMonoid.fintypeSubtypeDvd
          ((bourgainParabolaDiscriminant y).natAbs :
            BourgainEisensteinInt)
          (eisenstein_natCast_ne_zero
            (Int.natAbs_ne_zero.mpr (ne_of_gt hy)))) := by
  classical
  let K : ℕ := (bourgainParabolaDiscriminant y).natAbs
  have hK : K ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hy)
  letI : Fintype
      {z : BourgainEisensteinInt //
        z ∣ (K : BourgainEisensteinInt)} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd
      (K : BourgainEisensteinInt)
      (eisenstein_natCast_ne_zero hK)
  let f :
      {uv : ℤ × ℤ //
        uv ∈ bourgainParabolaRepresentationFinset H y} →
        {z : BourgainEisensteinInt //
          z ∣ (K : BourgainEisensteinInt)} :=
    fun uv => ⟨ofQuadraticPair uv.1.1 uv.1.2, by
      apply eisenstein_dvd_natCast_of_norm_eq
      rw [norm_ofQuadraticPair]
      have huvEq := (Finset.mem_filter.mp uv.2).2
      calc
        uv.1.1 ^ (2 : ℕ) + 3 * uv.1.2 ^ (2 : ℕ) =
            bourgainParabolaDiscriminant y := huvEq
        _ = (K : ℤ) := (Int.natAbs_of_nonneg hy.le).symm⟩
  have hf : Function.Injective f := by
    intro uv xy heq
    apply Subtype.ext
    apply ofQuadraticPair_injective
    exact congrArg Subtype.val heq
  have hcard :
      Fintype.card
          {uv : ℤ × ℤ //
            uv ∈ bourgainParabolaRepresentationFinset H y} ≤
        Fintype.card
          {z : BourgainEisensteinInt //
            z ∣ (K : BourgainEisensteinInt)} :=
    Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

end

end RHTower
