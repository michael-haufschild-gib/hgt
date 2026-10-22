import GaloisForLFunctions.HTGeometry.RationalNormalConeGenerators
import GaloisForLFunctions.HTGeometry.CohenMacaulayTransport
import GaloisForLFunctions.HTGeometry.RationalNormalConeNormal
import GaloisForLFunctions.RHTower.Deninger.DeningerHankelHigherRankGroebner

/-!
# The `r = 1` Hankel stratum is Cohen–Macaulay, in the card's own presentation

The rank-one moment map sends `a_i` to `U T ^ i`.  Its kernel is the rank-one Hankel secant ideal
(the corpus's `finiteHankelSecantIdeal_eq_parameterization_ker`, after renaming the atom
coordinates), and its image is `Algebra.adjoin K {U T ^ i : i < N}`, which
`rationalNormalCone_eq_adjoin` identifies with the coordinate ring of the affine cone over the
rational normal curve of degree `N - 1`.

```text
rankOneMomentHom, rankOneMomentHom_X, rankOneMomentHom_eq
ker_rankOneMomentHom             ker = finiteHankelSecantIdeal K N 1
range_rankOneMomentHom           range = rationalNormalCone K (N-1)
hankelRankOneQuotientEquiv
    ** MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N 1 ≃+* rationalNormalCone K (N-1) **
isCohenMacaulayRing_hankelSecantQuotient_one
    ** the r = 1 stratum C_{m-1} is Cohen–Macaulay **
```

Transported through `IsCohenMacaulayRing.of_ringEquiv`, this states the card's clause for the final
stratum in exactly the presentation the card uses, not merely for the cone.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

universe u
variable {K : Type u} [Field K]

/-- The rank-one moment map into the two coordinates `U`, `T`. -/
noncomputable def rankOneMomentHom (K : Type u) [Field K] (N : ℕ) :
    MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval (fun i : Fin N => (X 0 : MvPolynomial (Fin 2) K) * X 1 ^ (i : ℕ))

theorem rankOneMomentHom_X (K : Type u) [Field K] (N : ℕ) (i : Fin N) :
    rankOneMomentHom K N (X i)
      = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 (i : ℕ)) (1 : K) := by
  have hX : (X 0 : MvPolynomial (Fin 2) K) = MvPolynomial.monomial (Finsupp.single 0 1) 1 := rfl
  rw [rankOneMomentHom, MvPolynomial.aeval_X, MvPolynomial.X_pow_eq_monomial, hX,
    MvPolynomial.monomial_mul, one_mul]

/-- The two-variable equivalence used to read the rank-one atom coordinates. -/
def rankOneIndexEquiv : (Fin 1 × Fin 2) ≃ Fin 2 where
  toFun := fun p => p.2
  invFun := fun k => (0, k)
  left_inv := by rintro ⟨i, k⟩; ext <;> simp [Fin.fin_one_eq_zero i]
  right_inv := by intro k; rfl

theorem rankOneMomentHom_eq (K : Type u) [Field K] (N : ℕ) :
    (rankOneMomentHom K N : MvPolynomial (Fin N) K →+* MvPolynomial (Fin 2) K)
      = (MvPolynomial.rename rankOneIndexEquiv).toRingHom.comp
        (finiteHankelSecantParameterization K N 1) := by
  refine MvPolynomial.ringHom_ext ?_ ?_
  · intro a
    simp [rankOneMomentHom, finiteHankelSecantParameterization,
      deningerHankelSecantParameterization]
  · intro i
    rw [RingHom.comp_apply]
    simp only [finiteHankelSecantParameterization_X, deningerHankelSecantMoment,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_sum]
    simp only [Finset.univ_unique, Finset.sum_singleton, map_mul, map_pow,
      MvPolynomial.rename_X]
    show rankOneMomentHom K N (X i) = _
    rw [rankOneMomentHom, MvPolynomial.aeval_X]
    rfl

theorem ker_rankOneMomentHom (K : Type u) [Field K] (N : ℕ) :
    RingHom.ker (rankOneMomentHom K N : MvPolynomial (Fin N) K →+* MvPolynomial (Fin 2) K)
      = finiteHankelSecantIdeal K N 1 := by
  rw [rankOneMomentHom_eq, finiteHankelSecantIdeal_eq_parameterization_ker]
  ext p
  simp only [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · intro h
    exact MvPolynomial.rename_injective _ rankOneIndexEquiv.injective (by simpa using h)
  · intro h
    rw [h, map_zero]

theorem range_rankOneMomentHom (K : Type u) [Field K] {N : ℕ} (hN : 1 ≤ N) :
    (rankOneMomentHom K N).range = rationalNormalCone K (N - 1) := by
  classical
  rw [rationalNormalCone_eq_adjoin, rankOneMomentHom,
    ← Algebra.adjoin_range_eq_range_aeval K
      (fun i : Fin N => (X 0 : MvPolynomial (Fin 2) K) * X 1 ^ (i : ℕ))]
  congr 1
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    refine ⟨(i : ℕ), show (i : ℕ) ≤ N - 1 by omega, ?_⟩
    have := rankOneMomentHom_X K N i
    rw [rankOneMomentHom, MvPolynomial.aeval_X] at this
    exact this.symm
  · rintro ⟨j, hj, rfl⟩
    have hj' : j ≤ N - 1 := hj
    have hjN : j < N := by omega
    refine ⟨⟨j, hjN⟩, ?_⟩
    have := rankOneMomentHom_X K N ⟨j, hjN⟩
    rw [rankOneMomentHom, MvPolynomial.aeval_X] at this
    exact this

/-- **The rank-one Hankel secant quotient is the cone over the rational normal curve.** -/
noncomputable def hankelRankOneQuotientEquiv (K : Type u) [Field K] {N : ℕ} (hN : 1 ≤ N) :
    (MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N 1)
      ≃+* rationalNormalCone K (N - 1) := by
  classical
  have hmem : ∀ x, rankOneMomentHom K N x ∈ rationalNormalCone K (N - 1) := by
    intro x
    rw [← range_rankOneMomentHom K hN]
    exact ⟨x, rfl⟩
  set ψ := (rankOneMomentHom K N).codRestrict (rationalNormalCone K (N - 1)) hmem with hψ
  have hsurj : Function.Surjective (ψ : MvPolynomial (Fin N) K →+* rationalNormalCone K (N - 1)) := by
    rintro ⟨y, hy⟩
    rw [← range_rankOneMomentHom K hN] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hker : RingHom.ker (ψ : MvPolynomial (Fin N) K →+* rationalNormalCone K (N - 1))
      = finiteHankelSecantIdeal K N 1 := by
    rw [← ker_rankOneMomentHom K N]
    ext p
    simp only [RingHom.mem_ker, hψ]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

/-- **The `r = 1` stratum of the Hankel stratification is Cohen–Macaulay**, in the card's own
presentation. -/
theorem isCohenMacaulayRing_hankelSecantQuotient_one (K : Type u) [Field K] {N : ℕ} (hN : 2 ≤ N) :
    IsCohenMacaulayRing (MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N 1) :=
  IsCohenMacaulayRing.of_ringEquiv (hankelRankOneQuotientEquiv K (by omega)).symm
    (isCohenMacaulayRing_rationalNormalCone (K := K) (by omega))


end GaloisForLFunctions.HTGeometry
