import GaloisForLFunctions.MvPolynomialGradient
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Semilinear descent of Kähler circuits

An automorphism of a field extension which carries the base field through a
compatible base automorphism acts semilinearly on relative differential
relations.  Rather than constructing this action on the quotient definition
of Kähler differentials, we use the universal property: a differential
relation vanishes exactly when every field-valued relative derivation kills
it, and derivations can be conjugated by the compatible automorphisms.

For additive primitives, the automorphic translate differs from the original
element by a base-field element, so every relative derivation sees the same
differential.  Consequently the coefficient relation space is stable under
coordinatewise application of every difference automorphism.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Conjugate a relative derivation by compatible automorphisms of the base
and extension fields. -/
def conjugateDerivation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (tau : K ≃+* K) (sigma : L ≃+* L)
    (hcomp : ∀ k : K, sigma (algebraMap K L k) =
      algebraMap K L (tau k))
    (D : Derivation K L L) : Derivation K L L :=
  Derivation.mk'
    { toFun := fun z ↦ sigma.symm (D (sigma z))
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro k x
        have hcomp_symm : sigma.symm (algebraMap K L (tau k)) =
            algebraMap K L k := by
          apply sigma.injective
          simp [hcomp]
        simp only [Algebra.smul_def, RingHom.id_apply]
        change sigma.symm (D (sigma (algebraMap K L k * x))) =
          algebraMap K L k * sigma.symm (D (sigma x))
        rw [map_mul, hcomp]
        rw [← Algebra.smul_def, D.map_smul, Algebra.smul_def]
        rw [map_mul, hcomp_symm] }
    (by
      intro x y
      change sigma.symm (D (sigma (x * y))) =
        x * sigma.symm (D (sigma y)) +
          y * sigma.symm (D (sigma x))
      rw [map_mul, Derivation.leibniz]
      simp [smul_eq_mul])

@[simp] theorem conjugateDerivation_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (tau : K ≃+* K) (sigma : L ≃+* L)
    (hcomp : ∀ k : K, sigma (algebraMap K L k) =
      algebraMap K L (tau k))
    (D : Derivation K L L) (x : L) :
    conjugateDerivation tau sigma hcomp D x =
      sigma.symm (D (sigma x)) := rfl

/-- Linear maps commute with finite linear combinations. -/
theorem LinearMap.map_finsupp_linearCombination
    {kappa L M N : Type*} [Semiring L]
    [AddCommMonoid M] [AddCommMonoid N] [Module L M] [Module L N]
    (f : M →ₗ[L] N) (x : kappa → M) (c : kappa →₀ L) :
    f (Finsupp.linearCombination L x c) =
      Finsupp.linearCombination L (fun i ↦ f (x i)) c := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i a
  rw [map_smul]

/-- A linear combination of universal differentials vanishes exactly when
the corresponding combination vanishes for every field-valued relative
derivation. -/
theorem kaehler_linearCombination_eq_zero_iff_forall_derivation
    {kappa K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : kappa → L) (c : kappa →₀ L) :
    Finsupp.linearCombination L
        (fun i ↦ KaehlerDifferential.D K L (x i)) c = 0 ↔
      ∀ D : Derivation K L L,
        Finsupp.linearCombination L (fun i ↦ D (x i)) c = 0 := by
  classical
  let v : KaehlerDifferential K L :=
    Finsupp.linearCombination L
      (fun i ↦ KaehlerDifferential.D K L (x i)) c
  constructor
  · intro hv D
    have hmap := congrArg D.liftKaehlerDifferential hv
    rw [LinearMap.map_finsupp_linearCombination] at hmap
    simpa [v, Derivation.liftKaehlerDifferential_comp_D] using hmap
  · intro h
    change v = 0
    rw [← Module.forall_dual_apply_eq_zero_iff L v]
    intro phi
    let D : Derivation K L L :=
      KaehlerDifferential.linearMapEquivDerivation K L phi
    have hD := h D
    rw [LinearMap.map_finsupp_linearCombination]
    simpa [D, KaehlerDifferential.linearMapEquivDerivation_apply_apply] using hD

/-- Applying an extension automorphism to a finite linear combination
transforms its coefficients semilinearly. -/
theorem ringEquiv_linearCombination
    {kappa L : Type*} [Field L]
    (sigma : L ≃+* L) (x : kappa → L) (c : kappa →₀ L) :
    sigma (Finsupp.linearCombination L x c) =
      Finsupp.linearCombination L (fun k ↦ sigma (x k))
        (Finsupp.mapRange sigma (map_zero sigma) c) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum, Finsupp.sum]
  rw [map_sum]
  simp only [Finsupp.support_mapRange_of_injective
    (map_zero sigma) c sigma.injective]
  apply Finset.sum_congr rfl
  intro k hk
  simp

/-- If every automorphic translate of `x k` differs from `x k` by an
element of the base field, then its Kähler coefficient-relation space is
stable under all compatible extension automorphisms. -/
theorem kaehler_relationSpace_stable_of_base_shifts
    {I kappa K L : Type*} [Field K] [Field L] [Algebra K L]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, sigma i (x k) = x k + algebraMap K L (b i k)) :
    ∀ i c,
      c ∈ LinearMap.ker (Finsupp.linearCombination L
        (fun k ↦ KaehlerDifferential.D K L (x k))) →
      Finsupp.mapRange (sigma i) (map_zero (sigma i)) c ∈
        LinearMap.ker (Finsupp.linearCombination L
          (fun k ↦ KaehlerDifferential.D K L (x k))) := by
  classical
  intro i c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have hforall :=
    (kaehler_linearCombination_eq_zero_iff_forall_derivation x c).mp hc
  rw [kaehler_linearCombination_eq_zero_iff_forall_derivation]
  intro D
  have hconj := hforall
    (conjugateDerivation (tau i) (sigma i) (hcomp i) D)
  have hmapped := congrArg (sigma i) hconj
  rw [ringEquiv_linearCombination] at hmapped
  simpa [hshift, map_add] using hmapped

end

end GaloisForLFunctions
