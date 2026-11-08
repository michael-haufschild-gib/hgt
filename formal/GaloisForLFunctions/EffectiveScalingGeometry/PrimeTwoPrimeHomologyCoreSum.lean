import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeHomologyProjections
import Mathlib.Algebra.DirectSum.Module

/-!
# Canonical core decomposition of actual augmented homology

The original prime-valued homology is the direct sum of the ranges of its
large-prime core projections. Recombination is injective by orthogonality
and surjective by the finite cycle decomposition. The inverse coordinate
at a core is exactly the original homology projection, and the comparison
retains the actual height map on every coordinate.
-/

noncomputable section
open scoped Classical DirectSum
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- The actual homology contribution supported on one large-prime core. -/
def TwoPrimeHomologyCore (k N : ℕ) (c : TwoPrimeCoreFace) :
    Submodule R ((primeCutoffComplex R (primeValueFunctional R) N).homology k) :=
  (twoPrimeCoreHomologyProjection R k N c).range

/-- Recombine a finitely supported family of actual core homology classes. -/
def twoPrimeHomologyRecombine (k N : ℕ) :
    (⨁ c, TwoPrimeHomologyCore R k N c) →ₗ[R]
      (primeCutoffComplex R (primeValueFunctional R) N).homology k :=
  DirectSum.coeLinearMap (TwoPrimeHomologyCore R k N)

/-- A core projection retains its own range and annihilates every other range. -/
theorem twoPrimeCoreHomologyProjection_range (k N : ℕ) (c d : TwoPrimeCoreFace)
    (a : TwoPrimeHomologyCore R k N d) :
    twoPrimeCoreHomologyProjection R k N c a.val = if c=d then a.val else 0 := by
  obtain ⟨y,hy⟩ := a.property
  by_cases h : c=d
  · subst d
    rw [if_pos rfl]
    calc
      _ = twoPrimeCoreHomologyProjection R k N c (twoPrimeCoreHomologyProjection R k N c y) :=
        congrArg (twoPrimeCoreHomologyProjection R k N c) hy.symm
      _ = twoPrimeCoreHomologyProjection R k N c y :=
        LinearMap.congr_fun (twoPrimeCoreHomologyProjection_idempotent R k N c) y
      _ = a.val := hy
  · rw [if_neg h]
    calc
      _ = twoPrimeCoreHomologyProjection R k N c (twoPrimeCoreHomologyProjection R k N d y) :=
        congrArg (twoPrimeCoreHomologyProjection R k N c) hy.symm
      _ = 0 := LinearMap.congr_fun (twoPrimeCoreHomologyProjection_orthogonal R k N c d h) y

/-- Projecting a recombined family recovers exactly the corresponding component. -/
theorem twoPrimeCoreHomologyProjection_recombine (k N : ℕ)
    (x : ⨁ c, TwoPrimeHomologyCore R k N c) (c : TwoPrimeCoreFace) :
    twoPrimeCoreHomologyProjection R k N c (twoPrimeHomologyRecombine R k N x) = (x c).val := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero,DirectSum.zero_apply,Submodule.coe_zero]
  | of d a =>
    rw [twoPrimeHomologyRecombine,DirectSum.coeLinearMap_of,twoPrimeCoreHomologyProjection_range]
    by_cases h : c=d
    · subst d
      rw [if_pos rfl,DirectSum.of_eq_same]
    · rw [if_neg h,DirectSum.of_eq_of_ne _ _ _ h]
      rfl
  | add x y hx hy =>
    rw [map_add,map_add,hx,hy,DirectSum.add_apply]
    rfl

/-- No nonzero finite family of core classes can recombine to zero. -/
theorem twoPrimeHomologyRecombine_injective (k N : ℕ) :
    Function.Injective (twoPrimeHomologyRecombine R k N) := by
  intro x y h
  apply DirectSum.ext
  intro c
  apply Subtype.ext
  have hc := congrArg (twoPrimeCoreHomologyProjection R k N c) h
  rw [twoPrimeCoreHomologyProjection_recombine,twoPrimeCoreHomologyProjection_recombine] at hc
  exact hc

/-- Every original homology class is represented by finitely many actual core classes. -/
theorem twoPrimeHomologyRecombine_surjective (k N : ℕ) :
    Function.Surjective (twoPrimeHomologyRecombine R k N) := by
  intro x
  obtain ⟨S,hS⟩ := twoPrimeCoreHomologyProjection_finite_sum R k N x
  refine ⟨∑ c ∈ S, DirectSum.lof R TwoPrimeCoreFace (fun c => TwoPrimeHomologyCore R k N c) c
    ⟨twoPrimeCoreHomologyProjection R k N c x,⟨x,rfl⟩⟩,?_⟩
  rw [map_sum]
  simpa only [twoPrimeHomologyRecombine,DirectSum.coeLinearMap_lof] using hS

/-- Canonical direct-sum decomposition of the original augmented homology by large-prime core. -/
def twoPrimeHomologyCoreEquiv (k N : ℕ) :
    (primeCutoffComplex R (primeValueFunctional R) N).homology k ≃ₗ[R]
      ⨁ c, TwoPrimeHomologyCore R k N c :=
  (LinearEquiv.ofBijective (twoPrimeHomologyRecombine R k N)
    ⟨twoPrimeHomologyRecombine_injective R k N,twoPrimeHomologyRecombine_surjective R k N⟩).symm

/-- Recombination returns the same original homology class. -/
theorem twoPrimeHomologyRecombine_equiv (k N : ℕ)
    (x : (primeCutoffComplex R (primeValueFunctional R) N).homology k) :
    twoPrimeHomologyRecombine R k N (twoPrimeHomologyCoreEquiv R k N x) = x :=
  (LinearEquiv.ofBijective (twoPrimeHomologyRecombine R k N)
    ⟨twoPrimeHomologyRecombine_injective R k N,twoPrimeHomologyRecombine_surjective R k N⟩).apply_symm_apply x

/-- Every direct-sum coordinate is the original core projection, with no choice of representatives. -/
theorem twoPrimeHomologyCoreEquiv_apply (k N : ℕ)
    (x : (primeCutoffComplex R (primeValueFunctional R) N).homology k) (c : TwoPrimeCoreFace) :
    (twoPrimeHomologyCoreEquiv R k N x c).val = twoPrimeCoreHomologyProjection R k N c x := by
  have h := twoPrimeCoreHomologyProjection_recombine R k N (twoPrimeHomologyCoreEquiv R k N x) c
  rw [twoPrimeHomologyRecombine_equiv] at h
  exact h.symm

/-- The canonical core decomposition retains the original height map on every coordinate. -/
theorem twoPrimeHomologyCoreEquiv_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (primeCutoffComplex R (primeValueFunctional R) N).homology k) (c : TwoPrimeCoreFace) :
    (twoPrimeHomologyCoreEquiv R k M
      ((primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h) x) c).val =
    (primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h)
      (twoPrimeHomologyCoreEquiv R k N x c).val := by
  rw [twoPrimeHomologyCoreEquiv_apply,twoPrimeHomologyCoreEquiv_apply]
  have he := (twoPrimeCoreHomologyProjectionNat R k c).naturality (homOfLE h)
  exact congrArg (fun f :
    (primeCutoffHomology R (primeValueFunctional R) k).obj N ⟶
      (primeCutoffHomology R (primeValueFunctional R) k).obj M => f x) he

#print axioms twoPrimeHomologyCoreEquiv_natural
#print axioms twoPrimeHomologyCoreEquiv
#print axioms twoPrimeHomologyCoreEquiv_apply
end GaloisForLFunctions.EffectiveScalingGeometry
