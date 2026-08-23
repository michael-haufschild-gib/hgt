import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.RelativeSingularHomology

/-!
# Hasse classification of relative chains

At every degree, an ambient chain is determined modulo the subcomplex by its relative-chain class.
This exposes the degreewise local congruence and realization content of the short exact sequence of
a subcomplex and its quotient.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe v

namespace ModuleSubcomplex

variable {R : Type} [Field R] {K : ChainComplex (ModuleCat.{v} R) ℕ}

/-- Degreewise inclusion followed by relative projection is exact. -/
theorem relativeChain_functionExact (P : ModuleSubcomplex R K) (n : ℕ) :
    Function.Exact (P.incl.f n).hom (P.proj.f n).hom := by
  intro x
  constructor
  · intro hx
    change (P.carrier n).mkQ x = 0 at hx
    exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).mp hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr y.2

/-- Every relative chain class has an ambient representative. -/
theorem relativeChain_projection_surjective (P : ModuleSubcomplex R K) (n : ℕ) :
    Function.Surjective (P.proj.f n).hom :=
  Submodule.Quotient.mk_surjective _

/-- The degreewise subcomplex inclusion has the declared carrier as its range. -/
theorem range_relativeChain_inclusion (P : ModuleSubcomplex R K) (n : ℕ) :
    LinearMap.range (P.incl.f n).hom = P.carrier n := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Ambient chains modulo the subcomplex are the relative chains. -/
noncomputable def relativeChainHasseQuotientEquiv (P : ModuleSubcomplex R K) (n : ℕ) :
    (K.X n ⧸ P.carrier n) ≃ₗ[R] P.quotComplex.X n :=
  (Submodule.quotEquivOfEq _ _ (range_relativeChain_inclusion P n).symm).trans
    (linearHasseQuotientEquiv (P.incl.f n).hom (P.proj.f n).hom
      (relativeChain_functionExact P n) (relativeChain_projection_surjective P n))

/-- Relative-chain projection induces the Hasse quotient equivalence. -/
@[simp] theorem relativeChainHasseQuotientEquiv_mk
    (P : ModuleSubcomplex R K) (n : ℕ) (x : K.X n) :
    relativeChainHasseQuotientEquiv P n (Submodule.Quotient.mk x) = (P.proj.f n).hom x := by
  simp [relativeChainHasseQuotientEquiv]

/-- Two ambient chains determine the same relative class exactly when their difference lies in the
subcomplex. -/
theorem relativeChain_congr_hasse_iff
    (P : ModuleSubcomplex R K) (n : ℕ) (x y : K.X n) :
    x - y ∈ P.carrier n ↔ (P.proj.f n).hom x = (P.proj.f n).hom y := by
  rw [← range_relativeChain_inclusion P n]
  exact
    linearHasse_congr_iff (P.incl.f n).hom (P.proj.f n).hom
      (relativeChain_functionExact P n) x y

/-- Every relative class has an ambient representative, unique modulo the subcomplex. -/
theorem relativeChain_exists_unique_mod_subcomplex
    (P : ModuleSubcomplex R K) (n : ℕ) (q : P.quotComplex.X n) :
    ∃ x : K.X n, (P.proj.f n).hom x = q ∧
      ∀ y : K.X n, (P.proj.f n).hom y = q ↔ y - x ∈ P.carrier n := by
  rw [← range_relativeChain_inclusion P n]
  exact
    linearHasse_exists_unique_mod_global (P.incl.f n).hom (P.proj.f n).hom
      (relativeChain_functionExact P n) (relativeChain_projection_surjective P n) q

end ModuleSubcomplex

end


end GaloisForLFunctions.HTGeometry
