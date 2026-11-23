import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! A family of affine sections with Artinian quotient has a finite
common zero set in the affine open. -/

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SchemeCohomology

variable {X : Scheme.{0}} {U : X.Opens}

/-- The underlying common zero set of affine sections is finite when the
coordinate ring modulo the equations is Artinian. -/
theorem finite_commonZeros_of_isArtinianQuotient (hU : IsAffineOpen U)
    {J : Type*} (r : J → Γ(X, U))
    [IsArtinianRing (Γ(X, U) ⧸ Ideal.span (Set.range r))] :
    {x : X | x ∈ U ∧ ∀ j, x ∉ X.basicOpen (r j)}.Finite := by
  let A := Γ(X, U)
  let I := Ideal.span (Set.range r)
  let q := Ideal.Quotient.mk I
  let f (P : PrimeSpectrum (A ⧸ I)) := hU.fromSpec (PrimeSpectrum.comap q P)
  refine (Set.finite_range f).subset ?_
  rintro x ⟨hx, hz⟩
  let p := hU.primeIdealOf ⟨x, hx⟩
  have hp (j : J) : r j ∈ p.asIdeal := by
    change r j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    rw [hU.primeIdealOf_eq_map_closedPoint]
    change (X.presheaf.germ U x hx).hom (r j) ∈ IsLocalRing.maximalIdeal _
    exact (IsLocalRing.mem_maximalIdeal _).mpr (fun h => hz j ((Scheme.mem_basicOpen X (r j) x hx).mpr h))
  have hi : RingHom.ker q = I := SetLike.ext fun a =>
    RingHom.mem_ker.trans Ideal.Quotient.eq_zero_iff_mem
  have hpr : p ∈ Set.range (PrimeSpectrum.comap q) := by
    rw [range_comap_of_surjective (A ⧸ I) q Ideal.Quotient.mk_surjective, hi]
    exact Ideal.span_le.mpr (Set.range_subset_iff.mpr hp)
  obtain ⟨P, hP⟩ := hpr
  exact ⟨P, (congrArg (fun p : PrimeSpectrum A => hU.fromSpec p) hP).trans
    (hU.fromSpec_primeIdealOf ⟨x, hx⟩)⟩

end GlobalTheory.SchemeCohomology
