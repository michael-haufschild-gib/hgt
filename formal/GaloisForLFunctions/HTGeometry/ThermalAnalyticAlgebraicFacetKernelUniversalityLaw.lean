import GaloisForLFunctions.HTGeometry.GibbsExposedFaceRadicalFlag
import GaloisForLFunctions.HTGeometry.ThermalStanleyReisnerFacetFiltration

/-!
# Thermal analytic--algebraic facet-kernel universality

A finite energy marking cuts out one common flag of surviving facets.  Two apparently different
detectors on this flag have the same pointwise support: the radical of a positive complex Gibbs
Gram form and the intersection of localized Stanley--Reisner facet ideals.  Their simultaneous
kernel is therefore a canonical monotone, energy-origin-invariant joint analytic--algebraic flag,
whose top boundary is supported exactly on the exposed maximum-energy facets.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-- Simultaneous analytic and algebraic kernel at one energy threshold. -/
def thermalAnalyticAlgebraicFacetKernel
    {J R α S : Type*} [Fintype J] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (c : J → facets → ℂ)
    (base energy : facets → ℝ) (level : ℝ) (q : J → ℂ) (P : S) : Prop :=
  HTGeometry.finiteSourceSuperlevelGramEnergy c base energy level q = 0 ∧
    P ∈ energyFilteredLocalizedFacetIdeal (R := R) (S := S) facets energy level

/-- The joint thermal kernel is exactly pointwise joint vanishing on every surviving facet. -/
theorem thermalAnalyticAlgebraicFacetKernel_iff
    {J R α S : Type*} [Fintype J] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (c : J → facets → ℂ)
    (base energy : facets → ℝ) (level : ℝ) (hbase : ∀ F, 0 < base F)
    (q : J → ℂ) (P : S) :
    thermalAnalyticAlgebraicFacetKernel (R := R) (S := S)
        facets c base energy level q P ↔
      ∀ F : facets, level ≤ energy F →
        (∑ j, q j * c j F = 0) ∧
          P ∈ localizedFacetIdeal (R := R) (S := S) F.1 := by
  rw [thermalAnalyticAlgebraicFacetKernel,
    HTGeometry.finiteSourceSuperlevelGramEnergy_eq_zero_iff
      c base energy level hbase q,
    mem_energyFilteredLocalizedFacetIdeal_iff]
  constructor
  · rintro ⟨hgram, hideal⟩ F hF
    exact ⟨hgram F hF, hideal F hF⟩
  · intro h
    exact ⟨fun F hF => (h F hF).1, fun F hF => (h F hF).2⟩

/-- Raising the threshold enlarges the simultaneous analytic--algebraic kernel. -/
theorem thermalAnalyticAlgebraicFacetKernel_mono
    {J R α S : Type*} [Fintype J] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (c : J → facets → ℂ)
    (base energy : facets → ℝ) (hbase : ∀ F, 0 < base F)
    {lower upper : ℝ} (hlevels : lower ≤ upper) (q : J → ℂ) (P : S)
    (hkernel :
      thermalAnalyticAlgebraicFacetKernel (R := R) (S := S)
        facets c base energy lower q P) :
    thermalAnalyticAlgebraicFacetKernel (R := R) (S := S)
      facets c base energy upper q P := by
  rcases hkernel with ⟨hgram, hideal⟩
  exact ⟨
    HTGeometry.finiteSourceSuperlevelGramEnergy_radical_mono
      c base energy hbase hlevels q hgram,
    energyFilteredLocalizedFacetIdeal_mono
      (R := R) (S := S) facets energy hlevels hideal⟩

/-- A common translation of facet energies and threshold leaves the joint kernel unchanged. -/
theorem thermalAnalyticAlgebraicFacetKernel_add_const
    {J R α S : Type*} [Fintype J] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (c : J → facets → ℂ)
    (base energy : facets → ℝ) (level shift : ℝ) (hbase : ∀ F, 0 < base F)
    (q : J → ℂ) (P : S) :
    thermalAnalyticAlgebraicFacetKernel (R := R) (S := S) facets c base
        (fun F => energy F + shift) (level + shift) q P ↔
      thermalAnalyticAlgebraicFacetKernel (R := R) (S := S)
        facets c base energy level q P := by
  rw [thermalAnalyticAlgebraicFacetKernel_iff
      facets c base (fun F => energy F + shift) (level + shift) hbase q P,
    thermalAnalyticAlgebraicFacetKernel_iff
      facets c base energy level hbase q P]
  constructor
  · intro h F hF
    exact h F (by linarith)
  · intro h F hF
    exact h F (by linarith)

/-- At an upper energy radius the joint kernel is supported exactly on exposed facets. -/
theorem thermalAnalyticAlgebraicFacetKernel_radius_iff
    {J R α S : Type*} [Fintype J] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (c : J → facets → ℂ)
    (base energy : facets → ℝ) (radius : ℝ)
    (hbase : ∀ F, 0 < base F) (hupper : ∀ F, energy F ≤ radius)
    (q : J → ℂ) (P : S) :
    thermalAnalyticAlgebraicFacetKernel (R := R) (S := S)
        facets c base energy radius q P ↔
      ∀ F : facets, energy F = radius →
        (∑ j, q j * c j F = 0) ∧
          P ∈ localizedFacetIdeal (R := R) (S := S) F.1 := by
  rw [thermalAnalyticAlgebraicFacetKernel_iff
    facets c base energy radius hbase q P]
  constructor
  · intro h F hF
    exact h F hF.ge
  · intro h F hF
    exact h F (le_antisymm (hupper F) hF)

end

end GaloisForLFunctions.HTGeometry
