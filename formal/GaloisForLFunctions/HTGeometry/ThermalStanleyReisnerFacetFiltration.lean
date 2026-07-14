import GaloisForLFunctions.HTGeometry.FacetRestrictionEmbedding

/-!
# Thermal facet filtrations of Stanley--Reisner constraint geometries

An energy marking on the facets of a finite Stanley--Reisner geometry determines a canonical
increasing flag of annihilator ideals.  At threshold `level`, the ideal is the intersection of the
facet ideals whose energy is at least `level`.  The corresponding quotient embeds faithfully into
the product of precisely those surviving facet quotients.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The facets surviving an energy threshold. -/
abbrev EnergyFilteredFacet
    {α : Type*} (facets : Finset (Finset α))
    (energy : facets → ℝ) (level : ℝ) :=
  {F : facets // level ≤ energy F}

/-- The annihilator ideal carried by all facets surviving an energy threshold. -/
def energyFilteredLocalizedFacetIdeal
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level : ℝ) : Ideal S :=
  ⨅ F : EnergyFilteredFacet facets energy level,
    localizedFacetIdeal (R := R) (S := S) F.1.1

/-- Membership in the filtered ideal means vanishing on every facet above the threshold. -/
theorem mem_energyFilteredLocalizedFacetIdeal_iff
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level : ℝ) (P : S) :
    P ∈ energyFilteredLocalizedFacetIdeal (R := R) facets energy level ↔
      ∀ F : facets, level ≤ energy F →
        P ∈ localizedFacetIdeal (R := R) (S := S) F.1 := by
  rw [energyFilteredLocalizedFacetIdeal, Ideal.mem_iInf]
  constructor
  · intro h F hF
    exact h ⟨F, hF⟩
  · intro h F
    exact h F.1 F.2

/-- **Thermal constraint flag.** Raising the energy threshold removes facets and therefore
enlarges their common annihilator ideal. -/
theorem energyFilteredLocalizedFacetIdeal_mono
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ)
    {lower upper : ℝ} (hlevels : lower ≤ upper) :
    energyFilteredLocalizedFacetIdeal (R := R) (S := S) facets energy lower ≤
      energyFilteredLocalizedFacetIdeal (R := R) (S := S) facets energy upper := by
  intro P hP
  rw [mem_energyFilteredLocalizedFacetIdeal_iff] at hP ⊢
  intro F hF
  exact hP F (hlevels.trans hF)

/-- Shifting every facet energy and the threshold by the same constant leaves the constraint
ideal unchanged. -/
theorem energyFilteredLocalizedFacetIdeal_add_const
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level shift : ℝ) :
    energyFilteredLocalizedFacetIdeal (R := R) (S := S) facets
        (fun F => energy F + shift) (level + shift) =
      energyFilteredLocalizedFacetIdeal (R := R) (S := S) facets energy level := by
  ext P
  rw [mem_energyFilteredLocalizedFacetIdeal_iff,
    mem_energyFilteredLocalizedFacetIdeal_iff]
  constructor
  · intro h F hF
    exact h F (by linarith)
  · intro h F hF
    exact h F (by linarith)

/-- Below the minimum facet energy, the thermal ideal is the full localized
Stanley--Reisner ideal. -/
theorem energyFilteredLocalizedFacetIdeal_eq_localizedStanleyReisnerIdeal
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    (M : Submonoid (MvPolynomial α R))
    [Algebra (MvPolynomial α R) S] [IsLocalization M S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level : ℝ)
    (hbelow : ∀ F, level ≤ energy F) :
    energyFilteredLocalizedFacetIdeal (R := R) (S := S) facets energy level =
      localizedStanleyReisnerIdeal (R := R) (S := S) facets := by
  rw [localizedStanleyReisnerIdeal_eq_iInf_localizedFacetIdeal M facets]
  ext P
  rw [mem_energyFilteredLocalizedFacetIdeal_iff, Ideal.mem_iInf]
  constructor
  · intro h F
    exact h F (hbelow F)
  · intro h F hF
    exact h F

/-- At an upper energy radius, the filtered ideal is exactly the intersection over the exposed
maximum-energy facets. -/
theorem mem_energyFilteredLocalizedFacetIdeal_radius_iff
    {R α S : Type*} [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (radius : ℝ)
    (hupper : ∀ F, energy F ≤ radius) (P : S) :
    P ∈ energyFilteredLocalizedFacetIdeal (R := R) (S := S)
        facets energy radius ↔
      ∀ F : facets, energy F = radius →
        P ∈ localizedFacetIdeal (R := R) (S := S) F.1 := by
  rw [mem_energyFilteredLocalizedFacetIdeal_iff]
  constructor
  · intro h F hF
    exact h F hF.ge
  · intro h F hF
    exact h F (le_antisymm (hupper F) hF)

/-- Simultaneous restriction to precisely the facets surviving the energy threshold. -/
def energyFilteredFacetQuotientMap
    {k R α S : Type*} [CommRing k] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra k S] [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level : ℝ) :
    S →ₐ[k] ((F : EnergyFilteredFacet facets energy level) →
      S ⧸ localizedFacetIdeal (R := R) (S := S) F.1.1) :=
  facetQuotientMap (k := k)
    (fun F : EnergyFilteredFacet facets energy level =>
      localizedFacetIdeal (R := R) (S := S) F.1.1)

/-- The filtered restriction map has exactly the filtered annihilator as kernel. -/
theorem ker_energyFilteredFacetQuotientMap
    {k R α S : Type*} [CommRing k] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra k S] [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level : ℝ) :
    RingHom.ker
        (energyFilteredFacetQuotientMap (k := k) (R := R) (S := S)
          facets energy level).toRingHom =
      energyFilteredLocalizedFacetIdeal (R := R) (S := S) facets energy level :=
  ker_facetQuotientMap
    (fun F : EnergyFilteredFacet facets energy level =>
      localizedFacetIdeal (R := R) (S := S) F.1.1)

/-- The quotient by the thermal annihilator embeds canonically into the surviving facet
quotients. -/
def energyFilteredFacetEmbedding
    {k R α S : Type*} [CommRing k] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra k S] [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level : ℝ) :
    S ⧸ energyFilteredLocalizedFacetIdeal (R := R) (S := S) facets energy level →ₐ[k]
      ((F : EnergyFilteredFacet facets energy level) →
        S ⧸ localizedFacetIdeal (R := R) (S := S) F.1.1) :=
  facetQuotientEmbedding (k := k)
    (fun F : EnergyFilteredFacet facets energy level =>
      localizedFacetIdeal (R := R) (S := S) F.1.1)

/-- The thermal facet embedding is faithful at every threshold, including thresholds above every
facet energy where the quotient is the zero ring. -/
theorem energyFilteredFacetEmbedding_injective
    {k R α S : Type*} [CommRing k] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra k S] [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level : ℝ) :
    Function.Injective
      (energyFilteredFacetEmbedding (k := k) (R := R) (S := S)
        facets energy level) :=
  facetQuotientEmbedding_injective (k := k)
    (fun F : EnergyFilteredFacet facets energy level =>
      localizedFacetIdeal (R := R) (S := S) F.1.1)

/-- The surviving facet restrictions preserve and reflect linear independence in the filtered
constraint quotient. -/
theorem linearIndependent_energyFilteredFacetEmbedding_iff
    {k R α S ι : Type*} [Field k] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra k S] [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (energy : facets → ℝ) (level : ℝ)
    (P : ι → S ⧸ energyFilteredLocalizedFacetIdeal
      (R := R) (S := S) facets energy level) :
    LinearIndependent k
        ((energyFilteredFacetEmbedding (k := k) (R := R) (S := S)
          facets energy level) ∘ P) ↔
      LinearIndependent k P :=
  linearIndependent_facetQuotientEmbedding_iff
    (fun F : EnergyFilteredFacet facets energy level =>
      localizedFacetIdeal (R := R) (S := S) F.1.1) P

end

end GaloisForLFunctions.HTGeometry
