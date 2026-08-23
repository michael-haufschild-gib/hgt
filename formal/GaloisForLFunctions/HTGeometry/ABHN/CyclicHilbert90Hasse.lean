import GaloisForLFunctions.HTGeometry.ABHN.CyclicHilbert90

/-!
# Hasse quotient form of cyclic Hilbert 90

Cyclic Hilbert 90 identifies multiplicative coboundaries with norm-one units.  The first
isomorphism theorem therefore identifies extension units modulo generator-fixed units with the
norm-one subgroup.  This is the degree-one companion to the cyclic `H²` norm quotient.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Every cyclic coboundary has norm one. -/
theorem cyclicGaloisCoboundary_mem_normKer
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g) (x : Additive Lˣ) :
    cyclicGaloisAdditiveCoboundary g x ∈
      (cyclicGaloisAdditiveNormUnits K L).ker := by
  exact (cyclicGalois_hilbert90_exact hg _).mpr ⟨x, rfl⟩

/-- Cyclic coboundary, corestricted to the norm-one subgroup. -/
noncomputable def cyclicGaloisCoboundaryToNormKer
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Additive Lˣ →+ (cyclicGaloisAdditiveNormUnits K L).ker :=
  (cyclicGaloisAdditiveCoboundary g).codRestrict _
    (cyclicGaloisCoboundary_mem_normKer hg)

/-- Hilbert 90 says the corestricted coboundary exhausts norm-one units. -/
theorem cyclicGaloisCoboundaryToNormKer_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Function.Surjective (cyclicGaloisCoboundaryToNormKer hg) := by
  intro z
  obtain ⟨x, hx⟩ := (cyclicGalois_hilbert90_exact hg z).mp z.property
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

/-- Corestriction to norm-one units does not change the coboundary kernel. -/
theorem cyclicGaloisCoboundaryToNormKer_ker
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    (cyclicGaloisCoboundaryToNormKer hg).ker =
      (cyclicGaloisAdditiveCoboundary g).ker := by
  ext x
  simp [cyclicGaloisCoboundaryToNormKer]

/-- Cyclic Hilbert 90 in first-isomorphism form: extension units modulo generator-fixed units are
the norm-one units. -/
noncomputable def cyclicHilbert90HasseQuotientEquiv
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Additive Lˣ ⧸ (cyclicGaloisAdditiveCoboundary g).ker ≃+
      (cyclicGaloisAdditiveNormUnits K L).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (cyclicGaloisCoboundaryToNormKer_ker hg).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (cyclicGaloisCoboundaryToNormKer hg)
      (cyclicGaloisCoboundaryToNormKer_surjective hg))

/-- The Hilbert-90 quotient equivalence is induced by the coboundary. -/
@[simp] theorem cyclicHilbert90HasseQuotientEquiv_mk
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g) (x : Additive Lˣ) :
    cyclicHilbert90HasseQuotientEquiv hg (QuotientAddGroup.mk x) =
      cyclicGaloisCoboundaryToNormKer hg x := by
  rfl

/-- Two extension units have the same coboundary exactly when their difference is fixed by the
chosen cyclic generator. -/
theorem cyclicHilbert90_congr_hasse_iff
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (x y : Additive Lˣ) :
    x - y ∈ (cyclicGaloisAdditiveCoboundary g).ker ↔
      cyclicGaloisAdditiveCoboundary g x = cyclicGaloisAdditiveCoboundary g y := by
  change cyclicGaloisAdditiveCoboundary g (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every norm-one unit is a cyclic coboundary, uniquely modulo generator-fixed units. -/
theorem cyclicHilbert90_exists_unique_mod_fixed
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
    (z : (cyclicGaloisAdditiveNormUnits K L).ker) :
    ∃ x : Additive Lˣ,
      cyclicGaloisAdditiveCoboundary g x = z.1 ∧
      ∀ y : Additive Lˣ,
        cyclicGaloisAdditiveCoboundary g y = z.1 ↔
          y - x ∈ (cyclicGaloisAdditiveCoboundary g).ker := by
  obtain ⟨x, hx⟩ := cyclicGaloisCoboundaryToNormKer_surjective hg z
  have hx' : cyclicGaloisAdditiveCoboundary g x = z.1 := congrArg Subtype.val hx
  refine ⟨x, hx', fun y => ?_⟩
  simpa only [hx'] using (cyclicHilbert90_congr_hasse_iff (g := g) y x).symm

end


end GaloisForLFunctions.HTGeometry.ABHN
