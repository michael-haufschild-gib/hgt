import GaloisForLFunctions.HTGeometry.SymmetricAlgebraAlgebraicIndependence
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Module

/-!
# Matroids represented by localized module quotients

This module constructs the matroid of an arbitrary family in a module, then specializes it to
families in a quotient localized from a commutative domain to its fraction field. Independence is
equivalent to absence of a finitely supported relation landing in the quotient submodule, and the
rank of a finite packet is the fraction-field dimension of its localized quotient-class span.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Classical nonZeroDivisors

noncomputable section

universe u

/-- The linear matroid represented by a family in an arbitrary vector space. -/
def moduleFamilyMatroid
    {K M ι : Type u} [Field K] [AddCommGroup M] [Module K M]
    (q : ι → M) : Matroid ι :=
  (AlgebraicIndependent.matroid K (SymmetricAlgebra K M)).comap
    (fun i ↦ SymmetricAlgebra.ι K M (q i))

/-- The represented module-family matroid has the full index type as its ground set. -/
@[simp]
theorem moduleFamilyMatroid_ground
    {K M ι : Type u} [Field K] [AddCommGroup M] [Module K M]
    (q : ι → M) :
    (moduleFamilyMatroid (K := K) q).E = Set.univ := by
  simp [moduleFamilyMatroid]

/-- Independence in the represented module-family matroid is linear independence of the
corresponding restricted family. -/
theorem moduleFamilyMatroid_indep_iff
    {K M ι : Type u} [Field K] [AddCommGroup M] [Module K M]
    (q : ι → M) (I : Set ι) :
    (moduleFamilyMatroid (K := K) q).Indep I ↔
      LinearIndependent K (fun i : I ↦ q i) := by
  let f : ι → SymmetricAlgebra K M := fun i ↦ SymmetricAlgebra.ι K M (q i)
  rw [moduleFamilyMatroid, Matroid.comap_indep_iff,
    AlgebraicIndependent.matroid_indep_iff]
  constructor
  · rintro ⟨himage, hinj⟩
    have himage' : AlgebraicIndependent K
        (fun p : f '' I ↦ (p : SymmetricAlgebra K M)) := by
      simpa [AlgebraicIndepOn] using himage
    have hfamily : AlgebraicIndependent K (fun i : I ↦ f i) :=
      (algebraicIndependent_image (R := K) hinj).mpr himage'
    exact (symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent
      (fun i : I ↦ q i)).mp (by simpa [f] using hfamily)
  · intro hq
    have hfamily : AlgebraicIndependent K (fun i : I ↦ f i) := by
      simpa [f] using
        (symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent
          (fun i : I ↦ q i)).mpr hq
    have hinj : Set.InjOn f I := by
      intro a ha b hb hab
      exact congrArg Subtype.val
        (hfamily.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    have himage : AlgebraicIndependent K
        (fun p : f '' I ↦ (p : SymmetricAlgebra K M)) :=
      (algebraicIndependent_image (R := K) hinj).mp hfamily
    exact ⟨by simpa [AlgebraicIndepOn] using himage, hinj⟩

/-- The rank of a finite represented packet is the dimension of its vector span. -/
theorem moduleFamilyMatroid_eRk_finset
    {K M ι : Type u} [Field K] [AddCommGroup M] [Module K M]
    (q : ι → M) (I : Finset ι) :
    (moduleFamilyMatroid (K := K) q).eRk (↑I : Set ι) =
      (Module.finrank K (Submodule.span K (q '' (↑I : Set ι))) : ℕ∞) := by
  let V := moduleFamilyMatroid (K := K) q
  obtain ⟨B, hB⟩ := V.exists_isBasis (↑I : Set ι)
  have hBfin : B.Finite := (Finset.finite_toSet I).subset hB.subset
  letI : Fintype B := hBfin.fintype
  have hBind : LinearIndepOn K q B := by
    exact (moduleFamilyMatroid_indep_iff (K := K) q B).mp hB.indep
  have hspan : Submodule.span K (q '' B) =
      Submodule.span K (q '' (↑I : Set ι)) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hB.subset)
    · apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨i, hi, rfl⟩ := hy
      apply hBind.mem_span_iff.mpr
      intro hinsert
      have hVInsert : V.Indep (insert i B) :=
        (moduleFamilyMatroid_indep_iff (K := K) q (insert i B)).mpr hinsert
      exact hB.mem_of_insert_indep hi hVInsert
  have hfinrank : Module.finrank K (Submodule.span K (q '' B)) = Fintype.card B := by
    have hrange : Set.range (fun i : B ↦ q i) = q '' B := by
      ext y
      simp
    rw [← hrange]
    exact finrank_span_eq_card hBind
  change V.eRk (↑I : Set ι) = _
  calc
    V.eRk (↑I : Set ι) = B.encard := hB.eRk_eq_encard
    _ = (Fintype.card B : ℕ∞) := by rw [Set.coe_fintypeCard]
    _ = (Module.finrank K (Submodule.span K (q '' B)) : ℕ∞) := by
      exact_mod_cast hfinrank.symm
    _ = (Module.finrank K
        (Submodule.span K (q '' (↑I : Set ι))) : ℕ∞) := by rw [hspan]

/-- A family of quotient classes after localizing the quotient module to the fraction field. -/
def localizedQuotientFamily
    {R M ι : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (q : ι → M) :
    ι → LocalizedModule R⁰ (M ⧸ N) :=
  fun i ↦ LocalizedModule.mkLinearMap R⁰ (M ⧸ N) (N.mkQ (q i))

/-- The matroid represented by localized quotient classes of a module family. -/
def localizedQuotientMatroid
    {R M ι : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (q : ι → M) : Matroid ι :=
  moduleFamilyMatroid (K := FractionRing R) (localizedQuotientFamily N q)

/-- The localized quotient matroid has the full index type as its ground set. -/
@[simp]
theorem localizedQuotientMatroid_ground
    {R M ι : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (q : ι → M) :
    (localizedQuotientMatroid N q).E = Set.univ := by
  simp [localizedQuotientMatroid]

/-- Localization preserves and reflects linear independence of quotient classes over a domain. -/
theorem linearIndependent_localizedQuotientFamily_iff
    {R M ι : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (q : ι → M) :
    LinearIndependent (FractionRing R) (localizedQuotientFamily N q) ↔
      LinearIndependent R (N.mkQ ∘ q) := by
  constructor
  · intro h
    have hR : LinearIndependent R (localizedQuotientFamily N q) :=
      h.restrict_scalars' R
    exact hR.of_comp (LocalizedModule.mkLinearMap R⁰ (M ⧸ N))
  · intro h
    rw [show localizedQuotientFamily N q =
      (fun x => LocalizedModule.mk (N.mkQ (q x)) 1) by rfl]
    exact h.of_isLocalizedModule (FractionRing R) R⁰
      (LocalizedModule.mkLinearMap R⁰ (M ⧸ N))

/-- Quotient classes are linearly independent exactly when every finite relation landing in the
quotient submodule has zero coefficients. -/
theorem linearIndependent_quotientFamily_iff
    {R M ι : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (q : ι → M) :
    LinearIndependent R (N.mkQ ∘ q) ↔
      ∀ c : ι →₀ R, Finsupp.linearCombination R q c ∈ N → c = 0 := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  constructor
  · intro hinj c hc
    have hcq : N.mkQ (Finsupp.linearCombination R q c) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr hc
    have hcmap : Finsupp.linearCombination R (N.mkQ ∘ q) c = 0 := by
      rw [← Finsupp.apply_linearCombination R N.mkQ q]
      exact hcq
    apply hinj
    simpa using hcmap
  · intro h c d hcd
    have hzero : Finsupp.linearCombination R (N.mkQ ∘ q) (c - d) = 0 := by
      rw [map_sub, hcd, sub_self]
    have hmem : Finsupp.linearCombination R q (c - d) ∈ N := by
      apply (Submodule.Quotient.mk_eq_zero N).mp
      change N.mkQ (Finsupp.linearCombination R q (c - d)) = 0
      rw [Finsupp.apply_linearCombination R N.mkQ q]
      exact hzero
    exact sub_eq_zero.mp (h (c - d) hmem)

/-- Localized quotient-class independence in its finite-relation form. -/
theorem linearIndependent_localizedQuotientFamily_iff_relation
    {R M ι : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (q : ι → M) :
    LinearIndependent (FractionRing R) (localizedQuotientFamily N q) ↔
      ∀ c : ι →₀ R, Finsupp.linearCombination R q c ∈ N → c = 0 := by
  rw [linearIndependent_localizedQuotientFamily_iff (R := R) N q,
    linearIndependent_quotientFamily_iff (R := R) N q]

/-- Independence in a localized quotient matroid is absence of a finite relation landing in the
quotient submodule. -/
theorem localizedQuotientMatroid_indep_iff_relation
    {R M ι : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (q : ι → M) (I : Set ι) :
    (localizedQuotientMatroid N q).Indep I ↔
      ∀ c : I →₀ R,
        Finsupp.linearCombination R (fun i : I ↦ q i) c ∈ N → c = 0 := by
  rw [localizedQuotientMatroid,
    moduleFamilyMatroid_indep_iff (K := FractionRing R)]
  change LinearIndependent (FractionRing R)
      (localizedQuotientFamily N (fun i : I ↦ q i)) ↔ _
  rw [linearIndependent_localizedQuotientFamily_iff_relation (R := R)]

/-- The rank of a finite localized quotient packet is the fraction-field dimension of its span. -/
theorem localizedQuotientMatroid_eRk_finset
    {R M ι : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (q : ι → M) (I : Finset ι) :
    (localizedQuotientMatroid N q).eRk (↑I : Set ι) =
      (Module.finrank (FractionRing R)
        (Submodule.span (FractionRing R)
          (localizedQuotientFamily N q '' (↑I : Set ι))) : ℕ∞) := by
  exact moduleFamilyMatroid_eRk_finset (K := FractionRing R)
    (localizedQuotientFamily N q) I

/-- A localized quotient by the range of a linear map is dependent exactly when a nonzero finite
combination of the family is the image of one element. -/
theorem not_linearIndependent_localizedRangeQuotientFamily_iff
    {R G M ι : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup G] [Module R G] [AddCommGroup M] [Module R M]
    (delta : G →ₗ[R] M) (q : ι → M) :
    ¬ LinearIndependent (FractionRing R)
        (localizedQuotientFamily (LinearMap.range delta) q) ↔
      ∃ c : ι →₀ R, c ≠ 0 ∧
        ∃ k : G, Finsupp.linearCombination R q c = delta k := by
  rw [linearIndependent_localizedQuotientFamily_iff_relation (R := R)]
  constructor
  · intro h
    push Not at h
    obtain ⟨c, hcRange, hc0⟩ := h
    obtain ⟨k, hk⟩ := hcRange
    exact ⟨c, hc0, k, hk.symm⟩
  · rintro ⟨c, hc0, k, hk⟩ h
    exact hc0 (h c ⟨k, hk.symm⟩)

end

end GaloisForLFunctions.HTGeometry
