import GaloisForLFunctions.HTGeometry.QuasiAbelianFacetPaletteCompletion
import GaloisForLFunctions.HTGeometry.CapocasaCatanesePositivity

/-!
# Building a quasi-Abelian facet certificate

`QuasiAbelianFacetCertificate` was introduced as a package of conclusions.  This module supplies
those conclusions rather than assuming them: given the geometric data of a facet -- a period group,
its vertex incidence, and an alternating compatible form that is integral on the group and
nondegenerate -- every analytic field is produced by a theorem.

* the quotient is `W / Gamma` with its quotient topology, so surjectivity and the fibre description
  are definitional;
* noncompactness comes from `not_isCompact_univ_quotient_of_span_ne_top`;
* the Hermitian form is `hermitianOfAlternating`, whose four algebraic clauses are the
  Appell--Humbert dictionary and whose positivity is the Cauchy--Schwarz argument;
* integrality of its imaginary part is integrality of the alternating form, since
  `Im (hermitianOfAlternating E) = E` on the nose.

The remaining inputs -- discreteness, closedness, span deficiency, vertex incidence, integrality and
nondegeneracy of the form -- are the facet data itself, each of which the earlier modules produce
from a factor of automorphy and a nonvanishing theta function.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **A facet certificate built from an integral nondegenerate alternating form.** -/
noncomputable def certificateOfAlternating {α : Type*} [DecidableEq α] (Fs : Finset α)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℝ W]
    (Γ : AddSubgroup W) [DiscreteTopology Γ] (hΓclosed : IsClosed (Γ : Set W))
    (hspan : Submodule.span ℝ (Γ : Set W) ≠ ⊤)
    {E : W → W → ℝ} (hE : IsAlternatingCompatible E)
    (hEint : ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ n : ℤ, E x y = (n : ℝ))
    (hpsd : ∀ x : W, 0 ≤ altSym E x x)
    (hnd : ∀ x : W, x ≠ 0 → ∃ y, altSym E x y ≠ 0)
    (vertexClass : α → W) (hinc : ∀ v, vertexClass v ∈ Γ ↔ v ∉ Fs) :
    QuasiAbelianFacetCertificate α Fs where
  X := W ⧸ Γ
  W := W
  Gamma := Γ
  gammaClosed := hΓclosed
  quotientMap := QuotientAddGroup.mk' Γ
  quotientMap_surjective := QuotientAddGroup.mk'_surjective Γ
  quotientMap_eq_iff := by
    intro x y
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_iff_sub_mem]
  quotient_noncompact := not_isCompact_univ_quotient_of_span_ne_top Γ hspan
  vertexClass := vertexClass
  vertex_incidence := hinc
  H := hermitianOfAlternating E
  H_add_left := hE.hermitian_add_left
  H_smul_left := hE.hermitian_smul_left
  H_hermitian := hE.hermitian_symm
  H_positive := by
    intro x hx
    rw [hermitianOfAlternating_re]
    exact hE.altSym_pos_of_psd_of_nondegenerate hpsd hnd hx
  H_integral_imaginary := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [hermitianOfAlternating_im]
    obtain ⟨n, hn⟩ := hEint x hx y hy
    exact ⟨n, hn⟩

/-- **The certificate exists whenever the facet data does.**  Existence form, with every analytic
clause discharged. -/
theorem exists_certificateOfAlternating {α : Type*} [DecidableEq α] (Fs : Finset α)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℝ W]
    (Γ : AddSubgroup W) [DiscreteTopology Γ] (hΓclosed : IsClosed (Γ : Set W))
    (hspan : Submodule.span ℝ (Γ : Set W) ≠ ⊤)
    {E : W → W → ℝ} (hE : IsAlternatingCompatible E)
    (hEint : ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ n : ℤ, E x y = (n : ℝ))
    (hpsd : ∀ x : W, 0 ≤ altSym E x x)
    (hnd : ∀ x : W, x ≠ 0 → ∃ y, altSym E x y ≠ 0)
    (vertexClass : α → W) (hinc : ∀ v, vertexClass v ∈ Γ ↔ v ∉ Fs) :
    Nonempty (QuasiAbelianFacetCertificate α Fs) :=
  ⟨certificateOfAlternating Fs Γ hΓclosed hspan hE hEint hpsd hnd vertexClass hinc⟩

/-- **The lattice class of the constructed certificate is a quotient class.**  Two integral facet
exponents have the same class exactly when their difference lies in the period group, so the
injectivity clause of the palette becomes a concrete statement about `Gamma`. -/
theorem latticeClass_certificateOfAlternating_eq_iff {α : Type*} [DecidableEq α] (Fs : Finset α)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℝ W]
    (Γ : AddSubgroup W) [DiscreteTopology Γ] (hΓclosed : IsClosed (Γ : Set W))
    (hspan : Submodule.span ℝ (Γ : Set W) ≠ ⊤)
    {E : W → W → ℝ} (hE : IsAlternatingCompatible E)
    (hEint : ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ n : ℤ, E x y = (n : ℝ))
    (hpsd : ∀ x : W, 0 ≤ altSym E x x)
    (hnd : ∀ x : W, x ≠ 0 → ∃ y, altSym E x y ≠ 0)
    (vertexClass : α → W) (hinc : ∀ v, vertexClass v ∈ Γ ↔ v ∉ Fs) (n m : Fs → ℤ) :
    (certificateOfAlternating Fs Γ hΓclosed hspan hE hEint hpsd hnd vertexClass hinc).latticeClass n
        = (certificateOfAlternating Fs Γ hΓclosed hspan hE hEint hpsd hnd vertexClass
            hinc).latticeClass m
      ↔ (∑ v : Fs, (n v) • vertexClass v.1) - (∑ v : Fs, (m v) • vertexClass v.1) ∈ Γ := by
  show QuotientAddGroup.mk' Γ (∑ v : Fs, (n v) • vertexClass v.1)
      = QuotientAddGroup.mk' Γ (∑ v : Fs, (m v) • vertexClass v.1) ↔ _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]

/-- **Injectivity of the lattice class is all the palette input needs.**  Given a family of facet
certificates whose lattice classes are injective, the whole `QuasiAbelianFacetPaletteInput` is
constructed: the structural-shift clause follows because equal classes already force equal
exponents. -/
noncomputable def paletteInputOfCertificates {α : Type*} [Fintype α] [DecidableEq α]
    {facets : Finset (Finset α)} {omega : α → ℝ}
    (C : ∀ F : facets, QuasiAbelianFacetCertificate α F.1)
    (hinj : ∀ (F : facets) (n m : F.1 → ℤ),
      (C F).latticeClass n = (C F).latticeClass m → n = m) :
    QuasiAbelianFacetPaletteInput α facets omega where
  certificate := C
  latticeClass_eq_implies_shift_eq := by
    intro F n m h
    rw [hinj F n m h]

/-- A facet lattice meeting the period group only at the origin has an injective lattice class. -/
theorem latticeClass_injective_of_free {α : Type*} [DecidableEq α] (Fs : Finset α)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℝ W]
    (Γ : AddSubgroup W) [DiscreteTopology Γ] (hΓclosed : IsClosed (Γ : Set W))
    (hspan : Submodule.span ℝ (Γ : Set W) ≠ ⊤)
    {E : W → W → ℝ} (hE : IsAlternatingCompatible E)
    (hEint : ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ n : ℤ, E x y = (n : ℝ))
    (hpsd : ∀ x : W, 0 ≤ altSym E x x)
    (hnd : ∀ x : W, x ≠ 0 → ∃ y, altSym E x y ≠ 0)
    (vertexClass : α → W) (hinc : ∀ v, vertexClass v ∈ Γ ↔ v ∉ Fs)
    (hfree : ∀ k : Fs → ℤ, (∑ v : Fs, (k v) • vertexClass v.1) ∈ Γ → k = 0) (n m : Fs → ℤ)
    (h : (certificateOfAlternating Fs Γ hΓclosed hspan hE hEint hpsd hnd vertexClass
        hinc).latticeClass n
      = (certificateOfAlternating Fs Γ hΓclosed hspan hE hEint hpsd hnd vertexClass
        hinc).latticeClass m) :
    n = m := by
  rw [latticeClass_certificateOfAlternating_eq_iff] at h
  have hdiff : (∑ v : Fs, ((n - m) v) • vertexClass v.1)
      = (∑ v : Fs, (n v) • vertexClass v.1) - (∑ v : Fs, (m v) • vertexClass v.1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Pi.sub_apply, sub_zsmul]
    abel
  have hzero : (n - m) = 0 := hfree _ (by rw [hdiff]; exact h)
  funext v
  have := congrFun hzero v
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GaloisForLFunctions.HTGeometry
