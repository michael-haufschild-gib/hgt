import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistSections
import GaloisForLFunctions.HTGeometry.ProjTwistedComparison

/-! The degree-`-e` localized fractions identify the Čech terms of the projective twist. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry

namespace GlobalTheory.SchemeCohomology.ProjTwist

universe u

variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]
  {𝒜 : ℕ → Submodule K A} [GradedAlgebra 𝒜]
  {ι : Type*} [DecidableEq ι] {w : ι → A} (hw : ∀ i, w i ∈ 𝒜 1)

private theorem mem_awayDeg_iff {s : Finset ι} (hs : s.Nonempty) (e : ℕ) (z : LocAt w s) :
    z ∈ awayDeg 𝒜 (wProd_mem hw s) (Finset.card_pos.mpr hs) (-(e : ℤ)) ↔
      z ∈ twPart 𝒜 w s e := by
  rw [mem_twPart_iff hw hs]
  constructor
  · rintro ⟨m, i, a, ha, hdeg, rfl⟩
    refine ⟨m, i, a, ha, ?_, rfl⟩
    have h : ((i + e : ℕ) : ℤ) = ((m * s.card : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast h
  · rintro ⟨m, i, a, ha, hdeg, rfl⟩
    refine ⟨m, i, a, ha, ?_, rfl⟩
    have h : (i : ℤ) + e = (m : ℤ) * s.card := by exact_mod_cast hdeg
    omega

/-- On an intersection of coordinate opens, sections are the homogeneous localized fractions. -/
def twSections {s : Finset ι} (hs : s.Nonempty) (e : ℕ) :
    twPart 𝒜 w s e ≃+ Γ(twistingSheaf 𝒜 (-(e : ℤ)), Proj.basicOpen 𝒜 (wProd w s)) := by
  let h := mem_awayDeg_iff hw hs e
  let m : twPart 𝒜 w s e →+ awayDeg 𝒜 (wProd_mem hw s) (Finset.card_pos.mpr hs) (-(e : ℤ)) :=
    { toFun := fun z => ⟨z.1, (h z.1).2 z.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hm : Function.Bijective m :=
    ⟨fun _ _ eq => Subtype.ext (congrArg Subtype.val eq), fun z =>
      ⟨⟨z.1, (h z.1).1 z.2⟩, Subtype.ext rfl⟩⟩
  obtain ⟨i, hi⟩ := hs
  let t := s.erase i
  have heq := Finset.insert_erase hi
  have hf : wProd w s = w i * wProd w t := by
    conv_lhs => rw [← heq]
    exact Finset.prod_insert (Finset.notMem_erase i s)
  have hc : t.card + 1 = s.card := by
    rw [← Finset.card_insert_of_notMem (Finset.notMem_erase i s)]
    exact congrArg Finset.card heq
  have hb (d : ℕ) (hd : d = t.card + 1) (hf' : wProd w s ∈ 𝒜 d) :
      Function.Bijective (toSection hf' (show 0 < d by omega) (-(e : ℤ))) := by
    subst d
    exact toSection_bijective (hw i) (wProd_mem hw t) hf hf' _
  exact (AddEquiv.ofBijective m hm).trans
    (AddEquiv.ofBijective _ (hb s.card hc.symm (wProd_mem hw s)))

theorem twSections_val {s : Finset ι} (hs : s.Nonempty) (e : ℕ) (z : twPart 𝒜 w s e)
    (x : Proj.basicOpen 𝒜 (wProd w s)) :
    val (twSections hw hs e z) x = locMap x.1 (nmem_of_mem x) z.1 := rfl

private theorem basicOpen_wProd_le {s t : Finset ι} (h : s ⊆ t) :
    Proj.basicOpen 𝒜 (wProd w t) ≤ Proj.basicOpen 𝒜 (wProd w s) := by
  rw [wProd_eq_mul_sdiff h, Proj.basicOpen_mul]
  exact inf_le_left

/-- The localization maps in the Čech differential correspond to sheaf restriction. -/
theorem twSections_res {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty) (e : ℕ)
    (z : (twCech 𝒜 w hw e).obj s) :
    (twistingSheaf 𝒜 (-(e : ℤ))).presheaf.map
        (homOfLE (basicOpen_wProd_le h)).op (twSections hw hs e z) =
      twSections hw (hs.mono h) e ((twCech 𝒜 w hw e).res h z) := by
  ext x
  rw [val_res, twSections_val, twSections_val, twCech_res_val]
  exact (locMap_comp (resLoc w h) (RingHom.ext (resLoc_algebraMap w h)) x.1 _ _ z.1).symm

end GlobalTheory.SchemeCohomology.ProjTwist
