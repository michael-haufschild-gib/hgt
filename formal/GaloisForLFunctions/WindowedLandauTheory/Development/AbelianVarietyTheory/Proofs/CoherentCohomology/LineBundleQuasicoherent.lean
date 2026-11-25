import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.QuasicoherenceOnAffines

/-! Basic-open localization of sections in a line-bundle trivialization. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {L : LB X}

private theorem basicOpen_localization (hL : L.IsLB) (j : L.ι)
    {U : X.Opens} (hU : IsAffineOpen U) (hle : U ≤ L.U j) (f : Γ(X, U)) :
    HasBasicOpenLocalization (toMod L) U f := by
  let V := X.basicOpen f
  let i : V ⟶ U := homOfLE (X.basicOpen_le f)
  let r := resG X (X.basicOpen_le f)
  let eU := chartEquiv hL j hle
  let eV := chartEquiv hL j ((X.basicOpen_le f).trans hle)
  have he (t : Γ(toMod L, U)) : eV ((toMod L).presheaf.map i.op t) = r (eU t) :=
    chartEquiv_map hL j hle (X.basicOpen_le f) t
  letI := hU.isLocalization_basicOpen f
  constructor
  · intro t
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (Submonoid.powers f) (eV t)
    obtain ⟨n, hn⟩ := d.2
    have hmul : r f ^ n * eV t = r a := by
      change eV t * r d.1 = r a at hd
      rw [← hn, map_pow, mul_comm] at hd
      exact hd
    refine ⟨n, eU.symm a, eV.injective ?_⟩
    change eV ((r f) ^ n • t) = eV ((toMod L).presheaf.map i.op (eU.symm a))
    rw [eV.map_smul, he, eU.apply_symm_apply, smul_eq_mul, hmul]
  · intro t ht
    have hz : r (eU t) = 0 := (he t).symm.trans (by rw [ht, map_zero])
    obtain ⟨d, hd⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Γ(X, V)
      (eU t)).mp hz
    obtain ⟨n, hn⟩ := d.2
    refine ⟨n, eU.injective ?_⟩
    rw [eU.map_smul, eU.map_zero, smul_eq_mul]
    exact (congrArg (fun a : Γ(X, U) => a * eU t) hn).trans hd

/-- The affine refinements of the trivializing cover give quasi-coherence. -/
theorem isQuasicoherent_toMod (hL : L.IsLB) : (toMod L).IsQuasicoherent := by
  let I := {i : L.ι × X.affineOpens // (i.2 : X.Opens) ≤ L.U i.1}
  let U (i : I) : X.Opens := i.1.2
  have hcov : IsOpenCover U := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ j, L.U j := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVj⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hj (L.U j).isOpen
    exact Opens.mem_iSup.mpr ⟨⟨(j, ⟨V, hV⟩), hVj⟩, hxV⟩
  exact isQuasicoherent_of_affineCover_localization (toMod L) U hcov
    (fun i => i.1.2.2) (fun i => basicOpen_localization hL i.1.1 i.1.2.2 i.2)

end GlobalTheory.LineBundleSections
