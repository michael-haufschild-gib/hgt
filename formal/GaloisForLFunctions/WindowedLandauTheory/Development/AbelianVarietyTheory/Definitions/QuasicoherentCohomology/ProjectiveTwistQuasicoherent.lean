import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistTrivialization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.QuasicoherenceOnAffines

/-! On a coordinate chart, localization of a twist is localization of a free rank-one module. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology.ProjTwist

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

private theorem basicOpen_localization {v : A} (hv : v ∈ 𝒜 1) (k : ℤ)
    (f : Γ(Proj 𝒜, Proj.basicOpen 𝒜 v)) :
    HasBasicOpenLocalization (twistingSheaf 𝒜 k) (Proj.basicOpen 𝒜 v) f := by
  let X := Proj 𝒜
  let U := Proj.basicOpen 𝒜 v
  let T := twistingSheaf 𝒜 k
  let D := X.basicOpen f
  let i : D ⟶ U := homOfLE (X.basicOpen_le f)
  let b := coordinatePower hv k
  have hb := coordinatePower_basis hv k (X.basicOpen_le f)
  have hbU : Function.Bijective (fun r : Γ(X, U) => r • b) := by
    have h : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
    simpa only [h, T.presheaf.map_id, ConcreteCategory.id_apply] using
      coordinatePower_basis hv k (le_refl U)
  letI := (Proj.isAffineOpen_basicOpen 𝒜 v hv Nat.one_pos).isLocalization_basicOpen f
  have mul_loc (r : Γ(X, U)) : algebraMap Γ(X, U) Γ(X, D) r = X.presheaf.map i.op r := rfl
  constructor
  · intro s
    obtain ⟨c, rfl⟩ := hb.2 s
    obtain ⟨⟨r, d⟩, hd⟩ := IsLocalization.surj (Submonoid.powers f) c
    obtain ⟨n, hn⟩ := d.2
    have hmul : (X.presheaf.map i.op f) ^ n * c = X.presheaf.map i.op r := by
      change c * algebraMap Γ(X, U) Γ(X, D) d.1 = algebraMap Γ(X, U) Γ(X, D) r at hd
      rw [← hn, map_pow, mul_loc, mul_loc, mul_comm c] at hd
      exact hd
    refine ⟨n, r • b, ?_⟩
    change (X.presheaf.map i.op f) ^ n • (c • T.presheaf.map i.op b) =
      T.presheaf.map i.op (r • b)
    rw [smul_smul, hmul, T.map_smul i]
  · intro z hz
    obtain ⟨r, rfl⟩ := hbU.2 z
    have hr : algebraMap Γ(X, U) Γ(X, D) r = 0 := by
      rw [mul_loc]
      apply hb.1
      change (X.presheaf.map i.op r) • T.presheaf.map i.op b = (0 : Γ(X, D)) • T.presheaf.map i.op b
      rw [← T.map_smul i, zero_smul]
      exact hz
    obtain ⟨d, hd⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Γ(X, D) r).mp hr
    obtain ⟨n, hn⟩ := d.2
    refine ⟨n, ?_⟩
    rw [smul_smul, hn, hd, zero_smul]

/-- Degree-one coordinates covering Proj exhibit each twist as quasi-coherent. -/
theorem twistingSheaf_isQuasicoherent {ι : Type u} {v : ι → A} (hv : ∀ i, v i ∈ 𝒜 1)
    (hcov : ⨆ i, Proj.basicOpen 𝒜 (v i) = ⊤) (k : ℤ) :
    (twistingSheaf 𝒜 k).IsQuasicoherent :=
  isQuasicoherent_of_affineCover_localization (twistingSheaf 𝒜 k)
    (fun i => Proj.basicOpen 𝒜 (v i)) (.mk hcov)
    (fun i => Proj.isAffineOpen_basicOpen 𝒜 _ (hv i) Nat.one_pos)
    (fun i => basicOpen_localization (hv i) k)

end GlobalTheory.SchemeCohomology.ProjTwist
