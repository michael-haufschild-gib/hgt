import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectCochainModel

/-! A quasi-isomorphism identifies degree-zero kernels and reflects exactness in degree one. -/

noncomputable section

open CategoryTheory

namespace GlobalTheory

theorem bijOn_ker_and_exact_of_quasiIso {R : Type} [CommRing R]
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C) [QuasiIso φ] :
    Set.BijOn (φ.f 0).hom (LinearMap.ker (K.d 0 1).hom) (LinearMap.ker (C.d 0 1).hom) ∧
      (Function.Exact (C.d 0 1).hom (C.d 1 2).hom →
        Function.Exact (K.d 0 1).hom (K.d 1 2).hom) := by
  have h0 := (quasiIsoAt_zero_iff φ).1 inferInstance
  have h1 := (quasiIsoAt_succ_iff φ 0).1 inferInstance
  refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩,
    fun hex x => ⟨fun hx => ?_, ?_⟩⟩
  · change (K.d 0 1).hom x = 0 at hx
    change (C.d 0 1).hom ((φ.f 0).hom x) = 0
    rw [cochain_comm_apply, hx, map_zero]
  · change (K.d 0 1).hom x = 0 at hx
    change (K.d 0 1).hom y = 0 at hy
    exact sub_eq_zero.mp (h0.2 (x - y) (by rw [map_sub, hx, hy, sub_zero])
      (by rw [map_sub, hxy, sub_self]))
  · obtain ⟨x, hx, hφ⟩ := h0.1 y hy
    exact ⟨x, hx, hφ⟩
  · obtain ⟨z, hz⟩ := (hex ((φ.f 1).hom x)).mp (by rw [cochain_comm_apply, hx, map_zero])
    exact h1.2 x z hx hz
  · rintro ⟨y, rfl⟩
    exact cochain_d_d_apply K 0 1 2 y

end GlobalTheory
