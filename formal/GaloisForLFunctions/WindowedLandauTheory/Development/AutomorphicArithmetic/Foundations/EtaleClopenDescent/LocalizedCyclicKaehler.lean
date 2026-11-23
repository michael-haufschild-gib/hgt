import Mathlib.RingTheory.Etale.Kaehler
import GaloisForLFunctions.HTGeometry.AnnihilatorLocalization

/-! Localizing a monogenic algebra preserves the cyclic generator of its
relative differentials. -/

noncomputable section

open KaehlerDifferential

namespace GlobalTheory.PD

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- The differential of the monogenic generator spans the relative
Kähler module after localization. -/
theorem kaehler_toSpanSingleton_surjective_of_localization
    (S : Submonoid B) [IsLocalization S C] (b : B)
    (hb : Algebra.adjoin R ({b} : Set B) = ⊤) :
    Function.Surjective (LinearMap.toSpanSingleton C Ω[C⁄R] (D R C (algebraMap B C b))) := by
  let M := Submodule.span C ({D R C (algebraMap B C b)} : Set Ω[C⁄R])
  have hD (x : B) (hx : x ∈ Algebra.adjoin R ({b} : Set B)) :
      D R C (algebraMap B C x) ∈ M := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain rfl : x = b := Set.mem_singleton_iff.mp hx
      exact Submodule.mem_span_singleton_self _
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply R B C, Derivation.map_algebraMap]
      exact zero_mem _
    | add x y _ _ hx hy =>
      simpa only [map_add] using add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul, Derivation.leibniz]
      exact add_mem (M.smul_mem _ hy) (M.smul_mem _ hx)
  have hM : (⊤ : Submodule C Ω[C⁄R]) ≤ M := by
    rw [← span_range_map_derivation_of_isLocalization R B C S]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    change KaehlerDifferential.map R R B C (D R B x) ∈ M
    rw [KaehlerDifferential.map_D]
    exact hD x (by rw [hb]; trivial)
  intro ω
  exact Submodule.mem_span_singleton.mp (hM (Submodule.mem_top : ω ∈ ⊤))

/-- The annihilator of finite relative differentials extends to the
annihilator after localization. -/
theorem map_kaehler_annihilator_of_localization
    (S : Submonoid B) [IsLocalization S C] [Module.Finite B Ω[B⁄R]] :
    (Module.annihilator B Ω[B⁄R]).map (algebraMap B C) = Module.annihilator C Ω[C⁄R] := by
  let f := KaehlerDifferential.map R R B C
  letI : IsLocalizedModule S f := KaehlerDifferential.isLocalizedModule_map R B C S
  refine le_antisymm ?_ (GaloisForLFunctions.HTGeometry.annihilator_le_map_annihilator_of_isLocalizedModule S C f)
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  apply Module.mem_annihilator.mpr
  intro ω
  obtain ⟨⟨u, r⟩, hr⟩ := IsLocalizedModule.surj S f ω
  apply IsLocalizedModule.smul_injective f r
  calc
    r • (algebraMap B C b • ω) = algebraMap B C b • (r • ω) := by
      change (r : B) • (algebraMap B C b • ω) = algebraMap B C b • ((r : B) • ω)
      exact smul_comm (r : B) (algebraMap B C b) ω
    _ = f (b • u) := by rw [hr, map_smul, IsScalarTower.algebraMap_smul]
    _ = r • 0 := by rw [Module.mem_annihilator.mp hb u, map_zero, smul_zero]

end GlobalTheory.PD
