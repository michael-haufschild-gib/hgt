import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FixedFieldIdelicKernel

/-! A character factoring through a finite Artin map becomes faithful
on the Galois group of the fixed field of its kernel. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K M : Type} [Field K] [NumberField K] [Field M]
  [Algebra K M] [FiniteDimensional K M] [IsAbelianGalois K M] {A : Type*} [Group A]

local instance : CommGroup Gal(M/K) :=
  { (inferInstance : Group Gal(M/K)) with mul_comm := IsMulCommutative.is_comm.comm }

theorem exists_faithful_artin_factor_of_factor
    (φ : IdeleGroup K →* Gal(M/K)) (hφ : IsFiniteIdelicArtin φ)
    (hd : ∀ a : Kˣ, φ (diagonal K a) = 1) (ψ : Gal(M/K) →* A) :
    ∃ (L : IntermediateField K M) (hL : IsAbelianGalois K L), letI := hL
      ∃ (f : IdeleGroup K →* Gal(L/K)) (g : Gal(L/K) →* A),
        Continuous f ∧ Function.Surjective f ∧ IsFiniteIdelicArtin f ∧
        Function.Injective g ∧ g.comp f = ψ.comp φ := by
  letI : NumberField M := NumberField.of_module_finite K M
  letI : Fintype Gal(M/K) := Fintype.ofFinite _
  let θ := ψ.comp φ
  obtain ⟨m, hm, hp⟩ := hφ
  obtain ⟨L, hL, f, hf, hs, hk, ha⟩ := exists_finite_idelic_artin_of_kernel_le m φ hd
    (fun v hv => not_not.mp (fun hu => hv ((hm v).mpr hu))) hp θ.ker
    (fun x hx => MonoidHom.mem_ker.mpr (by rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]))
  let g := f.liftOfSurjective hs ⟨θ, hk.le⟩
  have hgf : g.comp f = θ :=
    f.liftOfRightInverse_comp _ (Function.rightInverse_surjInv hs) ⟨θ, hk.le⟩
  refine ⟨L, hL, f, g, hf, hs, ha, ?_, hgf⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨x, rfl⟩ := hs y
  change (g.comp f) x = 1 at hy
  rw [hgf] at hy
  exact MonoidHom.mem_ker.mp (hk.symm ▸ MonoidHom.mem_ker.mpr hy)

end GlobalTheory.Reciprocity
