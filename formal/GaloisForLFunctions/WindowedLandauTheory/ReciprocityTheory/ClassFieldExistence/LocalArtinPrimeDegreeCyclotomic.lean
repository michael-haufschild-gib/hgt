import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinPrimeDegreeBaseChange
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrimeCyclotomicDescentField

/-! Adjoining the roots of unity needed in prime degree costs at most
p - 1 degrees. Forming the compositum provides a small base change
for the local Artin map. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Module
open scoped IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K A : Type} [Field K] [NumberField K] [Field A] [NumberField A]
  [Algebra K A] [IsAbelianGalois K A]

theorem finiteIdelicArtin_surjective_at_full_decomposition_of_prime_degree
    {p : ℕ} (hp : p.Prime) (hA : finrank K A = p)
    (g : IdeleGroup K →* Gal(A/K)) (hg : IsFiniteIdelicArtin g)
    (hd : ∀ a : Kˣ, g (diagonal K a) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 A)) [w.asIdeal.LiesOver v.asIdeal]
    (hw : MulAction.stabilizer Gal(A/K) w.asIdeal = ⊤) :
    Function.Surjective (g.comp (finiteEmbedding v)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  let Ω := AlgebraicClosure K
  let C := CyclotomicField p K
  letI : IsGalois K C := IsCyclotomicExtension.isGalois {p} K C
  letI : IsCyclic Gal(C/K) := primeCyclotomicField_isCyclic K p hp
  letI : CommGroup Gal(C/K) := IsCyclic.commGroup
  letI : IsAbelianGalois K C := { is_comm.comm := fun x y => mul_comm x y }
  letI : HasEnoughRootsOfUnity C p := primeCyclotomicField_hasEnoughRootsOfUnity K p hp
  let α : A →ₐ[K] Ω := IsAlgClosed.lift
  let β : C →ₐ[K] Ω := IsAlgClosed.lift
  let A' := α.fieldRange
  let B := β.fieldRange
  let M := A' ⊔ B
  let e := β.equivFieldRange
  letI : FiniteDimensional K A' :=
    FiniteDimensional.of_injective α.equivFieldRange.symm.toLinearMap α.equivFieldRange.symm.injective
  letI : FiniteDimensional K B := FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  letI : IsAbelianGalois K A' := IsAbelianGalois.of_algHom α.equivFieldRange.symm.toAlgHom
  letI : IsAbelianGalois K B := IsAbelianGalois.of_algHom e.symm.toAlgHom
  letI : IsAbelianGalois K M := isAbelianGalois_of_le_maximalAbelianExtension M
    (sup_le (le_maximalAbelianExtension A') (le_maximalAbelianExtension B))
  letI : NumberField B := NumberField.of_module_finite K B
  letI : NumberField M := NumberField.of_module_finite K M
  let a := (IntermediateField.inclusion (show A' ≤ M from le_sup_left)).comp
    α.equivFieldRange.toAlgHom
  let b := IntermediateField.inclusion (show B ≤ M from le_sup_right)
  letI : Algebra A M := a.toRingHom.toAlgebra
  letI : Algebra B M := b.toRingHom.toAlgebra
  letI : Module.Free B M := Module.Free.of_divisionRing B M
  letI : IsScalarTower K A M := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  letI : IsScalarTower K B M := IsScalarTower.of_algebraMap_eq' b.comp_algebraMap.symm
  letI : IsAbelianGalois B M := IsAbelianGalois.tower_top K B M
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  letI : HasEnoughRootsOfUnity B p :=
    ⟨⟨e ζ, hζ.map_of_injective e.injective⟩, rootsOfUnity.isCyclic B p⟩
  have hB : finrank K B < p := by
    have he := e.toLinearEquiv.finrank_eq
    rw [← he, ← IsGalois.card_aut_eq_finrank K C]
    have h := Nat.card_le_card_of_injective (hζ.autToPow K) (hζ.autToPow_injective K)
    rw [Nat.card_eq_fintype_card (α := (ZMod p)ˣ), ZMod.card_units_eq_totient, Nat.totient_prime hp] at h
    exact h.trans_lt (Nat.sub_lt hp.pos Nat.one_pos)
  have hM : finrank B M ≤ p := by
    have h := IntermediateField.finrank_sup_le A' B
    have hA' : finrank K A' = p := α.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans hA
    rw [← finrank_mul_finrank K B M, hA', mul_comm p (finrank K B)] at h
    exact Nat.le_of_mul_le_mul_left h Module.finrank_pos
  exact finiteIdelicArtin_surjective_at_full_decomposition_of_prime_degree_baseChange
    K A B M hA hB hM g hg hd v w hw

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_surjective_at_full_decomposition_of_prime_degree
