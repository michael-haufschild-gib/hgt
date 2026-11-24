import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorFactorLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FlatRegularSequence
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Ideal

/-! The equations of an affine diagonal retain weak regularity and
generate the diagonal ideal after localization on either side. -/

noncomputable section

open scoped TensorProduct
open RingTheory.Sequence

namespace GlobalTheory.PD

variable {k A B C L : Type} [CommRing k] [CommRing A] [CommRing B] [CommRing C] [CommRing L]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k L]
  [Algebra A B] [Algebra A C] [Algebra A L] [Algebra B L] [Algebra C L]
  [IsScalarTower k A B] [IsScalarTower k A C] [IsScalarTower k A L]
  [IsScalarTower k B L] [IsScalarTower k C L] [IsScalarTower A B L] [IsScalarTower A C L]

private theorem ker_eq_map_ker_of_localization {R S D : Type*}
    [CommRing R] [CommRing S] [CommRing D] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (f : S →+* D) :
    RingHom.ker f = (RingHom.ker (f.comp (algebraMap R S))).map (algebraMap R S) := by
  rw [← RingHom.comap_ker]
  exact (IsLocalization.map_under M S (RingHom.ker f)).symm

/-- Subtract the two images of an affine coordinate in the tensor product. -/
def diagonalDifference (B₀ C₀ : Type) [CommRing B₀] [CommRing C₀]
    [Algebra k B₀] [Algebra k C₀] [Algebra A B₀] [Algebra A C₀] (a : A) :
    B₀ ⊗[k] C₀ :=
  algebraMap A B₀ a ⊗ₜ[k] (1 : C₀) - (1 : B₀) ⊗ₜ[k] algebraMap A C₀ a

/-- Multiply the images of two affine chart rings in their common function field. -/
def tensorChartRestriction (B₀ C₀ : Type) [CommRing B₀] [CommRing C₀]
    [Algebra k B₀] [Algebra k C₀] [Algebra B₀ L] [Algebra C₀ L]
    [IsScalarTower k B₀ L] [IsScalarTower k C₀ L] : B₀ ⊗[k] C₀ →ₐ[k] L :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k B₀ L) (IsScalarTower.toAlgHom k C₀ L)
    (fun _ _ => Commute.all _ _)

theorem tensorChartRestriction_tmul (B₀ C₀ : Type) [CommRing B₀] [CommRing C₀]
    [Algebra k B₀] [Algebra k C₀] [Algebra B₀ L] [Algebra C₀ L]
    [IsScalarTower k B₀ L] [IsScalarTower k C₀ L] (b : B₀) (c : C₀) :
    tensorChartRestriction (k := k) B₀ C₀ (b ⊗ₜ[k] c) =
      algebraMap B₀ L b * algebraMap C₀ L c := by
  simp [tensorChartRestriction]

/-- Transport both weak regularity and the diagonal ideal from a common
affine chart to two of its localizations. -/
theorem localized_tensor_diagonal {d : ℕ} (u : Fin d → A)
    (hreg : IsWeaklyRegular (A ⊗[k] A) (List.ofFn fun i => diagonalDifference (k := k) A A (u i)))
    (hker : RingHom.ker (Algebra.TensorProduct.lmul' k (S := A)).toRingHom =
      Ideal.span (Set.range fun i => diagonalDifference (k := k) A A (u i)))
    (hinj : Function.Injective (algebraMap A L))
    (S T : Submonoid A) [IsLocalization S B] [IsLocalization T C] :
    IsWeaklyRegular (B ⊗[k] C) (List.ofFn fun i => diagonalDifference (k := k) B C (u i)) ∧
    RingHom.ker (tensorChartRestriction (k := k) (L := L) B C).toRingHom =
      Ideal.span (Set.range fun i => diagonalDifference (k := k) B C (u i)) := by
  let X := A ⊗[k] A
  let Y := B ⊗[k] A
  let Z := B ⊗[k] C
  letI : Algebra X Y := tensorLeftChangeAlgebra
  letI : Algebra Y Z := tensorRightChangeAlgebra
  let U := Algebra.algebraMapSubmonoid X S
  let V := T.map (Algebra.TensorProduct.includeRight (R := k) (A := B))
  letI : IsLocalization U Y := isLocalization_tensorLeft S
  letI : IsLocalization V Z := isLocalization_tensorRight T
  have h₁ (a : A) : algebraMap X Y (diagonalDifference (k := k) A A a) =
      diagonalDifference (k := k) B A a := by
    change Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k A)
      (diagonalDifference (k := k) A A a) = diagonalDifference (k := k) B A a
    simp [diagonalDifference, Algebra.TensorProduct.map_tmul]
  have h₂ (a : A) : algebraMap Y Z (diagonalDifference (k := k) B A a) =
      diagonalDifference (k := k) B C a := by
    change Algebra.TensorProduct.map (AlgHom.id k B) (IsScalarTower.toAlgHom k A C)
      (diagonalDifference (k := k) B A a) = diagonalDifference (k := k) B C a
    simp [diagonalDifference, Algebra.TensorProduct.map_tmul]
  letI : Module.Flat X Y := IsLocalization.flat Y U
  letI : Module.Flat Y Z := IsLocalization.flat Z V
  have hseq₁ : (List.ofFn fun i => diagonalDifference (k := k) A A (u i)).map
      (algebraMap X Y) = List.ofFn (fun i => diagonalDifference (k := k) B A (u i)) := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => h₁ (u i))
  have hseq₂ : (List.ofFn fun i => diagonalDifference (k := k) B A (u i)).map
      (algebraMap Y Z) = List.ofFn (fun i => diagonalDifference (k := k) B C (u i)) := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => h₂ (u i))
  have hr₁ : IsWeaklyRegular Y (List.ofFn fun i => diagonalDifference (k := k) B A (u i)) :=
    hseq₁ ▸ weaklyRegular_map_of_flat (B := Y) hreg
  refine ⟨hseq₂ ▸ weaklyRegular_map_of_flat (B := Z) hr₁, ?_⟩
  let f : X →ₐ[k] Y := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k A)
  let g : Y →ₐ[k] Z := Algebra.TensorProduct.map (AlgHom.id k B) (IsScalarTower.toAlgHom k A C)
  let m₁ : Y →ₐ[k] L := tensorChartRestriction B A
  let m₂ : Z →ₐ[k] L := tensorChartRestriction B C
  let m₀ : X →ₐ[k] A := Algebra.TensorProduct.lmul' k
  have e₁ : m₁.comp f = (IsScalarTower.toAlgHom k A L).comp m₀ := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change m₁ (f (a ⊗ₜ[k] b)) = algebraMap A L (m₀ (a ⊗ₜ[k] b))
    rw [show f (a ⊗ₜ[k] b) = algebraMap A B a ⊗ₜ[k] b from
      Algebra.TensorProduct.map_tmul _ _ _ _]
    change tensorChartRestriction (k := k) B A (algebraMap A B a ⊗ₜ[k] b) = _
    rw [tensorChartRestriction_tmul, ← IsScalarTower.algebraMap_apply A B L]
    have hm : m₀ (a ⊗ₜ[k] b) = a * b :=
      Algebra.TensorProduct.lmul'_apply_tmul (R := k) (S := A) a b
    rw [hm]
    exact (map_mul (algebraMap A L) a b).symm
  have e₂ : m₂.comp g = m₁ := by
    apply Algebra.TensorProduct.ext'
    intro b a
    change m₂ (g (b ⊗ₜ[k] a)) = m₁ (b ⊗ₜ[k] a)
    rw [show g (b ⊗ₜ[k] a) = b ⊗ₜ[k] algebraMap A C a from
      Algebra.TensorProduct.map_tmul _ _ _ _]
    change tensorChartRestriction (k := k) B C (b ⊗ₜ[k] algebraMap A C a) =
      tensorChartRestriction (k := k) B A (b ⊗ₜ[k] a)
    rw [tensorChartRestriction_tmul, tensorChartRestriction_tmul, ← IsScalarTower.algebraMap_apply A C L]
  have hk₁ : RingHom.ker m₁.toRingHom =
      Ideal.span (Set.range fun i => diagonalDifference (k := k) B A (u i)) := by
    rw [ker_eq_map_ker_of_localization U, show m₁.toRingHom.comp (algebraMap X Y) =
      (algebraMap A L).comp m₀.toRingHom from congrArg AlgHom.toRingHom e₁,
      RingHom.ker_comp_of_injective _ hinj, hker, Ideal.map_span, ← Set.range_comp']
    change Ideal.span (Set.range (fun i : Fin d => algebraMap X Y
      (diagonalDifference (k := k) A A (u i)))) = _
    rw [show (fun i : Fin d => algebraMap X Y (diagonalDifference (k := k) A A (u i))) =
      (fun i => diagonalDifference (k := k) B A (u i)) from funext (fun i => h₁ (u i))]
  change RingHom.ker m₂.toRingHom = _
  rw [ker_eq_map_ker_of_localization V, show m₂.toRingHom.comp (algebraMap Y Z) =
    m₁.toRingHom from congrArg AlgHom.toRingHom e₂, hk₁, Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range (fun i : Fin d => algebraMap Y Z
    (diagonalDifference (k := k) B A (u i)))) = _
  rw [show (fun i : Fin d => algebraMap Y Z (diagonalDifference (k := k) B A (u i))) =
    (fun i => diagonalDifference (k := k) B C (u i)) from funext (fun i => h₂ (u i))]

end GlobalTheory.PD
