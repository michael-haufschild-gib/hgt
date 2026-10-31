import GaloisForLFunctions.HeckeKreinToeplitz.Index.IsotropicSubspaces
import GaloisForLFunctions.BiarithmeticGeometry.Affine.RationalCharacters
import GaloisForLFunctions.HTGeometry.FiniteCommutingFamiliesHaveCommonEigenvectors
import GaloisForLFunctions.ArithmeticPositiveDuality.ArchimedeanEigenvectorsAreInvisibleToTranslations
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Unipotence of isotropic rational translation subspaces

A nontrivial joint translation character would have arbitrarily many independent,
mutually isotropic dilation images, contradicting finite negative index. Every
isotropic invariant subspace is finite-dimensional, so its translation operators
have only eigenvalue one and are unipotent with the dimensional exponent.
-/

open Complex Module
open scoped ComplexConjugate
open GaloisForLFunctions.HeckeKreinToeplitz GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem joint_eigenvectors_linearIndependent {V ι J : Type*}
    [AddCommGroup V] [Module ℂ V] (f : ι → End ℂ V)
    (hcomm : ∀ i j, Commute (f i) (f j)) (χ : J → ι → ℂ)
    (hχ : Function.Injective χ) (v : J → V) (hv : ∀ j, v j ≠ 0)
    (he : ∀ j i, f i (v j) = χ j i • v j) : LinearIndependent ℂ v := by
  let P (ψ : ι → ℂ) : Submodule ℂ V := ⨅ i, (f i).maxGenEigenspace (ψ i)
  have hP : iSupIndep P :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j z => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) z)
  apply iSupIndep.linearIndependent (fun j => P (χ j)) (hP.comp hχ) _ hv
  intro j
  apply (Submodule.mem_iInf _).mpr
  intro i
  exact Module.End.eigenspace_le_maxGenEigenspace
    (Module.End.mem_eigenspace_iff.mpr (he j i))

private theorem pow_sub_one_eq_zero_of_eigenvalue_one {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : End ℂ V) (he : ∀ μ, T.HasEigenvalue μ → μ = 1) :
    (T - 1) ^ Module.finrank ℂ V = 0 := by
  have htop : (⊤ : Submodule ℂ V) ≤ T.maxGenEigenspace 1 := by
    rw [← T.iSup_maxGenEigenspace_eq_top]
    apply iSup_le
    intro μ
    by_cases hμ : T.maxGenEigenspace μ = ⊥
    · rw [hμ]
      exact bot_le
    · have hgen : T.HasGenEigenvalue μ (Module.finrank ℂ V) := by
        rwa [Module.End.maxGenEigenspace_eq_genEigenspace_finrank] at hμ
      rw [he μ (Module.End.hasEigenvalue_of_hasGenEigenvalue hgen)]
  ext x
  have hx := htop (show x ∈ (⊤ : Submodule ℂ V) from trivial)
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.genEigenspace_nat, LinearMap.mem_ker] at hx
  simpa only [one_smul, LinearMap.zero_apply] using hx

private theorem column_translation_commute (k : AffineGroupQ → ℂ) (a b : ℚ) :
    Commute (kernelColumnRepresentation k (translation a))
      (kernelColumnRepresentation k (translation b)) := by
  change kernelColumnRepresentation k (translation a) *
      kernelColumnRepresentation k (translation b) = _
  rw [← map_mul, ← map_mul, ← translation_add, ← translation_add, add_comm]

/-- An isotropic common translation eigenvector has the trivial character. -/
theorem isotropic_translation_eigencharacter_eq_one {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (v : kernelColumnSpan k) (hv : v ≠ 0) (hvv : kernelColumnPairing k v v = 0)
    (χ : ℚ → ℂ) (he : ∀ b, kernelColumnRepresentation k (translation b) v = χ b • v) :
    ∀ b, χ b = 1 := by
  classical
  let ρ := kernelColumnRepresentation k
  have h0 : χ 0 = 1 := by
    apply smul_left_injective ℂ hv
    simpa only [translation_zero, map_one, Module.End.one_apply, one_smul] using (he 0).symm
  have ha (a b : ℚ) : χ (a + b) = χ a * χ b := by
    apply smul_left_injective ℂ hv
    change χ (a + b) • v = (χ a * χ b) • v
    rw [← he, translation_add, map_mul]
    change ρ (translation a) (ρ (translation b) v) = (χ a * χ b) • v
    rw [he b, map_smul, he a, smul_smul, mul_comm]
  by_contra hχ
  obtain ⟨b₀, hb₀⟩ := not_forall.mp hχ
  let q (i : Fin (r + 1)) : ℚ := (i : ℕ) + 1
  have hqpos (i : Fin (r + 1)) : 0 < q i := by dsimp only [q]; positivity
  have hqne (i : Fin (r + 1)) : q i ≠ 0 := (hqpos i).ne'
  have hqinj : Function.Injective q := by
    intro i j hij
    apply Fin.ext
    have hcast : (i.val : ℚ) = (j.val : ℚ) := add_right_cancel hij
    exact_mod_cast hcast
  let u (i : Fin (r + 1)) : ℚˣ := Units.mk0 (q i) (hqne i)
  let w (i : Fin (r + 1)) := ρ (dilation (u i)) v
  let ψ (i : Fin (r + 1)) (b : ℚ) := χ (b / q i)
  have hundo (g : AffineGroupQ) (z : kernelColumnSpan k) : ρ g⁻¹ (ρ g z) = z := by
    change (ρ g⁻¹ * ρ g) z = z
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hw (i : Fin (r + 1)) : w i ≠ 0 := by
    intro hz
    have heq := congrArg (ρ (dilation (u i))⁻¹) hz
    rw [map_zero] at heq
    exact hv ((hundo (dilation (u i)) v).symm.trans heq)
  have hew (i : Fin (r + 1)) (b : ℚ) : ρ (translation b) (w i) = ψ i b • w i := by
    have hb : q i * (b / q i) = b := by field_simp [hqne i]
    have hg : translation b * dilation (u i) = dilation (u i) * translation (b / q i) := by
      simpa only [u, Units.val_mk0, hb] using translation_mul_dilation (u i) (b / q i)
    change (ρ (translation b) * ρ (dilation (u i))) v = ψ i b • w i
    rw [← map_mul, hg, map_mul]
    change ρ (dilation (u i)) (ρ (translation (b / q i)) v) = _
    rw [he, map_smul]
  have hdiv (i j : Fin (r + 1)) (t : ℚ) : (q i * q j * t) / q i = q j * t := by
    field_simp [hqne i]
  have hψinj : Function.Injective ψ := by
    intro i j hij
    by_contra hne
    have hqi : q j ≠ q i := fun h => hne (hqinj h.symm)
    have hs (t : ℚ) : χ (q j * t) = χ (q i * t) := by
      have ht := congrFun hij (q i * q j * t)
      change χ ((q i * q j * t) / q i) = χ ((q i * q j * t) / q j) at ht
      rw [hdiv] at ht
      have hd : (q i * q j * t) / q j = q i * t := by field_simp [hqne j]
      rwa [hd] at ht
    exact hb₀ (rational_character_eq_one_of_rescaling χ h0 ha hqi hs b₀)
  have hpair (i j : Fin (r + 1)) : kernelColumnPairing k (w i) (w j) = 0 := by
    by_cases hij : i = j
    · subst j
      exact (kernelColumnPairing_invariant hk (dilation (u i)) v v).trans hvv
    · by_contra hp
      have hsq : (q j) ^ 2 ≠ (q i) ^ 2 := by
        intro hs
        have heq : q j = q i := by nlinarith only [hs, hqpos i, hqpos j]
        exact hij (hqinj heq.symm)
      have hs (t : ℚ) : conj (χ (q j * t)) * χ (q i * t) = 1 := by
        have hB := kernelColumnPairing_invariant hk (translation (q i * q j * t)) (w i) (w j)
        rw [hew, hew, kernelColumnPairing_smul_left hk, map_smul, smul_eq_mul] at hB
        have hd : (q i * q j * t) / q j = q i * t := by field_simp [hqne j]
        change conj (χ ((q i * q j * t) / q i)) *
          (χ ((q i * q j * t) / q j) * kernelColumnPairing k (w i) (w j)) = _ at hB
        rw [hdiv, hd] at hB
        apply mul_right_cancel₀ hp
        simpa only [mul_assoc, one_mul] using hB
      exact hb₀ (rational_character_eq_one_of_conjugate_rescaling χ h0 ha hsq hs b₀)
  have hind : LinearIndependent ℂ w := joint_eigenvectors_linearIndependent
    (fun b => ρ (translation b)) (column_translation_commute k) ψ hψinj w hw hew
  let W := Submodule.span ℂ (Set.range w)
  have hbase (i : Fin (r + 1)) : W ≤ LinearMap.ker (kernelColumnPairing k (w i)) := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact hpair i j
  have hW (x : kernelColumnSpan k) (hx : x ∈ W) (z : kernelColumnSpan k) (hz : z ∈ W) :
      kernelColumnPairing k x z = 0 := by
    have hker : W ≤ LinearMap.ker (kernelColumnPairing k z) := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      change kernelColumnPairing k z (w i) = 0
      rw [kernelColumnPairing_conj_symm hk, show kernelColumnPairing k (w i) z = 0 from hbase i hz,
        map_zero]
    rw [kernelColumnPairing_conj_symm hk, show kernelColumnPairing k z x = 0 from hker hx,
      map_zero]
  have hdim := (finite_isotropic_column_subspace hk hi W hW).2
  change Module.finrank ℂ (Submodule.span ℂ (Set.range w)) ≤ r at hdim
  rw [finrank_span_eq_card hind, Fintype.card_fin] at hdim
  omega

/-- Rational translations restricted to an invariant column subspace. -/
def isotropicTranslationAction (k : AffineGroupQ → ℂ)
    (W : Submodule ℂ (kernelColumnSpan k))
    (hW : ∀ b, Set.MapsTo (kernelColumnRepresentation k (translation b)) W W)
    (b : ℚ) : End ℂ W := (kernelColumnRepresentation k (translation b)).restrict (hW b)

local instance (k : AffineGroupQ → ℂ) (W : Submodule ℂ (kernelColumnSpan k)) :
    AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ

/-- On an isotropic invariant subspace, translations are unipotent with the dimensional exponent. -/
theorem isotropic_translation_unipotent {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r) (W : Submodule ℂ (kernelColumnSpan k))
    (hnull : ∀ v ∈ W, ∀ z ∈ W, kernelColumnPairing k v z = 0)
    (hW : ∀ b, Set.MapsTo (kernelColumnRepresentation k (translation b)) W W)
    (b : ℚ) : (isotropicTranslationAction k W hW b - (1 : End ℂ W)) ^ Module.finrank ℂ W = 0 := by
  letI := (finite_isotropic_column_subspace hk hi W hnull).1
  let T := isotropicTranslationAction k W hW
  have hcomm (a c : ℚ) : Commute (T a) (T c) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (column_translation_commute k a c).eq x
  apply pow_sub_one_eq_zero_of_eigenvalue_one
  intro μ hμ
  let E := (T b).eigenspace μ
  letI : AddCommGroup E := Module.addCommMonoidToAddCommGroup ℂ
  letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hμ
  have hE (a : ℚ) : Set.MapsTo (T a) E E := by
    intro x hx
    apply Module.End.mem_eigenspace_iff.mpr
    calc
      T b (T a x) = T a (T b x) := LinearMap.congr_fun (hcomm b a).eq x
      _ = μ • T a x := by rw [Module.End.mem_eigenspace_iff.mp hx, map_smul]
  let S (a : ℚ) : End ℂ E := (T a).restrict (hE a)
  have hS (a c : ℚ) : Commute (S a) (S c) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (hcomm a c).eq x
  obtain ⟨x, χ, hx, he⟩ := exists_common_eigenvector_family S hS
  have hxW : (x : W) ≠ 0 := fun h => hx (Subtype.ext h)
  have hxV : ((x : W) : kernelColumnSpan k) ≠ 0 := fun h => hxW (Subtype.ext h)
  have heV (a : ℚ) : kernelColumnRepresentation k (translation a) (x : W) = χ a • (x : W) :=
    congrArg (fun y : E => ((y : W) : kernelColumnSpan k)) (he a)
  have hχ := isotropic_translation_eigencharacter_eq_one hk hi (x : W) hxV
    (hnull x (x : W).property x (x : W).property) χ heV
  have hb : T b (x : W) = μ • (x : W) := Module.End.mem_eigenspace_iff.mp x.property
  have hb' : T b (x : W) = χ b • (x : W) := congrArg Subtype.val (he b)
  have heq : μ = χ b := smul_left_injective ℂ hxW (hb.symm.trans hb')
  exact heq.trans (hχ b)

/-- The difference between translation and identity on the full column space. -/
def translationColumnDifference (k : AffineGroupQ → ℂ) (b : ℚ) :
    End ℂ (kernelColumnSpan k) :=
  kernelColumnRepresentation k (translation b) + (-1 : ℂ) • 1

/-- The index bounds translation nilpotence on every isotropic invariant column subspace. -/
theorem isotropic_translation_difference_pow_apply {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (W : Submodule ℂ (kernelColumnSpan k))
    (hnull : ∀ v ∈ W, ∀ z ∈ W, kernelColumnPairing k v z = 0)
    (hW : ∀ b, Set.MapsTo (kernelColumnRepresentation k (translation b)) W W)
    (b : ℚ) (v : kernelColumnSpan k) (hv : v ∈ W) :
    (translationColumnDifference k b ^ r) v = 0 := by
  let T := isotropicTranslationAction k W hW b
  have hpow (n : ℕ) (x : W) :
      (((T - 1) ^ n) x : kernelColumnSpan k) =
        (translationColumnDifference k b ^ n) (x : kernelColumnSpan k) := by
    induction n with
    | zero => simp only [pow_zero, Module.End.one_apply]
    | succ n ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
        change ((T (((T - 1) ^ n) x) + (-1 : ℂ) • (((T - 1) ^ n) x) : W) :
            kernelColumnSpan k) = _
        rw [Submodule.coe_add, Submodule.coe_smul]
        change kernelColumnRepresentation k (translation b)
            ((((T - 1) ^ n) x : W) : kernelColumnSpan k) +
            (-1 : ℂ) • ((((T - 1) ^ n) x : W) : kernelColumnSpan k) = _
        rw [ih]
        rfl
  have hz : (T - 1) ^ r = 0 :=
    pow_eq_zero_of_le (finite_isotropic_column_subspace hk hi W hnull).2
      (isotropic_translation_unipotent hk hi W hnull hW b)
  have he := congrArg (fun A : End ℂ W => ((A ⟨v, hv⟩ : W) : kernelColumnSpan k)) hz
  change ((((T - 1) ^ r) ⟨v, hv⟩ : W) : kernelColumnSpan k) = 0 at he
  rwa [hpow] at he

#print axioms isotropic_translation_difference_pow_apply

#print axioms isotropic_translation_eigencharacter_eq_one
#print axioms isotropic_translation_unipotent
end GaloisForLFunctions.BiarithmeticGeometry
