import GaloisForLFunctions.HTGeometry.PermutationInvariantSubspace
import GaloisForLFunctions.HTGeometry.RootFamilyGalois
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.GaloisSpecialization

/-!
# A symmetric Galois group makes the spectrum rationally rigid

If the Galois group of a separable polynomial is as large as the symmetric group on its roots, then
every permutation of a labelled root family is realized by a field automorphism.  The rational
relation space of the roots is therefore invariant under every permutation of the labels, and a
permutation-invariant subspace containing the constants and not everything *is* the constants.  So
the only rational relation among the roots of a traceless such polynomial is the trace relation.

## Main results

* `exists_algEquiv_of_card_gal` — **a symmetric Galois group realizes every permutation.**
* `ratRelationForm` — the rational relation form of a family in a `ℚ`-algebra.
* `ker_ratRelationForm_eq_constLine` — **the relation space is exactly the trace line.**
* `exists_rigid_root_family` — the same, starting from a polynomial over `ℚ`.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **A symmetric Galois group realizes every permutation of a labelled root family.** -/
theorem exists_algEquiv_of_card_gal {p : Polynomial F}
    [Fact ((p.map (algebraMap F E)).Splits)] [Normal F E]
    {θ : ι → E} (hinj : Function.Injective θ)
    (hroots : p.map (algebraMap F E) = ∏ i, (X - C (θ i)))
    (hgal : Nat.card p.Gal = (Fintype.card ι).factorial) (π : Equiv.Perm ι) :
    ∃ σ : E ≃ₐ[F] E, ∀ i, σ (θ i) = θ (π i) := by
  classical
  have hrange := rootSet_eq_range_of_prod (E := E) hroots
  have hmemRoot : ∀ i, θ i ∈ p.rootSet E := by
    intro i
    rw [hrange]
    exact ⟨i, rfl⟩
  set ε : ι → p.rootSet E := fun i => ⟨θ i, hmemRoot i⟩ with hε
  have hεinj : Function.Injective ε := fun a b hab => hinj (congrArg Subtype.val hab)
  have hεsurj : Function.Surjective ε := by
    rintro ⟨x, hx⟩
    rw [hrange] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨i, rfl⟩
  set e : ι ≃ p.rootSet E := Equiv.ofBijective ε ⟨hεinj, hεsurj⟩ with he
  haveI : Fintype (p.rootSet E) := Fintype.ofEquiv ι e
  have hcard : Fintype.card (p.rootSet E) = Fintype.card ι := (Fintype.card_congr e).symm
  have hcardperm : Nat.card (Equiv.Perm (p.rootSet E)) = (Fintype.card ι).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcard]
  have hbij : Function.Bijective (Gal.galActionHom p E) := by
    refine (Nat.bijective_iff_injective_and_card _).mpr ⟨Gal.galActionHom_injective p E, ?_⟩
    rw [hgal, hcardperm]
  obtain ⟨ϕ, hϕ⟩ := hbij.2 (e.symm.trans (π.trans e))
  obtain ⟨σ, hσ⟩ := Gal.restrict_surjective (p := p) (E := E) ϕ
  refine ⟨σ, fun i => ?_⟩
  have hval : ((Gal.galActionHom p E ϕ (ε i) : p.rootSet E) : E) = σ (θ i) := by
    rw [← hσ, Gal.galActionHom_restrict]
  rw [hϕ] at hval
  have hτ : (e.symm.trans (π.trans e)) (ε i) = ε (π i) := by
    show e (π (e.symm (ε i))) = ε (π i)
    rw [show e.symm (ε i) = i from Equiv.ofBijective_symm_apply_apply _ _ i]
    rfl
  rw [hτ] at hval
  exact hval.symm

/-- The rational relation form of a family in a `ℚ`-algebra. -/
def ratRelationForm {K : Type*} [Field K] [Algebra ℚ K] (θ : ι → K) : (ι → ℚ) →ₗ[ℚ] K :=
  ∑ i, (LinearMap.proj i : (ι → ℚ) →ₗ[ℚ] ℚ).smulRight (θ i)

omit [DecidableEq ι] in
@[simp] theorem ratRelationForm_apply {K : Type*} [Field K] [Algebra ℚ K] (θ : ι → K)
    (a : ι → ℚ) : ratRelationForm θ a = ∑ i, (a i) • θ i := by
  simp [ratRelationForm, LinearMap.sum_apply]

omit [DecidableEq ι] in
theorem isPermInvariant_ker_ratRelationForm {K : Type*} [Field K] [Algebra ℚ K] (θ : ι → K)
    (hperm : ∀ π : Equiv.Perm ι, ∃ σ : K ≃ₐ[ℚ] K, ∀ i, σ (θ i) = θ (π i)) :
    PermSubspace.IsPermInvariant (LinearMap.ker (ratRelationForm θ)) := by
  classical
  intro π a ha
  rw [LinearMap.mem_ker, ratRelationForm_apply] at ha
  obtain ⟨σ, hσ⟩ := hperm π⁻¹
  have hzero : ∑ i, (a i) • θ (π⁻¹ i) = 0 := by
    have := congrArg σ ha
    rw [map_zero, map_sum] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hσ i]
  rw [LinearMap.mem_ker, ratRelationForm_apply]
  rw [← hzero]
  refine Fintype.sum_equiv π (fun j => (a (π j)) • θ j) (fun i => (a i) • θ (π⁻¹ i)) ?_
  intro j
  simp

/-- **The relation space of a rigid spectrum is exactly the trace line.** -/
theorem ker_ratRelationForm_eq_constLine {K : Type*} [Field K] [Algebra ℚ K] (θ : ι → K)
    (hinj : Function.Injective θ) (hcard : 1 < Fintype.card ι) (hsum : ∑ i, θ i = 0)
    (hperm : ∀ π : Equiv.Perm ι, ∃ σ : K ≃ₐ[ℚ] K, ∀ i, σ (θ i) = θ (π i)) :
    LinearMap.ker (ratRelationForm θ) = PermSubspace.constLine (K := ℚ) (ι := ι) := by
  classical
  refine PermSubspace.eq_constLine_of_le_of_ne_top _
    (isPermInvariant_ker_ratRelationForm θ hperm) ?_ ?_ ?_
  · intro hcon
    have : 0 < Fintype.card ι := by omega
    exact absurd (by exact_mod_cast hcon : (Fintype.card ι : ℚ) = 0) (by
      simp only [Nat.cast_eq_zero]
      omega)
  · intro v hv
    obtain ⟨c, hc⟩ := PermSubspace.eq_const_of_mem_constLine hv
    rw [LinearMap.mem_ker, ratRelationForm_apply, hc]
    show ∑ i, c • θ i = 0
    have hsmul : ∑ i, c • θ i = algebraMap ℚ K c * ∑ i, θ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Algebra.smul_def c (θ i)
    rw [hsmul, hsum, mul_zero]
  · intro htop
    have hall : ∀ i : ι, θ i = 0 := by
      intro i
      have hmem : (Pi.single i (1 : ℚ)) ∈ LinearMap.ker (ratRelationForm θ) := by
        rw [htop]
        exact Submodule.mem_top
      rw [LinearMap.mem_ker, ratRelationForm_apply] at hmem
      rw [← hmem]
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, one_smul]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_smul]
      · intro hne
        exact absurd (Finset.mem_univ i) hne
    obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hcard
    exact hij (hinj (by rw [hall i, hall j]))


/-- **The rigid labelled root family of a traceless polynomial with symmetric Galois group.** -/
theorem exists_rigid_root_family {p : Polynomial ℚ} (hmonic : p.Monic) (hirr : Irreducible p)
    {D : ℕ} (hdeg : p.natDegree = D) (hD1 : 1 < D) (hcoeff : p.coeff (D - 1) = 0)
    (hgal : Nat.card p.Gal = D.factorial) :
    ∃ γ : Fin D → p.SplittingField, Function.Injective γ ∧
      p.map (algebraMap ℚ p.SplittingField) = ∏ j, (X - C (γ j)) ∧
      LinearMap.ker (ratRelationForm γ)
        = PermSubspace.constLine (K := ℚ) (ι := Fin D) := by
  classical
  have hDpos : 0 < D := by omega
  have hsep : p.Separable := hirr.separable
  haveI hsf : IsSplittingField ℚ p.SplittingField p :=
    Polynomial.IsSplittingField.splittingField p
  haveI : Normal ℚ p.SplittingField := Normal.of_isSplittingField p
  haveI : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨Polynomial.IsSplittingField.splits p.SplittingField p⟩
  obtain ⟨γ, hγ⟩ := HilbertIrreducibility.exists_root_index (M := p.SplittingField) hmonic
    (Polynomial.IsSplittingField.splits p.SplittingField p) hdeg
  have hγinj : Function.Injective γ := by
    refine Polynomial.separable_prod_X_sub_C_iff.mp ?_
    rw [← hγ]
    exact (Polynomial.separable_map _).mpr hsep
  have hnat : (p.map (algebraMap ℚ p.SplittingField)).natDegree = D := by
    rw [hmonic.natDegree_map, hdeg]
  have hsum : ∑ j, γ j = 0 := by
    have hnext : (p.map (algebraMap ℚ p.SplittingField)).nextCoeff = -∑ j, γ j := by
      rw [hγ]
      exact Polynomial.prod_X_sub_C_nextCoeff γ
    have hnext2 : (p.map (algebraMap ℚ p.SplittingField)).nextCoeff = 0 := by
      rw [Polynomial.nextCoeff_of_natDegree_pos (by rw [hnat]; exact hDpos), hnat,
        Polynomial.coeff_map, hcoeff, map_zero]
    rw [hnext2] at hnext
    exact neg_eq_zero.mp hnext.symm
  have hgalcard : Nat.card p.Gal = (Fintype.card (Fin D)).factorial := by
    rw [Fintype.card_fin]
    exact hgal
  refine ⟨γ, hγinj, hγ, ker_ratRelationForm_eq_constLine γ hγinj
    (by rw [Fintype.card_fin]; exact hD1) hsum (fun π => ?_)⟩
  exact exists_algEquiv_of_card_gal hγinj hγ hgalcard π

end

end GaloisForLFunctions.HTGeometry
