import GaloisForLFunctions.HTGeometry.HolographicCommutatorRank
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolUniversalShiftField

/-!
# The horizon linear-contact invariant and the sharp commutator-rank law

The commuting-chord theorem forces every commuting plane of laws to meet the complete
differential-algebraic dependence horizon in a projective-linear set: at most one line, or the
whole plane.  This file isolates that incidence condition as `LinearContactPlane`, defines the
horizon contact-kernel dimension `κ(X)` — the largest dimension of an exterior subspace all of
whose decomposable members span linear-contact planes — and its complement, the horizon
commutator index `χ_HT(X)`.

The sharp projective-obstruction law follows unconditionally: the commutator symbol of every
realization has rank at least `χ_HT` of its exact horizon, because the commutator kernel is
itself a contact-only subspace.  At the abelian endpoint the bound is attained: a linear-subspace
horizon has `χ_HT = 0`, and the diagonal universal shift field realizes every character-kernel
hyperplane as the exact one-observable horizon of a fully commuting law family with commutator
rank zero.  Equality in the rank law is therefore realizable inside an abelian Lie algebra.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [Field K] [Field L] [Algebra K L] [CharZero K]
  [AddCommGroup V] [Module K V]

/-- A plane spanned by two directions has linear contact with a horizon set when it meets the
horizon in at most one line, or lies inside it entirely. -/
def LinearContactPlane (H : Set V) (v w : V) : Prop :=
  (∀ p ∈ Submodule.span K {v, w}, ∀ q ∈ Submodule.span K {v, w},
      p ∈ H → q ∈ H → ¬ LinearIndependent K ![p, q]) ∨
    (Submodule.span K {v, w} : Set V) ⊆ H

omit [Field L] [Algebra K L] [CharZero K] in
/-- Two independent members of a plane span the plane. -/
theorem span_pair_le_of_linearIndependent_mem
    {v w p q : V} (hp : p ∈ Submodule.span K {v, w}) (hq : q ∈ Submodule.span K {v, w})
    (hpq : LinearIndependent K ![p, q]) :
    Submodule.span K {v, w} ≤ Submodule.span K {p, q} := by
  obtain ⟨α, β, hp'⟩ := Submodule.mem_span_pair.mp hp
  obtain ⟨γ, δ, hq'⟩ := Submodule.mem_span_pair.mp hq
  have hzero : ∀ c d : K, c • p + d • q = 0 → c = 0 ∧ d = 0 := by
    intro c d hcd
    have h := Fintype.linearIndependent_iff.mp hpq ![c, d] (by
      simpa [Fin.sum_univ_two] using hcd)
    exact ⟨h 0, h 1⟩
  have hv : (α * δ - β * γ) • v = δ • p - β • q := by
    rw [← hp', ← hq']
    module
  have hw : (α * δ - β * γ) • w = α • q - γ • p := by
    rw [← hp', ← hq']
    module
  have hdet : α * δ - β * γ ≠ 0 := by
    intro h0
    have hv0 : δ • p + (-β) • q = 0 := by
      have hsub : δ • p - β • q = 0 := by rw [← hv, h0, zero_smul]
      rw [neg_smul, ← sub_eq_add_neg]
      exact hsub
    obtain ⟨hδ, hβ'⟩ := hzero δ (-β) hv0
    have hβ : β = 0 := neg_eq_zero.mp hβ'
    have hw0 : (-γ) • p + α • q = 0 := by
      have hsub : α • q - γ • p = 0 := by rw [← hw, h0, zero_smul]
      rw [neg_smul, add_comm, ← sub_eq_add_neg]
      exact hsub
    obtain ⟨hγ', hα⟩ := hzero (-γ) α hw0
    have hp0 : p = 0 := by
      rw [← hp', hα, hβ, zero_smul, zero_smul, add_zero]
    have hne := hpq.ne_zero 0
    simp [hp0] at hne
  have hvmem : v ∈ Submodule.span K {p, q} := by
    apply Submodule.mem_span_pair.mpr
    refine ⟨(α * δ - β * γ)⁻¹ * δ, (α * δ - β * γ)⁻¹ * -β, ?_⟩
    have hv2 : v = (α * δ - β * γ)⁻¹ • (δ • p - β • q) := by
      rw [← hv, smul_smul, inv_mul_cancel₀ hdet, one_smul]
    rw [hv2]
    module
  have hwmem : w ∈ Submodule.span K {p, q} := by
    apply Submodule.mem_span_pair.mpr
    refine ⟨(α * δ - β * γ)⁻¹ * -γ, (α * δ - β * γ)⁻¹ * α, ?_⟩
    have hw2 : w = (α * δ - β * γ)⁻¹ • (α • q - γ • p) := by
      rw [← hw, smul_smul, inv_mul_cancel₀ hdet, one_smul]
    rw [hw2]
    module
  rw [Submodule.span_le]
  rintro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact hvmem
  · exact hwmem

/-- **Commuting planes have linear contact.**  The commuting-plane locus of every realization is
contained in the linear-contact locus of its exact one-observable dependence horizon. -/
theorem linearContactPlane_of_commute
    (ρ : V →ₗ[K] Derivation K L L) (x : L) {v w : V}
    (hcomm : Function.Commute (ρ v) (ρ w)) :
    LinearContactPlane (K := K) (linearDerivationDependenceHorizon ρ x) v w := by
  classical
  by_cases hsub : (Submodule.span K {v, w} : Set V) ⊆
      linearDerivationDependenceHorizon ρ x
  · exact Or.inr hsub
  · left
    intro p hp q hq hpH hqH hli
    apply hsub
    intro z hz
    have hle := span_pair_le_of_linearIndependent_mem (K := K) hp hq hli
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp (hle hz)
    obtain ⟨α, β, hp'⟩ := Submodule.mem_span_pair.mp hp
    obtain ⟨γ, δ, hq'⟩ := Submodule.mem_span_pair.mp hq
    have hpq_comm : Function.Commute (ρ p) (ρ q) := by
      rw [← hp', ← hq']
      simpa only [map_add, map_smul] using!
        linearCombinations_commute_of_commute (ρ v) (ρ w) hcomm α β γ δ
    exact commuting_horizon_chord ρ x hpH hqH hpq_comm a b

/-- A subspace of the second exterior power is contact-only for a horizon when every independent
pair whose wedge lies in it spans a linear-contact plane. -/
def ContactOnlySubspace (H : Set V) (U : Submodule K (⋀[K]^2 V)) : Prop :=
  ∀ v w : V, LinearIndependent K ![v, w] →
    exteriorPower.ιMulti K 2 ![v, w] ∈ U → LinearContactPlane (K := K) H v w

/-- The horizon contact-kernel dimension `κ(X)`: the largest dimension of a contact-only
exterior subspace. -/
def horizonContactKernelDim [FiniteDimensional K V] (H : Set V) : ℕ :=
  sSup {n : ℕ | ∃ U : Submodule K (⋀[K]^2 V),
    ContactOnlySubspace (K := K) H U ∧ Module.finrank K U = n}

/-- The horizon commutator index `χ_HT(X)`: the codimension of the largest contact-only exterior
subspace. -/
def horizonCommutatorIndex [FiniteDimensional K V] (H : Set V) : ℕ :=
  Module.finrank K (⋀[K]^2 V) - horizonContactKernelDim (K := K) H

/-- The kernel of the commutator symbol is contact-only for the exact dependence horizon. -/
theorem contactOnlySubspace_ker_derivationCommutatorMap
    (ρ : V →ₗ[K] Derivation K L L) (x : L) :
    ContactOnlySubspace (K := K) (linearDerivationDependenceHorizon ρ x)
      (derivationCommutatorMap ρ).ker := by
  intro v w _ hker
  have hzero : ⁅ρ v, ρ w⁆ = 0 := by
    have hmem := LinearMap.mem_ker.mp hker
    simpa [derivationCommutatorMap_wedge] using hmem
  exact linearContactPlane_of_commute ρ x
    ((derivation_commute_iff_commutator_eq_zero (ρ v) (ρ w)).mpr hzero)

/-- **Sharp projective-obstruction law.**  The commutator rank of every realization is bounded
below by the horizon commutator index of its exact dependence horizon. -/
theorem horizonCommutatorIndex_le_finrank_derivationCommutatorMap_range
    [FiniteDimensional K V] (ρ : V →ₗ[K] Derivation K L L) (x : L) :
    horizonCommutatorIndex (K := K) (linearDerivationDependenceHorizon ρ x) ≤
      Module.finrank K (derivationCommutatorMap ρ).range := by
  have hbdd : BddAbove {n : ℕ | ∃ U : Submodule K (⋀[K]^2 V),
      ContactOnlySubspace (K := K) (linearDerivationDependenceHorizon ρ x) U ∧
      Module.finrank K U = n} := by
    refine ⟨Module.finrank K (⋀[K]^2 V), ?_⟩
    rintro n ⟨U, _, rfl⟩
    exact Submodule.finrank_le U
  have hκ : Module.finrank K (derivationCommutatorMap ρ).ker ≤
      horizonContactKernelDim (K := K) (linearDerivationDependenceHorizon ρ x) :=
    le_csSup hbdd ⟨(derivationCommutatorMap ρ).ker,
      contactOnlySubspace_ker_derivationCommutatorMap ρ x, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (derivationCommutatorMap ρ)
  unfold horizonCommutatorIndex
  omega

/-! ## The abelian endpoint: linear-subspace horizons -/

omit [Field L] [Algebra K L] [CharZero K] in
/-- Every plane has linear contact with a linear-subspace horizon. -/
theorem linearContactPlane_of_submodule (W : Submodule K V) (v w : V) :
    LinearContactPlane (K := K) (W : Set V) v w := by
  classical
  by_cases hex : ∃ p q : V, p ∈ Submodule.span K {v, w} ∧ q ∈ Submodule.span K {v, w} ∧
      p ∈ W ∧ q ∈ W ∧ LinearIndependent K ![p, q]
  · right
    obtain ⟨p, q, hp, hq, hpW, hqW, hli⟩ := hex
    have hle := span_pair_le_of_linearIndependent_mem (K := K) hp hq hli
    have hpq_le : Submodule.span K {p, q} ≤ W := by
      rw [Submodule.span_le]
      rintro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hpW
      · exact hqW
    intro z hz
    exact hpq_le (hle hz)
  · left
    intro p hp q hq hpW hqW hli
    exact hex ⟨p, q, hp, hq, hpW, hqW, hli⟩

omit [Field L] [Algebra K L] [CharZero K] in
/-- The full exterior power is contact-only for a linear-subspace horizon. -/
theorem contactOnlySubspace_top_of_submodule (W : Submodule K V) :
    ContactOnlySubspace (K := K) (W : Set V) (⊤ : Submodule K (⋀[K]^2 V)) :=
  fun v w _ _ ↦ linearContactPlane_of_submodule W v w

omit [Field L] [Algebra K L] [CharZero K] in
/-- Linear-subspace horizons have maximal contact-kernel dimension. -/
theorem horizonContactKernelDim_of_submodule [FiniteDimensional K V] (W : Submodule K V) :
    horizonContactKernelDim (K := K) (W : Set V) = Module.finrank K (⋀[K]^2 V) := by
  have hmem : Module.finrank K (⋀[K]^2 V) ∈ {n : ℕ | ∃ U : Submodule K (⋀[K]^2 V),
      ContactOnlySubspace (K := K) (W : Set V) U ∧ Module.finrank K U = n} :=
    ⟨⊤, contactOnlySubspace_top_of_submodule W, finrank_top K _⟩
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro n ⟨U, _, rfl⟩
    exact Submodule.finrank_le U
  · refine le_csSup ⟨Module.finrank K (⋀[K]^2 V), ?_⟩ hmem
    rintro n ⟨U, _, rfl⟩
    exact Submodule.finrank_le U

omit [Field L] [Algebra K L] [CharZero K] in
/-- Linear-subspace horizons have vanishing commutator index. -/
theorem horizonCommutatorIndex_of_submodule [FiniteDimensional K V] (W : Submodule K V) :
    horizonCommutatorIndex (K := K) (W : Set V) = 0 := by
  unfold horizonCommutatorIndex
  rw [horizonContactKernelDim_of_submodule]
  omega

omit [CharZero K] in
/-- A fully commuting law family has vanishing commutator symbol. -/
theorem derivationCommutatorMap_eq_zero_of_forall_commute
    (ρ : V →ₗ[K] Derivation K L L)
    (hcomm : ∀ v w : V, Function.Commute (ρ v) (ρ w)) :
    derivationCommutatorMap ρ = 0 := by
  suffices h : ∀ z : ⋀[K]^2 V, derivationCommutatorMap ρ z = 0 by
    apply LinearMap.ext
    intro z
    rw [h z]
    rfl
  intro z
  have hz : z ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K 2 (M := V))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun y _ ↦ derivationCommutatorMap ρ y = 0) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨f, rfl⟩
    have hwedge : exteriorPower.ιMulti K 2 f = exteriorPower.ιMulti K 2 ![f 0, f 1] := by
      congr 1
      funext j
      fin_cases j <;> rfl
    rw [hwedge, derivationCommutatorMap_wedge]
    exact (derivation_commute_iff_commutator_eq_zero _ _).mp (hcomm (f 0) (f 1))
  · simp
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul, ha, smul_zero]

/-! ## The diagonal universal shift field attains the abelian endpoint -/

section AbelianWitness

variable {h ι : Type*} [AddCommGroup h] [Module K h]

omit [CharZero K] in
/-- Two derivations of the universal grid field agreeing on all ancestral coordinates agree. -/
theorem universalShiftField_derivation_ext
    (D₁ D₂ : Derivation K (UniversalShiftField K ι) (UniversalShiftField K ι))
    (hgen : ∀ n i, D₁ (universalShiftAncestor (K := K) n i) =
      D₂ (universalShiftAncestor (K := K) n i)) :
    D₁ = D₂ := by
  apply fractionRing_derivation_ext (A := UniversalShiftPolynomial K ι)
  intro a
  have hres : D₁.compAlgebraMap (UniversalShiftPolynomial K ι) =
      D₂.compAlgebraMap (UniversalShiftPolynomial K ι) := by
    apply MvPolynomial.derivation_ext
    intro p
    have := hgen p.1 p.2
    simpa [Derivation.compAlgebraMap_apply, universalShiftAncestor,
      universalShiftEmbedding_apply] using this
  simpa [Derivation.compAlgebraMap_apply] using DFunLike.congr_fun hres a

omit [CharZero K] in
/-- The diagonal weighted-shift law family is fully commuting. -/
theorem universalWeightedShift_commute
    (characters : ι → h →ₗ[K] K) (A B : h) :
    Function.Commute (universalWeightedShiftDerivation characters A)
      (universalWeightedShiftDerivation characters B) := by
  rw [derivation_commute_iff_commutator_eq_zero]
  apply universalShiftField_derivation_ext
  intro n i
  rw [Derivation.commutator_apply]
  simp [universalWeightedShiftDerivation_ancestor, smul_smul, mul_comm]

/-- The diagonal weighted-shift law as a linear map on law space. -/
def universalWeightedShiftLawMap (characters : ι → h →ₗ[K] K) :
    h →ₗ[K] Derivation K (UniversalShiftField K ι) (UniversalShiftField K ι) where
  toFun A := universalWeightedShiftDerivation characters A
  map_add' A B := by
    apply universalShiftField_derivation_ext
    intro n i
    simp [universalWeightedShiftDerivation_ancestor, add_smul]
  map_smul' c A := by
    apply universalShiftField_derivation_ext
    intro n i
    simp [universalWeightedShiftDerivation_ancestor, smul_smul]

omit [CharZero K] in
@[simp] theorem universalWeightedShiftLawMap_apply
    (characters : ι → h →ₗ[K] K) (A : h) :
    universalWeightedShiftLawMap (K := K) characters A =
      universalWeightedShiftDerivation characters A := rfl

omit [CharZero K] in
/-- The exact one-observable dependence horizon of the diagonal shift law is the character
kernel. -/
theorem universalWeightedShift_dependenceHorizon
    (characters : ι → h →ₗ[K] K) (i₀ : ι) :
    linearDerivationDependenceHorizon (universalWeightedShiftLawMap (K := K) characters)
        (universalShiftAncestor (K := K) 0 i₀) =
      (LinearMap.ker (characters i₀) : Set h) := by
  ext A
  have hjets : ∀ n : ℕ,
      linearDerivationLawJet (universalWeightedShiftLawMap (K := K) characters)
          (universalShiftAncestor (K := K) 0 i₀) A n =
        (characters i₀ A) ^ n • universalShiftAncestor (K := K) n i₀ :=
    fun n ↦ selectedDerivationJet_universalWeightedShift characters A i₀ n
  simp only [linearDerivationDependenceHorizon, Set.mem_setOf_eq, SetLike.mem_coe,
    LinearMap.mem_ker]
  constructor
  · intro hdep
    by_contra hchar
    apply hdep
    have hinj : Function.Injective (fun n : ℕ ↦ ((n, i₀) : ℕ × ι)) := by
      intro a b hab
      exact congrArg Prod.fst hab
    have hbase : AlgebraicIndependent K
        (fun n : ℕ ↦ universalShiftAncestor (K := K) n i₀) := by
      simpa [Function.comp_def] using
        (universalShiftAncestor_algebraicIndependent (K := K) (ι := ι)).comp _ hinj
    have hscaled := AlgebraicIndependent.const_mul_coordinates hbase
      (fun n : ℕ ↦ (characters i₀ A) ^ n)
      (fun n ↦ pow_ne_zero n hchar)
    have hconv : linearDerivationLawJet (universalWeightedShiftLawMap (K := K) characters)
        (universalShiftAncestor (K := K) 0 i₀) A =
        fun n : ℕ ↦ algebraMap K (UniversalShiftField K ι) ((characters i₀ A) ^ n) *
          universalShiftAncestor (K := K) n i₀ := by
      funext n
      rw [hjets n, Algebra.smul_def]
    rw [hconv]
    exact hscaled
  · intro hker hAI
    have h1 := hAI.ne_zero 1
    apply h1
    rw [hjets 1, hker]
    simp

omit [CharZero K] in
/-- **Sharp abelian endpoint.**  The character-kernel horizon is exactly realized by a fully
commuting law family with commutator rank zero, and its horizon commutator index vanishes:
equality holds in the projective-obstruction law inside an abelian Lie algebra. -/
theorem universalWeightedShift_abelian_equality
    [FiniteDimensional K h] (characters : ι → h →ₗ[K] K) (i₀ : ι) :
    Module.finrank K
        (derivationCommutatorMap (universalWeightedShiftLawMap (K := K) characters)).range =
      horizonCommutatorIndex (K := K)
        (linearDerivationDependenceHorizon (universalWeightedShiftLawMap (K := K) characters)
          (universalShiftAncestor (K := K) 0 i₀)) := by
  rw [universalWeightedShift_dependenceHorizon characters i₀,
    horizonCommutatorIndex_of_submodule (LinearMap.ker (characters i₀)),
    derivationCommutatorMap_eq_zero_of_forall_commute _
      (fun A B ↦ universalWeightedShift_commute characters A B),
    LinearMap.range_zero, finrank_bot]

end AbelianWitness

end

end GaloisForLFunctions.HTGeometry
