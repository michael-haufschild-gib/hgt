import GaloisForLFunctions.RHTower.FermiNymanWeightedConfluentCoupling
import GaloisForLFunctions.RHTower.FermiNymanWeightedCorrelation

/-!
# Exact weighted multiplicity tomography

Every finite packet of admitted zeta jets has spurious duals and mutually orthogonal
positive and negative identity blocks. Taking all finite multiplicity packets and
combining with correlation cancellation gives exact weighted negative index for
`0 < a < 1`, without a simplicity, finite-zero, or zero-location premise.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

theorem isWeightedFermiWitness_spuriousCombination {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (c : ℕ →₀ ℂ) :
    IsWeightedFermiWitness α (spuriousCombination c) :=
  isWeightedFermiWitness_finsetSum ha1 c.support (fun l => spuriousWitness ((l : ℤ) + 1)) c
    (fun _ _ => isWeightedFermiWitness_spurious ha0 (by omega))

theorem weightedDyadicForm_spuriousCombination_spuriousCombination {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (c d : ℕ →₀ ℂ) :
    weightedDyadicForm α (spuriousCombination c) (spuriousCombination d) = 0 := by
  change weightedDyadicForm α (fun t => ∑ l ∈ c.support,
    c l * spuriousWitness ((l : ℤ) + 1) t) (spuriousCombination d) = 0
  rw [weightedDyadicForm_sum_left c.support (fun l => spuriousWitness ((l : ℤ) + 1)) c
    (isWeightedFermiWitness_spuriousCombination ha0 ha1 d)
    (fun _ _ => isWeightedFermiWitness_spurious ha0 (by omega))]
  apply Finset.sum_eq_zero
  intro l hl
  change c l * weightedDyadicForm α (spuriousWitness ((l : ℤ) + 1))
    (fun t => ∑ k ∈ d.support, d k * spuriousWitness ((k : ℤ) + 1) t) = 0
  have hv : IsWeightedFermiWitness α (spuriousWitness ((l : ℤ) + 1)) :=
    isWeightedFermiWitness_spurious ha0 (by omega)
  rw [weightedDyadicForm_sum_right d.support (fun l => spuriousWitness ((l : ℤ) + 1)) d
    hv
    (fun _ _ => isWeightedFermiWitness_spurious ha0 (by omega))]
  simp [weightedDyadicForm_spurious_spurious ha0]

theorem exists_weighted_spurious_jet_duals {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℂ) (hinj : Function.Injective ρ) (n : ι → ℕ)
    (h1 : ∀ i, 1 - α < (ρ i).re) (h2 : ∀ i, (ρ i).re < 1)
    (hn : ∀ i, (n i : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ i)) :
    ∃ g : (Σ i, Fin (n i)) → ℝ → ℂ,
      (∀ a, IsWeightedFermiWitness α (g a)) ∧
      (∀ a b, weightedDyadicForm α (g a) (g b) = 0) ∧
      ∀ a b, weightedDyadicForm α (g a) (weightedNormalizedFermiJet α (ρ b.1) b.2) =
        if a = b then 1 else 0 := by
  classical
  let x : ι → ℂ := fun i => -ρ i
  let t : ℕ → ℂ := fun l => -weightedSpuriousNode α l
  have hx : Function.Injective x := neg_injective.comp hinj
  have ht : Function.Injective t := neg_injective.comp (weightedSpuriousNode_injective α)
  have hsep : ∀ l i, t l ≠ x i := by
    intro l i h
    have h' : weightedSpuriousNode α l = ρ i := neg_injective h
    have := congrArg Complex.re h'
    rw [weightedSpuriousNode_re] at this
    linarith [h1 i]
  let b : (Σ i, Fin (n i)) → ℂ := fun a =>
    (-1 : ℂ) ^ (a.2 : ℕ) * ((a.2 : ℕ).factorial : ℂ)
  have hb : ∀ a, b a ≠ 0 := fun a => mul_ne_zero
    (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero (a.2 : ℕ))
  have hsurj := cauchyJetLinearCombination_surjective x hx n t ht hsep
  have hchoose : ∀ a : (Σ i, Fin (n i)), ∃ c : ℕ →₀ ℂ,
      cauchyJetLinearCombination x n t c = fun s => (if a = s then 1 else 0) / b s := by
    intro a
    exact hsurj _
  choose c hc using hchoose
  refine ⟨fun a => spuriousCombination (c a),
    fun _ => isWeightedFermiWitness_spuriousCombination ha0 ha1 _,
    fun _ _ => weightedDyadicForm_spuriousCombination_spuriousCombination ha0 ha1 _ _, ?_⟩
  intro a s
  have hs : ((s.2.val + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ s.1) :=
    le_trans (by exact_mod_cast Nat.succ_le_of_lt s.2.isLt) (hn s.1)
  unfold spuriousCombination
  change weightedDyadicForm α (fun t => ∑ l ∈ (c a).support,
    c a l * spuriousWitness ((l : ℤ) + 1) t) (weightedNormalizedFermiJet α (ρ s.1) s.2) = _
  rw [weightedDyadicForm_sum_left (c a).support (fun l => spuriousWitness ((l : ℤ) + 1)) (c a)
    (isWeightedFermiWitness_weightedNormalizedFermiJet ha1 (h1 s.1) (h2 s.1) s.2 hs)
    (fun _ _ => isWeightedFermiWitness_spurious ha0 (by omega))]
  simp_rw [weightedDyadicForm_spurious_weightedNormalizedFermiJet ha0 ha1 _ _ (h1 s.1) (h2 s.1) hs]
  have heq := congrFun (hc a) s
  simp only [cauchyJetLinearCombination, Finsupp.linearCombination_apply,
    Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cauchyJetColumn] at heq
  calc
    _ = b s * ∑ l ∈ (c a).support,
        c a l * ((t l - x s.1)⁻¹) ^ (s.2.val + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp [b, t, x]
      rw [neg_sub_neg]
      ring
    _ = _ := by rw [heq]; exact mul_div_cancel₀ _ (hb s)

theorem isWeightedFermiWitness_neutralWitnessGraph {α : ℝ} (ha1 : α < 1) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ) (X : ι → ι → ℂ)
    (hh : ∀ i, IsWeightedFermiWitness α (h i)) (hg : ∀ i, IsWeightedFermiWitness α (g i)) (i : ι) :
    IsWeightedFermiWitness α (neutralWitnessGraph h g X i) := by
  apply isWeightedFermiWitness_finsetSum ha1 Finset.univ _ _
  intro a _
  cases a with
  | inl r => exact hh r
  | inr r => exact hg r

theorem weightedDyadicForm_neutralWitnessGraph {α : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ) (X Y : ι → ι → ℂ)
    (hh : ∀ i, IsWeightedFermiWitness α (h i)) (hg : ∀ i, IsWeightedFermiWitness α (g i))
    (hgg : ∀ i j, weightedDyadicForm α (g i) (g j) = 0)
    (hgh : ∀ i j, weightedDyadicForm α (g i) (h j) = if i = j then 1 else 0) (i j : ι) :
    weightedDyadicForm α (neutralWitnessGraph h g X i) (neutralWitnessGraph h g Y j) =
      weightedDyadicForm α (h i) (h j) + X i j + (starRingEnd ℂ) (Y j i) := by
  classical
  have hf : ∀ a : ι ⊕ ι, IsWeightedFermiWitness α ((Sum.elim h g) a) := by
    intro a
    cases a with
    | inl r => exact hh r
    | inr r => exact hg r
  have hhg : ∀ i j, weightedDyadicForm α (h i) (g j) = if j = i then 1 else 0 := by
    intro i j
    rw [weightedDyadicForm_conj, hgh]
    split_ifs <;> simp
  unfold neutralWitnessGraph
  rw [weightedDyadicForm_sum_sum _ _ _ (fun a b => (hf a).integrableOn_weighted_mul_conj (hf b))]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hgg, mul_zero,
    Finset.sum_const_zero, add_zero, hhg, hgh]
  have hδ : ∀ r : ι, (starRingEnd ℂ) (if r = j then (1 : ℂ) else 0) =
      if r = j then 1 else 0 := by
    intro r
    split_ifs <;> simp
  simp only [hδ, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

def weightedSignedWitnessCompletion (α : ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ) (r : ℝ) : ι → ℝ → ℂ :=
  neutralWitnessGraph h g (fun i j =>
    (1 / 2 : ℂ) * ((r : ℂ) * (if i = j then 1 else 0) - weightedDyadicForm α (h i) (h j)))

theorem weightedDyadicForm_weightedSignedWitnessCompletion {α : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ)
    (hh : ∀ i, IsWeightedFermiWitness α (h i)) (hg : ∀ i, IsWeightedFermiWitness α (g i))
    (hgg : ∀ i j, weightedDyadicForm α (g i) (g j) = 0)
    (hgh : ∀ i j, weightedDyadicForm α (g i) (h j) = if i = j then 1 else 0)
    (r s : ℝ) (i j : ι) :
    weightedDyadicForm α (weightedSignedWitnessCompletion α h g r i) (weightedSignedWitnessCompletion α h g s j) =
      (((r + s) / 2 : ℝ) : ℂ) * (if i = j then 1 else 0) := by
  unfold weightedSignedWitnessCompletion
  rw [weightedDyadicForm_neutralWitnessGraph _ _ _ _ hh hg hgg hgh]
  rw [map_mul, map_sub, map_mul, Complex.conj_ofReal, ← weightedDyadicForm_conj]
  by_cases hij : i = j
  · subst j
    simp only [if_true, map_one, mul_one, map_div₀, map_ofNat]
    push_cast
    ring
  · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
    simp only [map_div₀, map_one, map_ofNat]
    push_cast
    ring

theorem exists_weightedDyadicForm_multiplicity_hyperbolic {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℂ) (hinj : Function.Injective ρ) (n : ι → ℕ)
    (h1 : ∀ i, 1 - α < (ρ i).re) (h2 : ∀ i, (ρ i).re < 1)
    (hn : ∀ i, (n i : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ i)) :
    ∃ vneg vpos : (Σ i, Fin (n i)) → ℝ → ℂ,
      (∀ a, IsWeightedFermiWitness α (vneg a)) ∧
      (∀ a, IsWeightedFermiWitness α (vpos a)) ∧
      (∀ a b, weightedDyadicForm α (vneg a) (vneg b) = if a = b then -1 else 0) ∧
      (∀ a b, weightedDyadicForm α (vpos a) (vpos b) = if a = b then 1 else 0) ∧
      ∀ a b, weightedDyadicForm α (vneg a) (vpos b) = 0 := by
  classical
  let h : (Σ i, Fin (n i)) → ℝ → ℂ := fun a => weightedNormalizedFermiJet α (ρ a.1) a.2
  have hh : ∀ a, IsWeightedFermiWitness α (h a) := fun a =>
    isWeightedFermiWitness_weightedNormalizedFermiJet ha1 (h1 a.1) (h2 a.1) a.2
      (le_trans (by exact_mod_cast Nat.succ_le_of_lt a.2.isLt) (hn a.1))
  obtain ⟨g, hg, hgg, hgh⟩ := exists_weighted_spurious_jet_duals ha0 ha1 ρ hinj n h1 h2 hn
  refine ⟨weightedSignedWitnessCompletion α h g (-1), weightedSignedWitnessCompletion α h g 1,
    fun a => isWeightedFermiWitness_neutralWitnessGraph ha1 _ _ _ hh hg a,
    fun a => isWeightedFermiWitness_neutralWitnessGraph ha1 _ _ _ hh hg a, ?_, ?_, ?_⟩
  · intro a b
    rw [weightedDyadicForm_weightedSignedWitnessCompletion _ _ hh hg hgg hgh]
    split_ifs <;> norm_num
  · intro a b
    rw [weightedDyadicForm_weightedSignedWitnessCompletion _ _ hh hg hgg hgh]
    split_ifs <;> norm_num
  · intro a b
    rw [weightedDyadicForm_weightedSignedWitnessCompletion _ _ hh hg hgg hgh]
    norm_num


theorem exists_weightedStripMultiplicity_hyperbolic {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (s : Finset (weightedStripZeros α)) :
    ∃ vneg vpos : (Σ ρ : s, Fin (weightedStripMultiplicity ρ.1)) → ℝ → ℂ,
      (∀ a, IsWeightedFermiWitness α (vneg a)) ∧
      (∀ a, IsWeightedFermiWitness α (vpos a)) ∧
      (∀ a b, weightedDyadicForm α (vneg a) (vneg b) = if a = b then -1 else 0) ∧
      (∀ a b, weightedDyadicForm α (vpos a) (vpos b) = if a = b then 1 else 0) ∧
      ∀ a b, weightedDyadicForm α (vneg a) (vpos b) = 0 := by
  classical
  exact exists_weightedDyadicForm_multiplicity_hyperbolic ha0 ha1
    (fun ρ : s => ((ρ.1 : weightedStripZeros α) : ℂ))
    (Subtype.val_injective.comp Subtype.val_injective) (fun ρ => weightedStripMultiplicity ρ.1)
    (fun ρ => ρ.1.2.2.1) (fun ρ => ρ.1.2.2.2)
    (fun ρ => le_of_eq (weightedStripMultiplicity_coe ρ.1))

theorem weightedStripMultiplicityCount_le_weightedWitnessNegIndex {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) :
    weightedStripMultiplicityCount α ≤ weightedWitnessNegIndex α := by
  classical
  refine iSup_le fun s => ?_
  let n : s → ℕ := fun ρ => weightedStripMultiplicity ρ.1
  obtain ⟨v, _, hv, _, hq, _, _⟩ := exists_weightedStripMultiplicity_hyperbolic ha0 ha1 s
  have hcard : Fintype.card (Σ ρ : s, Fin (n ρ)) = ∑ ρ ∈ s, weightedStripMultiplicity ρ := by
    simp [Fintype.card_sigma, n, Finset.sum_attach]
  let e := Fintype.equivFin (Σ ρ : s, Fin (n ρ))
  have hfam : IsWeightedNegOrthonormalWitnessFamily α (Fintype.card (Σ ρ : s, Fin (n ρ))) := by
    refine ⟨fun i => v (e.symm i), fun i => hv _, fun i j => ?_⟩
    simpa only [e.symm.injective.eq_iff] using hq (e.symm i) (e.symm j)
  have hle := le_iSup₂_of_le
    (f := fun m (_ : IsWeightedNegOrthonormalWitnessFamily α m) => (m : ℕ∞)) _ hfam le_rfl
  simpa only [hcard, weightedWitnessNegIndex] using hle

/-- Exact weighted inertia counts every admitted zero with analytic multiplicity. -/
theorem weightedWitnessNegIndex_eq_weightedStripMultiplicityCount {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    weightedWitnessNegIndex a = weightedStripMultiplicityCount a :=
  le_antisymm (weightedWitnessNegIndex_le_weightedStripMultiplicityCount ha0.le ha1)
    (weightedStripMultiplicityCount_le_weightedWitnessNegIndex ha0 ha1)

/-- The full open weight profile, without a zero-finiteness or simplicity premise. -/
theorem weightedWitnessNegIndex_multiplicity_profile :
    ∀ a ∈ Ioo (0 : ℝ) 1,
      weightedWitnessNegIndex a = weightedStripMultiplicityCount a :=
  fun _ ha => weightedWitnessNegIndex_eq_weightedStripMultiplicityCount ha.1 ha.2

end RHTower
