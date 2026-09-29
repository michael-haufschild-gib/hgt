import GaloisForLFunctions.RHTower.FermiNymanConfluentCoupling
import GaloisForLFunctions.HTGeometry.CauchyJetControllability
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Zero multiplicities force literal hyperbolic Fermi witness blocks

Normalized logarithmic witnesses couple to spurious witnesses through confluent Cauchy columns.
Complex Cauchy-jet controllability supplies finitely supported spurious combinations dual to every
finite packet of jets. Their span is neutral. Completing the jet family against its own Hermitian
Gram matrix gives mutually orthogonal signed families with Gram matrices `-I` and `+I`.

Every right-strip zero of analytic order `m` contributes `m` slots to both families. In particular,
the total right-strip zero multiplicity, defined as an extended-natural supremum of finite sums,
is at most the negative index of the physical dyadic form. All orders are finite; this follows from
analytic continuation of zeta on the punctured plane and its nonvanishing at `2`.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def spuriousCombination (c : ℕ →₀ ℂ) (t : ℝ) : ℂ :=
  ∑ l ∈ c.support, c l * spuriousWitness ((l : ℤ) + 1) t

theorem isFermiNymanWitness_spuriousCombination (c : ℕ →₀ ℂ) :
    IsFermiNymanWitness (spuriousCombination c) :=
  isFermiNymanWitness_finsetSum c.support (fun l => spuriousWitness ((l : ℤ) + 1)) c
    (fun _ _ => isFermiNymanWitness_spurious (by omega))

theorem dyadicForm_spuriousCombination_spuriousCombination (c d : ℕ →₀ ℂ) :
    dyadicForm (spuriousCombination c) (spuriousCombination d) = 0 := by
  change dyadicForm (fun t => ∑ l ∈ c.support,
    c l * spuriousWitness ((l : ℤ) + 1) t) (spuriousCombination d) = 0
  rw [dyadicForm_sum_left c.support (fun l => spuriousWitness ((l : ℤ) + 1)) c
    (isFermiNymanWitness_spuriousCombination d)
    (fun _ _ => isFermiNymanWitness_spurious (by omega))]
  apply Finset.sum_eq_zero
  intro l hl
  change c l * dyadicForm (spuriousWitness ((l : ℤ) + 1))
    (fun t => ∑ k ∈ d.support, d k * spuriousWitness ((k : ℤ) + 1) t) = 0
  have hv : IsFermiNymanWitness (spuriousWitness ((l : ℤ) + 1)) :=
    isFermiNymanWitness_spurious (by omega)
  rw [dyadicForm_sum_right d.support (fun l => spuriousWitness ((l : ℤ) + 1)) d
    hv
    (fun _ _ => isFermiNymanWitness_spurious (by omega))]
  simp [dyadicForm_spurious_spurious]

theorem exists_spurious_jet_duals {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℂ) (hinj : Function.Injective ρ) (n : ι → ℕ)
    (h1 : ∀ i, 1 / 2 < (ρ i).re) (h2 : ∀ i, (ρ i).re < 1)
    (hn : ∀ i, (n i : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ i)) :
    ∃ g : (Σ i, Fin (n i)) → ℝ → ℂ,
      (∀ a, IsFermiNymanWitness (g a)) ∧
      (∀ a b, dyadicForm (g a) (g b) = 0) ∧
      ∀ a b, dyadicForm (g a) (normalizedFermiJet (ρ b.1) b.2) =
        if a = b then 1 else 0 := by
  classical
  let x : ι → ℂ := fun i => -ρ i
  let t : ℕ → ℂ := fun l => -spuriousNode l
  have hx : Function.Injective x := neg_injective.comp hinj
  have ht : Function.Injective t := neg_injective.comp spuriousNode_injective
  have hsep : ∀ l i, t l ≠ x i := by
    intro l i h
    have h' : spuriousNode l = ρ i := neg_injective h
    have := congrArg Complex.re h'
    rw [spuriousNode_re] at this
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
    fun _ => isFermiNymanWitness_spuriousCombination _,
    fun _ _ => dyadicForm_spuriousCombination_spuriousCombination _ _, ?_⟩
  intro a s
  have hs : ((s.2.val + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ s.1) :=
    le_trans (by exact_mod_cast Nat.succ_le_of_lt s.2.isLt) (hn s.1)
  unfold spuriousCombination
  change dyadicForm (fun t => ∑ l ∈ (c a).support,
    c a l * spuriousWitness ((l : ℤ) + 1) t) (normalizedFermiJet (ρ s.1) s.2) = _
  rw [dyadicForm_sum_left (c a).support (fun l => spuriousWitness ((l : ℤ) + 1)) (c a)
    (isFermiNymanWitness_normalizedFermiJet (h1 s.1) (h2 s.1) s.2 hs)
    (fun _ _ => isFermiNymanWitness_spurious (by omega))]
  simp_rw [dyadicForm_spurious_normalizedFermiJet _ _ (h1 s.1) (h2 s.1) hs]
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

def neutralWitnessGraph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ) (X : ι → ι → ℂ) (i : ι) (t : ℝ) : ℂ :=
  ∑ a : ι ⊕ ι, (Sum.elim (fun r => if r = i then 1 else 0) (X i)) a *
    (Sum.elim h g) a t

theorem isFermiNymanWitness_neutralWitnessGraph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ) (X : ι → ι → ℂ)
    (hh : ∀ i, IsFermiNymanWitness (h i)) (hg : ∀ i, IsFermiNymanWitness (g i)) (i : ι) :
    IsFermiNymanWitness (neutralWitnessGraph h g X i) := by
  apply isFermiNymanWitness_finsetSum Finset.univ _ _
  intro a _
  cases a with
  | inl r => exact hh r
  | inr r => exact hg r

theorem dyadicForm_neutralWitnessGraph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ) (X Y : ι → ι → ℂ)
    (hh : ∀ i, IsFermiNymanWitness (h i)) (hg : ∀ i, IsFermiNymanWitness (g i))
    (hgg : ∀ i j, dyadicForm (g i) (g j) = 0)
    (hgh : ∀ i j, dyadicForm (g i) (h j) = if i = j then 1 else 0) (i j : ι) :
    dyadicForm (neutralWitnessGraph h g X i) (neutralWitnessGraph h g Y j) =
      dyadicForm (h i) (h j) + X i j + (starRingEnd ℂ) (Y j i) := by
  classical
  have hf : ∀ a : ι ⊕ ι, IsFermiNymanWitness ((Sum.elim h g) a) := by
    intro a
    cases a with
    | inl r => exact hh r
    | inr r => exact hg r
  have hhg : ∀ i j, dyadicForm (h i) (g j) = if j = i then 1 else 0 := by
    intro i j
    rw [dyadicForm_conj, hgh]
    split_ifs <;> simp
  unfold neutralWitnessGraph
  rw [dyadicForm_sum_sum _ _ _ (fun a b => (hf a).integrableOn_mul_conj_witness (hf b))]
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

def signedWitnessCompletion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ) (r : ℝ) : ι → ℝ → ℂ :=
  neutralWitnessGraph h g (fun i j =>
    (1 / 2 : ℂ) * ((r : ℂ) * (if i = j then 1 else 0) - dyadicForm (h i) (h j)))

theorem dyadicForm_signedWitnessCompletion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h g : ι → ℝ → ℂ)
    (hh : ∀ i, IsFermiNymanWitness (h i)) (hg : ∀ i, IsFermiNymanWitness (g i))
    (hgg : ∀ i j, dyadicForm (g i) (g j) = 0)
    (hgh : ∀ i j, dyadicForm (g i) (h j) = if i = j then 1 else 0)
    (r s : ℝ) (i j : ι) :
    dyadicForm (signedWitnessCompletion h g r i) (signedWitnessCompletion h g s j) =
      (((r + s) / 2 : ℝ) : ℂ) * (if i = j then 1 else 0) := by
  unfold signedWitnessCompletion
  rw [dyadicForm_neutralWitnessGraph _ _ _ _ hh hg hgg hgh]
  rw [map_mul, map_sub, map_mul, Complex.conj_ofReal, ← dyadicForm_conj]
  by_cases hij : i = j
  · subst j
    simp only [if_true, map_one, mul_one, map_div₀, map_ofNat]
    push_cast
    ring
  · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
    simp only [map_div₀, map_one, map_ofNat]
    push_cast
    ring

theorem exists_dyadicForm_multiplicity_hyperbolic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℂ) (hinj : Function.Injective ρ) (n : ι → ℕ)
    (h1 : ∀ i, 1 / 2 < (ρ i).re) (h2 : ∀ i, (ρ i).re < 1)
    (hn : ∀ i, (n i : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ i)) :
    ∃ vneg vpos : (Σ i, Fin (n i)) → ℝ → ℂ,
      (∀ a, IsFermiNymanWitness (vneg a)) ∧
      (∀ a, IsFermiNymanWitness (vpos a)) ∧
      (∀ a b, dyadicForm (vneg a) (vneg b) = if a = b then -1 else 0) ∧
      (∀ a b, dyadicForm (vpos a) (vpos b) = if a = b then 1 else 0) ∧
      ∀ a b, dyadicForm (vneg a) (vpos b) = 0 := by
  classical
  let h : (Σ i, Fin (n i)) → ℝ → ℂ := fun a => normalizedFermiJet (ρ a.1) a.2
  have hh : ∀ a, IsFermiNymanWitness (h a) := fun a =>
    isFermiNymanWitness_normalizedFermiJet (h1 a.1) (h2 a.1) a.2
      (le_trans (by exact_mod_cast Nat.succ_le_of_lt a.2.isLt) (hn a.1))
  obtain ⟨g, hg, hgg, hgh⟩ := exists_spurious_jet_duals ρ hinj n h1 h2 hn
  refine ⟨signedWitnessCompletion h g (-1), signedWitnessCompletion h g 1,
    fun a => isFermiNymanWitness_neutralWitnessGraph _ _ _ hh hg a,
    fun a => isFermiNymanWitness_neutralWitnessGraph _ _ _ hh hg a, ?_, ?_, ?_⟩
  · intro a b
    rw [dyadicForm_signedWitnessCompletion _ _ hh hg hgg hgh]
    split_ifs <;> norm_num
  · intro a b
    rw [dyadicForm_signedWitnessCompletion _ _ hh hg hgg hgh]
    split_ifs <;> norm_num
  · intro a b
    rw [dyadicForm_signedWitnessCompletion _ _ hh hg hgg hgh]
    norm_num

/-- Analytic multiplicity of an actual zero strictly to the right of the critical line. -/
def rightStripMultiplicity (ρ : rightStripZeros) : ℕ :=
  (analyticOrderAt riemannZeta (ρ : ℂ)).toNat

theorem rightStripMultiplicity_coe (ρ : rightStripZeros) :
    (rightStripMultiplicity ρ : ℕ∞) = analyticOrderAt riemannZeta (ρ : ℂ) := by
  apply ENat.coe_toNat
  have hρ : (ρ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith [ρ.2.2.2]
  apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (x := 2) (by simp) (by simpa using hρ)
  rw [analyticOrderAt_eq_zero.mpr (Or.inr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re)))]
  exact ENat.zero_ne_top

/-- Every finite packet of actual right-strip zeros produces an exact hyperbolic witness block. -/
theorem exists_rightStripMultiplicity_hyperbolic (s : Finset rightStripZeros) :
    ∃ vneg vpos : (Σ ρ : s, Fin (rightStripMultiplicity ρ.1)) → ℝ → ℂ,
      (∀ a, IsFermiNymanWitness (vneg a)) ∧
      (∀ a, IsFermiNymanWitness (vpos a)) ∧
      (∀ a b, dyadicForm (vneg a) (vneg b) = if a = b then -1 else 0) ∧
      (∀ a b, dyadicForm (vpos a) (vpos b) = if a = b then 1 else 0) ∧
      ∀ a b, dyadicForm (vneg a) (vpos b) = 0 := by
  classical
  exact exists_dyadicForm_multiplicity_hyperbolic
    (fun ρ : s => ((ρ.1 : rightStripZeros) : ℂ))
    (Subtype.val_injective.comp Subtype.val_injective) (fun ρ => rightStripMultiplicity ρ.1)
    (fun ρ => ρ.1.2.2.1) (fun ρ => ρ.1.2.2.2)
    (fun ρ => le_of_eq (rightStripMultiplicity_coe ρ.1))

/-- Total right-strip multiplicity, including the case of infinitely many zeros. -/
def rightStripMultiplicityCount : ℕ∞ :=
  ⨆ s : Finset rightStripZeros, ((∑ ρ ∈ s, rightStripMultiplicity ρ : ℕ) : ℕ∞)

/-- The dyadic form detects every right-strip zero with its full analytic multiplicity. -/
theorem rightStripMultiplicityCount_le_witnessNegIndex :
    rightStripMultiplicityCount ≤ witnessNegIndex := by
  classical
  refine iSup_le fun s => ?_
  let n : s → ℕ := fun ρ => rightStripMultiplicity ρ.1
  obtain ⟨v, _, hv, _, hq, _, _⟩ := exists_rightStripMultiplicity_hyperbolic s
  have hcard : Fintype.card (Σ ρ : s, Fin (n ρ)) = ∑ ρ ∈ s, rightStripMultiplicity ρ := by
    simp [Fintype.card_sigma, n, Finset.sum_attach]
  let e := Fintype.equivFin (Σ ρ : s, Fin (n ρ))
  have hfam : IsNegOrthonormalWitnessFamily (Fintype.card (Σ ρ : s, Fin (n ρ))) := by
    refine ⟨fun i => v (e.symm i), fun i => hv _, fun i j => ?_⟩
    simpa only [e.symm.injective.eq_iff] using hq (e.symm i) (e.symm j)
  have hle := le_iSup₂_of_le
    (f := fun m (_ : IsNegOrthonormalWitnessFamily m) => (m : ℕ∞)) _ hfam le_rfl
  simpa only [hcard, witnessNegIndex] using hle

end RHTower
