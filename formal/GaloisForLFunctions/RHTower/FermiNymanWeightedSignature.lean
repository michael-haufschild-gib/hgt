import GaloisForLFunctions.RHTower.FermiNymanWeightedWitness
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# Infinite weighted Fermi signature above the critical parameter

For every finite packet of distinct zeta zeros with `1-a < Re rho < 1`, the
literal weighted Fermi form has a negative orthonormal family of the same size.
Spurious modes are neutral and their coupling matrix is Cauchy with translated
nodes; Hermitian graph completion gives the exact negative identity matrix.

Hardy's unconditional critical-line zeros therefore force infinite negative index
for every `1/2 < a < 1`. At `a=1/2`, the index is exactly the canonical Fermi
index. Its vanishing is equivalent to RH. The supercritical conclusion does not
assume RH and does not determine the index at the boundary.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem isWeightedFermiWitness_powerWitness_of_zeta_eq_zero {a : ℝ} (ha : a < 1)
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) (h1 : 1 - a < ρ.re) (h2 : ρ.re < 1) :
    IsWeightedFermiWitness a (powerWitness ((starRingEnd ℂ) ρ)) := by
  refine ⟨continuousOn_powerWitness _,
    (integrableOn_weighted_normSq_powerWitness_iff a _).2 (by simpa using h1), fun b hb => ?_⟩
  have hconj : ∀ t ∈ Ioc (0 : ℝ) 1,
      fermiNymanGen b t * (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) ρ) t) =
      fermiNymanGen b t * (t : ℂ) ^ (ρ - 1) := by
    intro t ht
    simp only [powerWitness, conj_ofReal_cpow ht.1, map_sub, map_one, Complex.conj_conj]
  rw [setIntegral_congr_fun measurableSet_Ioc hconj, integral_Ioc_fermiNymanGen_mul_cpow hb,
    mellin_fermiNymanGen (by linarith) h2 (by linarith), hζ]
  simp

/-- The source-neutral nodes translated by the weight exponent. -/
def weightedSpuriousNode (a : ℝ) (l : ℕ) : ℂ :=
  spuriousNode l + (1 - 2 * a : ℝ)

theorem weightedSpuriousNode_re (a : ℝ) (l : ℕ) :
    (weightedSpuriousNode a l).re = 1 - 2 * a := by
  simp [weightedSpuriousNode, spuriousNode_re]

theorem weightedSpuriousNode_injective (a : ℝ) : Function.Injective (weightedSpuriousNode a) := by
  intro l m h
  exact spuriousNode_injective (add_right_cancel h)

theorem exists_weightedDyadicForm_neg_orthonormal {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ} (ρ : Fin n → ℂ) (hinj : Function.Injective ρ)
    (hζ : ∀ j, riemannZeta (ρ j) = 0) (h1 : ∀ j, 1 - a < (ρ j).re) (h2 : ∀ j, (ρ j).re < 1) :
    ∃ v : Fin n → ℝ → ℂ, (∀ i, IsWeightedFermiWitness a (v i)) ∧
      ∀ i j, weightedDyadicForm a (v i) (v j) = if i = j then -1 else 0 := by
  classical
  set w : Fin n → ℝ → ℂ := fun j => powerWitness ((starRingEnd ℂ) (ρ j)) with hw
  set g : Fin n → ℝ → ℂ := fun l => spuriousWitness ((l : ℕ) + 1 : ℤ) with hg
  have hwW : ∀ j, IsWeightedFermiWitness a (w j) := fun j =>
    isWeightedFermiWitness_powerWitness_of_zeta_eq_zero ha1 (hζ j) (h1 j) (h2 j)
  have hgW : ∀ l, IsWeightedFermiWitness a (g l) := fun l =>
    isWeightedFermiWitness_spurious ha0 (by omega)
  set c : Fin n → ℂ := fun j => (2 : ℂ) ^ ((1 : ℂ) - (2 * a : ℝ)) * dyadicCoupling (ρ j) with hc
  have hc0 : ∀ j, c j ≠ 0 := fun j => mul_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (by norm_num))) (two_cpow_neg_ne_half (h2 j))
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun l j => weightedDyadicForm a (g l) (w j) with hB
  set Q : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => weightedDyadicForm a (w i) (w j) with hQ
  have hBval : ∀ l j, B l j = c j / (ρ j - weightedSpuriousNode a (l : ℕ)) := by
    intro l j
    simp only [hB, Matrix.of_apply, hg, hw, hc]
    rw [weightedDyadicForm_spurious_power a _ (by linarith [h1 j])]
    congr 1
    unfold weightedSpuriousNode spuriousNode
    push_cast
    ring
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hy0
    have hcy : (fun j => c j * y j) = 0 := by
      refine eq_zero_of_cauchy_sum_eq_zero (a := ρ) (b := fun l : Fin n => weightedSpuriousNode a l)
        hinj ((weightedSpuriousNode_injective a).comp Fin.val_injective) (fun j l => ?_) (fun l => ?_)
      · intro h
        have := congrArg Complex.re h
        rw [weightedSpuriousNode_re] at this
        linarith [h1 j]
      · have := congrFun hy l
        simp only [Matrix.mulVec, dotProduct, hBval, Pi.zero_apply] at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    funext j
    have := congrFun hcy j
    simp only [Pi.zero_apply] at this ⊢
    exact (mul_eq_zero.1 this).resolve_left (hc0 j)
  set X : Matrix (Fin n) (Fin n) ℂ := (-(1 / 2 : ℂ)) • (Q + 1) * B⁻¹ with hX
  have hXB : X * B = (-(1 / 2 : ℂ)) • (Q + 1) := by
    rw [hX, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet, Matrix.mul_one]
  -- the family of all involved witnesses
  set f : Fin n ⊕ Fin n → ℝ → ℂ := Sum.elim w g with hf
  have hfW : ∀ j, IsWeightedFermiWitness a (f j) := by
    intro j; cases j with
    | inl j => exact hwW j
    | inr l => exact hgW l
  set α : Fin n → Fin n ⊕ Fin n → ℂ :=
    fun i => Sum.elim (fun i' => if i' = i then 1 else 0) (fun l => X i l) with hα
  set v : Fin n → ℝ → ℂ := fun i t => ∑ a, α i a * f a t with hv
  refine ⟨v, fun i => ?_, fun i j => ?_⟩
  · exact isWeightedFermiWitness_finsetSum ha1 Finset.univ f (α i) (fun j _ => hfW j)
  · have hint : ∀ i j, IntegrableOn (fun t => (t ^ (2 * a - 1) : ℝ) * f i t * (starRingEnd ℂ) (f j t)) (Ioc 0 1) :=
      fun i j => (hfW i).integrableOn_weighted_mul_conj (hfW j)
    rw [show v i = fun t => ∑ a, α i a * f a t from rfl,
      show v j = fun t => ∑ a, α j a * f a t from rfl, weightedDyadicForm_sum_sum f (α i) (α j) hint]
    have hgg : ∀ l l', weightedDyadicForm a (g l) (g l') = 0 := fun l l' =>
      weightedDyadicForm_spurious_spurious ha0 _ _
    have hwg : ∀ i' l, weightedDyadicForm a (w i') (g l) = (starRingEnd ℂ) (B l i') := by
      intro i' l
      rw [hB, Matrix.of_apply, weightedDyadicForm_conj]
    simp only [Fintype.sum_sum_type, hα, hf, Sum.elim_inl, Sum.elim_inr, hgg, mul_zero,
      Finset.sum_const_zero, add_zero, hwg]
    -- `Q_ij + conj((XB)_{ji}) + (XB)_{ij} = −δ_ij`
    have hXBij : ∑ l, X i l * B l j = (-(1 / 2 : ℂ)) * (Q i j + (1 : Matrix (Fin n) (Fin n) ℂ) i j) := by
      have := congrFun (congrFun hXB i) j
      simpa [Matrix.mul_apply] using this
    have hXBji : ∑ l, X j l * B l i = (-(1 / 2 : ℂ)) * (Q j i + (1 : Matrix (Fin n) (Fin n) ℂ) j i) := by
      have := congrFun (congrFun hXB j) i
      simpa [Matrix.mul_apply] using this
    have hQsym : (starRingEnd ℂ) (Q j i) = Q i j := by
      simp only [hQ, Matrix.of_apply]
      rw [← weightedDyadicForm_conj]
    have hconj : ∑ l, (starRingEnd ℂ) (X j l) * (starRingEnd ℂ) (B l i) =
        (starRingEnd ℂ) (∑ l, X j l * B l i) := by
      rw [map_sum]; simp [map_mul]
    have hδ : ∀ x : Fin n, (starRingEnd ℂ) (if x = j then (1 : ℂ) else 0) =
        if x = j then 1 else 0 := by
      intro x; split_ifs <;> simp
    have hBw : ∀ l j', weightedDyadicForm a (g l) (w j') = B l j' := fun l j' => by
      rw [hB, Matrix.of_apply]
    simp only [hδ, hBw, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_add_distrib, Finset.sum_comm (γ := Fin n)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hQij : weightedDyadicForm a (w i) (w j) = Q i j := by rw [hQ, Matrix.of_apply]
    rw [hQij, hconj, hXBji, hXBij, map_mul, map_add, hQsym, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, map_one, map_neg, map_div₀, map_ofNat]
      ring
    · rw [if_neg hij, if_neg (Ne.symm hij), if_neg hij]
      simp only [map_zero, map_neg, map_div₀, map_one, map_ofNat]
      ring


/-- Negative orthonormal families for the literal weighted form. -/
def IsWeightedNegOrthonormalWitnessFamily (a : ℝ) (n : ℕ) : Prop :=
  ∃ v : Fin n → ℝ → ℂ, (∀ i, IsWeightedFermiWitness a (v i)) ∧
    ∀ i j, weightedDyadicForm a (v i) (v j) = if i = j then -1 else 0

/-- Extended negative index of the source-defined weighted form. -/
def weightedWitnessNegIndex (a : ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : IsWeightedNegOrthonormalWitnessFamily a n), (n : ℕ∞)

theorem weightedWitnessNegIndex_half : weightedWitnessNegIndex (1 / 2) = witnessNegIndex := by
  simp only [weightedWitnessNegIndex, witnessNegIndex, IsWeightedNegOrthonormalWitnessFamily,
    IsNegOrthonormalWitnessFamily, isWeightedFermiWitness_half, weightedDyadicForm_half]

/-- Every finite dimension occurs once critical-line power witnesses are admitted. -/
theorem exists_weighted_negative_family_above_half {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (n : ℕ) : IsWeightedNegOrthonormalWitnessFamily a n := by
  obtain ⟨T₀, _, hT⟩ := exists_riemannZeta_line_zero_dyadic
  let S : Set ℝ := {t | riemannZeta (linePt t) = 0}
  have hInf : S.Infinite := Set.infinite_of_not_bddAbove (by
    rintro ⟨M, hM⟩
    obtain ⟨t, ht, hz⟩ := hT (max T₀ (M + 1)) (le_max_left _ _)
    have hle := hM hz
    have hlow := le_max_right T₀ (M + 1)
    linarith [ht.1])
  let e : ℕ ↪ S := Set.Infinite.natEmbedding S hInf
  let ρ : Fin n → ℂ := fun i => linePt (e i).val
  have hinj : Function.Injective ρ := by
    intro i j hij
    apply Fin.val_injective
    apply e.injective
    apply Subtype.ext
    have h := congrArg Complex.im hij
    simpa only [ρ, linePt_im] using h
  exact exists_weightedDyadicForm_neg_orthonormal (by linarith) ha1 ρ hinj
    (fun i => (e i).property)
    (fun i => by dsimp [ρ]; rw [linePt_re]; linarith)
    (fun i => by dsimp [ρ]; rw [linePt_re]; norm_num)

/-- The weighted negative index is infinite throughout the supercritical parameter interval. -/
theorem weightedWitnessNegIndex_eq_top_of_half_lt {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    weightedWitnessNegIndex a = ⊤ := by
  apply top_unique
  rw [← ENat.iSup_natCast]
  refine iSup_le fun n => ?_
  exact le_iSup₂_of_le n (exists_weighted_negative_family_above_half ha ha1 n) le_rfl

/-- Canonical RH index and unconditional infinite index on every strictly larger admissible weight. -/
theorem weightedWitnessNegIndex_boundary_profile :
    (RiemannHypothesis ↔ weightedWitnessNegIndex (1 / 2) = 0) ∧
    ∀ a ∈ Ioo (1 / 2 : ℝ) 1, weightedWitnessNegIndex a = ⊤ := by
  constructor
  · rw [weightedWitnessNegIndex_half]
    exact riemannHypothesis_iff_witnessNegIndex_eq_zero
  · intro a ha
    exact weightedWitnessNegIndex_eq_top_of_half_lt ha.1 ha.2

end RHTower
