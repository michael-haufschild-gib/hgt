import GaloisForLFunctions.RHTower.FermiNymanWitnessSelfSimilarityCriterion
import Mathlib.LinearAlgebra.Lagrange
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted

/-!
# Every off-line zero forces a negative direction of the dyadic Hermitian form

On the witness class of the alternating Nyman–Beurling system (`IsFermiNymanWitness`) consider the
Hermitian form

`q(u, v) = ∫_0^{1/2} u v̄ − ½ ∫_0^1 u v̄`

(`q(w, w) = ½(‖w(·/2)‖² − ‖w‖²)`, the defect of the dyadic dilation from being an isometry).
The spurious witnesses `g_k = t^{−2πik/log 2}` are self-similar, so `q` vanishes identically on
their span; a zero `ρ` with `½ < Re ρ < 1` gives the witness `w_ρ = t^{ρ̄−1}` with cross term
`q(g_k, w_ρ) = (2^{−ρ} − ½)/(ρ − 2πik/log 2)`.  For `n` distinct such zeros the `n × n` cross matrix
is a nonsingular Cauchy matrix, so the vectors `v_i = w_i + Σ_l X_{il} g_{k_l}` with
`X = −½(Q + 1)B^{−1}` satisfy `q(v_i, v_j) = −δ_{ij}`.

Hence the negative index of `q` on the witness class is at least the number of zeros of `ζ` in
`½ < Re s < 1`, and it vanishes under RH: RH is the vanishing of one signature, and each off-line zero
contributes at least one to it.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## The dyadic Hermitian form -/

/-- `q(u, v) = ∫_0^{1/2} u v̄ − ½ ∫_0^1 u v̄`. -/
def dyadicForm (u v : ℝ → ℂ) : ℂ :=
  (∫ t in Ioc (0 : ℝ) (1 / 2), u t * (starRingEnd ℂ) (v t)) -
    (1 / 2 : ℂ) * ∫ t in Ioc (0 : ℝ) 1, u t * (starRingEnd ℂ) (v t)

theorem dyadicForm_conj (u v : ℝ → ℂ) :
    dyadicForm v u = (starRingEnd ℂ) (dyadicForm u v) := by
  unfold dyadicForm
  rw [map_sub, map_mul, ← integral_conj, ← integral_conj]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp [mul_comm]
  · congr 1
    · rw [map_div₀, map_one]; exact congrArg _ (map_ofNat (starRingEnd ℂ) 2).symm
    · refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
      simp [mul_comm]

/-- **Sesquilinear expansion** over a finite family with pairwise integrable products. -/
theorem dyadicForm_sum_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ) (a b : ι → ℂ)
    (hint : ∀ i j, IntegrableOn (fun t => f i t * (starRingEnd ℂ) (f j t)) (Ioc 0 1)) :
    dyadicForm (fun t => ∑ i, a i * f i t) (fun t => ∑ j, b j * f j t) =
      ∑ i, ∑ j, a i * (starRingEnd ℂ) (b j) * dyadicForm (f i) (f j) := by
  have hsub : Ioc (0 : ℝ) (1 / 2) ⊆ Ioc 0 1 := Ioc_subset_Ioc_right (by norm_num)
  have hexp : ∀ t, (∑ i, a i * f i t) * (starRingEnd ℂ) (∑ j, b j * f j t) =
      ∑ i, ∑ j, a i * (starRingEnd ℂ) (b j) * (f i t * (starRingEnd ℂ) (f j t)) := by
    intro t
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  have hI : ∀ (s : Set ℝ), s ⊆ Ioc 0 1 →
      (∫ t in s, (∑ i, a i * f i t) * (starRingEnd ℂ) (∑ j, b j * f j t)) =
        ∑ i, ∑ j, a i * (starRingEnd ℂ) (b j) * ∫ t in s, f i t * (starRingEnd ℂ) (f j t) := by
    intro s hs
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
      ((hint i j).mono_set hs).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => ((hint i j).mono_set hs).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_const_mul _ _
  unfold dyadicForm
  rw [hI _ hsub, hI _ subset_rfl, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `q` vanishes on a dyadically self-similar product. -/
theorem dyadicForm_eq_zero_of_selfSimilar {u v : ℝ → ℂ}
    (h : ∀ t ∈ Ioc (0 : ℝ) 1, u (t / 2) * (starRingEnd ℂ) (v (t / 2)) =
      u t * (starRingEnd ℂ) (v t)) : dyadicForm u v = 0 := by
  have hc := integral_Ioc_comp_half (fun t => u t * (starRingEnd ℂ) (v t))
  have hcongr : (∫ t in Ioc (0 : ℝ) 1, u (t / 2) * (starRingEnd ℂ) (v (t / 2))) =
      ∫ t in Ioc (0 : ℝ) 1, u t * (starRingEnd ℂ) (v t) :=
    setIntegral_congr_fun measurableSet_Ioc h
  rw [hcongr] at hc
  unfold dyadicForm
  rw [hc]
  simp only [real_smul, Complex.ofReal_ofNat]
  ring

/-- The spurious witness `g_k = t^{s̄_k − 1}`. -/
def spuriousWitness (k : ℤ) : ℝ → ℂ := powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k))

theorem dyadicForm_spurious_spurious (k l : ℤ) :
    dyadicForm (spuriousWitness k) (spuriousWitness l) = 0 := by
  refine dyadicForm_eq_zero_of_selfSimilar (fun t ht => ?_)
  unfold spuriousWitness
  rw [powerWitness_spurious_half k ht.1, powerWitness_spurious_half l ht.1]

/-! ## Cauchy matrices -/

/-- **A Cauchy system with distinct nodes has only the trivial solution:** if
`Σ_j y_j/(a_j − b_l) = 0` for `n` distinct `b_l`, with the `a_j` distinct and off the `b_l`, then
`y = 0`.  The polynomial `Σ_j y_j Π_{m≠j}(a_m − X)` has degree `< n` and vanishes at every `b_l`. -/
theorem eq_zero_of_cauchy_sum_eq_zero {n : ℕ} {a b : Fin n → ℂ} (ha : Function.Injective a)
    (hb : Function.Injective b) (hab : ∀ j l, a j ≠ b l) {y : Fin n → ℂ}
    (hy : ∀ l, ∑ j, y j / (a j - b l) = 0) : y = 0 := by
  classical
  set P : Polynomial ℂ := ∑ j, Polynomial.C (y j) *
    ∏ m ∈ Finset.univ.erase j, (Polynomial.C (a m) - Polynomial.X) with hP
  have hdeg : P.degree < ((Finset.univ : Finset (Fin n)).image b).card := by
    rw [Finset.card_image_of_injective _ hb, Finset.card_univ, Fintype.card_fin]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : P = 0 := by rw [hP]; simp
      rw [this, Polynomial.degree_zero]; exact WithBot.bot_lt_coe 0
    · refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le (n := n - 1) ?_)
        (by exact_mod_cast Nat.sub_lt hn one_pos)
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      have h1 : ∀ m ∈ Finset.univ.erase j,
          (Polynomial.C (a m) - Polynomial.X).natDegree ≤ 1 := fun m _ =>
        (Polynomial.natDegree_sub_le _ _).trans (by simp)
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin]
  have heval : ∀ x ∈ (Finset.univ : Finset (Fin n)).image b, P.eval x = 0 := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hx
    rw [hP, Polynomial.eval_finsetSum]
    have hterm : ∀ j, Polynomial.eval (b l) (Polynomial.C (y j) *
        ∏ m ∈ Finset.univ.erase j, (Polynomial.C (a m) - Polynomial.X)) =
        (∏ m, (a m - b l)) * (y j / (a j - b l)) := by
      intro j
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      have hne : a j - b l ≠ 0 := sub_ne_zero.2 (hab j l)
      field_simp
    simp_rw [hterm]
    rw [← Finset.mul_sum, hy l, mul_zero]
  have hP0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero _ hdeg heval
  funext j
  have hj := congrArg (Polynomial.eval (a j)) hP0
  rw [hP, Polynomial.eval_finsetSum, Polynomial.eval_zero,
    Finset.sum_eq_single j] at hj
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hj
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X] at hj
    have hprod : ∏ m ∈ Finset.univ.erase j, (a m - a j) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 (fun m hm => sub_ne_zero.2 ?_)
      intro h; exact (Finset.ne_of_mem_erase hm) (ha h)
    simpa [hprod] using hj
  · intro i _ hij
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := j)
      (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩) ?_)
    simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## Finite combinations of witnesses -/

theorem isFermiNymanWitness_zero : IsFermiNymanWitness (fun _ => (0 : ℂ)) := by
  refine ⟨continuousOn_const, ?_, fun a _ => by simp⟩
  simp only [norm_zero]
  exact (integrableOn_zero).congr_fun (fun t _ => by norm_num) measurableSet_Ioc

theorem isFermiNymanWitness_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (c : ι → ℂ)
    (hf : ∀ i ∈ s, IsFermiNymanWitness (f i)) :
    IsFermiNymanWitness (fun t => ∑ i ∈ s, c i * f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isFermiNymanWitness_zero
  | insert i s hi ih =>
    have h1 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have h2 := h1.add_smul (hf i (Finset.mem_insert_self i s)) (c i)
    refine (show (fun t => ∑ j ∈ insert i s, c j * f j t) =
      (fun t => (∑ j ∈ s, c j * f j t) + c i * f i t) from ?_) ▸ h2
    funext t
    rw [Finset.sum_insert hi, add_comm]

/-! ## The negative orthonormal family -/

/-- The node `d_l = 1 − s̄_{l+1} = 2πi(l+1)/log 2` of the `l`-th spurious witness. -/
def spuriousNode (l : ℕ) : ℂ := 1 - (starRingEnd ℂ) (dyadicSpuriousMode ((l : ℤ) + 1))

theorem spuriousNode_re (l : ℕ) : (spuriousNode l).re = 0 := by
  simp [spuriousNode, Complex.conj_re, dyadicSpuriousMode_re]

theorem spuriousNode_im (l : ℕ) : (spuriousNode l).im = 2 * Real.pi * ((l : ℝ) + 1) / Real.log 2 := by
  simp [spuriousNode, Complex.conj_im, dyadicSpuriousMode_im]

theorem spuriousNode_injective : Function.Injective spuriousNode := by
  intro l m h
  have := congrArg Complex.im h
  rw [spuriousNode_im, spuriousNode_im] at this
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : ((l : ℝ) + 1) = ((m : ℝ) + 1) := by
    field_simp at this
    nlinarith [this]
  exact_mod_cast (by linarith : (l : ℝ) = m)

/-- **Each off-line zero forces a negative direction.**  For `n` distinct zeros of `ζ` in
`½ < Re s < 1` there are `n` witnesses of the alternating Nyman–Beurling system that are
orthonormal for `−q`. -/
theorem exists_dyadicForm_neg_orthonormal {n : ℕ} (ρ : Fin n → ℂ) (hinj : Function.Injective ρ)
    (hζ : ∀ j, riemannZeta (ρ j) = 0) (h1 : ∀ j, 1 / 2 < (ρ j).re) (h2 : ∀ j, (ρ j).re < 1) :
    ∃ v : Fin n → ℝ → ℂ, (∀ i, IsFermiNymanWitness (v i)) ∧
      ∀ i j, dyadicForm (v i) (v j) = if i = j then -1 else 0 := by
  classical
  set w : Fin n → ℝ → ℂ := fun j => powerWitness ((starRingEnd ℂ) (ρ j)) with hw
  set g : Fin n → ℝ → ℂ := fun l => spuriousWitness ((l : ℕ) + 1 : ℤ) with hg
  have hwW : ∀ j, IsFermiNymanWitness (w j) := fun j =>
    isFermiNymanWitness_powerWitness_of_zeta_eq_zero (hζ j) (h1 j) (h2 j)
  have hgW : ∀ l, IsFermiNymanWitness (g l) := fun l =>
    isFermiNymanWitness_spurious (by omega)
  set c : Fin n → ℂ := fun j => (2 : ℂ) ^ (-ρ j) - 1 / 2 with hc
  have hc0 : ∀ j, c j ≠ 0 := fun j => two_cpow_neg_ne_half (h2 j)
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun l j => dyadicForm (g l) (w j) with hB
  set Q : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => dyadicForm (w i) (w j) with hQ
  have hBval : ∀ l j, B l j = c j / (ρ j - spuriousNode (l : ℕ)) := by
    intro l j
    simp only [hB, Matrix.of_apply, hg, hw, spuriousWitness, dyadicForm, hc, spuriousNode]
    rw [crossTerm_spurious_zeroWitness _ (by linarith [h1 j])]
    congr 1
    ring
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hy0
    have hcy : (fun j => c j * y j) = 0 := by
      refine eq_zero_of_cauchy_sum_eq_zero (a := ρ) (b := fun l : Fin n => spuriousNode l)
        hinj (spuriousNode_injective.comp Fin.val_injective) (fun j l => ?_) (fun l => ?_)
      · intro h
        have := congrArg Complex.re h
        rw [spuriousNode_re] at this
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
  have hfW : ∀ a, IsFermiNymanWitness (f a) := by
    intro a; cases a with
    | inl j => exact hwW j
    | inr l => exact hgW l
  set α : Fin n → Fin n ⊕ Fin n → ℂ :=
    fun i => Sum.elim (fun i' => if i' = i then 1 else 0) (fun l => X i l) with hα
  set v : Fin n → ℝ → ℂ := fun i t => ∑ a, α i a * f a t with hv
  refine ⟨v, fun i => ?_, fun i j => ?_⟩
  · exact isFermiNymanWitness_finsetSum Finset.univ f (α i) (fun a _ => hfW a)
  · have hint : ∀ a b, IntegrableOn (fun t => f a t * (starRingEnd ℂ) (f b t)) (Ioc 0 1) :=
      fun a b => (hfW a).integrableOn_mul_conj_witness (hfW b)
    rw [show v i = fun t => ∑ a, α i a * f a t from rfl,
      show v j = fun t => ∑ a, α j a * f a t from rfl, dyadicForm_sum_sum f (α i) (α j) hint]
    have hgg : ∀ l l', dyadicForm (g l) (g l') = 0 := fun l l' =>
      dyadicForm_spurious_spurious _ _
    have hwg : ∀ i' l, dyadicForm (w i') (g l) = (starRingEnd ℂ) (B l i') := by
      intro i' l
      rw [hB, Matrix.of_apply, dyadicForm_conj]
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
      rw [← dyadicForm_conj]
    have hconj : ∑ l, (starRingEnd ℂ) (X j l) * (starRingEnd ℂ) (B l i) =
        (starRingEnd ℂ) (∑ l, X j l * B l i) := by
      rw [map_sum]; simp [map_mul]
    have hδ : ∀ x : Fin n, (starRingEnd ℂ) (if x = j then (1 : ℂ) else 0) =
        if x = j then 1 else 0 := by
      intro x; split_ifs <;> simp
    have hBw : ∀ l j', dyadicForm (g l) (w j') = B l j' := fun l j' => by
      rw [hB, Matrix.of_apply]
    simp only [hδ, hBw, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_add_distrib, Finset.sum_comm (γ := Fin n)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hQij : dyadicForm (w i) (w j) = Q i j := by rw [hQ, Matrix.of_apply]
    rw [hQij, hconj, hXBji, hXBij, map_mul, map_add, hQsym, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, map_one, map_neg, map_div₀, map_ofNat]
      ring
    · rw [if_neg hij, if_neg (Ne.symm hij), if_neg hij]
      simp only [map_zero, map_neg, map_div₀, map_one, map_ofNat]
      ring

/-! ## The negative index -/

/-- The zeros of `ζ` with `½ < Re ρ < 1`. -/
def rightStripZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1}

/-- There are `n` witnesses orthonormal for `−q`. -/
def IsNegOrthonormalWitnessFamily (n : ℕ) : Prop :=
  ∃ v : Fin n → ℝ → ℂ, (∀ i, IsFermiNymanWitness (v i)) ∧
    ∀ i j, dyadicForm (v i) (v j) = if i = j then -1 else 0

/-- The negative index of the dyadic Hermitian form on the witness class. -/
def witnessNegIndex : ℕ∞ := ⨆ (n : ℕ) (_ : IsNegOrthonormalWitnessFamily n), (n : ℕ∞)

theorem isNegOrthonormalWitnessFamily_of_finset (s : Finset ℂ) (hs : ↑s ⊆ rightStripZeros) :
    IsNegOrthonormalWitnessFamily s.card := by
  set e := s.equivFin
  have hmem : ∀ i, ((e.symm i : ℂ)) ∈ rightStripZeros := fun i => hs (e.symm i).2
  exact exists_dyadicForm_neg_orthonormal (fun i => (e.symm i : ℂ))
    (Subtype.val_injective.comp e.symm.injective) (fun i => (hmem i).1) (fun i => (hmem i).2.1)
    (fun i => (hmem i).2.2)

/-- **Every zero in `½ < Re s < 1` contributes to the negative index.** -/
theorem encard_rightStripZeros_le_witnessNegIndex : rightStripZeros.encard ≤ witnessNegIndex := by
  by_contra hlt
  rw [not_le] at hlt
  have hW : witnessNegIndex ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨m, hm0⟩ := WithTop.ne_top_iff_exists.1 hW
  have hm : ((m : ℕ) : ℕ∞) = witnessNegIndex := hm0
  have hk : ((m + 1 : ℕ) : ℕ∞) ≤ rightStripZeros.encard := by
    rw [← hm] at hlt
    exact_mod_cast Order.add_one_le_of_lt hlt
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hk
  have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
  have hcard : htfin.toFinset.card = m + 1 := by
    have := htfin.encard_eq_coe_toFinset_card
    rw [htc] at this
    exact_mod_cast this.symm
  have hfam := isNegOrthonormalWitnessFamily_of_finset htfin.toFinset (by simpa using hts)
  rw [hcard] at hfam
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ witnessNegIndex :=
    le_iSup₂_of_le (f := fun n (_ : IsNegOrthonormalWitnessFamily n) => (n : ℕ∞)) (m + 1) hfam
      le_rfl
  rw [← hm] at hle
  have : m + 1 ≤ m := by exact_mod_cast hle
  omega

theorem dyadicForm_self (v : ℝ → ℂ) :
    dyadicForm v v = (((∫ t in Ioc (0 : ℝ) (1 / 2), ‖v t‖ ^ 2) -
      (1 / 2) * ∫ t in Ioc (0 : ℝ) 1, ‖v t‖ ^ 2 : ℝ) : ℂ) := by
  unfold dyadicForm
  have h : ∀ t, v t * (starRingEnd ℂ) (v t) = ((‖v t‖ ^ 2 : ℝ) : ℂ) := fun t => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [h]
  rw [integral_complex_ofReal, integral_complex_ofReal]
  push_cast
  ring

/-- Under RH the dyadic form has no negative direction on the witness class. -/
theorem witnessNegIndex_eq_zero_of_rh (hRH : RiemannHypothesis) : witnessNegIndex = 0 := by
  refine le_antisymm (iSup₂_le fun n hn => ?_) zero_le
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · exfalso
    obtain ⟨v, hvW, hvq⟩ := hn
    have h0 := hvq ⟨0, hpos⟩ ⟨0, hpos⟩
    have hhalf := riemannHypothesis_iff_fermiNymanWitness_halfMass.1 hRH (v ⟨0, hpos⟩) (hvW _)
    rw [dyadicForm_self, hhalf, if_pos rfl] at h0
    norm_num at h0

/-- **RH is the vanishing of the negative index of the dyadic Hermitian form on the witness class**,
and every zero in `½ < Re s < 1` contributes at least one to it. -/
theorem riemannHypothesis_iff_witnessNegIndex_eq_zero : RiemannHypothesis ↔ witnessNegIndex = 0 := by
  refine ⟨witnessNegIndex_eq_zero_of_rh, fun h => ?_⟩
  by_contra hRH
  obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hle := encard_rightStripZeros_le_witnessNegIndex
  rw [h, nonpos_iff_eq_zero, Set.encard_eq_zero] at hle
  have hmem : ρ ∈ rightStripZeros := ⟨hζ, h1, h2⟩
  rw [hle] at hmem
  exact hmem

/-! ## The quantum margin -/

theorem conj_mem_rightStripZeros {ρ : ℂ} (h : ρ ∈ rightStripZeros) :
    (starRingEnd ℂ) ρ ∈ rightStripZeros := by
  obtain ⟨hζ, h1, h2⟩ := h
  refine ⟨?_, by rwa [Complex.conj_re], by rwa [Complex.conj_re]⟩
  rw [riemannZeta_conj, hζ, map_zero]

/-- Off-line zeros come in conjugate pairs: without RH there are at least two in `½ < Re s < 1`. -/
theorem two_le_encard_rightStripZeros_of_not_rh (hRH : ¬ RiemannHypothesis) :
    2 ≤ rightStripZeros.encard := by
  obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hmem : ρ ∈ rightStripZeros := ⟨hζ, h1, h2⟩
  have hne : ρ ≠ (starRingEnd ℂ) ρ := by
    intro h
    have him : ρ.im = 0 := by
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    exact riemannZeta_ne_zero_of_abs_im_lt_four (by linarith) h2 (by rw [him, abs_zero]; norm_num) hζ
  have hsub : ({ρ, (starRingEnd ℂ) ρ} : Set ℂ) ⊆ rightStripZeros := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hmem
    · exact conj_mem_rightStripZeros hmem
  calc (2 : ℕ∞) = ({ρ, (starRingEnd ℂ) ρ} : Set ℂ).encard := (Set.encard_pair hne).symm
    _ ≤ rightStripZeros.encard := Set.encard_le_encard hsub

/-- **The full quantum margin.**  The negative index is `0` or at least `2`; RH holds as soon as it
is at most `1`. -/
theorem riemannHypothesis_iff_witnessNegIndex_le_one : RiemannHypothesis ↔ witnessNegIndex ≤ 1 := by
  refine ⟨fun hRH => by rw [witnessNegIndex_eq_zero_of_rh hRH]; exact zero_le, fun h => ?_⟩
  by_contra hRH
  have h2 := (two_le_encard_rightStripZeros_of_not_rh hRH).trans
    (encard_rightStripZeros_le_witnessNegIndex.trans h)
  exact absurd h2 (by norm_num)

end RHTower
