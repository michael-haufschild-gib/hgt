import GaloisForLFunctions.HTGeometry.RegularizedDeterminantScaling
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEntire
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# Hilbert--Schmidt block doubles

This module constructs literal block kernels on doubled index types. It proves Hilbert--Schmidt
closure and exact compatibility with kernel composition. These are the operator-level ingredients
for sign-paired regularized determinants.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry
open Metric

namespace HilbertSchmidt

noncomputable section

variable {ι : Type*}

/-- The block-diagonal kernel with blocks K and L. -/
def blockDouble (K L : ι × ι → ℂ) :
    (ι ⊕ ι) × (ι ⊕ ι) → ℂ
  | (Sum.inl i, Sum.inl j) => K (i, j)
  | (Sum.inr i, Sum.inr j) => L (i, j)
  | _ => 0

/-- Reindex the doubled matrix entries into its four matrix blocks. -/
def blockDoubleIndexEquiv :
    ((ι ⊕ ι) × (ι ⊕ ι)) ≃
      (ι × ι) ⊕ ((ι × ι) ⊕ ((ι × ι) ⊕ (ι × ι))) where
  toFun
    | (Sum.inl i, Sum.inl j) => Sum.inl (i, j)
    | (Sum.inl i, Sum.inr j) => Sum.inr (Sum.inl (i, j))
    | (Sum.inr i, Sum.inl j) => Sum.inr (Sum.inr (Sum.inl (i, j)))
    | (Sum.inr i, Sum.inr j) => Sum.inr (Sum.inr (Sum.inr (i, j)))
  invFun
    | Sum.inl (i, j) => (Sum.inl i, Sum.inl j)
    | Sum.inr (Sum.inl (i, j)) => (Sum.inl i, Sum.inr j)
    | Sum.inr (Sum.inr (Sum.inl (i, j))) => (Sum.inr i, Sum.inl j)
    | Sum.inr (Sum.inr (Sum.inr (i, j))) => (Sum.inr i, Sum.inr j)
  left_inv := by
    intro x
    rcases x with ⟨i, j⟩
    cases i <;> cases j <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl p => rfl
    | inr x =>
      cases x with
      | inl p => rfl
      | inr x =>
        cases x with
        | inl p => rfl
        | inr p => rfl

/-- A literal block double of Hilbert--Schmidt kernels is Hilbert--Schmidt. -/
theorem isHS_blockDouble {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    IsHS (blockDouble K L) := by
  rw [IsHS]
  refine (Equiv.summable_iff
    (f := fun p : (ι ⊕ ι) × (ι ⊕ ι) => ‖blockDouble K L p‖ ^ 2)
    blockDoubleIndexEquiv.symm).mp ?_
  apply Summable.sum
  · simpa [IsHS, Function.comp_def, blockDouble, blockDoubleIndexEquiv] using hK
  · apply Summable.sum
    · simp [Function.comp_def, blockDouble, blockDoubleIndexEquiv]
    · apply Summable.sum
      · simp [Function.comp_def, blockDouble, blockDoubleIndexEquiv]
      · simpa [IsHS, Function.comp_def, blockDouble, blockDoubleIndexEquiv] using hL

/-- Taking the Hilbert--Schmidt adjoint preserves the literal block decomposition. -/
theorem hsAdjoint_blockDouble (K L : ι × ι → ℂ) :
    hsAdjoint (blockDouble K L) = blockDouble (hsAdjoint K) (hsAdjoint L) := by
  funext p
  rcases p with ⟨i, j⟩
  cases i <;> cases j <;> simp [hsAdjoint, blockDouble]

/-- A literal block double of Hermitian Hilbert--Schmidt kernels represents a self-adjoint
operator. -/
theorem isSelfAdjoint_toOperator_blockDouble [DecidableEq ι] {K L : ι × ι → ℂ}
    (hK : IsHS K) (hL : IsHS L) (hKself : hsAdjoint K = K)
    (hLself : hsAdjoint L = L) :
    IsSelfAdjoint (toOperator (isHS_blockDouble hK hL)) := by
  refine ContinuousLinearMap.isSelfAdjoint_iff'.mpr ?_
  rw [adjoint_toOperator]
  exact toOperator_congr _ _ (by rw [hsAdjoint_blockDouble, hKself, hLself])

private theorem tsum_sum_inl_zero {κ : Type*} {f : ι → ℂ} (hf : Summable f) :
    (∑' x : ι ⊕ κ, Sum.elim f (fun _ => 0) x) = ∑' i, f i := by
  let g : ι ⊕ κ → ℂ := Sum.elim f (fun _ : κ => 0)
  change (∑' x : ι ⊕ κ, g x) = ∑' i, f i
  have hleft : HasSum (g ∘ (Sum.inl : ι → ι ⊕ κ)) (∑' i, f i) := by
    simpa only [Function.comp_def, g, Sum.elim_inl] using hf.hasSum
  have hright : HasSum (g ∘ (Sum.inr : κ → ι ⊕ κ)) 0 := by
    simpa only [Function.comp_def, g, Sum.elim_inr] using
      (hasSum_zero : HasSum (fun _ : κ => (0 : ℂ)) 0)
  simpa using (hleft.sum hright).tsum_eq

private theorem tsum_sum_inr_zero {κ : Type*} {f : κ → ℂ} (hf : Summable f) :
    (∑' x : ι ⊕ κ, Sum.elim (fun _ => 0) f x) = ∑' i, f i := by
  let g : ι ⊕ κ → ℂ := Sum.elim (fun _ : ι => 0) f
  change (∑' x : ι ⊕ κ, g x) = ∑' i, f i
  have hleft : HasSum (g ∘ (Sum.inl : ι → ι ⊕ κ)) 0 := by
    simpa only [Function.comp_def, g, Sum.elim_inl] using
      (hasSum_zero : HasSum (fun _ : ι => (0 : ℂ)) 0)
  have hright : HasSum (g ∘ (Sum.inr : κ → ι ⊕ κ)) (∑' i, f i) := by
    simpa only [Function.comp_def, g, Sum.elim_inr] using hf.hasSum
  simpa using (hleft.sum hright).tsum_eq

private theorem tsum_sum_elim {κ : Type*} {f : ι → ℂ} {g : κ → ℂ}
    (hf : Summable f) (hg : Summable g) :
    (∑' x : ι ⊕ κ, Sum.elim f g x) = (∑' i, f i) + ∑' j, g j := by
  let h : ι ⊕ κ → ℂ := Sum.elim f g
  change (∑' x : ι ⊕ κ, h x) = (∑' i, f i) + ∑' j, g j
  have hleft : HasSum (h ∘ (Sum.inl : ι → ι ⊕ κ)) (∑' i, f i) := by
    simpa only [Function.comp_def, h, Sum.elim_inl] using hf.hasSum
  have hright : HasSum (h ∘ (Sum.inr : κ → ι ⊕ κ)) (∑' j, g j) := by
    simpa only [Function.comp_def, h, Sum.elim_inr] using hg.hasSum
  exact (hleft.sum hright).tsum_eq

/-- Composition of literal block doubles is blockwise composition. -/
theorem hsComp_blockDouble {K L K' L' : ι × ι → ℂ}
    (hK : IsHS K) (hL : IsHS L) (hK' : IsHS K') (hL' : IsHS L') :
    hsComp (blockDouble K L) (blockDouble K' L') =
      blockDouble (hsComp K K') (hsComp L L') := by
  funext p
  rcases p with ⟨i | i, j | j⟩
  · change (∑' k : ι ⊕ ι,
      blockDouble K L (Sum.inl i, k) *
        blockDouble K' L' (k, Sum.inl j)) =
        hsComp K K' (i, j)
    rw [show (fun k : ι ⊕ ι =>
      blockDouble K L (Sum.inl i, k) *
        blockDouble K' L' (k, Sum.inl j)) =
        Sum.elim (fun k : ι => K (i, k) * K' (k, j)) (fun _ => 0) by
          funext k
          cases k <;> simp [blockDouble]]
    rw [tsum_sum_inl_zero (hsComp_summable hK hK' i j)]
    rfl
  · change (∑' k : ι ⊕ ι,
      blockDouble K L (Sum.inl i, k) *
        blockDouble K' L' (k, Sum.inr j)) = 0
    have hzero : (fun k : ι ⊕ ι =>
        blockDouble K L (Sum.inl i, k) *
          blockDouble K' L' (k, Sum.inr j)) = 0 := by
      funext k
      cases k <;> simp [blockDouble]
    rw [hzero]
    exact tsum_zero
  · change (∑' k : ι ⊕ ι,
      blockDouble K L (Sum.inr i, k) *
        blockDouble K' L' (k, Sum.inl j)) = 0
    have hzero : (fun k : ι ⊕ ι =>
        blockDouble K L (Sum.inr i, k) *
          blockDouble K' L' (k, Sum.inl j)) = 0 := by
      funext k
      cases k <;> simp [blockDouble]
    rw [hzero]
    exact tsum_zero
  · change (∑' k : ι ⊕ ι,
      blockDouble K L (Sum.inr i, k) *
        blockDouble K' L' (k, Sum.inr j)) =
        hsComp L L' (i, j)
    rw [show (fun k : ι ⊕ ι =>
      blockDouble K L (Sum.inr i, k) *
        blockDouble K' L' (k, Sum.inr j)) =
        Sum.elim (fun _ => 0) (fun k : ι => L (i, k) * L' (k, j)) by
          funext k
          cases k <;> simp [blockDouble]]
    rw [tsum_sum_inr_zero (hsComp_summable hL hL' i j)]
    rfl

/-- Every Hilbert--Schmidt power of a block double remains a block double of the
corresponding powers. -/
theorem hsPow_blockDouble {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    ∀ n : ℕ, hsPow (blockDouble K L) n =
      blockDouble (hsPow K n) (hsPow L n)
  | 0 => rfl
  | n + 1 => by
    rw [hsPow, hsPow_blockDouble hK hL n, hsPow, hsPow]
    exact hsComp_blockDouble hK hL (isHS_hsPow hK n) (isHS_hsPow hL n)

/-- The trace of every trace-class power of a block double is the sum of the
two block traces. -/
theorem hsTrace_hsPow_blockDouble_succ {K L : ι × ι → ℂ}
    (hK : IsHS K) (hL : IsHS L) (n : ℕ) :
    (∑' i : ι ⊕ ι, hsPow (blockDouble K L) (n + 1) (i, i)) =
      (∑' i : ι, hsPow K (n + 1) (i, i)) +
        ∑' i : ι, hsPow L (n + 1) (i, i) := by
  rw [hsPow_blockDouble hK hL]
  rw [show (fun i : ι ⊕ ι =>
      blockDouble (hsPow K (n + 1)) (hsPow L (n + 1)) (i, i)) =
      Sum.elim (fun i : ι => hsPow K (n + 1) (i, i))
        (fun i : ι => hsPow L (n + 1) (i, i)) by
          funext i
          cases i <;> simp [blockDouble]]
  apply tsum_sum_elim
  · simpa [hsPow, hsComp] using
      (hsComp_diag_summable hK (isHS_hsPow hK n)).prod
  · simpa [hsPow, hsComp] using
      (hsComp_diag_summable hL (isHS_hsPow hL n)).prod

/-- On a common convergence disc, the Hilbert--Carleman exponent of a literal
block double is the sum of its block exponents. -/
theorem fredholmExp_blockDouble {K L : ι × ι → ℂ}
    (hK : IsHS K) (hL : IsHS L) (z : ℂ)
    (hzK : ‖z‖ * hsNorm K < 1) (hzL : ‖z‖ * hsNorm L < 1) :
    fredholmExp (blockDouble K L) z = fredholmExp K z + fredholmExp L z := by
  let a : ℕ → ℂ := fun n =>
    z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) *
      (∑' i : ι, hsPow K (n + 1) (i, i))
  let b : ℕ → ℂ := fun n =>
    z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) *
      (∑' i : ι, hsPow L (n + 1) (i, i))
  have ha : Summable a := by
    simpa [a] using fredholmExp_summable hK z hzK
  have hb : Summable b := by
    simpa [b] using fredholmExp_summable hL z hzL
  unfold fredholmExp
  change (∑' n : ℕ, _) = (∑' n, a n) + ∑' n, b n
  rw [show (fun n : ℕ =>
      z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) *
        (∑' i : ι ⊕ ι, hsPow (blockDouble K L) (n + 1) (i, i))) =
      fun n => a n + b n by
        funext n
        rw [hsTrace_hsPow_blockDouble_succ hK hL]
        simp only [a, b]
        ring]
  exact ha.tsum_add hb

/-- On a common convergence disc, the regularized Fredholm determinant of a
literal block double is the product of the block determinants. -/
theorem fredholmDet_blockDouble {K L : ι × ι → ℂ}
    (hK : IsHS K) (hL : IsHS L) (z : ℂ)
    (hzK : ‖z‖ * hsNorm K < 1) (hzL : ‖z‖ * hsNorm L < 1) :
    fredholmDet (blockDouble K L) z = fredholmDet K z * fredholmDet L z := by
  rw [fredholmDet, fredholmDet, fredholmDet,
    fredholmExp_blockDouble hK hL z hzK hzL, neg_add, Complex.exp_add]

/-- The entire Hilbert--Carleman determinant of a literal block double factors
as the product of the entire block determinants. -/
theorem entireDet2_blockDouble [DecidableEq ι] {K L : ι × ι → ℂ}
    (hK : IsHS K) (hL : IsHS L) :
    entireDet2 (blockDouble K L) =
      fun z => entireDet2 K z * entireDet2 L z := by
  let hB : IsHS (blockDouble K L) := isHS_blockDouble hK hL
  obtain ⟨_, rB, hrB, hrBnorm, _⟩ := isRegularizedDet_entireDet2 hB
  obtain ⟨_, rK, hrK, hrKnorm, hKmatch⟩ := isRegularizedDet_entireDet2 hK
  obtain ⟨_, rL, hrL, hrLnorm, hLmatch⟩ := isRegularizedDet_entireDet2 hL
  let r : ℝ := min rB (min rK rL)
  have hr : 0 < r := lt_min hrB (lt_min hrK hrL)
  have hrB : r ≤ rB := min_le_left _ _
  have hrK : r ≤ rK := (min_le_right _ _).trans (min_le_left _ _)
  have hrL : r ≤ rL := (min_le_right _ _).trans (min_le_right _ _)
  refine (isRegularizedDet_entireDet2 hB).unique ?_
  refine ⟨(differentiable_entireDet2 hK).mul
    (differentiable_entireDet2 hL), r, hr, ?_, ?_⟩
  · exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hrB (hsNorm_nonneg _)) hrBnorm
  · intro z hz
    have hzK : z ∈ Metric.ball (0 : ℂ) rK :=
      Metric.ball_subset_ball hrK hz
    have hzL : z ∈ Metric.ball (0 : ℂ) rL :=
      Metric.ball_subset_ball hrL hz
    have hnormK : ‖z‖ * hsNorm K < 1 := by
      have hz' : ‖z‖ < rK := by rwa [mem_ball_zero_iff] at hzK
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hz'.le (hsNorm_nonneg K)) hrKnorm
    have hnormL : ‖z‖ * hsNorm L < 1 := by
      have hz' : ‖z‖ < rL := by rwa [mem_ball_zero_iff] at hzL
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hz'.le (hsNorm_nonneg L)) hrLnorm
    change entireDet2 K z * entireDet2 L z = fredholmDet (blockDouble K L) z
    rw [hKmatch z hzK, hLmatch z hzL]
    exact (fredholmDet_blockDouble hK hL z hnormK hnormL).symm

end

end HilbertSchmidt
