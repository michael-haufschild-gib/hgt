import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMetzlerDichotomy
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw

/-!
# The Frobenius ladder is Metzler

Calibration over `𝔽_q`. For a curve datum (normalized Frobenius eigenvalues `β_i`, point counts
`N_j = q^j + 1 − q^{j/2} Σ_i β_i^j`) the cycles `H, V, Γ_0, …, Γ_K` have the Gram matrix

    H² = V² = 0,  H·V = 1,  Γ_k·H = 1,  Γ_k·V = q^k,  Γ_k·Γ_l = q^{min(k,l)} N_{|k−l|}

(`frobeniusGram`). The three layers of Lorentzian theory separate as follows.

* **The block Hodge index theorem** (`isHyperbolic_fromBlocks_iff`). For any symmetric form with a
  hyperbolic pole plane, `Q[Sum.elim p d] = 2(p_H + d·V)(p_V + d·H) − δ(d)` with the polar defect
  `δ(d) = 2(d·H)(d·V) − d²`; so one positive square ⇔ `δ ≥ 0`. For curves:
  `frobeniusGram_isHyperbolic_iff` (⇔ the span defect of ArithmeticCastelnuovoSeveri is
  nonnegative), and unitary data are hyperbolic (`frobeniusGram_isHyperbolic_of_unitary`).
* **Bézout is the Metzler property** (`frobeniusGram_isMetzler_iff`): distinct graphs meet in
  `q^{min} N_{|k−l|}` points, so the Gram is Metzler iff the point counts are nonnegative. The
  sign hypothesis of Lorentzian theory is effectivity.
* **The trickle-down regime** (`frobeniusGram_mulVec_pos`, `frobeniusGram_isConnectedSupport`):
  every curve datum has a positive weight with positive image and connected support. Hence for
  every curve datum with nonnegative counts, Hodge index ⇔ (TD_π)
  (`frobeniusGram_isHyperbolic_iff_weightedTrickleDown`).
* **The fake curve separates sign from trickle-down** (`golden_not_weightedTrickleDown`). The
  golden datum (`q = 5`, `β = φ, φ⁻¹`) has positive counts, so its Gram is Metzler, connected and
  in the trickle-down regime, and it violates the Hodge index; therefore it violates (TD_π).

So over `𝔽_q` the degree-three lift of Lorentzian theory (hyperbolic links) exists exactly when
Weil's theorem holds, and the data a fake curve shares with a true one (integral nonnegative
counts, functional equation, Bézout) cannot construct it: the content of Weil's theorem in this
language is the trickle-down inequality, a negative semidefiniteness statement for
`Q − Q D⁻¹ Q`.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open ArithmeticCastelnuovoSeveri

variable {κ : Type*} [Fintype κ]

/-! ### The block Hodge index theorem -/

/-- The polar defect `δ(d) = 2(d·H)(d·V) − L[d]`, with `d·H = (Bd)_0`, `d·V = (Bd)_1`. -/
def polarDefect (B : Matrix (Fin 2) κ ℝ) (L : Matrix κ κ ℝ) (d : κ → ℝ) : ℝ :=
  2 * (B *ᵥ d) 0 * (B *ᵥ d) 1 - qf L d

theorem dotProduct_sumElim {α β : Type*} [Fintype α] [Fintype β] (u x : α → ℝ) (v y : β → ℝ) :
    Sum.elim u v ⬝ᵥ Sum.elim x y = u ⬝ᵥ x + v ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- **The polar split**: `Q[(p, d)] = 2(p_H + d·V)(p_V + d·H) − δ(d)`. -/
theorem qf_fromBlocks_pole (B : Matrix (Fin 2) κ ℝ) (L : Matrix κ κ ℝ) (p : Fin 2 → ℝ)
    (d : κ → ℝ) :
    qf (fromBlocks realPolePlane B Bᵀ L) (Sum.elim p d) =
      2 * (p 0 + (B *ᵥ d) 1) * (p 1 + (B *ᵥ d) 0) - polarDefect B L d := by
  have h1 : p ⬝ᵥ realPolePlane *ᵥ p = 2 * p 0 * p 1 := by
    simp [realPolePlane, dotProduct, mulVec, Fin.sum_univ_two]; ring
  have h2 : p ⬝ᵥ B *ᵥ d = p 0 * (B *ᵥ d) 0 + p 1 * (B *ᵥ d) 1 := by
    simp [dotProduct, Fin.sum_univ_two]
  have h3 : d ⬝ᵥ Bᵀ *ᵥ p = p 0 * (B *ᵥ d) 0 + p 1 * (B *ᵥ d) 1 := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]; exact h2
  unfold qf bil polarDefect
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_sumElim,
    dotProduct_add, dotProduct_add, h1, h2, h3]
  simp only [qf, bil]
  ring

/-- **The block Hodge index theorem.** A symmetric form with a hyperbolic pole plane has one
positive square iff its polar defect is nonnegative. -/
theorem isHyperbolic_fromBlocks_iff (B : Matrix (Fin 2) κ ℝ) {L : Matrix κ κ ℝ}
    (hL : L.IsSymm) :
    IsHyperbolic (fromBlocks realPolePlane B Bᵀ L) ↔ ∀ d, 0 ≤ polarDefect B L d := by
  have hG : (fromBlocks realPolePlane B Bᵀ L).IsSymm := by
    unfold Matrix.IsSymm
    rw [fromBlocks_transpose, transpose_transpose, hL.eq]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hsplit : ∀ x : Fin 2 ⊕ κ → ℝ, x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := fun x =>
    (Sum.elim_comp_inl_inr x).symm
  constructor
  · intro h d
    -- `u = H + V` has square `2`; `y = (−d·V, −d·H, d)` is orthogonal to it with square `−δ(d)`
    set u : Fin 2 ⊕ κ → ℝ := Sum.elim (fun _ => 1) 0
    set y : Fin 2 ⊕ κ → ℝ := Sum.elim ![-(B *ᵥ d) 1, -(B *ᵥ d) 0] d
    have hu : qf (fromBlocks realPolePlane B Bᵀ L) u = 2 := by
      rw [qf_fromBlocks_pole]; simp [polarDefect, qf, bil]
    have hy : qf (fromBlocks realPolePlane B Bᵀ L) y = -polarDefect B L d := by
      rw [qf_fromBlocks_pole]; simp
    have huy : qf (fromBlocks realPolePlane B Bᵀ L) (u + y) = 2 - polarDefect B L d := by
      have : u + y = Sum.elim ![1 - (B *ᵥ d) 1, 1 - (B *ᵥ d) 0] d := by
        ext (i | k)
        · fin_cases i <;> simp [u, y, sub_eq_add_neg]
        · simp [u, y]
      rw [this, qf_fromBlocks_pole]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring
    have hb : bil (fromBlocks realPolePlane B Bᵀ L) u y = 0 := by
      have := qf_add_smul hG 1 1 u y
      simp only [one_smul, one_pow, one_mul, mul_one] at this
      rw [huy, hu, hy] at this
      linarith
    have := h u y (by rw [hu]; norm_num)
    rw [hu, hy, hb] at this
    linarith
  · intro h
    refine isHyperbolic_of_nonpos_on_ker hG (dotLeft (Sum.elim (Pi.single 0 1) (B 1)))
      fun z hz => ?_
    rw [hsplit z, qf_fromBlocks_pole]
    have hz' : z (Sum.inl 0) + (B *ᵥ (z ∘ Sum.inr)) 1 = 0 := by
      have : Sum.elim (Pi.single 0 1) (B 1) ⬝ᵥ z = 0 := hz
      rw [hsplit z, dotProduct_sumElim] at this
      simpa [dotProduct, Fin.sum_univ_two, mulVec] using this
    simp only [Function.comp_apply] at hz' ⊢
    rw [hz', mul_zero, zero_mul, zero_sub]
    linarith [h (z ∘ Sum.inr)]

/-! ### The Frobenius Gram of a curve datum -/

variable {ι : Type*} [Fintype ι]

/-- The fibre row: `Γ_k·H = 1`, `Γ_k·V = q^k`. -/
def frobeniusPoleRow (D : CurveDatum ι) (K : ℕ) : Matrix (Fin 2) (Fin (K + 1)) ℝ :=
  Matrix.of fun a k => if a = 0 then 1 else D.q ^ (k : ℕ)

/-- The graph block `Γ_k·Γ_l = q^{min(k,l)} N_{|k−l|}`. -/
def frobeniusGraphBlock (D : CurveDatum ι) (K : ℕ) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ :=
  Matrix.of fun k l => D.graphPair k l

/-- The Gram matrix of `H, V, Γ_0, …, Γ_K`. -/
def frobeniusGram (D : CurveDatum ι) (K : ℕ) :
    Matrix (Fin 2 ⊕ Fin (K + 1)) (Fin 2 ⊕ Fin (K + 1)) ℝ :=
  fromBlocks realPolePlane (frobeniusPoleRow D K) (frobeniusPoleRow D K)ᵀ (frobeniusGraphBlock D K)

theorem frobeniusGraphBlock_isSymm (D : CurveDatum ι) (K : ℕ) :
    (frobeniusGraphBlock D K).IsSymm :=
  Matrix.IsSymm.ext fun k l => by simp [frobeniusGraphBlock, D.graphPair_comm]

/-- The polar defect of the Frobenius Gram is the span defect. -/
theorem polarDefect_frobenius (D : CurveDatum ι) (K : ℕ) (d : ℕ → ℝ) :
    polarDefect (frobeniusPoleRow D K) (frobeniusGraphBlock D K) (fun k => d k) =
      D.spanDefect (range (K + 1)) d := by
  have hH : (frobeniusPoleRow D K *ᵥ fun k => d k) 0 = ∑ k ∈ range (K + 1), d k := by
    simp only [mulVec, dotProduct, frobeniusPoleRow, Matrix.of_apply, if_true, one_mul]
    exact Fin.sum_univ_eq_sum_range d (K + 1)
  have hV : (frobeniusPoleRow D K *ᵥ fun k => d k) 1 = ∑ k ∈ range (K + 1), d k * D.q ^ k := by
    simp only [mulVec, dotProduct, frobeniusPoleRow, Matrix.of_apply, one_ne_zero, if_false]
    rw [Fin.sum_univ_eq_sum_range (fun k => D.q ^ k * d k) (K + 1)]
    exact sum_congr rfl fun k _ => mul_comm _ _
  have hL : qf (frobeniusGraphBlock D K) (fun k => d k) =
      ∑ k ∈ range (K + 1), ∑ l ∈ range (K + 1), d k * d l * D.graphPair k l := by
    rw [qf_eq_sum]
    simp only [frobeniusGraphBlock, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => ∑ l : Fin (K + 1), d k * D.graphPair k l * d l)
      (K + 1)]
    refine sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun l => d k * D.graphPair k l * d l) (K + 1)]
    exact sum_congr rfl fun l _ => by ring
  rw [polarDefect, hH, hV, hL, CurveDatum.spanDefect]

/-- **Hodge index on the Frobenius span ⇔ nonnegative span defect.** -/
theorem frobeniusGram_isHyperbolic_iff (D : CurveDatum ι) (K : ℕ) :
    IsHyperbolic (frobeniusGram D K) ↔ ∀ d : ℕ → ℝ, 0 ≤ D.spanDefect (range (K + 1)) d := by
  rw [frobeniusGram, isHyperbolic_fromBlocks_iff _ (frobeniusGraphBlock_isSymm D K)]
  constructor
  · intro h d; rw [← polarDefect_frobenius]; exact h _
  · intro h d
    have := h (fun k => if hk : k < K + 1 then d ⟨k, hk⟩ else 0)
    rw [← polarDefect_frobenius] at this
    convert this using 2
    ext k; simp [k.isLt]

/-- **Unitary data satisfy the Hodge index** (Weil's theorem as an input: `|β_i| = 1`). -/
theorem frobeniusGram_isHyperbolic_of_unitary (D : CurveDatum ι) (hU : ∀ i, ‖D.β i‖ = 1)
    (K : ℕ) : IsHyperbolic (frobeniusGram D K) := by
  rw [frobeniusGram_isHyperbolic_iff]
  intro d
  rw [D.spanDefect_eq_toeplitz, D.toeplitz_eq_sum_normSq hU]
  exact sum_nonneg fun _ _ => sq_nonneg _

/-! ### Bézout is the Metzler property -/

/-- **Bézout ⇔ Metzler**: distinct graphs meet nonnegatively iff the point counts are
nonnegative. -/
theorem frobeniusGram_isMetzler_iff (D : CurveDatum ι) (K : ℕ) :
    IsMetzler (frobeniusGram D K) ↔ ∀ j, 1 ≤ j → j ≤ K → 0 ≤ D.pointCount j := by
  have hq : 0 < D.q := by linarith [D.one_lt_q]
  constructor
  · intro h j hj hjK
    have := h (Sum.inr 0) (Sum.inr ⟨j, by omega⟩) (by
      intro e; have := congrArg (fun x => match x with | Sum.inr k => (k : ℕ) | _ => 0) e
      simp at this; omega)
    simpa [frobeniusGram, frobeniusGraphBlock, D.graphPair_zero, D.graphPair_comm 0 j] using this
  · intro h a b hab
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a <;> fin_cases b <;> simp_all [frobeniusGram, realPolePlane]
    · simp only [frobeniusGram, fromBlocks_apply₁₂, frobeniusPoleRow, Matrix.of_apply]
      split_ifs <;> positivity
    · simp only [frobeniusGram, fromBlocks_apply₂₁, transpose_apply, frobeniusPoleRow,
        Matrix.of_apply]
      split_ifs <;> positivity
    · simp only [frobeniusGram, fromBlocks_apply₂₂, frobeniusGraphBlock, Matrix.of_apply,
        CurveDatum.graphPair]
      have hab' : (a : ℕ) ≠ b := fun e => hab (by rw [Fin.ext e])
      have hd1 : 1 ≤ Nat.dist a b := by
        rcases le_total (a : ℕ) b with h' | h'
        · rw [Nat.dist_eq_sub_of_le h']; omega
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h']; omega
      have hdK : Nat.dist a b ≤ K := by
        have := a.isLt; have := b.isLt
        rcases le_total (a : ℕ) b with h' | h'
        · rw [Nat.dist_eq_sub_of_le h']; omega
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h']; omega
      exact mul_nonneg (pow_nonneg hq.le _) (h _ hd1 hdK)

/-- The support of the Frobenius Gram is connected (through `H`). -/
theorem frobeniusGram_isConnectedSupport (D : CurveDatum ι) (K : ℕ) :
    IsConnectedSupport (frobeniusGram D K) := by
  intro w hw
  have hH : ∀ j, w j = w (Sum.inl 0) := by
    rintro (a | k)
    · fin_cases a
      · rfl
      · exact (hw (Sum.inl 0) (Sum.inl 1) (by simp [frobeniusGram, realPolePlane])).symm
    · exact (hw (Sum.inl 0) (Sum.inr k) (by simp [frobeniusGram, frobeniusPoleRow])).symm
  intro j k; rw [hH j, hH k]

/-- The weight `π = (t, t, 1, …, 1)` with `t = 1 + Σ |Γ_k·Γ_l|`. -/
def frobeniusWeight (D : CurveDatum ι) (K : ℕ) : Fin 2 ⊕ Fin (K + 1) → ℝ :=
  Sum.elim (fun _ => 1 + ∑ k : Fin (K + 1), ∑ l : Fin (K + 1), |D.graphPair k l|) fun _ => 1

theorem frobeniusWeight_pos (D : CurveDatum ι) (K : ℕ) (i : Fin 2 ⊕ Fin (K + 1)) :
    0 < frobeniusWeight D K i := by
  rcases i with a | k
  · simp only [frobeniusWeight, Sum.elim_inl]
    have : 0 ≤ ∑ k : Fin (K + 1), ∑ l : Fin (K + 1), |D.graphPair k l| :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · simp [frobeniusWeight]

/-- **Every curve datum is in the trickle-down regime**: the weight has positive image. -/
theorem frobeniusGram_mulVec_pos (D : CurveDatum ι) (K : ℕ) (i : Fin 2 ⊕ Fin (K + 1)) :
    0 < (frobeniusGram D K *ᵥ frobeniusWeight D K) i := by
  have hq : 0 < D.q := by linarith [D.one_lt_q]
  set T := ∑ k : Fin (K + 1), ∑ l : Fin (K + 1), |D.graphPair k l|
  have hT : 0 ≤ T := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  rw [show frobeniusWeight D K = Sum.elim (fun _ => 1 + T) (fun _ => 1) from rfl, frobeniusGram,
    fromBlocks_mulVec]
  rcases i with a | k
  · simp only [Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply]
    fin_cases a
    · simp [realPolePlane, mulVec, dotProduct, Fin.sum_univ_two, frobeniusPoleRow]; positivity
    · simp [realPolePlane, mulVec, dotProduct, Fin.sum_univ_two, frobeniusPoleRow]; positivity
  · simp only [Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply]
    simp only [mulVec, dotProduct, transpose_apply, frobeniusPoleRow, frobeniusGraphBlock,
      Matrix.of_apply, Fin.sum_univ_two, mul_one]
    simp only [Fin.isValue, if_true, one_ne_zero, if_false]
    have hrow : -T ≤ ∑ l : Fin (K + 1), D.graphPair k l := by
      have h1 : ∑ l : Fin (K + 1), -|D.graphPair k l| ≤ ∑ l : Fin (K + 1), D.graphPair k l :=
        sum_le_sum fun l _ => neg_abs_le _
      have h2 : ∑ l : Fin (K + 1), |D.graphPair k l| ≤ T :=
        single_le_sum (s := univ)
          (f := fun k : Fin (K + 1) => ∑ l : Fin (K + 1), |D.graphPair (k : ℕ) (l : ℕ)|)
          (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ k)
      rw [sum_neg_distrib] at h1
      linarith
    have : 0 ≤ D.q ^ (k : ℕ) * (1 + T) := by positivity
    nlinarith

/-- **For curve data with nonnegative counts, Hodge index ⇔ (TD_π).** -/
theorem frobeniusGram_isHyperbolic_iff_weightedTrickleDown (D : CurveDatum ι) (K : ℕ)
    (hN : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ D.pointCount j) :
    IsHyperbolic (frobeniusGram D K) ↔
      WeightedTrickleDown (frobeniusWeight D K) (frobeniusGram D K) :=
  isHyperbolic_iff_weightedTrickleDown
    (by
      unfold frobeniusGram Matrix.IsSymm
      rw [fromBlocks_transpose, transpose_transpose, (frobeniusGraphBlock_isSymm D K).eq]
      congr 1
      ext i j; fin_cases i <;> fin_cases j <;> rfl)
    ((frobeniusGram_isMetzler_iff D K).mpr hN) (frobeniusGram_isConnectedSupport D K)
    (frobeniusWeight_pos D K) (frobeniusGram_mulVec_pos D K)

/-- **True curves satisfy the trickle-down inequality.** -/
theorem weightedTrickleDown_of_unitary (D : CurveDatum ι) (hU : ∀ i, ‖D.β i‖ = 1) (K : ℕ)
    (hN : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ D.pointCount j) :
    WeightedTrickleDown (frobeniusWeight D K) (frobeniusGram D K) :=
  (frobeniusGram_isHyperbolic_iff_weightedTrickleDown D K hN).mp
    (frobeniusGram_isHyperbolic_of_unitary D hU K)

/-! ### The fake curve -/

/-- **The golden datum is Metzler**: its counts are positive. -/
theorem golden_isMetzler (K : ℕ) : IsMetzler (frobeniusGram goldenDatum K) :=
  (frobeniusGram_isMetzler_iff _ K).mpr fun _ hj _ =>
    le_trans zero_le_one (one_le_goldenDatum_pointCount hj)

/-- **The golden datum violates the Hodge index** on `H, V, Γ_0, Γ_1`. -/
theorem golden_not_isHyperbolic : ¬ IsHyperbolic (frobeniusGram goldenDatum 1) := by
  rw [frobeniusGram_isHyperbolic_iff]
  intro h
  have := h (fun k => if k = 0 then 1 else -1 / Real.sqrt 5)
  rw [show range (1 + 1) = ({0, 1} : Finset ℕ) by decide] at this
  linarith [goldenDatum_spanDefect_neg]

/-- **Sign without trickle-down.** The golden datum is Metzler, connected and in the trickle-down
regime, yet fails (TD_π): the trickle-down inequality, not the sign, carries Weil's theorem. -/
theorem golden_not_weightedTrickleDown :
    IsMetzler (frobeniusGram goldenDatum 1) ∧ IsConnectedSupport (frobeniusGram goldenDatum 1) ∧
      (∀ i, 0 < (frobeniusGram goldenDatum 1 *ᵥ frobeniusWeight goldenDatum 1) i) ∧
      ¬ WeightedTrickleDown (frobeniusWeight goldenDatum 1) (frobeniusGram goldenDatum 1) := by
  refine ⟨golden_isMetzler 1, frobeniusGram_isConnectedSupport _ 1,
    frobeniusGram_mulVec_pos _ 1, fun h => golden_not_isHyperbolic ?_⟩
  exact (frobeniusGram_isHyperbolic_iff_weightedTrickleDown _ 1 fun _ hj _ =>
    le_trans zero_le_one (one_le_goldenDatum_pointCount hj)).mpr h

end GaloisForLFunctions.ArithmeticLorentzianGeometry
