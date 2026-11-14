import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.ThePolePlaneAbsorbsTheBoundStateAndTheGreenMatrixOfWeilsFormOnTheMiddleIsPositive
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheBoundStatesOfAWindowAreAtMostTheSinksOfAPositiveTrialVector
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnANarrowWindowThePotentialIsPositiveAndThereAreNoBoundStates
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfABlockAndAFarWindowIsMinusTheProductOfTheirCharges

/-!
# The first overlap step is one bound state of the middle dressed by the attraction of its two ends

The overlap law eliminates the dyadic middle; its mediator `G_D` is indefinite and its only
uniform bound is the reciprocal of a certified floor. For narrow ends, `16 a ≤ R` and
`8 b ≤ R + a`, the other elimination is available: the two ends hold no bound state and can be
eliminated instead. The range contains the first overlap step (`a ≤ 3R/100`,
`b ≤ 3(R + a)/50`) and the second step of the ladder to ratio three.

* **The ends are positive definite without a certificate** (`endForm_form_ge`): the neutral form
  of the two ends is at least `3/4`. Each end is a narrow window with potential above `1`, and
  the jets between the two ends sum to at most `1/4` in every row; no contact joins them.
* **The inverse of the end form preserves positivity** (`inv_mulVec_nonneg_of_offDiag_nonpos`):
  a positive definite matrix with entries `≤ 0` off the diagonal has an inverse that maps
  nonnegative vectors to nonnegative vectors.
* **The attraction of the ends** `Σ = P N_e⁻¹ Pᵀ` (`endAttraction`) is positive semidefinite,
  at most `(4/3) ‖Pᵀ m‖²`, and has nonnegative entries (`endAttraction_apply_nonneg`),
  because every coupling of the middle to the ends is negative.
* **The dressed middle** `M̃ = M_D − Σ` (`dressedMiddle`) is the energy of a middle packet after
  the ends relax (`window_form_eq_dressed`, `dressedMiddle_form_le_window`). It is again a
  symmetric matrix with negative entries off the diagonal, below `M_D` entry by entry and as a
  form.
* **The dual overlap law** (`hermNegIndex_neutralWindow_eq_dressedMiddle`): the window
  `(R, 2(R + a) + b]` and its dressed middle hold the same number of bound states. Hence a
  step with narrow ends is the Hodge index inequality of the dressed form on positive packets of the
  middle without a common block
  (`hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle_wells_bound`), and it is certified by a
  positive trial vector on the middle (`hermNegIndex_neutralWindow_eq_one_of_dressed_trial`).
* **Each end alone leaves one bound state** (`hermNegIndex_dressedMiddle_left_eq_one`,
  `hermNegIndex_dressedMiddle_right_eq_one`): on the first step the middle dressed by one end is
  a part of the certified range. The first step asks whether the two attractions together
  create a second well.

The mediator `N_e⁻¹` lies between `1/‖N_e‖` and `4/3` and is positivity preserving; all of the
difficulty of the step is moved into the universal matrix `M_D`. The reduction uses the sign of
every coupling, jets and contacts alike.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Positive definite matrices with nonpositive entries off the diagonal -/

section Cooperative

variable {κ : Type*} [Fintype κ] {E : Matrix κ κ ℝ} {δ : ℝ}

omit [Fintype κ] in
/-- The entries of `P A Pᵀ` as forms of `A` on the rows of `P`. -/
theorem mul_mul_transpose_apply [Fintype κ] {ι : Type*} (P : Matrix ι κ ℝ) (A : Matrix κ κ ℝ)
    (i j : ι) : (P * A * Pᵀ) i j = (fun p => P i p) ⬝ᵥ (A *ᵥ fun q => P j q) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

variable [DecidableEq κ]

/-- **The inverse of a positive definite matrix with entries `≤ 0` off the diagonal preserves
positivity.** The negative part `n` of `u = E⁻¹ w` has `⟨n, E n⟩ ≤ −⟨n, w⟩ ≤ 0`. -/
theorem inv_mulVec_nonneg_of_offDiag_nonpos (hoff : ∀ p q, p ≠ q → E p q ≤ 0) (hδ : 0 < δ)
    (hfloor : ∀ e : κ → ℝ, δ * (e ⬝ᵥ e) ≤ e ⬝ᵥ (E *ᵥ e)) {w : κ → ℝ} (hw : ∀ p, 0 ≤ w p)
    (p : κ) : 0 ≤ (E⁻¹ *ᵥ w) p := by
  obtain ⟨u, hu⟩ : ∃ u : κ → ℝ, u = E⁻¹ *ᵥ w := ⟨_, rfl⟩
  have hEu : E *ᵥ u = w := by
    rw [hu]
    exact mulVec_inv_mulVec_of_isUnit (isUnit_of_form_floor hδ hfloor) w
  rw [← hu]
  have hsplit : positiveWell u - negativeWell u = u :=
    funext fun i => positiveWell_sub_negativeWell u i
  have h1 : 0 ≤ negativeWell u ⬝ᵥ (E *ᵥ u) := by
    rw [hEu]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (negativeWell_nonneg u i) (hw i)
  have h2 : negativeWell u ⬝ᵥ (E *ᵥ positiveWell u) ≤ 0 := by
    have h := bilin_nonpos_of_disjoint hoff (negativeWell_nonneg u) (positiveWell_nonneg u)
      fun i => by rw [mul_comm]; exact positiveWell_mul_negativeWell u i
    rw [bilin_eq_sum_mul_mulVec] at h
    exact h
  have h3 : E *ᵥ u = E *ᵥ positiveWell u - E *ᵥ negativeWell u := by
    rw [← Matrix.mulVec_sub, hsplit]
  rw [h3, dotProduct_sub] at h1
  have h4 := hfloor (negativeWell u)
  have h5 : negativeWell u ⬝ᵥ negativeWell u ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    linarith [mul_pos hδ hpos]
  have h6 : negativeWell u = 0 := dotProduct_self_eq_zero.mp
    (le_antisymm h5 (dotProduct_self_star_nonneg (v := negativeWell u)))
  have h7 := positiveWell_sub_negativeWell u p
  rw [h6, Pi.zero_apply, sub_zero] at h7
  rw [← h7]
  exact positiveWell_nonneg u p

/-- The entries of `P E⁻¹ Pᵀ` are nonnegative when the entries of `P` are `≤ 0`. -/
theorem mul_inv_mul_transpose_apply_nonneg {ι : Type*} (hoff : ∀ p q, p ≠ q → E p q ≤ 0)
    (hδ : 0 < δ) (hfloor : ∀ e : κ → ℝ, δ * (e ⬝ᵥ e) ≤ e ⬝ᵥ (E *ᵥ e)) {P : Matrix ι κ ℝ}
    (hP : ∀ i p, P i p ≤ 0) (i j : ι) : 0 ≤ (P * E⁻¹ * Pᵀ) i j := by
  rw [mul_mul_transpose_apply]
  have hneg : ∀ p, (E⁻¹ *ᵥ fun q => P j q) p ≤ 0 := fun p => by
    have h := inv_mulVec_nonneg_of_offDiag_nonpos hoff hδ hfloor (w := -fun q => P j q)
      (fun q => neg_nonneg.mpr (hP j q)) p
    rw [Matrix.mulVec_neg, Pi.neg_apply] at h
    linarith
  exact Finset.sum_nonneg fun p _ => mul_nonneg_of_nonpos_of_nonpos (hP i p) (hneg p)

/-- The inverse of a form with a positive floor is nonnegative. -/
theorem inv_form_nonneg_of_form_floor (hδ : 0 < δ)
    (hfloor : ∀ e : κ → ℝ, δ * (e ⬝ᵥ e) ≤ e ⬝ᵥ (E *ᵥ e)) (w : κ → ℝ) :
    0 ≤ w ⬝ᵥ (E⁻¹ *ᵥ w) := by
  by_cases hw : w = 0
  · rw [hw, zero_dotProduct]
  · exact (inv_form_pos_of_form_floor hδ hfloor hw).le

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Completing the square over a positive definite corner.** -/
theorem dotProduct_fromBlocks_mulVec_eq_corner_schur (A : Matrix ι ι ℝ) (P : Matrix ι κ ℝ)
    (hE : ∀ p q, E p q = E q p) (hEu : IsUnit E) (m : ι → ℝ) (e : κ → ℝ) :
    Sum.elim m e ⬝ᵥ (fromBlocks A P Pᵀ E *ᵥ Sum.elim m e) =
      (e + E⁻¹ *ᵥ (Pᵀ *ᵥ m)) ⬝ᵥ (E *ᵥ (e + E⁻¹ *ᵥ (Pᵀ *ᵥ m))) +
        m ⬝ᵥ ((A - P * E⁻¹ * Pᵀ) *ᵥ m) := by
  have h := dotProduct_fromBlocks_mulVec_eq_schur hE hEu Pᵀ A e m
  rw [Matrix.transpose_transpose] at h
  have h1 : (Sum.elim m e : ι ⊕ κ → ℝ) ∘ (Equiv.sumComm κ ι) = Sum.elim e m := by
    funext x
    rcases x with x | x <;> rfl
  have h2 : (fromBlocks A P Pᵀ E).submatrix (Equiv.sumComm κ ι) (Equiv.sumComm κ ι) =
      fromBlocks E Pᵀ P A := Matrix.fromBlocks_submatrix_sum_swap_sum_swap A P Pᵀ E
  rw [← h, ← dotProduct_submatrix_equiv_mulVec (fromBlocks A P Pᵀ E) (Equiv.sumComm κ ι)
    (Sum.elim m e), h1, h2]

/-- **Haynsworth's additivity over a positive definite corner**: the block matrix and the
Schur complement of the corner have the same number of negative squares. -/
theorem hermNegIndex_fromBlocks_eq_of_corner_floor {A : Matrix ι ι ℝ}
    (hA : ∀ i j, A i j = A j i) (P : Matrix ι κ ℝ) (hE : ∀ p q, E p q = E q p) (hδ : 0 < δ)
    (hfloor : ∀ e : κ → ℝ, δ * (e ⬝ᵥ e) ≤ e ⬝ᵥ (E *ᵥ e)) :
    hermNegIndex ((fromBlocks A P Pᵀ E).map (↑) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) =
      hermNegIndex ((A - P * E⁻¹ * Pᵀ).map (↑) : Matrix ι ι ℂ) := by
  have hsw : (fromBlocks A P Pᵀ E).submatrix (Equiv.sumComm κ ι) (Equiv.sumComm κ ι) =
      fromBlocks E Pᵀ Pᵀᵀ A := by
    rw [Matrix.transpose_transpose]
    exact Matrix.fromBlocks_submatrix_sum_swap_sum_swap A P Pᵀ E
  have h0 : hermNegIndex (E.map (↑) : Matrix κ κ ℂ) = 0 :=
    hermNegIndex_eq_zero_iff_forall.mpr fun e =>
      le_trans (mul_nonneg hδ.le (dotProduct_self_star_nonneg (v := e))) (hfloor e)
  rw [← hermNegIndex_map_submatrix _ (Equiv.sumComm κ ι), hsw,
    hermNegIndex_fromBlocks_transpose hE (isUnit_of_form_floor hδ hfloor) Pᵀ hA,
    Matrix.transpose_transpose, h0, zero_add]

end Cooperative

/-! ### Two narrow ends -/

theorem endForm_inl_inl (Q R a b : ℕ) (i i' : Fin a) :
    endForm Q R a b (Sum.inl i) (Sum.inl i') = neutralBlock Q (R + i) (R + i') := rfl

theorem endForm_inl_inr (Q R a b : ℕ) (i : Fin a) (j : Fin b) :
    endForm Q R a b (Sum.inl i) (Sum.inr j) = neutralBlock Q (R + i) (2 * (R + a) + j) := rfl

theorem endForm_inr_inl (Q R a b : ℕ) (j : Fin b) (i : Fin a) :
    endForm Q R a b (Sum.inr j) (Sum.inl i) = neutralBlock Q (R + i) (2 * (R + a) + j) := rfl

theorem endForm_inr_inr (Q R a b : ℕ) (j j' : Fin b) :
    endForm Q R a b (Sum.inr j) (Sum.inr j') =
      neutralBlock Q (2 * (R + a) + j) (2 * (R + a) + j') := rfl

theorem endForm_symm (Q R a b : ℕ) (x y : Fin a ⊕ Fin b) :
    endForm Q R a b x y = endForm Q R a b y x :=
  fromBlocks_symm (posMatrix_symm (neutralBlock_symm Q) (leftPos R a)) _
    (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b)) x y

/-- Different blocks of the two ends have different positions. -/
theorem endPos_ne {R a b : ℕ} {x y : Fin a ⊕ Fin b} (hxy : x ≠ y) :
    Sum.elim (leftPos R a) (rightPos R a b) x ≠ Sum.elim (leftPos R a) (rightPos R a b) y := by
  rcases x with i | j <;> rcases y with i' | j'
  · simp only [Sum.elim_inl, leftPos]
    intro h
    exact hxy (congrArg Sum.inl (Fin.ext (by omega)))
  · have := i.2
    simp only [Sum.elim_inl, Sum.elim_inr, leftPos, rightPos]
    omega
  · have := i'.2
    simp only [Sum.elim_inl, Sum.elim_inr, leftPos, rightPos]
    omega
  · simp only [Sum.elim_inr, rightPos]
    intro h
    exact hxy (congrArg Sum.inr (Fin.ext (by omega)))

/-- Two different blocks of the ends attract. -/
theorem endForm_neg_of_ne (Q R a b : ℕ) {x y : Fin a ⊕ Fin b} (hxy : x ≠ y) :
    endForm Q R a b x y < 0 := by
  rw [endForm_apply_pos]
  exact neutralBlock_neg (endPos_ne hxy) Q

/-- Every coupling of the middle to the ends is negative. -/
theorem endCoupling_neg (Q R a b : ℕ) (m : Fin (R + a)) (p : Fin a ⊕ Fin b) :
    endCoupling Q R a b m p < 0 := by
  rw [endCoupling_apply]
  exact neutralBlock_neg (middlePos_ne_endPos R a b m p) Q

/-- A block above twice another and below three times it is not its image under a floor map. -/
theorem floorContact_eq_zero_of_far {Q x y : ℕ} (h2 : 2 * x + 2 ≤ y) (h3 : y < 3 * x) :
    floorContact Q x y = 0 := by
  refine Finset.sum_eq_zero fun k hk => if_neg ?_
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk : k = 2 := by omega
    subst hk
    omega
  · have h1 : y / k ≤ y / 3 := Nat.div_le_div_left hk3 (by norm_num)
    omega

/-- **The jets between the two ends are weak**: below ratio three a block of the left end and a
block of the right end are coupled by at least `−2/(R + a)`; no contact joins them. -/
theorem neg_two_div_le_neutralBlock_ends {Q R a b : ℕ} (hR : 1 ≤ R)
    (h3 : 2 * (R + a) + b ≤ 3 * R) (i : Fin a) (j : Fin b) :
    -(2 / ((R + a : ℕ) : ℝ)) ≤ neutralBlock Q (R + i) (2 * (R + a) + j) := by
  have hi := i.2
  have hj := j.2
  have hD : (0 : ℝ) < ((R + a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + a)
  have hlt : R + (i : ℕ) < 2 * (R + a) + j := by omega
  rw [neutralBlock, blockMatrix_of_lt hlt, floorContact_eq_zero_of_far (by omega) (by omega)]
  have h1 := blockJet_le hlt
  have h2 : (2 : ℝ) / (((2 * (R + a) + j : ℕ) : ℝ) - ((R + i : ℕ) : ℝ)) ≤
      2 / ((R + a : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) hD
    have h : ((R + a : ℕ) : ℝ) + ((R + i : ℕ) : ℝ) ≤ ((2 * (R + a) + j : ℕ) : ℝ) := by
      exact_mod_cast (by omega : R + a + (R + i) ≤ 2 * (R + a) + j)
    linarith
  linarith

/-- **The row sums of the form of two narrow ends are at least `3/4`.** -/
theorem endForm_rowSum_ge {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) (p : Fin a ⊕ Fin b) :
    (3 / 4 : ℝ) ≤ ∑ q, endForm Q R a b p q := by
  have hD : (0 : ℝ) < ((R + a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + a)
  have h3 : 2 * (R + a) + b ≤ 3 * R := by omega
  have hbD : (b : ℝ) * (2 / ((R + a : ℕ) : ℝ)) ≤ 1 / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hD]
    have h : (8 * b : ℝ) ≤ ((R + a : ℕ) : ℝ) := by exact_mod_cast hb
    linarith
  have haD : (a : ℝ) * (2 / ((R + a : ℕ) : ℝ)) ≤ 1 / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hD]
    have h : (16 * a : ℝ) ≤ ((R + a : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 16 * a ≤ R + a)
    linarith
  rw [Fintype.sum_sum_type]
  rcases p with i | j
  · have h1 : ∑ i' : Fin a, endForm Q R a b (Sum.inl i) (Sum.inl i') = blockPotential Q R a i := by
      rw [blockPotential, ← Fin.sum_univ_eq_sum_range (fun l => neutralBlock Q (R + i) (R + l)) a]
      rfl
    have h2 : -((b : ℝ) * (2 / ((R + a : ℕ) : ℝ))) ≤
        ∑ j : Fin b, endForm Q R a b (Sum.inl i) (Sum.inr j) := by
      have h : ∑ _j : Fin b, -(2 / ((R + a : ℕ) : ℝ)) ≤
          ∑ j : Fin b, endForm Q R a b (Sum.inl i) (Sum.inr j) :=
        Finset.sum_le_sum fun j _ => by
          rw [endForm_inl_inr]
          exact neg_two_div_le_neutralBlock_ends hR h3 i j
      rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg] at h
    have h4 := one_lt_blockPotential_of_narrow (Q := Q) (R := R) (J := a) (j := i) (by omega) i.2
    rw [h1]
    linarith
  · have h1 : ∑ j' : Fin b, endForm Q R a b (Sum.inr j) (Sum.inr j') =
        blockPotential Q (2 * (R + a)) b j := by
      rw [blockPotential, ← Fin.sum_univ_eq_sum_range
        (fun l => neutralBlock Q (2 * (R + a) + j) (2 * (R + a) + l)) b]
      rfl
    have h2 : -((a : ℝ) * (2 / ((R + a : ℕ) : ℝ))) ≤
        ∑ i : Fin a, endForm Q R a b (Sum.inr j) (Sum.inl i) := by
      have h : ∑ _i : Fin a, -(2 / ((R + a : ℕ) : ℝ)) ≤
          ∑ i : Fin a, endForm Q R a b (Sum.inr j) (Sum.inl i) :=
        Finset.sum_le_sum fun i _ => by
          rw [endForm_inr_inl]
          exact neg_two_div_le_neutralBlock_ends hR h3 i j
      rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg] at h
    have h4 := one_lt_blockPotential_of_narrow (Q := Q) (R := 2 * (R + a)) (J := b) (j := j)
      (by omega) j.2
    rw [h1]
    linarith

/-- **Two narrow ends are positive definite**: their neutral form is at least `3/4` at every
block size. -/
theorem endForm_form_ge {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) (e : Fin a ⊕ Fin b → ℝ) :
    3 / 4 * (e ⬝ᵥ e) ≤ e ⬝ᵥ (endForm Q R a b *ᵥ e) := by
  have h := form_ge_of_offDiag_nonpos (endForm_symm Q R a b)
    (fun _ _ hxy => (endForm_neg_of_ne Q R a b hxy).le) (B := -(3 / 4))
    (fun p => by rw [neg_neg]; exact endForm_rowSum_ge hR ha hb p) e
  rwa [neg_neg] at h

/-! ### The attraction of the ends and the dressed middle -/

/-- **The attraction of the two ends on the middle**: `P N_e⁻¹ Pᵀ`. -/
def endAttraction (Q R a b : ℕ) : Matrix (Fin (R + a)) (Fin (R + a)) ℝ :=
  endCoupling Q R a b * (endForm Q R a b)⁻¹ * (endCoupling Q R a b)ᵀ

/-- **The dressed middle**: the neutral part of the dyadic middle minus the attraction of the two
ends. -/
def dressedMiddle (Q R a b : ℕ) : Matrix (Fin (R + a)) (Fin (R + a)) ℝ :=
  primeFreeMiddle (R + a) - endAttraction Q R a b

theorem endAttraction_form (Q R a b : ℕ) (m : Fin (R + a) → ℝ) :
    m ⬝ᵥ (endAttraction Q R a b *ᵥ m) =
      ((endCoupling Q R a b)ᵀ *ᵥ m) ⬝ᵥ
        ((endForm Q R a b)⁻¹ *ᵥ ((endCoupling Q R a b)ᵀ *ᵥ m)) := by
  have h := dotProduct_transpose_mul_mul_mulVec (endCoupling Q R a b)ᵀ (endForm Q R a b)⁻¹ m
  rw [Matrix.transpose_transpose] at h
  exact h

/-- The attraction of the ends is positive semidefinite. -/
theorem endAttraction_form_nonneg {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) (m : Fin (R + a) → ℝ) :
    0 ≤ m ⬝ᵥ (endAttraction Q R a b *ᵥ m) := by
  rw [endAttraction_form]
  exact inv_form_nonneg_of_form_floor (by norm_num : (0 : ℝ) < 3 / 4)
    (endForm_form_ge hR ha hb) _

/-- **The attraction of the ends is at most `4/3` times the square of the couplings.** -/
theorem endAttraction_form_le {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) (m : Fin (R + a) → ℝ) :
    m ⬝ᵥ (endAttraction Q R a b *ᵥ m) ≤
      4 / 3 * (((endCoupling Q R a b)ᵀ *ᵥ m) ⬝ᵥ ((endCoupling Q R a b)ᵀ *ᵥ m)) := by
  rw [endAttraction_form]
  have h := inv_form_le_of_form_floor (by norm_num : (0 : ℝ) < 3 / 4)
    (endForm_form_ge (Q := Q) hR ha hb) ((endCoupling Q R a b)ᵀ *ᵥ m)
  have h2 : (1 : ℝ) / (3 / 4) = 4 / 3 := by norm_num
  rwa [h2] at h

/-- **The ends attract any two blocks of the middle**: the entries of the attraction are
nonnegative. -/
theorem endAttraction_apply_nonneg {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) (i j : Fin (R + a)) : 0 ≤ endAttraction Q R a b i j :=
  mul_inv_mul_transpose_apply_nonneg (fun _ _ hxy => (endForm_neg_of_ne Q R a b hxy).le)
    (by norm_num : (0 : ℝ) < 3 / 4) (endForm_form_ge hR ha hb)
    (fun m p => (endCoupling_neg Q R a b m p).le) i j

theorem endAttraction_symm (Q R a b : ℕ) (i j : Fin (R + a)) :
    endAttraction Q R a b i j = endAttraction Q R a b j i := by
  have hEt : (endForm Q R a b)ᵀ = endForm Q R a b :=
    Matrix.ext fun x y => endForm_symm Q R a b y x
  have h : (endAttraction Q R a b)ᵀ = endAttraction Q R a b := by
    rw [endAttraction, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, hEt, Matrix.mul_assoc]
  have h2 := congrFun (congrFun h j) i
  rwa [Matrix.transpose_apply] at h2

theorem dressedMiddle_symm (Q R a b : ℕ) (i j : Fin (R + a)) :
    dressedMiddle Q R a b i j = dressedMiddle Q R a b j i := by
  simp only [dressedMiddle, Matrix.sub_apply]
  rw [primeFreeMiddle_symm (R + a) i j, endAttraction_symm Q R a b i j]

/-- **The dressed middle is a potential plus a Dirichlet form**: its entries off the diagonal
are negative, below those of the middle. -/
theorem dressedMiddle_neg_of_ne {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) {i j : Fin (R + a)} (hij : i ≠ j) :
    dressedMiddle Q R a b i j < 0 := by
  have h1 : primeFreeMiddle (R + a) i j < 0 := neutralWindow_neg_of_ne 1 (R + a) hij
  have h2 := endAttraction_apply_nonneg (Q := Q) hR ha hb i j
  simp only [dressedMiddle, Matrix.sub_apply]
  linarith

theorem dressedMiddle_form (Q R a b : ℕ) (m : Fin (R + a) → ℝ) :
    m ⬝ᵥ (dressedMiddle Q R a b *ᵥ m) =
      m ⬝ᵥ (primeFreeMiddle (R + a) *ᵥ m) - m ⬝ᵥ (endAttraction Q R a b *ᵥ m) := by
  rw [dressedMiddle, Matrix.sub_mulVec, dotProduct_sub]

/-- The dressed middle is below the middle. -/
theorem dressedMiddle_form_le {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) (m : Fin (R + a) → ℝ) :
    m ⬝ᵥ (dressedMiddle Q R a b *ᵥ m) ≤ m ⬝ᵥ (primeFreeMiddle (R + a) *ᵥ m) := by
  rw [dressedMiddle_form]
  linarith [endAttraction_form_nonneg (Q := Q) hR ha hb m]

/-- **The energy of a window after the ends relax.** The neutral form of the window at a middle
packet `m` and an end packet `e` is the dressed form of `m` plus the form of the ends at the
deviation of `e` from its equilibrium `−N_e⁻¹ Pᵀ m`. -/
theorem window_form_eq_dressed {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) (m : Fin (R + a) → ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    Sum.elim m e ⬝ᵥ (fromBlocks (primeFreeMiddle (R + a)) (endCoupling Q R a b)
        (endCoupling Q R a b)ᵀ (endForm Q R a b) *ᵥ Sum.elim m e) =
      (e + (endForm Q R a b)⁻¹ *ᵥ ((endCoupling Q R a b)ᵀ *ᵥ m)) ⬝ᵥ
          (endForm Q R a b *ᵥ (e + (endForm Q R a b)⁻¹ *ᵥ ((endCoupling Q R a b)ᵀ *ᵥ m))) +
        m ⬝ᵥ (dressedMiddle Q R a b *ᵥ m) :=
  dotProduct_fromBlocks_mulVec_eq_corner_schur _ _ (endForm_symm Q R a b)
    (isUnit_of_form_floor (by norm_num : (0 : ℝ) < 3 / 4) (endForm_form_ge hR ha hb)) m e

/-- **The dressed form is the least energy of the window over the end packets.** -/
theorem dressedMiddle_form_le_window {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) (m : Fin (R + a) → ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    m ⬝ᵥ (dressedMiddle Q R a b *ᵥ m) ≤
      Sum.elim m e ⬝ᵥ (fromBlocks (primeFreeMiddle (R + a)) (endCoupling Q R a b)
        (endCoupling Q R a b)ᵀ (endForm Q R a b) *ᵥ Sum.elim m e) := by
  rw [window_form_eq_dressed hR ha hb]
  have h := endForm_form_ge (Q := Q) hR ha hb
    (e + (endForm Q R a b)⁻¹ *ᵥ ((endCoupling Q R a b)ᵀ *ᵥ m))
  have h2 : (0 : ℝ) ≤ 3 / 4 *
      ((e + (endForm Q R a b)⁻¹ *ᵥ ((endCoupling Q R a b)ᵀ *ᵥ m)) ⬝ᵥ
        (e + (endForm Q R a b)⁻¹ *ᵥ ((endCoupling Q R a b)ᵀ *ᵥ m))) :=
    mul_nonneg (by norm_num) (dotProduct_self_star_nonneg
      (v := e + (endForm Q R a b)⁻¹ *ᵥ ((endCoupling Q R a b)ᵀ *ᵥ m)))
  linarith

/-! ### The dual overlap law -/

/-- **The dual overlap law.** For narrow ends the window `(R, 2(R + a) + b]` and its
dressed middle hold the same number of bound states. -/
theorem hermNegIndex_neutralWindow_eq_dressedMiddle {Q R a b : ℕ} (hR : 1 ≤ R)
    (ha : 16 * a ≤ R) (hb : 8 * b ≤ R + a) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
        Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) =
      hermNegIndex ((dressedMiddle Q R a b).map (↑) :
        Matrix (Fin (R + a)) (Fin (R + a)) ℂ) := by
  rw [← hermNegIndex_map_submatrix _ (overlapEquiv a (R + a) b),
    neutralWindow_submatrix_overlapEquiv, overlapWhole]
  change hermNegIndex ((fromBlocks (neutralWindow Q (R + a) (R + a)) (endCoupling Q R a b)
    (endCoupling Q R a b)ᵀ (endForm Q R a b)).map (↑) : Matrix _ _ ℂ) = _
  rw [neutralWindow_dyadic_eq]
  exact hermNegIndex_fromBlocks_eq_of_corner_floor (primeFreeMiddle_symm (R + a)) _
    (endForm_symm Q R a b) (by norm_num : (0 : ℝ) < 3 / 4) (endForm_form_ge hR ha hb)

/-- The dressed middle holds at least one bound state: the flat packet is negative. -/
theorem one_le_hermNegIndex_dressedMiddle {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 16 * a ≤ R)
    (hb : 8 * b ≤ R + a) :
    1 ≤ hermNegIndex ((dressedMiddle Q R a b).map (↑) :
      Matrix (Fin (R + a)) (Fin (R + a)) ℂ) := by
  by_contra hlt
  have h0 : hermNegIndex ((dressedMiddle Q R a b).map (↑) :
      Matrix (Fin (R + a)) (Fin (R + a)) ℂ) = 0 := by omega
  have h1 := hermNegIndex_eq_zero_iff_forall.mp h0 fun _ => (1 : ℝ)
  have h2 := dressedMiddle_form_le (Q := Q) hR ha hb fun _ => (1 : ℝ)
  have h3 := flat_form_primeFreeMiddle_neg (D := R + a) (by omega)
  linarith

/-- **A step with narrow ends is one bound state of the dressed middle.** -/
theorem hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle {Q R a b : ℕ} (hR : 1 ≤ R)
    (ha : 16 * a ≤ R) (hb : 8 * b ≤ R + a) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
        Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 ↔
      hermNegIndex ((dressedMiddle Q R a b).map (↑) :
        Matrix (Fin (R + a)) (Fin (R + a)) ℂ) ≤ 1 := by
  rw [hermNegIndex_neutralWindow_eq_dressedMiddle hR ha hb]
  have h := one_le_hermNegIndex_dressedMiddle (Q := Q) hR ha hb
  omega

/-- **A step with narrow ends as a Hodge index inequality on the middle.** The window
`(R, 2(R + a) + b]` holds exactly one bound state iff any two nonnegative packets of the dyadic
middle without a common block, the first of negative dressed energy, satisfy the reverse
Cauchy–Schwarz inequality of the dressed form. -/
theorem hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle_wells_bound {Q R a b : ℕ}
    (hR : 1 ≤ R) (ha : 16 * a ≤ R) (hb : 8 * b ≤ R + a) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
        Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 ↔
      ∀ x y : Fin (R + a) → ℝ, (∀ k, 0 ≤ x k) → (∀ k, 0 ≤ y k) → (∀ k, x k * y k = 0) →
        bilin (dressedMiddle Q R a b) x x < 0 →
          bilin (dressedMiddle Q R a b) x x * bilin (dressedMiddle Q R a b) y y ≤
            bilin (dressedMiddle Q R a b) x y ^ 2 := by
  rw [hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle hR ha hb]
  exact hermNegIndex_le_one_iff_forall_wells_bound (dressedMiddle_symm Q R a b)
    fun _ _ hij => (dressedMiddle_neg_of_ne hR ha hb hij).le

/-- **A certificate of a step on the middle.** A positive trial vector `v` on the dyadic
middle, a charge `c` and a number `λ` with `M̃_ij + λ c_i c_j ≤ 0` off the diagonal and
`(M̃ v)_i + λ c_i ⟨c, v⟩ ≥ 0` at every block give exactly one bound state of the window. -/
theorem hermNegIndex_neutralWindow_eq_one_of_dressed_trial {Q R a b : ℕ} (hR : 1 ≤ R)
    (ha : 16 * a ≤ R) (hb : 8 * b ≤ R + a) (c : Fin (R + a) → ℝ) (lam : ℝ)
    (hoff : ∀ i j, i ≠ j → dressedMiddle Q R a b i j + lam * c i * c j ≤ 0)
    {v : Fin (R + a) → ℝ} (hv : ∀ i, 0 < v i)
    (hsuper : ∀ i, 0 ≤ (dressedMiddle Q R a b *ᵥ v) i + lam * c i * (c ⬝ᵥ v)) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 := by
  rw [hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle hR ha hb]
  have h := hermNegIndex_le_one_add_card_sinks (dressedMiddle Q R a b)
    (dressedMiddle_symm Q R a b) c lam hoff hv
  have h0 : Fintype.card
      {i // (dressedMiddle Q R a b *ᵥ v) i + lam * c i * (c ⬝ᵥ v) < 0} = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun i => absurd i.2 (not_lt.mpr (hsuper i.1))⟩
  rwa [h0, add_zero] at h

/-! ### Each end alone -/

/-- **The middle dressed by the left end alone holds exactly one bound state.** -/
theorem hermNegIndex_dressedMiddle_left_eq_one {Q R a : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (ha : 100 * a ≤ 3 * R) :
    hermNegIndex ((dressedMiddle Q R a 0).map (↑) :
      Matrix (Fin (R + a)) (Fin (R + a)) ℂ) = 1 := by
  rw [← hermNegIndex_neutralWindow_eq_dressedMiddle hR (by omega) (by omega)]
  obtain ⟨ψ, ν, -, h⟩ := exists_oneBoundState_neutralWindow (Q := Q) (R := R)
    (J := a + (R + a) + 0) hR (by omega) (by omega) hQ
  exact h.hermNegIndex_eq_one

/-- **The middle dressed by the right end alone holds exactly one bound state.** -/
theorem hermNegIndex_dressedMiddle_right_eq_one {Q R b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hb : 50 * b ≤ 3 * R) :
    hermNegIndex ((dressedMiddle Q R 0 b).map (↑) :
      Matrix (Fin (R + 0)) (Fin (R + 0)) ℂ) = 1 := by
  rw [← hermNegIndex_neutralWindow_eq_dressedMiddle hR (by omega) (by omega)]
  obtain ⟨ψ, ν, -, h⟩ := exists_oneBoundState_neutralWindow (Q := Q) (R := R)
    (J := 0 + (R + 0) + b) hR (by omega) (by omega) hQ
  exact h.hermNegIndex_eq_one

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
