import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheSliverBlocksOfTheGreenMatrixHaveALogarithmicDiagonalAndBulkDipoleCoupling

/-!
# The excess of an overlap step and the four-step ladder to ratio three

This module records the exact and operator-norm step excess functions of the overlap gluing law as
functions of the window ratio `ρ` and level `C`, proves their uniform boundedness across all block
sizes `R ≥ 1` via an integral-free discrete Hilbert and Schur bound, proves that the prime `2`
alone ceases to bind past ratio `3` while remaining the sole active prime up to ratio `3`, and
iterates the zero-rounding rational ratio-squaring step `ρ ↦ ρ² / 2` from `103 / 50 = 2.06`
through `2.1218`, `2.25`, `2.53`, and `3.209 > 3` (and `3.21` at the fifth step) to `(R, 3R]` and
to all ratios.

* **Uniform Hilbert and Schur bounds** (`hilbert_sum_le_six`,
  `dotProduct_mulVec_sq_le_of_inv_add`, `sum_floorGraph_injective_le`,
  `dotProduct_endCoupling_mulVec_sq_le`): for every window `(R, 2(R + a) + b]` at every block size,
  `‖endCoupling Q R a b‖_{2 → 2} ≤ 34 + 2 ∑_{2 ≤ k ≤ Q} Λ(k)`.
* **Step excess as a function of the ratio** (`windowExcess`, `couplingNorm`, `schurStepExcess`,
  `couplingStepExcess`, `schurStepExcess_le_analyticEnvelope`,
  `couplingStepExcess_le_analyticEnvelope`): exact Schur-complement and conditional-coupling
  excesses over all `ρ`-steps (`2(R + a) ≤ ρ R`, `2(R + a) + b ≤ ρ(R + a)`), uniformly bounded
  above over all block sizes `R ≥ 1` below the binding energy `-neutralBlock 1 1 1`, with
  `schurStepExcess Q ρ C = 0` at `C = 0` iff the Green inequality holds on every `ρ`-step.
* **Sharp prime-`2` regime and failure past ratio `3`** (`neutralWindow_eq_two_iff_le_two_mul`,
  `two_le_hermNegIndex_primeTwo_two_six`, `two_le_hermNegIndex_primeTwo`,
  `primeThree_restores_positivity_two_six`): `neutralWindow Q R J = neutralWindow 2 R J` iff
  `J ≤ 2 R` (`3 ≤ Q`, `1 ≤ R`). Past ratio `3`, `neutralWindow 2 2 6` on `(2, 8]` holds at least
  two bound states on the disjoint packets `e₀` and `e₄ + e₅`, propagating to every `(R, R + J]`
  with `2 ≤ R` and `3 R + 4 ≤ J`; turning on `Q ≥ 3` restores a positive direction on their span.
* **Zero-rounding ratio-squaring ladder and 0-or-escape quantization**
  (`hermNegIndex_le_one_of_sq_div_two`, `iteratedRatio_eq`, `hermNegIndex_ratio_three_le_one`,
  `hermNegIndex_ratio_three_eq_one_of_groundEnergy_nonneg`,
  `riemannHypothesis_iff_globalTowerLevel_zero`,
  `riemannHypothesis_iff_exists_lt_dyadicDepth_globalTowerLevel`): refining by `2 q²` makes
  `ρ = p / q ↦ ρ² / 2` exact at every block size `R ≥ 1`. Starting at `103 / 50`, four steps cross
  `9 / 4 = 2.25`, `253 / 100 = 2.53`, and `3` (`> 3.209`, and `> 3.21` at step `5`), giving
  `hermNegIndex ≤ 1` on `(R, 3R]` at level `levelAt 2 4` whenever `levelAt 2 3 < dyadicDepth` and
  `hermNegIndex = 1` whenever Weil's ground energy is nonnegative past `(log 3) / 2`. Globally, the
  cumulative tower loss stays uniformly below `dyadicDepth` iff it vanishes identically at every
  step, iff `RiemannHypothesis` holds.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Finite-dimensional supremum helpers for quadratic and bilinear forms -/

theorem abs_coord_le_one_of_dotProduct_eq_one {κ : Type*} [Fintype κ] {v : κ → ℝ}
    (hv : v ⬝ᵥ v = 1) (p : κ) : |v p| ≤ 1 := by
  have hsq : (v p) ^ 2 ≤ 1 := by
    calc (v p) ^ 2
        ≤ ∑ q : κ, (v q) ^ 2 :=
          Finset.single_le_sum (fun q _ => sq_nonneg (v q)) (Finset.mem_univ p)
      _ = v ⬝ᵥ v := Finset.sum_congr rfl fun q _ => sq (v q)
      _ = 1 := hv
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_dotProduct_mulVec_le_sum_abs {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) {u : α → ℝ} {v : β → ℝ} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    |u ⬝ᵥ (A *ᵥ v)| ≤ ∑ i : α, ∑ j : β, |A i j| := by
  simp only [dotProduct, Matrix.mulVec]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hui := abs_coord_le_one_of_dotProduct_eq_one hu i
  calc |u i| * |∑ j : β, A i j * v j|
      ≤ 1 * ∑ j : β, |A i j * v j| :=
        mul_le_mul hui (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) zero_le_one
    _ = ∑ j : β, |A i j| * |v j| := by
        rw [one_mul]
        exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ j : β, |A i j| := Finset.sum_le_sum fun j _ =>
        mul_le_of_le_one_right (abs_nonneg _) (abs_coord_le_one_of_dotProduct_eq_one hv j)

theorem unit_smul_dotProduct_self {κ : Type*} [Fintype κ] {v : κ → ℝ} (hv : 0 < v ⬝ᵥ v) :
    ((1 / Real.sqrt (v ⬝ᵥ v)) • v) ⬝ᵥ ((1 / Real.sqrt (v ⬝ᵥ v)) • v) = 1 := by
  have hs : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.mpr hv
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hsq : Real.sqrt (v ⬝ᵥ v) * Real.sqrt (v ⬝ᵥ v) = v ⬝ᵥ v := Real.mul_self_sqrt hv.le
  field_simp [hs.ne']
  linarith

/-! ### Exact Schur excess and conditional-coupling norm of a single overlap window -/

/-- Exact Schur-complement excess of `(R, 2(R + a) + b]` at level `C`: the least `x ≥ 0` such that
`overlapSchurLevel Q R a b C + x • 1 ⪰ 0`. -/
def windowExcess (Q R a b : ℕ) (C : ℝ) : ℝ :=
  sSup {y : ℝ | y = 0 ∨ ∃ e : Fin a ⊕ Fin b → ℝ, e ⬝ᵥ e = 1 ∧
    y = -(e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e))}

/-- Operator norm `‖overlapCouplingLevel Q R a b C‖_{2 → 2}` of the conditional coupling between the
two ends at level `C`. -/
def couplingNorm (Q R a b : ℕ) (C : ℝ) : ℝ :=
  sSup {y : ℝ | y = 0 ∨ ∃ (u : Fin a → ℝ) (v : Fin b → ℝ),
    u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ y = u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v)}

theorem windowExcess_bddAbove (Q R a b : ℕ) (C : ℝ) :
    BddAbove {y : ℝ | y = 0 ∨ ∃ e : Fin a ⊕ Fin b → ℝ, e ⬝ᵥ e = 1 ∧
      y = -(e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e))} := by
  refine ⟨∑ p, ∑ q, |overlapSchurLevel Q R a b C p q|, ?_⟩
  rintro y (rfl | ⟨e, he, rfl⟩)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  · exact (neg_le_abs _).trans (abs_dotProduct_mulVec_le_sum_abs _ he he)

theorem couplingNorm_bddAbove (Q R a b : ℕ) (C : ℝ) :
    BddAbove {y : ℝ | y = 0 ∨ ∃ (u : Fin a → ℝ) (v : Fin b → ℝ),
      u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ y = u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v)} := by
  refine ⟨∑ i, ∑ j, |overlapCouplingLevel Q R a b C i j|, ?_⟩
  rintro y (rfl | ⟨u, v, hu, hv, rfl⟩)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  · exact (le_abs_self _).trans (abs_dotProduct_mulVec_le_sum_abs _ hu hv)

theorem windowExcess_nonneg (Q R a b : ℕ) (C : ℝ) : 0 ≤ windowExcess Q R a b C :=
  le_csSup (windowExcess_bddAbove Q R a b C) (Or.inl rfl)

theorem couplingNorm_nonneg (Q R a b : ℕ) (C : ℝ) : 0 ≤ couplingNorm Q R a b C :=
  le_csSup (couplingNorm_bddAbove Q R a b C) (Or.inl rfl)

/-- Tautological lower bound on `overlapSchurLevel` in terms of `windowExcess`. -/
theorem neg_windowExcess_mul_le (Q R a b : ℕ) (C : ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    -windowExcess Q R a b C * (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e) := by
  by_cases h0 : e ⬝ᵥ e = 0
  · have he0 : e = 0 := dotProduct_self_eq_zero.mp h0
    simp [he0]
  · have hpos : 0 < e ⬝ᵥ e := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := e)) (Ne.symm h0)
    set r := Real.sqrt (e ⬝ᵥ e)
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    set u := (1 / r) • e
    have hu : u ⬝ᵥ u = 1 := unit_smul_dotProduct_self hpos
    have hle : -(u ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ u)) ≤ windowExcess Q R a b C :=
      le_csSup (windowExcess_bddAbove Q R a b C) (Or.inr ⟨u, hu, rfl⟩)
    have hquad : u ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ u) =
        (e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e)) / (e ⬝ᵥ e) := by
      simp only [u, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      have hsq : r * r = e ⬝ᵥ e := Real.mul_self_sqrt hpos.le
      field_simp [hr.ne', hpos.ne']
      rw [← hsq]; ring
    rw [hquad, neg_div, div_le_iff₀ hpos] at hle
    linarith

/-- Characterization of upper bounds on `windowExcess`. -/
theorem windowExcess_le_iff (Q R a b : ℕ) (C : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    windowExcess Q R a b C ≤ x ↔
      ∀ e : Fin a ⊕ Fin b → ℝ, -x * (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e) := by
  constructor
  · intro hle e
    have he := neg_windowExcess_mul_le Q R a b C e
    have hee : 0 ≤ e ⬝ᵥ e := dotProduct_self_star_nonneg (v := e)
    nlinarith
  · intro h
    refine csSup_le ⟨0, Or.inl rfl⟩ ?_
    rintro y (rfl | ⟨e, he, rfl⟩)
    · exact hx
    · have := h e
      rw [he, mul_one] at this
      linarith

theorem windowExcess_eq_zero_iff (Q R a b : ℕ) (C : ℝ) :
    windowExcess Q R a b C = 0 ↔
      ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e) := by
  rw [le_antisymm_iff, and_iff_left (windowExcess_nonneg Q R a b C),
    windowExcess_le_iff Q R a b C le_rfl]
  simp

/-- At level `0`, `windowExcess` vanishes iff the Green inequality holds on the two ends. -/
theorem windowExcess_zero_eq_zero_iff_greenForm {Q R a b : ℕ} (hD : 1 ≤ R + a) :
    windowExcess Q R a b 0 = 0 ↔
      ∀ e : Fin a ⊕ Fin b → ℝ,
        (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) ≤
          e ⬝ᵥ (endForm Q R a b *ᵥ e) +
            (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) := by
  rw [windowExcess_eq_zero_iff]
  refine forall_congr' fun e => ?_
  rw [overlapSchurLevel_zero, overlapSchur_form_eq_channels Q R a b hD]
  constructor <;> intro h <;> linarith

/-- Sublinear decrease of `windowExcess` in the level below the binding energy. -/
theorem windowExcess_le_sub (Q : ℕ) {R : ℕ} (a b : ℕ) (hR : 1 ≤ R) {C C' : ℝ}
    (hC : -(1 / 5000) < C) (hCC : C ≤ C') (hC' : C' < bindingEnergy (R + a)) :
    windowExcess Q R a b C' ≤ max 0 (windowExcess Q R a b C - (C' - C)) := by
  rw [windowExcess_le_iff Q R a b C' (le_max_left _ _)]
  intro e
  have hmon := overlapSchurLevel_mono Q a b hR hC hCC hC' e
  have hlo := neg_windowExcess_mul_le Q R a b C e
  have hee : 0 ≤ e ⬝ᵥ e := dotProduct_self_star_nonneg (v := e)
  have hmax : windowExcess Q R a b C - (C' - C) ≤ max 0 (windowExcess Q R a b C - (C' - C)) :=
    le_max_right _ _
  nlinarith

/-- Tautological operator-norm bound of `couplingNorm` on `overlapCouplingLevel`. -/
theorem dotProduct_overlapCouplingLevel_sq_le_couplingNorm (Q R a b : ℕ) (C : ℝ)
    (u : Fin a → ℝ) (v : Fin b → ℝ) :
    (u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v)) ^ 2 ≤
      (couplingNorm Q R a b C) ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
  by_cases hu0 : u ⬝ᵥ u = 0
  · have : u = 0 := dotProduct_self_eq_zero.mp hu0
    simp [this]
  · by_cases hv0 : v ⬝ᵥ v = 0
    · have : v = 0 := dotProduct_self_eq_zero.mp hv0
      simp [this]
    · have hupos : 0 < u ⬝ᵥ u := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := u)) (Ne.symm hu0)
      have hvpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := v)) (Ne.symm hv0)
      set ru := Real.sqrt (u ⬝ᵥ u)
      set rv := Real.sqrt (v ⬝ᵥ v)
      have hru : 0 < ru := Real.sqrt_pos.mpr hupos
      have hrv : 0 < rv := Real.sqrt_pos.mpr hvpos
      set u' := (1 / ru) • u
      set v' := (1 / rv) • v
      have hu1 : u' ⬝ᵥ u' = 1 := unit_smul_dotProduct_self hupos
      have hv1 : v' ⬝ᵥ v' = 1 := unit_smul_dotProduct_self hvpos
      have hnu1 : (-u') ⬝ᵥ (-u') = 1 := by simp [hu1]
      have hpos_le : u' ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v') ≤ couplingNorm Q R a b C :=
        le_csSup (couplingNorm_bddAbove Q R a b C) (Or.inr ⟨u', v', hu1, hv1, rfl⟩)
      have hneg_le : -(u' ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v')) ≤ couplingNorm Q R a b C := by
        have := le_csSup (couplingNorm_bddAbove Q R a b C) (Or.inr ⟨-u', v', hnu1, hv1, rfl⟩)
        simpa [neg_dotProduct] using this
      have habs : |u' ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v')| ≤ couplingNorm Q R a b C :=
        abs_le.mpr ⟨by linarith, hpos_le⟩
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at hsq
      have hval : u' ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v') =
          (u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v)) / (ru * rv) := by
        simp only [u', v', Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        field_simp [hru.ne', hrv.ne']
      rw [hval, div_pow, div_le_iff₀ (by positivity)] at hsq
      have hprod : (ru * rv) ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
        rw [mul_pow, sq, sq, Real.mul_self_sqrt hupos.le, Real.mul_self_sqrt hvpos.le]
      linarith

theorem couplingNorm_le_iff (Q R a b : ℕ) (C : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    couplingNorm Q R a b C ≤ x ↔
      ∀ (u : Fin a → ℝ) (v : Fin b → ℝ),
        (u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v)) ^ 2 ≤ x ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
  constructor
  · intro hle u v
    have h1 := dotProduct_overlapCouplingLevel_sq_le_couplingNorm Q R a b C u v
    have h2 : (couplingNorm Q R a b C) ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ (couplingNorm_nonneg Q R a b C) hle 2
    have hnn : 0 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) :=
      mul_nonneg (dotProduct_self_star_nonneg (v := u)) (dotProduct_self_star_nonneg (v := v))
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hnn)
  · intro h
    refine csSup_le ⟨0, Or.inl rfl⟩ ?_
    rintro y (rfl | ⟨u, v, hu, hv, rfl⟩)
    · exact hx
    · have hsq := h u v
      rw [hu, hv, mul_one, mul_one] at hsq
      by_contra hgt
      have : x < u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v) := not_le.mp hgt
      nlinarith

/-- Whenever both overlapping parts hold at most one bound state at level `C`, `windowExcess` is
dominated by `couplingNorm`. -/
theorem windowExcess_le_couplingNorm {Q R a b : ℕ} (hR : 1 ≤ R) {C : ℝ}
    (hC : -(1 / 5000) < C) (hCμ : C < bindingEnergy (R + a))
    (hleft : hermNegIndex ((neutralWindow Q R (a + (R + a)) +
        Matrix.diagonal fun _ => C).map (↑) :
      Matrix (Fin (a + (R + a))) (Fin (a + (R + a))) ℂ) ≤ 1)
    (hright : hermNegIndex ((neutralWindow Q (R + a) ((R + a) + b) +
        Matrix.diagonal fun _ => C).map (↑) :
      Matrix (Fin ((R + a) + b)) (Fin ((R + a) + b)) ℂ) ≤ 1) :
    windowExcess Q R a b C ≤ couplingNorm Q R a b C := by
  rw [windowExcess_le_iff Q R a b C (couplingNorm_nonneg Q R a b C)]
  intro e
  have hA := (oneBoundState_primeFreeMiddle (by omega : 1 ≤ R + a)).add_diagonal hCμ (by linarith)
  rw [← hermNegIndex_map_submatrix _ (leftPartEquiv a (R + a)), submatrix_add_diagonal_equiv,
    neutralWindow_submatrix_leftPartEquiv, neutralWindow_dyadic_eq,
    fromBlocks_add_diagonal_const] at hleft
  rw [← hermNegIndex_map_submatrix _ (finSumFinEquiv : Fin (R + a) ⊕ Fin b ≃ Fin (R + a + b)),
    submatrix_add_diagonal_equiv, neutralWindow_submatrix_rightPart, neutralWindow_dyadic_eq,
    fromBlocks_add_diagonal_const] at hright
  have h₁ := schur_nonneg_of_hermNegIndex_le_one hA _
    (symm_add_diagonal (posMatrix_symm (neutralBlock_symm Q) (leftPos R a)) C) hleft
  have h₂ := schur_nonneg_of_hermNegIndex_le_one hA _
    (symm_add_diagonal (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b)) C) hright
  have hblk : overlapSchurLevel Q R a b C =
      fromBlocks
        (posMatrix (neutralBlock Q) (leftPos R a) (leftPos R a) + Matrix.diagonal (fun _ => C) -
          (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))ᵀ *
            (primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *
            posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))
        (overlapCouplingLevel Q R a b C) (overlapCouplingLevel Q R a b C)ᵀ
        (posMatrix (neutralBlock Q) (rightPos R a b) (rightPos R a b) + Matrix.diagonal (fun _ => C) -
          (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))ᵀ *
            (primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *
            posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b)) := by
    rw [overlapSchurLevel, endForm, endCoupling, fromBlocks_add_diagonal_const,
      fromBlocks_sub_joinColumns hA.symm]
    rfl
  rw [hblk]
  exact fromBlocks_form_ge_of_coupling_le h₁ h₂ (couplingNorm_nonneg Q R a b C)
    (dotProduct_overlapCouplingLevel_sq_le_couplingNorm Q R a b C) e

/-! ### Integral-free discrete Hilbert and Schur operator-norm bounds -/

/-- **Integral-free discrete Hilbert sum**: for every real `r ≥ 1` and `N : ℕ`,
`∑_{s < N} √r / ((r + s + 1) √(s + 1)) ≤ 6`. -/
theorem hilbert_sum_le_six {r : ℝ} (hr : 1 ≤ r) (N : ℕ) :
    ∑ s ∈ range N, Real.sqrt r / ((r + ((s : ℝ) + 1)) * Real.sqrt ((s : ℝ) + 1)) ≤ 6 := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  set M := min N (Nat.floor r)
  rw [← Finset.sum_range_add_sum_Ico _ (min_le_left N (Nat.floor r))]
  have h1 : ∑ s ∈ range M, Real.sqrt r / ((r + ((s : ℝ) + 1)) * Real.sqrt ((s : ℝ) + 1)) ≤ 2 := by
    have hterm : ∀ s ∈ range M,
        Real.sqrt r / ((r + ((s : ℝ) + 1)) * Real.sqrt ((s : ℝ) + 1)) ≤
          2 / Real.sqrt r * (Real.sqrt (((s + 1 : ℕ) : ℝ)) - Real.sqrt (s : ℝ)) := by
      intro s _
      set a := Real.sqrt (s : ℝ)
      set b := Real.sqrt ((s : ℝ) + 1)
      have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
      have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
      have hba : (b - a) * (b + a) = 1 := by
        have hsqa : a * a = (s : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg s)
        have hsqb : b * b = (s : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
        nlinarith
      have h1le : 1 ≤ 2 * b * (b - a) := by nlinarith
      have hcast : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
      rw [hcast, mul_comm (2 / Real.sqrt r), ← mul_div_assoc]
      rw [div_le_div_iff₀ (by positivity) hsr]
      have hsqc : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
      have hrs : r ≤ r + ((s : ℝ) + 1) := by positivity
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun k : ℕ => Real.sqrt (k : ℝ)) M,
      Nat.cast_zero, Real.sqrt_zero, sub_zero]
    have hMr : (M : ℝ) ≤ r :=
      (Nat.cast_le.mpr (min_le_right N (Nat.floor r))).trans (Nat.floor_le hr0.le)
    have hsM : Real.sqrt (M : ℝ) ≤ Real.sqrt r := Real.sqrt_le_sqrt hMr
    have hmul := mul_le_mul_of_nonneg_left hsM (by positivity : 0 ≤ 2 / Real.sqrt r)
    have h2 : 2 / Real.sqrt r * Real.sqrt r = 2 := div_mul_cancel₀ 2 hsr.ne'
    linarith
  have h2 : ∑ s ∈ Ico M N, Real.sqrt r / ((r + ((s : ℝ) + 1)) * Real.sqrt ((s : ℝ) + 1)) ≤ 4 := by
    rcases le_or_gt N (Nat.floor r) with hN | hN
    · have hMN : M = N := min_eq_left hN
      rw [hMN, Finset.Ico_self, Finset.sum_empty]
      norm_num
    · have hM : M = Nat.floor r := min_eq_right hN.le
      have hM1 : 1 ≤ Nat.floor r := (Nat.le_floor_iff hr0.le).mpr (by norm_num; exact hr)
      have hMpos : (0 : ℝ) < (M : ℝ) := by rw [hM]; exact_mod_cast hM1
      have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
      have hterm : ∀ s ∈ Ico M N,
          Real.sqrt r / ((r + ((s : ℝ) + 1)) * Real.sqrt ((s : ℝ) + 1)) ≤
            2 * Real.sqrt r * (1 / Real.sqrt (s : ℝ) - 1 / Real.sqrt (((s + 1 : ℕ) : ℝ))) := by
        intro s hs
        have hs1 : 1 ≤ s := by have := (Finset.mem_Ico.mp hs).1; omega
        have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
        set a := Real.sqrt (s : ℝ)
        set b := Real.sqrt ((s : ℝ) + 1)
        have ha : 0 < a := Real.sqrt_pos.mpr hs0
        have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
        have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
        have hba : (b - a) * (b + a) = 1 := by
          have hsqa : a * a = (s : ℝ) := Real.mul_self_sqrt hs0.le
          have hsqb : b * b = (s : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
          nlinarith
        have hsqb : b * b = (s : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
        have key : a ≤ 2 * ((s : ℝ) + 1) * (b - a) := by
          have hprod : a * (b + a) ≤ 2 * (b * b) := by nlinarith
          have hrhs : 2 * ((s : ℝ) + 1) * (b - a) * (b + a) = 2 * (b * b) := by
            calc 2 * ((s : ℝ) + 1) * (b - a) * (b + a)
                = 2 * ((s : ℝ) + 1) * ((b - a) * (b + a)) := by ring
              _ = 2 * (b * b) := by rw [hba, mul_one, hsqb]
          nlinarith
        have hcast : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
        rw [hcast, div_sub_div _ _ ha.ne' hb.ne', one_mul, mul_one]
        calc Real.sqrt r / ((r + ((s : ℝ) + 1)) * b)
            ≤ Real.sqrt r / (((s : ℝ) + 1) * b) :=
              div_le_div_of_nonneg_left hsr.le (by positivity) (by nlinarith)
          _ ≤ 2 * Real.sqrt r * ((b - a) / (a * b)) := by
              rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
      have htel : ∑ k ∈ range (N - M),
          (1 / Real.sqrt ((M + k : ℕ) : ℝ) - 1 / Real.sqrt ((M + k + 1 : ℕ) : ℝ)) =
          1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((M + (N - M) : ℕ) : ℝ) := by
        simpa only [Nat.add_zero] using
          Finset.sum_range_sub' (fun k : ℕ => 1 / Real.sqrt ((M + k : ℕ) : ℝ)) (N - M)
      rw [htel]
      have hsub : 1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((M + (N - M) : ℕ) : ℝ) ≤
          1 / Real.sqrt (M : ℝ) := by
        linarith [show (0 : ℝ) ≤ 1 / Real.sqrt ((M + (N - M) : ℕ) : ℝ) by positivity]
      have hr4M : Real.sqrt r ≤ 2 * Real.sqrt (M : ℝ) := by
        have hlt : r < (M : ℝ) + 1 := by rw [hM]; exact Nat.lt_floor_add_one r
        have hle4 : r ≤ (2 * Real.sqrt (M : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hMpos.le]
          linarith
        exact (Real.sqrt_le_sqrt hle4).trans (by rw [Real.sqrt_sq (by positivity)])
      have hmul1 : 2 * Real.sqrt r *
          (1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((M + (N - M) : ℕ) : ℝ)) ≤
          2 * Real.sqrt r * (1 / Real.sqrt (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
      have hmul2 : 2 * Real.sqrt r * (1 / Real.sqrt (M : ℝ)) ≤
          2 * (2 * Real.sqrt (M : ℝ)) * (1 / Real.sqrt (M : ℝ)) := by
        nlinarith [show (0 : ℝ) < 1 / Real.sqrt (M : ℝ) by positivity]
      have hcancel : 2 * (2 * Real.sqrt (M : ℝ)) * (1 / Real.sqrt (M : ℝ)) = 4 := by
        field_simp [hsM.ne']; ring
      linarith
  linarith

/-- **Discrete Hilbert operator-norm bound**: if `|A i j| ≤ B / (r i + s j)` for injective maps
`r : α → ℕ`, `s : β → ℕ` taking positive values, then `‖A‖_{2 → 2} ≤ 6 B`. -/
theorem dotProduct_mulVec_sq_le_of_inv_add {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) {r : α → ℕ} {s : β → ℕ} (hr_inj : Function.Injective r)
    (hs_inj : Function.Injective s) (hr1 : ∀ i, 1 ≤ r i) (hs1 : ∀ j, 1 ≤ s j)
    {B : ℝ} (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B / ((r i : ℝ) + (s j : ℝ)))
    (u : α → ℝ) (v : β → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (6 * B) ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
  have unit_bound : ∀ {u' : α → ℝ} {v' : β → ℝ}, u' ⬝ᵥ u' = 1 → v' ⬝ᵥ v' = 1 →
      |u' ⬝ᵥ (A *ᵥ v')| ≤ 6 * B := by
    intro u' v' hu' hv'
    have hrow : ∀ i : α, ∑ j : β,
        Real.sqrt (r i : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (s j : ℝ)) ≤ 6 := by
      intro i
      refine (Finset.sum_le_sum_of_ne_zero (t := range (Finset.sup Finset.univ s))
        (f := fun j : β => Real.sqrt (r i : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (s j : ℝ)))
        (g := fun k : ℕ => Real.sqrt (r i : ℝ) / (((r i : ℝ) + ((k : ℝ) + 1)) * Real.sqrt ((k : ℝ) + 1)))
        (i := fun j _ => s j - 1) ?_ ?_ ?_).trans
        (hilbert_sum_le_six (by exact_mod_cast hr1 i) _)
      · intro j _ _
        have hjle : s j ≤ Finset.sup Finset.univ s := Finset.le_sup (Finset.mem_univ j)
        have := hs1 j
        exact Finset.mem_range.mpr (by omega)
      · intro j₁ _ _ j₂ _ _ heq
        have h1 := hs1 j₁; have h2 := hs1 j₂
        exact hs_inj (by omega)
      · intro j _ _
        have hsj : ((s j - 1 : ℕ) : ℝ) + 1 = (s j : ℝ) := by
          have : s j - 1 + 1 = s j := Nat.sub_add_cancel (hs1 j)
          exact_mod_cast this
        rw [hsj]
    have hcol : ∀ j : β, ∑ i : α,
        Real.sqrt (s j : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ)) ≤ 6 := by
      intro j
      refine (Finset.sum_le_sum_of_ne_zero (t := range (Finset.sup Finset.univ r))
        (f := fun i : α => Real.sqrt (s j : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ)))
        (g := fun k : ℕ => Real.sqrt (s j : ℝ) / (((s j : ℝ) + ((k : ℝ) + 1)) * Real.sqrt ((k : ℝ) + 1)))
        (i := fun i _ => r i - 1) ?_ ?_ ?_).trans
        (hilbert_sum_le_six (by exact_mod_cast hs1 j) _)
      · intro i _ _
        have hile : r i ≤ Finset.sup Finset.univ r := Finset.le_sup (Finset.mem_univ i)
        have := hr1 i
        exact Finset.mem_range.mpr (by omega)
      · intro i₁ _ _ i₂ _ _ heq
        have h1 := hr1 i₁; have h2 := hr1 i₂
        exact hr_inj (by omega)
      · intro i _ _
        have hri : ((r i - 1 : ℕ) : ℝ) + 1 = (r i : ℝ) := by
          have : r i - 1 + 1 = r i := Nat.sub_add_cancel (hr1 i)
          exact_mod_cast this
        rw [hri, add_comm (s j : ℝ)]
    have hpair : ∑ i : α, ∑ j : β, |u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ)) ≤ 6 := by
      have hamgm : ∀ (i : α) (j : β),
          2 * (|u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ))) ≤
            (u' i) ^ 2 * (Real.sqrt (r i : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (s j : ℝ))) +
              (v' j) ^ 2 * (Real.sqrt (s j : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ))) := by
        intro i j
        have hri : (0 : ℝ) < r i := by exact_mod_cast hr1 i
        have hsj : (0 : ℝ) < s j := by exact_mod_cast hs1 j
        have hsri : 0 < Real.sqrt (r i : ℝ) := Real.sqrt_pos.mpr hri
        have hssj : 0 < Real.sqrt (s j : ℝ) := Real.sqrt_pos.mpr hsj
        have hden : 0 < ((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ) * Real.sqrt (s j : ℝ) := by
          positivity
        rw [← mul_le_mul_left hden]
        have hlhs : ((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ) * Real.sqrt (s j : ℝ) *
            (2 * (|u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ)))) =
            2 * |u' i| * |v' j| * Real.sqrt (r i : ℝ) * Real.sqrt (s j : ℝ) := by
          field_simp [(by positivity : (0 : ℝ) < (r i : ℝ) + (s j : ℝ)).ne']; ring
        have hrhs : ((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ) * Real.sqrt (s j : ℝ) *
            ((u' i) ^ 2 * (Real.sqrt (r i : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (s j : ℝ))) +
              (v' j) ^ 2 * (Real.sqrt (s j : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ)))) =
            (u' i) ^ 2 * (r i : ℝ) + (v' j) ^ 2 * (s j : ℝ) := by
          have hsqi : Real.sqrt (r i : ℝ) * Real.sqrt (r i : ℝ) = (r i : ℝ) := Real.mul_self_sqrt hri.le
          have hsqj : Real.sqrt (s j : ℝ) * Real.sqrt (s j : ℝ) = (s j : ℝ) := Real.mul_self_sqrt hsj.le
          field_simp [(by positivity : (0 : ℝ) < (r i : ℝ) + (s j : ℝ)).ne', hsri.ne', hssj.ne']
          nlinarith
        rw [hlhs, hrhs]
        have hsq : 0 ≤ (|u' i| * Real.sqrt (r i : ℝ) - |v' j| * Real.sqrt (s j : ℝ)) ^ 2 :=
          sq_nonneg _
        have hsqi : Real.sqrt (r i : ℝ) ^ 2 = (r i : ℝ) := Real.sq_sqrt hri.le
        have hsqj : Real.sqrt (s j : ℝ) ^ 2 = (s j : ℝ) := Real.sq_sqrt hsj.le
        have hu2 : |u' i| ^ 2 = (u' i) ^ 2 := sq_abs _
        have hv2 : |v' j| ^ 2 = (v' j) ^ 2 := sq_abs _
        nlinarith
      have hsum : 2 * ∑ i : α, ∑ j : β, |u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ)) ≤
          ∑ i : α, (u' i) ^ 2 *
              (∑ j : β, Real.sqrt (r i : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (s j : ℝ))) +
            ∑ j : β, (v' j) ^ 2 *
              (∑ i : α, Real.sqrt (s j : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ))) := by
        rw [Finset.mul_sum]
        calc ∑ i : α, 2 * ∑ j : β, |u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ))
            = ∑ i : α, ∑ j : β, 2 * (|u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ))) :=
              Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
          _ ≤ ∑ i : α, ∑ j : β,
              ((u' i) ^ 2 * (Real.sqrt (r i : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (s j : ℝ))) +
                (v' j) ^ 2 * (Real.sqrt (s j : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ)))) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hamgm i j
          _ = _ := by
              simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
              rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
                (f := fun i j => (v' j) ^ 2 * _)]
              simp only [← Finset.mul_sum]
      have hs1' : ∑ i : α, (u' i) ^ 2 *
          (∑ j : β, Real.sqrt (r i : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (s j : ℝ))) ≤ 6 := by
        calc _ ≤ ∑ i : α, (u' i) ^ 2 * 6 :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
          _ = (u' ⬝ᵥ u') * 6 := by
              rw [← Finset.sum_mul]; congr 1; exact Finset.sum_congr rfl fun i _ => sq (u' i)
          _ = 6 := by rw [hu', one_mul]
      have hs2' : ∑ j : β, (v' j) ^ 2 *
          (∑ i : α, Real.sqrt (s j : ℝ) / (((r i : ℝ) + (s j : ℝ)) * Real.sqrt (r i : ℝ))) ≤ 6 := by
        calc _ ≤ ∑ j : β, (v' j) ^ 2 * 6 :=
              Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _)
          _ = (v' ⬝ᵥ v') * 6 := by
              rw [← Finset.sum_mul]; congr 1; exact Finset.sum_congr rfl fun j _ => sq (v' j)
          _ = 6 := by rw [hv', one_mul]
      linarith
    calc |u' ⬝ᵥ (A *ᵥ v')|
        = |∑ i : α, ∑ j : β, u' i * A i j * v' j| := by
          simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
          congr 1; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ i : α, ∑ j : β, |u' i * A i j * v' j| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : α, ∑ j : β, B * (|u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ))) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hA i j) (abs_nonneg (u' i))) (abs_nonneg (v' j))
          linarith [show |u' i| * (B / ((r i : ℝ) + (s j : ℝ))) * |v' j| =
            B * (|u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ))) by ring]
      _ = B * ∑ i : α, ∑ j : β, |u' i| * |v' j| / ((r i : ℝ) + (s j : ℝ)) := by
          simp only [← Finset.mul_sum]
      _ ≤ 6 * B := by nlinarith
  by_cases hu0 : u ⬝ᵥ u = 0
  · have : u = 0 := dotProduct_self_eq_zero.mp hu0
    simp [this]
  · by_cases hv0 : v ⬝ᵥ v = 0
    · have : v = 0 := dotProduct_self_eq_zero.mp hv0
      simp [this]
    · have hupos : 0 < u ⬝ᵥ u := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := u)) (Ne.symm hu0)
      have hvpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := v)) (Ne.symm hv0)
      set ru := Real.sqrt (u ⬝ᵥ u)
      set rv := Real.sqrt (v ⬝ᵥ v)
      have hru : 0 < ru := Real.sqrt_pos.mpr hupos
      have hrv : 0 < rv := Real.sqrt_pos.mpr hvpos
      have habs := unit_bound (unit_smul_dotProduct_self hupos) (unit_smul_dotProduct_self hvpos)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at hsq
      have hval : ((1 / ru) • u) ⬝ᵥ (A *ᵥ ((1 / rv) • v)) =
          (u ⬝ᵥ (A *ᵥ v)) / (ru * rv) := by
        simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        field_simp [hru.ne', hrv.ne']
      rw [hval, div_pow, div_le_iff₀ (by positivity)] at hsq
      have hprod : (ru * rv) ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
        rw [mul_pow, sq, sq, Real.mul_self_sqrt hupos.le, Real.mul_self_sqrt hvpos.le]
      linarith

/-- **Schur row-column operator-norm bound** for nonnegative matrices. -/
theorem dotProduct_mulVec_sq_le_of_row_col_sum {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) (hnn : ∀ i j, 0 ≤ A i j) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, A i j ≤ B) (hcol : ∀ j, ∑ i, A i j ≤ B)
    (u : α → ℝ) (v : β → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ B ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
  have unit_bound : ∀ {u' : α → ℝ} {v' : β → ℝ}, u' ⬝ᵥ u' = 1 → v' ⬝ᵥ v' = 1 →
      |u' ⬝ᵥ (A *ᵥ v')| ≤ B := by
    intro u' v' hu' hv'
    have hsum : 2 * ∑ i : α, ∑ j : β, |u' i| * A i j * |v' j| ≤ 2 * B := by
      rw [Finset.mul_sum]
      calc ∑ i : α, 2 * ∑ j : β, |u' i| * A i j * |v' j|
          = ∑ i : α, ∑ j : β, A i j * (2 * |u' i| * |v' j|) :=
            Finset.sum_congr rfl fun i _ => by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ ∑ i : α, ∑ j : β, (A i j * (u' i) ^ 2 + A i j * (v' j) ^ 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              have hsq : 0 ≤ (|u' i| - |v' j|) ^ 2 := sq_nonneg _
              have hu2 : |u' i| ^ 2 = (u' i) ^ 2 := sq_abs _
              have hv2 : |v' j| ^ 2 = (v' j) ^ 2 := sq_abs _
              nlinarith [hnn i j]
        _ = ∑ i : α, (u' i) ^ 2 * (∑ j : β, A i j) +
            ∑ j : β, (v' j) ^ 2 * (∑ i : α, A i j) := by
            simp only [Finset.sum_add_distrib]
            congr 1
            · exact Finset.sum_congr rfl fun i _ => by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
            · rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ ≤ B + B := by
            have h1 : ∑ i : α, (u' i) ^ 2 * (∑ j : β, A i j) ≤ B := by
              calc _ ≤ ∑ i : α, (u' i) ^ 2 * B :=
                    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
                _ = (u' ⬝ᵥ u') * B := by
                    rw [← Finset.sum_mul]; congr 1
                    exact Finset.sum_congr rfl fun i _ => sq (u' i)
                _ = B := by rw [hu', one_mul]
            have h2 : ∑ j : β, (v' j) ^ 2 * (∑ i : α, A i j) ≤ B := by
              calc _ ≤ ∑ j : β, (v' j) ^ 2 * B :=
                    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _)
                _ = (v' ⬝ᵥ v') * B := by
                    rw [← Finset.sum_mul]; congr 1
                    exact Finset.sum_congr rfl fun j _ => sq (v' j)
                _ = B := by rw [hv', one_mul]
            linarith
        _ = 2 * B := by ring
    calc |u' ⬝ᵥ (A *ᵥ v')|
        = |∑ i : α, ∑ j : β, u' i * A i j * v' j| := by
          simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
          congr 1; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ i : α, ∑ j : β, |u' i * A i j * v' j| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ i : α, ∑ j : β, |u' i| * A i j * |v' j| :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
            rw [abs_mul, abs_mul, abs_of_nonneg (hnn i j)]
      _ ≤ B := by linarith
  by_cases hu0 : u ⬝ᵥ u = 0
  · have : u = 0 := dotProduct_self_eq_zero.mp hu0
    simp [this]
  · by_cases hv0 : v ⬝ᵥ v = 0
    · have : v = 0 := dotProduct_self_eq_zero.mp hv0
      simp [this]
    · have hupos : 0 < u ⬝ᵥ u := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := u)) (Ne.symm hu0)
      have hvpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := v)) (Ne.symm hv0)
      set ru := Real.sqrt (u ⬝ᵥ u)
      set rv := Real.sqrt (v ⬝ᵥ v)
      have hru : 0 < ru := Real.sqrt_pos.mpr hupos
      have hrv : 0 < rv := Real.sqrt_pos.mpr hvpos
      have habs := unit_bound (unit_smul_dotProduct_self hupos) (unit_smul_dotProduct_self hvpos)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at hsq
      have hval : ((1 / ru) • u) ⬝ᵥ (A *ᵥ ((1 / rv) • v)) =
          (u ⬝ᵥ (A *ᵥ v)) / (ru * rv) := by
        simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        field_simp [hru.ne', hrv.ne']
      rw [hval, div_pow, div_le_iff₀ (by positivity)] at hsq
      have hprod : (ru * rv) ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
        rw [mul_pow, sq, sq, Real.mul_self_sqrt hupos.le, Real.mul_self_sqrt hvpos.le]
      linarith

/-- Sum of von Mangoldt weights up to `Q`. -/
def primeContactSum (Q : ℕ) : ℝ := ∑ k ∈ Icc 2 Q, (Λ k : ℝ)

theorem primeContactSum_nonneg (Q : ℕ) : 0 ≤ primeContactSum Q :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Against any injective family of block indices, each floor map `k ≥ 2` has row sum at most
`(k + 1) · Λ(k) / k ≤ 2 Λ(k)`. -/
theorem sum_floorGraph_injective_le {α : Type*} [Fintype α] {q : α → ℕ}
    (hq : Function.Injective q) {k : ℕ} (hk : 2 ≤ k) (x : ℕ) :
    ∑ j : α, floorGraph k x (q j) ≤ 2 * (Λ k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let S : Finset ℕ := insert (x / k) (Ico (k * x) (k * x + k))
  have hcard : (S.card : ℝ) ≤ (k : ℝ) + 1 := by
    have hc : S.card ≤ 1 + (Ico (k * x) (k * x + k)).card := Finset.card_insert_le _ _
    rw [Nat.card_Ico, Nat.add_sub_cancel_left] at hc
    exact_mod_cast (by omega : S.card ≤ k + 1)
  have hsub : ∑ j : α, floorGraph k x (q j) ≤ ∑ y ∈ S, (Λ k : ℝ) / k := by
    refine Finset.sum_le_sum_of_ne_zero (i := fun j _ => q j) ?_ ?_ ?_
    · intro j _ hne
      rw [floorGraph] at hne
      have hdiv : max x (q j) / k = min x (q j) := by
        by_contra hc; exact hne (if_neg hc)
      rcases le_total (q j) x with hle | hge
      · rw [max_eq_left hle, min_eq_right hle] at hdiv
        exact Finset.mem_insert.mpr (Or.inl hdiv.symm)
      · rw [max_eq_right hge, min_eq_left hge] at hdiv
        refine Finset.mem_insert.mpr (Or.inr (Finset.mem_Ico.mpr ?_))
        have h1 : x * k ≤ q j := (Nat.le_div_iff_mul_le (by omega)).mp hdiv.ge
        have h2 : q j < (x + 1) * k := (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
        exact ⟨by nlinarith, by nlinarith⟩
    · intro j₁ _ _ j₂ _ _ heq; exact hq heq
    · intro j _ _
      rw [floorGraph]
      split_ifs
      · exact le_rfl
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk0.le
  rw [Finset.sum_const, nsmul_eq_mul] at hsub
  refine hsub.trans ?_
  have h1 : (S.card : ℝ) * ((Λ k : ℝ) / k) ≤ ((k : ℝ) + 1) * ((Λ k : ℝ) / k) :=
    mul_le_mul_of_nonneg_right hcard (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk0.le)
  have h2 : ((k : ℝ) + 1) / k ≤ 2 := by
    rw [div_le_iff₀ hk0]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 ArithmeticFunction.vonMangoldt_nonneg
  linarith [show ((k : ℝ) + 1) * ((Λ k : ℝ) / k) = ((k : ℝ) + 1) / k * (Λ k : ℝ) by ring]

theorem sum_floorContact_injective_le {α : Type*} [Fintype α] {q : α → ℕ}
    (hq : Function.Injective q) (Q x : ℕ) :
    ∑ j : α, floorContact Q (min x (q j)) (max x (q j)) ≤ 2 * primeContactSum Q := by
  have hfg : ∀ j : α, floorContact Q (min x (q j)) (max x (q j)) =
      ∑ k ∈ Icc 2 Q, floorGraph k x (q j) := by
    intro j
    rw [floorContact_eq_sum_floorGraph Q min_le_max]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases le_total x (q j) with hle | hge
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hge, max_eq_left hge, floorGraph_comm]
  simp only [hfg]
  rw [Finset.sum_comm, primeContactSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun k hk => sum_floorGraph_injective_le hq (Finset.mem_Icc.mp hk).1 x

theorem blockJet_le_two_div {x y : ℕ} (hxy : x < y) :
    blockJet x y ≤ 2 / ((y - x : ℕ) : ℝ) := by
  rw [blockJet]
  have hd : 1 ≤ y - x := by omega
  have h1 : xLogXDiff (x + y + 1) ≤ 2 / ((y - x : ℕ) : ℝ) :=
    (xLogXDiff_le (by omega)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hd)
        (by exact_mod_cast (by omega : y - x ≤ x + y + 1)))
  have h2 : xLogXDiff (y - x) ≤ 2 / ((y - x : ℕ) : ℝ) := xLogXDiff_le hd
  linarith

/-- **Block-size-independent operator-norm bound on `endJet`**. -/
theorem dotProduct_endJet_mulVec_sq_le (R a b : ℕ) (w : Fin (R + a) → ℝ)
    (e : Fin a ⊕ Fin b → ℝ) :
    (w ⬝ᵥ (endJet R a b *ᵥ e)) ^ 2 ≤ 34 ^ 2 * ((w ⬝ᵥ w) * (e ⬝ᵥ e)) := by
  set J₁ : Matrix (Fin (R + a)) (Fin a) ℝ :=
    Matrix.of fun m i => endJet R a b m (Sum.inl i)
  set J₂ : Matrix (Fin (R + a)) (Fin b) ℝ :=
    Matrix.of fun m j => endJet R a b m (Sum.inr j)
  have hL : (w ⬝ᵥ (J₁ *ᵥ (e ∘ Sum.inl))) ^ 2 ≤ 24 ^ 2 * ((w ⬝ᵥ w) * ((e ∘ Sum.inl) ⬝ᵥ (e ∘ Sum.inl))) := by
    simpa only [show (6 * (4 : ℝ)) ^ 2 = 24 ^ 2 by norm_num] using
      dotProduct_mulVec_sq_le_of_inv_add J₁
        (r := fun m : Fin (R + a) => (m : ℕ) + 1) (s := fun i : Fin a => a - (i : ℕ))
        (fun m₁ m₂ h => Fin.ext (by omega))
        (fun i₁ i₂ h => by have := i₁.2; have := i₂.2; exact Fin.ext (by omega))
        (fun m => by omega) (fun i => by have := i.2; omega) (B := 4) (by norm_num)
        (fun m i => by
          have hi := i.2
          have hpos : 0 < J₁ m i := endJet_pos R a b m (Sum.inl i)
          rw [abs_of_pos hpos]
          simp only [J₁, Matrix.of_apply, endJet_apply, middlePos, leftPos, Sum.elim_inl]
          have hlt : R + (i : ℕ) < R + a + (m : ℕ) := by omega
          rw [min_eq_left hlt.le, max_eq_right hlt.le]
          refine (blockJet_le_two_div hlt).trans ?_
          rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < R + a + (m : ℕ) - (R + (i : ℕ))))
            (by positivity)]
          have h2 : (((m : ℕ) + 1) + (a - (i : ℕ)) : ℝ) ≤
              2 * ((R + a + (m : ℕ) - (R + (i : ℕ)) : ℕ) : ℝ) := by
            have : (m : ℕ) + 1 + (a - (i : ℕ)) ≤ 2 * (R + a + (m : ℕ) - (R + (i : ℕ))) := by omega
            exact_mod_cast this
          linarith) w (e ∘ Sum.inl)
  have hR : (w ⬝ᵥ (J₂ *ᵥ (e ∘ Sum.inr))) ^ 2 ≤ 24 ^ 2 * ((w ⬝ᵥ w) * ((e ∘ Sum.inr) ⬝ᵥ (e ∘ Sum.inr))) := by
    simpa only [show (6 * (4 : ℝ)) ^ 2 = 24 ^ 2 by norm_num] using
      dotProduct_mulVec_sq_le_of_inv_add J₂
        (r := fun m : Fin (R + a) => R + a - (m : ℕ)) (s := fun j : Fin b => (j : ℕ) + 1)
        (fun m₁ m₂ h => by have := m₁.2; have := m₂.2; exact Fin.ext (by omega))
        (fun j₁ j₂ h => Fin.ext (by omega))
        (fun m => by have := m.2; omega) (fun j => by omega) (B := 4) (by norm_num)
        (fun m j => by
          have hm := m.2
          have hpos : 0 < J₂ m j := endJet_pos R a b m (Sum.inr j)
          rw [abs_of_pos hpos]
          simp only [J₂, Matrix.of_apply, endJet_apply, middlePos, rightPos, Sum.elim_inr]
          have hlt : R + a + (m : ℕ) < 2 * (R + a) + (j : ℕ) := by omega
          rw [min_eq_left hlt.le, max_eq_right hlt.le]
          refine (blockJet_le_two_div hlt).trans ?_
          rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < 2 * (R + a) + (j : ℕ) - (R + a + (m : ℕ))))
            (by positivity)]
          have h2 : ((R + a - (m : ℕ)) + ((j : ℕ) + 1) : ℝ) ≤
              2 * ((2 * (R + a) + (j : ℕ) - (R + a + (m : ℕ)) : ℕ) : ℝ) := by
            have : (R + a - (m : ℕ)) + ((j : ℕ) + 1) ≤
                2 * (2 * (R + a) + (j : ℕ) - (R + a + (m : ℕ))) := by omega
            exact_mod_cast this
          linarith) w (e ∘ Sum.inr)
  have hsplit : w ⬝ᵥ (endJet R a b *ᵥ e) =
      w ⬝ᵥ (J₁ *ᵥ (e ∘ Sum.inl)) + w ⬝ᵥ (J₂ *ᵥ (e ∘ Sum.inr)) := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, J₁, J₂, Matrix.of_apply,
      Function.comp_apply, mul_add, Finset.sum_add_distrib]
  have hee : e ⬝ᵥ e = (e ∘ Sum.inl) ⬝ᵥ (e ∘ Sum.inl) + (e ∘ Sum.inr) ⬝ᵥ (e ∘ Sum.inr) := by
    conv_lhs => rw [← Sum.elim_comp_inl_inr e, sumElim_dotProduct_sumElim]
  rw [hsplit, hee]
  have hcs : (w ⬝ᵥ (J₁ *ᵥ (e ∘ Sum.inl)) + w ⬝ᵥ (J₂ *ᵥ (e ∘ Sum.inr))) ^ 2 ≤
      2 * ((w ⬝ᵥ (J₁ *ᵥ (e ∘ Sum.inl))) ^ 2 + (w ⬝ᵥ (J₂ *ᵥ (e ∘ Sum.inr))) ^ 2) := by
    nlinarith [sq_nonneg (w ⬝ᵥ (J₁ *ᵥ (e ∘ Sum.inl)) - w ⬝ᵥ (J₂ *ᵥ (e ∘ Sum.inr)))]
  have hww : 0 ≤ w ⬝ᵥ w := dotProduct_self_star_nonneg (v := w)
  have he1 : 0 ≤ (e ∘ Sum.inl) ⬝ᵥ (e ∘ Sum.inl) := dotProduct_self_star_nonneg (v := e ∘ Sum.inl)
  have he2 : 0 ≤ (e ∘ Sum.inr) ⬝ᵥ (e ∘ Sum.inr) := dotProduct_self_star_nonneg (v := e ∘ Sum.inr)
  nlinarith

theorem endPos_injective (R a b : ℕ) :
    Function.Injective (Sum.elim (leftPos R a) (rightPos R a b)) := by
  rintro (i₁ | j₁) (i₂ | j₂) h
  · simp only [Sum.elim_inl, leftPos] at h
    exact congrArg Sum.inl (Fin.ext (by omega))
  · simp only [Sum.elim_inl, Sum.elim_inr, leftPos, rightPos] at h
    have := i₁.2; omega
  · simp only [Sum.elim_inl, Sum.elim_inr, leftPos, rightPos] at h
    have := i₂.2; omega
  · simp only [Sum.elim_inr, rightPos] at h
    exact congrArg Sum.inr (Fin.ext (by omega))

/-- **Block-size-independent operator-norm bound on `endContact`**. -/
theorem dotProduct_endContact_mulVec_sq_le (Q R a b : ℕ) (w : Fin (R + a) → ℝ)
    (e : Fin a ⊕ Fin b → ℝ) :
    (w ⬝ᵥ (endContact Q R a b *ᵥ e)) ^ 2 ≤
      (2 * primeContactSum Q) ^ 2 * ((w ⬝ᵥ w) * (e ⬝ᵥ e)) := by
  refine dotProduct_mulVec_sq_le_of_row_col_sum (endContact Q R a b) (endContact_nonneg Q R a b)
    (by linarith [primeContactSum_nonneg Q]) (fun m => ?_) (fun p => ?_) w e
  · simp only [endContact_apply]
    exact sum_floorContact_injective_le (endPos_injective R a b) Q (middlePos R a m)
  · simp only [endContact_apply]
    have hcomm : ∀ m : Fin (R + a),
        floorContact Q (min (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p))
          (max (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p)) =
        floorContact Q (min (Sum.elim (leftPos R a) (rightPos R a b) p) (middlePos R a m))
          (max (Sum.elim (leftPos R a) (rightPos R a b) p) (middlePos R a m)) := fun m => by
      rw [min_comm, max_comm]
    simp only [hcomm]
    exact sum_floorContact_injective_le
      (fun m₁ m₂ h => Fin.ext (by simp only [middlePos] at h; omega)) Q _

/-- **Block-size-independent operator-norm bound on `endCoupling`**. -/
theorem dotProduct_endCoupling_mulVec_sq_le (Q R a b : ℕ) (w : Fin (R + a) → ℝ)
    (e : Fin a ⊕ Fin b → ℝ) :
    (w ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 ≤
      (34 + 2 * primeContactSum Q) ^ 2 * ((w ⬝ᵥ w) * (e ⬝ᵥ e)) := by
  have h1 := dotProduct_endJet_mulVec_sq_le R a b w e
  have h2 := dotProduct_endContact_mulVec_sq_le Q R a b w e
  have hsplit : w ⬝ᵥ (endCoupling Q R a b *ᵥ e) =
      -(w ⬝ᵥ (endJet R a b *ᵥ e)) - w ⬝ᵥ (endContact Q R a b *ᵥ e) := by
    rw [endCoupling_eq_neg_endJet_sub_endContact, Matrix.sub_mulVec, Matrix.neg_mulVec,
      dotProduct_sub, dotProduct_neg]
  rw [hsplit]
  set x := w ⬝ᵥ (endJet R a b *ᵥ e)
  set y := w ⬝ᵥ (endContact Q R a b *ᵥ e)
  set P := (w ⬝ᵥ w) * (e ⬝ᵥ e)
  have hP : 0 ≤ P :=
    mul_nonneg (dotProduct_self_star_nonneg (v := w)) (dotProduct_self_star_nonneg (v := e))
  have hQnn := primeContactSum_nonneg Q
  have hxy : |x| * |y| ≤ 34 * (2 * primeContactSum Q) * P := by
    have hprod : (|x| * |y|) ^ 2 ≤ (34 * (2 * primeContactSum Q) * P) ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs]
      calc x ^ 2 * y ^ 2
          ≤ (34 ^ 2 * P) * ((2 * primeContactSum Q) ^ 2 * P) :=
            mul_le_mul h1 h2 (sq_nonneg y) (by positivity)
        _ = (34 * (2 * primeContactSum Q) * P) ^ 2 := by ring
    by_contra hgt
    have : 34 * (2 * primeContactSum Q) * P < |x| * |y| := not_le.mp hgt
    nlinarith [show 0 ≤ 34 * (2 * primeContactSum Q) * P by positivity]
  have habs : (-x - y) ^ 2 ≤ (|x| + |y|) ^ 2 := by
    have htri : |-x - y| ≤ |x| + |y| := by
      calc |-x - y| = |-(x + y)| := by ring_nf
        _ = |x + y| := abs_neg _
        _ ≤ |x| + |y| := abs_add_le x y
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) htri 2
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  nlinarith

/-! ### Uniform analytic envelopes for `windowExcess` and `couplingNorm` across all block sizes -/

/-- Closed-form analytic upper envelope on `couplingNorm` across all block sizes `R ≥ 1` and all
`(a, b)`. -/
def couplingAnalyticEnvelope (Q : ℕ) (C : ℝ) : ℝ :=
  12 + 2 * primeContactSum Q +
    (1 / (-neutralBlock 1 1 1 - C) + 1 / (1 / 5000 + C)) * (34 + 2 * primeContactSum Q) ^ 2

/-- Closed-form analytic upper envelope on `windowExcess` across all `ρ`-steps (`ρ ≥ 2`) and all
block sizes `R ≥ 1`. -/
def schurAnalyticEnvelope (Q : ℕ) (ρ C : ℝ) : ℝ :=
  5 + Real.log (ρ ^ 2 / 2) + Real.log (1 + ρ ^ 2 / 2) + 2 * primeContactSum Q + |C| +
    1 / (1 / 5000 + C) * (34 + 2 * primeContactSum Q) ^ 2

theorem form_ge_of_offDiag_nonpos {κ : Type*} [Fintype κ]
    {E : Matrix κ κ ℝ} (hE : ∀ p q, E p q = E q p) (hoff : ∀ p q, p ≠ q → E p q ≤ 0)
    {B : ℝ} (hrow : ∀ p, -B ≤ ∑ q, E p q) (e : κ → ℝ) :
    -B * (e ⬝ᵥ e) ≤ e ⬝ᵥ (E *ᵥ e) := by
  have hpt : ∀ p q : κ, 1 / 2 * E p q * ((e p) ^ 2 + (e q) ^ 2) ≤ E p q * (e p * e q) := by
    intro p q
    by_cases hpq : p = q
    · subst hpq; ring_nf; exact le_rfl
    · have hneg := hoff p q hpq
      nlinarith [sq_nonneg (e p - e q)]
  have hsum : ∑ p : κ, ∑ q : κ, 1 / 2 * E p q * ((e p) ^ 2 + (e q) ^ 2) ≤
      ∑ p : κ, ∑ q : κ, E p q * (e p * e q) :=
    Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hpt p q
  have hlhs : ∑ p : κ, ∑ q : κ, 1 / 2 * E p q * ((e p) ^ 2 + (e q) ^ 2) =
      ∑ p : κ, (∑ q : κ, E p q) * (e p) ^ 2 := by
    have hsplit : ∀ p q : κ, 1 / 2 * E p q * ((e p) ^ 2 + (e q) ^ 2) =
        1 / 2 * (E p q * (e p) ^ 2) + 1 / 2 * (E q p * (e q) ^ 2) := fun p q => by
      rw [hE p q]; ring
    simp only [hsplit, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun p q => 1 / 2 * (E q p * (e q) ^ 2))]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hrhs : ∑ p : κ, ∑ q : κ, E p q * (e p * e q) = e ⬝ᵥ (E *ᵥ e) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [hlhs, hrhs] at hsum
  have hlo : -B * (e ⬝ᵥ e) ≤ ∑ p : κ, (∑ q : κ, E p q) * (e p) ^ 2 := by
    calc -B * (e ⬝ᵥ e)
        = ∑ p : κ, (-B) * (e p) ^ 2 := by
          rw [← Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun p _ => (sq (e p)).symm
      _ ≤ ∑ p : κ, (∑ q : κ, E p q) * (e p) ^ 2 :=
          Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hrow p) (sq_nonneg _)
  exact hlo.trans hsum

/-- Row-sum potential lower bound for `neutralWindow Q R J` at ratio `((R + J : ℕ) : ℝ) ≤ γ * R`. -/
theorem blockPotential_ge_of_ratio {Q R J j : ℕ} (hR : 1 ≤ R) (hj : j < J) {γ : ℝ}
    (hγ1 : 1 ≤ γ) (hJ : ((R + J : ℕ) : ℝ) ≤ γ * R) :
    -(5 + Real.log γ + Real.log (1 + γ) + 2 * primeContactSum Q) ≤ blockPotential Q R J j := by
  have hpot1 : blockPotential 1 R J j = blockDensity (R + j) -
      (xLogXStep (R + j + R + J) - xLogXStep (R + j + R)) / 2 -
        (xLogXStep j + xLogXStep (J - 1 - j)) / 2 := by
    have hterm : ∀ l ∈ range J, neutralBlock 1 (R + j) (R + l) =
        (if j = l then blockDensity (R + j) else 0) - xLogXDiff (R + j + R + l + 1) / 2 -
          xLogXDiff (max j l - min j l) / 2 := by
      intro l _
      have e2 : max (R + j) (R + l) - min (R + j) (R + l) = max j l - min j l := by omega
      have e3 : R + j + (R + l) + 1 = R + j + R + l + 1 := by omega
      by_cases h : j = l
      · subst h
        rw [neutralBlock, blockMatrix_self (by omega), if_pos rfl, Nat.sub_self, xLogXDiff_zero,
          blockJet, Nat.sub_self, xLogXDiff_zero]
        ring
      · have hne : R + j ≠ R + l := by omega
        rw [neutralBlock_eq_neg_jet_sub_contact_of_ne 1 hne, floorContact_one, sub_zero,
          if_neg h, blockJet, min_add_max, e2, e3]
        ring
    have h1 := sum_range_xLogXDiff_add (R + j + R) J
    have h2 : ∑ l ∈ range J, xLogXDiff (max j l - min j l) =
        xLogXStep j + xLogXStep (J - 1 - j) := by
      obtain ⟨K, rfl⟩ : ∃ K, J = j + 1 + K := ⟨J - 1 - j, by omega⟩
      have ha : ∑ l ∈ range (j + 1), xLogXDiff (max j l - min j l) = xLogXStep j := by
        rw [← sum_range_succ_xLogXDiff j, ← Finset.sum_range_reflect (fun d => xLogXDiff d) (j + 1)]
        refine Finset.sum_congr rfl fun l hl => ?_
        have := Finset.mem_range.mp hl
        congr 1; omega
      have hb : ∑ i ∈ range K, xLogXDiff (max j (j + 1 + i) - min j (j + 1 + i)) =
          xLogXStep K := by
        rw [← sum_range_succ_xLogXDiff K, Finset.sum_range_succ', xLogXDiff_zero, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; omega
      rw [Finset.sum_range_add, ha, hb]; congr 2; omega
    rw [blockPotential, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hj), ← Finset.sum_div, ← Finset.sum_div, h1, h2]
  have hpotQ : blockPotential 1 R J j - 2 * primeContactSum Q ≤ blockPotential Q R J j := by
    have hdiff : blockPotential 1 R J j - blockPotential Q R J j =
        ∑ l : Fin J, floorContact Q (min (R + j) (R + l)) (max (R + j) (R + l)) := by
      rw [blockPotential, blockPotential, ← Finset.sum_sub_distrib,
        ← Fin.sum_univ_eq_sum_range _ J]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : R + j = R + (l : ℕ)
      · rw [h, neutralBlock, neutralBlock, blockMatrix_self (by omega),
          blockMatrix_self (by omega), min_self, max_self, floorContact_self (by omega)]
        ring
      · rw [neutralBlock_eq_neg_jet_sub_contact_of_ne 1 h,
          neutralBlock_eq_neg_jet_sub_contact_of_ne Q h, floorContact_one]
        ring
    linarith [sum_floorContact_injective_le
      (fun l₁ l₂ h => Fin.ext (by omega) : Function.Injective fun l : Fin J => R + (l : ℕ)) Q (R + j)]
  have hb_dens : Real.log (((R + j : ℕ) : ℝ) + 1) - 13 / 6 ≤ blockDensity (R + j) := by
    have hρ : blockDensity (R + j) =
        xLogXStep (R + j) - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) := rfl
    rw [hρ]
    have h1 := le_xLogXStep (n := R + j) (by omega)
    have h2 : 1 / (((R + j : ℕ) : ℝ) + 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 2 ≤ R + j + 1))
    linarith [Real.eulerMascheroniConstant_lt_two_thirds, log_two_pi_lt_two]
  have hb_sum : xLogXStep (R + j + R + J) - xLogXStep (R + j + R) ≤ Real.log (1 + γ) + 1 / 2 := by
    have h1 := xLogXStep_le (R + j + R + J)
    have h2 := le_xLogXStep (n := R + j + R) (by omega)
    have h3 : 1 / (((R + j + R : ℕ) : ℝ) + 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 2 ≤ R + j + R + 1))
    have hle : (((R + j + R + J : ℕ) : ℝ) + 1) ≤ (1 + γ) * (((R + j + R : ℕ) : ℝ) + 1) := by
      push_cast at hJ ⊢
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hR0 : (1 : ℝ) ≤ R := by exact_mod_cast hR
      nlinarith
    have hl := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by positivity) (by positivity)] at hl
    linarith
  have hb_diff : (xLogXStep j + xLogXStep (J - 1 - j)) / 2 ≤
      Real.log γ + Real.log (((R + j : ℕ) : ℝ) + 1) + 1 := by
    have h1 := xLogXStep_le j
    have h2 := xLogXStep_le (J - 1 - j)
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
    have hj_le : (j : ℝ) + 1 ≤ γ * R := by
      have : ((j + 1 : ℕ) : ℝ) ≤ ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ R + J)
      push_cast at this; linarith
    have hk_le : ((J - 1 - j : ℕ) : ℝ) + 1 ≤ γ * R := by
      have : ((J - 1 - j + 1 : ℕ) : ℝ) ≤ ((R + J : ℕ) : ℝ) := by
        exact_mod_cast (by omega : J - 1 - j + 1 ≤ R + J)
      push_cast at this; linarith
    have hl1 := Real.log_le_log (by positivity) hj_le
    have hl2 := Real.log_le_log (by positivity) hk_le
    rw [Real.log_mul (by positivity) hRpos.ne'] at hl1 hl2
    have hlR : Real.log R ≤ Real.log (((R + j : ℕ) : ℝ) + 1) :=
      Real.log_le_log hRpos (by exact_mod_cast (by omega : R ≤ R + j + 1))
    linarith
  linarith

theorem inv_norm_le_of_oneBoundState {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ} (h : OneBoundState A φ μ c) (w : ι → ℝ) :
    (A⁻¹ *ᵥ w) ⬝ᵥ (A⁻¹ *ᵥ w) ≤ (1 / μ + 1 / c) ^ 2 * (w ⬝ᵥ w) := by
  set g := A⁻¹ *ᵥ w
  set z := OneBoundState.perp φ g
  have hAg : A *ᵥ g = w := h.mulVec_inv_mulVec w
  have hφg : φ ⬝ᵥ g = -(1 / μ) * (φ ⬝ᵥ w) := by
    have := h.dot_mulVec g
    rw [hAg] at this
    have hμ := h.depth_pos.ne'
    field_simp; linarith
  have hAz : A *ᵥ z = w + (μ * (φ ⬝ᵥ g)) • φ := h.mulVec_perp_inv w
  have hzAz : z ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ OneBoundState.perp φ w := by
    have hφz : φ ⬝ᵥ z = 0 := h.dot_perp g
    rw [hAz, dotProduct_add, dotProduct_smul, dotProduct_comm z φ, hφz, smul_zero, add_zero,
      OneBoundState.perp, dotProduct_sub, dotProduct_smul, dotProduct_comm z φ, hφz, smul_zero, sub_zero]
  have hfloor := h.floor z (h.dot_perp g)
  rw [hzAz] at hfloor
  have hcs : (z ⬝ᵥ OneBoundState.perp φ w) ^ 2 ≤
      (z ⬝ᵥ z) * (OneBoundState.perp φ w ⬝ᵥ OneBoundState.perp φ w) := by
    simp only [dotProduct]
    simpa only [sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z (OneBoundState.perp φ w)
  have hzz : z ⬝ᵥ z ≤ (1 / c) ^ 2 * (OneBoundState.perp φ w ⬝ᵥ OneBoundState.perp φ w) := by
    have hc := h.floor_pos
    have hzz_nn : 0 ≤ z ⬝ᵥ z := dotProduct_self_star_nonneg (v := z)
    have hp_nn : 0 ≤ OneBoundState.perp φ w ⬝ᵥ OneBoundState.perp φ w :=
      dotProduct_self_star_nonneg (v := OneBoundState.perp φ w)
    rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
    by_contra hlt
    have hgt : OneBoundState.perp φ w ⬝ᵥ OneBoundState.perp φ w < (z ⬝ᵥ z) * c ^ 2 := not_le.mp hlt
    have hq_nn : 0 ≤ z ⬝ᵥ OneBoundState.perp φ w := by nlinarith
    have hsq_fl : (c * (z ⬝ᵥ z)) ^ 2 ≤ (z ⬝ᵥ OneBoundState.perp φ w) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hfloor 2
    nlinarith
  have hgg : g ⬝ᵥ g = (φ ⬝ᵥ g) ^ 2 + z ⬝ᵥ z := by
    have := h.perp_dot_perp g
    change z ⬝ᵥ z = g ⬝ᵥ g - (φ ⬝ᵥ g) ^ 2 at this
    linarith
  rw [hgg, hφg, h.perp_dot_perp w] at hzz ⊢
  have hμ := h.depth_pos
  have hc := h.floor_pos
  have hp_nn : 0 ≤ w ⬝ᵥ w - (φ ⬝ᵥ w) ^ 2 := by
    rw [← h.perp_dot_perp w]; exact dotProduct_self_star_nonneg (v := _)
  have h1 : (-(1 / μ) * (φ ⬝ᵥ w)) ^ 2 ≤ (1 / μ + 1 / c) ^ 2 * (φ ⬝ᵥ w) ^ 2 := by
    have : (1 / μ) ^ 2 ≤ (1 / μ + 1 / c) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by positivity) 2
    nlinarith [sq_nonneg (φ ⬝ᵥ w)]
  have h2 : (1 / c) ^ 2 * (w ⬝ᵥ w - (φ ⬝ᵥ w) ^ 2) ≤
      (1 / μ + 1 / c) ^ 2 * (w ⬝ᵥ w - (φ ⬝ᵥ w) ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hp_nn
    exact pow_le_pow_left₀ (by positivity) (by positivity) 2
  linarith

/-- **Uniform all-block-size upper bound on `couplingNorm`** below `-neutralBlock 1 1 1`. -/
theorem couplingNorm_le_analyticEnvelope {Q R a b : ℕ} (hR : 1 ≤ R) {C : ℝ}
    (hC1 : -(1 / 5000) < C) (hC2 : C < -neutralBlock 1 1 1) :
    couplingNorm Q R a b C ≤ couplingAnalyticEnvelope Q C := by
  have hD : 1 ≤ R + a := by omega
  have hμ_ge := (bindingEnergy_lt_three hD).1
  have hCμ : C < bindingEnergy (R + a) := lt_of_lt_of_le hC2 hμ_ge
  have hA := (oneBoundState_primeFreeMiddle hD).add_diagonal hCμ (by linarith)
  have hQnn := primeContactSum_nonneg Q
  have hden1 : 0 < -neutralBlock 1 1 1 - C := by linarith
  have hden2 : 0 < 1 / 5000 + C := by linarith
  have henv_nn : 0 ≤ couplingAnalyticEnvelope Q C := by unfold couplingAnalyticEnvelope; positivity
  rw [couplingNorm_le_iff Q R a b C henv_nn]
  intro u v
  -- Bound direct end-to-end block `K` by `12 + 2 primeContactSum Q`
  set K := posMatrix (neutralBlock Q) (leftPos R a) (rightPos R a b)
  set K_jet : Matrix (Fin a) (Fin b) ℝ :=
    Matrix.of fun i j => blockJet (leftPos R a i) (rightPos R a b j)
  set K_con : Matrix (Fin a) (Fin b) ℝ :=
    Matrix.of fun i j => floorContact Q (leftPos R a i) (rightPos R a b j)
  have hKeq : K = -K_jet - K_con := by
    ext i j
    simp only [K, K_jet, K_con, posMatrix, Matrix.of_apply, Matrix.sub_apply, Matrix.neg_apply]
    have hlt : leftPos R a i < rightPos R a b j := by
      simp only [leftPos, rightPos]; have := i.2; omega
    exact neutralBlock_of_lt hlt
  have hKj : (u ⬝ᵥ (K_jet *ᵥ v)) ^ 2 ≤ 12 ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
    simpa only [show (6 * (2 : ℝ)) ^ 2 = 12 ^ 2 by norm_num] using
      dotProduct_mulVec_sq_le_of_inv_add K_jet
        (r := fun i : Fin a => a - (i : ℕ)) (s := fun j : Fin b => (j : ℕ) + 1)
        (fun i₁ i₂ h => by have := i₁.2; have := i₂.2; exact Fin.ext (by omega))
        (fun j₁ j₂ h => Fin.ext (by omega))
        (fun i => by have := i.2; omega) (fun j => by omega) (B := 2) (by norm_num)
        (fun i j => by
          have hi := i.2
          have hlt : leftPos R a i < rightPos R a b j := by simp only [leftPos, rightPos]; omega
          have hpos : 0 < blockJet (leftPos R a i) (rightPos R a b j) := by
            rw [blockJet]
            linarith [xLogXDiff_pos (n := leftPos R a i + rightPos R a b j + 1) (by omega),
              xLogXDiff_pos (n := rightPos R a b j - leftPos R a i) (by omega)]
          simp only [K_jet, Matrix.of_apply, abs_of_pos hpos]
          refine (blockJet_le_two_div hlt).trans ?_
          refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
          simp only [leftPos, rightPos]
          have : (a - (i : ℕ)) + ((j : ℕ) + 1) ≤ 2 * (R + a) + (j : ℕ) - (R + (i : ℕ)) := by omega
          exact_mod_cast this) u v
  have hKc : (u ⬝ᵥ (K_con *ᵥ v)) ^ 2 ≤ (2 * primeContactSum Q) ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
    refine dotProduct_mulVec_sq_le_of_row_col_sum K_con
      (fun i j => Finset.sum_nonneg fun k _ => by
        split_ifs <;> [exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k);
          exact le_rfl])
      (by positivity) (fun i => ?_) (fun j => ?_) u v
    · have hm : ∀ j : Fin b, K_con i j =
          floorContact Q (min (leftPos R a i) (rightPos R a b j))
            (max (leftPos R a i) (rightPos R a b j)) := fun j => by
        have hlt : leftPos R a i ≤ rightPos R a b j := by
          simp only [leftPos, rightPos]; have := i.2; omega
        simp only [K_con, Matrix.of_apply, min_eq_left hlt, max_eq_right hlt]
      simp only [hm]
      exact sum_floorContact_injective_le
        (fun j₁ j₂ h => Fin.ext (by simp only [rightPos] at h; omega)) Q _
    · have hm : ∀ i : Fin a, K_con i j =
          floorContact Q (min (rightPos R a b j) (leftPos R a i))
            (max (rightPos R a b j) (leftPos R a i)) := fun i => by
        have hlt : leftPos R a i ≤ rightPos R a b j := by
          simp only [leftPos, rightPos]; have := i.2; omega
        simp only [K_con, Matrix.of_apply, min_eq_right hlt, max_eq_left hlt]
      simp only [hm]
      exact sum_floorContact_injective_le
        (fun i₁ i₂ h => Fin.ext (by simp only [leftPos] at h; omega)) Q _
  -- Bound indirect term `(P₁ u)ᵀ (M + C)⁻¹ (P₂ v)`
  set P₁ := posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a)
  set P₂ := posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b)
  have hP₁ : (P₁ *ᵥ u) ⬝ᵥ (P₁ *ᵥ u) ≤ (34 + 2 * primeContactSum Q) ^ 2 * (u ⬝ᵥ u) := by
    have hmul : P₁ *ᵥ u = endCoupling Q R a b *ᵥ Sum.elim u 0 := by
      ext m; simp [Matrix.mulVec, dotProduct, endCoupling, joinColumns, P₁]
    rw [hmul]
    by_cases hw : (endCoupling Q R a b *ᵥ Sum.elim u 0) ⬝ᵥ (endCoupling Q R a b *ᵥ Sum.elim u 0) = 0
    · rw [hw]; positivity
    · have hwpos : 0 < _ := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := _)) (Ne.symm hw)
      have hsq := dotProduct_endCoupling_mulVec_sq_le Q R a b
        (endCoupling Q R a b *ᵥ Sum.elim u 0) (Sum.elim u 0)
      have heu : Sum.elim u (0 : Fin b → ℝ) ⬝ᵥ Sum.elim u 0 = u ⬝ᵥ u := by
        rw [sumElim_dotProduct_sumElim, dotProduct_zero, add_zero]
      rw [heu] at hsq
      nlinarith
  have hP₂ : (P₂ *ᵥ v) ⬝ᵥ (P₂ *ᵥ v) ≤ (34 + 2 * primeContactSum Q) ^ 2 * (v ⬝ᵥ v) := by
    have hmul : P₂ *ᵥ v = endCoupling Q R a b *ᵥ Sum.elim 0 v := by
      ext m; simp [Matrix.mulVec, dotProduct, endCoupling, joinColumns, P₂]
    rw [hmul]
    by_cases hw : (endCoupling Q R a b *ᵥ Sum.elim 0 v) ⬝ᵥ (endCoupling Q R a b *ᵥ Sum.elim 0 v) = 0
    · rw [hw]; positivity
    · have hwpos : 0 < _ := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := _)) (Ne.symm hw)
      have hsq := dotProduct_endCoupling_mulVec_sq_le Q R a b
        (endCoupling Q R a b *ᵥ Sum.elim 0 v) (Sum.elim 0 v)
      have hev : Sum.elim (0 : Fin a → ℝ) v ⬝ᵥ Sum.elim 0 v = v ⬝ᵥ v := by
        rw [sumElim_dotProduct_sumElim, zero_dotProduct, zero_add]
      rw [hev] at hsq
      nlinarith
  have hinv := inv_norm_le_of_oneBoundState hA (P₂ *ᵥ v)
  have hfac : 1 / (bindingEnergy (R + a) - C) + 1 / (1 / 5000 + C) ≤
      1 / (-neutralBlock 1 1 1 - C) + 1 / (1 / 5000 + C) := by
    gcongr
  have hcs_ind : ((P₁ *ᵥ u) ⬝ᵥ ((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (P₂ *ᵥ v))) ^ 2 ≤
      ((1 / (-neutralBlock 1 1 1 - C) + 1 / (1 / 5000 + C)) * (34 + 2 * primeContactSum Q) ^ 2) ^ 2 *
        ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
    have h1 : ((P₁ *ᵥ u) ⬝ᵥ ((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (P₂ *ᵥ v))) ^ 2 ≤
        ((P₁ *ᵥ u) ⬝ᵥ (P₁ *ᵥ u)) *
          (((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (P₂ *ᵥ v)) ⬝ᵥ
            ((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (P₂ *ᵥ v))) := by
      simp only [dotProduct]
      simpa only [sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (P₁ *ᵥ u) _
    have h2 : (1 / (bindingEnergy (R + a) - C) + 1 / (1 / 5000 + C)) ^ 2 ≤
        (1 / (-neutralBlock 1 1 1 - C) + 1 / (1 / 5000 + C)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hfac 2
    have h3 : (((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (P₂ *ᵥ v)) ⬝ᵥ
          ((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (P₂ *ᵥ v))) ≤
        (1 / (-neutralBlock 1 1 1 - C) + 1 / (1 / 5000 + C)) ^ 2 *
          ((34 + 2 * primeContactSum Q) ^ 2 * (v ⬝ᵥ v)) := by
      calc _ ≤ (1 / (bindingEnergy (R + a) - C) + 1 / (1 / 5000 + C)) ^ 2 * ((P₂ *ᵥ v) ⬝ᵥ (P₂ *ᵥ v)) := hinv
        _ ≤ (1 / (-neutralBlock 1 1 1 - C) + 1 / (1 / 5000 + C)) ^ 2 * ((P₂ *ᵥ v) ⬝ᵥ (P₂ *ᵥ v)) :=
            mul_le_mul_of_nonneg_right h2 (dotProduct_self_star_nonneg (v := P₂ *ᵥ v))
        _ ≤ _ := mul_le_mul_of_nonneg_left hP₂ (by positivity)
    calc _ ≤ ((P₁ *ᵥ u) ⬝ᵥ (P₁ *ᵥ u)) *
          ((1 / (-neutralBlock 1 1 1 - C) + 1 / (1 / 5000 + C)) ^ 2 *
            ((34 + 2 * primeContactSum Q) ^ 2 * (v ⬝ᵥ v))) :=
          h1.trans (mul_le_mul_of_nonneg_left h3 (dotProduct_self_star_nonneg (v := P₁ *ᵥ u)))
      _ ≤ ((34 + 2 * primeContactSum Q) ^ 2 * (u ⬝ᵥ u)) *
          ((1 / (-neutralBlock 1 1 1 - C) + 1 / (1 / 5000 + C)) ^ 2 *
            ((34 + 2 * primeContactSum Q) ^ 2 * (v ⬝ᵥ v))) :=
          mul_le_mul_of_nonneg_right hP₁ (by positivity)
      _ = _ := by ring
  -- Combine the three pieces by triangle inequality on `|·|`
  have hexp : u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v) =
      -(u ⬝ᵥ (K_jet *ᵥ v)) - u ⬝ᵥ (K_con *ᵥ v) -
        (P₁ *ᵥ u) ⬝ᵥ ((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (P₂ *ᵥ v)) := by
    rw [overlapCouplingLevel]
    change u ⬝ᵥ ((K - P₁ᵀ * _ * P₂) *ᵥ v) = _
    rw [Matrix.sub_mulVec, dotProduct_sub, hKeq, Matrix.sub_mulVec, Matrix.neg_mulVec,
      dotProduct_sub, dotProduct_neg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [hexp]
  have sq_sqrt_bound : ∀ {X B' : ℝ}, 0 ≤ B' → X ^ 2 ≤ B' ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) →
      |X| ≤ B' * Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
    intro X B' hB' hX
    have hnn : 0 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) :=
      mul_nonneg (dotProduct_self_star_nonneg (v := u)) (dotProduct_self_star_nonneg (v := v))
    rw [← Real.sqrt_sq (abs_nonneg X), sq_abs,
      ← Real.sqrt_sq (mul_nonneg hB' (Real.sqrt_nonneg _)), mul_pow, Real.sq_sqrt hnn]
    exact Real.sqrt_le_sqrt hX
  have b1 := sq_sqrt_bound (by norm_num) hKj
  have b2 := sq_sqrt_bound (by positivity) hKc
  have b3 := sq_sqrt_bound (by positivity) hcs_ind
  set t1 := u ⬝ᵥ (K_jet *ᵥ v)
  set t2 := u ⬝ᵥ (K_con *ᵥ v)
  set t3 := (P₁ *ᵥ u) ⬝ᵥ ((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (P₂ *ᵥ v))
  have htri : |-t1 - t2 - t3| ≤ |t1| + |t2| + |t3| := by
    calc |-t1 - t2 - t3| = |-(t1 + t2 + t3)| := by ring_nf
      _ = |t1 + t2 + t3| := abs_neg _
      _ ≤ |t1 + t2| + |t3| := abs_add_le _ _
      _ ≤ |t1| + |t2| + |t3| := by linarith [abs_add_le t1 t2]
  have htot : |-t1 - t2 - t3| ≤
      couplingAnalyticEnvelope Q C * Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
    unfold couplingAnalyticEnvelope
    linarith
  have hsq := pow_le_pow_left₀ (abs_nonneg _) htot 2
  have hnn : 0 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) :=
    mul_nonneg (dotProduct_self_star_nonneg (v := u)) (dotProduct_self_star_nonneg (v := v))
  rw [sq_abs, mul_pow, Real.sq_sqrt hnn] at hsq
  exact hsq

/-! ### Ratio-indexed step excess functions -/

/-- `(R, 2(R + a) + b]` is a `ρ`-overlap step when both overlapping parts `(R, 2(R + a)]` and
`(R + a, 2(R + a) + b]` have ratio at most `ρ`. -/
def IsRatioStep (ρ : ℝ) (R a b : ℕ) : Prop :=
  1 ≤ R ∧ 2 * ((R + a : ℕ) : ℝ) ≤ ρ * R ∧ ((2 * (R + a) + b : ℕ) : ℝ) ≤ ρ * (R + a)

/-- At `ρ = 103 / 50 = 2.06`, `IsRatioStep` is the exact condition `1 ≤ R`, `100 a ≤ 3 R`,
`50 b ≤ 3(R + a)`. -/
theorem isRatioStep_103_div_50_iff (R a b : ℕ) :
    IsRatioStep (103 / 50) R a b ↔ 1 ≤ R ∧ 100 * a ≤ 3 * R ∧ 50 * b ≤ 3 * (R + a) := by
  unfold IsRatioStep
  constructor
  · rintro ⟨hR, h1, h2⟩
    refine ⟨hR, ?_, ?_⟩
    · have : (100 * (R + a) : ℝ) ≤ 103 * R := by push_cast at h1 ⊢; linarith
      exact_mod_cast (by linarith : (100 * a : ℝ) ≤ 3 * R)
    · have : (50 * (2 * (R + a) + b) : ℝ) ≤ 103 * (R + a) := by push_cast at h2 ⊢; linarith
      exact_mod_cast (by linarith : (50 * b : ℝ) ≤ 3 * ((R + a : ℕ) : ℝ))
  · rintro ⟨hR, ha, hb⟩
    refine ⟨hR, ?_, ?_⟩
    · have : (100 : ℝ) * a ≤ 3 * R := by exact_mod_cast ha
      push_cast; linarith
    · have : (50 : ℝ) * b ≤ 3 * ((R + a : ℕ) : ℝ) := by exact_mod_cast hb
      push_cast; linarith

theorem ratioStep_two_le {ρ : ℝ} {R a b : ℕ} (h : IsRatioStep ρ R a b) : 2 ≤ ρ := by
  have hR : (0 : ℝ) < R := by exact_mod_cast h.1
  have h1 := h.2.1
  push_cast at h1
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith

theorem ratioStep_whole_le {ρ : ℝ} {R a b : ℕ} (h : IsRatioStep ρ R a b) :
    ((2 * (R + a) + b : ℕ) : ℝ) ≤ ρ ^ 2 / 2 * R := by
  have hρ : 0 ≤ ρ := le_trans (by norm_num) (ratioStep_two_le h)
  nlinarith [h.2.1, h.2.2]

/-- **Uniform all-block-size upper bound on `windowExcess`** on every `ρ`-overlap step. -/
theorem windowExcess_le_analyticEnvelope {Q R a b : ℕ} {ρ C : ℝ} (hstep : IsRatioStep ρ R a b)
    (hC1 : -(1 / 5000) < C) (hC2 : C < -neutralBlock 1 1 1) :
    windowExcess Q R a b C ≤ schurAnalyticEnvelope Q ρ C := by
  have hR := hstep.1
  have hD : 1 ≤ R + a := by omega
  have hρ2 : 2 ≤ ρ := ratioStep_two_le hstep
  have hγ1 : 1 ≤ ρ ^ 2 / 2 := by nlinarith
  have hμ_ge := (bindingEnergy_lt_three hD).1
  have hCμ : C < bindingEnergy (R + a) := lt_of_lt_of_le hC2 hμ_ge
  have hA := (oneBoundState_primeFreeMiddle hD).add_diagonal hCμ (by linarith)
  have hQnn := primeContactSum_nonneg Q
  have hden2 : 0 < 1 / 5000 + C := by linarith
  have henv_nn : 0 ≤ schurAnalyticEnvelope Q ρ C := by
    unfold schurAnalyticEnvelope
    have hl1 : 0 ≤ Real.log (ρ ^ 2 / 2) := Real.log_nonneg hγ1
    have hl2 : 0 ≤ Real.log (1 + ρ ^ 2 / 2) := Real.log_nonneg (by linarith)
    positivity
  rw [windowExcess_le_iff Q R a b C henv_nn]
  intro e
  rw [overlapSchurLevel, Matrix.sub_mulVec, dotProduct_sub, dotProduct_add_diagonal_mulVec,
    dotProduct_transpose_mul_mul_mulVec]
  -- Upper bound on `(P e)ᵀ (M + C)⁻¹ (P e)`
  have hinv_le : (endCoupling Q R a b *ᵥ e) ⬝ᵥ
      ((primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *ᵥ (endCoupling Q R a b *ᵥ e)) ≤
      1 / (1 / 5000 + C) * (34 + 2 * primeContactSum Q) ^ 2 * (e ⬝ᵥ e) := by
    set w := endCoupling Q R a b *ᵥ e
    rw [inv_form_eq_channels _ (groundVector (R + a)) (bindingEnergy (R + a) - C) w]
    have hch := positiveChannel_le hA w
    have hrank_nn : 0 ≤ 1 / (bindingEnergy (R + a) - C) * (groundVector (R + a) ⬝ᵥ w) ^ 2 := by
      have : 0 < bindingEnergy (R + a) - C := by linarith
      positivity
    have hww : w ⬝ᵥ w ≤ (34 + 2 * primeContactSum Q) ^ 2 * (e ⬝ᵥ e) := by
      by_cases hw0 : w ⬝ᵥ w = 0
      · rw [hw0]; positivity
      · have hwpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne (dotProduct_self_star_nonneg (v := w)) (Ne.symm hw0)
        have hsq := dotProduct_endCoupling_mulVec_sq_le Q R a b w e
        nlinarith
    have h1 : 1 / (1 / 5000 + C) * (w ⬝ᵥ w - (groundVector (R + a) ⬝ᵥ w) ^ 2) ≤
        1 / (1 / 5000 + C) * (w ⬝ᵥ w) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (groundVector (R + a) ⬝ᵥ w)]) (by positivity)
    have h2 : 1 / (1 / 5000 + C) * (w ⬝ᵥ w) ≤
        1 / (1 / 5000 + C) * ((34 + 2 * primeContactSum Q) ^ 2 * (e ⬝ᵥ e)) :=
      mul_le_mul_of_nonneg_left hww (by positivity)
    linarith
  -- Lower bound on `eᵀ endForm e` via row sums of `neutralWindow`
  have hend_ge : -(5 + Real.log (ρ ^ 2 / 2) + Real.log (1 + ρ ^ 2 / 2) + 2 * primeContactSum Q) *
      (e ⬝ᵥ e) ≤ e ⬝ᵥ (endForm Q R a b *ᵥ e) := by
    have hsymm : ∀ p q, endForm Q R a b p q = endForm Q R a b q p :=
      fromBlocks_symm (posMatrix_symm (neutralBlock_symm Q) (leftPos R a)) _
        (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b))
    have hoff : ∀ p q, p ≠ q → endForm Q R a b p q ≤ 0 := by
      intro p q hpq
      have hval : endForm Q R a b p q =
          neutralBlock Q (Sum.elim (leftPos R a) (rightPos R a b) p)
            (Sum.elim (leftPos R a) (rightPos R a b) q) := by
        rcases p with i₁ | j₁ <;> rcases q with i₂ | j₂
        · rfl
        · rfl
        · exact neutralBlock_comm Q _ _
        · rfl
      rw [hval, neutralBlock_eq_neg_jet_sub_contact_of_ne Q (fun h => hpq (endPos_injective R a b h))]
      have hlt := min_lt_max.mpr (fun h => hpq (endPos_injective R a b h))
      have hj : 0 < blockJet (min _ _) (max _ _) := by
        rw [blockJet]
        linarith [xLogXDiff_pos (n := min _ _ + max _ _ + 1) (by omega),
          xLogXDiff_pos (n := max _ _ - min _ _) (by omega)]
      have hc : 0 ≤ floorContact Q (min _ _) (max _ _) :=
        Finset.sum_nonneg fun k _ => by
          split_ifs <;> [exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k);
            exact le_rfl]
      linarith
    refine form_ge_of_offDiag_nonpos hsymm hoff (fun p => ?_) e
    set J := a + (R + a) + b
    let idx : Fin a ⊕ Fin b → Fin J := fun q => overlapEquiv a (R + a) b (Sum.inr q)
    have hidx : ∀ q, R + (idx q : ℕ) = Sum.elim (leftPos R a) (rightPos R a b) q := by
      rintro (i | j) <;> simp [idx, overlapEquiv, leftPos, rightPos] <;> omega
    have hwhole_le : ((R + J : ℕ) : ℝ) ≤ ρ ^ 2 / 2 * R := by
      have : R + J = 2 * (R + a) + b := by omega
      rw [this]; exact ratioStep_whole_le hstep
    have hpot := blockPotential_ge_of_ratio (Q := Q) hR (idx p).2 hγ1 hwhole_le
    refine hpot.trans ?_
    rw [blockPotential, ← Fin.sum_univ_eq_sum_range _ J,
      ← (overlapEquiv a (R + a) b).sum_comp (fun l : Fin J => neutralBlock Q (R + (idx p : ℕ)) (R + (l : ℕ))),
      Fintype.sum_sum_type]
    have hmid_nonpos : ∑ m : Fin (R + a),
        neutralBlock Q (R + (idx p : ℕ)) (R + (overlapEquiv a (R + a) b (Sum.inl m) : ℕ)) ≤ 0 := by
      refine Finset.sum_nonpos fun m _ => ?_
      have hmpos : R + (overlapEquiv a (R + a) b (Sum.inl m) : ℕ) = middlePos R a m := by
        simp [overlapEquiv, middlePos]; omega
      rw [hidx p, hmpos, neutralBlock_comm,
        neutralBlock_eq_neg_jet_sub_contact_of_ne Q (middlePos_ne_endPos R a b m p)]
      have hlt := min_lt_max.mpr (middlePos_ne_endPos R a b m p)
      have hj : 0 < blockJet (min _ _) (max _ _) := by
        rw [blockJet]
        linarith [xLogXDiff_pos (n := min _ _ + max _ _ + 1) (by omega),
          xLogXDiff_pos (n := max _ _ - min _ _) (by omega)]
      have hc : 0 ≤ floorContact Q (min _ _) (max _ _) :=
        Finset.sum_nonneg fun k _ => by
          split_ifs <;> [exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k);
            exact le_rfl]
      linarith
    have hend_eq : ∑ q : Fin a ⊕ Fin b,
        neutralBlock Q (R + (idx p : ℕ)) (R + (overlapEquiv a (R + a) b (Sum.inr q) : ℕ)) =
        ∑ q : Fin a ⊕ Fin b, endForm Q R a b p q := by
      refine Finset.sum_congr rfl fun q _ => ?_
      change neutralBlock Q (R + (idx p : ℕ)) (R + (idx q : ℕ)) = _
      rw [hidx p, hidx q]
      rcases p with i₁ | j₁ <;> rcases q with i₂ | j₂
      · rfl
      · rfl
      · exact (neutralBlock_comm Q _ _).symm
      · rfl
    linarith
  have hC_ge : -|C| * (e ⬝ᵥ e) ≤ C * (e ⬝ᵥ e) :=
    mul_le_mul_of_nonneg_right (neg_abs_le C) (dotProduct_self_star_nonneg (v := e))
  unfold schurAnalyticEnvelope
  linarith

/-- **Exact Schur-complement excess of a `ρ`-overlap step at level `C`**, uniform over all block
sizes `R ≥ 1`. -/
def schurStepExcess (Q : ℕ) (ρ C : ℝ) : ℝ :=
  sSup {y : ℝ | y = 0 ∨ ∃ R a b : ℕ, IsRatioStep ρ R a b ∧ y = windowExcess Q R a b C}

/-- **Conditional-coupling operator-norm excess of a `ρ`-overlap step at level `C`**, uniform over
all block sizes `R ≥ 1`. -/
def couplingStepExcess (Q : ℕ) (ρ C : ℝ) : ℝ :=
  sSup {y : ℝ | y = 0 ∨ ∃ R a b : ℕ, IsRatioStep ρ R a b ∧ y = couplingNorm Q R a b C}

theorem schurStepExcess_bddAbove {Q : ℕ} {ρ C : ℝ} (hC1 : -(1 / 5000) < C)
    (hC2 : C < -neutralBlock 1 1 1) :
    BddAbove {y : ℝ | y = 0 ∨ ∃ R a b : ℕ, IsRatioStep ρ R a b ∧ y = windowExcess Q R a b C} := by
  refine ⟨max 0 (schurAnalyticEnvelope Q ρ C), ?_⟩
  rintro y (rfl | ⟨R, a, b, hstep, rfl⟩)
  · exact le_max_left _ _
  · exact (windowExcess_le_analyticEnvelope hstep hC1 hC2).trans (le_max_right _ _)

theorem couplingStepExcess_bddAbove {Q : ℕ} {ρ C : ℝ} (hC1 : -(1 / 5000) < C)
    (hC2 : C < -neutralBlock 1 1 1) :
    BddAbove {y : ℝ | y = 0 ∨ ∃ R a b : ℕ, IsRatioStep ρ R a b ∧ y = couplingNorm Q R a b C} := by
  refine ⟨max 0 (couplingAnalyticEnvelope Q C), ?_⟩
  rintro y (rfl | ⟨R, a, b, hstep, rfl⟩)
  · exact le_max_left _ _
  · exact (couplingNorm_le_analyticEnvelope hstep.1 hC1 hC2).trans (le_max_right _ _)

theorem schurStepExcess_nonneg (Q : ℕ) (ρ C : ℝ) : 0 ≤ schurStepExcess Q ρ C := by
  unfold schurStepExcess
  by_cases h : BddAbove {y : ℝ | y = 0 ∨ ∃ R a b : ℕ, IsRatioStep ρ R a b ∧ y = windowExcess Q R a b C}
  · exact le_csSup h (Or.inl rfl)
  · rw [Real.sSup_of_not_bddAbove h]

theorem couplingStepExcess_nonneg (Q : ℕ) (ρ C : ℝ) : 0 ≤ couplingStepExcess Q ρ C := by
  unfold couplingStepExcess
  by_cases h : BddAbove {y : ℝ | y = 0 ∨ ∃ R a b : ℕ, IsRatioStep ρ R a b ∧ y = couplingNorm Q R a b C}
  · exact le_csSup h (Or.inl rfl)
  · rw [Real.sSup_of_not_bddAbove h]

theorem windowExcess_le_schurStepExcess {Q R a b : ℕ} {ρ C : ℝ} (hstep : IsRatioStep ρ R a b)
    (hC1 : -(1 / 5000) < C) (hC2 : C < -neutralBlock 1 1 1) :
    windowExcess Q R a b C ≤ schurStepExcess Q ρ C :=
  le_csSup (schurStepExcess_bddAbove hC1 hC2) (Or.inr ⟨R, a, b, hstep, rfl⟩)

theorem couplingNorm_le_couplingStepExcess {Q R a b : ℕ} {ρ C : ℝ} (hstep : IsRatioStep ρ R a b)
    (hC1 : -(1 / 5000) < C) (hC2 : C < -neutralBlock 1 1 1) :
    couplingNorm Q R a b C ≤ couplingStepExcess Q ρ C :=
  le_csSup (couplingStepExcess_bddAbove hC1 hC2) (Or.inr ⟨R, a, b, hstep, rfl⟩)

theorem schurStepExcess_le_analyticEnvelope {Q : ℕ} {ρ C : ℝ} (hρ : 2 ≤ ρ)
    (hC1 : -(1 / 5000) < C) (hC2 : C < -neutralBlock 1 1 1) :
    schurStepExcess Q ρ C ≤ schurAnalyticEnvelope Q ρ C := by
  have henv_nn : 0 ≤ schurAnalyticEnvelope Q ρ C := by
    unfold schurAnalyticEnvelope
    have hl1 : 0 ≤ Real.log (ρ ^ 2 / 2) := Real.log_nonneg (by nlinarith)
    have hl2 : 0 ≤ Real.log (1 + ρ ^ 2 / 2) := Real.log_nonneg (by nlinarith)
    have hden2 : 0 < 1 / 5000 + C := by linarith
    have hQnn := primeContactSum_nonneg Q
    positivity
  refine csSup_le ⟨0, Or.inl rfl⟩ ?_
  rintro y (rfl | ⟨R, a, b, hstep, rfl⟩)
  · exact henv_nn
  · exact windowExcess_le_analyticEnvelope hstep hC1 hC2

theorem couplingStepExcess_le_analyticEnvelope {Q : ℕ} {ρ C : ℝ}
    (hC1 : -(1 / 5000) < C) (hC2 : C < -neutralBlock 1 1 1) :
    couplingStepExcess Q ρ C ≤ couplingAnalyticEnvelope Q C := by
  have henv_nn : 0 ≤ couplingAnalyticEnvelope Q C := by
    unfold couplingAnalyticEnvelope
    have hden1 : 0 < -neutralBlock 1 1 1 - C := by linarith
    have hden2 : 0 < 1 / 5000 + C := by linarith
    have hQnn := primeContactSum_nonneg Q
    positivity
  refine csSup_le ⟨0, Or.inl rfl⟩ ?_
  rintro y (rfl | ⟨R, a, b, hstep, rfl⟩)
  · exact henv_nn
  · exact couplingNorm_le_analyticEnvelope hstep.1 hC1 hC2

/-- When every window up to ratio `ρ` holds at most one bound state at level `C`,
`schurStepExcess Q ρ C ≤ couplingStepExcess Q ρ C`. -/
theorem schurStepExcess_le_couplingStepExcess {Q : ℕ} {ρ C : ℝ}
    (hC1 : -(1 / 5000) < C) (hC2 : C < -neutralBlock 1 1 1)
    (hcert : ∀ R J : ℕ, 1 ≤ R → R ≤ J → ((R + J : ℕ) : ℝ) ≤ ρ * R →
      hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => C).map (↑) :
        Matrix (Fin J) (Fin J) ℂ) ≤ 1) :
    schurStepExcess Q ρ C ≤ couplingStepExcess Q ρ C := by
  refine csSup_le ⟨0, Or.inl rfl⟩ ?_
  rintro y (rfl | ⟨R, a, b, hstep, rfl⟩)
  · exact couplingStepExcess_nonneg Q ρ C
  · have hD : 1 ≤ R + a := by linarith [hstep.1]
    have hCμ : C < bindingEnergy (R + a) := lt_of_lt_of_le hC2 (bindingEnergy_lt_three hD).1
    have hL := hcert R (a + (R + a)) hstep.1 (by omega) (by
      have : R + (a + (R + a)) = 2 * (R + a) := by omega
      rw [this]; exact_mod_cast hstep.2.1)
    have hR' := hcert (R + a) ((R + a) + b) hD (by omega) (by
      have : (R + a) + ((R + a) + b) = 2 * (R + a) + b := by omega
      rw [this]; exact hstep.2.2)
    exact (windowExcess_le_couplingNorm hstep.1 hC1 hCμ hL hR').trans
      (couplingNorm_le_couplingStepExcess hstep hC1 hC2)

/-- At level `0`, `schurStepExcess Q ρ 0 = 0` iff the Green inequality holds on every `ρ`-overlap
step. -/
theorem schurStepExcess_zero_eq_zero_iff_greenForm (Q : ℕ) (ρ : ℝ) :
    schurStepExcess Q ρ 0 = 0 ↔
      ∀ R a b : ℕ, IsRatioStep ρ R a b → ∀ e : Fin a ⊕ Fin b → ℝ,
        (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) ≤
          e ⬝ᵥ (endForm Q R a b *ᵥ e) +
            (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) := by
  have hC1 : -(1 / 5000 : ℝ) < 0 := by norm_num
  have hC2 : (0 : ℝ) < -neutralBlock 1 1 1 := by
    rw [neutralBlock_one_one, neg_neg]
    linarith [dyadicDepth_mem.1]
  rw [le_antisymm_iff, and_iff_left (schurStepExcess_nonneg Q ρ 0)]
  constructor
  · intro h R a b hstep
    have hw : windowExcess Q R a b 0 = 0 :=
      le_antisymm ((windowExcess_le_schurStepExcess hstep hC1 hC2).trans h)
        (windowExcess_nonneg Q R a b 0)
    have hR := hstep.1
    exact (windowExcess_zero_eq_zero_iff_greenForm (by omega)).mp hw
  · intro h
    refine csSup_le ⟨0, Or.inl rfl⟩ ?_
    rintro y (rfl | ⟨R, a, b, hstep, rfl⟩)
    · exact le_rfl
    · have hR := hstep.1
      rw [(windowExcess_zero_eq_zero_iff_greenForm (by omega)).mpr (h R a b hstep)]

/-! ### Sharp prime-`2` regime up to ratio `3` and breakdown past ratio `3` -/

/-- Up to ratio `3` (`J ≤ 2 R`), no prime `k ≥ 3` enters `neutralWindow Q R J`. -/
theorem neutralWindow_eq_two_of_le_two_mul {Q R J : ℕ} (hQ : 2 ≤ Q) (hJ : J ≤ 2 * R) :
    neutralWindow Q R J = neutralWindow 2 R J := by
  ext i l
  simp only [neutralWindow, windowMatrix, Matrix.of_apply]
  exact neutralBlock_eq_of_le hQ (by have := i.2; have := l.2; omega)

/-- **Sharp prime-`2` boundary**: for `1 ≤ R` and `3 ≤ Q`, `neutralWindow Q R J = neutralWindow 2 R J`
if and only if `J ≤ 2 R`. -/
theorem neutralWindow_eq_two_iff_le_two_mul {Q R J : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q) :
    neutralWindow Q R J = neutralWindow 2 R J ↔ J ≤ 2 * R := by
  refine ⟨fun heq => ?_, neutralWindow_eq_two_of_le_two_mul (by omega)⟩
  by_contra hgt
  have hlt : 2 * R < J := not_le.mp hgt
  have hent := congrArg (fun M => M ⟨0, by omega⟩ ⟨2 * R, hlt⟩) heq
  simp only [neutralWindow, windowMatrix, Matrix.of_apply, Nat.add_zero] at hent
  have h2R : R + 2 * R = 3 * R := by omega
  rw [h2R, neutralBlock_of_lt (by omega : R < 3 * R),
    neutralBlock_of_lt (by omega : R < 3 * R)] at hent
  have hcon : floorContact 2 R (3 * R) < floorContact Q R (3 * R) := by
    rw [floorContact_eq_sum_floorGraph 2 (by omega), floorContact_eq_sum_floorGraph Q (by omega)]
    have hsplit : Icc 2 Q = insert 2 (insert 3 (Icc 4 Q)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2only : Icc 2 2 = {2} := by ext k; simp; omega
    rw [h2only, Finset.sum_singleton, hsplit, Finset.sum_insert (by simp),
      Finset.sum_insert (by simp)]
    have hg3 : 0 < floorGraph 3 R (3 * R) := by
      rw [floorGraph_of_le 3 (by omega), if_pos (Nat.mul_div_right 3 hR), vonMangoldt_three]
      linarith [log_three_mem.1]
    have hrest : 0 ≤ ∑ k ∈ Icc 4 Q, floorGraph k R (3 * R) :=
      Finset.sum_nonneg fun k _ => by
        rw [floorGraph]; split_ifs
        · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
        · exact le_rfl
    linarith
  linarith

/-- **Prime `2` alone fails past ratio `3` (`(2, 8]`)**: on the 6-block window `(2, 8]` at `Q = 2`,
the disjoint packets `e₀` (block `2`) and `e₄ + e₅` (blocks `6, 7`) form an unbound negative pair,
giving at least two bound states. -/
theorem two_le_hermNegIndex_primeTwo_two_six :
    2 ≤ hermNegIndex ((neutralWindow 2 2 6).map (↑) : Matrix (Fin 6) (Fin 6) ℂ) := by
  let v₁ : Fin 6 → ℝ := Pi.single ⟨0, by decide⟩ 1
  let v₂ : Fin 6 → ℝ := Pi.single ⟨4, by decide⟩ 1 + Pi.single ⟨5, by decide⟩ 1
  have hv₁ : bilin (neutralWindow 2 2 6) v₁ v₁ = -thirdDepth := by
    rw [bilin_eq_sum_mul_mulVec]
    simp only [v₁, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, neutralWindow, windowMatrix, Matrix.of_apply]
    exact neutralBlock_two_two 2
  have hv₂_eq : bilin (neutralWindow 2 2 6) v₂ v₂ =
      -(2 * dyadicDepth + 8 * Real.log 2 + 18 * Real.log 3 - 14 * Real.log 7) := by
    have hbil : bilin (neutralWindow 2 2 6) v₂ v₂ =
        neutralBlock 2 6 6 + 2 * neutralBlock 2 6 7 + neutralBlock 2 7 7 := by
      rw [bilin_eq_sum_mul_mulVec]
      simp only [v₂, Matrix.mulVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib,
        Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, neutralWindow,
        windowMatrix, Matrix.of_apply]
      have hc := neutralBlock_comm 2 7 6
      norm_num; linarith
    have hm66 := windowClosed_succ (a := 6) (by norm_num) 2
    have hm77 := windowClosed_succ (a := 7) (by norm_num) 2
    have hm67 := windowClosed_mixed (a := 6) (b := 7) (by norm_num) 2
    have hw77 := windowClosed_self (x := 7) (by norm_num) 2
    norm_num at hm66 hm77 hm67
    have hsum_bm : blockMatrix 2 6 6 + 2 * blockMatrix 2 6 7 + blockMatrix 2 7 7 =
        windowClosed 2 6 8 := by linarith
    have hwc68 : windowClosed 2 6 8 = windowSmooth 6 8 := by
      rw [windowClosed, show Icc 2 2 = {2} by ext k; simp; omega, Finset.sum_singleton,
        max_eq_right (by norm_num), mul_zero, mul_zero, sub_zero]
    have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hl14 : Real.log 14 = Real.log 2 + Real.log 7 := by
      rw [show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [hbil, neutralBlock, neutralBlock, neutralBlock]
    have hdeg : 2 * blockDegree 6 + 2 * (blockDegree 6 + blockDegree 7) + 2 * blockDegree 7 =
        4 * (Real.log 8 - Real.log 6) := by
      simp only [blockDegree]; norm_num; ring
    have hws : windowSmooth 6 8 - 4 * (Real.log 8 - Real.log 6) =
        -(2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) +
          14 * Real.log 2 + 12 * Real.log 3 - 14 * Real.log 7) := by
      rw [windowSmooth]
      norm_num [hl6, hl8, hl14, Real.log_two]
      ring
    rw [dyadicDepth]
    linarith
  have hv₁₂_eq : bilin (neutralWindow 2 2 6) v₁ v₂ =
      -(11 * Real.log 11 + 12 * Real.log 2 - 9 * Real.log 3 - 15 * Real.log 5) / 2 := by
    have hbil : bilin (neutralWindow 2 2 6) v₁ v₂ =
        neutralBlock 2 2 6 + neutralBlock 2 2 7 := by
      rw [bilin_eq_sum_mul_mulVec]
      simp only [v₁, v₂, Matrix.mulVec_add, Pi.add_apply, Pi.single_apply, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mulVec, dotProduct,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, neutralWindow, windowMatrix,
        Matrix.of_apply]
      norm_num
    have hc26 : floorContact 2 2 6 = 0 := by
      rw [floorContact, show Icc 2 2 = {2} by ext k; simp; omega, Finset.sum_singleton,
        if_neg (by norm_num)]
    have hc27 : floorContact 2 2 7 = 0 := by
      rw [floorContact, show Icc 2 2 = {2} by ext k; simp; omega, Finset.sum_singleton,
        if_neg (by norm_num)]
    rw [hbil, neutralBlock_of_lt (by norm_num), neutralBlock_of_lt (by norm_num), hc26, hc27]
    simp only [blockJet, xLogXDiff, xLogX]
    norm_num
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hl9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl10 : Real.log 10 = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [hl4, hl6, hl8, hl9, hl10]
    ring
  have hv₁_lt : bilin (neutralWindow 2 2 6) v₁ v₁ < -0.6027 := by
    linarith [hv₁, thirdDepth_gt]
  have hv₂_lt : bilin (neutralWindow 2 2 6) v₂ v₂ < -0.467 := by
    rw [hv₂_eq]
    linarith [dyadicDepth_mem.1, Real.log_two_gt_d9, log_three_mem.1, log_seven_mem.2]
  have hv₁₂_mem : -0.333 < bilin (neutralWindow 2 2 6) v₁ v₂ ∧
      bilin (neutralWindow 2 2 6) v₁ v₂ < 0 := by
    rw [hv₁₂_eq]
    constructor <;> linarith [log_eleven_mem.1, log_eleven_mem.2, Real.log_two_gt_d9,
      Real.log_two_lt_d9, log_three_mem.1, log_three_mem.2, log_five_mem.1, log_five_mem.2]
  refine two_le_hermNegIndex_of_unbound_pair (neutralWindow_symm 2 2 6) (by linarith) ?_
  have hsq : bilin (neutralWindow 2 2 6) v₁ v₂ ^ 2 < 0.333 ^ 2 :=
    sq_lt_sq' hv₁₂_mem.1 (by linarith [hv₁₂_mem.2])
  have hprod : 0.6027 * 0.467 <
      bilin (neutralWindow 2 2 6) v₁ v₁ * bilin (neutralWindow 2 2 6) v₂ v₂ := by
    nlinarith
  linarith

/-- On even block sizes `R = 2 m` (`1 ≤ m`), `neutralWindow 2 (2 m) J` holds at least two bound
states for every `J ≥ 6 m`. -/
theorem two_le_hermNegIndex_primeTwo_even {m J : ℕ} (hm : 1 ≤ m) (hJ : 6 * m ≤ J) :
    2 ≤ hermNegIndex ((neutralWindow 2 (2 * m) J).map (↑) : Matrix (Fin J) (Fin J) ℂ) := by
  have href := hermNegIndex_neutralWindow_le_refined (R := 2) (by norm_num) hm 2 6
  rw [Nat.mul_comm m 2, Nat.mul_comm m 6] at href
  exact (two_le_hermNegIndex_primeTwo_two_six.trans href).trans
    (hermNegIndex_windowMatrix_mono _ _ hJ)

/-- **Prime `2` alone fails at every block size `R ≥ 2` once `J ≥ 3 R + 4`**. -/
theorem two_le_hermNegIndex_primeTwo {R J : ℕ} (hR : 2 ≤ R) (hJ : 3 * R + 4 ≤ J) :
    2 ≤ hermNegIndex ((neutralWindow 2 R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) := by
  rcases Nat.even_or_odd' R with ⟨m, rfl | rfl⟩
  · exact two_le_hermNegIndex_primeTwo_even (by omega) (by omega)
  · set m' := m + 1
    have hm' : 1 ≤ m' := by omega
    have heven := two_le_hermNegIndex_primeTwo_even hm' (le_rfl : 6 * m' ≤ 6 * m')
    let emb : Fin (6 * m') ↪ Fin J :=
      ⟨fun i => ⟨1 + i, by have := i.2; omega⟩, fun i₁ i₂ h => by
        simp only [Fin.ext_iff] at h; exact Fin.ext (by omega)⟩
    have hsub : ((neutralWindow 2 R J).map (↑) : Matrix (Fin J) (Fin J) ℂ).submatrix emb emb =
        (neutralWindow 2 (2 * m') (6 * m')).map (↑) := by
      ext i l
      simp only [Matrix.submatrix_apply, Matrix.map_apply, neutralWindow, windowMatrix,
        Matrix.of_apply, emb, Function.Embedding.coeFn_mk]
      congr 2 <;> omega
    rw [← hsub] at heven
    exact heven.trans (HeckeKreinToeplitz.hermNegIndex_submatrix_le _ emb)

/-- **Prime `3` restores positivity on `span{e₀, e₄ + e₅}` in `(2, 8]`**: for every `Q ≥ 3`, the
floor map `x ↦ ⌊x / 3⌋` sends both `6` and `7` to `2`, reversing the discriminant sign. -/
theorem primeThree_restores_positivity_two_six {Q : ℕ} (hQ : 3 ≤ Q) :
    let v₁ : Fin 6 → ℝ := Pi.single ⟨0, by decide⟩ 1
    let v₂ : Fin 6 → ℝ := Pi.single ⟨4, by decide⟩ 1 + Pi.single ⟨5, by decide⟩ 1
    bilin (neutralWindow Q 2 6) v₁ v₁ * bilin (neutralWindow Q 2 6) v₂ v₂ <
      bilin (neutralWindow Q 2 6) v₁ v₂ ^ 2 := by
  intro v₁ v₂
  have hv₁ : bilin (neutralWindow Q 2 6) v₁ v₁ = -thirdDepth := by
    rw [bilin_eq_sum_mul_mulVec]
    simp only [v₁, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, neutralWindow, windowMatrix, Matrix.of_apply]
    exact neutralBlock_two_two Q
  have hv₂_eq : bilin (neutralWindow Q 2 6) v₂ v₂ = bilin (neutralWindow 2 2 6) v₂ v₂ := by
    have h66 : neutralBlock Q 6 6 = neutralBlock 2 6 6 :=
      neutralBlock_eq_of_le (by omega) (by norm_num)
    have h67 : neutralBlock Q 6 7 = neutralBlock 2 6 7 :=
      neutralBlock_eq_of_le (by omega) (by norm_num)
    have h76 : neutralBlock Q 7 6 = neutralBlock 2 7 6 :=
      neutralBlock_eq_of_le (by omega) (by norm_num)
    have h77 : neutralBlock Q 7 7 = neutralBlock 2 7 7 :=
      neutralBlock_eq_of_le (by omega) (by norm_num)
    rw [bilin_eq_sum_mul_mulVec, bilin_eq_sum_mul_mulVec]
    simp only [v₂, Matrix.mulVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, neutralWindow,
      windowMatrix, Matrix.of_apply]
    norm_num [h66, h67, h76, h77]
  have hv₂_gt : -0.478 < bilin (neutralWindow Q 2 6) v₂ v₂ := by
    rw [hv₂_eq]
    have hbil : bilin (neutralWindow 2 2 6) v₂ v₂ =
        neutralBlock 2 6 6 + 2 * neutralBlock 2 6 7 + neutralBlock 2 7 7 := by
      rw [bilin_eq_sum_mul_mulVec]
      simp only [v₂, Matrix.mulVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib,
        Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, neutralWindow,
        windowMatrix, Matrix.of_apply]
      have hc := neutralBlock_comm 2 7 6
      norm_num; linarith
    have hm66 := windowClosed_succ (a := 6) (by norm_num) 2
    have hm77 := windowClosed_succ (a := 7) (by norm_num) 2
    have hm67 := windowClosed_mixed (a := 6) (b := 7) (by norm_num) 2
    have hw77 := windowClosed_self (x := 7) (by norm_num) 2
    norm_num at hm66 hm77 hm67
    have hwc68 : windowClosed 2 6 8 = windowSmooth 6 8 := by
      rw [windowClosed, show Icc 2 2 = {2} by ext k; simp; omega, Finset.sum_singleton,
        max_eq_right (by norm_num), mul_zero, mul_zero, sub_zero]
    have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hl14 : Real.log 14 = Real.log 2 + Real.log 7 := by
      rw [show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [hbil, neutralBlock, neutralBlock, neutralBlock]
    have hws : windowSmooth 6 8 -
        (2 * blockDegree 6 + 2 * (blockDegree 6 + blockDegree 7) + 2 * blockDegree 7) =
        -(2 * dyadicDepth + 8 * Real.log 2 + 18 * Real.log 3 - 14 * Real.log 7) := by
      rw [windowSmooth, dyadicDepth]
      simp only [blockDegree]
      norm_num [hl6, hl8, hl14, Real.log_two]
      ring
    linarith [dyadicDepth_mem.2, Real.log_two_lt_d9, log_three_mem.2, log_seven_mem.1]
  have hv₁_gt : -0.604 < bilin (neutralWindow Q 2 6) v₁ v₁ := by
    rw [hv₁, thirdDepth]
    have h3d : thirdDepth = dyadicDepth + 6 * Real.log 2 + 3 * Real.log 3 - 5 * Real.log 5 := by
      rw [thirdDepth, dyadicDepth]; ring
    rw [h3d]
    linarith [dyadicDepth_mem.2, Real.log_two_lt_d9, log_three_mem.2, log_five_mem.1]
  have hv₁₂_lt : bilin (neutralWindow Q 2 6) v₁ v₂ < -1 := by
    have hbil : bilin (neutralWindow Q 2 6) v₁ v₂ =
        neutralBlock 3 2 6 + neutralBlock 3 2 7 := by
      rw [bilin_eq_sum_mul_mulVec]
      simp only [v₁, v₂, Matrix.mulVec_add, Pi.add_apply, Pi.single_apply, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mulVec, dotProduct,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, neutralWindow, windowMatrix,
        Matrix.of_apply]
      have h26 : neutralBlock Q 2 6 = neutralBlock 3 2 6 := neutralBlock_eq_of_le hQ (by norm_num)
      have h27 : neutralBlock Q 2 7 = neutralBlock 3 2 7 := neutralBlock_eq_of_le hQ (by norm_num)
      norm_num [h26, h27]
    have hc3_26 : floorContact 3 2 6 = Real.log 3 / 3 := by
      rw [floorContact, show Icc 2 3 = {2, 3} by ext k; simp; omega,
        Finset.sum_insert (by norm_num), Finset.sum_singleton, if_neg (by norm_num),
        if_pos (by norm_num), vonMangoldt_three]
      norm_num
    have hc3_27 : floorContact 3 2 7 = Real.log 3 / 3 := by
      rw [floorContact, show Icc 2 3 = {2, 3} by ext k; simp; omega,
        Finset.sum_insert (by norm_num), Finset.sum_singleton, if_neg (by norm_num),
        if_pos (by norm_num), vonMangoldt_three]
      norm_num
    rw [hbil, neutralBlock_of_lt (by norm_num), neutralBlock_of_lt (by norm_num), hc3_26, hc3_27]
    simp only [blockJet, xLogXDiff, xLogX]
    norm_num
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hl9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl10 : Real.log 10 = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [hl4, hl6, hl8, hl9, hl10]
    linarith [log_eleven_mem.1, Real.log_two_gt_d9, log_three_mem.1, log_three_mem.2,
      log_five_mem.2]
  have hv₁_neg : bilin (neutralWindow Q 2 6) v₁ v₁ < 0 := by linarith [hv₁, thirdDepth_gt]
  have hv₂_neg : bilin (neutralWindow Q 2 6) v₂ v₂ < 0 := by
    rw [hv₂_eq]
    have hbil : bilin (neutralWindow 2 2 6) v₂ v₂ =
        neutralBlock 2 6 6 + 2 * neutralBlock 2 6 7 + neutralBlock 2 7 7 := by
      rw [bilin_eq_sum_mul_mulVec]
      simp only [v₂, Matrix.mulVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib,
        Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, neutralWindow,
        windowMatrix, Matrix.of_apply]
      have hc := neutralBlock_comm 2 7 6
      norm_num; linarith
    have hm66 := windowClosed_succ (a := 6) (by norm_num) 2
    have hm77 := windowClosed_succ (a := 7) (by norm_num) 2
    have hm67 := windowClosed_mixed (a := 6) (b := 7) (by norm_num) 2
    have hw77 := windowClosed_self (x := 7) (by norm_num) 2
    norm_num at hm66 hm77 hm67
    have hwc68 : windowClosed 2 6 8 = windowSmooth 6 8 := by
      rw [windowClosed, show Icc 2 2 = {2} by ext k; simp; omega, Finset.sum_singleton,
        max_eq_right (by norm_num), mul_zero, mul_zero, sub_zero]
    have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hl14 : Real.log 14 = Real.log 2 + Real.log 7 := by
      rw [show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [hbil, neutralBlock, neutralBlock, neutralBlock]
    have hws : windowSmooth 6 8 -
        (2 * blockDegree 6 + 2 * (blockDegree 6 + blockDegree 7) + 2 * blockDegree 7) =
        -(2 * dyadicDepth + 8 * Real.log 2 + 18 * Real.log 3 - 14 * Real.log 7) := by
      rw [windowSmooth, dyadicDepth]
      simp only [blockDegree]
      norm_num [hl6, hl8, hl14, Real.log_two]
      ring
    linarith [dyadicDepth_mem.1, Real.log_two_gt_d9, log_three_mem.1, log_seven_mem.2]
  have hprod : bilin (neutralWindow Q 2 6) v₁ v₁ * bilin (neutralWindow Q 2 6) v₂ v₂ < 1 := by
    nlinarith
  have hsq : 1 < bilin (neutralWindow Q 2 6) v₁ v₂ ^ 2 := by nlinarith
  linarith

/-! ### Zero-rounding rational ratio-squaring step and the ladder `2.06 → 2.1218 → 2.25 → 2.53 → 3.21` -/

/-- **Zero-rounding rational ratio-squaring step**: for `ρ = p / q` (`1 ≤ q`, `2 q ≤ p`), refining
by `m = 2 q²` splits every window of ratio at most `ρ² / 2` across `(q p R, 2 q p R]` with zero
integer-rounding loss, propagating `hermNegIndex ≤ 1` from `(ρ, C)` to
`(ρ² / 2, C + schurStepExcess Q ρ C)` at **every** block size `R ≥ 1`. -/
theorem hermNegIndex_le_one_of_sq_div_two (Q : ℕ) {p q : ℕ} (hq : 1 ≤ q) (hpq : 2 * q ≤ p)
    {C : ℝ} (hC1 : -(1 / 5000) < C) (hC2 : C < -neutralBlock 1 1 1)
    (hcert : ∀ R J : ℕ, 1 ≤ R → R ≤ J → ((R + J : ℕ) : ℝ) ≤ ((p : ℝ) / q) * R →
      hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => C).map (↑) :
        Matrix (Fin J) (Fin J) ℂ) ≤ 1)
    {R J : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hJ : ((R + J : ℕ) : ℝ) ≤ (((p : ℝ) / q) ^ 2 / 2) * R) :
    hermNegIndex ((neutralWindow Q R J +
        Matrix.diagonal fun _ => (C + schurStepExcess Q ((p : ℝ) / q) C)).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  set ρ : ℝ := (p : ℝ) / q
  set x : ℝ := schurStepExcess Q ρ C
  have hx : 0 ≤ x := schurStepExcess_nonneg Q ρ C
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- If `(R, R + J]` already has ratio `≤ ρ`, monotonicity in the level closes directly.
  rcases le_or_gt ((R + J : ℕ) : ℝ) (ρ * R) with hshort | hlong
  · exact (hermNegIndex_add_diagonal_mono (neutralWindow Q R J) (by linarith : C ≤ C + x)).trans
      (hcert R J hR hRJ hshort)
  · -- Refine by `m = 2 q²` and split at `a' = q (p − 2 q) R`
    set m : ℕ := 2 * q ^ 2
    have hm : 1 ≤ m := by nlinarith
    set R' : ℕ := m * R
    set J' : ℕ := m * J
    set a' : ℕ := q * (p - 2 * q) * R
    have hR'a' : R' + a' = q * p * R := by
      dsimp [R', a', m]
      have hsub : 2 * q ^ 2 + q * (p - 2 * q) = q * p := by
        zify [hpq]; ring
      calc 2 * q ^ 2 * R + q * (p - 2 * q) * R
          = (2 * q ^ 2 + q * (p - 2 * q)) * R := (Nat.add_mul _ _ R).symm
        _ = q * p * R := by rw [hsub]
    have hlt_mid : 2 * (R' + a') < R' + J' := by
      have : (2 * q * p * R : ℝ) < (2 * q ^ 2 * (R + J) : ℝ) := by
        dsimp [ρ] at hlong
        rw [div_mul_eq_mul_div, lt_div_iff₀ hq0] at hlong
        push_cast at hlong ⊢
        nlinarith
      have hnat : 2 * q * p * R < m * (R + J) := by exact_mod_cast this
      rw [hR'a']
      dsimp [R', J']
      omega
    have hle_top : R' + J' ≤ p ^ 2 * R := by
      have : (2 * q ^ 2 * (R + J) : ℝ) ≤ (p ^ 2 * R : ℝ) := by
        dsimp [ρ] at hJ
        have hq2 : (0 : ℝ) < 2 * (q : ℝ) ^ 2 := by positivity
        have heq : ((p : ℝ) / q) ^ 2 / 2 * R = (p : ℝ) ^ 2 * R / (2 * (q : ℝ) ^ 2) := by ring
        rw [heq, le_div_iff₀ hq2] at hJ
        push_cast at hJ ⊢
        linarith
      have hnat : m * (R + J) ≤ p ^ 2 * R := by exact_mod_cast this
      dsimp [R', J']
      omega
    set b' : ℕ := R' + J' - 2 * (R' + a')
    have hJ'_eq : J' = a' + (R' + a') + b' := by omega
    have hstep : IsRatioStep ρ R' a' b' := by
      refine ⟨by nlinarith, ?_, ?_⟩
      · rw [hR'a']
        dsimp [ρ, R', m]
        field_simp [hq0.ne']
        push_cast; ring
      · have htot : 2 * (R' + a') + b' = R' + J' := by omega
        rw [htot, hR'a']
        dsimp [ρ]
        rw [div_mul_eq_mul_div, le_div_iff₀ hq0]
        have : ((R' + J') * q : ℝ) ≤ (p ^ 2 * R * q : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_right q hle_top
        push_cast at this ⊢
        linarith
    have hex_le : windowExcess Q R' a' b' C ≤ x :=
      windowExcess_le_schurStepExcess hstep hC1 hC2
    have hS : ∀ e : Fin a' ⊕ Fin b' → ℝ, -x * (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchurLevel Q R' a' b' C *ᵥ e) :=
      (windowExcess_le_iff Q R' a' b' C hx).mp hex_le
    have hD' : 1 ≤ R' + a' := by linarith [hstep.1]
    have hCμ : C < bindingEnergy (R' + a') := lt_of_lt_of_le hC2 (bindingEnergy_lt_three hD').1
    have href_whole := hermNegIndex_neutralWindow_add_le_one_of_schurLevel (Q := Q) a' b'
      hstep.1 hC1 hCμ hx hS
    rw [← hJ'_eq] at href_whole
    exact (hermNegIndex_neutralWindow_add_le_refined hR hm Q J (C + x)).trans href_whole

/-- Numerators of the exact ratio-squaring sequence starting at `103 / 50`. -/
def iteratedNum : ℕ → ℕ
  | 0 => 103
  | k + 1 => (iteratedNum k) ^ 2

/-- Denominators of the exact ratio-squaring sequence starting at `103 / 50`. -/
def iteratedDen : ℕ → ℕ
  | 0 => 50
  | k + 1 => 2 * (iteratedDen k) ^ 2

/-- Exact rational ratio sequence `ρ₀ = 103 / 50`, `ρ_{k+1} = ρ_k² / 2`. -/
def iteratedRatio (k : ℕ) : ℝ := (iteratedNum k : ℝ) / (iteratedDen k : ℝ)

theorem iteratedDen_pos (k : ℕ) : 1 ≤ iteratedDen k := by
  induction k with
  | zero => norm_num [iteratedDen]
  | succ k ih => simp only [iteratedDen]; nlinarith

theorem two_mul_iteratedDen_le_num (k : ℕ) : 2 * iteratedDen k ≤ iteratedNum k := by
  induction k with
  | zero => norm_num [iteratedDen, iteratedNum]
  | succ k ih =>
    simp only [iteratedDen, iteratedNum]
    nlinarith

theorem iteratedRatio_succ (k : ℕ) : iteratedRatio (k + 1) = (iteratedRatio k) ^ 2 / 2 := by
  simp only [iteratedRatio, iteratedNum, iteratedDen]
  have hd : (iteratedDen k : ℝ) ≠ 0 := by exact_mod_cast (iteratedDen_pos k).ne'
  push_cast
  field_simp [hd]

/-- Closed-form exponential growth `iteratedRatio k = 2 · (103 / 100) ^ (2 ^ k)`. -/
theorem iteratedRatio_eq (k : ℕ) : iteratedRatio k = 2 * (103 / 100 : ℝ) ^ (2 ^ k) := by
  induction k with
  | zero => norm_num [iteratedRatio, iteratedNum, iteratedDen]
  | succ k ih =>
    rw [iteratedRatio_succ, ih, pow_succ, pow_mul]
    ring

/-- **Milestones of the ratio ladder** (`2.06 → 2.1218 → 2.25 → 2.53 → 3.209 > 3 → 3.21`):
four steps surpass `2.25`, `2.53`, and `3` (`> 3.209`), and the fifth step surpasses `3.21`. -/
theorem iteratedRatio_milestones :
    iteratedRatio 0 = 103 / 50 ∧
      iteratedRatio 1 = 10609 / 5000 ∧
      9 / 4 < iteratedRatio 2 ∧
      253 / 100 < iteratedRatio 3 ∧
      3209 / 1000 < iteratedRatio 4 ∧
      321 / 100 < iteratedRatio 5 := by
  have h0 : iteratedRatio 0 = 103 / 50 := by norm_num [iteratedRatio_eq]
  have h1 : iteratedRatio 1 = 10609 / 5000 := by norm_num [iteratedRatio_eq]
  have h2_gt : 2251 / 1000 < iteratedRatio 2 := by
    rw [iteratedRatio_succ, h1]; norm_num
  have h3_gt : 25335 / 10000 < iteratedRatio 3 := by
    rw [iteratedRatio_succ]
    have : (2251 / 1000 : ℝ) ^ 2 / 2 < (iteratedRatio 2) ^ 2 / 2 := by nlinarith
    linarith [show (25335 / 10000 : ℝ) < (2251 / 1000) ^ 2 / 2 by norm_num]
  have h4_gt : 3209 / 1000 < iteratedRatio 4 := by
    rw [iteratedRatio_succ]
    have : (25335 / 10000 : ℝ) ^ 2 / 2 < (iteratedRatio 3) ^ 2 / 2 := by nlinarith
    linarith [show (3209 / 1000 : ℝ) < (25335 / 10000) ^ 2 / 2 by norm_num]
  have h5_gt : 321 / 100 < iteratedRatio 5 := by
    rw [iteratedRatio_succ]
    have : (3209 / 1000 : ℝ) ^ 2 / 2 < (iteratedRatio 4) ^ 2 / 2 := by nlinarith
    linarith [show (321 / 100 : ℝ) < (3209 / 1000) ^ 2 / 2 by norm_num]
  exact ⟨h0, h1, by linarith, by linarith, h4_gt, h5_gt⟩

/-- Cumulative level loss after `k` ratio-squaring steps at prime cutoff `Q`. -/
def levelAt (Q : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => levelAt Q k + schurStepExcess Q (iteratedRatio k) (levelAt Q k)

theorem levelAt_nonneg (Q k : ℕ) : 0 ≤ levelAt Q k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact add_nonneg ih (schurStepExcess_nonneg Q _ _)

theorem levelAt_mono (Q : ℕ) : Monotone (levelAt Q) :=
  monotone_nat_of_le_succ fun k => le_add_of_nonneg_right (schurStepExcess_nonneg Q _ _)

/-- **Inductive propagation along the ratio-squaring ladder**: for every `Q ≥ 2` and `k : ℕ`, if
`levelAt Q k < -neutralBlock 1 1 1`, then every window of ratio at most `iteratedRatio (k + 1)`
holds at most one bound state at level `levelAt Q (k + 1)`, at **every** block size `R ≥ 1`. -/
theorem hermNegIndex_le_one_of_levelAt {Q : ℕ} (hQ : 2 ≤ Q) (k : ℕ)
    (hk : levelAt Q k < -neutralBlock 1 1 1) {R J : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hJ : ((R + J : ℕ) : ℝ) ≤ iteratedRatio (k + 1) * R) :
    hermNegIndex ((neutralWindow Q R J +
        Matrix.diagonal fun _ => levelAt Q (k + 1)).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  induction k generalizing R J with
  | zero =>
    have hbase : ∀ R₀ J₀ : ℕ, 1 ≤ R₀ → R₀ ≤ J₀ →
        ((R₀ + J₀ : ℕ) : ℝ) ≤ ((iteratedNum 0 : ℝ) / iteratedDen 0) * R₀ →
        hermNegIndex ((neutralWindow Q R₀ J₀ + Matrix.diagonal fun _ => levelAt Q 0).map (↑) :
          Matrix (Fin J₀) (Fin J₀) ℂ) ≤ 1 := by
      intro R₀ J₀ hR₀ hRJ₀ hJ₀
      rw [levelAt, Matrix.diagonal_zero, add_zero]
      have h53 : 50 * J₀ ≤ 53 * R₀ := by
        simp only [iteratedNum, iteratedDen] at hJ₀
        have : (50 * (R₀ + J₀) : ℝ) ≤ 103 * R₀ := by push_cast at hJ₀ ⊢; linarith
        have hnat : 50 * (R₀ + J₀) ≤ 103 * R₀ := by exact_mod_cast this
        omega
      exact (hermNegIndex_neutralWindow_eq_one hR₀ hRJ₀ h53 hQ).le
    rw [iteratedRatio_succ] at hJ
    exact hermNegIndex_le_one_of_sq_div_two Q (iteratedDen_pos 0)
      (two_mul_iteratedDen_le_num 0) (by rw [levelAt]; norm_num) hk hbase hR hRJ hJ
  | succ k ih =>
    have hk_prev : levelAt Q k < -neutralBlock 1 1 1 :=
      lt_of_le_of_lt (levelAt_mono Q (Nat.le_succ k)) hk
    have hC1 : -(1 / 5000 : ℝ) < levelAt Q (k + 1) := by
      linarith [levelAt_nonneg Q (k + 1)]
    rw [iteratedRatio_succ] at hJ
    exact hermNegIndex_le_one_of_sq_div_two Q (iteratedDen_pos (k + 1))
      (two_mul_iteratedDen_le_num (k + 1)) hC1 hk
      (fun R₀ J₀ hR₀ hRJ₀ hJ₀ => ih hk_prev hR₀ hRJ₀ hJ₀) hR hRJ hJ

/-- **Unconditional first-step bound (`k = 0`)**: at ratio `10609 / 5000 = 2.1218` and every block
size `R ≥ 1`, `neutralWindow Q R J` holds at most one bound state at level `levelAt Q 1`. -/
theorem hermNegIndex_firstStep_le_one {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hJ : 5000 * (R + J) ≤ 10609 * R) :
    hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => levelAt Q 1).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  have hk0 : levelAt Q 0 < -neutralBlock 1 1 1 := by
    rw [levelAt, neutralBlock_one_one, neg_neg]
    linarith [dyadicDepth_mem.1]
  refine hermNegIndex_le_one_of_levelAt hQ 0 hk0 hR hRJ ?_
  rw [iteratedRatio_milestones.2.1]
  have : (5000 * (R + J) : ℝ) ≤ 10609 * R := by exact_mod_cast hJ
  push_cast at this ⊢; linarith

/-- **Four-step theorem for `(R, 3R]` at every block size**: if `levelAt 2 3 < -neutralBlock 1 1 1`
(across `2.06 → 2.1218 → 2.25 → 2.53`), then for every `Q ≥ 2`, `R ≥ 1`, and `R ≤ J ≤ 2 R`
(including `(R, 3R]`), `neutralWindow Q R J` holds at most one bound state at level `levelAt 2 4`;
when `levelAt 2 4 = 0`, it holds **one** bound state at every block size. -/
theorem hermNegIndex_ratio_three_le_one (h3 : levelAt 2 3 < -neutralBlock 1 1 1)
    {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R) (hRJ : R ≤ J) (hJ : J ≤ 2 * R) :
    hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => levelAt 2 4).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  rw [neutralWindow_eq_two_of_le_two_mul hQ hJ]
  refine hermNegIndex_le_one_of_levelAt le_rfl 3 h3 hR hRJ ?_
  have h4 := iteratedRatio_milestones.2.2.2.2.1
  have h3R : ((R + J : ℕ) : ℝ) ≤ 3 * (R : ℝ) := by exact_mod_cast (by omega : R + J ≤ 3 * R)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  nlinarith

theorem hermNegIndex_ratio_three_eq_one_of_levelAt_zero (h0 : levelAt 2 4 = 0)
    {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R) (hRJ : R ≤ J) (hJ : J ≤ 2 * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 := by
  have h3_zero : levelAt 2 3 = 0 :=
    le_antisymm ((levelAt_mono 2 (by norm_num : 3 ≤ 4)).trans h0.le) (levelAt_nonneg 2 3)
  have h3 : levelAt 2 3 < -neutralBlock 1 1 1 := by
    rw [h3_zero, neutralBlock_one_one, neg_neg]
    linarith [dyadicDepth_mem.1]
  have hle := hermNegIndex_ratio_three_le_one h3 hQ hR hRJ hJ
  rw [h0, Matrix.diagonal_zero, add_zero] at hle
  exact le_antisymm hle (one_le_hermNegIndex_neutralWindow Q hR hRJ)

/-- **Aperture theorem for `(R, 3R]` at every block size**: if Weil's ground energy is nonnegative
at an aperture `A` with `log 3 < 2 A`, then every window `(R, R + J]` with `R ≤ J ≤ 2 R` (`Q ≥ 2`)
holds **one** bound state at every block size `R ≥ 1`. -/
theorem hermNegIndex_ratio_three_eq_one_of_groundEnergy_nonneg
    {A : _root_.RHTower.SuzukiPositiveAperture} (hA : Real.log 3 < 2 * A.1)
    (hge : 0 ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A)
    {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R) (hRJ : R ≤ J) (hJ : J ≤ 2 * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 := by
  rw [neutralWindow_eq_two_of_le_two_mul hQ hJ,
    ← neutralWindow_eq_two_of_le_two_mul (Q := 3) (by norm_num) hJ]
  have hle : hermNegIndex ((neutralWindow 3 R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
    refine hermNegIndex_le_one_of_nonneg_on_hyperplane (neutralWindow 3 R J) (fun _ => 1)
      fun y hy => ?_
    rw [AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, neutralWindow, sum_fin_windowMatrix_eq]
    have hsum0 : ∑ j ∈ range J, extendFin y j = 0 := by
      rw [← sum_fin_eq_sum_range_extendFin]
      simpa [dotProduct] using hy
    rw [sum_neutralBlock_eq_of_charge_zero (Or.inl hsum0),
      ← packetForm_stepPacket_eq_sum_blockMatrix hR 3 J (extendFin y)]
    have hlen : Real.log ((R + J : ℕ) : ℝ) - Real.log R ≤ Real.log 3 := by
      have hR' : (0 : ℝ) < R := by exact_mod_cast hR
      have hle3 : ((R + J : ℕ) : ℝ) ≤ 3 * R := by exact_mod_cast (by omega : R + J ≤ 3 * R)
      have hl := Real.log_le_log (by positivity) hle3
      rw [Real.log_mul (by norm_num) hR'.ne'] at hl
      linarith
    have hlogQ : Real.log ((R + J : ℕ) : ℝ) - Real.log R < Real.log ((3 : ℝ) + 1) := by
      have hl34 : Real.log 3 < Real.log ((3 : ℝ) + 1) := Real.log_lt_log (by norm_num) (by norm_num)
      linarith
    have hfl : _root_.RHTower.ccmRestrictedWeilGroundEnergy A *
        packetAutocorr (stepPacket R J (extendFin y)) 0 ≤
        packetForm 3 (stepPacket R J (extendFin y)) := by
      simp only [stepPacket_eq_nested hR J (extendFin y)]
      exact groundEnergy_mul_nested_mass_le_packetForm_of_log_lt hR (nested_bounds R J)
        (nestedCoeff J (extendFin y)) (by linarith) hlogQ
    rw [packetAutocorr_stepPacket_zero hR J (extendFin y)] at hfl
    exact le_trans
      (mul_nonneg hge (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hfl
  exact le_antisymm hle (one_le_hermNegIndex_neutralWindow 3 hR hRJ)

/-! ### Global 0-or-escape quantization law of the iterated excess tower -/

/-- Prime cutoff covering all windows of ratio up to `iteratedRatio (k + 1)`. -/
def towerCutoff (k : ℕ) : ℕ :=
  iteratedNum (k + 1) / iteratedDen (k + 1) + 2

/-- Cumulative excess after `k + 1` steps at the matching prime cutoff `towerCutoff k`. -/
def globalTowerLevel (k : ℕ) : ℝ :=
  levelAt (towerCutoff k) (k + 1)

theorem iteratedRatio_succ_le_towerCutoff (k : ℕ) :
    iteratedRatio (k + 1) ≤ towerCutoff k := by
  rw [iteratedRatio, towerCutoff]
  have hd : (0 : ℝ) < iteratedDen (k + 1) := by exact_mod_cast iteratedDen_pos (k + 1)
  rw [div_le_iff₀ hd]
  have hdiv : iteratedNum (k + 1) < (iteratedNum (k + 1) / iteratedDen (k + 1) + 2) *
      iteratedDen (k + 1) := by
    have hmod := Nat.div_add_mod (iteratedNum (k + 1)) (iteratedDen (k + 1))
    have hlt := Nat.mod_lt (iteratedNum (k + 1)) (iteratedDen_pos (k + 1))
    nlinarith [iteratedDen_pos (k + 1)]
  exact_mod_cast hdiv.le

theorem two_le_towerCutoff (k : ℕ) : 2 ≤ towerCutoff k := by
  unfold towerCutoff; omega

theorem levelAt_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis) {Q : ℕ} (k : ℕ)
    (hQ : iteratedRatio k ≤ Q) : levelAt Q k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_le : iteratedRatio k ≤ iteratedRatio (k + 1) := by
      rw [iteratedRatio_eq, iteratedRatio_eq]
      have : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) this) (by norm_num)
    have hprev : levelAt Q k = 0 := ih (hk_le.trans hQ)
    rw [levelAt, hprev, zero_add]
    rw [schurStepExcess_zero_eq_zero_iff_greenForm]
    intro R a b hstep e
    have hwhole := ratioStep_whole_le hstep
    rw [← iteratedRatio_succ] at hwhole
    have hQR : R + (a + (R + a) + b) ≤ Q * R := by
      have htot : ((R + (a + (R + a) + b) : ℕ) : ℝ) ≤ (Q * R : ℕ) := by
        have h1 : R + (a + (R + a) + b) = 2 * (R + a) + b := by omega
        rw [h1]
        have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        push_cast
        exact hwhole.trans (mul_le_mul_of_nonneg_right hQ hR0)
      exact_mod_cast htot
    have hS := overlapSchur_nonneg_of_riemannHypothesis hRH hstep.1 hQR e
    rw [overlapSchur_form_eq_channels Q R a b (by have := hstep.1; omega)] at hS
    linarith

/-- **Global quantization equivalence (zero loss)**: `RiemannHypothesis` holds iff
`globalTowerLevel k = 0` at every step `k`. -/
theorem riemannHypothesis_iff_globalTowerLevel_zero :
    RiemannHypothesis ↔ ∀ k : ℕ, globalTowerLevel k = 0 := by
  constructor
  · intro hRH k
    exact levelAt_eq_zero_of_riemannHypothesis hRH (k + 1) (iteratedRatio_succ_le_towerCutoff k)
  · intro h0
    rw [riemannHypothesis_iff_initialWindow_margin_bddBelow]
    refine ⟨0, fun M hM => ?_⟩
    -- Choose `k` with `2 M ≤ iteratedRatio (k + 1)` via Bernoulli's inequality
    set k := 17 * M
    have h2M_le : (2 * M : ℝ) ≤ iteratedRatio (k + 1) := by
      rw [iteratedRatio_eq]
      have hbern := one_add_mul_le_pow (x := (3 / 100 : ℝ)) (by norm_num) (2 ^ (k + 1))
      rw [show (1 : ℝ) + 3 / 100 = 103 / 100 by norm_num] at hbern
      have hpow : (k + 1 : ℝ) ≤ (2 ^ (k + 1) : ℕ) := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k + 1)).le
      push_cast at hpow
      dsimp [k] at hpow
      nlinarith
    have hQ_ge : M + M ≤ towerCutoff k := by
      have : ((M + M : ℕ) : ℝ) ≤ (towerCutoff k : ℝ) := by
        push_cast
        linarith [h2M_le, iteratedRatio_succ_le_towerCutoff k]
      exact_mod_cast this
    have hwin_eq : neutralWindow (M + M) 1 (M + M - 1) =
        neutralWindow (towerCutoff k) 1 (M + M - 1) := by
      ext i l
      simp only [neutralWindow, windowMatrix, Matrix.of_apply]
      exact (neutralBlock_eq_of_le hQ_ge (by have := i.2; have := l.2; omega)).symm
    have hk_lt : levelAt (towerCutoff k) k < -neutralBlock 1 1 1 := by
      have hk0 : levelAt (towerCutoff k) k = 0 :=
        le_antisymm
          ((levelAt_mono (towerCutoff k) (Nat.le_succ k)).trans (h0 k).le)
          (levelAt_nonneg _ _)
      rw [hk0, neutralBlock_one_one, neg_neg]
      linarith [dyadicDepth_mem.1]
    have hle := hermNegIndex_le_one_of_levelAt (two_le_towerCutoff k) k hk_lt le_rfl (by omega)
      (by
        have : 1 + (M + M - 1) = 2 * M := by omega
        rw [this, mul_one]; exact_mod_cast h2M_le)
    rw [hwin_eq]
    change hermNegIndex ((neutralWindow (towerCutoff k) 1 (M + M - 1) +
      Matrix.diagonal fun _ => (0 : ℝ)).map (↑) : Matrix _ _ ℂ) ≤ 1
    rw [← h0 k]
    exact hle

/-- **0-or-escape quantization law**: a positive cumulative loss cannot iterate indefinitely below
the binding energy `-neutralBlock 1 1 1` of the dyadic middle; `globalTowerLevel` stays uniformly
below `-neutralBlock 1 1 1` iff it vanishes identically (`globalTowerLevel k = 0` for all `k`),
iff `RiemannHypothesis` holds. -/
theorem riemannHypothesis_iff_exists_lt_dyadicDepth_globalTowerLevel :
    RiemannHypothesis ↔
      ∃ C : ℝ, C < -neutralBlock 1 1 1 ∧ ∀ k : ℕ, globalTowerLevel k ≤ C := by
  constructor
  · intro hRH
    refine ⟨0, ?_, fun k => ?_⟩
    · rw [neutralBlock_one_one, neg_neg]; linarith [dyadicDepth_mem.1]
    · rw [riemannHypothesis_iff_globalTowerLevel_zero.mp hRH k]
  · rintro ⟨C, hC_lt, hC⟩
    rw [riemannHypothesis_iff_initialWindow_margin_bddBelow]
    refine ⟨C, fun M hM => ?_⟩
    set k := 17 * M
    have h2M_le : (2 * M : ℝ) ≤ iteratedRatio (k + 1) := by
      rw [iteratedRatio_eq]
      have hbern := one_add_mul_le_pow (x := (3 / 100 : ℝ)) (by norm_num) (2 ^ (k + 1))
      rw [show (1 : ℝ) + 3 / 100 = 103 / 100 by norm_num] at hbern
      have hpow : (k + 1 : ℝ) ≤ (2 ^ (k + 1) : ℕ) := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k + 1)).le
      push_cast at hpow
      dsimp [k] at hpow
      nlinarith
    have hQ_ge : M + M ≤ towerCutoff k := by
      have : ((M + M : ℕ) : ℝ) ≤ (towerCutoff k : ℝ) := by
        push_cast
        linarith [h2M_le, iteratedRatio_succ_le_towerCutoff k]
      exact_mod_cast this
    have hwin_eq : neutralWindow (M + M) 1 (M + M - 1) =
        neutralWindow (towerCutoff k) 1 (M + M - 1) := by
      ext i l
      simp only [neutralWindow, windowMatrix, Matrix.of_apply]
      exact (neutralBlock_eq_of_le hQ_ge (by have := i.2; have := l.2; omega)).symm
    have hk_lt : levelAt (towerCutoff k) k < -neutralBlock 1 1 1 :=
      lt_of_le_of_lt ((levelAt_mono (towerCutoff k) (Nat.le_succ k)).trans (hC k)) hC_lt
    have hle := hermNegIndex_le_one_of_levelAt (two_le_towerCutoff k) k hk_lt le_rfl (by omega)
      (by
        have : 1 + (M + M - 1) = 2 * M := by omega
        rw [this, mul_one]; exact_mod_cast h2M_le)
    rw [hwin_eq]
    exact (hermNegIndex_add_diagonal_mono _ (hC k)).trans hle

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
