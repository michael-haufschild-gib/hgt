import GaloisForLFunctions.RHTower.CircleHardyPhaseTraceIndex

/-!
# Hilbert–Schmidt energy of the Hankel seams of a circle symbol

Let `P` be the Hardy projection on `L²(ℝ/ℤ)`, `Q = 1 - P`, and `M_a` multiplication by a bounded
measurable symbol `a`.  In the Fourier basis the seam `Q M_a P` has entries `â(l - j)` for
`l < 0 ≤ j`, so its Hilbert–Schmidt energy is

`‖Q M_a P‖²_HS = ∑_{j ≥ 0} ∑_{l < 0} |â(l - j)|² = ∑_{n ≥ 1} n |â(-n)|²`,

and symmetrically `‖P M_a Q‖²_HS = ∑_{n ≥ 1} n |â(n)|²`.  The Hardy commutator is
`[P, M_a] = P M_a Q - Q M_a P`; it is Hilbert–Schmidt exactly when both half-Sobolev energies are
finite, with `‖[P, M_a]‖²_HS = ∑_{n ≠ 0} |n| |â(n)|²`.

For a unimodular phase `u` of finite half-Sobolev energy the pair `(M_u† P M_u, P)` is a
restricted-unitary datum, and its cubic trace is the signed first moment
`Tr (M_u† P M_u - P)³ = ∑_{n ≥ 1} n |û(n)|² - ∑_{n ≥ 1} n |û(-n)|²`, an integer (the relative
index).  No absolute summability of `n û(n)` is assumed: this is the critical Hilbert–Schmidt
boundary, which contains every continuous piecewise `C¹` phase.
-/

noncomputable section

open Complex MeasureTheory ContinuousLinearMap Filter
open scoped ENNReal InnerProductSpace

namespace RHTower

/-! ## Fourier energy of a circle vector -/

theorem fourierBasis_eq_fourierLp (l : ℤ) :
    (fourierBasis (T := (1 : ℝ))) l = (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2) := by
  rw [coe_fourierBasis]

/-- Parseval in the Fourier basis: `‖v‖² = ∑_l |⟨e_l, v⟩|²`. -/
theorem hasSum_norm_inner_fourierLp_sq (v : CCMCircleL2) :
    HasSum (fun l : ℤ => ‖inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2) v‖ ^ 2)
      (‖v‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) ((fourierBasis (T := (1 : ℝ))).repr v)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at h
  refine h.congr_fun fun l => ?_
  rw [(fourierBasis (T := (1 : ℝ))).repr_apply_apply, fourierBasis_eq_fourierLp]

/-- Tail-sum rearrangement: `∑_{a} ∑_{b} E(a + b) = ∑_n (n + 1) E(n)` for nonnegative `E`. -/
theorem hasSum_tsum_nat_add_of_nonneg {E : ℕ → ℝ} (hE : ∀ n, 0 ≤ E n)
    (h : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * E n) :
    HasSum (fun a : ℕ => ∑' b : ℕ, E (a + b)) (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * E n) := by
  let G : (Σ m : ℕ, Finset.HasAntidiagonal.antidiagonal (A := ℕ) m) → ℝ := fun x => E x.1
  have hfib : ∀ m : ℕ, HasSum (fun y : Finset.HasAntidiagonal.antidiagonal (A := ℕ) m =>
      G ⟨m, y⟩) (((m + 1 : ℕ) : ℝ) * E m) := by
    intro m
    convert hasSum_fintype (fun y : Finset.HasAntidiagonal.antidiagonal (A := ℕ) m => G ⟨m, y⟩)
      using 1
    simp only [G, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    rw [Finset.Nat.card_antidiagonal]
  have hG : Summable G :=
    (summable_sigma_of_nonneg (fun x => hE x.1)).2
      ⟨fun m => (hfib m).summable, h.congr fun m => (hfib m).tsum_eq.symm⟩
  have hGsum : HasSum G (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * E n) := by
    have := hG.hasSum
    rwa [hG.tsum_sigma' (fun m => (hfib m).summable), tsum_congr fun m => (hfib m).tsum_eq]
      at this
  let F : ℕ × ℕ → ℝ := fun p => E (p.1 + p.2)
  have hFG : F ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd = G := by
    funext x
    obtain ⟨m, p, hp⟩ := x
    change E (p.1 + p.2) = E m
    rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hp]
  have hF : HasSum F (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * E n) := by
    rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff, hFG]
    exact hGsum
  refine hF.prod_fiberwise fun a => ?_
  have hEs : Summable E :=
    Summable.of_nonneg_of_le hE (fun n => by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith [hE n]) h
  exact ((summable_nat_add_iff a).2 hEs |>.congr fun b => by rw [add_comm]).hasSum
    |>.congr_fun fun b => rfl

/-- Energy of an operator supported on the block `l < 0 ≤ j` with Toeplitz entries `c(l - j)`. -/
theorem lowerBlock_isHilbertSchmidt_hsNormSq
    (S : CCMCircleL2 →L[ℂ] CCMCircleL2) (c : ℤ → ℂ)
    (hS : ∀ l j : ℤ, inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (S (fourierLp (T := (1 : ℝ)) 2 j)) = if l < 0 ∧ 0 ≤ j then c (l - j) else 0)
    (hc : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖c (-((n + 1 : ℕ) : ℤ))‖ ^ 2) :
    S.IsHilbertSchmidt ∧
      hsNormSq S = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖c (-((n + 1 : ℕ) : ℤ))‖ ^ 2 := by
  let E : ℕ → ℝ := fun n => ‖c (-((n + 1 : ℕ) : ℤ))‖ ^ 2
  have hE : ∀ n, 0 ≤ E n := fun n => sq_nonneg _
  have hEs : Summable E :=
    Summable.of_nonneg_of_le hE (fun n => by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith [hE n]) hc
  have hcol_nat : ∀ a : ℕ,
      ‖S (fourierLp (T := (1 : ℝ)) 2 (a : ℤ))‖ ^ 2 = ∑' b : ℕ, E (a + b) := by
    intro a
    refine (hasSum_norm_inner_fourierLp_sq _).unique ?_
    have hnat : HasSum (fun n : ℕ => ‖inner ℂ (fourierLp (T := (1 : ℝ)) 2 (n : ℤ) : CCMCircleL2)
        (S (fourierLp (T := (1 : ℝ)) 2 (a : ℤ)))‖ ^ 2) 0 := by
      convert hasSum_zero using 1
      funext n
      rw [hS, if_neg (fun h => absurd h.1 (by omega))]
      simp
    have hneg : HasSum (fun n : ℕ => ‖inner ℂ (fourierLp (T := (1 : ℝ)) 2 (-((n : ℤ) + 1)) :
        CCMCircleL2) (S (fourierLp (T := (1 : ℝ)) 2 (a : ℤ)))‖ ^ 2) (∑' b : ℕ, E (a + b)) := by
      refine ((summable_nat_add_iff a).2 hEs |>.congr fun b => by rw [add_comm]).hasSum
        |>.congr_fun fun b => ?_
      rw [hS, if_pos ⟨by omega, by omega⟩]
      simp only [E]
      congr 3
      push_cast
      ring
    have h := HasSum.of_nat_of_neg_add_one (f := fun l : ℤ =>
      ‖inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (S (fourierLp (T := (1 : ℝ)) 2 (a : ℤ)))‖ ^ 2) hnat hneg
    rwa [zero_add] at h
  have hcol_neg : ∀ a : ℕ, ‖S (fourierLp (T := (1 : ℝ)) 2 (-((a : ℤ) + 1)))‖ ^ 2 = 0 := by
    intro a
    refine (hasSum_norm_inner_fourierLp_sq _).unique ?_
    convert hasSum_zero using 1
    funext l
    rw [hS, if_neg (fun h => absurd h.2 (by omega))]
    simp
  have hsum : HasSum (fun j : ℤ => ‖S ((fourierBasis (T := (1 : ℝ))) j)‖ ^ 2)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * E n) := by
    have h1 : HasSum (fun a : ℕ => ‖S ((fourierBasis (T := (1 : ℝ))) (a : ℤ))‖ ^ 2)
        (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * E n) := by
      refine (hasSum_tsum_nat_add_of_nonneg hE hc).congr_fun fun a => ?_
      rw [fourierBasis_eq_fourierLp, hcol_nat]
    have h2 : HasSum (fun a : ℕ => ‖S ((fourierBasis (T := (1 : ℝ))) (-((a : ℤ) + 1)))‖ ^ 2)
        0 := by
      convert hasSum_zero using 1
      funext a
      rw [fourierBasis_eq_fourierLp, hcol_neg]
    have h := HasSum.of_nat_of_neg_add_one
      (f := fun j : ℤ => ‖S ((fourierBasis (T := (1 : ℝ))) j)‖ ^ 2) h1 h2
    rwa [add_zero] at h
  have hHS : S.IsHilbertSchmidt :=
    isHilbertSchmidt_of_summable (fourierBasis (T := (1 : ℝ))) hsum.summable
  exact ⟨hHS, (hsNormSq_eq hHS (fourierBasis (T := (1 : ℝ)))).trans hsum.tsum_eq⟩

/-- Energy of an operator supported on the block `j < 0 ≤ l` with Toeplitz entries `c(l - j)`. -/
theorem upperBlock_isHilbertSchmidt_hsNormSq
    (S : CCMCircleL2 →L[ℂ] CCMCircleL2) (c : ℤ → ℂ)
    (hS : ∀ l j : ℤ, inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (S (fourierLp (T := (1 : ℝ)) 2 j)) = if 0 ≤ l ∧ j < 0 then c (l - j) else 0)
    (hc : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖c ((n + 1 : ℕ) : ℤ)‖ ^ 2) :
    S.IsHilbertSchmidt ∧
      hsNormSq S = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖c ((n + 1 : ℕ) : ℤ)‖ ^ 2 := by
  let E : ℕ → ℝ := fun n => ‖c ((n + 1 : ℕ) : ℤ)‖ ^ 2
  have hE : ∀ n, 0 ≤ E n := fun n => sq_nonneg _
  have hEs : Summable E :=
    Summable.of_nonneg_of_le hE (fun n => by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith [hE n]) hc
  have hcol_neg : ∀ a : ℕ,
      ‖S (fourierLp (T := (1 : ℝ)) 2 (-((a : ℤ) + 1)))‖ ^ 2 = ∑' b : ℕ, E (a + b) := by
    intro a
    refine (hasSum_norm_inner_fourierLp_sq _).unique ?_
    have hnat : HasSum (fun n : ℕ => ‖inner ℂ (fourierLp (T := (1 : ℝ)) 2 (n : ℤ) : CCMCircleL2)
        (S (fourierLp (T := (1 : ℝ)) 2 (-((a : ℤ) + 1))))‖ ^ 2) (∑' b : ℕ, E (a + b)) := by
      refine ((summable_nat_add_iff a).2 hEs |>.congr fun b => by rw [add_comm]).hasSum
        |>.congr_fun fun b => ?_
      rw [hS, if_pos ⟨by omega, by omega⟩]
      simp only [E]
      congr 3
      push_cast
      ring
    have hneg : HasSum (fun n : ℕ => ‖inner ℂ (fourierLp (T := (1 : ℝ)) 2 (-((n : ℤ) + 1)) :
        CCMCircleL2) (S (fourierLp (T := (1 : ℝ)) 2 (-((a : ℤ) + 1))))‖ ^ 2) 0 := by
      convert hasSum_zero using 1
      funext n
      rw [hS, if_neg (fun h => absurd h.1 (by omega))]
      simp
    have h := HasSum.of_nat_of_neg_add_one (f := fun l : ℤ =>
      ‖inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (S (fourierLp (T := (1 : ℝ)) 2 (-((a : ℤ) + 1))))‖ ^ 2) hnat hneg
    rwa [add_zero] at h
  have hcol_nat : ∀ a : ℕ, ‖S (fourierLp (T := (1 : ℝ)) 2 (a : ℤ))‖ ^ 2 = 0 := by
    intro a
    refine (hasSum_norm_inner_fourierLp_sq _).unique ?_
    convert hasSum_zero using 1
    funext l
    rw [hS, if_neg (fun h => absurd h.2 (by omega))]
    simp
  have hsum : HasSum (fun j : ℤ => ‖S ((fourierBasis (T := (1 : ℝ))) j)‖ ^ 2)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * E n) := by
    have h1 : HasSum (fun a : ℕ => ‖S ((fourierBasis (T := (1 : ℝ))) (a : ℤ))‖ ^ 2) 0 := by
      convert hasSum_zero using 1
      funext a
      rw [fourierBasis_eq_fourierLp, hcol_nat]
    have h2 : HasSum (fun a : ℕ => ‖S ((fourierBasis (T := (1 : ℝ))) (-((a : ℤ) + 1)))‖ ^ 2)
        (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * E n) := by
      refine (hasSum_tsum_nat_add_of_nonneg hE hc).congr_fun fun a => ?_
      rw [fourierBasis_eq_fourierLp, hcol_neg]
    have h := HasSum.of_nat_of_neg_add_one
      (f := fun j : ℤ => ‖S ((fourierBasis (T := (1 : ℝ))) j)‖ ^ 2) h1 h2
    rwa [zero_add] at h
  have hHS : S.IsHilbertSchmidt :=
    isHilbertSchmidt_of_summable (fourierBasis (T := (1 : ℝ))) hsum.summable
  exact ⟨hHS, (hsNormSq_eq hHS (fourierBasis (T := (1 : ℝ)))).trans hsum.tsum_eq⟩

/-! ## Seams of a bounded symbol -/

theorem inner_fourierLp_ccmCircleMultiplier (a : CCMCircleBoundedSymbol) (l j : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (ccmCircleMultiplier a (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) =
      fourierCoeff a.toFun (l - j) := by
  rw [GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff, ccmCircleMultiplier_fourierCoeff]

/-- The seam `Q M_a P`: positive frequencies sent to negative ones. -/
def ccmCircleForwardSeam (a : CCMCircleBoundedSymbol) : CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  (1 - ccmCircleHardyProjection) * ccmCircleMultiplier a * ccmCircleHardyProjection

/-- The seam `P M_a Q`: negative frequencies sent to positive ones. -/
def ccmCircleBackwardSeam (a : CCMCircleBoundedSymbol) : CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  ccmCircleHardyProjection * ccmCircleMultiplier a * (1 - ccmCircleHardyProjection)

theorem inner_fourierLp_ccmCircleForwardSeam (a : CCMCircleBoundedSymbol) (l j : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (ccmCircleForwardSeam a (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) =
      if l < 0 ∧ 0 ≤ j then fourierCoeff a.toFun (l - j) else 0 := by
  change inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
    ((1 - ccmCircleHardyProjection) (ccmCircleMultiplier a
      (ccmCircleHardyProjection (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)))) = _
  rw [inner_fourierLp_one_sub_ccmCircleHardyProjection]
  by_cases hl : l < 0
  · rw [if_pos hl]
    by_cases hj : 0 ≤ j
    · rw [ccmCircleHardyProjection_fourierLp, if_pos hj, inner_fourierLp_ccmCircleMultiplier,
        if_pos ⟨hl, hj⟩]
    · rw [ccmCircleHardyProjection_fourierLp, if_neg hj]
      simp [hj]
  · rw [if_neg hl, if_neg (fun h => hl h.1)]

theorem inner_fourierLp_ccmCircleBackwardSeam (a : CCMCircleBoundedSymbol) (l j : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (ccmCircleBackwardSeam a (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) =
      if 0 ≤ l ∧ j < 0 then fourierCoeff a.toFun (l - j) else 0 := by
  change inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
    (ccmCircleHardyProjection (ccmCircleMultiplier a
      ((1 - ccmCircleHardyProjection) (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)))) = _
  rw [inner_fourierLp_ccmCircleHardyProjection]
  by_cases hl : 0 ≤ l
  · rw [if_pos hl]
    by_cases hj : 0 ≤ j
    · rw [show (1 - ccmCircleHardyProjection)
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) = 0 by
          simp [ccmCircleHardyProjection_fourierLp, hj]]
      simp [hj]
    · have hjlt : j < 0 := lt_of_not_ge hj
      rw [show (1 - ccmCircleHardyProjection)
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) =
            (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) by
          simp [ccmCircleHardyProjection_fourierLp, hj]]
      rw [inner_fourierLp_ccmCircleMultiplier, if_pos ⟨hl, hjlt⟩]
  · rw [if_neg hl, if_neg (fun h => hl h.1)]

/-- The Hardy commutator splits into its two seams: `[P, M_a] = P M_a Q - Q M_a P`. -/
theorem ccmCircleHardyCommutator_eq_seams (a : CCMCircleBoundedSymbol) :
    ccmCircleHardyProjection * ccmCircleMultiplier a -
        ccmCircleMultiplier a * ccmCircleHardyProjection =
      ccmCircleBackwardSeam a - ccmCircleForwardSeam a := by
  have hPP : ccmCircleHardyProjection * ccmCircleHardyProjection = ccmCircleHardyProjection :=
    ccmCircleHardyProjection_idempotent
  rw [ccmCircleBackwardSeam, ccmCircleForwardSeam]
  noncomm_ring [hPP]

/-- A bounded circle symbol with finite half-Sobolev energy `∑_{n ≠ 0} |n| |â(n)|² < ∞`. -/
structure CCMCircleHankelSymbol extends CCMCircleBoundedSymbol where
  positiveEnergy : Summable fun n : ℕ =>
    ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff toFun ((n + 1 : ℕ) : ℤ)‖ ^ 2
  negativeEnergy : Summable fun n : ℕ =>
    ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff toFun (-((n + 1 : ℕ) : ℤ))‖ ^ 2

namespace CCMCircleHankelSymbol

variable (a : CCMCircleHankelSymbol)

theorem forwardSeam_isHilbertSchmidt :
    (ccmCircleForwardSeam a.toCCMCircleBoundedSymbol).IsHilbertSchmidt :=
  (lowerBlock_isHilbertSchmidt_hsNormSq _ _
    (inner_fourierLp_ccmCircleForwardSeam a.toCCMCircleBoundedSymbol) a.negativeEnergy).1

/-- `‖Q M_a P‖²_HS = ∑_{n ≥ 1} n |â(-n)|²`. -/
theorem hsNormSq_forwardSeam :
    hsNormSq (ccmCircleForwardSeam a.toCCMCircleBoundedSymbol) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff a.toFun (-((n + 1 : ℕ) : ℤ))‖ ^ 2 :=
  (lowerBlock_isHilbertSchmidt_hsNormSq _ _
    (inner_fourierLp_ccmCircleForwardSeam a.toCCMCircleBoundedSymbol) a.negativeEnergy).2

theorem backwardSeam_isHilbertSchmidt :
    (ccmCircleBackwardSeam a.toCCMCircleBoundedSymbol).IsHilbertSchmidt :=
  (upperBlock_isHilbertSchmidt_hsNormSq _ _
    (inner_fourierLp_ccmCircleBackwardSeam a.toCCMCircleBoundedSymbol) a.positiveEnergy).1

/-- `‖P M_a Q‖²_HS = ∑_{n ≥ 1} n |â(n)|²`. -/
theorem hsNormSq_backwardSeam :
    hsNormSq (ccmCircleBackwardSeam a.toCCMCircleBoundedSymbol) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff a.toFun ((n + 1 : ℕ) : ℤ)‖ ^ 2 :=
  (upperBlock_isHilbertSchmidt_hsNormSq _ _
    (inner_fourierLp_ccmCircleBackwardSeam a.toCCMCircleBoundedSymbol) a.positiveEnergy).2

theorem commutator_isHilbertSchmidt :
    (ccmCircleHardyProjection * ccmCircleMultiplier a.toCCMCircleBoundedSymbol -
      ccmCircleMultiplier a.toCCMCircleBoundedSymbol * ccmCircleHardyProjection).IsHilbertSchmidt := by
  rw [ccmCircleHardyCommutator_eq_seams]
  exact a.backwardSeam_isHilbertSchmidt.sub a.forwardSeam_isHilbertSchmidt

/-- `‖[P, M_a]‖²_HS = ∑_{n ≥ 1} n (|â(n)|² + |â(-n)|²)`. -/
theorem hsNormSq_commutator :
    hsNormSq (ccmCircleHardyProjection * ccmCircleMultiplier a.toCCMCircleBoundedSymbol -
        ccmCircleMultiplier a.toCCMCircleBoundedSymbol * ccmCircleHardyProjection) =
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff a.toFun ((n + 1 : ℕ) : ℤ)‖ ^ 2) +
        ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff a.toFun (-((n + 1 : ℕ) : ℤ))‖ ^ 2 := by
  let B := ccmCircleBackwardSeam a.toCCMCircleBoundedSymbol
  let F := ccmCircleForwardSeam a.toCCMCircleBoundedSymbol
  have hcomm := a.commutator_isHilbertSchmidt
  rw [ccmCircleHardyCommutator_eq_seams] at hcomm ⊢
  rw [hsNormSq_eq hcomm (fourierBasis (T := (1 : ℝ))), ← a.hsNormSq_backwardSeam,
    ← a.hsNormSq_forwardSeam,
    hsNormSq_eq a.backwardSeam_isHilbertSchmidt (fourierBasis (T := (1 : ℝ))),
    hsNormSq_eq a.forwardSeam_isHilbertSchmidt (fourierBasis (T := (1 : ℝ))),
    ← (a.backwardSeam_isHilbertSchmidt.summable (fourierBasis (T := (1 : ℝ)))).tsum_add
      (a.forwardSeam_isHilbertSchmidt.summable (fourierBasis (T := (1 : ℝ))))]
  refine tsum_congr fun j => ?_
  rw [fourierBasis_eq_fourierLp, sub_apply]
  by_cases hj : 0 ≤ j
  · have hB : B (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) = 0 := by
      change ccmCircleHardyProjection (ccmCircleMultiplier a.toCCMCircleBoundedSymbol
        ((1 - ccmCircleHardyProjection) (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2))) = 0
      simp [ccmCircleHardyProjection_fourierLp, hj]
    change ‖B _ - F _‖ ^ 2 = ‖B _‖ ^ 2 + ‖F _‖ ^ 2
    rw [hB, zero_sub, norm_neg]
    simp
  · have hF : F (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) = 0 := by
      change (1 - ccmCircleHardyProjection) (ccmCircleMultiplier a.toCCMCircleBoundedSymbol
        (ccmCircleHardyProjection (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2))) = 0
      simp [ccmCircleHardyProjection_fourierLp, hj]
    change ‖B _ - F _‖ ^ 2 = ‖B _‖ ^ 2 + ‖F _‖ ^ 2
    rw [hF, sub_zero]
    simp

end CCMCircleHankelSymbol

/-! ## Conjugate symbols and adjoint multipliers -/

/-- The conjugate of a bounded symbol. -/
def CCMCircleBoundedSymbol.conj (a : CCMCircleBoundedSymbol) : CCMCircleBoundedSymbol where
  toFun z := starRingEnd ℂ (a.toFun z)
  bound := a.bound
  bound_nonneg := a.bound_nonneg
  measurable := Complex.continuous_conj.measurable.comp a.measurable
  norm_le z := by rw [Complex.norm_conj]; exact a.norm_le z

theorem CCMCircleBoundedSymbol.fourierCoeff_conj (a : CCMCircleBoundedSymbol) (n : ℤ) :
    fourierCoeff a.conj.toFun n = starRingEnd ℂ (fourierCoeff a.toFun (-n)) := by
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change (fourier (-n)) z • starRingEnd ℂ (a.toFun z) =
    starRingEnd ℂ ((fourier (-(-n))) z • a.toFun z)
  rw [neg_neg, smul_eq_mul, smul_eq_mul, map_mul, fourier_neg]

theorem adjoint_ccmCircleMultiplier (a : CCMCircleBoundedSymbol) :
    adjoint (ccmCircleMultiplier a) = ccmCircleMultiplier a.conj := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lpBoundedMulCLM_coeFn a.conj.measurable a.conj.bound_nonneg a.conj.norm_le x,
    lpBoundedMulCLM_coeFn a.measurable a.bound_nonneg a.norm_le y] with z h1 h2
  change inner ℂ ((ccmCircleMultiplier a.conj x : CCMCircleL2) z) _ =
    inner ℂ _ ((ccmCircleMultiplier a y : CCMCircleL2) z)
  rw [ccmCircleMultiplier, ccmCircleMultiplier, h1, h2, RCLike.inner_apply', RCLike.inner_apply']
  change starRingEnd ℂ (starRingEnd ℂ (a.toFun z) * _) * _ = _
  rw [map_mul, Complex.conj_conj]
  ring

/-- The conjugate of a finite-energy symbol has the two energies exchanged. -/
def CCMCircleHankelSymbol.conj (a : CCMCircleHankelSymbol) : CCMCircleHankelSymbol where
  toCCMCircleBoundedSymbol := a.toCCMCircleBoundedSymbol.conj
  positiveEnergy := by
    simpa only [CCMCircleBoundedSymbol.fourierCoeff_conj, Complex.norm_conj] using a.negativeEnergy
  negativeEnergy := by
    simpa only [CCMCircleBoundedSymbol.fourierCoeff_conj, neg_neg, Complex.norm_conj] using
      a.positiveEnergy

/-! ## Unimodular phases of finite half-Sobolev energy -/

/-- A measurable unimodular circle phase with finite half-Sobolev energy. -/
structure HankelCirclePhase where
  toFun : AddCircle (1 : ℝ) → ℂ
  measurable : Measurable toFun
  norm_eq_one : ∀ z, ‖toFun z‖ = 1
  positiveEnergy : Summable fun n : ℕ =>
    ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff toFun ((n + 1 : ℕ) : ℤ)‖ ^ 2
  negativeEnergy : Summable fun n : ℕ =>
    ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff toFun (-((n + 1 : ℕ) : ℤ))‖ ^ 2

namespace HankelCirclePhase

variable (u : HankelCirclePhase)

/-- The phase as a finite-energy bounded symbol. -/
def toHankelSymbol : CCMCircleHankelSymbol where
  toFun := u.toFun
  bound := 1
  bound_nonneg := zero_le_one
  measurable := u.measurable
  norm_le z := (u.norm_eq_one z).le
  positiveEnergy := u.positiveEnergy
  negativeEnergy := u.negativeEnergy

/-- Multiplication by the phase. -/
def multiplier : CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  ccmCircleMultiplier u.toHankelSymbol.toCCMCircleBoundedSymbol

theorem multiplier_coeFn (f : CCMCircleL2) :
    ((u.multiplier f : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun z => u.toFun z * (f : AddCircle (1 : ℝ) → ℂ) z :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem adjoint_multiplier :
    adjoint u.multiplier = ccmCircleMultiplier u.toHankelSymbol.conj.toCCMCircleBoundedSymbol :=
  adjoint_ccmCircleMultiplier _

theorem conj_mul_self (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (u.toFun z) * u.toFun z = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, u.norm_eq_one]
  norm_num

theorem adjoint_multiplier_mul_multiplier : adjoint u.multiplier * u.multiplier = 1 := by
  rw [u.adjoint_multiplier]
  ext1 f
  apply Lp.ext
  change ((ccmCircleMultiplier u.toHankelSymbol.conj.toCCMCircleBoundedSymbol
    (u.multiplier f) : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[_] _
  filter_upwards [lpBoundedMulCLM_coeFn u.toHankelSymbol.conj.measurable
      u.toHankelSymbol.conj.bound_nonneg u.toHankelSymbol.conj.norm_le (u.multiplier f),
    u.multiplier_coeFn f] with z h1 h2
  change (ccmCircleMultiplier u.toHankelSymbol.conj.toCCMCircleBoundedSymbol
    (u.multiplier f) : CCMCircleL2) z = f z
  rw [ccmCircleMultiplier, h1, h2]
  change starRingEnd ℂ (u.toFun z) * (u.toFun z * _) = _
  rw [← mul_assoc, u.conj_mul_self, one_mul]

theorem multiplier_mul_adjoint_multiplier : u.multiplier * adjoint u.multiplier = 1 := by
  rw [u.adjoint_multiplier]
  ext1 f
  apply Lp.ext
  change ((u.multiplier (ccmCircleMultiplier u.toHankelSymbol.conj.toCCMCircleBoundedSymbol f) :
    CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[_] _
  filter_upwards [u.multiplier_coeFn
      (ccmCircleMultiplier u.toHankelSymbol.conj.toCCMCircleBoundedSymbol f),
    lpBoundedMulCLM_coeFn u.toHankelSymbol.conj.measurable
      u.toHankelSymbol.conj.bound_nonneg u.toHankelSymbol.conj.norm_le f] with z h1 h2
  change (u.multiplier (ccmCircleMultiplier u.toHankelSymbol.conj.toCCMCircleBoundedSymbol f) :
    CCMCircleL2) z = f z
  rw [h1]
  rw [ccmCircleMultiplier, h2]
  change u.toFun z * (starRingEnd ℂ (u.toFun z) * _) = _
  rw [← mul_assoc, mul_comm (u.toFun z), u.conj_mul_self, one_mul]

/-- The restricted-unitary datum of a finite-energy phase. -/
def datum : RestrictedUnitaryDatum CCMCircleL2 where
  projection := ccmCircleHardyProjection
  unitary := u.multiplier
  projection_idempotent := ccmCircleHardyProjection_idempotent
  projection_adjoint := ccmCircleHardyProjection_adjoint
  adjoint_mul_unitary := u.adjoint_multiplier_mul_multiplier
  unitary_mul_adjoint := u.multiplier_mul_adjoint_multiplier
  commutator_isHilbertSchmidt := u.toHankelSymbol.commutator_isHilbertSchmidt

theorem forwardHankelSeam_eq :
    u.datum.forwardHankelSeam = ccmCircleForwardSeam u.toHankelSymbol.toCCMCircleBoundedSymbol :=
  rfl

theorem adjointHankelSeam_eq :
    u.datum.adjointHankelSeam =
      ccmCircleForwardSeam u.toHankelSymbol.conj.toCCMCircleBoundedSymbol := by
  change (1 - ccmCircleHardyProjection) * adjoint u.multiplier * ccmCircleHardyProjection = _
  rw [u.adjoint_multiplier]
  rfl

/-- The signed first Fourier moment `∑_{n ≥ 1} n |û(n)|² - ∑_{n ≥ 1} n |û(-n)|²`. -/
def windingMoment : ℝ :=
  (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff u.toFun ((n + 1 : ℕ) : ℤ)‖ ^ 2) -
    ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff u.toFun (-((n + 1 : ℕ) : ℤ))‖ ^ 2

/-- Two-seam form: `Re Tr (M_u† P M_u - P)³ = ‖Q M_ū P‖²_HS - ‖Q M_u P‖²_HS = ∑ n |û(n)|² - ∑ n |û(-n)|²`. -/
theorem re_opTrace_cubicDefect :
    (opTrace (restrictedProjectionCubicDefect u.datum.conjugateProjection
      u.datum.projection)).re = u.windingMoment := by
  rw [u.datum.re_opTrace_cubicDefect_eq_hankelSeams, u.adjointHankelSeam_eq,
    u.forwardHankelSeam_eq, u.toHankelSymbol.conj.hsNormSq_forwardSeam,
    u.toHankelSymbol.hsNormSq_forwardSeam, windingMoment]
  congr 1
  refine tsum_congr fun n => ?_
  change _ * ‖fourierCoeff u.toHankelSymbol.toCCMCircleBoundedSymbol.conj.toFun _‖ ^ 2 = _
  rw [CCMCircleBoundedSymbol.fourierCoeff_conj, neg_neg, Complex.norm_conj]
  rfl

/-- **Relative index of a finite-energy phase.**  The relative index of `(M_u† P M_u, P)` is
the signed first Fourier moment. -/
theorem relativeIndex_eq_windingMoment :
    (restrictedProjectionRelativeIndex u.datum.conjugateProjection u.datum.projection : ℝ) =
      u.windingMoment := by
  rw [← u.re_opTrace_cubicDefect, u.datum.opTrace_cubicDefect_eq_relativeIndex]
  simp

/-- The cubic trace equals the signed first Fourier moment. -/
theorem opTrace_cubicDefect :
    opTrace (restrictedProjectionCubicDefect u.datum.conjugateProjection u.datum.projection) =
      (u.windingMoment : ℂ) := by
  rw [u.datum.opTrace_cubicDefect_eq_relativeIndex, ← u.relativeIndex_eq_windingMoment]
  simp

/-- The signed first Fourier moment of a finite-energy unimodular phase is an integer. -/
theorem windingMoment_eq_intCast : ∃ m : ℤ, u.windingMoment = m :=
  ⟨_, u.relativeIndex_eq_windingMoment.symm⟩

end HankelCirclePhase

end RHTower
