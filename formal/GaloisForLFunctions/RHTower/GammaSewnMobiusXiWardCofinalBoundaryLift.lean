import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyNonexpansive
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Cofinal four-unit Julia boundary lift for the Xi Ward column

This module studies the exact augmented boundary Gram demanded by the CCM endpoint:

`W_P = [[G_P, r_P], [r_Pᴴ, 4]]`.

The key new mechanism is zero-adapted sampling.  If `q` is one strict-right Xi Schwarz pair and
`lambda` is its centered zero, evaluate the full continued Ward response at `conj lambda`.
Every Schwarz-pair summand then has positive real part.  The selected pair alone contributes
strictly more than `1 / re lambda`; hence no contribution from the rest of the infinite divisor
can cancel it.  Since `0 < re lambda < 1/2`, the one-node four-unit Schur defect is strictly
negative.

Consequently the actual augmented Gram is positive semidefinite on every finite right-half-plane
packet if and only if RH holds.  This is an exact endpoint classification of the requested
singular/cofinal lift, not a diagonal multiplier estimate.
-/

open Complex Filter Topology Set
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

theorem re_inv_pos_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    0 < z⁻¹.re := by
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr (by
    intro h
    subst z
    simp at hz))

/-- Every raw strict-right Xi Schwarz-pair Ward response has positive real
part on the right half-plane. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_pos
    (q : XiRightUpperZeroCopy) {w : ℂ} (hw : 0 < w.re) :
    0 < (xiAntiCausalWardSchwarzPairResponse q w).re := by
  rw [xiAntiCausalWardSchwarzPairResponse]
  have h₁ : 0 < (w + xiRightCenteredZero q.1).re := by
    simp only [Complex.add_re]
    exact add_pos hw (xiRightCenteredZero_re_pos q.1)
  have h₂ : 0 <
      (w + xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1)).re := by
    simp only [Complex.add_re]
    exact add_pos hw
      (xiRightCenteredZero_re_pos (xiRightZeroCopyConjEquiv q.1))
  have hi₁ : 0 < ((w + xiRightCenteredZero q.1)⁻¹).re :=
    re_inv_pos_of_re_pos h₁
  have hi₂ : 0 <
      ((w + xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1))⁻¹).re :=
    re_inv_pos_of_re_pos h₂
  rw [Complex.inv_re] at hi₁ hi₂
  simp only [Complex.add_re] at hi₁ hi₂
  norm_num [Complex.mul_re, Complex.add_re]
  nlinarith

/-- At the node adapted to one strict-right zero, that pair contributes more
than the reciprocal transverse displacement. -/
theorem re_selected_xiAntiCausalWardSchwarzPairResponse_gt_inv
    (q : XiRightUpperZeroCopy) :
    ((xiRightCenteredZero q.1).re)⁻¹ <
      (xiAntiCausalWardSchwarzPairResponse q
        ((starRingEnd ℂ) (xiRightCenteredZero q.1))).re := by
  let lam := xiRightCenteredZero q.1
  change lam.re⁻¹ <
    (xiAntiCausalWardSchwarzPairResponse q ((starRingEnd ℂ) lam)).re
  have ha : 0 < lam.re := xiRightCenteredZero_re_pos q.1
  have hconj :
      xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1) =
        (starRingEnd ℂ) lam := by
    exact xiRightCenteredZero_conj q.1
  rw [xiAntiCausalWardSchwarzPairResponse, hconj]
  have hsum : (starRingEnd ℂ) lam + lam = (2 * lam.re : ℂ) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [hsum]
  have hfirst : (2 * ((2 * lam.re : ℂ)⁻¹)).re = (lam.re)⁻¹ := by
    norm_num
    field_simp [ha.ne']
  have hother : 0 <
      (((starRingEnd ℂ) lam + (starRingEnd ℂ) lam)⁻¹).re := by
    apply re_inv_pos_of_re_pos
    simp only [Complex.add_re, Complex.conj_re]
    linarith
  rw [Complex.inv_re] at hother
  simp only [Complex.add_re, Complex.conj_re] at hother
  rw [show
    (2 : ℂ) * ((2 * lam.re : ℂ)⁻¹ +
        ((starRingEnd ℂ) lam + (starRingEnd ℂ) lam)⁻¹) =
      2 * (2 * lam.re : ℂ)⁻¹ +
        2 * ((starRingEnd ℂ) lam + (starRingEnd ℂ) lam)⁻¹ by ring]
  rw [Complex.add_re, hfirst]
  norm_num [Complex.mul_re]
  nlinarith

/-- The full infinite Ward response inherits the selected-pair lower bound:
all remaining absolutely summable Schwarz-pair contributions have positive
real part. -/
theorem re_continuedXiAntiCausalWardResponse_at_adaptedNode_gt_inv
    (q : XiRightUpperZeroCopy) :
    ((xiRightCenteredZero q.1).re)⁻¹ <
      (continuedXiAntiCausalWardResponse
        ((starRingEnd ℂ) (xiRightCenteredZero q.1))).re := by
  let w := (starRingEnd ℂ) (xiRightCenteredZero q.1)
  have hw : 0 < w.re := by
    simp only [w, Complex.conj_re]
    exact xiRightCenteredZero_re_pos q.1
  have hsum :=
    summable_xiAntiCausalWardSchwarzPairResponse hw
  have hreal : Summable (fun p : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse p w).re) := by
    simpa only [Complex.reCLM_apply] using hsum.mapL Complex.reCLM
  have hselected :
      (xiAntiCausalWardSchwarzPairResponse q w).re ≤
        ∑' p : XiRightUpperZeroCopy,
          (xiAntiCausalWardSchwarzPairResponse p w).re := by
    have hle := hreal.sum_le_tsum ({q} : Finset XiRightUpperZeroCopy)
      (fun p _ => (re_xiAntiCausalWardSchwarzPairResponse_pos p hw).le)
    simpa only [Finset.sum_singleton] using hle
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
    Complex.re_tsum hsum]
  exact lt_of_lt_of_le
    (by simpa only [w] using
      re_selected_xiAntiCausalWardSchwarzPairResponse_gt_inv q)
    hselected

/-- Atomic boundary-charge law.  A strict-right centered zero with transverse
coordinate `a` forces the squared Ward response at its adapted node to exceed
`2/a`, the exact one-node four-unit Cauchy budget. -/
theorem normSq_continuedXiAntiCausalWardResponse_at_adaptedNode_gt
    (q : XiRightUpperZeroCopy) :
    2 * ((xiRightCenteredZero q.1).re)⁻¹ <
      Complex.normSq (continuedXiAntiCausalWardResponse
        ((starRingEnd ℂ) (xiRightCenteredZero q.1))) := by
  let a := (xiRightCenteredZero q.1).re
  let r := continuedXiAntiCausalWardResponse
    ((starRingEnd ℂ) (xiRightCenteredZero q.1))
  have ha : 0 < a := xiRightCenteredZero_re_pos q.1
  have hahalf : a < 1 / 2 := by
    exact (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have har : a⁻¹ < r.re := by
    simpa only [a, r] using
      re_continuedXiAntiCausalWardResponse_at_adaptedNode_gt_inv q
  have hainv : a * a⁻¹ = 1 := by
    exact mul_inv_cancel₀ ha.ne'
  have hinv_gt_two : 2 < a⁻¹ := by
    nlinarith
  have hre_sq : r.re * r.re ≤ Complex.normSq r :=
    Complex.re_sq_le_normSq r
  nlinarith

/-- Four-unit Schur complement demanded by a Julia boundary lift with
boundary column `r_P` and scalar boundary diagonal `4`. -/
def continuedXiWardFourUnitSchurDefect {n : ℕ}
    (node : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    4 * rightHalfPlaneHardyCauchyGram node i j -
      continuedXiAntiCausalWardResponse (node i) *
        star (continuedXiAntiCausalWardResponse (node j))

/-- One strict-right Xi pair makes the adapted one-node Schur diagonal
strictly negative. -/
theorem continuedXiWardFourUnitSchurDefect_adaptedNode_diag_re_neg
    (q : XiRightUpperZeroCopy) :
    (continuedXiWardFourUnitSchurDefect
      (fun _ : Fin 1 =>
        (starRingEnd ℂ) (xiRightCenteredZero q.1)) 0 0).re < 0 := by
  let a := (xiRightCenteredZero q.1).re
  let r := continuedXiAntiCausalWardResponse
    ((starRingEnd ℂ) (xiRightCenteredZero q.1))
  have ha : 0 < a := xiRightCenteredZero_re_pos q.1
  have hnorm : 2 * a⁻¹ < Complex.normSq r := by
    simpa only [a, r] using
      normSq_continuedXiAntiCausalWardResponse_at_adaptedNode_gt q
  change
    (4 * (1 /
      ((starRingEnd ℂ) (xiRightCenteredZero q.1) +
        star ((starRingEnd ℂ) (xiRightCenteredZero q.1)))) -
      r * star r).re < 0
  have hden :
      (starRingEnd ℂ) (xiRightCenteredZero q.1) +
          star ((starRingEnd ℂ) (xiRightCenteredZero q.1)) =
        (2 * a : ℂ) := by
    apply Complex.ext
    · simp [a]
      ring
    · simp [a]
  rw [hden]
  rw [show r * star r = (Complex.normSq r : ℂ) by
    exact Complex.mul_conj r]
  norm_num [Complex.mul_re, Complex.inv_re]
  have hainv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  field_simp [ha.ne']
  nlinarith

theorem continuedXiWardFourUnitSchurDefect_adaptedNode_not_posSemidef
    (q : XiRightUpperZeroCopy) :
    ¬ (continuedXiWardFourUnitSchurDefect
      (fun _ : Fin 1 =>
        (starRingEnd ℂ) (xiRightCenteredZero q.1))).PosSemidef := by
  intro h
  have hd := h.diag_nonneg (i := 0)
  rw [Complex.le_def, Complex.zero_re, Complex.zero_im] at hd
  linarith [hd.1,
    continuedXiWardFourUnitSchurDefect_adaptedNode_diag_re_neg q]

theorem continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.re) :
    continuedXiAntiCausalWardResponse w = 0 := by
  letI : IsEmpty XiRightZeroCopy := by
    constructor
    intro q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q.1
    have hpos := q.2
    rw [ht] at hpos
    simp at hpos
  letI : IsEmpty XiRightUpperZeroCopy :=
    ⟨fun q => isEmptyElim q.1⟩
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw]
  simp

/-- Cofinal four-unit Schur law: every finite right-half-plane packet admits
the Schur complement required by a Julia boundary lift with column `r_P`
and boundary diagonal `4`. -/
def ContinuedXiWardFourUnitBoundaryLiftLaw : Prop :=
  ∀ {n : ℕ} (node : Fin n → ℂ), (∀ i, 0 < (node i).re) →
    (continuedXiWardFourUnitSchurDefect node).PosSemidef

theorem continuedXiWardFourUnitBoundaryLiftLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ContinuedXiWardFourUnitBoundaryLiftLaw := by
  intro n node hnode
  have hr (i : Fin n) :
      continuedXiAntiCausalWardResponse (node i) = 0 :=
    continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis
      hRH (hnode i)
  have hdef :
      continuedXiWardFourUnitSchurDefect node =
        (4 : ℂ) • rightHalfPlaneHardyCauchyGram node := by
    ext i j
    simp [continuedXiWardFourUnitSchurDefect, hr]
  rw [hdef]
  exact (rightHalfPlaneHardyCauchyGram_posSemidef hnode).smul
    (by norm_num)

theorem nonempty_xiRightUpperZeroCopy_for_boundaryLift
    (hRH : ¬ RiemannHypothesis) :
    Nonempty XiRightUpperZeroCopy := by
  obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  obtain q' | q' := xiRightSchwarzPairEquiv.symm q
  · exact ⟨q'⟩
  · exact ⟨q'⟩

theorem riemannHypothesis_of_continuedXiWardFourUnitBoundaryLiftLaw
    (hlift : ContinuedXiWardFourUnitBoundaryLiftLaw) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  have hnode :
      ∀ i : Fin 1, 0 <
        ((fun _ : Fin 1 =>
          (starRingEnd ℂ) (xiRightCenteredZero q.1)) i).re := by
    intro i
    simp only [Complex.conj_re]
    exact xiRightCenteredZero_re_pos q.1
  exact continuedXiWardFourUnitSchurDefect_adaptedNode_not_posSemidef q
    (hlift
      (fun _ : Fin 1 =>
        (starRingEnd ℂ) (xiRightCenteredZero q.1)) hnode)

/-- Exact endpoint classification of the four-unit Schur law. -/
theorem riemannHypothesis_iff_continuedXiWardFourUnitBoundaryLiftLaw :
    RiemannHypothesis ↔ ContinuedXiWardFourUnitBoundaryLiftLaw :=
  ⟨continuedXiWardFourUnitBoundaryLiftLaw_of_riemannHypothesis,
    riemannHypothesis_of_continuedXiWardFourUnitBoundaryLiftLaw⟩

/-- The requested Ward column as a one-column matrix. -/
def continuedXiWardBoundaryColumnMatrix {n : ℕ}
    (node : Fin n → ℂ) : Matrix (Fin n) Unit ℂ :=
  fun i _ => continuedXiAntiCausalWardResponse (node i)

/-- Actual augmented Julia boundary Gram:
`W_P = [[G, r_P], [r_Pᴴ, 4]]`. -/
def continuedXiWardFourUnitBoundaryGram {n : ℕ}
    (node : Fin n → ℂ) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.fromBlocks
    (rightHalfPlaneHardyCauchyGram node)
    (continuedXiWardBoundaryColumnMatrix node)
    (continuedXiWardBoundaryColumnMatrix node).conjTranspose
    (Matrix.of fun _ _ : Unit => (4 : ℂ))

/-- The actual augmented block is PSD exactly when its four-unit Schur
complement is PSD. -/
theorem continuedXiWardFourUnitBoundaryGram_posSemidef_iff_schur
    {n : ℕ} (node : Fin n → ℂ) :
    (continuedXiWardFourUnitBoundaryGram node).PosSemidef ↔
      (continuedXiWardFourUnitSchurDefect node).PosSemidef := by
  let G := rightHalfPlaneHardyCauchyGram node
  let B := continuedXiWardBoundaryColumnMatrix node
  let D := Matrix.of fun _ _ : Unit => (4 : ℂ)
  let E := Matrix.of fun _ _ : Unit => (1 / 4 : ℂ)
  have hDE : D * E = 1 := by
    ext i j
    simp [D, E, Matrix.mul_apply]
  letI : Invertible D :=
    invertibleOfRightInverse D E hDE
  have hDinv : D⁻¹ = E := by
    rw [← Matrix.invOf_eq_nonsing_inv]
    exact invOf_eq_right_inv hDE
  have hD : D.PosDef := by
    have hD_eq :
        D = Matrix.diagonal (fun _ : Unit => (4 : ℂ)) := by
      ext i j
      simp [D, Subsingleton.elim i j]
    rw [hD_eq]
    exact Matrix.PosDef.diagonal (fun _ => by norm_num)
  have hscaled :
      continuedXiWardFourUnitSchurDefect node =
        (4 : ℂ) • (G - B * D⁻¹ * B.conjTranspose) := by
    ext i j
    rw [hDinv]
    simp [continuedXiWardFourUnitSchurDefect, G, B, E,
      continuedXiWardBoundaryColumnMatrix, Matrix.mul_apply]
    ring
  change (Matrix.fromBlocks G B B.conjTranspose D).PosSemidef ↔
    (continuedXiWardFourUnitSchurDefect node).PosSemidef
  rw [Matrix.PosDef.fromBlocks₂₂ G B hD]
  constructor
  · intro hschur
    rw [hscaled]
    exact hschur.smul (by norm_num)
  · intro hdef
    have hscaledBack :=
      hdef.smul (show (0 : ℂ) ≤ (1 / 4 : ℂ) by
        rw [Complex.nonneg_iff]
        norm_num)
    have hback :
        (1 / 4 : ℂ) • continuedXiWardFourUnitSchurDefect node =
          G - B * D⁻¹ * B.conjTranspose := by
      rw [hscaled]
      simp [smul_smul]
    rwa [hback] at hscaledBack

/-- Cofinal singular Julia boundary-lift law stated on the actual augmented
Gram with Ward column and boundary diagonal four. -/
def ContinuedXiWardFourUnitBoundaryGramLaw : Prop :=
  ∀ {n : ℕ} (node : Fin n → ℂ), (∀ i, 0 < (node i).re) →
    (continuedXiWardFourUnitBoundaryGram node).PosSemidef

theorem continuedXiWardFourUnitBoundaryGramLaw_iff_schurLaw :
    ContinuedXiWardFourUnitBoundaryGramLaw ↔
      ContinuedXiWardFourUnitBoundaryLiftLaw := by
  constructor
  · intro h n node hnode
    exact
      (continuedXiWardFourUnitBoundaryGram_posSemidef_iff_schur node).mp
        (h node hnode)
  · intro h n node hnode
    exact
      (continuedXiWardFourUnitBoundaryGram_posSemidef_iff_schur node).mpr
        (h node hnode)

theorem continuedXiWardFourUnitBoundaryGram_adaptedNode_not_posSemidef
    (q : XiRightUpperZeroCopy) :
    ¬ (continuedXiWardFourUnitBoundaryGram
      (fun _ : Fin 1 =>
        (starRingEnd ℂ) (xiRightCenteredZero q.1))).PosSemidef := by
  rw [continuedXiWardFourUnitBoundaryGram_posSemidef_iff_schur]
  exact continuedXiWardFourUnitSchurDefect_adaptedNode_not_posSemidef q

/-- Exact endpoint theorem for the requested object.  The singular/cofinal
augmented Julia Gram with column `r_P` and boundary diagonal `4` exists on
all finite packets exactly when RH holds. -/
theorem riemannHypothesis_iff_continuedXiWardFourUnitBoundaryGramLaw :
    RiemannHypothesis ↔ ContinuedXiWardFourUnitBoundaryGramLaw := by
  rw [continuedXiWardFourUnitBoundaryGramLaw_iff_schurLaw]
  exact riemannHypothesis_iff_continuedXiWardFourUnitBoundaryLiftLaw

end

end RHTower
