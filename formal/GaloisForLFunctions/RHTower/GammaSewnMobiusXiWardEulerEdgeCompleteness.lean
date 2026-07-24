import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardCofinalBoundaryLift
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardySaturation

/-!
# Euler-edge scalar completeness of the Xi Ward column

The full four-unit boundary Gram is RH-complete on one fixed vertical line.  If
`lambda = a + i b` is a strict-right centered Xi zero, sample the continued Ward response at
`w = 1/2 - i b`.  The selected Schwarz-pair term has real part strictly larger than two, while
every remaining pair has positive real part.  Since the Hardy Cauchy diagonal at this node is
one, the scalar four-unit budget fails.

Thus RH is equivalent to the pointwise scalar bound `|r(1/2 + i t)|² <= 4` for every real `t`.
No finite packet, limiting process, or zero-location hypothesis occurs in the statement.
-/

open Complex Filter Topology Set
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Fixed Euler-edge node matched to the height of one strict-right Schwarz pair. -/
def xiWardEulerEdgeAdaptedNode (q : XiRightUpperZeroCopy) : ℂ :=
  (1 / 2 : ℂ) -
    I * ((xiRightCenteredZero q.1).im : ℂ)

@[simp] theorem xiWardEulerEdgeAdaptedNode_re
    (q : XiRightUpperZeroCopy) :
    (xiWardEulerEdgeAdaptedNode q).re = 1 / 2 := by
  simp [xiWardEulerEdgeAdaptedNode]

@[simp] theorem xiWardEulerEdgeAdaptedNode_im
    (q : XiRightUpperZeroCopy) :
    (xiWardEulerEdgeAdaptedNode q).im =
      -(xiRightCenteredZero q.1).im := by
  simp [xiWardEulerEdgeAdaptedNode]

/-- At the fixed Euler edge, the selected strict-right pair alone contributes real part
strictly larger than two. -/
theorem re_selected_xiAntiCausalWardSchwarzPairResponse_at_eulerEdge_gt_two
    (q : XiRightUpperZeroCopy) :
    2 <
      (xiAntiCausalWardSchwarzPairResponse q
        (xiWardEulerEdgeAdaptedNode q)).re := by
  let lam := xiRightCenteredZero q.1
  let w := xiWardEulerEdgeAdaptedNode q
  have ha : 0 < lam.re := xiRightCenteredZero_re_pos q.1
  have hahalf : lam.re < 1 / 2 := by
    exact (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hconj :
      xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1) =
        (starRingEnd ℂ) lam :=
    xiRightCenteredZero_conj q.1
  have hwlam : w + lam = (lam.re + 1 / 2 : ℂ) := by
    apply Complex.ext
    · simp [w, xiWardEulerEdgeAdaptedNode, lam]
      ring
    · simp [w, xiWardEulerEdgeAdaptedNode, lam]
  have hother : 0 < (w + (starRingEnd ℂ) lam).re := by
    simp [w, xiWardEulerEdgeAdaptedNode, lam]
    linarith
  have hiother : 0 < ((w + (starRingEnd ℂ) lam)⁻¹).re :=
    re_inv_pos_of_re_pos hother
  have hdenpos : 0 < lam.re + 1 / 2 := by linarith
  have hrealCast :
      (lam.re + 1 / 2 : ℂ) = ((lam.re + 1 / 2 : ℝ) : ℂ) := by
    norm_num
  have hfirstEq :
      (2 * ((lam.re + 1 / 2 : ℂ)⁻¹)).re =
        2 / (lam.re + 1 / 2) := by
    rw [hrealCast, Complex.mul_re, Complex.inv_re,
      Complex.normSq_ofReal]
    norm_num
    field_simp [hdenpos.ne']
  have hdenlt : lam.re + 1 / 2 < 1 := by linarith
  have hfirst : 2 < (2 * ((lam.re + 1 / 2 : ℂ)⁻¹)).re := by
    rw [hfirstEq]
    exact (lt_div_iff₀ hdenpos).2 (by nlinarith)
  have hsecond :
      0 < (2 * (w + (starRingEnd ℂ) lam)⁻¹).re := by
    calc
      0 < 2 * ((w + (starRingEnd ℂ) lam)⁻¹).re :=
        mul_pos (by norm_num) hiother
      _ = (2 * (w + (starRingEnd ℂ) lam)⁻¹).re := by
        norm_num [Complex.mul_re]
  rw [xiAntiCausalWardSchwarzPairResponse, hconj, hwlam]
  rw [show
    (2 : ℂ) *
        (((lam.re + 1 / 2 : ℂ)⁻¹) +
          (w + (starRingEnd ℂ) lam)⁻¹) =
      2 * ((lam.re + 1 / 2 : ℂ)⁻¹) +
        2 * (w + (starRingEnd ℂ) lam)⁻¹ by ring]
  rw [Complex.add_re]
  nlinarith

/-- Any one summand of the positive Schwarz-pair expansion is bounded above by the real part of
the complete continued Ward response. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_le_continued
    (q : XiRightUpperZeroCopy) {w : ℂ} (hw : 0 < w.re) :
    (xiAntiCausalWardSchwarzPairResponse q w).re ≤
      (continuedXiAntiCausalWardResponse w).re := by
  have hsum :=
    summable_xiAntiCausalWardSchwarzPairResponse hw
  have hreal : Summable (fun p : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse p w).re) := by
    simpa only [Complex.reCLM_apply] using hsum.mapL Complex.reCLM
  have hselected :=
    hreal.sum_le_tsum ({q} : Finset XiRightUpperZeroCopy)
      (fun p _ => (re_xiAntiCausalWardSchwarzPairResponse_pos p hw).le)
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
    Complex.re_tsum hsum]
  simpa only [Finset.sum_singleton] using hselected

/-- A strict-right Xi pair forces the continued Ward response above the scalar four-unit budget
at its height on the fixed Euler edge. -/
theorem normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_four
    (q : XiRightUpperZeroCopy) :
    4 <
      Complex.normSq
        (continuedXiAntiCausalWardResponse
          (xiWardEulerEdgeAdaptedNode q)) := by
  have hw : 0 < (xiWardEulerEdgeAdaptedNode q).re := by
    rw [xiWardEulerEdgeAdaptedNode_re]
    norm_num
  have hselected :=
    re_selected_xiAntiCausalWardSchwarzPairResponse_at_eulerEdge_gt_two q
  have hfull :=
    re_xiAntiCausalWardSchwarzPairResponse_le_continued q hw
  have hre :
      2 <
        (continuedXiAntiCausalWardResponse
          (xiWardEulerEdgeAdaptedNode q)).re :=
    lt_of_lt_of_le hselected hfull
  have hsq := Complex.re_sq_le_normSq
    (continuedXiAntiCausalWardResponse
      (xiWardEulerEdgeAdaptedNode q))
  nlinarith

/-- One-node four-unit Schur defect is strictly negative at the Euler-edge witness. -/
theorem continuedXiWardFourUnitSchurDefect_eulerEdge_diag_re_neg
    (q : XiRightUpperZeroCopy) :
    (continuedXiWardFourUnitSchurDefect
      (fun _ : Fin 1 => xiWardEulerEdgeAdaptedNode q) 0 0).re < 0 := by
  let r :=
    continuedXiAntiCausalWardResponse
      (xiWardEulerEdgeAdaptedNode q)
  have hnorm : 4 < Complex.normSq r := by
    simpa only [r] using
      normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_four q
  change
    (4 * (1 /
      (xiWardEulerEdgeAdaptedNode q +
        star (xiWardEulerEdgeAdaptedNode q))) -
      r * star r).re < 0
  have hden :
      xiWardEulerEdgeAdaptedNode q +
          star (xiWardEulerEdgeAdaptedNode q) = (1 : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, RCLike.star_def, Complex.conj_re,
        xiWardEulerEdgeAdaptedNode_re, one_re]
      norm_num
    · simp [xiWardEulerEdgeAdaptedNode]
  rw [hden, div_one]
  rw [show r * star r = (Complex.normSq r : ℂ) by
    exact Complex.mul_conj r]
  norm_num
  linarith

/-- Scalar four-unit Ward law on the single vertical Euler edge `Re w = 1/2`. -/
def ContinuedXiWardEulerEdgeScalarLaw : Prop :=
  ∀ t : ℝ,
    Complex.normSq
        (continuedXiAntiCausalWardResponse
          ((1 / 2 : ℂ) + I * (t : ℂ))) ≤ 4

theorem continuedXiWardEulerEdgeScalarLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ContinuedXiWardEulerEdgeScalarLaw := by
  intro t
  have hw :
      0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis hRH hw]
  norm_num

theorem riemannHypothesis_of_continuedXiWardEulerEdgeScalarLaw
    (hscalar : ContinuedXiWardEulerEdgeScalarLaw) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  have hnode :
      (1 / 2 : ℂ) +
          I * ((-(xiRightCenteredZero q.1).im : ℝ) : ℂ) =
        xiWardEulerEdgeAdaptedNode q := by
    simp only [xiWardEulerEdgeAdaptedNode, ofReal_neg]
    ring
  have hle :=
    hscalar (-(xiRightCenteredZero q.1).im)
  rw [hnode] at hle
  linarith [
    normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_four q]

/-- **Euler-edge scalar completeness law.**  RH is equivalent to a scalar norm bound on one
fixed vertical line. -/
theorem riemannHypothesis_iff_continuedXiWardEulerEdgeScalarLaw :
    RiemannHypothesis ↔ ContinuedXiWardEulerEdgeScalarLaw :=
  ⟨continuedXiWardEulerEdgeScalarLaw_of_riemannHypothesis,
    riemannHypothesis_of_continuedXiWardEulerEdgeScalarLaw⟩

/-- Fixed-line form of the requested augmented Gram law.  Every node of every packet lies on
`Re w = 1/2`; no interior right-half-plane sampling is requested. -/
def ContinuedXiWardEulerEdgeBoundaryGramLaw : Prop :=
  ∀ {n : ℕ} (height : Fin n → ℝ),
    (continuedXiWardFourUnitBoundaryGram
      (fun i => (1 / 2 : ℂ) + I * (height i : ℂ))).PosSemidef

theorem continuedXiWardFourUnitBoundaryGram_eulerEdge_adapted_not_posSemidef
    (q : XiRightUpperZeroCopy) :
    ¬ (continuedXiWardFourUnitBoundaryGram
      (fun _ : Fin 1 => xiWardEulerEdgeAdaptedNode q)).PosSemidef := by
  rw [continuedXiWardFourUnitBoundaryGram_posSemidef_iff_schur]
  intro h
  have hd := h.diag_nonneg (i := 0)
  rw [Complex.le_def, Complex.zero_re, Complex.zero_im] at hd
  linarith [hd.1,
    continuedXiWardFourUnitSchurDefect_eulerEdge_diag_re_neg q]

theorem continuedXiWardEulerEdgeBoundaryGramLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ContinuedXiWardEulerEdgeBoundaryGramLaw := by
  intro n height
  apply (riemannHypothesis_iff_continuedXiWardFourUnitBoundaryGramLaw.mp hRH)
  intro i
  norm_num [Complex.add_re, Complex.mul_re]

theorem riemannHypothesis_of_continuedXiWardEulerEdgeBoundaryGramLaw
    (hgram : ContinuedXiWardEulerEdgeBoundaryGramLaw) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  have hnode :
      (fun _ : Fin 1 =>
        (1 / 2 : ℂ) +
          I * ((-(xiRightCenteredZero q.1).im : ℝ) : ℂ)) =
      (fun _ : Fin 1 => xiWardEulerEdgeAdaptedNode q) := by
    funext i
    simp only [xiWardEulerEdgeAdaptedNode, ofReal_neg]
    ring
  have hpacket :=
    hgram (fun _ : Fin 1 => -(xiRightCenteredZero q.1).im)
  rw [hnode] at hpacket
  exact
    continuedXiWardFourUnitBoundaryGram_eulerEdge_adapted_not_posSemidef q
      hpacket

/-- **Fixed-line augmented-Gram completeness law.**  Source-side positivity of the requested
`W_P` need only be proved for packets on the Euler edge `Re w = 1/2`; that restricted statement
is already exactly RH. -/
theorem riemannHypothesis_iff_continuedXiWardEulerEdgeBoundaryGramLaw :
    RiemannHypothesis ↔ ContinuedXiWardEulerEdgeBoundaryGramLaw :=
  ⟨continuedXiWardEulerEdgeBoundaryGramLaw_of_riemannHypothesis,
    riemannHypothesis_of_continuedXiWardEulerEdgeBoundaryGramLaw⟩

/-- **Xi Ward Euler-edge/bulk saturation-phase universality law.** For every
positive right-half-plane node and aperture, the fixed Euler-edge scalar phase
is exactly simultaneous edge/full-bulk Gram positivity, exact Hardy
saturation, and zero anti-causal transport. Its complement is exactly failure
of both Gram phases, strict Hardy contraction, and nonzero transport. -/
theorem xiWardEulerEdge_bulkSaturationPhaseUniversality
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 < alpha) :
    (ContinuedXiWardEulerEdgeScalarLaw ↔
      ContinuedXiWardEulerEdgeBoundaryGramLaw ∧
      ContinuedXiWardFourUnitBoundaryGramLaw ∧
      xiRightWardBoundarySourcePhaseCrossRatio
          (I * w) (alpha : ℂ) = 1 ∧
      mobiusGammaXiAntiCausalWardTransportV w (alpha : ℂ) = 0) ∧
    (¬ ContinuedXiWardEulerEdgeScalarLaw ↔
      ¬ ContinuedXiWardEulerEdgeBoundaryGramLaw ∧
      ¬ ContinuedXiWardFourUnitBoundaryGramLaw ∧
      ‖xiRightWardBoundarySourcePhaseCrossRatio
          (I * w) (alpha : ℂ)‖ < 1 ∧
      mobiusGammaXiAntiCausalWardTransportV w (alpha : ℂ) ≠ 0) := by
  constructor
  · constructor
    · intro hscalar
      have hRH :=
        riemannHypothesis_of_continuedXiWardEulerEdgeScalarLaw hscalar
      exact
        ⟨continuedXiWardEulerEdgeBoundaryGramLaw_of_riemannHypothesis hRH,
          (riemannHypothesis_iff_continuedXiWardFourUnitBoundaryGramLaw.mp hRH),
          xiRightWardBoundarySourcePhaseCrossRatio_eq_one_of_riemannHypothesis
            hRH w alpha,
          (riemannHypothesis_iff_mobiusGammaXiAntiCausalWardTransportV_eq_zero
            hw ha).mp hRH⟩
    · rintro ⟨hEdgeGram, _hBulkGram, _hphase, _htransport⟩
      exact continuedXiWardEulerEdgeScalarLaw_of_riemannHypothesis
        (riemannHypothesis_of_continuedXiWardEulerEdgeBoundaryGramLaw
          hEdgeGram)
  · constructor
    · intro hscalar
      have hnRH : ¬ RiemannHypothesis := by
        intro hRH
        exact hscalar
          (continuedXiWardEulerEdgeScalarLaw_of_riemannHypothesis hRH)
      exact
        ⟨fun hEdgeGram => hnRH
            (riemannHypothesis_of_continuedXiWardEulerEdgeBoundaryGramLaw
              hEdgeGram),
          fun hBulkGram => hnRH
            (riemannHypothesis_iff_continuedXiWardFourUnitBoundaryGramLaw.mpr
              hBulkGram),
          (not_riemannHypothesis_iff_norm_xiRightWardBoundarySourcePhaseCrossRatio_lt_one
            hw ha).mp hnRH,
          (not_riemannHypothesis_iff_mobiusGammaXiAntiCausalWardTransportV_ne_zero
            hw ha).mp hnRH⟩
    · rintro ⟨_hEdgeGram, _hBulkGram, hstrict, _htransport⟩
      have hnRH :=
        (not_riemannHypothesis_iff_norm_xiRightWardBoundarySourcePhaseCrossRatio_lt_one
          hw ha).mpr hstrict
      intro hscalar
      exact hnRH
        (riemannHypothesis_of_continuedXiWardEulerEdgeScalarLaw hscalar)

end

end RHTower
