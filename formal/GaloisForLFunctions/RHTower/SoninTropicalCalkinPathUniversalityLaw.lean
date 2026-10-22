import GaloisForLFunctions.RHTower.CCM.CCMSoninPathTropicalMemory

/-!
# Sonin tropical Calkin path universality

Finite composable Sonin Gram paths forget every interior scale except the minimum.  With endpoints
fixed, equality of genuine Gram-word operators modulo compacts is exactly equality of tropical
minima.  This path classifier lives inside the faithful inverse-semigroup realization of canonical
Sonin window states.
-/

namespace RHTower

noncomputable section

/-- Two finite composable Sonin Gram paths with the same endpoints have the same Calkin operator
class exactly when they have the same minimum visited scale. -/
theorem SoninScalePath.operator_compactEq_iff_minimum_eq
    (a : ℝ) (ha : 0 < a) (P Q : SoninScalePath)
    (hstart : P.start = Q.start) (hend : P.endpoint = Q.endpoint) :
    P.operator a =ₖ Q.operator a ↔ P.minimum = Q.minimum := by
  have hP := P.operator_compactEq_window a ha
  have hQ := Q.operator_compactEq_window a ha
  constructor
  · intro hPQ
    have hwindowOp : (P.window a ha).operator =ₖ (Q.window a ha).operator :=
      hP.symm.trans (hPQ.trans hQ)
    have hwindow : P.window a ha = Q.window a ha :=
      ((P.window a ha).operator_compactEq_iff ha (Q.window a ha)).mp hwindowOp
    change soninPathWindow a P.start P.endpoint P.minimum ha
          P.start_gt_one P.endpoint_gt_one P.minimum_gt_one
          P.minimum_le_start P.minimum_le_endpoint =
        soninPathWindow a Q.start Q.endpoint Q.minimum ha
          Q.start_gt_one Q.endpoint_gt_one Q.minimum_gt_one
          Q.minimum_le_start Q.minimum_le_endpoint at hwindow
    have hfloor := congrArg SoninLiveWindow.floor hwindow
    change (P.start * P.minimum⁻¹) * a =
      (Q.start * Q.minimum⁻¹) * a at hfloor
    rw [← hstart] at hfloor
    have hratio : P.start * P.minimum⁻¹ = P.start * Q.minimum⁻¹ :=
      mul_right_cancel₀ ha.ne' hfloor
    have hinv : P.minimum⁻¹ = Q.minimum⁻¹ :=
      mul_left_cancel₀ (ne_of_gt (zero_lt_one.trans P.start_gt_one)) hratio
    exact inv_injective hinv
  · intro hminimum
    have hwindow : P.window a ha = Q.window a ha := by
      unfold SoninScalePath.window
      apply SoninLiveWindow.ext_coordinates
      · simp only [soninPathWindow, hstart]
      · simp only [soninPathWindow, hstart, hminimum]
      · simp only [soninPathWindow, hstart, hend]
    exact hP.trans
      ((CompactOperatorEq.of_eq (congrArg SoninLiveWindow.operator hwindow)).trans hQ.symm)

/-- Complete algebraic/operator certificate: inverse-semigroup states, tropical concatenation,
faithful minimum classification, noncompact path words, and exact endpoint absorption. -/
structure SoninTropicalCalkinPathUniversalCertificate (a : ℝ) : Prop where
  stateUniqueInverse :
    ∀ s : SoninWindowState a, ∃! t : SoninWindowState a,
      composeSoninWindowStates (composeSoninWindowStates s t) s = s ∧
      composeSoninWindowStates (composeSoninWindowStates t s) t = t
  stateIdempotentsCommute :
    ∀ e f : SoninWindowState a,
      composeSoninWindowStates e e = e →
      composeSoninWindowStates f f = f →
      composeSoninWindowStates e f = composeSoninWindowStates f e
  stateOperatorFaithful :
    ∀ s t : SoninWindowState a, (s.operator =ₖ t.operator ↔ s = t)
  pathOperatorClassifiedByMinimum :
    ∀ P Q : SoninScalePath,
      P.start = Q.start → P.endpoint = Q.endpoint →
      (P.operator a =ₖ Q.operator a ↔ P.minimum = Q.minimum)
  pathWordsNoncompact :
    ∀ P : SoninScalePath, ¬ IsCompactOperator (P.operator a)
  endpointAbsorptionClassifiedByMinimum :
    ∀ P : SoninScalePath,
      (P.operator a =ₖ
          (soninGramFactorOfScales P.start P.endpoint P.start_gt_one
            P.endpoint_gt_one).operator a ↔
        P.minimum = min P.start P.endpoint)
  tropicalConcatenation :
    ∀ (p q r m n : ℝ)
      (ha : 0 < a)
      (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
      (hm : 1 < m) (hn : 1 < n)
      (hmp : m ≤ p) (hmq : m ≤ q) (hnq : n ≤ q) (hnr : n ≤ r),
      composeSoninLiveWindows
          (soninPathWindow a p q m ha hp hq hm hmp hmq)
          (soninPathWindow a q r n ha hq hr hn hnq hnr) =
        SoninWindowState.live
          (soninPathWindow a p r (min m n) ha hp hr (lt_min hm hn)
            ((min_le_left m n).trans hmp) ((min_le_right m n).trans hnr))

/-- **Sonin tropical Calkin path universality law.** At every positive cutoff, genuine finite
Gram paths form a faithful noncompact tropical path representation inside the canonical Sonin
inverse semigroup; fixed-endpoint Calkin classes are classified exactly by one minimum. -/
theorem soninTropicalCalkinPathUniversalCertificate
    {a : ℝ} (ha : 0 < a) :
    SoninTropicalCalkinPathUniversalCertificate a := by
  exact {
    stateUniqueInverse := SoninWindowState.existsUnique_inverse ha
    stateIdempotentsCommute := composeSoninWindowStates_idempotents_comm ha
    stateOperatorFaithful := fun s t => s.operator_compactEq_iff ha t
    pathOperatorClassifiedByMinimum :=
      fun P Q hstart hend => P.operator_compactEq_iff_minimum_eq a ha Q hstart hend
    pathWordsNoncompact := SoninScalePath.operator_not_isCompactOperator a ha
    endpointAbsorptionClassifiedByMinimum :=
      SoninScalePath.operator_compactEq_direct_iff_minimum_eq_endpointMin a ha
    tropicalConcatenation := fun p q r m n ha' hp hq hr hm hn hmp hmq hnq hnr =>
      composeSoninPathWindows a p q r m n ha' hp hq hr hm hn hmp hmq hnq hnr }

end

end RHTower
