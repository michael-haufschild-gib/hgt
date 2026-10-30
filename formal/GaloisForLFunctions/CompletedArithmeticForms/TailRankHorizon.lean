import GaloisForLFunctions.CompletedArithmeticForms.PhysicalQuadraticHorizon
import GaloisForLFunctions.CompletedArithmeticForms.SeamCoercivity

/-!
# Logarithmic rank boundary and strict order of complete native tails

The literal complete native signed form is positive throughout every tail beyond
the quadratic rank horizon. Exact integration retains strictness and makes the
tail heads strictly decreasing in Loewner order on that ray. Their exact Schur
successors retain the corresponding order with their own integrated inverse heads.
-/

noncomputable section

open MeasureTheory Matrix Finset Set

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower

private theorem signedHead_quadratic_eq {N : ℕ} (x : ℝ) (v : Fin N → ℝ) :
    v ⬝ᵥ finiteHankelMatrix (thetaCuspNativeSignedJet x) N *ᵥ v =
      thetaCuspNativeSignedHankelForm x v := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, finiteHankelMatrix,
    thetaCuspNativeSignedHankelForm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Every nonzero mixed direction is strict beyond the logarithmic source horizon. -/
theorem nativeSignedHankelForm_pos_of_quadratic_rank_horizon {N : ℕ}
    {v : Fin N → ℝ} (hv : v ≠ 0) {x : ℝ}
    (hx : nativeQuadraticRankHorizon (N + 1) ≤ x) :
    0 < thetaCuspNativeSignedHankelForm x v := by
  have h := (Matrix.posDef_iff_dotProduct_mulVec.mp
    (nativeSignedHead_posDef_of_quadratic_rank_horizon N hx)).2 (x := v) hv
  simpa only [star_trivial, signedHead_quadratic_eq] using h

/-- The complete native tail is strict at a center logarithmic in its rank. -/
theorem nativeTailHead_posDef_of_quadratic_rank_horizon (N : ℕ) {r : ℝ}
    (hr : 2 * nativeQuadraticRankHorizon (N + 1) ≤ r) : (nativeTailHead N r).PosDef := by
  have hH : 0 ≤ nativeQuadraticRankHorizon (N + 1) := le_max_left _ _
  have hr0 : 0 ≤ r := by linarith only [hr, hH]
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp [nativeTailHead, finiteHankelMatrix, Nat.add_comm]
  · intro v hv
    have hpos (s : ℝ) (hs : s ∈ Ioi r) :
        0 < thetaCuspNativeSignedHankelForm (s / 2) v := by
      apply nativeSignedHankelForm_pos_of_quadratic_rank_horizon hv
      have hs' : r < s := hs
      linarith only [hr, hs']
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi r)]
        (fun s => thetaCuspNativeSignedHankelForm (s / 2) v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hpos s hs).le
    rw [star_trivial, nativeTailHead_quadratic_eq_integral v hr0,
      setIntegral_pos_iff_support_of_nonneg_ae hnn (integrableOn_nativeSignedHankelForm_tail v hr0)]
    have hsupport : Ioi r ⊆ Function.support (fun s => thetaCuspNativeSignedHankelForm (s / 2) v) :=
      fun s hs => (hpos s hs).ne'
    rw [Set.inter_eq_right.mpr hsupport]
    exact isOpen_Ioi.measure_pos volume ⟨r + 1, by change r < r + 1; linarith⟩

/-- Subtracting complete tails retains the full native mixed form on the intervening interval. -/
theorem nativeTailHead_sub_quadratic_eq_integral {N : ℕ} (v : Fin N → ℝ)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    v ⬝ᵥ (nativeTailHead N r - nativeTailHead N t) *ᵥ v =
      ∫ s in Ioc r t, thetaCuspNativeSignedHankelForm (s / 2) v := by
  have hi := integrableOn_nativeSignedHankelForm_tail v hr
  have hsplit : Ioi r = Ioc r t ∪ Ioi t := by
    ext s
    constructor
    · intro hs
      rcases le_or_gt s t with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr h
    · rintro (⟨hs, _⟩ | hs)
      · exact hs
      · exact lt_of_le_of_lt hrt hs
  have hdisj : Disjoint (Ioc r t) (Ioi t) := by
    rw [Set.disjoint_left]
    rintro s ⟨_, hs⟩ ht
    exact (not_lt.mpr hs) ht
  have hsum : (∫ s in Ioi r, thetaCuspNativeSignedHankelForm (s / 2) v) =
      (∫ s in Ioc r t, thetaCuspNativeSignedHankelForm (s / 2) v) +
        ∫ s in Ioi t, thetaCuspNativeSignedHankelForm (s / 2) v := by
    rw [hsplit]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hi.mono_set (fun _ h => h.1))
      (hi.mono_set (fun _ h => lt_of_le_of_lt hrt h))
  rw [sub_mulVec, dotProduct_sub, nativeTailHead_quadratic_eq_integral v hr,
    nativeTailHead_quadratic_eq_integral v (hr.trans hrt), hsum]
  ring

/-- Complete native tails decrease strictly in Loewner order beyond their logarithmic boundary. -/
theorem nativeTailHead_sub_posDef_of_quadratic_rank_horizon (N : ℕ) {r t : ℝ}
    (hr : 2 * nativeQuadraticRankHorizon (N + 1) ≤ r) (hrt : r < t) :
    (nativeTailHead N r - nativeTailHead N t).PosDef := by
  have hH : 0 ≤ nativeQuadraticRankHorizon (N + 1) := le_max_left _ _
  have hr0 : 0 ≤ r := by linarith only [hr, hH]
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp [nativeTailHead, finiteHankelMatrix, Nat.add_comm]
  · intro v hv
    have hi := (integrableOn_nativeSignedHankelForm_tail v hr0).mono_set
      (show Ioc r t ⊆ Ioi r from fun _ h => h.1)
    have hpos (s : ℝ) (hs : s ∈ Ioc r t) :
        0 < thetaCuspNativeSignedHankelForm (s / 2) v := by
      apply nativeSignedHankelForm_pos_of_quadratic_rank_horizon hv
      have hs' := hs.1
      linarith only [hr, hs']
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc r t)]
        (fun s => thetaCuspNativeSignedHankelForm (s / 2) v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (hpos s hs).le
    rw [star_trivial, nativeTailHead_sub_quadratic_eq_integral v hr0 hrt.le,
      setIntegral_pos_iff_support_of_nonneg_ae hnn hi]
    have hsupport : Ioc r t ⊆ Function.support (fun s => thetaCuspNativeSignedHankelForm (s / 2) v) :=
      fun s hs => (hpos s hs).ne'
    rw [Set.inter_eq_right.mpr hsupport]
    have hm : 0 < volume (Ioo r t) := isOpen_Ioo.measure_pos volume
      ⟨(r + t) / 2, by constructor <;> linarith only [hrt]⟩
    exact hm.trans_le (measure_mono (fun _ h => ⟨h.1, h.2.le⟩))

/-- Exact integrated successors decrease along the paid tail ray. -/
theorem nativeTailSuccessor_antitone_of_quadratic_rank_horizon (N : ℕ) {r t : ℝ}
    (hr : 2 * nativeQuadraticRankHorizon (N + 2) ≤ r) (hrt : r ≤ t) :
    finiteHankelSuccessorSchur (fun k => thetaCuspNativeSignedJetTail k t) N ≤
      finiteHankelSuccessorSchur (fun k => thetaCuspNativeSignedJetTail k r) N := by
  rcases eq_or_lt_of_le hrt with h | h
  · subst t
    exact le_rfl
  have hR := nativeTailHead_posDef_of_quadratic_rank_horizon (N + 1) hr
  have hT := nativeTailHead_posDef_of_quadratic_rank_horizon (N + 1) (hr.trans hrt)
  have he : Function.Injective (Fin.castSucc : Fin N → Fin (N + 1)) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (N + 1) => z.val) hij)
  exact successorSchur_mono (hR.submatrix he) (hT.submatrix he)
    (nativeTailHead_sub_posDef_of_quadratic_rank_horizon (N + 1) hr h).posSemidef

#print axioms nativeTailHead_posDef_of_quadratic_rank_horizon
#print axioms nativeTailHead_sub_quadratic_eq_integral
#print axioms nativeTailHead_sub_posDef_of_quadratic_rank_horizon
#print axioms nativeTailSuccessor_antitone_of_quadratic_rank_horizon

end GaloisForLFunctions.CompletedArithmeticForms
