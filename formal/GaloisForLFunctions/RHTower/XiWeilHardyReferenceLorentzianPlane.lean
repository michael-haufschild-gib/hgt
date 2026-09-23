import GaloisForLFunctions.RHTower.XiWeilSpectralFoldIndexConservation
import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositiveBoundarySourceSaturation
import GaloisForLFunctions.RHTower.XiHurwitzOrientationSourceSequenceGate
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.XiSpectralSupportCriterion
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# A Hardy reference packet and finite source Lorentzian planes

Hardy's theorem supplies an unconditional critical-line Xi zero.  Its full multiplicity fiber is
a nonzero reflection-fixed vector, hence has strictly positive Xi Weil energy.  Universal
continued-Cauchy reconstruction and openness of strict positivity then produce an actual finite,
pairwise-separated prime--Gamma source packet with strictly positive source energy.

This positive packet is a time-like reference for the reflected source form.  Any negative source
packet forced by failure of RH forms with it a literal `2 x 2` Hermitian Lorentzian plane: the two
diagonal energies have opposite signs and the determinant is strictly negative.  Conversely, under
RH every finite source Gram is positive semidefinite.  Thus any one positive reference packet
reduces RH to either nonnegativity of one family of `2 x 2` determinants or one fixed-reference
reflected Cauchy--Schwarz inequality.

The reference packet is selected through Hardy's zero and Hilbert closure; this module does not
prove the remaining source-first Cauchy--Schwarz inequality.
-/

open scoped ComplexConjugate BigOperators Topology ComplexOrder
open Complex Matrix Filter

namespace RHTower

noncomputable section

/-- Reflected source-packet Gram matrices are unconditionally Hermitian. -/
theorem xiSeparatedPacketWeilGram_isHermitian {k : ℕ}
    (P : Fin k → XiSeparatedContinuedCauchyPacket) :
    (xiSeparatedPacketWeilGram P).IsHermitian := by
  ext j l
  show (starRingEnd ℂ) (xiSeparatedPacketWeilGram P l j) =
    xiSeparatedPacketWeilGram P j l
  simp only [xiSeparatedPacketWeilGram]
  rw [inner_conj_symm]
  simpa only [xiWeilLineConjLinearIsometry_apply] using
    (CliffordWeil.inner_map_left_eq_inner_map_right
      xiWeilLineConjLinearIsometry
      xiWeilLineConjLinearIsometry_involutive
      (P l).evaluation (P j).evaluation).symm

/-- Exact determinant law for two explicit separated prime--Gamma source packets. -/
theorem xiSeparatedPacketWeilGram_two_det_re
    (P : Fin 2 → XiSeparatedContinuedCauchyPacket) :
    (xiSeparatedPacketWeilGram P).det.re =
      (P 0).sourceEnergy * (P 1).sourceEnergy -
        Complex.normSq (xiSeparatedPacketWeilGram P 0 1) := by
  let G := xiSeparatedPacketWeilGram P
  have hG : G.IsHermitian := xiSeparatedPacketWeilGram_isHermitian P
  have h00im : (G 0 0).im = 0 := by
    have h := congrArg Complex.im (hG.apply 0 0)
    simp at h
    linarith
  have h11im : (G 1 1).im = 0 := by
    have h := congrArg Complex.im (hG.apply 1 1)
    simp at h
    linarith
  have h10re : (G 1 0).re = (G 0 1).re := by
    have h := congrArg Complex.re (hG.apply 0 1)
    simpa using h
  have h10im : (G 1 0).im = -(G 0 1).im := by
    have h := congrArg Complex.im (hG.apply 0 1)
    simp at h
    linarith
  have h00re : (G 0 0).re = (P 0).sourceEnergy := by
    exact xiSeparatedPacketWeilGram_diagonal_re P 0
  have h11re : (G 1 1).re = (P 1).sourceEnergy := by
    exact xiSeparatedPacketWeilGram_diagonal_re P 1
  rw [Matrix.det_fin_two]
  change
    ((G 0 0 * G 1 1 - G 0 1 * G 1 0).re) =
      (P 0).sourceEnergy * (P 1).sourceEnergy -
        Complex.normSq (G 0 1)
  simp only [Complex.sub_re, Complex.mul_re]
  rw [h00im, h11im, h10re, h10im, h00re, h11re]
  simp only [mul_zero, sub_zero, Complex.normSq_apply]
  ring

/-- A two-packet determinant is nonnegative exactly at the reflected Cauchy--Schwarz wall. -/
theorem xiSeparatedPacketWeilGram_two_det_nonnegative_iff
    (P : Fin 2 → XiSeparatedContinuedCauchyPacket) :
    0 ≤ (xiSeparatedPacketWeilGram P).det.re ↔
      Complex.normSq (xiSeparatedPacketWeilGram P 0 1) ≤
        (P 0).sourceEnergy * (P 1).sourceEnergy := by
  rw [xiSeparatedPacketWeilGram_two_det_re, sub_nonneg]

/-- Under RH every finite reflected source Gram is positive semidefinite. -/
theorem xiSeparatedPacketWeilGram_posSemidef_of_riemannHypothesis
    {k : ℕ} (hRH : RiemannHypothesis)
    (P : Fin k → XiSeparatedContinuedCauchyPacket) :
    (xiSeparatedPacketWeilGram P).PosSemidef := by
  apply GaloisForLFunctions.HTGeometry.posSemidef_of_isHermitian_of_re_nonneg
    (xiSeparatedPacketWeilGram_isHermitian P)
  intro x
  rw [xiSeparatedPacketWeilGram_eq_xiWeilHilbertGram,
    xiWeilHilbertGram_quadratic]
  simpa only [xiWeilHilbertQuadratic,
    xiWeilLineConjLinearIsometry_apply] using
    xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH
      (∑ j, star (x j) • (P j).evaluation)

/-- Hardy's theorem supplies an unconditional critical-line point of the Xi divisor. -/
theorem exists_criticalLine_xiDivisorSupport_of_hardy :
    ∃ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2 := by
  obtain ⟨T₀, _hT₀, hzero⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨t, _ht, hzeta⟩ := hzero T₀ le_rfl
  have hnontrivial : ∀ n : ℕ,
      linePt t ≠ -(2 * ((n : ℂ) + 1)) := by
    intro n h
    have hre := congrArg Complex.re h
    have hre' : (1 / 2 : ℝ) = -2 * ((n : ℝ) + 1) := by
      simpa [linePt] using hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hxi : xi (linePt t) = 0 :=
    xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr
      ⟨hzeta, hnontrivial⟩
  let ρ : XiDivisorSupport :=
    ⟨linePt t, mem_xi_divisor_support_of_eq_zero hxi⟩
  refine ⟨ρ, ?_⟩
  simp [ρ, linePt]

/-- There exists an actual finite separated prime--Gamma packet with strictly positive source
energy, unconditionally.  The proof reconstructs a nonzero Hardy critical-line fiber. -/
theorem exists_xiSeparatedContinuedCauchyPacket_sourceEnergy_pos :
    ∃ Q : XiSeparatedContinuedCauchyPacket, 0 < Q.sourceEnergy := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  let α : ℂ := xiSpectralPointSupport ρ
  let v : lp (fun _ : XiZeroCopy => ℂ) 2 := xiWeilFiberIndicatorLp α
  have hαim : α.im = 0 := by
    exact (xiSpectralPointSupport_im_eq_zero_iff ρ).2 hρ
  have hαstar : (starRingEnd ℂ) α = α := by
    apply Complex.ext
    · simp
    · simp [hαim]
  have hvfix : xiWeilLineConjLinearIsometry v = v := by
    apply Subtype.ext
    funext q
    rw [xiWeilLineConjLinearIsometry_apply, xiWeilLineConjLp_apply]
    simp only [v, xiWeilFiberIndicatorLp_apply, xiSpectralPoint_lineConj]
    by_cases hq : xiSpectralPoint q = α
    · simp [hq, hαstar]
    · have hj : (starRingEnd ℂ) (xiSpectralPoint q) ≠ α := by
        intro h
        apply hq
        have h' := congrArg (starRingEnd ℂ) h
        simpa [hαstar] using h'
      simp [hq, hj]
  have hvne : v ≠ 0 := by
    intro hv
    have hval := congrArg (fun w => w (xiFirstZeroCopy ρ)) hv
    simp [v, α, xiWeilFiberIndicatorLp_apply,
      xiSpectralPoint_eq_support] at hval
  have hvpos : 0 < xiWeilHilbertQuadratic v := by
    rw [xiWeilHilbertQuadratic, hvfix]
    have hinner : (inner ℂ v v).re = ‖v‖ ^ (2 : ℕ) := by
      change RCLike.re (inner ℂ v v) = _
      exact inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hinner]
    positivity
  have hvmem : v ∈ xiWeilContinuedCauchyHilbertSubspace := by
    simpa only [v, α, xiSpectralPoint_eq_support] using!
      xiWeilFiberIndicatorLp_mem_continuedCauchyHilbertSubspace
        (xiFirstZeroCopy ρ)
  have hvclosure : v ∈ closure xiSeparatedContinuedCauchyPacketEvaluationSet :=
    xiWeilContinuedCauchyHilbertSubspace_le_closure_separatedPacketEvaluations hvmem
  obtain ⟨Q, hQpos, _hQnear⟩ :=
    exists_separatedContinuedCauchyPacket_sourceEnergy_pos_near
      hvclosure hvpos (by norm_num : (0 : ℝ) < 1)
  exact ⟨Q, hQpos⟩

/-- Any positive source packet is a complete fixed reference: RH is equivalent to nonnegativity
of its `2 x 2` determinant against every source packet. -/
theorem riemannHypothesis_iff_two_det_nonnegative_against_positivePacket
    (Q : XiSeparatedContinuedCauchyPacket) (hQ : 0 < Q.sourceEnergy) :
    RiemannHypothesis ↔
      ∀ P : XiSeparatedContinuedCauchyPacket,
        0 ≤ (xiSeparatedPacketWeilGram ![P, Q]).det.re := by
  constructor
  · intro hRH P
    have hdet :=
      (xiSeparatedPacketWeilGram_posSemidef_of_riemannHypothesis hRH ![P, Q]).det_nonneg
    exact (RCLike.nonneg_iff.mp hdet).1
  · intro hall
    by_contra hRH
    obtain ⟨P, hP⟩ :=
      not_riemannHypothesis_iff_exists_xiSeparatedPacket_sourceEnergy_neg.mp hRH
    let W : Fin 2 → XiSeparatedContinuedCauchyPacket := ![P, Q]
    have hW0 : (W 0).sourceEnergy < 0 := by simpa [W] using hP
    have hW1 : 0 < (W 1).sourceEnergy := by simpa [W] using hQ
    have hdetneg : (xiSeparatedPacketWeilGram W).det.re < 0 := by
      rw [xiSeparatedPacketWeilGram_two_det_re]
      have hprod : (W 0).sourceEnergy * (W 1).sourceEnergy < 0 :=
        mul_neg_of_neg_of_pos hW0 hW1
      exact lt_of_le_of_lt
        (sub_le_self _ (Complex.normSq_nonneg _)) hprod
    exact (not_lt_of_ge (by simpa [W] using hall P)) hdetneg

/-- Fixed-reference source form of Cauchy--Schwarz is exactly RH for every positive packet. -/
theorem riemannHypothesis_iff_reflectedCauchySchwarz_against_positivePacket
    (Q : XiSeparatedContinuedCauchyPacket) (hQ : 0 < Q.sourceEnergy) :
    RiemannHypothesis ↔
      ∀ P : XiSeparatedContinuedCauchyPacket,
        Complex.normSq
            (inner ℂ (xiWeilLineConjLp Q.evaluation) P.evaluation) ≤
          P.sourceEnergy * Q.sourceEnergy := by
  rw [riemannHypothesis_iff_two_det_nonnegative_against_positivePacket Q hQ]
  apply forall_congr'
  intro P
  rw [xiSeparatedPacketWeilGram_two_det_nonnegative_iff]
  simp [xiSeparatedPacketWeilGram]

/-- An unconditional positive reference packet reduces RH to one determinant family. -/
theorem exists_positiveReferencePacket_riemannHypothesis_iff_two_det_nonnegative :
    ∃ Q : XiSeparatedContinuedCauchyPacket,
      0 < Q.sourceEnergy ∧
      (RiemannHypothesis ↔
        ∀ P : XiSeparatedContinuedCauchyPacket,
          0 ≤ (xiSeparatedPacketWeilGram ![P, Q]).det.re) := by
  obtain ⟨Q, hQ⟩ := exists_xiSeparatedContinuedCauchyPacket_sourceEnergy_pos
  exact ⟨Q, hQ,
    riemannHypothesis_iff_two_det_nonnegative_against_positivePacket Q hQ⟩

/-- An unconditional positive reference packet reduces RH to one reflected Cauchy--Schwarz
family. -/
theorem exists_positiveReferencePacket_riemannHypothesis_iff_reflectedCauchySchwarz :
    ∃ Q : XiSeparatedContinuedCauchyPacket,
      0 < Q.sourceEnergy ∧
      (RiemannHypothesis ↔
        ∀ P : XiSeparatedContinuedCauchyPacket,
          Complex.normSq
              (inner ℂ (xiWeilLineConjLp Q.evaluation) P.evaluation) ≤
            P.sourceEnergy * Q.sourceEnergy) := by
  obtain ⟨Q, hQ⟩ := exists_xiSeparatedContinuedCauchyPacket_sourceEnergy_pos
  exact ⟨Q, hQ,
    riemannHypothesis_iff_reflectedCauchySchwarz_against_positivePacket Q hQ⟩

/-- Failure of RH is exactly existence of a literal finite source Lorentzian plane. -/
theorem not_riemannHypothesis_iff_exists_xiSeparatedPacketWeilGram_lorentzian :
    ¬ RiemannHypothesis ↔
      ∃ P : Fin 2 → XiSeparatedContinuedCauchyPacket,
        (P 0).sourceEnergy < 0 ∧
        0 < (P 1).sourceEnergy ∧
        (xiSeparatedPacketWeilGram P).det.re < 0 := by
  constructor
  · intro hRH
    obtain ⟨Pneg, hneg⟩ :=
      not_riemannHypothesis_iff_exists_xiSeparatedPacket_sourceEnergy_neg.mp hRH
    obtain ⟨Ppos, hpos⟩ :=
      exists_xiSeparatedContinuedCauchyPacket_sourceEnergy_pos
    let P : Fin 2 → XiSeparatedContinuedCauchyPacket := ![Pneg, Ppos]
    refine ⟨P, ?_, ?_, ?_⟩
    · simpa [P] using hneg
    · simpa [P] using hpos
    · rw [xiSeparatedPacketWeilGram_two_det_re]
      have hprod : (P 0).sourceEnergy * (P 1).sourceEnergy < 0 :=
        mul_neg_of_neg_of_pos (by simpa [P] using hneg)
          (by simpa [P] using hpos)
      exact lt_of_le_of_lt
        (sub_le_self _ (Complex.normSq_nonneg _)) hprod
  · rintro ⟨P, hneg, _hpos, _hdet⟩
    exact not_riemannHypothesis_iff_exists_xiSeparatedPacket_sourceEnergy_neg.mpr
      ⟨P 0, hneg⟩

/-- Rank-two determinant criterion on all separated prime--Gamma packet pairs. -/
theorem riemannHypothesis_iff_forall_xiSeparatedPacketWeilGram_two_det_nonnegative :
    RiemannHypothesis ↔
      ∀ P : Fin 2 → XiSeparatedContinuedCauchyPacket,
        0 ≤ (xiSeparatedPacketWeilGram P).det.re := by
  constructor
  · intro hRH P
    have hdet :=
      (xiSeparatedPacketWeilGram_posSemidef_of_riemannHypothesis hRH P).det_nonneg
    exact (RCLike.nonneg_iff.mp hdet).1
  · intro hall
    by_contra hRH
    obtain ⟨P, _hneg, _hpos, hdet⟩ :=
      not_riemannHypothesis_iff_exists_xiSeparatedPacketWeilGram_lorentzian.mp hRH
    exact (not_lt_of_ge (hall P)) hdet

end

end RHTower
