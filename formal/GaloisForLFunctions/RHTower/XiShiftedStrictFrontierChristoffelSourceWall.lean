import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionScaleCompletedArithmeticSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDefectEnergy
import GaloisForLFunctions.RHTower.XiShiftedTerminalFrontierZeroPhaseLaw
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Christoffel source walls at strict shifted-Xi frontiers

The adaptive arithmetic source is formed from current inverse-Hankel admission before reflection
aggregation.  This file identifies its exact behavior at an actual strict terminal frontier.

At such a frontier the newly admitted monic flag is the normalized null vector of the singular
positive-semidefinite extension, so its norm vanishes.  The preceding adaptive source does not
vanish: its Jacobi energy retains the previous positive Christoffel edge.  Consequently source
completed by the next admitted norm tends to `+∞` from the positive side of every strict frontier.

This is a source law, not an orientation map or a fixed linear reporter.  The pole belongs to the
endogenous admission scale; the literal arithmetic numerator remains finite and positive.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

noncomputable section

/-- Actual source-first adaptive shear completed by the next current admitted norm. -/
def xiShiftedCanonicalAdmissionChristoffelSourceWall
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveShear y n /
    (16 * xiShiftedCanonicalAdmissionNorm y (n + 1))

/-- The completed-square Jacobi energy strictly dominates its current positive edge. -/
theorem adaptiveOrthoJacobiEnergy_gt_succ_mul_currentBeta
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n <
      HTGeometry.adaptiveOrthoJacobiEnergy s n := by
  have hsquares :
      0 ≤ ∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha s j +
          HTGeometry.monicOrthoAlpha s n / 2) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag :
      0 ≤ (3 * (n : ℝ) / 4 + 1) *
        HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) := by
    positivity
  have hinterior :
      0 ≤ 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hboundary :
      (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n <
        (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n +
            HTGeometry.monicOrthoBeta s (n + 1)) := by
    have hnext := HTGeometry.monicOrthoBeta_pos_below
      (n := n + 1) h (by omega) (by omega)
    have hdegree : 0 < (n + 1 : ℝ) := by positivity
    nlinarith
  unfold HTGeometry.adaptiveOrthoJacobiEnergy
  linarith

/-- In a positive chamber, actual adaptive shear is current admitted norm times Jacobi energy. -/
theorem xiShiftedCanonicalAdmissionAdaptiveShear_eq_norm_mul_jacobiEnergy
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAdaptiveShear y n =
      xiShiftedCanonicalAdmissionNorm y n *
        HTGeometry.adaptiveOrthoJacobiEnergy
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hP : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedCanonicalAdmissionAdaptiveShear, HTGeometry.momentInner_def]
  rw [hP]
  have hshear :
      (X * HTGeometry.monicOrtho s n) *
          (X * xiShiftedBoundaryShiftedEuler 1 (HTGeometry.monicOrtho s n)) =
        HTGeometry.adaptiveOrthoSourcePolynomial s n := by
    simp only [xiShiftedBoundaryShiftedEuler,
      HTGeometry.adaptiveOrthoSourcePolynomial, C_1, one_mul]
  rw [hshear]
  rw [HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
    hbelow hn le_rfl]
  rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]

/-- Head positivity alone identifies actual inverse-Hankel admission norm with monic orthogonal
norm.  No positivity of either following Hankel extension is needed. -/
theorem xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef) :
    xiShiftedCanonicalAdmissionNorm y n =
      HTGeometry.monicOrthoNormSq
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  rw [xiShiftedCanonicalAdmissionNorm,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hH]
  rfl

/-- The previous Christoffel edge gives a strict division-free lower bound for actual source. -/
theorem succ_mul_admissionNorm_mul_prevNormRatio_lt_adaptiveShear
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (n + 1 : ℝ) * xiShiftedCanonicalAdmissionNorm y n *
        (xiShiftedCanonicalAdmissionNorm y n /
          xiShiftedCanonicalAdmissionNorm y (n - 1)) <
      xiShiftedCanonicalAdmissionAdaptiveShear y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have henergy := adaptiveOrthoJacobiEnergy_gt_succ_mul_currentBeta hbelow hn le_rfl
  have hnorm : xiShiftedCanonicalAdmissionNorm y n =
      HTGeometry.monicOrthoNormSq s n := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH
  have hprevH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n - 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hprev : xiShiftedCanonicalAdmissionNorm y (n - 1) =
      HTGeometry.monicOrthoNormSq s (n - 1) := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hprevH
  have hbeta : HTGeometry.monicOrthoBeta s n =
      xiShiftedCanonicalAdmissionNorm y n /
        xiShiftedCanonicalAdmissionNorm y (n - 1) := by
    rcases n with _ | m
    · omega
    · simp only [HTGeometry.monicOrthoBeta, Nat.succ_sub_one]
      have hprev' : xiShiftedCanonicalAdmissionNorm y m =
          HTGeometry.monicOrthoNormSq s m := by
        simpa only [Nat.succ_sub_one] using hprev
      rw [hnorm, hprev']
  have hnormPos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [hnorm]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  rw [xiShiftedCanonicalAdmissionAdaptiveShear_eq_norm_mul_jacobiEnergy hn hH,
    ← hbeta]
  nlinarith

/-- Actual canonical admitted norm is continuous at every positive mass where its leading block
is nonsingular, including degree zero. -/
theorem continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (xiShiftedMomentHankelMatrix y n).det ≠ 0) :
    ContinuousAt (fun v => xiShiftedCanonicalAdmissionNorm v n) y := by
  rcases n with _ | n
  · have hzero : (fun v => xiShiftedCanonicalAdmissionNorm v 0) =
        (fun v => (xiShiftedReciprocalMoment v 0).re) := by
      funext v
      let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment v k).re
      have hP : HTGeometry.monicMomentAdmissionPolynomial s 0 = 1 := by
        rw [HTGeometry.monicMomentAdmissionPolynomial_eq]
        simp
      rw [xiShiftedCanonicalAdmissionNorm]
      change HTGeometry.momentInner s
        (HTGeometry.monicMomentAdmissionPolynomial s 0)
        (HTGeometry.monicMomentAdmissionPolynomial s 0) = _
      rw [hP, HTGeometry.momentInner_def, one_mul,
        HTGeometry.momentFunctional_one_eq]
    rw [hzero]
    exact (hasDerivAt_re_xiShiftedReciprocalMoment hy 0).continuousAt
  · exact (hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
      hy (Nat.succ_pos n) hdet).continuousAt

/-- A singular positive-semidefinite Hankel extension with positive head annihilates the canonical
terminal-normalized inverse-Hankel admission. -/
theorem xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
    {y : ℝ} {n : ℕ}
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hpsd : (xiShiftedMomentHankelMatrix y (n + 1)).PosSemidef)
    (hnot : ¬(xiShiftedMomentHankelMatrix y (n + 1)).PosDef) :
    xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
        HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment y k).re) n = 0 := by
  have hdet : (xiShiftedMomentHankelMatrix y (n + 1)).det = 0 :=
    not_ne_iff.mp ((hpsd.posDef_iff_det_ne_zero).not.mp hnot)
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hlast : c (Fin.last n) ≠ 0 :=
    xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
      y n c hhead hcne hc
  let d : Fin (n + 1) → ℝ := (c (Fin.last n))⁻¹ • c
  have hd : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ d = 0 := by
    change xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      ((c (Fin.last n))⁻¹ • c) = 0
    rw [Matrix.mulVec_smul, hc, smul_zero]
  have hdlast : d (Fin.last n) = 1 := by
    simp [d, hlast]
  have heq : d = HTGeometry.monicMomentAdmissionVector
      (fun k => (xiShiftedReciprocalMoment y k).re) n := by
    have hmatrix : xiShiftedMomentHankelMatrix y n =
        HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
      ext i j
      rfl
    have hhead' : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef := by
      rw [← hmatrix]
      exact hhead
    have hmatrixNext : xiShiftedMomentHankelMatrix y (n + 1) =
        HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) := by
      ext i j
      rfl
    apply HTGeometry.eq_monicMomentAdmissionVector_of_kernel_of_last_eq_one
      (ne_of_gt hhead'.det_pos)
    · rw [← hmatrixNext]
      exact hd
    · exact hdlast
  rwa [← heq]

/-- At an occupied strict frontier, next canonical admitted norm is exactly zero. -/
theorem xiShiftedCanonicalAdmissionNorm_eq_zero_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 2) = 0 := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hflat :=
    xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
      hface.1 hface.2.1 hface.2.2
  exact xiShiftedCanonicalAdmissionNorm_eq_zero_of_flatFace hflat

/-- Canonical monic admission minimizes the moment square among all monic polynomials of the same
positive degree.  The proof is the exact admission-sensitive Pythagorean decomposition, not a
fixed reporting functional. -/
theorem xiShiftedCanonicalAdmissionNorm_le_momentInner_monic
    {v : ℝ} {m : ℕ} (hm : 0 < m)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment v k).re) (m + 1)).PosDef)
    (A : Polynomial ℝ) (hA : A.Monic) (hAdeg : A.natDegree = m) :
    xiShiftedCanonicalAdmissionNorm v m ≤
      HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re) A A := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment v k).re
  let P : Polynomial ℝ := HTGeometry.monicMomentAdmissionPolynomial s m
  let R : Polynomial ℝ := A - P
  have hhead : (HTGeometry.momentHankelMatrix s m).PosDef := by
    simpa only [s] using xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hPmonic : P.Monic := by
    simpa only [P] using HTGeometry.monicMomentAdmissionPolynomial_monic s m
  have hPdeg : P.natDegree = m := by
    simpa only [P] using HTGeometry.monicMomentAdmissionPolynomial_natDegree s m
  have hRdeg : R.degree < (m : WithBot ℕ) := by
    have hdeg : A.degree = P.degree := by
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree hPmonic.ne_zero, hAdeg, hPdeg]
    have hlc : A.leadingCoeff = P.leadingCoeff := by
      rw [hA.leadingCoeff, hPmonic.leadingCoeff]
    have hlt := Polynomial.degree_sub_lt hdeg hA.ne_zero hlc
    have hAdegree : A.degree = (m : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hA.ne_zero, hAdeg]
    rw [hAdegree] at hlt
    simpa only [R] using hlt
  have hRnat : R.natDegree < m := by
    by_cases hRzero : R = 0
    · rw [hRzero, Polynomial.natDegree_zero]
      exact hm
    · exact (Polynomial.natDegree_lt_iff_degree_lt hRzero).mpr hRdeg
  have horth : HTGeometry.momentInner s P R = 0 := by
    exact HTGeometry.momentInner_monicMomentAdmission_lower_eq_zero
      (ne_of_gt hhead.det_pos) hRnat
  have hRnonneg : 0 ≤ HTGeometry.momentInner s R R := by
    by_cases hRzero : R = 0
    · simp [hRzero]
    · exact (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH).self_pos
        hRzero (hRnat.trans_le (Nat.le_add_right m 1)) |>.le
  have hsplit : A = P + R := by
    dsimp only [R]
    ring
  rw [xiShiftedCanonicalAdmissionNorm]
  change HTGeometry.momentInner s P P ≤ HTGeometry.momentInner s A A
  rw [hsplit, HTGeometry.momentInner_add_left,
    HTGeometry.momentInner_add_right, HTGeometry.momentInner_add_right,
    horth, HTGeometry.momentInner_comm s R P, horth]
  linarith

/-- A moving canonical monic admission is bounded above by the quadratic energy of any frozen
canonical admission packet of the same degree. -/
theorem xiShiftedCanonicalAdmissionNorm_le_frozenAdmissionQuadratic
    {a v : ℝ} {m : ℕ} (hm : 0 < m)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment v k).re) (m + 1)).PosDef) :
    xiShiftedCanonicalAdmissionNorm v m ≤
      xiShiftedMomentHankelQuadratic v (m + 1)
        (HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment a k).re) m) := by
  let A := HTGeometry.monicMomentAdmissionPolynomial
    (fun k => (xiShiftedReciprocalMoment a k).re) m
  have hmin := xiShiftedCanonicalAdmissionNorm_le_momentInner_monic hm hH A
    (HTGeometry.monicMomentAdmissionPolynomial_monic _ _)
    (HTGeometry.monicMomentAdmissionPolynomial_natDegree _ _)
  calc
    xiShiftedCanonicalAdmissionNorm v m ≤
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment v k).re) A A := hmin
    _ = xiShiftedMomentHankelQuadratic v (m + 1)
        (HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment a k).re) m) := by
      have hmatrix : xiShiftedMomentHankelMatrix v (m + 1) =
          HTGeometry.momentHankelMatrix
            (fun k => (xiShiftedReciprocalMoment v k).re) (m + 1) := by
        ext i j
        rfl
      rw [xiShiftedMomentHankelQuadratic, hmatrix]
      simpa only [A, HTGeometry.monicMomentAdmissionPolynomial,
        HTGeometry.finiteHankelNullPolynomial] using
        HTGeometry.momentInner_ofFn_ofFn
          (fun k => (xiShiftedReciprocalMoment v k).re) (m + 1)
          (HTGeometry.monicMomentAdmissionVector
            (fun k => (xiShiftedReciprocalMoment a k).re) m)
          (HTGeometry.monicMomentAdmissionVector
            (fun k => (xiShiftedReciprocalMoment a k).re) m)

/-- **Linear admission collapse at a strict frontier.**  Freeze the terminal null flag at the
frontier.  Canonical minimization bounds the moving next norm by that fixed packet, while the
actual integral Lipschitz theorem bounds the packet by its explicit global weight times distance
from the frontier. -/
theorem xiShiftedCanonicalAdmissionNorm_le_lipschitzWeight_mul_sub_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    {v : ℝ} (hv : xiShiftedHigherBlockTerminalFrontier (n + 1) < v) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    let c := HTGeometry.monicMomentAdmissionVector
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)
    xiShiftedCanonicalAdmissionNorm v (n + 2) ≤
      xiShiftedMomentHankelQuadraticLipschitzWeight c * (v - y) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let c := HTGeometry.monicMomentAdmissionVector
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  have hv0 : 0 ≤ v := (hy.trans hv).le
  have hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment v k).re) (n + 3)).PosDef := by
    simpa only [y, Nat.add_assoc] using
      (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
        (n := n + 1) hv0 hv)
  have hmin : xiShiftedCanonicalAdmissionNorm v (n + 2) ≤
      xiShiftedMomentHankelQuadratic v (n + 3) c := by
    simpa only [c, y, Nat.add_assoc] using
      (xiShiftedCanonicalAdmissionNorm_le_frozenAdmissionQuadratic
        (a := y) (v := v) (m := n + 2) (by omega) hH)
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hflat :=
    xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
      hface.1 hface.2.1 hface.2.2
  have hzero : xiShiftedMomentHankelQuadratic y (n + 3) c = 0 := by
    rw [xiShiftedMomentHankelQuadratic]
    change c ⬝ᵥ (xiShiftedMomentHankelMatrix y (n + 2 + 1) *ᵥ c) = 0
    rw [hflat, dotProduct_zero]
  have hLip := abs_xiShiftedMomentHankelQuadratic_sub_le hy hv.le c
  have hfixed : xiShiftedMomentHankelQuadratic v (n + 3) c ≤
      xiShiftedMomentHankelQuadraticLipschitzWeight c * (v - y) := by
    rw [hzero, sub_zero] at hLip
    exact (le_abs_self _).trans hLip
  exact hmin.trans hfixed

/-- Previous adaptive source remains strictly positive at an occupied strict frontier. -/
theorem xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    0 < xiShiftedCanonicalAdmissionAdaptiveShear
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let d := n + 1
  let source : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionAdaptiveShear v d
  let lower : ℝ → ℝ := fun v =>
    (d + 1 : ℝ) * xiShiftedCanonicalAdmissionNorm v d *
      (xiShiftedCanonicalAdmissionNorm v d /
        xiShiftedCanonicalAdmissionNorm v (d - 1))
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hdH : (xiShiftedMomentHankelMatrix y d).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hprevH : (xiShiftedMomentHankelMatrix y (d - 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hprevNormH : (xiShiftedMomentHankelMatrix y d).PosDef := hdH
  have hsourceCont : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy d (ne_of_gt hdH.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using h
  have hnormCont : ContinuousAt
      (fun v => xiShiftedCanonicalAdmissionNorm v d) y :=
    continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
      hy d (ne_of_gt hdH.det_pos)
  have hprevCont : ContinuousAt
      (fun v => xiShiftedCanonicalAdmissionNorm v (d - 1)) y :=
    continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
      hy (d - 1) (ne_of_gt hprevH.det_pos)
  have hprevPos : 0 < xiShiftedCanonicalAdmissionNorm y (d - 1) := by
    have hmatrix : xiShiftedMomentHankelMatrix y d =
        HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment y k).re) d := by
      ext i j
      rfl
    have hHd : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) d).PosDef := by
      rw [← hmatrix]
      exact hprevNormH
    have hHhead : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (d - 1)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hHd
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hHhead]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hHd) (by omega)
  have hnormPos : 0 < xiShiftedCanonicalAdmissionNorm y d := by
    have hmatrixD : xiShiftedMomentHankelMatrix y d =
        HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment y k).re) d := by
      ext i j
      rfl
    have hHd : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) d).PosDef := by
      rw [← hmatrixD]
      exact hdH
    have hmatrixNext : xiShiftedMomentHankelMatrix y (d + 1) =
        HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment y k).re) (d + 1) := by
      ext i j
      rfl
    have hHnext : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (d + 1)).PosDef := by
      rw [← hmatrixNext]
      simpa only [d] using hface.1
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hHd]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hHnext) (by omega)
  have hlowerPos : 0 < lower y := by
    dsimp only [lower]
    exact mul_pos (mul_pos (by positivity) hnormPos)
      (div_pos hnormPos hprevPos)
  have hlowerCont : ContinuousAt lower y := by
    exact ((continuousAt_const.mul hnormCont).mul
      (hnormCont.div hprevCont (ne_of_gt hprevPos)))
  have hle : lower y ≤ source y := by
    have hsourceLim : Tendsto source (nhdsWithin y (Ioi y)) (nhds (source y)) :=
      hsourceCont.mono_left nhdsWithin_le_nhds
    have hlowerLim : Tendsto lower (nhdsWithin y (Ioi y)) (nhds (lower y)) :=
      hlowerCont.mono_left nhdsWithin_le_nhds
    have hdiff := hsourceLim.sub hlowerLim
    have hevent : ∀ᶠ v in nhdsWithin y (Ioi y), 0 ≤ source v - lower v := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv0 : 0 ≤ v := (hy.trans hv).le
      have hH : (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment v k).re) (d + 2)).PosDef := by
        simpa only [d, y] using
          (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
            (n := n + 1) hv0 hv)
      have hbound :=
        succ_mul_admissionNorm_mul_prevNormRatio_lt_adaptiveShear
          (n := d) (by omega) hH
      dsimp only [source, lower]
      linarith
    have hzero : 0 ≤ source y - lower y := ge_of_tendsto hdiff hevent
    linarith
  dsimp only [source] at hle
  exact lt_of_lt_of_le hlowerPos hle

/-- The strict-frontier wall dominates an explicit positive multiple of the reciprocal distance.
The coefficient uses only the actual boundary source and the global integral-Lipschitz weight of
the frozen terminal null flag. -/
theorem eventually_strictFrontier_reciprocal_le_christoffelSourceWall
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    let source0 := xiShiftedCanonicalAdmissionAdaptiveShear y (n + 1)
    let c := HTGeometry.monicMomentAdmissionVector
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)
    ∀ᶠ v in 𝓝[>] y,
      (source0 /
          (32 * (xiShiftedMomentHankelQuadraticLipschitzWeight c + 1))) *
          (v - y)⁻¹ ≤
        xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let source : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionAdaptiveShear v (n + 1)
  let source0 := source y
  let c := HTGeometry.monicMomentAdmissionVector
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)
  let W := xiShiftedMomentHankelQuadraticLipschitzWeight c
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  have hsource0 : 0 < source0 := by
    simpa only [source0, source, y] using
      xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hsourceCont : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy (n + 1) (ne_of_gt hhead.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using h
  have hsourceLower : ∀ᶠ v in 𝓝 y, source0 / 2 < source v := by
    exact continuousAt_const.eventually_lt hsourceCont (by linarith)
  have hW : 0 ≤ W := by
    exact xiShiftedMomentHankelQuadraticLipschitzWeight_nonneg c
  filter_upwards [hsourceLower.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with v hsourcev hv
  have hv0 : 0 ≤ v := (hy.trans hv).le
  have hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment v k).re) (n + 3)).PosDef := by
    simpa only [y, Nat.add_assoc] using
      (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
        (n := n + 1) hv0 hv)
  have hnextPos : 0 < xiShiftedCanonicalAdmissionNorm v (n + 2) := by
    have hnextHead : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (n + 2)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hH
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hnextHead]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
  have hcollapse : xiShiftedCanonicalAdmissionNorm v (n + 2) ≤
      W * (v - y) := by
    simpa only [W, c, y] using
      (xiShiftedCanonicalAdmissionNorm_le_lipschitzWeight_mul_sub_at_strict_frontier
        hne hstrict hv)
  have hdelta : 0 < v - y := sub_pos.mpr hv
  have hL : 0 < W + 1 := by linarith
  have hcollapse' : xiShiftedCanonicalAdmissionNorm v (n + 2) ≤
      (W + 1) * (v - y) := by
    nlinarith
  have hK : 0 < source0 / (32 * (W + 1)) := by positivity
  rw [xiShiftedCanonicalAdmissionChristoffelSourceWall]
  apply (le_div_iff₀ (mul_pos (by norm_num) hnextPos)).2
  calc
    source0 / (32 * (W + 1)) * (v - y)⁻¹ *
          (16 * xiShiftedCanonicalAdmissionNorm v (n + 2)) ≤
        source0 / (32 * (W + 1)) * (v - y)⁻¹ *
          (16 * ((W + 1) * (v - y))) := by
      gcongr
    _ = source0 / 2 := by
      field_simp [ne_of_gt hdelta, ne_of_gt hL]
      all_goals ring
    _ ≤ source v := hsourcev.le

/-- Reciprocal distance is asymptotically bounded by the actual adaptive Christoffel source wall
on the positive side of every occupied strict frontier. -/
theorem strictFrontier_sub_inv_isBigO_christoffelSourceWall
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    (fun v => (v - y)⁻¹) =O[𝓝[>] y]
      (fun v => xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let source0 := xiShiftedCanonicalAdmissionAdaptiveShear y (n + 1)
  let c := HTGeometry.monicMomentAdmissionVector
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)
  let K := source0 /
    (32 * (xiShiftedMomentHankelQuadraticLipschitzWeight c + 1))
  have hsource0 : 0 < source0 := by
    simpa only [source0, y] using
      xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  have hW : 0 ≤ xiShiftedMomentHankelQuadraticLipschitzWeight c :=
    xiShiftedMomentHankelQuadraticLipschitzWeight_nonneg c
  have hK : 0 < K := by dsimp only [K]; positivity
  have hevent :=
    eventually_strictFrontier_reciprocal_le_christoffelSourceWall hne hstrict
  dsimp only at hevent
  rw [Asymptotics.isBigO_iff'']
  refine ⟨K, hK, ?_⟩
  filter_upwards [hevent, self_mem_nhdsWithin] with v hvwall hv
  have hinv : 0 < (v - y)⁻¹ := inv_pos.mpr (sub_pos.mpr hv)
  have hwall : 0 < xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1) :=
    lt_of_lt_of_le (mul_pos hK hinv) (by simpa only [K, source0, c, y] using hvwall)
  simpa only [Real.norm_eq_abs, abs_of_pos hinv, abs_of_pos hwall, K, source0, c, y]
    using hvwall

/-- **Infinite local action at a strict frontier.**  The actual adaptive source wall is not
Bochner-integrable on any nontrivial interval starting at an occupied strict frontier. -/
theorem not_intervalIntegrable_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    {b : ℝ} (hb : xiShiftedHigherBlockTerminalFrontier (n + 1) < b) :
    ¬IntervalIntegrable
      (fun v => xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1))
      MeasureTheory.volume (xiShiftedHigherBlockTerminalFrontier (n + 1)) b := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let wall : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1)
  have hbig : (fun v => (v - y)⁻¹) =O[𝓝[>] y] wall := by
    simpa only [wall, y] using
      strictFrontier_sub_inv_isBigO_christoffelSourceWall hne hstrict
  have hderiv : ∀ᶠ v in 𝓝[>] y,
      HasDerivAt (fun z => Real.log (z - y)) (v - y)⁻¹ v := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    simpa only [id_eq, one_div] using
      ((hasDerivAt_id v).sub_const y).log (sub_ne_zero.mpr hv.ne')
  have hsubN : Tendsto (fun v => v - y) (𝓝 y) (𝓝 0) := by
    have h : Tendsto (fun v => v - y) (𝓝 y) (𝓝 (y - y)) :=
      ((hasDerivAt_id y).sub_const y).continuousAt
    simpa using h
  have hsub : Tendsto (fun v => v - y) (𝓝[>] y) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsubN.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    change 0 < v - y
    exact sub_pos.mpr hv
  have hlog : Tendsto (fun v => ‖Real.log (v - y)‖) (𝓝[>] y) atTop := by
    rw [show (fun v => ‖Real.log (v - y)‖) =
        abs ∘ Real.log ∘ (fun v => v - y) by
      funext v
      simp only [Function.comp_apply, Real.norm_eq_abs]]
    exact tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsub)
  have hderivBig : deriv (fun z => Real.log (z - y)) =O[𝓝[>] y] wall :=
    hbig.congr' (hderiv.mono fun v hv => hv.deriv.symm) EventuallyEq.rfl
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
  simpa only [wall, y] using
    (not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
      (𝓝[>] y) (Ioc_mem_nhdsGT hb)
        (hderiv.mono fun v hv => hv.differentiableAt) hlog hderivBig)

/-- **Strict-frontier Christoffel source wall.**  Approaching every occupied strict terminal
frontier from its positive chamber, preceding actual adaptive source divided by next admitted norm
tends to `+∞`. -/
theorem tendsto_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    Tendsto
      (fun y => xiShiftedCanonicalAdmissionChristoffelSourceWall y (n + 1))
      (nhdsWithin (xiShiftedHigherBlockTerminalFrontier (n + 1))
        (Ioi (xiShiftedHigherBlockTerminalFrontier (n + 1)))) atTop := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let d := n + 1
  let source : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionAdaptiveShear v d
  let nextNorm : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (d + 1)
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hsourcePos : 0 < source y := by
    simpa only [source, d, y] using
      xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  have hdH : (xiShiftedMomentHankelMatrix y d).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hsourceCont : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy d (ne_of_gt hdH.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using h
  have hnextCont : ContinuousAt nextNorm y := by
    have hdet : (xiShiftedMomentHankelMatrix y (d + 1)).det ≠ 0 := by
      simpa only [d] using ne_of_gt hface.1.det_pos
    exact continuousAt_xiShiftedCanonicalAdmissionNorm_of_det hy (d + 1) hdet
  have hnextZero : nextNorm y = 0 := by
    simpa only [nextNorm, d, y, Nat.add_assoc] using
      xiShiftedCanonicalAdmissionNorm_eq_zero_at_strict_frontier hne hstrict
  have hnextTendsto : Tendsto nextNorm (nhdsWithin y (Ioi y)) (nhds 0) := by
    simpa only [hnextZero] using hnextCont.mono_left nhdsWithin_le_nhds
  have hnextPos : ∀ᶠ v in nhdsWithin y (Ioi y), nextNorm v ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv0 : 0 ≤ v := (hy.trans hv).le
    have hH : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (d + 2)).PosDef := by
      simpa only [d, y] using
        (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
          (n := n + 1) hv0 hv)
    dsimp only [nextNorm]
    have hhead : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (d + 1)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hH
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hhead]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
  have hnextWithin : Tendsto nextNorm (nhdsWithin y (Ioi y))
      (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      nextNorm hnextTendsto hnextPos
  have hinv : Tendsto (fun v => (16 * nextNorm v)⁻¹)
      (nhdsWithin y (Ioi y)) atTop := by
    have hscaled : Tendsto (fun v => 16 * nextNorm v)
        (nhdsWithin y (Ioi y)) (nhdsWithin 0 (Ioi 0)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using (tendsto_const_nhds.mul hnextTendsto)
      · filter_upwards [hnextPos] with v hv
        change 0 < 16 * nextNorm v
        exact mul_pos (by norm_num) hv
    exact tendsto_inv_nhdsGT_zero.comp hscaled
  have hsourceTendsto : Tendsto source (nhdsWithin y (Ioi y)) (nhds (source y)) :=
    hsourceCont.mono_left nhdsWithin_le_nhds
  have hwall := Filter.Tendsto.pos_mul_atTop hsourcePos hsourceTendsto hinv
  simpa only [xiShiftedCanonicalAdmissionChristoffelSourceWall, source, nextNorm,
    d, y, div_eq_mul_inv] using hwall

/-- The wall numerator is exactly the literal rational--Gamma minus von Mangoldt adaptive
completed aggregate at square mass. -/
theorem two_mul_xiShiftedCanonicalAdmissionChristoffelSourceWall_eq_arithmeticSource_div_nextNorm
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    2 * xiShiftedCanonicalAdmissionChristoffelSourceWall (w ^ (2 : ℕ)) n =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) /
        (16 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1)) := by
  have hsource := two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)
  rw [xiShiftedCanonicalAdmissionChristoffelSourceWall]
  rw [← hsource]
  change 2 *
      (xiShiftedCanonicalAdmissionAdaptiveShear (w ^ (2 : ℕ)) n /
        (16 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1))) =
    (2 * xiShiftedCanonicalAdmissionAdaptiveShear (w ^ (2 : ℕ)) n) /
      (16 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1))
  ring

/-- False-RH phase expressed entirely by cofinal actual-frontier source walls. -/
def XiShiftedCofinalChristoffelSourceWallPhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      Tendsto
        (fun y => xiShiftedCanonicalAdmissionChristoffelSourceWall y (n + 1))
        (nhdsWithin (xiShiftedHigherBlockTerminalFrontier (n + 1))
          (Ioi (xiShiftedHigherBlockTerminalFrontier (n + 1)))) atTop

/-- False-RH phase sharpened from pointwise wall divergence to infinite local action of the actual
admission-completed arithmetic source at cofinally many strict frontiers. -/
def XiShiftedCofinalNonintegrableChristoffelSourceWallPhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      ∀ b : ℝ, xiShiftedHigherBlockTerminalFrontier (n + 1) < b →
        ¬IntervalIntegrable
          (fun v => xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1))
          MeasureTheory.volume
          (xiShiftedHigherBlockTerminalFrontier (n + 1)) b

/-- False RH forces cofinally many actual strict-frontier Christoffel source walls. -/
theorem xiShiftedCofinalChristoffelSourceWallPhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalChristoffelSourceWallPhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot A
  exact ⟨n, hne, hA, hstrict,
    tendsto_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
      hne hstrict⟩

/-- False RH forces cofinally many strict frontiers with infinite local arithmetic-source action. -/
theorem xiShiftedCofinalNonintegrableChristoffelSourceWallPhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalNonintegrableChristoffelSourceWallPhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot A
  exact ⟨n, hne, hA, hstrict, fun _b hb =>
    not_intervalIntegrable_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
      hne hstrict hb⟩

/-- RH excludes the wall phase because every positive-definite failure set is empty. -/
theorem not_xiShiftedCofinalChristoffelSourceWallPhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedCofinalChristoffelSourceWallPhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- RH excludes the infinite-local-action phase because every positive-definite failure set is
empty. -/
theorem not_xiShiftedCofinalNonintegrableChristoffelSourceWallPhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedCofinalNonintegrableChristoffelSourceWallPhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- **Closed strict-frontier source-wall phase law.**  RH is exactly absence of the cofinal phase
of one-sided infinite, admission-sensitive arithmetic source walls.  This theorem has no premises;
all source formation, frontier admission, and cofinality are internal. -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalChristoffelSourceWallPhase :
    RiemannHypothesis ↔ ¬XiShiftedCofinalChristoffelSourceWallPhase := by
  constructor
  · exact not_xiShiftedCofinalChristoffelSourceWallPhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalChristoffelSourceWallPhase_of_not_riemannHypothesis hnotRH)

/-- Unconditional excluded-phase dichotomy in source-wall coordinates. -/
theorem riemannHypothesis_or_xiShiftedCofinalChristoffelSourceWallPhase :
    RiemannHypothesis ∨ XiShiftedCofinalChristoffelSourceWallPhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (xiShiftedCofinalChristoffelSourceWallPhase_of_not_riemannHypothesis hRH)

/-- **Closed infinite-action source-wall phase law.**  RH is exactly absence of cofinally many
locally non-integrable, admission-completed adaptive arithmetic source walls.  No premises or
external schedules remain. -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalNonintegrableChristoffelSourceWallPhase :
    RiemannHypothesis ↔
      ¬XiShiftedCofinalNonintegrableChristoffelSourceWallPhase := by
  constructor
  · exact
      not_xiShiftedCofinalNonintegrableChristoffelSourceWallPhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalNonintegrableChristoffelSourceWallPhase_of_not_riemannHypothesis
        hnotRH)

/-- Unconditional dichotomy in infinite-local-action arithmetic-source coordinates. -/
theorem riemannHypothesis_or_xiShiftedCofinalNonintegrableChristoffelSourceWallPhase :
    RiemannHypothesis ∨
      XiShiftedCofinalNonintegrableChristoffelSourceWallPhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (xiShiftedCofinalNonintegrableChristoffelSourceWallPhase_of_not_riemannHypothesis
        hRH)

end

end RHTower
