import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCenteredCompletedSourceLogDerivative
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveGaussRootRenewal

/-!
# Completed arithmetic source as faithful nodal Jacobi history

The coefficient-level degree-centered rational--Gamma-minus-von-Mangoldt source and the faithful
apex-centered nodal producer are not parallel constructions.  Finite Vieta/Jacobi identities
identify causal degree-centered history with current root-square energy plus current diagonal times
root trace.  Eliminating root-square energy yields a division-free balance between literal
completed arithmetic source and total moving-apex nodal residue.
-/

open Matrix Polynomial
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- **Nodal realization of causal degree-centered history.** -/
theorem degreeCenteredOrthoJacobiHistory_eq_gaussNodeEnergy_add_alphaTrace
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) :
    degreeCenteredOrthoJacobiHistory s n =
      (∑ x ∈ gaussNodes s (n - 1), x ^ 2) +
        monicOrthoAlpha s n * gaussNodeTrace s (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (by omega : 0 < n))
  simp only [Nat.succ_sub_one]
  have hnodup : (monicOrtho s (m + 1)).roots.Nodup :=
    monicOrtho_roots_nodup_below h hnN
  have htrace : gaussNodeTrace s m = (monicOrtho s (m + 1)).roots.sum := by
    rw [gaussNodeTrace, gaussNodes, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup]
    simp
  have henergy : (∑ x ∈ gaussNodes s m, x ^ 2) =
      ((monicOrtho s (m + 1)).roots.map fun x => x ^ 2).sum := by
    rw [gaussNodes, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup]
  have hrootsum := monicOrtho_roots_sum_eq_sum_alpha_below
    h (n := m + 1) (by omega) hnN
  have hrootsq := monicOrtho_roots_sum_sq_eq_jacobiEnergy_below
    h (n := m + 1) (by omega) hnN
  rw [degreeCenteredOrthoJacobiHistory, htrace, henergy, hrootsum, hrootsq]
  ring

end

end HTGeometry

namespace RHTower

noncomputable section

/-- **Literal completed arithmetic source/root-history law.**  Degree-centered
rational--Gamma-minus-von-Mangoldt formation equals twice current norm times faithful nodal
quadratic history. -/
theorem xiShiftedCanonicalAdmissionDegreeCenteredCompletedArithmeticSource_eq_nodalHistory
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedDegreeCenteredCompletedArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) =
      2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
        ((∑ x ∈ HTGeometry.gaussNodes
            (xiShiftedRealMomentSequence w) (n - 1), x ^ 2) +
          HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n *
            HTGeometry.gaussNodeTrace (xiShiftedRealMomentSequence w) (n - 1)) := by
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional hw,
    hP, xiShiftedBoundaryDegreeCenteredShearPolynomial_monicOrtho,
    HTGeometry.momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory_below
      hbelow (by omega) (by omega),
    HTGeometry.degreeCenteredOrthoJacobiHistory_eq_gaussNodeEnergy_add_alphaTrace
      hbelow hn (by omega)]
  ring

/-- **Division-free completed-source/nodal balance.**  Literal arithmetic source, total faithful
moving-apex residue, degree vacuum, and diagonal/root-trace coupling are one exact account. -/
theorem massSq_mul_degreeCenteredCompletedArithmeticSource_eq_centeredResidueBalance
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    (w ^ 2) ^ 2 *
        xiShiftedDegreeCenteredCompletedArithmeticSource w n
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) =
      2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
        (HTGeometry.gaussApexCenteredResidueTotal
            (xiShiftedRealMomentSequence w) (n - 1) (w ^ 2) +
          (n : ℝ) +
          (w ^ 2) ^ 2 *
            HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n *
              HTGeometry.gaussNodeTrace
                (xiShiftedRealMomentSequence w) (n - 1)) := by
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedCanonicalAdmissionDegreeCenteredCompletedArithmeticSource_eq_nodalHistory
    hw hn hH, HTGeometry.gaussApexCenteredResidueTotal_eq,
    HTGeometry.gaussNodes_card_below hbelow (n - 1) (by omega)]
  norm_num [show n - 1 + 1 = n by omega]
  ring

/-- Quotient form: total centered faithful residue is recovered exactly from literal completed
arithmetic source after the endogenous degree and diagonal/trace counterterms. -/
theorem gaussApexCenteredResidueTotal_eq_completedArithmeticSource
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    HTGeometry.gaussApexCenteredResidueTotal
        (xiShiftedRealMomentSequence w) (n - 1) (w ^ 2) =
      (w ^ 2) ^ 2 *
          xiShiftedDegreeCenteredCompletedArithmeticSource w n
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n) /
        (2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n) -
      (n : ℝ) -
      (w ^ 2) ^ 2 * HTGeometry.monicOrthoAlpha
          (xiShiftedRealMomentSequence w) n *
        HTGeometry.gaussNodeTrace (xiShiftedRealMomentSequence w) (n - 1) := by
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : HTGeometry.monicOrthoNormSq
      (xiShiftedRealMomentSequence w) n ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega))
  have hbalance :=
    massSq_mul_degreeCenteredCompletedArithmeticSource_eq_centeredResidueBalance
      hw hn hH
  have hden : 2 * HTGeometry.monicOrthoNormSq
      (xiShiftedRealMomentSequence w) n ≠ 0 := mul_ne_zero (by norm_num) hnorm
  have hquot :
      (w ^ 2) ^ 2 *
          xiShiftedDegreeCenteredCompletedArithmeticSource w n
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n) /
        (2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n) =
      HTGeometry.gaussApexCenteredResidueTotal
          (xiShiftedRealMomentSequence w) (n - 1) (w ^ 2) +
        (n : ℝ) +
        (w ^ 2) ^ 2 * HTGeometry.monicOrthoAlpha
            (xiShiftedRealMomentSequence w) n *
          HTGeometry.gaussNodeTrace (xiShiftedRealMomentSequence w) (n - 1) := by
    apply (div_eq_iff hden).2
    simpa only [mul_comm] using hbalance
  rw [hquot]
  ring

end

end RHTower
