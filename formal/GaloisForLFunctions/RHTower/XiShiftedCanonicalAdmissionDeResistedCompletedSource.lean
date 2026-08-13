import GaloisForLFunctions.HTGeometry.GaussTerminalSourceLogDerivative
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalSourceWeylRenewal

/-!
# De-resisted shifted-Xi completed source

Terminal Weyl renewal has finite probability mass, but a selected resistance share may vanish.
The already-formed current/adjacent mixed `P^sharp` source supplies exact reciprocal inertia.
Multiplying resistance by the literal Padé-residue/completed-capacity product and dividing by hard
forcing leaves coefficient one at every nonzero current node.

Thus de-resisted source is faithful: no current node can hide through probability escape.  Its
total capital is exactly degree and increases by one at each renewal.  This also proves sharp
limitation: faithful raw source has linearly extensive vacuum, so it cannot itself be a finite
all-degree budget.  Apex centering or a signed arithmetic coboundary remains necessary.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Source-first de-resistance coefficient.  Literal completed source is formed before this
normalization. -/
def xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance w n x *
      (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
        xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
          w n x) /
    (w ^ 2 * x ^ 4 *
      HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n - 1))

/-- **Pointwise faithful-source law.**  Every nonzero admitted node carries exactly one unit after
completed source cancels endogenous resistance. -/
theorem xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient_eq_one
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ} (hx : x ≠ 0)
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient w n x = 1 := by
  have hproduct :=
    xiShiftedCanonicalAdmissionTerminalSourceResistance_mul_residue_mul_vacuumFreeCapacity_eq
      hn hH hx hroot
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : HTGeometry.monicOrthoNormSq
      (xiShiftedRealMomentSequence w) (n - 1) ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega))
  have hrhs : w ^ 2 * x ^ 4 *
      HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hw) (pow_ne_zero 4 hx)) hnorm
  rw [xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient]
  rw [hproduct]
  exact div_self hrhs

/-- **Faithful-source degree law.**  Total de-resisted completed source equals number of admitted
nodes, hence exactly current degree. -/
theorem sum_xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient_eq_degree
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) :
    ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
        xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient w n x = n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one] at hnodes ⊢
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  calc
    ∑ x ∈ HTGeometry.gaussNodes s m,
        xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient w (m + 1) x =
        ∑ x ∈ HTGeometry.gaussNodes s m, 1 := by
      apply Finset.sum_congr rfl
      intro x hxmem
      apply xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient_eq_one
        (by omega) hw hH (hnodes x hxmem)
      rw [hP]
      exact (HTGeometry.mem_gaussNodes_iff m x).mp hxmem
    _ = ((m + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [HTGeometry.gaussNodes_card_below hbelow m (by omega)]

/-- Faithful Poisson localization of literal de-resisted completed source. -/
def xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate
    (w : ℝ) (n : ℕ) (a eta : ℝ) : ℝ :=
  ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
    xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient w n x * eta /
      ((a - x) ^ 2 + eta ^ 2)

/-- De-resisted completed source is exactly unweighted nodal Poisson density. -/
theorem xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate_eq_unweighted
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) (a eta : ℝ) :
    xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate w n a eta =
      ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
        eta / ((a - x) ^ 2 + eta ^ 2) := by
  rw [xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate]
  apply Finset.sum_congr rfl
  intro x hxmem
  have hP : HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n =
        HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n := by
    change HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n =
        HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n
    exact xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0 := by
    rw [hP]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa only [Nat.succ_sub_one] using (HTGeometry.mem_gaussNodes_iff m x).mp hxmem
  rw [xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient_eq_one
    hn hw hH (hnodes x hxmem) hroot, one_mul]

/-- **Literal source/log-derivative landing.**  Faithful Poisson localization of already-formed
completed source is the negative imaginary logarithmic derivative of current canonical admission. -/
theorem xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate_eq_neg_im_logDerivative
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) (a : ℝ) {eta : ℝ}
    (heta : eta ≠ 0) :
    xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate w n a eta =
      -(Polynomial.aeval (a + eta * I)
          (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n).derivative /
        HTGeometry.monicOrthoC (xiShiftedRealMomentSequence w) n (a + eta * I)).im := by
  rw [xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate_eq_unweighted
    hn hw hH hnodes a eta]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  change HTGeometry.gaussUnitPolePoissonDensity
    (xiShiftedRealMomentSequence w) m a eta = _
  rw [← HTGeometry.neg_im_gaussUnitPoleTransformComplex_eq_poissonDensity]
  rw [HTGeometry.gaussUnitPoleTransformComplex_eq_logDerivative hbelow (m := m)
    (by omega) (by simpa using heta)]

/-- Faithful completed-source Poisson aggregate is strictly positive at every positive aperture. -/
theorem xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate_pos
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) (a : ℝ) {eta : ℝ}
    (heta : 0 < eta) :
    0 < xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate w n a eta := by
  rw [xiShiftedCanonicalAdmissionDeResistedCompletedSourcePoissonAggregate_eq_unweighted
    hn hw hH hnodes a eta]
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hcard : (HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1)).card = n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa only [Nat.succ_sub_one] using HTGeometry.gaussNodes_card_below hbelow m (by omega)
  have hnonempty : (HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty] at hcard
    omega
  exact Finset.sum_pos (fun x hx => div_pos heta (add_pos_of_nonneg_of_pos
    (sq_nonneg (a - x)) (sq_pos_of_pos heta))) hnonempty

/-- **One-unit renewal and raw-budget no-go.**  Every strict degree increase adds exactly one
faithful completed-source atom.  Consequently raw de-resisted source cannot have finite total
capital along an unbounded degree tower. -/
theorem sub_sum_deResistedCompletedSourceCoefficient_eq_one
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef)
    (hnodesCurrent : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0)
    (hnodesNext : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) n, x ≠ 0) :
    (∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) n,
        xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient w (n + 1) x) -
      ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
        xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient w n x = 1 := by
  have hHcurrent : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 2)).PosDef
    exact xiShiftedMomentHankel_posDef_of_le (m := n + 2) (by omega) hH
  have hnext :=
    sum_xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient_eq_degree
      (n := n + 1) (by omega) hw hH (by
        simpa only [show n + 1 - 1 = n by omega] using hnodesNext)
  have hcurrent :=
    sum_xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient_eq_degree
      hn hw hHcurrent hnodesCurrent
  have hnext' :
      (∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) n,
        xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient w (n + 1) x) =
          (n + 1 : ℕ) := by
    simpa only [show n + 1 - 1 = n by omega] using hnext
  rw [hnext', hcurrent]
  push_cast
  ring

end

end RHTower
