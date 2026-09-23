import GaloisForLFunctions.HTGeometry.GaussTerminalWeylRenewal
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalSourceResistance

/-!
# Shifted-Xi completed terminal-source Weyl renewal

The current/adjacent vacuum-free mixed `P^sharp` producer is formed before aggregation.  At every
nonzero hard node, its actual Padé-residue times completed transverse capacity recovers the
terminal spectral atom by nonlinear reciprocal normalization.  The Cauchy aggregate of these
atoms is the adjacent admission ratio and obeys exact Jacobi coefficient stripping across degree.

Its anti-Herglotz continuation has a stronger local capital account: after undoing current
Riccati transmission and preceding-edge transport, every degree renewal injects exactly the
positive aperture height.  This is admission-sensitive source renewal, not a fixed linear
reporter or a post-aggregation orientation map.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Nonlinear Cauchy aggregate formed from actual current/adjacent Padé-residue/completed-capacity
products.  Source formation precedes reciprocal normalization and nodal aggregation. -/
def xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate
    (w : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
    ((w ^ (2 : ℕ) * x ^ (4 : ℕ) *
        HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n - 1)) /
      (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
        xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
          w n x)) / (z - x)

/-- Literal completed-source atoms are exactly terminal-resistance atoms. -/
theorem xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate_eq_terminalWeyl
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) (z : ℝ) :
    xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate w n z =
      HTGeometry.gaussTerminalWeylTransform
        (xiShiftedRealMomentSequence w) (n - 1) z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one] at hnodes ⊢
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  rw [xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate,
    HTGeometry.gaussTerminalWeylTransform]
  simp only [Nat.succ_sub_one]
  apply Finset.sum_congr rfl
  intro x hx
  have hx0 : x ≠ 0 := hnodes x hx
  have hrootOrtho : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 :=
    (HTGeometry.mem_gaussNodes_iff m x).mp hx
  have hrootAdmission :
      (HTGeometry.monicMomentAdmissionPolynomial s (m + 1)).eval x = 0 := by
    rw [hP]
    exact hrootOrtho
  have hproduct :=
    xiShiftedCanonicalAdmissionTerminalSourceResistance_mul_residue_mul_vacuumFreeCapacity_eq
      (w := w) (n := m + 1) (by omega) hH hx0 hrootAdmission
  have hnorm : HTGeometry.monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega))
  have hrhs : w ^ (2 : ℕ) * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hw) (pow_ne_zero 4 hx0)) hnorm
  have hsource :
      xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w (m + 1) x *
          xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
            w (m + 1) x ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hproduct
    exact hrhs hproduct.symm
  have hratio :
      (w ^ (2 : ℕ) * x ^ (4 : ℕ) * HTGeometry.monicOrthoNormSq s m) /
          (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w (m + 1) x *
            xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
              w (m + 1) x) =
        HTGeometry.gaussTerminalSourceResistance s m x := by
    apply (div_eq_iff hsource).2
    simpa only [xiShiftedCanonicalAdmissionHardEdgeTerminalSourceResistance,
      Nat.succ_sub_one, s, mul_comm] using hproduct.symm
  rw [hratio]

/-- **Completed-source Weyl identity.**  The literal nonlinear aggregate is the preceding/current
canonical-admission ratio. -/
theorem xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate_eq_ratio
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) {z : ℝ}
    (hz : (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n).eval z ≠ 0) :
    xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate w n z =
      (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) (n - 1)).eval z /
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n).eval z := by
  rw [xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate_eq_terminalWeyl
    hn hw hH hnodes z]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  simpa only [Nat.succ_sub_one] using
    HTGeometry.gaussTerminalWeylTransform_eq_ratio hbelow (m := m) (by omega) hz

/-- **Literal nonlinear degree renewal.**  Actual mixed/completed source aggregate survives the
changing admission by Jacobi coefficient stripping. -/
theorem xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate_renewal
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef)
    (hnodesCurrent : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0)
    (hnodesNext : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) n, x ≠ 0) {z : ℝ}
    (hzCurrent : (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n).eval z ≠ 0)
    (hzNext : (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) (n + 1)).eval z ≠ 0) :
    xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate w (n + 1) z =
      1 / (z - HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n -
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
          xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate w n z) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let s := xiShiftedRealMomentSequence w
  have hHcurrent :
      (HTGeometry.momentHankelMatrix s (m + 1 + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  rw [xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate_eq_terminalWeyl
      (by omega : 0 < m + 2) hw (by simpa only [s] using hH)
      (by simpa only [s, show m + 2 - 1 = m + 1 by omega] using hnodesNext) z,
    xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate_eq_terminalWeyl
      (by omega : 0 < m + 1) hw (by simpa only [s] using hHcurrent)
      (by simpa only [s] using hnodesCurrent) z]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  simpa only [Nat.succ_sub_one, s] using
    HTGeometry.gaussTerminalWeylTransform_renewal hbelow (m := m) (by omega)
      hzCurrent hzNext

/-- Anti-Herglotz continuation of the actual completed-source aggregate. -/
def xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex
    (w : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  HTGeometry.gaussTerminalWeylTransformComplex
    (xiShiftedRealMomentSequence w) (n - 1) z

/-- Real boundary value of complex source continuation is the literal completed-source aggregate. -/
theorem xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex_ofReal
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) {z : ℝ}
    (hz : (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n).eval z ≠ 0) :
    xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w n z =
      (xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate w n z : ℂ) := by
  rw [xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex,
    xiShiftedCanonicalAdmissionCompletedSourceWeylAggregate_eq_terminalWeyl
      hn hw hH hnodes z]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  simpa only [Nat.succ_sub_one] using
    HTGeometry.gaussTerminalWeylTransformComplex_ofReal hbelow (m := m) (by omega) hz

/-- Complex source continuation is strictly anti-Herglotz on every positive admitted block. -/
theorem neg_im_xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex_pos
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) {z : ℂ}
    (hz : 0 < z.im) :
    0 < -(xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w n z).im := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  simpa only [xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex,
    Nat.succ_sub_one] using
    HTGeometry.neg_im_gaussTerminalWeylTransformComplex_pos hbelow (m := m) (by omega) hz

/-- **Exact arithmetic source increment across degree.**  Once current nonlinear transmission and
the newborn Jacobi edge are accounted for, source capital added at every renewal is exactly the
upper-half-plane aperture height. -/
theorem xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex_normalized_increment
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) {z : ℂ}
    (hz : 0 < z.im) :
    -(xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w (n + 1) z).im /
          Complex.normSq
            (xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w (n + 1) z) -
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
          (-(xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w n z).im) = z.im := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  simpa only [xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex,
    Nat.succ_sub_one] using
    HTGeometry.gaussTerminalWeylTransformComplex_normalized_source_increment
      hbelow (m := m) (by omega) hz

end

end RHTower
