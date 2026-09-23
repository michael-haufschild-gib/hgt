import GaloisForLFunctions.HTGeometry.GaussApexCenteredSourceLogDerivative
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDeResistedCompletedSource

/-!
# Shifted-Xi apex-centered completed-source landing

The literal current/adjacent Padé-residue/completed-`P^sharp` product is first de-resisted, leaving
one faithful unit at each admitted node.  The moving-apex factor `(w^(2 : ℕ)*x)^(2 : ℕ) - 1` is then applied
before aggregation.  The resulting signed source lands exactly in the current admission
logarithmic derivative plus intrinsic degree and first-trace counterterms.

This is an adaptive arithmetic producer.  It is neither a fixed linear reporter nor an orientation
map applied after reflection aggregation.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Literal completed-source coefficient after de-resistance and moving-apex centering. -/
def xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient w n x *
    ((w ^ (2 : ℕ) * x) ^ (2 : ℕ) - 1)

/-- **Pointwise source-first centered law.**  Actual completed source cancels resistance before
moving-apex centering, leaving exactly the signed hard residue. -/
theorem xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue_eq
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ} (hx : x ≠ 0)
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w n x =
      (w ^ (2 : ℕ) * x) ^ (2 : ℕ) - 1 := by
  rw [xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue,
    xiShiftedCanonicalAdmissionDeResistedCompletedSourceCoefficient_eq_one
      hn hw hH hx hroot, one_mul]

/-- On every positive current node, positive literal centered completed source is exactly the
super-apex condition. -/
theorem xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue_pos_iff
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ} (hx : 0 < x)
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0) :
    0 < xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w n x ↔
      1 < w ^ (2 : ℕ) * x := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans (by norm_num) hw)
  rw [xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue_eq
    hn hw0 hH hx.ne' hroot]
  exact HTGeometry.gaussApexCenteredResidue_pos_iff
    (sq_pos_of_pos (lt_trans (by norm_num) hw)) hx

/-- Cauchy aggregate of literal completed-source residues after source-first de-resistance and
moving-apex centering. -/
def xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceTransform
    (w : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
    (xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w n x : ℂ) /
      (z - (x : ℂ))

/-- Literal centered completed-source transform equals the generic faithful moving-apex carrier. -/
theorem xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceTransform_eq_gauss
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) (z : ℂ) :
    xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceTransform w n z =
      HTGeometry.gaussApexCenteredUnitPoleTransformComplex
        (xiShiftedRealMomentSequence w) (n - 1) (w ^ (2 : ℕ)) z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one] at hnodes ⊢
  let s := xiShiftedRealMomentSequence w
  have hP : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  rw [xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceTransform,
    HTGeometry.gaussApexCenteredUnitPoleTransformComplex]
  simp only [Nat.succ_sub_one]
  apply Finset.sum_congr rfl
  intro x hxmem
  have hroot : (HTGeometry.monicMomentAdmissionPolynomial s (m + 1)).eval x = 0 := by
    rw [hP]
    exact (HTGeometry.mem_gaussNodes_iff m x).mp hxmem
  rw [xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue_eq
    (by omega) hw hH (hnodes x hxmem) hroot]

/-- **Adaptive mixed-amplitude/completed-source aggregate law.**  The literal source-first signed
carrier lands in current admission logarithmic derivative after exact endogenous degree and
first-trace vacuum subtraction. -/
theorem xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceTransform_eq_logDerivative
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) {z : ℂ}
    (hz : z.im ≠ 0) :
    xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceTransform w n z =
      (((w ^ (2 : ℕ) : ℝ) : ℂ) ^ (2 : ℕ) * z ^ (2 : ℕ) - 1) *
          (Polynomial.aeval z
              (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n).derivative /
            HTGeometry.monicOrthoC (xiShiftedRealMomentSequence w) n z) -
        (((w ^ (2 : ℕ) : ℝ) : ℂ) ^ (2 : ℕ)) *
          (((n : ℕ) : ℂ) * z +
            (HTGeometry.gaussNodeTrace
              (xiShiftedRealMomentSequence w) (n - 1) : ℂ)) := by
  rw [xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceTransform_eq_gauss
    hn hw hH hnodes z]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  exact HTGeometry.gaussApexCenteredUnitPoleTransformComplex_eq_degree_logDerivative
    hbelow (m := m) (by omega) (w ^ (2 : ℕ)) hz

/-- **Even adaptive null-flag shear.**  Positive part is taken on each literal source-first
centered residue before Poisson aggregation.  Consequently negative sub-apex source cannot cancel
a positive super-apex atom. -/
def xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag
    (w : ℝ) (n : ℕ) (a eta : ℝ) : ℝ :=
  ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
    max 0
        (xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w n x) *
      eta / ((a - x) ^ (2 : ℕ) + eta ^ (2 : ℕ))

/-- Literal completed-source null flag equals generic admission-sensitive positive shear. -/
theorem xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag_eq_gauss
    {w : ℝ} {n : ℕ} (hn : 0 < n) (hw : w ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) (a eta : ℝ) :
    xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag w n a eta =
      HTGeometry.gaussSuperApexNullFlagPoissonSource
        (xiShiftedRealMomentSequence w) (n - 1) (w ^ (2 : ℕ)) a eta := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one] at hnodes ⊢
  let s := xiShiftedRealMomentSequence w
  have hP : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  rw [xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag,
    HTGeometry.gaussSuperApexNullFlagPoissonSource]
  simp only [Nat.succ_sub_one]
  apply Finset.sum_congr rfl
  intro x hxmem
  have hroot : (HTGeometry.monicMomentAdmissionPolynomial s (m + 1)).eval x = 0 := by
    rw [hP]
    exact (HTGeometry.mem_gaussNodes_iff m x).mp hxmem
  rw [xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue_eq
    (by omega) hw hH (hnodes x hxmem) hroot]

/-- **Exact super-apex detection by source-first null flag.**  If current admitted nodes are
positive, the adaptive completed-source shear is positive exactly when current admission contains
a super-apex node. -/
theorem xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag_pos_iff
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), 0 < x)
    (a : ℝ) {eta : ℝ} (heta : 0 < eta) :
    0 < xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag w n a eta ↔
      ∃ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
        1 < w ^ (2 : ℕ) * x := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans (by norm_num) hw)
  rw [xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag_eq_gauss
      hn hw0 hH (fun x hxmem => (hnodes x hxmem).ne') a eta,
    HTGeometry.gaussSuperApexNullFlagPoissonSource_pos_iff
      (xiShiftedRealMomentSequence w) (n - 1) (w ^ (2 : ℕ)) a heta]
  constructor
  · rintro ⟨x, hxmem, hxsource⟩
    exact ⟨x, hxmem,
      (HTGeometry.gaussApexCenteredResidue_pos_iff
        (sq_pos_of_pos (lt_trans (by norm_num) hw)) (hnodes x hxmem)).mp hxsource⟩
  · rintro ⟨x, hxmem, hxapex⟩
    exact ⟨x, hxmem,
      (HTGeometry.gaussApexCenteredResidue_pos_iff
        (sq_pos_of_pos (lt_trans (by norm_num) hw)) (hnodes x hxmem)).mpr hxapex⟩

end

end RHTower
