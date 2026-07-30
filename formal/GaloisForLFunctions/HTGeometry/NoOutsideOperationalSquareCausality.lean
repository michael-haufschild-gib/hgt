import GaloisForLFunctions.HTGeometry.CausalRayPolarityNonselection
import GaloisForLFunctions.HTGeometry.ColorGramMinkowskiOrbit
import GaloisForLFunctions.HTGeometry.EventSquarePolarization
import GaloisForLFunctions.HTGeometry.TriangleSourceHermitianLift
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef

/-!
# No-outside operational square--causality law

This file closes the finite operational bridge left after the triangle source has generated the
complex `3 × 2` carrier and its positive Hermitian Gram record.

Independent event carriers compose by row stacking, so their public Gram records add.  For
positive two-channel records `A` and `B`, the following conditions are then equivalent:

* `B - A` is positive semidefinite;
* `B` is `A` plus another `3 × 2` event square;
* every pure two-channel quadratic witness has nondecreasing weight;
* the Pauli coordinates of `B - A` form a closed Lorentz-future vector.

The same quadratic evaluations obey exact binary Born normalization for every unit spinor and its
antilinear spin complement.

All statements are finite matrix theorems.  They do not assert that observed histories use this
record, construct continuum spacetime, or derive gravitational dynamics.
-/

open Matrix
open scoped ComplexOrder Matrix MatrixOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {m k n : Type*} [Fintype m] [Fintype k]

/-- Stack independent event matrices on the direct sum of their left carriers. -/
def eventStack (X : Matrix m n ℂ) (Y : Matrix k n ℂ) :
    Matrix (m ⊕ k) n ℂ
  | Sum.inl i, j => X i j
  | Sum.inr i, j => Y i j

/-- Independent event composition adds public Gram squares exactly. -/
theorem eventSquare_eventStack_eq_add
    (X : Matrix m n ℂ) (Y : Matrix k n ℂ) :
    eventSquare (eventStack X Y) = eventSquare X + eventSquare Y := by
  ext i j
  simp [eventSquare, eventStack, Matrix.mul_apply, Fintype.sum_sum_type]

/-- A finite positive two-channel public record. -/
abbrev TwoChannelPositiveRecord :=
  {A : Matrix (Fin 2) (Fin 2) ℂ // A.PosSemidef}

/-- Positive-record precedence: the later record differs by a positive event increment. -/
def twoRecordPrecedes (A B : TwoChannelPositiveRecord) : Prop :=
  (B.1 - A.1).PosSemidef

/-- Pure two-channel witness weight.  For a density record this is the Born quadratic form. -/
def twoRecordWitnessWeight
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (A *ᵥ ψ)).re

/-- Witness weights are additive in the public record. -/
theorem twoRecordWitnessWeight_add
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ) :
    twoRecordWitnessWeight (A + B) ψ =
      twoRecordWitnessWeight A ψ + twoRecordWitnessWeight B ψ := by
  simp [twoRecordWitnessWeight, Matrix.add_mulVec, dotProduct_add]

/-- Witness weights subtract in the public record. -/
theorem twoRecordWitnessWeight_sub
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ) :
    twoRecordWitnessWeight (A - B) ψ =
      twoRecordWitnessWeight A ψ - twoRecordWitnessWeight B ψ := by
  simp [twoRecordWitnessWeight, Matrix.sub_mulVec, dotProduct_sub]

/-- Every positive record gives nonnegative weight to every pure witness. -/
theorem twoRecordWitnessWeight_nonneg
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (ψ : Fin 2 → ℂ) :
    0 ≤ twoRecordWitnessWeight A ψ := by
  exact hA.re_dotProduct_nonneg ψ

/--
Positive-record precedence is exactly pointwise monotonicity under every pure two-channel
quadratic witness.
-/
theorem twoRecordPrecedes_iff_forall_witnessWeight_le
    (A B : TwoChannelPositiveRecord) :
    twoRecordPrecedes A B ↔
      ∀ ψ : Fin 2 → ℂ,
        twoRecordWitnessWeight A.1 ψ ≤ twoRecordWitnessWeight B.1 ψ := by
  constructor
  · intro h ψ
    have hnonneg :=
      twoRecordWitnessWeight_nonneg h ψ
    rw [twoRecordWitnessWeight_sub] at hnonneg
    linarith
  · intro h
    have hHermitian : (B.1 - A.1).IsHermitian :=
      B.2.isHermitian.sub A.2.isHermitian
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHermitian
    intro ψ
    apply Complex.nonneg_iff.mpr
    constructor
    · change 0 ≤ twoRecordWitnessWeight (B.1 - A.1) ψ
      rw [twoRecordWitnessWeight_sub]
      exact sub_nonneg.mpr (h ψ)
    · exact (hHermitian.im_star_dotProduct_mulVec_self ψ).symm

/--
A positive increment is exactly another color-event Gram square.  This turns Loewner precedence
into literal finite event addition.
-/
theorem twoRecordPrecedes_iff_exists_colorEvent_increment
    (A B : TwoChannelPositiveRecord) :
    twoRecordPrecedes A B ↔
      ∃ Y : ColorEventMatrix, B.1 = A.1 + colorGramMatrix Y := by
  constructor
  · intro h
    obtain ⟨Y, hY⟩ :=
      exists_colorEventMatrix_gram_eq (B.1 - A.1) h
    refine ⟨Y, ?_⟩
    rw [colorGramMatrix]
    rw [hY]
    abel
  · rintro ⟨Y, hY⟩
    have hdiff : B.1 - A.1 = colorGramMatrix Y := by
      rw [hY]
      abel
    rw [twoRecordPrecedes, hdiff]
    exact colorGramMatrix_posSemidef Y

/-- Closed Lorentz-future condition in real Pauli coordinates. -/
def IsLorentzFuture (t x y z : ℝ) : Prop :=
  0 ≤ t ∧ 0 ≤ t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2

/--
The positive cone of Hermitian `2 × 2` matrices is exactly the closed Lorentz future cone.

The reverse implication is proved by an explicit completed-square decomposition, including the
singular boundary where the leading diagonal entry vanishes.
-/
theorem lorentzHermitianMatrix_posSemidef_iff
    (t x y z : ℝ) :
    (lorentzHermitianMatrix t x y z).PosSemidef ↔
      IsLorentzFuture t x y z := by
  constructor
  · intro h
    have h00 := h.diag_nonneg (i := (0 : Fin 2))
    have h11 := h.diag_nonneg (i := (1 : Fin 2))
    have hdet := h.det_nonneg
    have h00re : 0 ≤ t + z := by
      exact (Complex.nonneg_iff.mp h00).1
    have h11re : 0 ≤ t - z := by
      exact (Complex.nonneg_iff.mp h11).1
    have hdetre :
        0 ≤ t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
      rw [lorentzHermitianMatrix_det] at hdet
      exact (Complex.nonneg_iff.mp hdet).1
    exact ⟨by linarith, hdetre⟩
  · rintro ⟨ht, hdet⟩
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    have hzbound : z ^ 2 ≤ t ^ 2 := by nlinarith
    have ha : 0 ≤ t + z := by nlinarith
    have hd : 0 ≤ t - z := by nlinarith
    have hHermitian := lorentzHermitianMatrix_isHermitian t x y z
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHermitian
    intro v
    apply Complex.nonneg_iff.mpr
    constructor
    · by_cases ha0 : t + z = 0
      · have hxy : x ^ 2 + y ^ 2 = 0 := by
          nlinarith
        have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
        have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
        have hv := mul_nonneg hd (Complex.normSq_nonneg (v 1))
        simp [lorentzHermitianMatrix, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, ha0, hx, hy]
        simp [Complex.normSq_apply] at hv
        nlinarith
      · have hapos : 0 < t + z := lt_of_le_of_ne ha (Ne.symm ha0)
        have hform :
            (star v ⬝ᵥ (lorentzHermitianMatrix t x y z *ᵥ v)).re =
              (t + z) *
                  Complex.normSq
                    (v 0 + (((x : ℂ) + (y : ℂ) * Complex.I) / (t + z)) * v 1) +
                ((t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) / (t + z)) *
                  Complex.normSq (v 1) := by
          simp [lorentzHermitianMatrix, Matrix.mulVec, dotProduct,
            Fin.sum_univ_succ, Complex.normSq_apply, Complex.div_re,
            Complex.div_im, Complex.mul_re, Complex.mul_im]
          field_simp [ha0]
          ring
        rw [hform]
        exact add_nonneg
          (mul_nonneg hapos.le (Complex.normSq_nonneg _))
          (mul_nonneg (div_nonneg hdet hapos.le) (Complex.normSq_nonneg _))
    · exact (hHermitian.im_star_dotProduct_mulVec_self v).symm

/-- Lorentz-coordinate form of positive-record precedence. -/
theorem twoRecordPrecedes_iff_lorentzFuture_of_difference_eq
    (A B : TwoChannelPositiveRecord) (t x y z : ℝ)
    (hcoord : B.1 - A.1 = lorentzHermitianMatrix t x y z) :
    twoRecordPrecedes A B ↔ IsLorentzFuture t x y z := by
  rw [twoRecordPrecedes, hcoord, lorentzHermitianMatrix_posSemidef_iff]

/--
Bundled finite operational lift: event addition, all pure Born-witness tests, and Lorentz-future
order are three equivalent readings of the same positive increment.
-/
theorem noOutside_operationalSquareCausality_fourWay
    (A B : TwoChannelPositiveRecord) (t x y z : ℝ)
    (hcoord : B.1 - A.1 = lorentzHermitianMatrix t x y z) :
    (twoRecordPrecedes A B ↔
        ∃ Y : ColorEventMatrix, B.1 = A.1 + colorGramMatrix Y) ∧
      (twoRecordPrecedes A B ↔
        ∀ ψ : Fin 2 → ℂ,
          twoRecordWitnessWeight A.1 ψ ≤ twoRecordWitnessWeight B.1 ψ) ∧
      (twoRecordPrecedes A B ↔ IsLorentzFuture t x y z) := by
  exact ⟨twoRecordPrecedes_iff_exists_colorEvent_increment A B,
    twoRecordPrecedes_iff_forall_witnessWeight_le A B,
    twoRecordPrecedes_iff_lorentzFuture_of_difference_eq A B t x y z hcoord⟩

/-- The source-generated triangle witness record as a positive operational record. -/
def triangleWitnessPositiveRecord
    (X : TriangleWitnessEvent) : TwoChannelPositiveRecord :=
  ⟨triangleWitnessGram X, triangleWitnessGram_posSemidef X⟩

/-- Record obtained after independently adjoining a second source-generated triangle witness. -/
def triangleWitnessPositiveRecordAfter
    (X Y : TriangleWitnessEvent) : TwoChannelPositiveRecord :=
  ⟨triangleWitnessGram X + triangleWitnessGram Y,
    (triangleWitnessGram_posSemidef X).add (triangleWitnessGram_posSemidef Y)⟩

/-- The triangle witness record is definitionally the color-event Gram record. -/
theorem triangleWitnessGram_eq_colorGramMatrix
    (X : TriangleWitnessEvent) :
    triangleWitnessGram X = colorGramMatrix X := rfl

/--
Source-to-operation closure.  Independently adjoining a triangle witness is simultaneously a
positive-record successor, an exact added event square, monotone under every pure quantum witness,
and a Lorentz-future increment.
-/
theorem triangleSource_operationalPhysicalLift
    (X Y : TriangleWitnessEvent) :
    twoRecordPrecedes
        (triangleWitnessPositiveRecord X)
        (triangleWitnessPositiveRecordAfter X Y) ∧
      (triangleWitnessPositiveRecordAfter X Y).1 =
        (triangleWitnessPositiveRecord X).1 + triangleWitnessGram Y ∧
      (∀ ψ : Fin 2 → ℂ,
        twoRecordWitnessWeight (triangleWitnessPositiveRecord X).1 ψ ≤
          twoRecordWitnessWeight (triangleWitnessPositiveRecordAfter X Y).1 ψ) ∧
      IsLorentzFuture
        (colorGramTime Y) (colorGramX Y) (colorGramY Y) (colorGramZ Y) := by
  have hprecedes :
      twoRecordPrecedes
        (triangleWitnessPositiveRecord X)
        (triangleWitnessPositiveRecordAfter X Y) := by
    change
      (triangleWitnessGram X + triangleWitnessGram Y -
        triangleWitnessGram X).PosSemidef
    simpa only [add_sub_cancel_left] using triangleWitnessGram_posSemidef Y
  refine ⟨hprecedes, rfl, ?_, ?_⟩
  · exact
      (twoRecordPrecedes_iff_forall_witnessWeight_le
        (triangleWitnessPositiveRecord X)
        (triangleWitnessPositiveRecordAfter X Y)).mp hprecedes
  · exact ⟨colorGramTime_nonneg Y, colorGramLorentzMassSq_nonneg Y⟩

/-- Squared norm of a two-channel spinor. -/
def twoSpinorNormSq (ψ : Fin 2 → ℂ) : ℝ :=
  Complex.normSq (ψ 0) + Complex.normSq (ψ 1)

/--
A spinor and its antilinear spin complement resolve a scalar identity.  Unit spinors therefore
give complete binary alternatives without choosing a preferred basis.
-/
theorem higgsSpinorEventMatrix_add_spinFlip_eq_smul_one
    (ψ : Fin 2 → ℂ) :
    higgsSpinorEventMatrix ψ +
        higgsSpinorEventMatrix (causalSpinFlip ψ) =
      ((twoSpinorNormSq ψ : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higgsSpinorEventMatrix, causalSpinFlip, twoSpinorNormSq,
      Matrix.vecMulVec_apply, Matrix.smul_apply,
      Complex.normSq_eq_conj_mul_self] <;> ring

/-- The two complementary pure witness weights sum to norm-square times record trace. -/
theorem twoRecordWitnessWeight_add_spinFlip
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ) :
    twoRecordWitnessWeight A ψ +
        twoRecordWitnessWeight A (causalSpinFlip ψ) =
      twoSpinorNormSq ψ * (Matrix.trace A).re := by
  simp [twoRecordWitnessWeight, causalSpinFlip, twoSpinorNormSq,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.trace_fin_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/--
Exact binary Born normalization.  A positive trace-one record evaluated on a unit spinor and its
spin complement gives two numbers in `[0,1]` whose sum is one.
-/
theorem twoRecord_binaryBorn_probabilities
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef)
    (htrace : Matrix.trace A = 1)
    (ψ : Fin 2 → ℂ) (hψ : twoSpinorNormSq ψ = 1) :
    0 ≤ twoRecordWitnessWeight A ψ ∧
      twoRecordWitnessWeight A ψ ≤ 1 ∧
      0 ≤ twoRecordWitnessWeight A (causalSpinFlip ψ) ∧
      twoRecordWitnessWeight A (causalSpinFlip ψ) ≤ 1 ∧
      twoRecordWitnessWeight A ψ +
        twoRecordWitnessWeight A (causalSpinFlip ψ) = 1 := by
  have hp := twoRecordWitnessWeight_nonneg hA ψ
  have hq := twoRecordWitnessWeight_nonneg hA (causalSpinFlip ψ)
  have hsum :=
    twoRecordWitnessWeight_add_spinFlip A ψ
  rw [hψ, htrace] at hsum
  norm_num at hsum
  exact ⟨hp, by linarith, hq, by linarith, hsum⟩

end GaloisForLFunctions.HTGeometry
