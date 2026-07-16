import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Matrix.Order

/-!
# Finite-rank hypertranscendental asymptotic connections

A dilation-covariant family of invertible finite matrix frames has a positive-definite Hermitian
metric and a scale-independent normalized connection. For connections valued in the units of a
normed ring, two-sided bounded flatability is equivalent to two-sided boundedness of the canonical
partial transport. The explicit scalar links (n+2)/(n+1) have transport n+1: their normalized
logarithmic exponent vanishes although no two-sided bounded flat gauge exists.

The purely group-theoretic transport, gauge covariance, algebraic flatness, and uniqueness results
are imported from HypertranscendentalClockBoundary and reused here.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

abbrev FiniteRankGL (r : ℕ) := (Matrix (Fin r) (Fin r) ℂ)ˣ

noncomputable def matrixExpUnit (r : ℕ) (s : ℝ) : FiniteRankGL r :=
  Units.map (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ)).toMonoidHom
    (Units.mk0 (Real.exp s : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero s)))

@[simp] theorem matrixExpUnit_zero (r : ℕ) : matrixExpUnit r 0 = 1 := by
  ext
  simp [matrixExpUnit]

theorem matrixExpUnit_add (r : ℕ) (s t : ℝ) :
    matrixExpUnit r (s + t) = matrixExpUnit r s * matrixExpUnit r t := by
  ext
  simp [matrixExpUnit, Real.exp_add]

@[simp] theorem matrixExpUnit_neg (r : ℕ) (s : ℝ) :
    (matrixExpUnit r s)⁻¹ = matrixExpUnit r (-s) := by
  ext
  simp [matrixExpUnit, Real.exp_neg]

theorem matrixExpUnit_comm (r : ℕ) (s : ℝ) (A : FiniteRankGL r) :
    matrixExpUnit r s * A = A * matrixExpUnit r s := by
  apply Units.ext
  exact Algebra.commutes _ _

structure CovariantPositiveMatrixFrame (r : ℕ) where
  frame : ℝ → ℕ → FiniteRankGL r
  frame_covariant : ∀ s n,
    frame s n = matrixExpUnit r (-((n : ℝ) * s)) * frame 0 n

namespace CovariantPositiveMatrixFrame

variable {r : ℕ} (F : CovariantPositiveMatrixFrame r)

def metric (s : ℝ) (n : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  (F.frame s n : Matrix (Fin r) (Fin r) ℂ)ᴴ * F.frame s n

theorem metric_posDef (s : ℝ) (n : ℕ) : (F.metric s n).PosDef := by
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_iff_isUnit.mpr (F.frame s n).isUnit)

def scaleNormalizedFrame (s : ℝ) (n : ℕ) : FiniteRankGL r :=
  matrixExpUnit r ((n : ℝ) * s) * F.frame s n

@[simp] theorem scaleNormalizedFrame_eq_base (s : ℝ) (n : ℕ) :
    F.scaleNormalizedFrame s n = F.frame 0 n := by
  rw [scaleNormalizedFrame, F.frame_covariant]
  rw [← mul_assoc, ← matrixExpUnit_add]
  simp

def scaleNormalizedConnection (S : ℕ → FiniteRankGL r) (s : ℝ) (n : ℕ) :
    FiniteRankGL r :=
  F.scaleNormalizedFrame s (n + 1) * S n * (F.scaleNormalizedFrame s n)⁻¹

@[simp] theorem scaleNormalizedConnection_eq_base
    (S : ℕ → FiniteRankGL r) (s : ℝ) (n : ℕ) :
    F.scaleNormalizedConnection S s n =
      F.frame 0 (n + 1) * S n * (F.frame 0 n)⁻¹ := by
  simp [scaleNormalizedConnection]

theorem scaleNormalizedConnection_independent
    (S : ℕ → FiniteRankGL r) (s t : ℝ) (n : ℕ) :
    F.scaleNormalizedConnection S s n = F.scaleNormalizedConnection S t n := by
  rw [F.scaleNormalizedConnection_eq_base, F.scaleNormalizedConnection_eq_base]

end CovariantPositiveMatrixFrame

/-- A finite-rank positive Hermitian metric with the exact jet-dilation covariance from the card.
The positive square root will supply its canonical invertible frame. -/
structure DilationCovariantPositiveMetric (r : ℕ) where
  metric : ℝ → ℕ → Matrix (Fin r) (Fin r) ℂ
  posDef : ∀ s n, (metric s n).PosDef
  covariant : ∀ s n,
    metric s n = Real.exp (-2 * (n : ℝ) * s) • metric 0 n

namespace DilationCovariantPositiveMetric

variable {r : ℕ} (H : DilationCovariantPositiveMetric r)

/-- The canonical positive square-root frame of a positive-definite metric. -/
noncomputable def positiveFrame (s : ℝ) (n : ℕ) : FiniteRankGL r :=
  ((CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt).1
    (H.posDef s n).isStrictlyPositive).1.unit

@[simp] theorem coe_positiveFrame (s : ℝ) (n : ℕ) :
    (H.positiveFrame s n : Matrix (Fin r) (Fin r) ℂ) = CFC.sqrt (H.metric s n) := by
  exact IsUnit.unit_spec _

/-- The positive square root has half the metric's dilation weight. -/
theorem sqrt_metric_eq_smul_base (s : ℝ) (n : ℕ) :
    CFC.sqrt (H.metric s n) =
      Real.exp (-((n : ℝ) * s)) • CFC.sqrt (H.metric 0 n) := by
  apply (CFC.sqrt_eq_iff _ _ (H.posDef s n).posSemidef.nonneg
    (smul_nonneg (Real.exp_pos _).le (CFC.sqrt_nonneg _))).2
  rw [H.covariant s n]
  rw [smul_mul_smul]
  rw [CFC.sqrt_mul_sqrt_self _ (H.posDef 0 n).posSemidef.nonneg]
  congr 1
  rw [← Real.exp_add]
  ring_nf

/-- Every dilation-covariant positive metric canonically determines a covariant invertible frame. -/
noncomputable def covariantPositiveFrame : CovariantPositiveMatrixFrame r where
  frame := H.positiveFrame
  frame_covariant s n := by
    apply Units.ext
    rw [coe_positiveFrame, Units.val_mul, coe_positiveFrame,
      H.sqrt_metric_eq_smul_base]
    ext i j
    simp [matrixExpUnit, Matrix.mul_apply, Matrix.algebraMap_matrix_apply]

/-- The canonical square-root frame factors the original Hermitian metric exactly. -/
theorem metric_eq_frame_conjTranspose_mul_frame (s : ℝ) (n : ℕ) :
    H.metric s n =
      (H.positiveFrame s n : Matrix (Fin r) (Fin r) ℂ)ᴴ * H.positiveFrame s n := by
  rw [coe_positiveFrame]
  change H.metric s n = star (CFC.sqrt (H.metric s n)) * CFC.sqrt (H.metric s n)
  rw [(CFC.sqrt_nonneg (H.metric s n)).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self _ (H.posDef s n).posSemidef.nonneg]

/-- **Finite-rank defect conservation from the metric itself.** The square-root connection
attached to any dilation-covariant positive metric is independent of the scale fiber. -/
theorem scaleNormalizedConnection_independent
    (S : ℕ → FiniteRankGL r) (s t : ℝ) (n : ℕ) :
    H.covariantPositiveFrame.scaleNormalizedConnection S s n =
      H.covariantPositiveFrame.scaleNormalizedConnection S t n :=
  H.covariantPositiveFrame.scaleNormalizedConnection_independent S s t n

end DilationCovariantPositiveMetric

def IsTwoSidedUniformlyBounded {R : Type*} [Monoid R] [Norm R] (g : ℕ → Rˣ) : Prop :=
  ∃ C D : ℝ, ∀ n, ‖(g n : R)‖ ≤ C ∧ ‖(↑((g n)⁻¹) : R)‖ ≤ D

theorem canonicalFlatGauge_twoSidedBounded_iff_transport
    {R : Type*} [Monoid R] [Norm R] (U : ℕ → Rˣ) :
    IsTwoSidedUniformlyBounded (discreteConnectionFlatGauge U) ↔
      IsTwoSidedUniformlyBounded (discreteConnectionTransport U) := by
  constructor
  · rintro ⟨C, D, h⟩
    exact ⟨D, C, fun n => by
      simpa [discreteConnectionFlatGauge] using (h n).symm⟩
  · rintro ⟨C, D, h⟩
    exact ⟨D, C, fun n => by
      simpa [discreteConnectionFlatGauge] using (h n).symm⟩

theorem exists_twoSidedBounded_flatGauge_iff_transport
    {R : Type*} [NormedRing R] (U : ℕ → Rˣ) :
    (∃ g : ℕ → Rˣ, IsTwoSidedUniformlyBounded g ∧
      ∀ n, discreteConnectionGauge U g n = 1) ↔
      IsTwoSidedUniformlyBounded (discreteConnectionTransport U) := by
  constructor
  · rintro ⟨g, ⟨C, D, hg⟩, hflat⟩
    refine ⟨D * ‖(g 0 : R)‖, ‖(↑((g 0)⁻¹) : R)‖ * C, ?_⟩
    intro n
    have hunique := discreteConnectionFlatGauge_unique U g hflat n
    have htransport : discreteConnectionTransport U n = (g n)⁻¹ * g 0 := by
      rw [hunique]
      group
    have htransportInv : (discreteConnectionTransport U n)⁻¹ = (g 0)⁻¹ * g n := by
      rw [hunique]
      group
    constructor
    · rw [htransport]
      change ‖(↑((g n)⁻¹) : R) * (g 0 : R)‖ ≤ D * ‖(g 0 : R)‖
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hg n).2 (norm_nonneg _))
    · rw [htransportInv]
      change ‖(↑((g 0)⁻¹) : R) * (g n : R)‖ ≤ ‖(↑((g 0)⁻¹) : R)‖ * C
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hg n).1 (norm_nonneg _))
  · intro htransport
    refine ⟨discreteConnectionFlatGauge U,
      (canonicalFlatGauge_twoSidedBounded_iff_transport U).2 htransport, ?_⟩
    exact discreteConnectionGauge_flat U

noncomputable def polynomialConnectionLink (n : ℕ) : ℝˣ :=
  Units.mk0 (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) (by positivity)

theorem polynomialConnectionTransport_eq (n : ℕ) :
    ((discreteConnectionTransport polynomialConnectionLink n : ℝˣ) : ℝ) = (n + 1 : ℕ) := by
  induction n with
  | zero => simp [discreteConnectionTransport]
  | succ n ih =>
      rw [discreteConnectionTransport]
      change (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
          ((discreteConnectionTransport polynomialConnectionLink n : ℝˣ) : ℝ) =
        ((n + 2 : ℕ) : ℝ)
      rw [ih]
      field_simp

def polynomialEscapeTransport (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

theorem polynomialEscapeTransport_tendsto_atTop :
    Tendsto polynomialEscapeTransport atTop atTop := by
  have h := tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by
    simp [polynomialEscapeTransport, Nat.cast_add, Nat.cast_one]

theorem polynomialEscapeTransport_not_uniformlyBounded :
    ¬ IsUniformlyBoundedProfile polynomialEscapeTransport := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have h := hB n
  have hnonneg : 0 ≤ polynomialEscapeTransport n := by
    unfold polynomialEscapeTransport
    exact_mod_cast Nat.zero_le (n + 1)
  rw [abs_of_nonneg hnonneg] at h
  exact (not_lt_of_ge h) (hn.trans_le (by
    change (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.le_add_right n 1))

theorem polynomialEscapeTransport_normalizedLog_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (polynomialEscapeTransport n) / (n : ℝ))
      atTop (nhds 0) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hshift
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ))
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h := hone.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    have heq : (fun n : ℕ => (1 : ℝ) + (n : ℝ)⁻¹) =ᶠ[atTop]
        (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
    simpa only [add_zero] using h.congr' heq
  have hmul := hlog.mul hratio
  simp only [zero_mul] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [polynomialEscapeTransport, Nat.cast_add, Nat.cast_one]
  field_simp

theorem polynomialConnectionTransport_not_twoSidedUniformlyBounded :
    ¬ IsTwoSidedUniformlyBounded
      (discreteConnectionTransport polynomialConnectionLink) := by
  rintro ⟨C, D, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hforward := (h n).1
  rw [polynomialConnectionTransport_eq] at hforward
  have hnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hforward
  exact (not_lt_of_ge hforward) (hn.trans_le (by
    exact_mod_cast Nat.le_add_right n 1))

theorem polynomialConnection_no_twoSidedBounded_flatGauge :
    ¬ ∃ g : ℕ → ℝˣ, IsTwoSidedUniformlyBounded g ∧
      ∀ n, discreteConnectionGauge polynomialConnectionLink g n = 1 := by
  rw [exists_twoSidedBounded_flatGauge_iff_transport]
  exact polynomialConnectionTransport_not_twoSidedUniformlyBounded

theorem polynomialConnection_normalizedLog_tendsto_zero :
    Tendsto (fun n : ℕ =>
      Real.log ‖((discreteConnectionTransport polynomialConnectionLink n : ℝˣ) : ℝ)‖ /
        (n : ℝ)) atTop (nhds 0) := by
  apply polynomialEscapeTransport_normalizedLog_tendsto_zero.congr'
  exact Filter.Eventually.of_forall fun n => by
    dsimp
    rw [polynomialConnectionTransport_eq]
    simp [polynomialEscapeTransport]

end

end GaloisForLFunctions.HTGeometry
