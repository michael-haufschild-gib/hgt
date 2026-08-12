import GaloisForLFunctions.RHTower.SoninCofinalContractiveMobiusGammaXiIncidence
import GaloisForLFunctions.RHTower.SoninCofinalAmbidextrousInwardIncidence
import GaloisForLFunctions.RHTower.MobiusCriticalFisherReporterRankOneReduction
import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHardySource
import GaloisForLFunctions.RHTower.CCMGalerkinDiagonalTransfer

/-!
# Sonin--reporter arithmetic-clock commutator seam

The contractive cofinal Sonin carrier and the countable Hardy reporter both
land on the same complete `ell²` source.  Their apparent compatibility is not
automatic: the Sonin pullback acts before the complex arithmetic damping,
whereas the reporter remembers only the pullback of the undamped source.

This module identifies the discrepancy exactly.  The transported complex
Fisher score is the reporter-selected source-vector term plus one explicit
commutator between the positive Sonin pullback and the arithmetic damping
operator.  Consequently no additional operator-selection freedom remains;
the only missing cross-route theorem is a source law annihilating (or
controlling at the required scale) this commutator coefficient.
-/

open Complex MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open ContinuousLinearMap InnerProductSpace
open GaloisForLFunctions.HTGeometry

/-- Common complete source carrier for Möbius, reporter, and Sonin data. -/
abbrev MobiusClockSourceL2 := lp (fun _ : ℕ => ℂ) 2

/-- Holomorphic arithmetic-clock damping coefficient. -/
def mobiusCriticalComplexClockFactor (sigma : ℝ) (u : ℂ) (n : ℕ) : ℂ :=
  Complex.exp
    (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ))

theorem norm_mobiusCriticalComplexClockFactor_le_one
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) (n : ℕ) :
    ‖mobiusCriticalComplexClockFactor sigma u n‖ ≤ 1 := by
  rw [mobiusCriticalComplexClockFactor, Complex.norm_exp,
    Real.exp_le_one_iff]
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu)
      (sub_nonneg.mpr hsigma.le)) hlog

/-- Actual bounded arithmetic-clock damping on the complete source carrier. -/
def mobiusCriticalComplexClockDamping
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    MobiusClockSourceL2 →L[ℂ] MobiusClockSourceL2 := by
  let L : MobiusClockSourceL2 →ₗ[ℂ] MobiusClockSourceL2 :=
    { toFun := fun x =>
        ⟨fun n => mobiusCriticalComplexClockFactor sigma u n * x n,
          (lp.memℓp x).mono' (fun n => by
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg (x n))
              (norm_mobiusCriticalComplexClockFactor_le_one
                hsigma hu n))⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext n
        change mobiusCriticalComplexClockFactor sigma u n * (x n + y n) =
          mobiusCriticalComplexClockFactor sigma u n * x n +
            mobiusCriticalComplexClockFactor sigma u n * y n
        ring
      map_smul' := by
        intro z x
        apply lp.ext
        funext n
        change mobiusCriticalComplexClockFactor sigma u n * (z * x n) =
          z * (mobiusCriticalComplexClockFactor sigma u n * x n)
        ring }
  exact L.mkContinuous 1 (fun x => by
    simpa using lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun n => by
      change ‖mobiusCriticalComplexClockFactor sigma u n * x n‖ ≤ ‖x n‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg (x n))
        (norm_mobiusCriticalComplexClockFactor_le_one hsigma hu n)))

@[simp]
theorem mobiusCriticalComplexClockDamping_apply
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (x : MobiusClockSourceL2) (n : ℕ) :
    mobiusCriticalComplexClockDamping sigma u hsigma hu x n =
      mobiusCriticalComplexClockFactor sigma u n * x n := by
  rfl

theorem norm_mobiusCriticalComplexClockDamping_le_one
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    ‖mobiusCriticalComplexClockDamping sigma u hsigma hu‖ ≤ 1 := by
  apply (mobiusCriticalComplexClockDamping sigma u hsigma hu).opNorm_le_bound
    zero_le_one
  intro x
  simpa using lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun n => by
    change ‖mobiusCriticalComplexClockFactor sigma u n * x n‖ ≤ ‖x n‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg (x n))
      (norm_mobiusCriticalComplexClockFactor_le_one hsigma hu n))

/-- Complex damping is genuinely application of the bounded arithmetic clock
to the normalized physical source, not merely a coefficient analogy. -/
theorem mobiusCriticalComplexClockDamping_apply_source
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    mobiusCriticalComplexClockDamping sigma u hsigma hu
        (infiniteMobiusSignedWeightLp sigma hsigma) =
      infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma u hsigma hu := by
  apply lp.ext
  funext n
  change mobiusCriticalComplexClockFactor sigma u n *
      infiniteMobiusSignedWeight sigma n =
    infiniteMobiusCriticalComplexDampedSignedWeight sigma u n
  exact (infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp
    sigma u n).symm

/-- One finite-depth cofinal Sonin corner, pulled forward from the common
source carrier. -/
def soninCofinalSourceCorner
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ) :
    MobiusClockSourceL2 →L[ℂ] SoninL2 :=
  centralSoninInwardDilationCorner a r hr ∘L
    (cofinalInverseDilatedShellEmbedding
      c d r hc hcd hr N).toContinuousLinearMap

theorem norm_soninCofinalSourceCorner_apply_le
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (x : MobiusClockSourceL2) :
    ‖soninCofinalSourceCorner a c d r hc hcd hr N x‖ ≤ ‖x‖ := by
  exact norm_centralSoninInwardDilationCorner_cofinalEmbedding_le
    a c d r hc hcd hr N x

theorem norm_soninCofinalSourceCorner_le_one
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ) :
    ‖soninCofinalSourceCorner a c d r hc hcd hr N‖ ≤ 1 := by
  apply (soninCofinalSourceCorner a c d r hc hcd hr N).opNorm_le_bound
    zero_le_one
  intro x
  simpa using norm_soninCofinalSourceCorner_apply_le
    a c d r hc hcd hr N x

/-- Positive source pullback `A†A` of the finite-depth Sonin corner. -/
def soninCofinalPositiveSourcePullback
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ) :
    MobiusClockSourceL2 →L[ℂ] MobiusClockSourceL2 :=
  let A := soninCofinalSourceCorner a c d r hc hcd hr N
  ContinuousLinearMap.adjoint A ∘L A

/-- The Sonin transported pairing is exactly the pairing against its positive
source pullback. -/
theorem inner_soninCofinalSourceCorner_eq_pullback
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (x y : MobiusClockSourceL2) :
    inner ℂ (soninCofinalSourceCorner a c d r hc hcd hr N x)
        (soninCofinalSourceCorner a c d r hc hcd hr N y) =
      inner ℂ x (soninCofinalPositiveSourcePullback
        a c d r hc hcd hr N y) := by
  let A := soninCofinalSourceCorner a c d r hc hcd hr N
  change inner ℂ (A x) (A y) = inner ℂ x ((ContinuousLinearMap.adjoint A) (A y))
  exact (ContinuousLinearMap.adjoint_inner_right A x (A y)).symm

theorem norm_soninCofinalPositiveSourcePullback_apply_le
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (x : MobiusClockSourceL2) :
    ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N x‖ ≤ ‖x‖ := by
  let A := soninCofinalSourceCorner a c d r hc hcd hr N
  have hA : ‖A‖ ≤ 1 := norm_soninCofinalSourceCorner_le_one
    a c d r hc hcd hr N
  have hAdjNorm : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ :=
    (ContinuousLinearMap.adjoint :
      (MobiusClockSourceL2 →L[ℂ] SoninL2) ≃ₗᵢ⋆[ℂ]
        (SoninL2 →L[ℂ] MobiusClockSourceL2)).norm_map A
  change ‖(ContinuousLinearMap.adjoint A) (A x)‖ ≤ ‖x‖
  calc
    ‖(ContinuousLinearMap.adjoint A) (A x)‖ ≤
        ‖ContinuousLinearMap.adjoint A‖ * ‖A x‖ :=
      (ContinuousLinearMap.adjoint A).le_opNorm _
    _ ≤ 1 * ‖A x‖ := by
      rw [hAdjNorm]
      exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = ‖A x‖ := one_mul _
    _ ≤ ‖x‖ := norm_soninCofinalSourceCorner_apply_le
      a c d r hc hcd hr N x

/-- The positive Sonin source pullbacks converge strongly to the identity.
This is stronger than forward shell transport: it uses the reverse-oriented
corner, identified with the Hilbert adjoint, and the exact isometry of every
cofinal source embedding. -/
theorem tendsto_norm_soninCofinalPositiveSourcePullback_sub
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (x : MobiusClockSourceL2) :
    Tendsto (fun N =>
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N x - x‖)
      Filter.atTop (nhds 0) := by
  let E : ℕ → MobiusClockSourceL2 →L[ℂ] SoninL2 := fun N =>
    (cofinalInverseDilatedShellEmbedding
      c d r hc hcd hr N).toContinuousLinearMap
  let C : SoninL2 →L[ℂ] SoninL2 :=
    centralSoninInwardDilationCorner a r hr
  let R : SoninL2 →L[ℂ] SoninL2 :=
    centralSoninOutwardDilationCorner a r hr
  have hphysical : Tendsto (fun N =>
      ‖R (C (E N x)) - E N x‖) Filter.atTop (nhds 0) := by
    exact centralSoninOutward_comp_inward_cofinalEmbedding_tendsto
      a c d r ha hc hcd hda hr harc x
  have hrewrite (N : ℕ) :
      soninCofinalPositiveSourcePullback a c d r hc hcd hr N x - x =
        (ContinuousLinearMap.adjoint (E N))
          (R (C (E N x)) - E N x) := by
    change
      (ContinuousLinearMap.adjoint (C ∘L E N)) ((C ∘L E N) x) - x =
        (ContinuousLinearMap.adjoint (E N))
          (R (C (E N x)) - E N x)
    rw [ContinuousLinearMap.adjoint_comp,
      adjoint_centralSoninInwardDilationCorner, map_sub]
    have hE := (cofinalInverseDilatedShellEmbedding
      c d r hc hcd hr N).adjoint_comp_self
    have hEx := congrArg (fun T : MobiusClockSourceL2 →L[ℂ]
      MobiusClockSourceL2 => T x) hE
    have hEx' : (ContinuousLinearMap.adjoint (E N)) (E N x) = x := by
      simpa only [E, ContinuousLinearMap.comp_apply, one_apply_eq_self] using hEx
    change (ContinuousLinearMap.adjoint (E N)) (R (C (E N x))) - x =
      (ContinuousLinearMap.adjoint (E N)) (R (C (E N x))) -
        (ContinuousLinearMap.adjoint (E N)) (E N x)
    rw [hEx']
  apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hphysical
  rw [hrewrite]
  calc
    ‖(ContinuousLinearMap.adjoint (E N))
        (R (C (E N x)) - E N x)‖ ≤
        ‖ContinuousLinearMap.adjoint (E N)‖ *
          ‖R (C (E N x)) - E N x‖ :=
      (ContinuousLinearMap.adjoint (E N)).le_opNorm _
    _ ≤ 1 * ‖R (C (E N x)) - E N x‖ := by
      have hAdjNorm : ‖ContinuousLinearMap.adjoint (E N)‖ = ‖E N‖ :=
        (ContinuousLinearMap.adjoint :
          (MobiusClockSourceL2 →L[ℂ] SoninL2) ≃ₗᵢ⋆[ℂ]
            (SoninL2 →L[ℂ] MobiusClockSourceL2)).norm_map (E N)
      rw [hAdjNorm]
      exact mul_le_mul_of_nonneg_right
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr N).norm_toContinuousLinearMap_le (norm_nonneg _)
    _ = ‖R (C (E N x)) - E N x‖ := one_mul _

/-- Unit-ball source vector selected by the Sonin pullback and therefore
admissible for the countable Hardy reporter. -/
def soninCofinalPulledBackMobiusSourceVector
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (hsigma : 1 < sigma) : MobiusClockSourceL2 :=
  soninCofinalPositiveSourcePullback a c d r hc hcd hr N
    (infiniteMobiusSignedWeightLp sigma hsigma)

theorem norm_soninCofinalPulledBackMobiusSourceVector_le_one
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (hsigma : 1 < sigma) :
    ‖soninCofinalPulledBackMobiusSourceVector
      a c d r hc hcd hr N sigma hsigma‖ ≤ 1 := by
  rw [soninCofinalPulledBackMobiusSourceVector]
  simpa [norm_infiniteMobiusSignedWeightLp hsigma] using
    norm_soninCofinalPositiveSourcePullback_apply_le
      a c d r hc hcd hr N
      (infiniteMobiusSignedWeightLp sigma hsigma)

/-- The actual countable Hardy reporter selected by the Sonin pullback. -/
def soninCofinalPulledBackMobiusReporter
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (hsigma : 1 < sigma) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  squarefreeMobiusCriticalFisherSourceVectorReporter sigma hsigma
    (soninCofinalPulledBackMobiusSourceVector
      a c d r hc hcd hr N sigma hsigma)
    (norm_soninCofinalPulledBackMobiusSourceVector_le_one
      a c d r hc hcd hr N sigma hsigma)

/-- Exact obstruction to exchanging the Sonin pullback and arithmetic clock. -/
def soninCofinalComplexClockCommutator
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    MobiusClockSourceL2 →L[ℂ] MobiusClockSourceL2 :=
  soninCofinalPositiveSourcePullback a c d r hc hcd hr N ∘L
      mobiusCriticalComplexClockDamping sigma u hsigma hu -
    mobiusCriticalComplexClockDamping sigma u hsigma hu ∘L
      soninCofinalPositiveSourcePullback a c d r hc hcd hr N

/-- Every bounded arithmetic clock asymptotically commutes with the cofinal
positive Sonin pullback.  No equivariance hypothesis is required: both
orders converge strongly to the same clocked source vector. -/
theorem tendsto_norm_soninCofinalComplexClockCommutator_apply
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (x : MobiusClockSourceL2) :
    Tendsto (fun N =>
      ‖soninCofinalComplexClockCommutator
        a c d r hc hcd hr N sigma u hsigma hu x‖)
      atTop (nhds 0) := by
  let S := mobiusCriticalComplexClockDamping sigma u hsigma hu
  let D : ℕ → MobiusClockSourceL2 →L[ℂ] MobiusClockSourceL2 := fun N =>
    soninCofinalPositiveSourcePullback a c d r hc hcd hr N
  have hleft : Tendsto (fun N => ‖D N (S x) - S x‖) atTop (nhds 0) := by
    exact tendsto_norm_soninCofinalPositiveSourcePullback_sub
      a c d r ha hc hcd hda hr harc (S x)
  have hright0 : Tendsto (fun N => ‖D N x - x‖) atTop (nhds 0) := by
    exact tendsto_norm_soninCofinalPositiveSourcePullback_sub
      a c d r ha hc hcd hda hr harc x
  have hright : Tendsto (fun N => ‖S‖ * ‖D N x - x‖)
      atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hright0 using 1
    all_goals simp
  have hsum : Tendsto
      (fun N => ‖D N (S x) - S x‖ + ‖S‖ * ‖D N x - x‖)
      atTop (nhds 0) := by
    simpa using hleft.add hright
  apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hsum
  change ‖D N (S x) - S (D N x)‖ ≤
    ‖D N (S x) - S x‖ + ‖S‖ * ‖D N x - x‖
  calc
    ‖D N (S x) - S (D N x)‖ =
        ‖(D N (S x) - S x) - S (D N x - x)‖ := by
      rw [map_sub]
      congr 1
      abel
    _ ≤ ‖D N (S x) - S x‖ + ‖S (D N x - x)‖ := norm_sub_le _ _
    _ ≤ ‖D N (S x) - S x‖ + ‖S‖ * ‖D N x - x‖ :=
      add_le_add le_rfl (S.le_opNorm _)

/-- SOURCE-CLOCK-SEAM: transported complex-damped Fisher score equals the
term determined by the reporter-selected source vector plus one explicit
clock commutator coefficient. -/
theorem soninCofinal_complexFisherScore_eq_reporterTerm_add_commutator
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    inner ℂ
        (soninCofinalSourceCorner a c d r hc hcd hr N
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
        (soninCofinalSourceCorner a c d r hc hcd hr N
          (infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma u hsigma hu)) =
      inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
          (mobiusCriticalComplexClockDamping sigma u hsigma hu
            (soninCofinalPulledBackMobiusSourceVector
              a c d r hc hcd hr N sigma hsigma)) +
        inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
          (soninCofinalComplexClockCommutator
            a c d r hc hcd hr N sigma u hsigma hu
              (infiniteMobiusSignedWeightLp sigma hsigma)) := by
  rw [inner_soninCofinalSourceCorner_eq_pullback,
    ← mobiusCriticalComplexClockDamping_apply_source]
  simp only [soninCofinalPulledBackMobiusSourceVector,
    soninCofinalComplexClockCommutator, ContinuousLinearMap.comp_apply,
    sub_apply, inner_sub_right]
  ring

/-- Exact gap form: every future route need only annihilate this scalar
commutator coefficient, not identify two unrelated transports globally. -/
theorem soninCofinal_complexFisherScore_sub_reporterTerm_eq_commutator
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    inner ℂ
        (soninCofinalSourceCorner a c d r hc hcd hr N
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
        (soninCofinalSourceCorner a c d r hc hcd hr N
          (infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma u hsigma hu)) -
      inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (mobiusCriticalComplexClockDamping sigma u hsigma hu
          (soninCofinalPulledBackMobiusSourceVector
            a c d r hc hcd hr N sigma hsigma)) =
      inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (soninCofinalComplexClockCommutator
          a c d r hc hcd hr N sigma u hsigma hu
            (infiniteMobiusSignedWeightLp sigma hsigma)) := by
  rw [soninCofinal_complexFisherScore_eq_reporterTerm_add_commutator]
  ring

/-- ASYMPTOTIC SOURCE-CLOCK IDENTIFICATION: the transported Sonin score and
the reporter-selected clocked source score coincide in the cofinal limit.
This discharges the non-equivariant compatibility seam without assuming
literal finite-depth commutation. -/
theorem tendsto_soninCofinal_complexFisherScore_sub_reporterTerm
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    Tendsto (fun N =>
      inner ℂ
          (soninCofinalSourceCorner a c d r hc hcd hr N
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
          (soninCofinalSourceCorner a c d r hc hcd hr N
            (infiniteMobiusCriticalComplexDampedSignedWeightLp
              sigma u hsigma hu)) -
        inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
          (mobiusCriticalComplexClockDamping sigma u hsigma hu
            (soninCofinalPulledBackMobiusSourceVector
              a c d r hc hcd hr N sigma hsigma)))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hcomm := tendsto_norm_soninCofinalComplexClockCommutator_apply
    a c d r ha hc hcd hda hr harc sigma u hsigma hu
      (infiniteMobiusSignedWeightLp sigma hsigma)
  have hmajor : Tendsto (fun N =>
      ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ *
        ‖soninCofinalComplexClockCommutator
          a c d r hc hcd hr N sigma u hsigma hu
            (infiniteMobiusSignedWeightLp sigma hsigma)‖)
      atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hcomm using 1
    all_goals simp
  apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hmajor
  rw [soninCofinal_complexFisherScore_sub_reporterTerm_eq_commutator]
  exact norm_inner_le_norm _ _

/-- If another corpus route supplies clock commutation, the Sonin score is
already completely identified by the same source vector used by the Hardy
reporter. -/
theorem soninCofinal_complexFisherScore_eq_reporterTerm_of_commutator_zero
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (hcomm : soninCofinalComplexClockCommutator
      a c d r hc hcd hr N sigma u hsigma hu = 0) :
    inner ℂ
        (soninCofinalSourceCorner a c d r hc hcd hr N
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
        (soninCofinalSourceCorner a c d r hc hcd hr N
          (infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma u hsigma hu)) =
      inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (mobiusCriticalComplexClockDamping sigma u hsigma hu
          (soninCofinalPulledBackMobiusSourceVector
            a c d r hc hcd hr N sigma hsigma)) := by
  rw [soninCofinal_complexFisherScore_eq_reporterTerm_add_commutator,
    hcomm]
  simp

/-! ## Source-derived cofinal Fisher profile -/

/-- The complex source with real aperture is definitionally the original
real-damped physical source, including its `ell²` certificate.  This is the
coefficient-faithful identification needed to feed the real Euler theorem
through the non-equivariant Sonin transport. -/
theorem infiniteMobiusCriticalComplexDampedSignedWeightLp_ofReal
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma (u : ℂ) hsigma (by simpa using hu) =
      infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu := by
  apply lp.ext
  funext n
  change infiniteMobiusCriticalComplexDampedSignedWeight sigma (u : ℂ) n =
    infiniteMobiusCriticalDampedSignedWeight sigma u n
  simp [infiniteMobiusCriticalComplexDampedSignedWeight]

/-- FIXED-SOURCE SONIN--EULER SPLICE: at every admissible Euler parameter,
the actual transported Sonin score converges to the coefficient computed by
the squarefree Möbius Fisher law.  No finite-depth equivariance or realization
hypothesis is assumed. -/
theorem tendsto_soninCofinal_complexFisherScore_ofReal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Tendsto (fun N =>
      inner ℂ
          (soninCofinalSourceCorner a c d r hc hcd hr N
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
          (soninCofinalSourceCorner a c d r hc hcd hr N
            (infiniteMobiusCriticalComplexDampedSignedWeightLp
              sigma (u : ℂ) hsigma (by simpa using hu))))
      atTop
      (nhds (infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u)) := by
  simp_rw [inner_soninCofinalSourceCorner_eq_pullback]
  have hpull : Tendsto (fun N =>
      soninCofinalPositiveSourcePullback a c d r hc hcd hr N
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma (u : ℂ) hsigma (by simpa using hu)))
      atTop
      (nhds (infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma (u : ℂ) hsigma (by simpa using hu))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_norm_soninCofinalPositiveSourcePullback_sub
      a c d r ha hc hcd hda hr harc
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma (u : ℂ) hsigma (by simpa using hu))
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      atTop (nhds (infiniteMobiusCriticalFisherTangentLp sigma hsigma)))
    hpull
  rw [infiniteMobiusCriticalComplexDampedSignedWeightLp_ofReal
      hsigma hu,
    inner_fisherTangent_damped_eq_coefficient hsigma hu] at hinner
  convert hinner using 1
  ext N
  rw [infiniteMobiusCriticalComplexDampedSignedWeightLp_ofReal hsigma hu]

/-- Explicit source-half-plane schedule approaching the critical boundary. -/
def soninMobiusCriticalSigmaSequence (j : ℕ) : ℝ :=
  1 + 1 / (j + 1)

theorem soninMobiusCriticalSigmaSequence_gt_one (j : ℕ) :
    1 < soninMobiusCriticalSigmaSequence j := by
  rw [soninMobiusCriticalSigmaSequence]
  have hden : (0 : ℝ) < j + 1 := by positivity
  have hinv : (0 : ℝ) < 1 / (j + 1) := one_div_pos.mpr hden
  linarith

theorem tendsto_soninMobiusCriticalSigmaSequence :
    Tendsto soninMobiusCriticalSigmaSequence atTop
      (nhdsWithin 1 (Set.Ioi 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hzero : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [soninMobiusCriticalSigmaSequence, add_zero] using!
      tendsto_const_nhds.add hzero
  · exact Filter.Eventually.of_forall
      soninMobiusCriticalSigmaSequence_gt_one

/-- The one scalar observed after simultaneously choosing a critical Euler
level `j` and a finite Sonin depth `N`. -/
def soninCofinalCriticalFisherScore
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (u : ℝ) (hu : 0 ≤ u) (j N : ℕ) : ℂ :=
  inner ℂ
    (soninCofinalSourceCorner a c d r hc hcd hr N
      (infiniteMobiusCriticalFisherTangentLp
        (soninMobiusCriticalSigmaSequence j)
        (soninMobiusCriticalSigmaSequence_gt_one j)))
    (soninCofinalSourceCorner a c d r hc hcd hr N
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        (soninMobiusCriticalSigmaSequence j) (u : ℂ)
        (soninMobiusCriticalSigmaSequence_gt_one j)
        (by simpa using hu)))

/-- COFINAL SOURCE-DIAGONAL LAW: one genuinely finite-depth Sonin sequence
tracks the physical Möbius coefficient while the Euler parameter approaches
the critical boundary.  The selected depths are cofinal, the tracking error
is quantitatively `O(1/j)`, and the transported scores converge to the exact
positive Fisher profile `2u/(1+u)²`.

This is the corpus-wide Frankenstein splice: Sonin strong recovery supplies
each finite-depth approximation, the Galerkin route supplies diagonal
selection, and the squarefree Euler route supplies the terminal coefficient. -/
theorem exists_soninCofinalCriticalFisherScore_diagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (u : ℝ) (hu : 0 ≤ u) :
    ∃ Nseq : ℕ → ℕ,
      (∀ j, j < Nseq j) ∧
      (∀ j,
        dist (soninCofinalCriticalFisherScore
          a c d r hc hcd hr u hu j (Nseq j))
          (infiniteMobiusCriticalFisherTangentDampedCoefficient
            (soninMobiusCriticalSigmaSequence j) u) <
          1 / (j + 1 : ℝ)) ∧
      Tendsto (fun j => soninCofinalCriticalFisherScore
        a c d r hc hcd hr u hu j (Nseq j))
        atTop (nhds (((2 * u / (1 + u) ^ 2 : ℝ) : ℂ))) := by
  let F : ℕ → ℕ → ℝ := fun j N =>
    dist (soninCofinalCriticalFisherScore
      a c d r hc hcd hr u hu j N)
      (infiniteMobiusCriticalFisherTangentDampedCoefficient
        (soninMobiusCriticalSigmaSequence j) u)
  have happrox : ∀ j : ℕ, ∀ ε > 0, ∃ M, j < M ∧ F j M < ε := by
    intro j ε hε
    have hfixed := tendsto_soninCofinal_complexFisherScore_ofReal
      a c d r ha hc hcd hda hr harc
      (soninMobiusCriticalSigmaSequence j) u
      (soninMobiusCriticalSigmaSequence_gt_one j) hu
    have hfixed' : Tendsto (fun N =>
        soninCofinalCriticalFisherScore a c d r hc hcd hr u hu j N)
        atTop
        (nhds (infiniteMobiusCriticalFisherTangentDampedCoefficient
          (soninMobiusCriticalSigmaSequence j) u)) := by
      exact hfixed
    rw [Metric.tendsto_atTop] at hfixed'
    obtain ⟨N, hN⟩ := hfixed' ε hε
    refine ⟨max N (j + 1), by omega, ?_⟩
    exact hN _ (le_max_left _ _)
  obtain ⟨Nseq, hcofinal, herror⟩ :=
    GaloisForLFunctions.RHTower.exists_diagonal_lt happrox
  refine ⟨Nseq, hcofinal, herror, ?_⟩
  have hcoeff : Tendsto (fun j =>
      infiniteMobiusCriticalFisherTangentDampedCoefficient
        (soninMobiusCriticalSigmaSequence j) u)
      atTop (nhds (((2 * u / (1 + u) ^ 2 : ℝ) : ℂ))) :=
    (tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient hu).comp
      tendsto_soninMobiusCriticalSigmaSequence
  exact GaloisForLFunctions.RHTower.tendsto_of_dist_lt_inv hcoeff herror

end RHTower
