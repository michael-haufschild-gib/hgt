import GaloisForLFunctions.RHTower.SoninCofinalReporterClockCommutatorSeam

open Complex MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open ContinuousLinearMap InnerProductSpace
open GaloisForLFunctions.HTGeometry

private theorem gce_invSqrtTwo_mul_self :
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 / 2 := by
  have hsqrt0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hsqrt0]
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

/-- Source-native two-order block, before choosing a scalar port. -/
def mobiusClockSoninMarkedProducer
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (x : MobiusClockSourceL2) : WithLp 2 (MobiusClockSourceL2 × MobiusClockSourceL2) :=
  let P := soninCofinalPositiveSourcePullback a c d r hc hcd hr N
  let D := mobiusCriticalComplexClockDamping sigma u hsigma hu
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • WithLp.toLp 2 (P (D x), D (P x))

/-- Bundled continuous-linear form of the marked two-order producer. -/
def mobiusClockSoninMarkedProducerCLM
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    MobiusClockSourceL2 →L[ℂ]
      WithLp 2 (MobiusClockSourceL2 × MobiusClockSourceL2) :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    (WithLp.prodContinuousLinearEquiv 2 ℂ
      MobiusClockSourceL2 MobiusClockSourceL2).symm.toContinuousLinearMap.comp
      (((soninCofinalPositiveSourcePullback a c d r hc hcd hr N).comp
            (mobiusCriticalComplexClockDamping sigma u hsigma hu)).prod
        ((mobiusCriticalComplexClockDamping sigma u hsigma hu).comp
            (soninCofinalPositiveSourcePullback a c d r hc hcd hr N)))

@[simp] theorem mobiusClockSoninMarkedProducerCLM_apply
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (x : MobiusClockSourceL2) :
    mobiusClockSoninMarkedProducerCLM
        a c d r hc hcd hr N sigma u hsigma hu x =
      mobiusClockSoninMarkedProducer
        a c d r hc hcd hr N sigma u hsigma hu x := rfl

/-- Symmetric Hadamard source port. -/
def mobiusClockSoninMarkedEvenPort
    (z : WithLp 2 (MobiusClockSourceL2 × MobiusClockSourceL2)) :
    MobiusClockSourceL2 :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (z.fst + z.snd)

/-- Reflection-odd Hadamard source port. -/
def mobiusClockSoninMarkedOddPort
    (z : WithLp 2 (MobiusClockSourceL2 × MobiusClockSourceL2)) :
    MobiusClockSourceL2 :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (z.fst - z.snd)

theorem mobiusClockSoninMarkedOddPort_producer
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (x : MobiusClockSourceL2) :
    mobiusClockSoninMarkedOddPort
        (mobiusClockSoninMarkedProducer
          a c d r hc hcd hr N sigma u hsigma hu x) =
      (1 / 2 : ℂ) •
        soninCofinalComplexClockCommutator
          a c d r hc hcd hr N sigma u hsigma hu x := by
  simp only [mobiusClockSoninMarkedOddPort,
    mobiusClockSoninMarkedProducer, smul_sub, WithLp.smul_fst,
    WithLp.smul_snd, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [smul_smul, smul_smul, gce_invSqrtTwo_mul_self]
  simp [soninCofinalComplexClockCommutator, smul_sub]

theorem mobiusClockSoninMarkedEvenPort_producer
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (x : MobiusClockSourceL2) :
    mobiusClockSoninMarkedEvenPort
        (mobiusClockSoninMarkedProducer
          a c d r hc hcd hr N sigma u hsigma hu x) =
      (1 / 2 : ℂ) •
        ((soninCofinalPositiveSourcePullback a c d r hc hcd hr N ∘L
            mobiusCriticalComplexClockDamping sigma u hsigma hu) +
          (mobiusCriticalComplexClockDamping sigma u hsigma hu ∘L
            soninCofinalPositiveSourcePullback a c d r hc hcd hr N)) x := by
  simp only [mobiusClockSoninMarkedEvenPort,
    mobiusClockSoninMarkedProducer, smul_add, WithLp.smul_fst,
    WithLp.smul_snd, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [smul_smul, smul_smul, gce_invSqrtTwo_mul_self]
  simp [smul_add]

theorem mobiusClockSoninMarkedPorts_energy
    (z : WithLp 2 (MobiusClockSourceL2 × MobiusClockSourceL2)) :
    ‖mobiusClockSoninMarkedEvenPort z‖ ^ 2 +
        ‖mobiusClockSoninMarkedOddPort z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [mobiusClockSoninMarkedEvenPort, mobiusClockSoninMarkedOddPort,
    norm_smul, norm_smul, mul_pow, mul_pow,
    invSqrtTwo_norm_sq, norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ),
    WithLp.prod_norm_sq_eq_of_L2]
  ring

theorem norm_mobiusClockSoninMarkedProducer_le
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (x : MobiusClockSourceL2) :
    ‖mobiusClockSoninMarkedProducer
      a c d r hc hcd hr N sigma u hsigma hu x‖ ≤ ‖x‖ := by
  let P := soninCofinalPositiveSourcePullback a c d r hc hcd hr N
  let D := mobiusCriticalComplexClockDamping sigma u hsigma hu
  have hP (y : MobiusClockSourceL2) : ‖P y‖ ≤ ‖y‖ := by
    exact norm_soninCofinalPositiveSourcePullback_apply_le
      a c d r hc hcd hr N y
  have hD (y : MobiusClockSourceL2) : ‖D y‖ ≤ ‖y‖ := by
    calc
      ‖D y‖ ≤ ‖D‖ * ‖y‖ := D.le_opNorm y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right
        (norm_mobiusCriticalComplexClockDamping_le_one
          sigma u hsigma hu) (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  have hPD : ‖P (D x)‖ ≤ ‖x‖ := le_trans (hP _) (hD _)
  have hDP : ‖D (P x)‖ ≤ ‖x‖ := le_trans (hD _) (hP _)
  have hsqPD : ‖P (D x)‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hPD
  have hsqDP : ‖D (P x)‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hDP
  have hproducerSq :
      ‖mobiusClockSoninMarkedProducer
        a c d r hc hcd hr N sigma u hsigma hu x‖ ^ 2 =
        (1 / 2 : ℝ) * (‖P (D x)‖ ^ 2 + ‖D (P x)‖ ^ 2) := by
    rw [mobiusClockSoninMarkedProducer, norm_smul, mul_pow,
      invSqrtTwo_norm_sq, WithLp.prod_norm_sq_eq_of_L2]
    rfl
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hproducerSq]
  nlinarith

def soninCofinalMarkedClockOddScalar
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) : ℂ :=
  inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
    (mobiusClockSoninMarkedOddPort
      (mobiusClockSoninMarkedProducer a c d r hc hcd hr N sigma u hsigma hu
        (infiniteMobiusSignedWeightLp sigma hsigma)))

theorem soninCofinal_scalarSeam_eq_two_mul_markedOddScalar
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
      2 * soninCofinalMarkedClockOddScalar
        a c d r hc hcd hr N sigma u hsigma hu := by
  rw [soninCofinal_complexFisherScore_sub_reporterTerm_eq_commutator,
    soninCofinalMarkedClockOddScalar,
    mobiusClockSoninMarkedOddPort_producer,
    inner_smul_right]
  ring

theorem norm_actual_mobiusClockSoninMarkedProducer_le_one
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    ‖mobiusClockSoninMarkedProducer a c d r hc hcd hr N sigma u hsigma hu
      (infiniteMobiusSignedWeightLp sigma hsigma)‖ ≤ 1 := by
  calc
    _ ≤ ‖infiniteMobiusSignedWeightLp sigma hsigma‖ :=
      norm_mobiusClockSoninMarkedProducer_le
        a c d r hc hcd hr N sigma u hsigma hu _
    _ = 1 := norm_infiniteMobiusSignedWeightLp hsigma

/-- On the actual Möbius source, the marked reflection-odd vector port vanishes
cofinally before any scalar reporter is applied. -/
theorem tendsto_norm_actual_mobiusClockSoninMarkedOddPort
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    Tendsto (fun N =>
      ‖mobiusClockSoninMarkedOddPort
        (mobiusClockSoninMarkedProducer
          a c d r hc hcd hr N sigma u hsigma hu
          (infiniteMobiusSignedWeightLp sigma hsigma))‖)
      atTop (nhds 0) := by
  have hcomm := tendsto_norm_soninCofinalComplexClockCommutator_apply
    a c d r ha hc hcd hda hr harc sigma u hsigma hu
      (infiniteMobiusSignedWeightLp sigma hsigma)
  have hscaled := hcomm.const_mul (1 / 2 : ℝ)
  convert hscaled using 1
  · funext N
    rw [mobiusClockSoninMarkedOddPort_producer, norm_smul]
    norm_num
  · norm_num

/-- Fixed lawful geometry and clock used to expose a completely closed instance
of the marked producer package. -/
def canonicalMobiusClockSoninMarkedProducer (N : ℕ) :
    MobiusClockSourceL2 →L[ℂ]
      WithLp 2 (MobiusClockSourceL2 × MobiusClockSourceL2) :=
  mobiusClockSoninMarkedProducerCLM
    4 2 3 3 (by norm_num) (by norm_num) (by norm_num)
    N 2 1 (by norm_num) (by norm_num)

/-- Actual normalized Möbius source at the canonical clock parameter. -/
def canonicalMobiusClockMarkedSource : MobiusClockSourceL2 :=
  infiniteMobiusSignedWeightLp 2 (by norm_num)

/-- Premise-free capstone: the actual marked source is produced contractively,
the two vector ports conserve its marked energy exactly, and its odd port
vanishes cofinally before scalarization. -/
theorem canonicalMobiusClockSoninMarkedProducer_closed :
    (∀ N,
      ‖canonicalMobiusClockSoninMarkedProducer N
        canonicalMobiusClockMarkedSource‖ ≤ 1) ∧
    (∀ N,
      ‖mobiusClockSoninMarkedEvenPort
          (canonicalMobiusClockSoninMarkedProducer N
            canonicalMobiusClockMarkedSource)‖ ^ 2 +
        ‖mobiusClockSoninMarkedOddPort
          (canonicalMobiusClockSoninMarkedProducer N
            canonicalMobiusClockMarkedSource)‖ ^ 2 =
        ‖canonicalMobiusClockSoninMarkedProducer N
          canonicalMobiusClockMarkedSource‖ ^ 2) ∧
    Tendsto (fun N =>
      ‖mobiusClockSoninMarkedOddPort
        (canonicalMobiusClockSoninMarkedProducer N
          canonicalMobiusClockMarkedSource)‖)
      atTop (nhds 0) := by
  constructor
  · intro N
    simpa [canonicalMobiusClockSoninMarkedProducer,
      canonicalMobiusClockMarkedSource] using
      norm_actual_mobiusClockSoninMarkedProducer_le_one
        4 2 3 3 (by norm_num) (by norm_num) (by norm_num)
        N 2 1 (by norm_num) (by norm_num)
  constructor
  · intro N
    exact mobiusClockSoninMarkedPorts_energy _
  · simpa [canonicalMobiusClockSoninMarkedProducer,
      canonicalMobiusClockMarkedSource] using
      tendsto_norm_actual_mobiusClockSoninMarkedOddPort
        4 2 3 3 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        2 1 (by norm_num) (by norm_num)

end RHTower


