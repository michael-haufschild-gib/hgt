import GaloisForLFunctions.HTGeometry.RectangularVectorDiagonal
import GaloisForLFunctions.HTGeometry.RectangularWeakSchatten
import GaloisForLFunctions.RHTower.DeningerMobiusGammaSixNormalTransgression
import GaloisForLFunctions.RHTower.DeningerGammaSixShellPrincipalIdeal
import GaloisForLFunctions.RHTower.L2HilbertTensorProduct

open Complex Real MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Completed Hilbert tensor square of the physical logarithmic source. -/
abbrev DeningerGammaSixTensorSourceL2 :=
  Lp (α := ℝ × ℝ) ℂ 2 (volume.prod volume)

/-- Exact half-density remaining after countertransporting the first surviving
ordinary-integer label `6` back to the origin. -/
def deningerGammaSixHalfWeight (m : MobiusHonestDepth) : ℝ :=
  (6 : ℝ) ^ (-((m : ℝ) / 2))

theorem deningerGammaSixHalfWeight_pos (m : MobiusHonestDepth) :
    0 < deningerGammaSixHalfWeight m := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem deningerGammaSixHalfWeight_sq (m : MobiusHonestDepth) :
    deningerGammaSixHalfWeight m * deningerGammaSixHalfWeight m =
      (1 / 6 : ℝ) ^ (m : ℕ) := by
  rw [deningerGammaSixHalfWeight, ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  have hleft : -((m : ℝ) / 2) + -((m : ℝ) / 2) = -(m : ℝ) := by ring
  rw [hleft, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  simp [one_div]

/-- Full post-six source after unitary countertransport, expressed in its
exact normal form. -/
def deningerGammaSixCountertransportedSource (m : MobiusHonestDepth) :
    MobiusThetaSourceL2 :=
  ((deningerGammaSixHalfWeight m : ℝ) : ℂ) •
    mobiusThetaPrimeNormalResidual 6 m

/-- First surviving Gamma-six atom after countertransport. -/
def deningerGammaSixCountertransportedLeadingSource (m : MobiusHonestDepth) :
    MobiusThetaSourceL2 :=
  ((deningerGammaSixHalfWeight m : ℝ) : ℂ) • xiThetaSourceL2

/-- Complete post-six tail after countertransport. -/
def deningerGammaSixCountertransportedTail (m : MobiusHonestDepth) :
    MobiusThetaSourceL2 :=
  ((deningerGammaSixHalfWeight m : ℝ) : ℂ) •
    ∑' k : ℕ, mobiusThetaPrimeNormalTailTerm 6 m k

theorem deningerGammaSixCountertransportedSource_eq_leading_add_tail
    (m : MobiusHonestDepth) :
    deningerGammaSixCountertransportedSource m =
      deningerGammaSixCountertransportedLeadingSource m +
        deningerGammaSixCountertransportedTail m := by
  rw [deningerGammaSixCountertransportedSource,
    mobiusThetaPrimeNormalResidual, moebius_six]
  simp only [Int.cast_one, Complex.ofReal_one, one_smul]
  rw [smul_add]
  rfl

/-- Literal countertransport relation to the finite-corrected complete source:
only the unitary translation is applied; the half-density is forced by the
normal transport theorem. -/
theorem additiveTranslationUnitary_deningerGammaSixCompleteSource
    (m : MobiusHonestDepth) :
    MellinL2.additiveTranslationUnitary
        (((m : ℝ) * Real.log 6) * MellinL2.spectralNormalization)
        (deningerGammaSixCompleteSource m) =
      deningerGammaSixCountertransportedSource m := by
  have hnormal := deningerGammaSixNormal_completeSource m
  rw [deningerGammaSixNormalCLM_apply] at hnormal
  let a : ℝ := (6 : ℝ) ^ ((m : ℝ) / 2)
  have ha : a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hweight : deningerGammaSixHalfWeight m = a⁻¹ := by
    rw [deningerGammaSixHalfWeight,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6)]
  have hnormal' : (((a : ℝ) : ℂ) •
      MellinL2.additiveTranslationUnitary
        (((m : ℝ) * Real.log 6) * MellinL2.spectralNormalization)
        (deningerGammaSixCompleteSource m)) =
      mobiusThetaPrimeNormalResidual 6 m := by
    simpa [a] using hnormal
  rw [deningerGammaSixCountertransportedSource, hweight]
  calc
    MellinL2.additiveTranslationUnitary
        (((m : ℝ) * Real.log 6) * MellinL2.spectralNormalization)
        (deningerGammaSixCompleteSource m) =
      ((a⁻¹ : ℝ) : ℂ) •
        (((a : ℝ) : ℂ) •
          MellinL2.additiveTranslationUnitary
            (((m : ℝ) * Real.log 6) * MellinL2.spectralNormalization)
            (deningerGammaSixCompleteSource m)) := by
      rw [smul_smul]
      have hscalar : ((a⁻¹ : ℝ) : ℂ) * ((a : ℝ) : ℂ) = 1 := by
        exact_mod_cast inv_mul_cancel₀ ha
      rw [hscalar, one_smul]
    _ = ((a⁻¹ : ℝ) : ℂ) • mobiusThetaPrimeNormalResidual 6 m := by
      exact congrArg (fun z : MobiusThetaSourceL2 =>
        ((a⁻¹ : ℝ) : ℂ) • z) hnormal'

/-- Countertransported completed tensor square. -/
def deningerGammaSixSourceTensorSquare (m : MobiusHonestDepth) :
    DeningerGammaSixTensorSourceL2 :=
  l2SeparatedProduct
    (deningerGammaSixCountertransportedSource m)
    (deningerGammaSixCountertransportedSource m)

/-- Tensor square of the first surviving atom at depth `m`. -/
def deningerGammaSixSourceTensorPrincipal (m : MobiusHonestDepth) :
    DeningerGammaSixTensorSourceL2 :=
  l2SeparatedProduct
    (deningerGammaSixCountertransportedLeadingSource m)
    (deningerGammaSixCountertransportedLeadingSource m)

/-- Complete tensor-square correction beyond the first surviving atom. -/
def deningerGammaSixSourceTensorRemainder (m : MobiusHonestDepth) :
    DeningerGammaSixTensorSourceL2 :=
  deningerGammaSixSourceTensorSquare m -
    deningerGammaSixSourceTensorPrincipal m

/-- Fixed nonzero tensor direction selected by the ordinary integer six. -/
def deningerGammaSixLeadingTensorVector : DeningerGammaSixTensorSourceL2 :=
  l2SeparatedProduct xiThetaSourceL2 xiThetaSourceL2

theorem deningerGammaSixLeadingTensorVector_ne_zero :
    deningerGammaSixLeadingTensorVector ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  rw [deningerGammaSixLeadingTensorVector,
    l2SeparatedProduct_norm, norm_zero] at hnorm
  exact xiThetaSourceL2_ne_zero (norm_eq_zero.mp (mul_self_eq_zero.mp hnorm))

theorem deningerGammaSixSourceTensorPrincipal_eq (m : MobiusHonestDepth) :
    deningerGammaSixSourceTensorPrincipal m =
      (((1 / 6 : ℝ) ^ (m : ℕ) : ℝ) : ℂ) •
        deningerGammaSixLeadingTensorVector := by
  change l2SeparatedProduct
      (((deningerGammaSixHalfWeight m : ℝ) : ℂ) • xiThetaSourceL2)
      (((deningerGammaSixHalfWeight m : ℝ) : ℂ) • xiThetaSourceL2) = _
  change (l2SeparatedProductContinuousBilinear
      (((deningerGammaSixHalfWeight m : ℝ) : ℂ) • xiThetaSourceL2))
      (((deningerGammaSixHalfWeight m : ℝ) : ℂ) • xiThetaSourceL2) = _
  rw [map_smul]
  rw [map_smul]
  rw [smul_apply, smul_smul]
  change (((deningerGammaSixHalfWeight m : ℝ) : ℂ) *
      ((deningerGammaSixHalfWeight m : ℝ) : ℂ)) •
      deningerGammaSixLeadingTensorVector = _
  congr 1
  exact_mod_cast deningerGammaSixHalfWeight_sq m

theorem deningerGammaSixSourceTensorRemainder_eq (m : MobiusHonestDepth) :
    deningerGammaSixSourceTensorRemainder m =
      l2SeparatedProduct
          (deningerGammaSixCountertransportedLeadingSource m)
          (deningerGammaSixCountertransportedTail m) +
        l2SeparatedProduct
          (deningerGammaSixCountertransportedTail m)
          (deningerGammaSixCountertransportedLeadingSource m) +
        l2SeparatedProduct
          (deningerGammaSixCountertransportedTail m)
          (deningerGammaSixCountertransportedTail m) := by
  rw [deningerGammaSixSourceTensorRemainder,
    deningerGammaSixSourceTensorSquare,
    deningerGammaSixCountertransportedSource_eq_leading_add_tail]
  change (l2SeparatedProductContinuousBilinear (_ + _)) (_ + _) -
      l2SeparatedProduct _ _ = _
  simp only [map_add, add_apply,
    l2SeparatedProductContinuousBilinear_apply]
  abel

def deningerGammaSixTailRate (m : MobiusHonestDepth) : ℝ :=
  ((6 : ℝ) / 7) ^ (((m : ℝ) - 3) / 2)

def deningerGammaSixTailConstant : ℝ :=
  ∑' k : ℕ, mobiusThetaPrimeNormalMajorant 6 k

theorem deningerGammaSixTailConstant_nonneg :
    0 ≤ deningerGammaSixTailConstant := by
  exact tsum_nonneg fun k => by
    unfold mobiusThetaPrimeNormalMajorant
    positivity

theorem norm_deningerGammaSixCountertransportedTail_le
    (m : MobiusHonestDepth) :
    ‖deningerGammaSixCountertransportedTail m‖ ≤
      deningerGammaSixHalfWeight m * deningerGammaSixTailRate m *
        deningerGammaSixTailConstant := by
  rw [deningerGammaSixCountertransportedTail, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerGammaSixHalfWeight_pos m)]
  have htail := norm_tsum_mobiusThetaPrimeNormalTailTerm_le_geometricMajorant
    (p := 6) (m := (m : ℕ)) (by omega) m.2
  change deningerGammaSixHalfWeight m * ‖∑' k : ℕ,
      mobiusThetaPrimeNormalTailTerm 6 m k‖ ≤ _
  simpa [deningerGammaSixTailRate, deningerGammaSixTailConstant,
    mul_assoc] using
    (mul_le_mul_of_nonneg_left htail
      (deningerGammaSixHalfWeight_pos m).le)

theorem norm_deningerGammaSixCountertransportedLeadingSource
    (m : MobiusHonestDepth) :
    ‖deningerGammaSixCountertransportedLeadingSource m‖ =
      deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖ := by
  rw [deningerGammaSixCountertransportedLeadingSource, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerGammaSixHalfWeight_pos m)]

theorem norm_deningerGammaSixSourceTensorRemainder_le
    (m : MobiusHonestDepth) :
    ‖deningerGammaSixSourceTensorRemainder m‖ ≤
      deningerGammaSixHalfWeight m ^ 2 *
        (2 * ‖xiThetaSourceL2‖ *
            (deningerGammaSixTailRate m * deningerGammaSixTailConstant) +
          (deningerGammaSixTailRate m * deningerGammaSixTailConstant) ^ 2) := by
  rw [deningerGammaSixSourceTensorRemainder_eq]
  calc
    ‖l2SeparatedProduct
          (deningerGammaSixCountertransportedLeadingSource m)
          (deningerGammaSixCountertransportedTail m) +
        l2SeparatedProduct
          (deningerGammaSixCountertransportedTail m)
          (deningerGammaSixCountertransportedLeadingSource m) +
        l2SeparatedProduct
          (deningerGammaSixCountertransportedTail m)
          (deningerGammaSixCountertransportedTail m)‖ ≤
      ‖l2SeparatedProduct
          (deningerGammaSixCountertransportedLeadingSource m)
          (deningerGammaSixCountertransportedTail m)‖ +
        ‖l2SeparatedProduct
          (deningerGammaSixCountertransportedTail m)
          (deningerGammaSixCountertransportedLeadingSource m)‖ +
        ‖l2SeparatedProduct
          (deningerGammaSixCountertransportedTail m)
          (deningerGammaSixCountertransportedTail m)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = 2 * ‖deningerGammaSixCountertransportedLeadingSource m‖ *
          ‖deningerGammaSixCountertransportedTail m‖ +
        ‖deningerGammaSixCountertransportedTail m‖ ^ 2 := by
      simp only [l2SeparatedProduct_norm]
      ring
    _ ≤ 2 * (deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖) *
          (deningerGammaSixHalfWeight m *
            (deningerGammaSixTailRate m * deningerGammaSixTailConstant)) +
        (deningerGammaSixHalfWeight m *
          (deningerGammaSixTailRate m * deningerGammaSixTailConstant)) ^ 2 := by
      rw [norm_deningerGammaSixCountertransportedLeadingSource]
      have ht := norm_deningerGammaSixCountertransportedTail_le m
      have ht' : ‖deningerGammaSixCountertransportedTail m‖ ≤
          deningerGammaSixHalfWeight m *
            (deningerGammaSixTailRate m * deningerGammaSixTailConstant) := by
        simpa [mul_assoc] using ht
      have hrate : 0 ≤ deningerGammaSixTailRate m := by
        unfold deningerGammaSixTailRate
        positivity
      have htailBound : 0 ≤ deningerGammaSixHalfWeight m *
          (deningerGammaSixTailRate m * deningerGammaSixTailConstant) :=
        mul_nonneg (deningerGammaSixHalfWeight_pos m).le
          (mul_nonneg hrate deningerGammaSixTailConstant_nonneg)
      have hcoeff : 0 ≤ 2 *
          (deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (deningerGammaSixHalfWeight_pos m).le (norm_nonneg _))
      exact add_le_add
        (mul_le_mul_of_nonneg_left ht' hcoeff)
        (by simpa [pow_two] using
          mul_self_le_mul_self (norm_nonneg _) ht')
    _ = deningerGammaSixHalfWeight m ^ 2 *
        (2 * ‖xiThetaSourceL2‖ *
            (deningerGammaSixTailRate m * deningerGammaSixTailConstant) +
          (deningerGammaSixTailRate m * deningerGammaSixTailConstant) ^ 2) := by
      ring

/-- Canonical parametrization of all honest depths by excess over three. -/
def deningerGammaSixHonestDepth (j : ℕ) : MobiusHonestDepth :=
  ⟨j + 3, by omega⟩

@[simp] theorem deningerGammaSixHonestDepth_val (j : ℕ) :
    (deningerGammaSixHonestDepth j : ℕ) = j + 3 := rfl

theorem deningerGammaSixTailRate_honestDepth (j : ℕ) :
    deningerGammaSixTailRate (deningerGammaSixHonestDepth j) =
      ((6 : ℝ) / 7) ^ ((j : ℝ) / 2) := by
  rw [deningerGammaSixTailRate]
  change ((6 : ℝ) / 7) ^ ((((j + 3 : ℕ) : ℝ) - 3) / 2) = _
  congr 1
  push_cast
  ring

theorem deningerGammaSix_shellWeightedRemainder_le (j : ℕ) :
    (6 : ℝ) ^ (j + 3) *
        ‖deningerGammaSixSourceTensorRemainder
          (deningerGammaSixHonestDepth j)‖ ≤
      2 * ‖xiThetaSourceL2‖ * deningerGammaSixTailConstant *
          (((6 : ℝ) / 7) ^ ((j : ℝ) / 2)) +
        deningerGammaSixTailConstant ^ 2 *
          (((6 : ℝ) / 7) ^ ((j : ℝ) / 2)) ^ 2 := by
  let m := deningerGammaSixHonestDepth j
  have hrem := norm_deningerGammaSixSourceTensorRemainder_le m
  have hmul := mul_le_mul_of_nonneg_left hrem
    (by positivity : 0 ≤ (6 : ℝ) ^ (j + 3))
  rw [show j + 3 = (m : ℕ) by rfl] at hmul
  rw [pow_two (deningerGammaSixHalfWeight m),
    deningerGammaSixHalfWeight_sq] at hmul
  have hcancel : (6 : ℝ) ^ (m : ℕ) * (1 / 6 : ℝ) ^ (m : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hcancel, one_mul] at hmul
  rw [deningerGammaSixTailRate_honestDepth] at hmul
  calc
    (6 : ℝ) ^ (j + 3) *
        ‖deningerGammaSixSourceTensorRemainder m‖ ≤
      2 * ‖xiThetaSourceL2‖ *
            (((6 : ℝ) / 7) ^ ((j : ℝ) / 2) * deningerGammaSixTailConstant) +
        (((6 : ℝ) / 7) ^ ((j : ℝ) / 2) * deningerGammaSixTailConstant) ^ 2 :=
      hmul
    _ = 2 * ‖xiThetaSourceL2‖ * deningerGammaSixTailConstant *
          (((6 : ℝ) / 7) ^ ((j : ℝ) / 2)) +
        deningerGammaSixTailConstant ^ 2 *
          (((6 : ℝ) / 7) ^ ((j : ℝ) / 2)) ^ 2 := by ring

theorem summable_deningerGammaSixTailRate_honestDepth :
    Summable (fun j : ℕ =>
      deningerGammaSixTailRate (deningerGammaSixHonestDepth j)) := by
  have hbase_nonneg : 0 ≤ ((6 : ℝ) / 7) ^ (1 / 2 : ℝ) := by positivity
  have hbase_lt : ((6 : ℝ) / 7) ^ (1 / 2 : ℝ) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hgeom := summable_geometric_of_lt_one hbase_nonneg hbase_lt
  rw [show (fun j : ℕ => deningerGammaSixTailRate
      (deningerGammaSixHonestDepth j)) =
      (fun j : ℕ => ((6 : ℝ) / 7) ^ ((j : ℝ) / 2)) by
        funext j
        exact deningerGammaSixTailRate_honestDepth j]
  convert hgeom using 1
  funext j
  rw [← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (6 : ℝ) / 7)]
  congr 1
  ring

theorem summable_sq_deningerGammaSixTailRate_honestDepth :
    Summable (fun j : ℕ =>
      deningerGammaSixTailRate (deningerGammaSixHonestDepth j) ^ 2) := by
  apply summable_deningerGammaSixTailRate_honestDepth.of_nonneg_of_le
  · intro j
    positivity
  · intro j
    have hnonneg : 0 ≤ deningerGammaSixTailRate
        (deningerGammaSixHonestDepth j) := by
      unfold deningerGammaSixTailRate
      positivity
    have hle : deningerGammaSixTailRate
        (deningerGammaSixHonestDepth j) ≤ 1 := by
      rw [deningerGammaSixTailRate_honestDepth]
      exact Real.rpow_le_one
        (by norm_num : (0 : ℝ) ≤ (6 : ℝ) / 7)
        (by norm_num : (6 : ℝ) / 7 ≤ 1)
        (by positivity : 0 ≤ (j : ℝ) / 2)
    rw [pow_two]
    exact mul_le_of_le_one_right hnonneg hle

/-- **Trace-order remainder theorem before shell replication.**  Multiplicity
`6^m` times the exact tensor-square remainder is summable over every honest
depth. -/
theorem summable_deningerGammaSix_shellWeightedRemainder :
    Summable (fun j : ℕ =>
      (6 : ℝ) ^ (j + 3) *
        ‖deningerGammaSixSourceTensorRemainder
          (deningerGammaSixHonestDepth j)‖) := by
  have hfirst := summable_deningerGammaSixTailRate_honestDepth.mul_left
    (2 * ‖xiThetaSourceL2‖ * deningerGammaSixTailConstant)
  have hsecond := summable_sq_deningerGammaSixTailRate_honestDepth.mul_left
    (deningerGammaSixTailConstant ^ 2)
  have hmajor := hfirst.add hsecond
  apply hmajor.of_nonneg_of_le
  · intro j
    positivity
  · intro j
    simpa [deningerGammaSixTailRate_honestDepth] using
      deningerGammaSix_shellWeightedRemainder_le j

theorem three_le_deningerGammaSixShellDepth (n : ℕ) :
    3 ≤ deningerGammaSixShellDepth n := by
  rw [deningerGammaSixShellDepth]
  apply Nat.le_log_of_pow_le (by norm_num)
  norm_num

/-- Every ordinary-integer shell coordinate determines an honest source
depth, without a cutoff convention. -/
def deningerGammaSixShellHonestDepth (n : ℕ) : MobiusHonestDepth :=
  ⟨deningerGammaSixShellDepth n, three_le_deningerGammaSixShellDepth n⟩

@[simp] theorem deningerGammaSixShellHonestDepth_val (n : ℕ) :
    (deningerGammaSixShellHonestDepth n : ℕ) =
      deningerGammaSixShellDepth n := rfl

def deningerGammaSixDepthFiber (m : ℕ) : Set ℕ :=
  {n | deningerGammaSixShellDepth n = m}

theorem existsUnique_mem_deningerGammaSixDepthFiber (n : ℕ) :
    ∃! m : ℕ, n ∈ deningerGammaSixDepthFiber m := by
  refine ⟨deningerGammaSixShellDepth n, rfl, ?_⟩
  intro m hm
  exact hm.symm

theorem deningerGammaSixDepthFiber_eq_shellCoordinates
    {m : ℕ} (hm : 3 ≤ m) :
    deningerGammaSixDepthFiber m =
      (deningerGammaSixShellCoordinates m : Set ℕ) := by
  ext n
  rw [deningerGammaSixDepthFiber, Set.mem_setOf_eq,
    Finset.mem_coe, deningerGammaSixShellCoordinates, Finset.mem_Ico]
  constructor
  · intro hdepth
    have hlo : 6 ^ m ≤ n + 216 := by
      have h := Nat.pow_log_le_self 6 (by omega : n + 216 ≠ 0)
      rw [← hdepth]
      exact h
    have hhi : n + 216 < 6 ^ (m + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 6) (n + 216)
      change Nat.log 6 (n + 216) = m at hdepth
      rw [hdepth] at h
      simpa [Nat.succ_eq_add_one] using h
    have hpow := deningerGammaSix_pow_three_le hm
    have hpow' : 216 ≤ 6 ^ (m + 1) := hpow.trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m))
    omega
  · intro hn
    exact deningerGammaSixShellDepth_eq_of_shell
      (by
        have hpow := deningerGammaSix_pow_three_le hm
        omega)
      (by
        have hpow := deningerGammaSix_pow_three_le hm
        have hpow' : 216 ≤ 6 ^ (m + 1) := hpow.trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m))
        omega)

theorem deningerGammaSixDepthFiber_eq_empty {m : ℕ} (hm : m < 3) :
    deningerGammaSixDepthFiber m = ∅ := by
  ext n
  simp only [deningerGammaSixDepthFiber, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  exact (hm.trans_le (three_le_deningerGammaSixShellDepth n)).ne.symm

/-- Exact tensor-square correction repeated on every ordinary-integer
coordinate of its Gamma-six shell. -/
def deningerGammaSixSourceTensorRemainderColumn (n : ℕ) :
    DeningerGammaSixTensorSourceL2 :=
  deningerGammaSixSourceTensorRemainder
    (deningerGammaSixShellHonestDepth n)

theorem deningerGammaSixDepthFiber_tsum_remainderColumn
    {m : ℕ} (hm : 3 ≤ m) :
    (∑' n : deningerGammaSixDepthFiber m,
        ‖deningerGammaSixSourceTensorRemainderColumn n‖) =
      5 * (6 : ℝ) ^ m *
        ‖deningerGammaSixSourceTensorRemainder ⟨m, hm⟩‖ := by
  rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
  letI : Fintype ((deningerGammaSixShellCoordinates m : Set ℕ)) :=
    (Finset.finite_toSet (deningerGammaSixShellCoordinates m)).fintype
  rw [tsum_fintype]
  calc
    ∑ n : (deningerGammaSixShellCoordinates m : Set ℕ),
        ‖deningerGammaSixSourceTensorRemainderColumn n‖ =
      ∑ _n : (deningerGammaSixShellCoordinates m : Set ℕ),
        ‖deningerGammaSixSourceTensorRemainder ⟨m, hm⟩‖ := by
      apply Finset.sum_congr rfl
      intro n _hn
      have hdepthNat : deningerGammaSixShellDepth (n : ℕ) = m := by
        change (n : ℕ) ∈ deningerGammaSixDepthFiber m
        rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
        exact n.property
      have hdepth : deningerGammaSixShellHonestDepth n = ⟨m, hm⟩ := by
        apply Subtype.ext
        exact hdepthNat
      change ‖deningerGammaSixSourceTensorRemainder
          (deningerGammaSixShellHonestDepth n)‖ = _
      rw [hdepth]
    _ = (Fintype.card ((deningerGammaSixShellCoordinates m : Set ℕ)) : ℝ) *
        ‖deningerGammaSixSourceTensorRemainder ⟨m, hm⟩‖ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = ((deningerGammaSixShellCoordinates m).card : ℝ) *
        ‖deningerGammaSixSourceTensorRemainder ⟨m, hm⟩‖ := by
      have hcard : Fintype.card
          ((deningerGammaSixShellCoordinates m : Set ℕ)) =
          (deningerGammaSixShellCoordinates m).card := by
        calc
          Fintype.card ((deningerGammaSixShellCoordinates m : Set ℕ)) =
              Nat.card ((deningerGammaSixShellCoordinates m : Set ℕ)) :=
            Nat.card_eq_fintype_card.symm
          _ = (deningerGammaSixShellCoordinates m : Set ℕ).ncard :=
            Nat.card_coe_set_eq _
          _ = (deningerGammaSixShellCoordinates m).card :=
            Set.ncard_coe_finset _
      rw [hcard]
    _ = 5 * (6 : ℝ) ^ m *
        ‖deningerGammaSixSourceTensorRemainder ⟨m, hm⟩‖ := by
      rw [deningerGammaSixShellCoordinates_card hm]
      push_cast
      ring

/-- **Ordinary-integer trace-order theorem.**  After exact shell
replication, the full corrected tensor-square source differs from its leading
Gamma-six atom by an `ell^1` family of Hilbert vectors. -/
theorem summable_norm_deningerGammaSixSourceTensorRemainderColumn :
    Summable (fun n : ℕ =>
      ‖deningerGammaSixSourceTensorRemainderColumn n‖) := by
  rw [summable_partition (fun n => norm_nonneg
      (deningerGammaSixSourceTensorRemainderColumn n))
    existsUnique_mem_deningerGammaSixDepthFiber]
  constructor
  · intro m
    by_cases hm : 3 ≤ m
    · rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
      exact (hasSum_fintype (fun n :
        (deningerGammaSixShellCoordinates m : Set ℕ) =>
          ‖deningerGammaSixSourceTensorRemainderColumn n‖)).summable
    · rw [deningerGammaSixDepthFiber_eq_empty (by omega)]
      exact summable_empty
  · apply (summable_nat_add_iff 3).1
    have hscaled := summable_deningerGammaSix_shellWeightedRemainder.mul_left 5
    exact hscaled.congr fun j => by
      rw [deningerGammaSixDepthFiber_tsum_remainderColumn
        (by omega : 3 ≤ j + 3)]
      simp only [deningerGammaSixHonestDepth]
      ring

theorem deningerGammaSixTailRate_le_one (m : MobiusHonestDepth) :
    deningerGammaSixTailRate m ≤ 1 := by
  unfold deningerGammaSixTailRate
  exact Real.rpow_le_one (by norm_num) (by norm_num) (by
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast m.2
    linarith)

theorem norm_mobiusThetaPrimeNormalResidual_six_le
    (m : MobiusHonestDepth) :
    ‖mobiusThetaPrimeNormalResidual 6 m‖ ≤
      ‖xiThetaSourceL2‖ + deningerGammaSixTailConstant := by
  rw [mobiusThetaPrimeNormalResidual, moebius_six]
  simp only [Int.cast_one, Complex.ofReal_one, one_smul]
  calc
    ‖xiThetaSourceL2 +
        ∑' k : ℕ, mobiusThetaPrimeNormalTailTerm 6 m k‖ ≤
      ‖xiThetaSourceL2‖ +
        ‖∑' k : ℕ, mobiusThetaPrimeNormalTailTerm 6 m k‖ := norm_add_le _ _
    _ ≤ ‖xiThetaSourceL2‖ +
        deningerGammaSixTailRate m * deningerGammaSixTailConstant := by
      gcongr
      simpa [deningerGammaSixTailRate, deningerGammaSixTailConstant] using
        (norm_tsum_mobiusThetaPrimeNormalTailTerm_le_geometricMajorant
          (p := 6) (m := (m : ℕ)) (by omega) m.2)
    _ ≤ ‖xiThetaSourceL2‖ + deningerGammaSixTailConstant := by
      gcongr
      exact mul_le_of_le_one_left deningerGammaSixTailConstant_nonneg
        (deningerGammaSixTailRate_le_one m)

/-- Undamped tensor direction left after factoring out the exact Gamma-six
principal shell weight. -/
def deningerGammaSixNormalTensorDirection (m : MobiusHonestDepth) :
    DeningerGammaSixTensorSourceL2 :=
  l2SeparatedProduct
    (mobiusThetaPrimeNormalResidual 6 m)
    (mobiusThetaPrimeNormalResidual 6 m)

theorem norm_deningerGammaSixNormalTensorDirection_le
    (m : MobiusHonestDepth) :
    ‖deningerGammaSixNormalTensorDirection m‖ ≤
      (‖xiThetaSourceL2‖ + deningerGammaSixTailConstant) ^ 2 := by
  rw [deningerGammaSixNormalTensorDirection, l2SeparatedProduct_norm, pow_two]
  exact mul_self_le_mul_self (norm_nonneg _)
    (norm_mobiusThetaPrimeNormalResidual_six_le m)

theorem deningerGammaSixSourceTensorSquare_eq_normalDirection
    (m : MobiusHonestDepth) :
    deningerGammaSixSourceTensorSquare m =
      (((1 / 6 : ℝ) ^ (m : ℕ) : ℝ) : ℂ) •
        deningerGammaSixNormalTensorDirection m := by
  change l2SeparatedProduct
      (((deningerGammaSixHalfWeight m : ℝ) : ℂ) •
        mobiusThetaPrimeNormalResidual 6 m)
      (((deningerGammaSixHalfWeight m : ℝ) : ℂ) •
        mobiusThetaPrimeNormalResidual 6 m) = _
  change (l2SeparatedProductContinuousBilinear
      (((deningerGammaSixHalfWeight m : ℝ) : ℂ) •
        mobiusThetaPrimeNormalResidual 6 m))
      (((deningerGammaSixHalfWeight m : ℝ) : ℂ) •
        mobiusThetaPrimeNormalResidual 6 m) = _
  rw [map_smul, map_smul, smul_apply, smul_smul]
  change (((deningerGammaSixHalfWeight m : ℝ) : ℂ) *
      ((deningerGammaSixHalfWeight m : ℝ) : ℂ)) •
      deningerGammaSixNormalTensorDirection m = _
  congr 1
  exact_mod_cast deningerGammaSixHalfWeight_sq m

def deningerGammaSixNormalTensorDirectionColumn (n : ℕ) :
    DeningerGammaSixTensorSourceL2 :=
  deningerGammaSixNormalTensorDirection
    (deningerGammaSixShellHonestDepth n)

theorem norm_deningerGammaSixNormalTensorDirectionColumn_le (n : ℕ) :
    ‖deningerGammaSixNormalTensorDirectionColumn n‖ ≤
      (‖xiThetaSourceL2‖ + deningerGammaSixTailConstant) ^ 2 :=
  norm_deningerGammaSixNormalTensorDirection_le _

theorem deningerGammaSixShellEigenvalue_le_one (n : ℕ) :
    deningerGammaSixShellEigenvalue n ≤ 1 := by
  unfold deningerGammaSixShellEigenvalue
  exact pow_le_one₀ (by norm_num) (by norm_num)

def deningerGammaSixLeadingTensorEmbedding :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  vectorDiagonalOperator
    (fun _n : ℕ => deningerGammaSixLeadingTensorVector)
    (norm_nonneg deningerGammaSixLeadingTensorVector)
    (fun _n => le_rfl)

def deningerGammaSixNormalTensorSynthesis :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  vectorDiagonalOperator deningerGammaSixNormalTensorDirectionColumn
    (sq_nonneg (‖xiThetaSourceL2‖ + deningerGammaSixTailConstant))
    norm_deningerGammaSixNormalTensorDirectionColumn_le

/-- Shell amplification of the first surviving tensor atom. -/
def deningerGammaSixSourceTensorPrincipalOperator :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  deningerGammaSixLeadingTensorEmbedding ∘L
    deningerGammaSixShellPrincipalOperator

/-- Shell amplification of the complete corrected tensor-square source. -/
def deningerGammaSixFullSourceTensorOperator :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  deningerGammaSixNormalTensorSynthesis ∘L
    deningerGammaSixShellPrincipalOperator

def deningerGammaSixSourceTensorRemainderTraceBound : ℝ :=
  ∑' n : ℕ, ‖deningerGammaSixSourceTensorRemainderColumn n‖

theorem deningerGammaSixSourceTensorRemainderTraceBound_nonneg :
    0 ≤ deningerGammaSixSourceTensorRemainderTraceBound :=
  tsum_nonneg fun _n => norm_nonneg _

theorem norm_deningerGammaSixSourceTensorRemainderColumn_le_traceBound
    (_n : ℕ) :
    ‖deningerGammaSixSourceTensorRemainderColumn _n‖ ≤
      deningerGammaSixSourceTensorRemainderTraceBound := by
  exact summable_norm_deningerGammaSixSourceTensorRemainderColumn.le_tsum _n
    (fun k _hk => norm_nonneg _)

/-- Shell amplification of the complete tensor-square correction. -/
def deningerGammaSixSourceTensorRemainderOperator :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  vectorDiagonalOperator deningerGammaSixSourceTensorRemainderColumn
    deningerGammaSixSourceTensorRemainderTraceBound_nonneg
    norm_deningerGammaSixSourceTensorRemainderColumn_le_traceBound

theorem deningerGammaSixShellPrincipalOperator_apply
    (x : EllTwo) (n : ℕ) :
    deningerGammaSixShellPrincipalOperator x n =
      ((deningerGammaSixShellEigenvalue n : ℝ) : ℂ) * x n := by
  rw [deningerGammaSixShellPrincipalOperator,
    deningerGammaSixShellPowerOperator,
    antitoneDiagonalOperator, diagonalOperator_apply]
  change ((deningerGammaSixShellPowerWeight
      deningerGammaSixOneExponent n : ℝ) : ℂ) * x n = _
  rw [show deningerGammaSixShellPowerWeight
      deningerGammaSixOneExponent n = deningerGammaSixShellEigenvalue n by
    exact congrFun deningerGammaSixShellPowerWeight_one n]

@[simp] theorem deningerGammaSixSourceTensorPrincipalOperator_apply
    (x : EllTwo) (n : ℕ) :
    deningerGammaSixSourceTensorPrincipalOperator x n =
      x n • deningerGammaSixSourceTensorPrincipal
        (deningerGammaSixShellHonestDepth n) := by
  rw [deningerGammaSixSourceTensorPrincipalOperator,
    ContinuousLinearMap.comp_apply,
    deningerGammaSixLeadingTensorEmbedding,
    vectorDiagonalOperator_apply,
    deningerGammaSixShellPrincipalOperator_apply,
    deningerGammaSixSourceTensorPrincipal_eq]
  rw [smul_smul]
  congr 1
  change ((deningerGammaSixShellEigenvalue n : ℝ) : ℂ) * x n =
    x n * ((deningerGammaSixShellEigenvalue n : ℝ) : ℂ)
  ring

@[simp] theorem deningerGammaSixFullSourceTensorOperator_apply
    (x : EllTwo) (n : ℕ) :
    deningerGammaSixFullSourceTensorOperator x n =
      x n • deningerGammaSixSourceTensorSquare
        (deningerGammaSixShellHonestDepth n) := by
  rw [deningerGammaSixFullSourceTensorOperator,
    ContinuousLinearMap.comp_apply,
    deningerGammaSixNormalTensorSynthesis,
    vectorDiagonalOperator_apply,
    deningerGammaSixShellPrincipalOperator_apply,
    deningerGammaSixSourceTensorSquare_eq_normalDirection]
  rw [smul_smul]
  congr 1
  change ((deningerGammaSixShellEigenvalue n : ℝ) : ℂ) * x n =
    x n * ((deningerGammaSixShellEigenvalue n : ℝ) : ℂ)
  ring

@[simp] theorem deningerGammaSixSourceTensorRemainderOperator_apply
    (x : EllTwo) (n : ℕ) :
    deningerGammaSixSourceTensorRemainderOperator x n =
      x n • deningerGammaSixSourceTensorRemainderColumn n := by
  rfl

/-- Exact operator-level decomposition of the full corrected source into its
weak principal symbol and trace-order correction. -/
theorem deningerGammaSixFullSourceTensorOperator_sub_principal :
    deningerGammaSixFullSourceTensorOperator -
        deningerGammaSixSourceTensorPrincipalOperator =
      deningerGammaSixSourceTensorRemainderOperator := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change deningerGammaSixFullSourceTensorOperator x n -
      deningerGammaSixSourceTensorPrincipalOperator x n =
    deningerGammaSixSourceTensorRemainderOperator x n
  rw [
    deningerGammaSixFullSourceTensorOperator_apply,
    deningerGammaSixSourceTensorPrincipalOperator_apply,
    deningerGammaSixSourceTensorRemainderOperator_apply]
  rw [deningerGammaSixSourceTensorRemainderColumn,
    deningerGammaSixSourceTensorRemainder, smul_sub]

theorem deningerGammaSixSourceTensorPrincipalOperator_eq_full_sub_remainder :
    deningerGammaSixSourceTensorPrincipalOperator =
      deningerGammaSixFullSourceTensorOperator -
        deningerGammaSixSourceTensorRemainderOperator := by
  rw [← deningerGammaSixFullSourceTensorOperator_sub_principal]
  abel

/-- The complete corrected shell remainder is a rectangular trace-class
operator, by an explicit nuclear column decomposition. -/
theorem deningerGammaSixSourceTensorRemainderOperator_traceClass :
    MemRectSchattenClass 1
      deningerGammaSixSourceTensorRemainderOperator := by
  exact vectorDiagonalOperator_memRectSchattenClass_one_of_summable_norm
    deningerGammaSixSourceTensorRemainderColumn
    deningerGammaSixSourceTensorRemainderTraceBound_nonneg
    norm_deningerGammaSixSourceTensorRemainderColumn_le_traceBound
    summable_norm_deningerGammaSixSourceTensorRemainderColumn

theorem deningerGammaSixSourceTensorPrincipalOperator_weak :
    MemRectWeakSchattenClass 1
      deningerGammaSixSourceTensorPrincipalOperator := by
  have hscalar : MemRectWeakSchattenClass 1
      deningerGammaSixShellPrincipalOperator :=
    (memRectWeakSchattenClass_iff_memWeakSchattenClass 1 _).2
      deningerGammaSixShellPrincipalOperator_weak
  exact hscalar.one_comp_left deningerGammaSixLeadingTensorEmbedding

theorem deningerGammaSixFullSourceTensorOperator_weak :
    MemRectWeakSchattenClass 1
      deningerGammaSixFullSourceTensorOperator := by
  have hscalar : MemRectWeakSchattenClass 1
      deningerGammaSixShellPrincipalOperator :=
    (memRectWeakSchattenClass_iff_memWeakSchattenClass 1 _).2
      deningerGammaSixShellPrincipalOperator_weak
  exact hscalar.one_comp_left deningerGammaSixNormalTensorSynthesis

/-- Canonical normalized coefficient reader of the nonzero leading tensor. -/
def deningerGammaSixLeadingTensorCoefficient :
    DeningerGammaSixTensorSourceL2 →L[ℂ] ℂ :=
  (((‖deningerGammaSixLeadingTensorVector‖ ^ 2 : ℝ) : ℂ)⁻¹) •
    innerSL ℂ deningerGammaSixLeadingTensorVector

theorem deningerGammaSixLeadingTensorCoefficient_leading :
    deningerGammaSixLeadingTensorCoefficient
      deningerGammaSixLeadingTensorVector = 1 := by
  rw [deningerGammaSixLeadingTensorCoefficient, smul_apply,
    innerSL_apply_apply, inner_self_eq_norm_sq_to_K]
  have hnorm : ‖deningerGammaSixLeadingTensorVector‖ ≠ 0 :=
    norm_ne_zero_iff.mpr deningerGammaSixLeadingTensorVector_ne_zero
  push_cast
  simp only [smul_eq_mul]
  have hnormC : (‖deningerGammaSixLeadingTensorVector‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnorm
  field_simp
  rfl

/-- Blockwise coefficient reader from the vector shell amplification back to
the scalar Gamma-six Green model. -/
def deningerGammaSixLeadingTensorReader :
    lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 →L[ℂ] EllTwo :=
  rectangularBlockOperator
    (fun _n : ℕ => deningerGammaSixLeadingTensorCoefficient)
    (norm_nonneg deningerGammaSixLeadingTensorCoefficient)
    (fun _n => le_rfl)

theorem deningerGammaSixLeadingTensorReader_comp_embedding :
    deningerGammaSixLeadingTensorReader ∘L
        deningerGammaSixLeadingTensorEmbedding =
      ContinuousLinearMap.id ℂ EllTwo := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [ContinuousLinearMap.comp_apply,
    deningerGammaSixLeadingTensorReader,
    deningerGammaSixLeadingTensorEmbedding,
    rectangularBlockOperator_apply, vectorDiagonalOperator_apply,
    map_smul, deningerGammaSixLeadingTensorCoefficient_leading]
  simp

theorem deningerGammaSixLeadingTensorReader_comp_principal :
    deningerGammaSixLeadingTensorReader ∘L
        deningerGammaSixSourceTensorPrincipalOperator =
      deningerGammaSixShellPrincipalOperator := by
  rw [deningerGammaSixSourceTensorPrincipalOperator,
    ← ContinuousLinearMap.comp_assoc,
    deningerGammaSixLeadingTensorReader_comp_embedding,
    ContinuousLinearMap.id_comp]

theorem deningerGammaSixSourceTensorPrincipalOperator_not_traceClass :
    ¬ MemRectSchattenClass 1
      deningerGammaSixSourceTensorPrincipalOperator := by
  intro htrace
  have hread := htrace.one_comp_left deningerGammaSixLeadingTensorReader
  rw [deningerGammaSixLeadingTensorReader_comp_principal] at hread
  exact deningerGammaSixShellPrincipalOperator_not_traceClass
    ((memRectSchattenClass_iff_memSchattenClass 1 _).1 hread)

theorem deningerGammaSixFullSourceTensorOperator_not_traceClass :
    ¬ MemRectSchattenClass 1 deningerGammaSixFullSourceTensorOperator := by
  intro htrace
  have hprincipal : MemRectSchattenClass 1
      deningerGammaSixSourceTensorPrincipalOperator := by
    rw [deningerGammaSixSourceTensorPrincipalOperator_eq_full_sub_remainder]
    exact htrace.one_sub
      deningerGammaSixSourceTensorRemainderOperator_traceClass
  exact deningerGammaSixSourceTensorPrincipalOperator_not_traceClass hprincipal

/-- **Full-source weak-trace principal class.**  The literal corrected
Gamma-six Möbius tensor square is weak trace class, is not trace class, and
differs from its first surviving atom by a trace-class operator. -/
theorem deningerGammaSix_fullSource_weakTracePrincipalClass :
    MemRectSchattenClass 1
        (deningerGammaSixFullSourceTensorOperator -
          deningerGammaSixSourceTensorPrincipalOperator) ∧
      MemRectWeakSchattenClass 1 deningerGammaSixFullSourceTensorOperator ∧
      ¬ MemRectSchattenClass 1 deningerGammaSixFullSourceTensorOperator := by
  rw [deningerGammaSixFullSourceTensorOperator_sub_principal]
  exact ⟨deningerGammaSixSourceTensorRemainderOperator_traceClass,
    deningerGammaSixFullSourceTensorOperator_weak,
    deningerGammaSixFullSourceTensorOperator_not_traceClass⟩

end

end RHTower
