import GaloisForLFunctions.RHTower.XiAperturePhysicalEndpointResponseRenormalization
import GaloisForLFunctions.RHTower.PrimeArchEndpointFrequencyAccretivity
import GaloisForLFunctions.RHTower.XiCompletedApertureReflectionKernel
import GaloisForLFunctions.RHTower.XiUnitDoubleCompletedOffDiagonalResponse

/-!
# Physical-endpoint valuation correction and the completed odd shuttle

The unit-to-double response has two orientations which must not be conflated.  The existing
scale shuttle is the coarse-minus-fine coefficient.  This file keeps the source-facing
fine-minus-coarse coefficient and proves that the ordinary-prime physical endpoint is obtained
from it by one unique valuation-resolved correction.  The correction fuses to the already known
inverse-square endpoint remainder, but the stronger statement is coefficientwise and therefore
preserves every prime-power phase before fusion.

The second part identifies the naturally clock-weighted reflected completed shuttle with the
unique reflection-odd aperture sector.  At regular source points this sector is exactly the
imaginary part of the continued prime--archimedean trace.  These are unconditional source
identities; no high-frequency sign or RH assertion is made.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The forced valuation-resolved endpoint correction -/

/-- The physical endpoint retains the ordinary-prime layer and annihilates every deeper
prime-power layer. -/
def xiPhysicalEndpointValuationAtom (p : Nat.Primes) (e : ℕ) : ℝ :=
  if e = 0 then ((p : ℝ))⁻¹ else 0

/-- Fine-minus-coarse unit-to-double response at one actual prime-valuation clock.  This is the
negative of the existing coarse-minus-fine `poissonSpectralScaleShuttle 1 2`. -/
def xiUnitDoubleRefinementValuationCoefficient
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  poissonSpectralHalfDensity 1 (xiPrimeValuationLaplaceRate e p) -
    poissonSpectralHalfDensity 2 (xiPrimeValuationLaplaceRate e p)

/-- The unique phase-preserving correction from the refinement spectrum to the physical
ordinary-prime spectrum. -/
def xiPhysicalEndpointValuationCorrection
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  xiPhysicalEndpointValuationAtom p e -
    xiUnitDoubleRefinementValuationCoefficient p e

private theorem xiPrimeValuationGeometricNode_one_eq_inv'
    (p : Nat.Primes) :
    xiPrimeValuationGeometricNode 1 p = ((p : ℝ))⁻¹ := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [xiPrimeValuationGeometricNode]
  rw [show -(1 : ℝ) * Real.log (p : ℝ) = -Real.log (p : ℝ) by ring]
  rw [Real.exp_neg, Real.exp_log hp]

private theorem xiPrimeValuationGeometricNode_two_eq_inv_sq'
    (p : Nat.Primes) :
    xiPrimeValuationGeometricNode 2 p = ((p : ℝ))⁻¹ ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [xiPrimeValuationGeometricNode]
  rw [show -(2 : ℝ) * Real.log (p : ℝ) =
      -Real.log (p : ℝ) + -Real.log (p : ℝ) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hp]
  ring

/-- The refinement orientation is exactly the negative of the previously formalized scale
shuttle. -/
theorem xiUnitDoubleRefinementValuationCoefficient_eq_neg_scaleShuttle
    (p : Nat.Primes) (e : ℕ) :
    xiUnitDoubleRefinementValuationCoefficient p e =
      -poissonSpectralScaleShuttle 1 2
        (xiPrimeValuationLaplaceRate e p) := by
  rw [xiUnitDoubleRefinementValuationCoefficient,
    poissonSpectralScaleShuttle]
  ring

/-- Explicit prime-power coefficient of the fine-minus-coarse refinement. -/
theorem xiUnitDoubleRefinementValuationCoefficient_eq
    (p : Nat.Primes) (e : ℕ) :
    xiUnitDoubleRefinementValuationCoefficient p e =
      ((p : ℝ))⁻¹ ^ (e + 1) -
        2 * ((p : ℝ))⁻¹ ^ (2 * (e + 1)) := by
  rw [xiUnitDoubleRefinementValuationCoefficient,
    poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate_eq_geometric,
    poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate_eq_geometric,
    xiPrimeValuationGeometricNode_one_eq_inv',
    xiPrimeValuationGeometricNode_two_eq_inv_sq']
  rw [pow_mul]
  ring

/-- The depth-zero correction is twice the inverse-square prime weight. -/
theorem xiPhysicalEndpointValuationCorrection_zero
    (p : Nat.Primes) :
    xiPhysicalEndpointValuationCorrection p 0 =
      2 * ((p : ℝ))⁻¹ ^ 2 := by
  rw [xiPhysicalEndpointValuationCorrection,
    xiPhysicalEndpointValuationAtom, if_pos rfl,
    xiUnitDoubleRefinementValuationCoefficient_eq]
  norm_num

/-- Every positive-depth correction is the explicit difference of two absolutely summable
prime-power tails. -/
theorem xiPhysicalEndpointValuationCorrection_succ
    (p : Nat.Primes) (e : ℕ) :
    xiPhysicalEndpointValuationCorrection p (e + 1) =
      -((p : ℝ))⁻¹ ^ (e + 2) +
        2 * ((p : ℝ))⁻¹ ^ (2 * (e + 2)) := by
  rw [xiPhysicalEndpointValuationCorrection,
    xiPhysicalEndpointValuationAtom, if_neg (by omega),
    xiUnitDoubleRefinementValuationCoefficient_eq]
  ring

/-- Coefficientwise reconstruction of the physical ordinary-prime spectrum.  This is stronger
than the fused scalar endpoint-remainder identity because no valuation phase has been erased. -/
theorem xiUnitDoubleRefinement_add_valuationCorrection
    (p : Nat.Primes) (e : ℕ) :
    xiUnitDoubleRefinementValuationCoefficient p e +
        xiPhysicalEndpointValuationCorrection p e =
      xiPhysicalEndpointValuationAtom p e := by
  rw [xiPhysicalEndpointValuationCorrection]
  ring

theorem summable_xiUnitDoubleRefinementValuationCoefficient
    (p : Nat.Primes) :
    Summable (xiUnitDoubleRefinementValuationCoefficient p) := by
  exact (summable_poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate
      (by norm_num : (0 : ℝ) < 1) p).sub
    (summable_poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate
      (by norm_num : (0 : ℝ) < 2) p)

/-- Complete valuation fusion of the correctly oriented response is the unsquared critical
Möbius damping. -/
theorem tsum_xiUnitDoubleRefinementValuationCoefficient
    (p : Nat.Primes) :
    (∑' e : ℕ, xiUnitDoubleRefinementValuationCoefficient p e) =
      1 / ((p : ℝ) + 1) := by
  rw [show (∑' e : ℕ, xiUnitDoubleRefinementValuationCoefficient p e) =
      poissonPrimeValuationFusedHalfDensity 1 p -
        poissonPrimeValuationFusedHalfDensity 2 p by
    rw [poissonPrimeValuationFusedHalfDensity,
      poissonPrimeValuationFusedHalfDensity]
    exact (summable_poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate
      (by norm_num : (0 : ℝ) < 1) p).tsum_sub
      (summable_poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate
        (by norm_num : (0 : ℝ) < 2) p)]
  have h := poissonPrimeValuationFusedScaleShuttle_one_two_eq p
  rw [poissonPrimeValuationFusedScaleShuttle] at h
  calc
    poissonPrimeValuationFusedHalfDensity 1 p -
        poissonPrimeValuationFusedHalfDensity 2 p =
      -(poissonPrimeValuationFusedHalfDensity 2 p -
        poissonPrimeValuationFusedHalfDensity 1 p) := by ring
    _ = -(-1 / ((p : ℝ) + 1)) := by rw [h]
    _ = 1 / ((p : ℝ) + 1) := by ring

theorem summable_xiPhysicalEndpointValuationAtom
    (p : Nat.Primes) :
    Summable (xiPhysicalEndpointValuationAtom p) := by
  simpa [xiPhysicalEndpointValuationAtom] using
    (hasSum_ite_eq (0 : ℕ) ((p : ℝ))⁻¹).summable

theorem tsum_xiPhysicalEndpointValuationAtom
    (p : Nat.Primes) :
    (∑' e : ℕ, xiPhysicalEndpointValuationAtom p e) =
      ((p : ℝ))⁻¹ := by
  simp [xiPhysicalEndpointValuationAtom]

theorem summable_xiPhysicalEndpointValuationCorrection
    (p : Nat.Primes) :
    Summable (xiPhysicalEndpointValuationCorrection p) :=
  (summable_xiPhysicalEndpointValuationAtom p).sub
    (summable_xiUnitDoubleRefinementValuationCoefficient p)

/-- The valuation-resolved correction fuses to the exact inverse-square endpoint remainder. -/
theorem tsum_xiPhysicalEndpointValuationCorrection
    (p : Nat.Primes) :
    (∑' e : ℕ, xiPhysicalEndpointValuationCorrection p e) =
      1 / ((p : ℝ) * ((p : ℝ) + 1)) := by
  simp_rw [xiPhysicalEndpointValuationCorrection]
  rw [(summable_xiPhysicalEndpointValuationAtom p).tsum_sub
      (summable_xiUnitDoubleRefinementValuationCoefficient p),
    tsum_xiPhysicalEndpointValuationAtom,
    tsum_xiUnitDoubleRefinementValuationCoefficient]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hp0, hp1]
  ring

/-- Clocking after valuation fusion recovers exactly the pre-existing physical endpoint response
remainder. -/
theorem log_mul_tsum_xiPhysicalEndpointValuationCorrection
    (p : Nat.Primes) :
    Real.log (p : ℝ) *
        (∑' e : ℕ, xiPhysicalEndpointValuationCorrection p e) =
      xiPhysicalEndpointResponseWeightRemainder p := by
  rw [tsum_xiPhysicalEndpointValuationCorrection,
    xiPhysicalEndpointResponseWeightRemainder]
  ring

/-! ## Absolute convergence of the phase-preserving correction kernel -/

/-- A geometric majorant which starts at inverse-square order even at depth zero. -/
def xiPhysicalEndpointValuationCorrectionMajorant
    (p : Nat.Primes) : ℕ → ℝ
  | 0 => 2 * ((p : ℝ))⁻¹ ^ 2
  | e + 1 => 3 * ((p : ℝ))⁻¹ ^ (e + 2)

private theorem xiPrimeInv_nonneg (p : Nat.Primes) :
    0 ≤ ((p : ℝ))⁻¹ := by positivity

private theorem xiPrimeInv_le_one (p : Nat.Primes) :
    ((p : ℝ))⁻¹ ≤ 1 := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_lt.le
  exact (inv_le_one₀ (by positivity : (0 : ℝ) < (p : ℝ))).mpr hp

/-- Every valuation correction is bounded by an inverse-square geometric tail. -/
theorem abs_xiPhysicalEndpointValuationCorrection_le_majorant
    (p : Nat.Primes) (e : ℕ) :
    |xiPhysicalEndpointValuationCorrection p e| ≤
      xiPhysicalEndpointValuationCorrectionMajorant p e := by
  rcases e with _ | e
  · rw [xiPhysicalEndpointValuationCorrection_zero,
      xiPhysicalEndpointValuationCorrectionMajorant]
    rw [abs_of_nonneg (by positivity)]
  · rw [xiPhysicalEndpointValuationCorrection_succ,
      xiPhysicalEndpointValuationCorrectionMajorant]
    let q : ℝ := ((p : ℝ))⁻¹
    let x : ℝ := q ^ (e + 2)
    have hq0 : 0 ≤ q := xiPrimeInv_nonneg p
    have hq1 : q ≤ 1 := xiPrimeInv_le_one p
    have hx0 : 0 ≤ x := pow_nonneg hq0 _
    have hx1 : x ≤ 1 := pow_le_one₀ hq0 hq1
    have hxsq : x ^ 2 ≤ x := by
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
    have hpow : q ^ (2 * (e + 2)) = x ^ 2 := by
      rw [mul_comm 2 (e + 2), pow_mul]
    change |-x + 2 * q ^ (2 * (e + 2))| ≤ 3 * x
    rw [hpow]
    calc
      |-x + 2 * x ^ 2| ≤ |-x| + |2 * x ^ 2| := abs_add_le _ _
      _ = x + 2 * x ^ 2 := by simp [abs_of_nonneg hx0]
      _ ≤ 3 * x := by nlinarith

theorem summable_xiPhysicalEndpointValuationCorrectionMajorant
    (p : Nat.Primes) :
    Summable (xiPhysicalEndpointValuationCorrectionMajorant p) := by
  let q : ℝ := ((p : ℝ))⁻¹
  have hq0 : 0 ≤ q := xiPrimeInv_nonneg p
  have hq1 : q < 1 := by
    have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    exact (inv_lt_one₀ (by positivity : (0 : ℝ) < (p : ℝ))).mpr hp
  have hqnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hgeom : Summable (fun e : ℕ => q ^ e) :=
    summable_geometric_of_norm_lt_one hqnorm
  apply (summable_nat_add_iff 1).mp
  convert hgeom.mul_left (3 * q ^ 2) using 1
  apply funext
  intro e
  simp [xiPhysicalEndpointValuationCorrectionMajorant, q, pow_add]
  ring

/-- The complete absolute correction fibre is uniformly of inverse-square prime order. -/
theorem tsum_xiPhysicalEndpointValuationCorrectionMajorant_le
    (p : Nat.Primes) :
    (∑' e : ℕ, xiPhysicalEndpointValuationCorrectionMajorant p e) ≤
      8 * ((p : ℝ))⁻¹ ^ 2 := by
  let q : ℝ := ((p : ℝ))⁻¹
  have hq0 : 0 ≤ q := xiPrimeInv_nonneg p
  have hqhalf : q ≤ 1 / 2 := by
    have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hp0 : (0 : ℝ) < p := by positivity
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).mpr hp
  have hq1 : q < 1 := lt_of_le_of_lt hqhalf (by norm_num)
  have hqnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have htail :
      (∑' e : ℕ, xiPhysicalEndpointValuationCorrectionMajorant p (e + 1)) =
        3 * q ^ 2 * (1 - q)⁻¹ := by
    calc
      (∑' e : ℕ,
          xiPhysicalEndpointValuationCorrectionMajorant p (e + 1)) =
          ∑' e : ℕ, (3 * q ^ 2) * q ^ e := by
        congr 1
        funext e
        simp [xiPhysicalEndpointValuationCorrectionMajorant, q, pow_add,
          mul_assoc, mul_comm]
      _ = (3 * q ^ 2) * ∑' e : ℕ, q ^ e := by
        rw [tsum_mul_left]
      _ = 3 * q ^ 2 * (1 - q)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one hqnorm]
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    have hden : 0 < 1 - q := by linarith
    have hprod : (1 - q) * (1 - q)⁻¹ = 1 :=
      mul_inv_cancel₀ hden.ne'
    have hinv0 : 0 ≤ (1 - q)⁻¹ := by positivity
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - q - 1 / 2) hinv0]
  rw [(summable_xiPhysicalEndpointValuationCorrectionMajorant p).tsum_eq_zero_add,
    htail]
  change 2 * q ^ 2 + 3 * q ^ 2 * (1 - q)⁻¹ ≤ 8 * q ^ 2
  nlinarith [sq_nonneg q]

private theorem summable_log_prime_div_sq :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have h := RHTower.summable_abs_log_natCast_pow_mul_rpow_neg 1 2 (by norm_num)
  have hnat : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
    apply h.congr
    intro n
    rcases n with _ | n
    · simp
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by norm_num)
    rw [abs_of_nonneg hlog, pow_one, Real.rpow_neg hn.le]
    rw [show ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
        ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) by
      exact Real.rpow_natCast _ 2]
    field_simp
  exact hnat.comp_injective Subtype.val_injective

/-- Absolute clocked mass of one correction fibre. -/
def xiPhysicalEndpointClockedCorrectionAbsoluteFibre
    (p : Nat.Primes) : ℝ :=
  ∑' e : ℕ,
    |Real.log (p : ℝ) * xiPhysicalEndpointValuationCorrection p e|

theorem xiPhysicalEndpointClockedCorrectionAbsoluteFibre_le
    (p : Nat.Primes) :
    xiPhysicalEndpointClockedCorrectionAbsoluteFibre p ≤
      8 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hlog : 0 ≤ Real.log (p : ℝ) := (Real.log_pos hp).le
  have habs : Summable
      (fun e : ℕ => |xiPhysicalEndpointValuationCorrection p e|) := by
    simpa [Real.norm_eq_abs] using
      (summable_xiPhysicalEndpointValuationCorrection p).norm
  have hmaj := summable_xiPhysicalEndpointValuationCorrectionMajorant p
  have hle :
      (∑' e : ℕ, |xiPhysicalEndpointValuationCorrection p e|) ≤
        ∑' e : ℕ, xiPhysicalEndpointValuationCorrectionMajorant p e :=
    habs.tsum_le_tsum
      (abs_xiPhysicalEndpointValuationCorrection_le_majorant p) hmaj
  calc
    xiPhysicalEndpointClockedCorrectionAbsoluteFibre p =
        Real.log (p : ℝ) *
          (∑' e : ℕ, |xiPhysicalEndpointValuationCorrection p e|) := by
      rw [xiPhysicalEndpointClockedCorrectionAbsoluteFibre, ← tsum_mul_left]
      congr 1
      funext e
      rw [abs_mul, abs_of_nonneg hlog]
    _ ≤ Real.log (p : ℝ) *
        (∑' e : ℕ, xiPhysicalEndpointValuationCorrectionMajorant p e) :=
      mul_le_mul_of_nonneg_left hle hlog
    _ ≤ Real.log (p : ℝ) * (8 * ((p : ℝ))⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (tsum_xiPhysicalEndpointValuationCorrectionMajorant_le p) hlog
    _ = 8 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
      field_simp [hp0]

theorem summable_xiPhysicalEndpointClockedCorrectionAbsoluteFibre :
    Summable xiPhysicalEndpointClockedCorrectionAbsoluteFibre := by
  have hbound : Summable (fun p : Nat.Primes =>
      8 * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) :=
    summable_log_prime_div_sq.mul_left 8
  exact Summable.of_nonneg_of_le
    (fun p => tsum_nonneg (fun e => abs_nonneg _))
    xiPhysicalEndpointClockedCorrectionAbsoluteFibre_le hbound

/-- Absolute convergence before choosing a height: the correction is summable on the full
prime-by-valuation diagram. -/
theorem summable_abs_clocked_xiPhysicalEndpointValuationCorrection :
    Summable (fun pe : Nat.Primes × ℕ =>
      |Real.log (pe.1 : ℝ) *
        xiPhysicalEndpointValuationCorrection pe.1 pe.2|) := by
  apply (summable_prod_of_nonneg (fun pe => abs_nonneg _)).mpr
  constructor
  · intro p
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      (Real.log_pos (by exact_mod_cast p.prop.one_lt)).le
    simpa [abs_mul, abs_of_nonneg hlog, Real.norm_eq_abs] using
      (summable_xiPhysicalEndpointValuationCorrection p).norm.mul_left
        (Real.log (p : ℝ))
  · exact summable_xiPhysicalEndpointClockedCorrectionAbsoluteFibre

/-- One phase-preserving correction atom at height `t`. -/
def xiPhysicalEndpointValuationCorrectionKernelTerm
    (t : ℝ) (pe : Nat.Primes × ℕ) : ℂ :=
  (Real.log (pe.1 : ℝ) *
      xiPhysicalEndpointValuationCorrection pe.1 pe.2 : ℂ) *
    Complex.exp
      (-Complex.I *
        (((pe.2 + 1 : ℕ) : ℝ) * Real.log (pe.1 : ℝ) * t : ℂ))

/-- The valuation-resolved correction is an honest absolutely convergent translation kernel. -/
def xiPhysicalEndpointValuationCorrectionKernel (t : ℝ) : ℂ :=
  ∑' pe : Nat.Primes × ℕ,
    xiPhysicalEndpointValuationCorrectionKernelTerm t pe

theorem summable_xiPhysicalEndpointValuationCorrectionKernelTerm
    (t : ℝ) :
    Summable (xiPhysicalEndpointValuationCorrectionKernelTerm t) := by
  apply Summable.of_norm
  apply summable_abs_clocked_xiPhysicalEndpointValuationCorrection.congr
  intro pe
  rw [xiPhysicalEndpointValuationCorrectionKernelTerm,
    norm_mul, Complex.norm_exp]
  have him :
      (-Complex.I *
        (((pe.2 + 1 : ℕ) : ℝ) * Real.log (pe.1 : ℝ) * t : ℂ)).re = 0 := by
    have harg :
        -Complex.I *
            (((pe.2 + 1 : ℕ) : ℝ) * Real.log (pe.1 : ℝ) * t : ℂ) =
          ((-(((pe.2 + 1 : ℕ) : ℝ) * Real.log (pe.1 : ℝ) * t) : ℝ) : ℂ) *
            Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  rw [him, Real.exp_zero, mul_one]
  norm_cast

/-- The corrected completed endpoint kernel: correctly oriented refinement, plus the unique
absolutely convergent phase-preserving endpoint correction. -/
def xiPhysicalEndpointCompletedKernel (t : ℝ) : ℂ :=
  xiCompletedApertureOffDiagonalKernel (1 / 2) t 0 -
    2 * xiCompletedApertureOffDiagonalKernel (3 / 2) t 0 +
      xiPhysicalEndpointValuationCorrectionKernel t

/-- The physical endpoint completion is the negative of the old coarse-minus-fine kernel plus
the forced correction. -/
theorem xiPhysicalEndpointCompletedKernel_eq_neg_unitDouble_add_correction
    (t : ℝ) :
    xiPhysicalEndpointCompletedKernel t =
      -xiUnitDoubleCompletedOffDiagonalResponseKernel t 0 +
        xiPhysicalEndpointValuationCorrectionKernel t := by
  rw [xiPhysicalEndpointCompletedKernel,
    xiUnitDoubleCompletedOffDiagonalResponseKernel]
  ring

/-! ## The clock-weighted reflected shuttle and the live source gate -/

/-- The functional-equation reflected shuttle with the two natural aperture clocks retained. -/
def xiCompletedReflectedClockShuttle (u x y : ℝ) : ℂ :=
  (((1 / 2 : ℝ) + u : ℝ) : ℂ) *
      xiCompletedApertureOffDiagonalKernel u x y -
    (((1 / 2 : ℝ) - u : ℝ) : ℂ) *
      xiCompletedApertureOffDiagonalKernel (-u) x y

/-- Reflection makes the real part of the clock-weighted shuttle independent of the individual
clock weights: only their sum, equal to one, survives. -/
theorem xiCompletedReflectedClockShuttle_re
    (u x y : ℝ) :
    (xiCompletedReflectedClockShuttle u x y).re =
      (xiCompletedApertureOffDiagonalKernel u x y).re := by
  rw [xiCompletedReflectedClockShuttle,
    xiCompletedApertureOffDiagonalKernel_reflect,
    xiCompletedApertureOffDiagonalKernel_swap]
  simp
  ring

/-- The reflected clock shuttle is exactly half of the unique aperture-odd completed sector. -/
theorem xiCompletedReflectedClockShuttle_re_eq_odd
    (u x y : ℝ) :
    (xiCompletedReflectedClockShuttle u x y).re =
      (xiCompletedApertureOddKernel u x y).re / 2 := by
  rw [xiCompletedReflectedClockShuttle_re,
    xiCompletedApertureOddKernel_eq_two_re]
  simp

/-- **Direct source bridge.** At every regular point in the upper critical half-strip, the live
continued prime--archimedean source gate is exactly half the completed reflection-odd aperture
kernel.  This identifies the missing high-frequency sign sector without assuming that sign. -/
theorem continuedPrimeArchSourceRelativeTrace_im_eq_half_apertureOddKernel
    {u t : ℝ} (hu : 0 < u) (huHalf : u < 1 / 2)
    (hzeta : riemannZeta
      ((((1 / 2 : ℝ) - u : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (continuedPrimeArchSourceRelativeTrace
        ((t : ℂ) + (u : ℂ) * Complex.I)).im =
      (xiCompletedApertureOddKernel u t 0).re / 2 := by
  let z : ℂ := (t : ℂ) + (u : ℂ) * Complex.I
  let s : ℂ := 1 / 2 + z * Complex.I
  have hspos : 0 < s.re := by
    dsimp [s, z]
    simp [Complex.mul_re]
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s, z] at hre
    simp [Complex.mul_re] at hre
    linarith
  have hsarg : s =
      (((1 / 2 : ℝ) - u : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [s, z, Complex.mul_re]
    ring
  have hzeta' : riemannZeta s ≠ 0 := by
    simpa [hsarg] using hzeta
  rw [continuedPrimeArchSourceRelativeTrace]
  rw [← seamFluxCochain_eq_continuedPrime_add_archimedean hspos hs1 hzeta']
  rw [hsarg]
  have hk :
      seamFluxCochain
          ((((1 / 2 : ℝ) - u : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        xiCompletedApertureOffDiagonalKernel (-u) t 0 := by
    rw [xiCompletedApertureOffDiagonalKernel]
    congr 2
    push_cast
    ring
  rw [hk, xiCompletedApertureOffDiagonalKernel_reflect,
    xiCompletedApertureOffDiagonalKernel_swap,
    xiCompletedApertureOddKernel_eq_two_re]
  simp

end


end RHTower
