import GaloisForLFunctions.RHTower.DeningerFinitePrimeGreenDomainXiJets
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCompletedSourceGreen
import GaloisForLFunctions.RHTower.DeningerGammaSixCofinalMeyerTateXiGreenBoundary

/-!
# Actual paired prime source through completed Green and fixed Sonin transport

Finite paired prime depletion of the reflected Gaussian has whole-divisor
Mellin evaluations in `XiDivisorL2`, with norm bound `4^P.length` times the
original Gaussian norm. These are the literal evaluations of C38's source.
The paired multiplier is reflection invariant and nonzero at every divisor
copy, so the completed Green primitive and provenance retain it exactly.

The actual ordinary-prime Tate chains constructed with this provenance
converge in the existing Gamma graph. Every finite chain and its limit have
fixed Sonin operator image equal to that nonzero multiplier times the old
physical image. This source change therefore cannot remove the old image.
The original residue normalizer is retained on every multiplicity copy.

This identifies source evaluation, completed Green, Tate and Sonin transport.
It does not identify the distributional Gamma/flux boundary with that graph
boundary, and it does not assert Burnol Sonin-vector admission of the Gaussian.
The complete original Green/BV source-to-reader comparison remains open.
-/

open Complex Filter Topology
open scoped TensorProduct
namespace RHTower
open DeningerMeyerGaussianGreen
noncomputable section

/-- Literal paired finite-prime multiplier; order and repeated prime depths are retained. -/
def deningerPairedPrimeXiMultiplier (P : List Nat.Primes) (s : ℂ) : ℂ :=
  (P.map fun (p : Nat.Primes) => (1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * s)) *
    (1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * (1-s)))).prod

/-- The actual strong-log source, before any Hilbert completion. -/
def deningerPairedPrimeGaussianSource (P : List Nat.Primes) :
    DeningerMeyerStrongLogTarget :=
  deningerStrongLogPairedDepletion (P.map fun (p : Nat.Primes) => Real.log (p : ℕ))
    deningerMeyerReflectedLogGaussianSource

theorem deningerPairedPrimeGaussianSource_mellin (P : List Nat.Primes) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerPairedPrimeGaussianSource P) s =
      deningerPairedPrimeXiMultiplier P s *
        deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s := by
  simp only [deningerPairedPrimeGaussianSource, deningerStrongLogPairedDepletion_mellin,
    List.map_map, Function.comp_def, deningerPairedPrimeXiMultiplier]

theorem deningerPairedPrimeXiMultiplier_reflect (P : List Nat.Primes) (s : ℂ) :
    deningerPairedPrimeXiMultiplier P (1-s) = deningerPairedPrimeXiMultiplier P s := by
  simp only [deningerPairedPrimeXiMultiplier, sub_sub_cancel]
  congr 1
  apply List.map_congr_left
  intro p hp
  ring

private theorem norm_one_sub_prime_character_le (p : Nat.Primes) (s : ℂ)
    (hs : 0 ≤ s.re) :
    ‖1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * s)‖ ≤ 2 := by
  have hp : 0 ≤ Real.log (p : ℕ) := le_of_lt (Real.log_pos (by exact_mod_cast p.prop.one_lt))
  have hexp : ‖Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * s)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) hs
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * s)‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

/-- A uniform whole-divisor bound, with no critical-line hypothesis. -/
theorem norm_deningerPairedPrimeXiMultiplier_le (P : List Nat.Primes) (q : XiZeroCopy) :
    ‖deningerPairedPrimeXiMultiplier P (q.1 : ℂ)‖ ≤ (4 : ℝ) ^ P.length := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  induction P with
  | nil => simp [deningerPairedPrimeXiMultiplier]
  | cons p P ih =>
    simp only [deningerPairedPrimeXiMultiplier, List.map_cons, List.prod_cons, norm_mul,
      List.length_cons, pow_succ] at *
    have h1 := norm_one_sub_prime_character_le p (q.1 : ℂ) (le_of_lt hs.1)
    have h2 := norm_one_sub_prime_character_le p (1-(q.1 : ℂ)) (by simp; linarith [hs.2])
    have hprod : ‖1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * (q.1 : ℂ))‖ *
        ‖1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * (1-(q.1 : ℂ)))‖ ≤ 4 := by
      nlinarith [norm_nonneg (1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * (q.1 : ℂ))),
        norm_nonneg (1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * (1-(q.1 : ℂ))))]
    calc
      _ ≤ 4 * ‖(P.map fun (p : Nat.Primes) => (1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * (q.1 : ℂ))) *
        (1 - Complex.exp (((-Real.log (p : ℕ) : ℝ) : ℂ) * (1-(q.1 : ℂ))))).prod‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ ≤ 4 * 4 ^ P.length := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := mul_comm _ _

/-- Source-defined full Xi field: the entries are actual Mellin evaluations. -/
def deningerPairedPrimeGaussianXiField (P : List Nat.Primes) : XiDivisorL2 :=
  ⟨fun q => deningerMeyerStrongLogMellin (deningerPairedPrimeGaussianSource P) (q.1 : ℂ),
    Memℓp.mono
      ((lp.memℓp reflectedGaussianHorizonGradeL2).norm.const_smul ((4 : ℝ) ^ P.length))
      (fun q => by
        rw [deningerPairedPrimeGaussianSource_mellin, norm_mul, Pi.smul_apply,
          smul_eq_mul, reflectedGaussianHorizonGradeL2_apply]
        exact mul_le_mul_of_nonneg_right (norm_deningerPairedPrimeXiMultiplier_le P q)
          (norm_nonneg _))⟩

@[simp] theorem deningerPairedPrimeGaussianXiField_apply (P : List Nat.Primes) (q : XiZeroCopy) :
    deningerPairedPrimeGaussianXiField P q =
      deningerMeyerStrongLogMellin (deningerPairedPrimeGaussianSource P) (q.1 : ℂ) := rfl

theorem deningerPairedPrimeGaussianXiField_factor (P : List Nat.Primes) (q : XiZeroCopy) :
    deningerPairedPrimeGaussianXiField P q =
      deningerPairedPrimeXiMultiplier P (q.1 : ℂ) * reflectedGaussianHorizonGrade q :=
  deningerPairedPrimeGaussianSource_mellin P _

theorem deningerPairedPrimeGaussianXiField_ne_zero (P : List Nat.Primes) (q : XiZeroCopy) :
    deningerPairedPrimeGaussianXiField P q ≠ 0 :=
  (deningerPairedPrimeGreenGaussian_source P).2.2 q.1

theorem deningerPairedPrimeXiMultiplier_ne_zero (P : List Nat.Primes) (q : XiZeroCopy) :
    deningerPairedPrimeXiMultiplier P (q.1 : ℂ) ≠ 0 := by
  have h := deningerPairedPrimeGaussianXiField_ne_zero P q
  rw [deningerPairedPrimeGaussianXiField_factor] at h
  exact (mul_ne_zero_iff.mp h).1

theorem deningerPairedPrimeGaussianXiField_reflect (P : List Nat.Primes) (q : XiZeroCopy) :
    deningerPairedPrimeGaussianXiField P (xiZeroCopyReflectEquiv q) =
      deningerPairedPrimeGaussianXiField P q := by
  rw [deningerPairedPrimeGaussianXiField_factor, deningerPairedPrimeGaussianXiField_factor,
    reflectedGaussianHorizonGrade_reflect]
  change deningerPairedPrimeXiMultiplier P (1-(q.1 : ℂ)) * _ = _
  rw [deningerPairedPrimeXiMultiplier_reflect]

/-- Genuine completed Green primitive of the source-defined whole-divisor field. -/
def deningerPairedPrimeGaussianGreenPrimitive (P : List Nat.Primes) : XiDivisorL2 :=
  -deningerArithmeticCompletedSourceGreen (deningerPairedPrimeGaussianXiField P)

theorem deningerPairedPrimeGaussianGreenPrimitive_resolves (P : List Nat.Primes) :
    deningerArithmeticCompletedSourceGreen (deningerPairedPrimeGaussianGreenPrimitive P) =
      deningerPairedPrimeGaussianXiField P := by
  rw [deningerPairedPrimeGaussianGreenPrimitive, map_neg,
    deningerArithmeticCompletedSourceGreen_sq, neg_neg]

theorem deningerPairedPrimeGaussianGreenPrimitive_apply (P : List Nat.Primes) (q : XiZeroCopy) :
    deningerPairedPrimeGaussianGreenPrimitive P q =
      -deningerArithmeticFEOrientation q * deningerPairedPrimeGaussianXiField P q := by
  simp only [deningerPairedPrimeGaussianGreenPrimitive, lp.coeFn_neg, Pi.neg_apply,
    deningerArithmeticCompletedSourceGreen_apply, deningerPairedPrimeGaussianXiField_reflect]
  ring

/-- The original completed primitive retains exactly the source-forced multiplier. -/
theorem deningerPairedPrimeGaussianGreenPrimitive_factor (P : List Nat.Primes)
    (q : XiZeroCopy) :
    deningerPairedPrimeGaussianGreenPrimitive P q =
      deningerPairedPrimeXiMultiplier P (q.1 : ℂ) *
        reflectedGaussianHorizonCompletedGreenPrimitive q := by
  rw [deningerPairedPrimeGaussianGreenPrimitive_apply,
    deningerPairedPrimeGaussianXiField_factor,
    reflectedGaussianHorizonCompletedGreenPrimitive_apply]
  ring

/-- The original Gamma residue normalizer is unchanged on every multiplicity copy. -/
theorem deningerPairedPrimeGaussian_original_residue_normalization
    (P : List Nat.Primes) (q : XiZeroCopy) :
    (deningerPairedPrimeGaussianXiField P q * xiGaussianGammaResidueNormalizer q) *
      xiGaussianGammaResiduePacket q = deningerPairedPrimeGaussianXiField P q := by
  exact horizonGrade_mul_normalizer_mul_packet (deningerPairedPrimeGaussianXiField P) q

/-- Existing completed Green defect evaluated on the actual admitted source. -/
def deningerPairedPrimeGaussianGreenProvenance (P : List Nat.Primes) : XiDivisorL2 :=
  deningerArithmeticCompletedGreenProvenance (deningerPairedPrimeGaussianXiField P)

theorem deningerPairedPrimeGaussianGreenProvenance_factor (P : List Nat.Primes)
    (q : XiZeroCopy) :
    deningerPairedPrimeGaussianGreenProvenance P q =
      deningerPairedPrimeXiMultiplier P (q.1 : ℂ) * reflectedGaussianHorizonGreenProvenance q := by
  simp only [deningerPairedPrimeGaussianGreenProvenance, reflectedGaussianHorizonGreenProvenance,
    deningerArithmeticCompletedGreenProvenance_apply, deningerArithmeticOrientedHodgeLp_apply,
    deningerArithmeticCompletedRieszConjugation_apply]
  simp only [starRingEnd_apply, star_star]
  rw [deningerPairedPrimeGaussianXiField_reflect, deningerPairedPrimeGaussianXiField_factor,
    reflectedGaussianHorizonGradeL2_apply, reflectedGaussianHorizonGrade_reflect]
  ring

/-- Quantitative full-divisor admission bound for the actual source. -/
theorem norm_deningerPairedPrimeGaussianXiField_le (P : List Nat.Primes) :
    ‖deningerPairedPrimeGaussianXiField P‖ ≤
      (4 : ℝ) ^ P.length * ‖reflectedGaussianHorizonGradeL2‖ := by
  calc
    _ ≤ ‖((4 : ℂ) ^ P.length) • reflectedGaussianHorizonGradeL2‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro q
      rw [deningerPairedPrimeGaussianXiField_factor, norm_mul, lp.coeFn_smul,
        Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow, reflectedGaussianHorizonGradeL2_apply]
      norm_num only [Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_right (norm_deningerPairedPrimeXiMultiplier_le P q)
        (norm_nonneg _)
    _ = _ := by simp [norm_smul, norm_pow]

/-- Singular graph boundary of the actual paired-source Green provenance. -/
def deningerPairedPrimeGaussianVerticalBoundary (P : List Nat.Primes) (q : XiZeroCopy) :
    DeningerGammaSixCofinalSingularGraph :=
  deningerPairedPrimeGaussianGreenProvenance P q • deningerGammaSixCofinalGraphSingularVector

/-- Actual ordinary-prime chain, retaining the original prime and every cofinal depth. -/
def deningerPairedPrimeGaussianDegreeOneChain (P : List Nat.Primes) (p : Nat.Primes)
    (q : XiZeroCopy) (n : ℕ) : DeningerGammaSixCofinalMeyerTateDegreeOneSource :=
  ccmRationalAdelicOrdinaryPrimeCycleAtom p ⊗ₜ[ℂ]
    (deningerPairedPrimeGaussianGreenProvenance P q • deningerGammaSixCofinalAveragingPacket n)

/-- Convergence in the existing singular Gamma graph, from literal source chains. -/
theorem tendsto_deningerPairedPrimeGaussian_chain (P : List Nat.Primes) (p : Nat.Primes)
    (q : XiZeroCopy) :
    Tendsto (fun n => deningerGammaSixCofinalMeyerTateCompletedDifferential
      (deningerPairedPrimeGaussianDegreeOneChain P p q n))
      atTop (nhds (deningerPairedPrimeGaussianVerticalBoundary P q)) := by
  simpa [deningerPairedPrimeGaussianDegreeOneChain, deningerPairedPrimeGaussianVerticalBoundary,
    map_smul] using
    tendsto_deningerGammaSixCofinalFiniteGraphAdmission_averagingPacket.const_smul
      (deningerPairedPrimeGaussianGreenProvenance P q)

/-- Exact physical readout of each finite chain; no quotient or trace kills a coefficient. -/
theorem deningerPairedPrimeGaussian_finite_physical_readout (P : List Nat.Primes)
    (p : Nat.Primes) (q : XiZeroCopy) (n : ℕ) :
    deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
      (deningerGammaSixCofinalMeyerTateCompletedDifferential
        (deningerPairedPrimeGaussianDegreeOneChain P p q n)) =
    deningerPairedPrimeXiMultiplier P (q.1 : ℂ) •
      deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) := by
  rw [deningerPairedPrimeGaussianDegreeOneChain,
    deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom, map_smul, map_smul,
    deningerGammaSixCofinalGraphPhysicalTransport_finiteGraph,
    deningerGammaSixCofinalFiniteActualGammaTransport_averagingPacket,
    deningerPairedPrimeGaussianGreenProvenance_factor,
    deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary, mul_smul]

/-- The completed graph boundary has the same forced physical normalization. -/
theorem deningerPairedPrimeGaussian_completed_physical_readout (P : List Nat.Primes)
    (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
      (deningerPairedPrimeGaussianVerticalBoundary P q) =
    deningerPairedPrimeXiMultiplier P (q.1 : ℂ) •
      deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) := by
  rw [deningerPairedPrimeGaussianVerticalBoundary, map_smul,
    deningerGammaSixCofinalGraphPhysicalTransport_singularVector,
    deningerPairedPrimeGaussianGreenProvenance_factor,
    deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary, mul_smul]

/-- Finite prime Green admission cannot remove a nonzero original physical readout. -/
theorem deningerPairedPrimeGaussian_physical_readout_eq_zero_iff (P : List Nat.Primes)
    (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
      (deningerPairedPrimeGaussianVerticalBoundary P q) = 0 ↔
    deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
      (deningerGammaSixCofinalXiGreenVerticalBoundary q) = 0 := by
  rw [deningerPairedPrimeGaussian_completed_physical_readout, smul_eq_zero,
    or_iff_right (deningerPairedPrimeXiMultiplier_ne_zero P q)]

end
end RHTower
