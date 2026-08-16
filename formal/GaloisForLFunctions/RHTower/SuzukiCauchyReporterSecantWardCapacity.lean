import GaloisForLFunctions.RHTower.SuzukiCauchyWallGammaSecantAssembly
import GaloisForLFunctions.HTGeometry.JuliaDefectSpectralEquilibrium
import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite
import Mathlib.Probability.Distributions.Cauchy

/-!
# Cauchy Ward capacity and negative interscale law for Suzuki reporter secants

Suzuki's two-depth reporter secants form a Cauchy-height Gram packet whose lower-Hardy evaluation
is its correlation with the unit vacuum.  This yields the exact finite Ward-capacity inequality.

More importantly, the individual cross-Gram has a forced negative factor once one lag is at least
twice the other.  At `q = 2p+r` it factors as

`(exp(-p/2)-1) exp(-r/2) (1-exp(-(2p+r)/2))`.

Thus positive reporter coefficients have strictly negative far-scale interaction.  This exposes a
concrete interscale cancellation channel for the completed CCM/Suzuki source; it does not prove the
still-missing cofinal prime--polar--Gamma energy bound.
-/

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate NNReal ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

def cauchyHalfExponentialKernel (x : ℝ) : ℝ :=
  Real.exp (-|x| / 2)

theorem charFun_standardCauchy_eq_exp_neg_abs (x : ℝ) :
    charFun (ProbabilityTheory.cauchyMeasure 0 1) x =
      (Real.exp (-|x|) : ℂ) := by
  rw [MeasureTheory.charFun_apply_real,
    ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (ProbabilityTheory.measurable_cauchyPDF 0 1)
    (Filter.Eventually.of_forall fun y => by simp [ProbabilityTheory.cauchyPDF])]
  calc
    (∫ y : ℝ, (ProbabilityTheory.cauchyPDF 0 1 y).toReal •
        Complex.exp ((x * y : ℂ) * I)) =
        (Real.pi : ℂ)⁻¹ * massPairing (cauchyFourierWeight (-x)) 0 1 := by
      rw [massPairing, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      simp only [ProbabilityTheory.cauchyPDF, ProbabilityTheory.cauchyPDFReal]
      rw [ENNReal.toReal_ofReal (by positivity)]
      simp only [Nat.reduceAdd, pow_one, cauchyFourierWeight]
      norm_num
      ring_nf
    _ = (Real.exp (-|x|) : ℂ) := by
      rw [massPairing_cauchyFourierWeight_zero (by norm_num : (0 : ℝ) < 1)]
      norm_num [abs_neg]

theorem positiveDefiniteOnReal_cauchyHalfExponentialKernel :
    PositiveDefiniteOnReal (fun x => (cauchyHalfExponentialKernel x : ℂ)) := by
  have hPD := positiveDefiniteOnReal_charFun
    (ProbabilityTheory.cauchyMeasure 0 1)
  intro N t c
  obtain ⟨r, hr, hform⟩ := hPD N (fun i => t i / 2) c
  refine ⟨r, hr, ?_⟩
  rw [← hform]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [charFun_standardCauchy_eq_exp_neg_abs]
  simp only [cauchyHalfExponentialKernel]
  congr 3
  rw [show t j / 2 - t i / 2 = (t j - t i) / 2 by ring, abs_div]
  norm_num
  ring

/-- Doubled wall nodes carrying the two depths `p` and `2p`. -/
def suzukiReporterSecantPacketNodes {N : ℕ}
    (p : Fin N → ℝ≥0) : Fin (N + N) → ℝ :=
  Fin.append (fun i => -(p i : ℝ)) (fun i => -2 * (p i : ℝ))

/-- Signed coefficients of the two-depth wall secants. -/
def suzukiReporterSecantPacketCoefficients {N : ℕ}
    (c : Fin N → ℝ) : Fin (N + N) → ℝ :=
  Fin.append c (fun i => -c i)

/-- Literal lower-Hardy reporter amplitude of a finite Suzuki lag packet. -/
def suzukiReporterSecantPacketLowerHardyAmplitude {N : ℕ}
    (p : Fin N → ℝ≥0) (c : Fin N → ℝ) : ℝ :=
  ∑ i, c i * _root_.RHTower.unitRieszSuzukiReporter 0 (-(p i : ℝ))

/-- Full Cauchy wall Gram energy of the doubled Suzuki secant packet. -/
def suzukiReporterSecantPacketCauchyEnergy {N : ℕ}
    (p : Fin N → ℝ≥0) (c : Fin N → ℝ) : ℝ :=
  realKernelPacketEnergy cauchyHalfExponentialKernel
    (suzukiReporterSecantPacketNodes p)
    (suzukiReporterSecantPacketCoefficients c)

/-- Cauchy inner product of two individual Suzuki two-depth secants. -/
def suzukiReporterSecantCauchyGram (p q : ℝ≥0) : ℝ :=
  cauchyHalfExponentialKernel ((p : ℝ) - q) -
    cauchyHalfExponentialKernel ((p : ℝ) - 2 * q) -
    cauchyHalfExponentialKernel (2 * (p : ℝ) - q) +
    cauchyHalfExponentialKernel (2 * (p : ℝ) - 2 * q)

/-- The doubled-node packet energy is exactly the quadratic form of the source-level Suzuki
secant cross-Gram.  This is the bridge needed to use far-scale negativity in packet estimates. -/
theorem suzukiReporterSecantPacketCauchyEnergy_eq_sum_gram
    {N : ℕ} (p : Fin N → ℝ≥0) (c : Fin N → ℝ) :
    suzukiReporterSecantPacketCauchyEnergy p c =
      ∑ i, ∑ j, c i * suzukiReporterSecantCauchyGram (p i) (p j) * c j := by
  rw [suzukiReporterSecantPacketCauchyEnergy, realKernelPacketEnergy]
  simp only [Fin.sum_univ_add, suzukiReporterSecantPacketNodes,
    suzukiReporterSecantPacketCoefficients, Fin.append_left, Fin.append_right,
    Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [suzukiReporterSecantCauchyGram]
  ring_nf

/-- Exact far-lag factorization.  At `q = 2p+r`, the secant cross-Gram has one forced negative
factor and two nonnegative attenuation factors. -/
theorem suzukiReporterSecantCauchyGram_two_mul_add_eq
    (p r : ℝ≥0) :
    suzukiReporterSecantCauchyGram p (2 * p + r) =
      (Real.exp (-(p : ℝ) / 2) - 1) * Real.exp (-(r : ℝ) / 2) *
        (1 - Real.exp (-(2 * (p : ℝ) + r) / 2)) := by
  have hp : 0 ≤ (p : ℝ) := p.property
  have hr : 0 ≤ (r : ℝ) := r.property
  have hppr : 0 ≤ (p : ℝ) + r := add_nonneg hp hr
  have hthree : 0 ≤ 3 * (p : ℝ) + 2 * r := by positivity
  have htwo : 0 ≤ 2 * ((p : ℝ) + r) := by positivity
  have h1 : |(p : ℝ) - (2 * p + r : ℝ≥0)| = (p : ℝ) + r := by
    rw [show (p : ℝ) - (2 * p + r : ℝ≥0) = -((p : ℝ) + r) by push_cast; ring,
      abs_neg, abs_of_nonneg hppr]
  have h2 : |(p : ℝ) - 2 * (2 * p + r : ℝ≥0)| = 3 * (p : ℝ) + 2 * r := by
    rw [show (p : ℝ) - 2 * (2 * p + r : ℝ≥0) =
        -(3 * (p : ℝ) + 2 * r) by push_cast; ring,
      abs_neg, abs_of_nonneg hthree]
  have h3 : |2 * (p : ℝ) - (2 * p + r : ℝ≥0)| = (r : ℝ) := by
    rw [show 2 * (p : ℝ) - (2 * p + r : ℝ≥0) = -(r : ℝ) by push_cast; ring,
      abs_neg, abs_of_nonneg hr]
  have h4 : |2 * (p : ℝ) - 2 * (2 * p + r : ℝ≥0)| =
      2 * ((p : ℝ) + r) := by
    rw [show 2 * (p : ℝ) - 2 * (2 * p + r : ℝ≥0) =
        -(2 * ((p : ℝ) + r)) by push_cast; ring,
      abs_neg, abs_of_nonneg htwo]
  rw [suzukiReporterSecantCauchyGram, cauchyHalfExponentialKernel,
    cauchyHalfExponentialKernel, cauchyHalfExponentialKernel,
    cauchyHalfExponentialKernel, h1, h2, h3, h4]
  have e1 : Real.exp (-((p : ℝ) + r) / 2) =
      Real.exp (-(p : ℝ) / 2) * Real.exp (-(r : ℝ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(3 * (p : ℝ) + 2 * r) / 2) =
      Real.exp (-(p : ℝ) / 2) * Real.exp (-(r : ℝ) / 2) *
        Real.exp (-(2 * (p : ℝ) + r) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e4 : Real.exp (-(2 * ((p : ℝ) + r)) / 2) =
      Real.exp (-(r : ℝ) / 2) * Real.exp (-(2 * (p : ℝ) + r) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e1, e2, e4]
  ring

/-- Two Suzuki wall secants separated by at least a factor two have nonpositive Cauchy
cross-Gram.  This is unconditional because the separation is parameterized as `q = 2p+r`. -/
theorem suzukiReporterSecantCauchyGram_two_mul_add_nonpos
    (p r : ℝ≥0) :
    suzukiReporterSecantCauchyGram p (2 * p + r) ≤ 0 := by
  rw [suzukiReporterSecantCauchyGram_two_mul_add_eq]
  have hfirst : Real.exp (-(p : ℝ) / 2) - 1 ≤ 0 := by
    apply sub_nonpos.mpr
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property) (by norm_num)
  have hmiddle : 0 ≤ Real.exp (-(r : ℝ) / 2) := Real.exp_pos _ |>.le
  have hlast : 0 ≤ 1 - Real.exp (-(2 * (p : ℝ) + r) / 2) := by
    apply sub_nonneg.mpr
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (add_nonneg (mul_nonneg (by norm_num) p.property) r.property))
      (by norm_num)
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hfirst hmiddle) hlast

/-- Sharpness of the factor-two wall: every nonzero shallower lag has strictly negative
cross-Gram with every lag of the form `2p+r`. -/
theorem suzukiReporterSecantCauchyGram_two_mul_add_neg
    (p : {p : ℝ≥0 // p ≠ 0}) (r : ℝ≥0) :
    suzukiReporterSecantCauchyGram p.1 (2 * p.1 + r) < 0 := by
  rw [suzukiReporterSecantCauchyGram_two_mul_add_eq]
  have hp : 0 < (p.1 : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr p.2)
  have hfirst : Real.exp (-(p.1 : ℝ) / 2) - 1 < 0 := by
    apply sub_neg.mpr
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith) (by norm_num)
  have hmiddle : 0 < Real.exp (-(r : ℝ) / 2) := Real.exp_pos _
  have hlast : 0 < 1 - Real.exp (-(2 * (p.1 : ℝ) + r) / 2) := by
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos
      (by have := r.property; linarith)
      (by norm_num)
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfirst hmiddle) hlast

/-- Total cross-energy between nonnegative reporter packets when every deeper lag is represented
as `2p+r`.  Pair-dependent residuals retain the exact far-block geometry. -/
def suzukiReporterSecantFarBlockEnergy {N M : ℕ}
    (p : Fin N → ℝ≥0) (c : Fin N → ℝ≥0)
    (r : Fin N → Fin M → ℝ≥0) (d : Fin M → ℝ≥0) : ℝ :=
  ∑ i, ∑ j, (c i : ℝ) *
    suzukiReporterSecantCauchyGram (p i) (2 * p i + r i j) * (d j : ℝ)

/-- **Negative far block.** Every factor-two-separated cross-scale block of nonnegative Suzuki
reporter coefficients contributes nonpositively to the full Cauchy energy. -/
theorem suzukiReporterSecantFarBlockEnergy_nonpos
    {N M : ℕ} (p : Fin N → ℝ≥0) (c : Fin N → ℝ≥0)
    (r : Fin N → Fin M → ℝ≥0) (d : Fin M → ℝ≥0) :
    suzukiReporterSecantFarBlockEnergy p c r d ≤ 0 := by
  rw [suzukiReporterSecantFarBlockEnergy]
  apply Finset.sum_nonpos
  intro i hi
  apply Finset.sum_nonpos
  intro j hj
  have hc : 0 ≤ (c i : ℝ) := (c i).property
  have hd : 0 ≤ (d j : ℝ) := (d j).property
  have hg := suzukiReporterSecantCauchyGram_two_mul_add_nonpos (p i) (r i j)
  calc
    (c i : ℝ) * suzukiReporterSecantCauchyGram (p i) (2 * p i + r i j) * (d j : ℝ) =
        ((c i : ℝ) * (d j : ℝ)) *
          suzukiReporterSecantCauchyGram (p i) (2 * p i + r i j) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc hd) hg

/-- Natural aperture pair lying below the multiplicative hyperbola `N*j = k^2`. -/
structure SuzukiNaturalApertureHyperbolaPair where
  aperture : ℕ
  shallowIndex : ℕ
  deepIndex : ℕ
  two_le_deepIndex : 2 ≤ deepIndex
  deepIndex_le_shallowIndex : deepIndex ≤ shallowIndex
  shallowIndex_le_aperture : shallowIndex ≤ aperture
  belowHyperbola : aperture * deepIndex ≤ shallowIndex ^ 2

/-- Source lag `log(N/k)` attached to the shallower natural index. -/
def SuzukiNaturalApertureHyperbolaPair.shallowLag
    (P : SuzukiNaturalApertureHyperbolaPair) : ℝ≥0 :=
  ⟨Real.log P.aperture - Real.log P.shallowIndex, by
    have hkpos : (0 : ℝ) < P.shallowIndex := by
      exact_mod_cast (lt_of_lt_of_le
        (lt_of_lt_of_le Nat.zero_lt_two P.two_le_deepIndex)
        P.deepIndex_le_shallowIndex)
    have hNpos : (0 : ℝ) < P.aperture := by
      exact_mod_cast (lt_of_lt_of_le
        (lt_of_lt_of_le
          (lt_of_lt_of_le Nat.zero_lt_two P.two_le_deepIndex)
          P.deepIndex_le_shallowIndex)
        P.shallowIndex_le_aperture)
    exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hkpos hNpos
      (by exact_mod_cast P.shallowIndex_le_aperture))⟩

/-- Source lag `log(N/j)` attached to the deeper natural index. -/
def SuzukiNaturalApertureHyperbolaPair.deepLag
    (P : SuzukiNaturalApertureHyperbolaPair) : ℝ≥0 :=
  ⟨Real.log P.aperture - Real.log P.deepIndex, by
    have hjpos : (0 : ℝ) < P.deepIndex := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two P.two_le_deepIndex)
    have hNpos : (0 : ℝ) < P.aperture := by
      exact_mod_cast (lt_of_lt_of_le
        (lt_of_lt_of_le
          (lt_of_lt_of_le Nat.zero_lt_two P.two_le_deepIndex)
          P.deepIndex_le_shallowIndex)
        P.shallowIndex_le_aperture)
    exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hjpos hNpos
      (by exact_mod_cast P.deepIndex_le_shallowIndex.trans P.shallowIndex_le_aperture))⟩

/-- The multiplicative hyperbola `N*j ≤ k²` is exactly the factor-two lag region
`2 log(N/k) ≤ log(N/j)`. -/
theorem SuzukiNaturalApertureHyperbolaPair.two_mul_shallowLag_le_deepLag
    (P : SuzukiNaturalApertureHyperbolaPair) :
    2 * P.shallowLag ≤ P.deepLag := by
  have hjpos : (0 : ℝ) < P.deepIndex := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two P.two_le_deepIndex)
  have hkpos : (0 : ℝ) < P.shallowIndex := by
    exact_mod_cast (lt_of_lt_of_le
      (lt_of_lt_of_le Nat.zero_lt_two P.two_le_deepIndex)
      P.deepIndex_le_shallowIndex)
  have hNpos : (0 : ℝ) < P.aperture := by
    exact_mod_cast (lt_of_lt_of_le
      (lt_of_lt_of_le
        (lt_of_lt_of_le Nat.zero_lt_two P.two_le_deepIndex)
        P.deepIndex_le_shallowIndex)
      P.shallowIndex_le_aperture)
  have hmul : (P.aperture : ℝ) * P.deepIndex ≤ (P.shallowIndex : ℝ) ^ 2 := by
    exact_mod_cast P.belowHyperbola
  have hlog := Real.strictMonoOn_log.monotoneOn
    (mul_pos hNpos hjpos) (sq_pos_of_pos hkpos) hmul
  rw [Real.log_mul hNpos.ne' hjpos.ne', Real.log_pow] at hlog
  norm_num at hlog
  change 2 * (Real.log P.aperture - Real.log P.shallowIndex) ≤
    Real.log P.aperture - Real.log P.deepIndex
  linarith

/-- Exact residual depth beyond the factor-two wall. -/
def SuzukiNaturalApertureHyperbolaPair.farResidual
    (P : SuzukiNaturalApertureHyperbolaPair) : ℝ≥0 :=
  P.deepLag - 2 * P.shallowLag

theorem SuzukiNaturalApertureHyperbolaPair.deepLag_eq_two_mul_add_farResidual
    (P : SuzukiNaturalApertureHyperbolaPair) :
    P.deepLag = 2 * P.shallowLag + P.farResidual := by
  rw [SuzukiNaturalApertureHyperbolaPair.farResidual]
  exact (tsub_add_cancel_of_le P.two_mul_shallowLag_le_deepLag).symm.trans (add_comm _ _)

/-- **Arithmetic negative region.** Every natural source pair below `N*j = k²` contributes
nonpositively to the Cauchy reporter-secant Gram. -/
theorem SuzukiNaturalApertureHyperbolaPair.reporterSecantCauchyGram_nonpos
    (P : SuzukiNaturalApertureHyperbolaPair) :
    suzukiReporterSecantCauchyGram P.shallowLag P.deepLag ≤ 0 := by
  rw [P.deepLag_eq_two_mul_add_farResidual]
  exact suzukiReporterSecantCauchyGram_two_mul_add_nonpos P.shallowLag P.farResidual

/-- Natural Suzuki source lag, clipped only outside its literal aperture index set. -/
def suzukiNaturalApertureLag (N k : ℕ) : ℝ≥0 :=
  Real.toNNReal (Real.log N - Real.log k)

/-- Literal critical-Mellin coefficient of a prime reporter secant in Suzuki's Green source. -/
def suzukiNaturalAperturePrimeWeight (_N k : ℕ) : ℝ≥0 :=
  ⟨_root_.RHTower.criticalMellinAtomWeight k,
    _root_.RHTower.criticalMellinAtomWeight_nonneg k⟩

def suzukiNaturalAperturePairSet (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc 2 N ×ˢ Finset.Icc 2 N

/-- Symmetric factor-two separation predicate in natural source coordinates. -/
def suzukiNaturalApertureBelowHyperbola (N : ℕ) (ij : ℕ × ℕ) : Prop :=
  if ij.1 ≤ ij.2 then N * ij.1 ≤ ij.2 ^ 2 else N * ij.2 ≤ ij.1 ^ 2

instance (N : ℕ) (ij : ℕ × ℕ) :
    Decidable (suzukiNaturalApertureBelowHyperbola N ij) := by
  unfold suzukiNaturalApertureBelowHyperbola
  infer_instance

/-- One ordered pair contribution to the literal finite Mangoldt Cauchy-secant energy. -/
def suzukiNaturalApertureCauchyPairTerm (N : ℕ) (ij : ℕ × ℕ) : ℝ :=
  (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
    suzukiReporterSecantCauchyGram
      (suzukiNaturalApertureLag N ij.1)
      (suzukiNaturalApertureLag N ij.2) *
    (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ)

/-- Full literal finite Mangoldt reporter-secant Cauchy energy. -/
def suzukiNaturalApertureCauchyEnergy (N : ℕ) : ℝ :=
  ∑ ij ∈ suzukiNaturalAperturePairSet N,
    suzukiNaturalApertureCauchyPairTerm N ij

/-- The only source region that can contribute positive pair energy:
`max(j,k)^2 < N * min(j,k)`. -/
def suzukiNaturalApertureNearHyperbolaCauchyEnergy (N : ℕ) : ℝ :=
  ∑ ij ∈ (suzukiNaturalAperturePairSet N).filter
      (fun ij => ¬ suzukiNaturalApertureBelowHyperbola N ij),
    suzukiNaturalApertureCauchyPairTerm N ij

/-- Source energy in the complementary factor-two-separated region. -/
def suzukiNaturalApertureFarHyperbolaCauchyEnergy (N : ℕ) : ℝ :=
  ∑ ij ∈ (suzukiNaturalAperturePairSet N).filter
      (suzukiNaturalApertureBelowHyperbola N),
    suzukiNaturalApertureCauchyPairTerm N ij

theorem suzukiReporterSecantCauchyGram_comm (p q : ℝ≥0) :
    suzukiReporterSecantCauchyGram p q = suzukiReporterSecantCauchyGram q p := by
  rw [suzukiReporterSecantCauchyGram, suzukiReporterSecantCauchyGram]
  simp only [cauchyHalfExponentialKernel]
  have h0 : |(p : ℝ) - (q : ℝ)| = |(q : ℝ) - (p : ℝ)| := abs_sub_comm _ _
  have h1 : |(p : ℝ) - 2 * (q : ℝ)| = |2 * (q : ℝ) - (p : ℝ)| := abs_sub_comm _ _
  have h2 : |2 * (p : ℝ) - (q : ℝ)| = |(q : ℝ) - 2 * (p : ℝ)| := abs_sub_comm _ _
  have h3 : |2 * (p : ℝ) - 2 * (q : ℝ)| = |2 * (q : ℝ) - 2 * (p : ℝ)| := abs_sub_comm _ _
  rw [h0, h1, h2, h3]
  ring_nf

/-- **Literal prime far-energy cancellation.** Every ordered Mangoldt pair on or below the
multiplicative hyperbola has nonpositive total Cauchy reporter-secant energy. -/
theorem suzukiNaturalApertureFarHyperbolaCauchyEnergy_nonpos (N : ℕ) :
    suzukiNaturalApertureFarHyperbolaCauchyEnergy N ≤ 0 := by
  rw [suzukiNaturalApertureFarHyperbolaCauchyEnergy]
  apply Finset.sum_nonpos
  intro ij hij
  rw [Finset.mem_filter] at hij
  have hijmem := Finset.mem_product.mp hij.1
  have hiIcc := Finset.mem_Icc.mp hijmem.1
  have hjIcc := Finset.mem_Icc.mp hijmem.2
  have hwi : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.1).property
  have hwj : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.2).property
  have hgram : suzukiReporterSecantCauchyGram
      (suzukiNaturalApertureLag N ij.1)
      (suzukiNaturalApertureLag N ij.2) ≤ 0 := by
    by_cases horder : ij.1 ≤ ij.2
    · have hbelow : N * ij.1 ≤ ij.2 ^ 2 := by
        simpa [suzukiNaturalApertureBelowHyperbola, horder] using hij.2
      let P : SuzukiNaturalApertureHyperbolaPair :=
        { aperture := N
          shallowIndex := ij.2
          deepIndex := ij.1
          two_le_deepIndex := hiIcc.1
          deepIndex_le_shallowIndex := horder
          shallowIndex_le_aperture := hjIcc.2
          belowHyperbola := hbelow }
      have hdeepNonneg : 0 ≤ Real.log N - Real.log ij.1 := by
        exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn
          (by show (0 : ℝ) < ij.1
              exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hiIcc.1))
          (by show (0 : ℝ) < N
              exact_mod_cast (lt_of_lt_of_le
            (lt_of_lt_of_le Nat.zero_lt_two hjIcc.1) hjIcc.2))
          (by exact_mod_cast hiIcc.2))
      have hshallowNonneg : 0 ≤ Real.log N - Real.log ij.2 := by
        exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn
          (by show (0 : ℝ) < ij.2
              exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hjIcc.1))
          (by show (0 : ℝ) < N
              exact_mod_cast (lt_of_lt_of_le
            (lt_of_lt_of_le Nat.zero_lt_two hjIcc.1) hjIcc.2))
          (by exact_mod_cast hjIcc.2))
      have hdeep : suzukiNaturalApertureLag N ij.1 = P.deepLag := by
        rw [suzukiNaturalApertureLag, Real.toNNReal_of_nonneg hdeepNonneg]
        rfl
      have hshallow : suzukiNaturalApertureLag N ij.2 = P.shallowLag := by
        rw [suzukiNaturalApertureLag, Real.toNNReal_of_nonneg hshallowNonneg]
        rfl
      rw [hdeep, hshallow, suzukiReporterSecantCauchyGram_comm]
      exact P.reporterSecantCauchyGram_nonpos
    · have horder' : ij.2 ≤ ij.1 := Nat.le_of_lt (Nat.lt_of_not_ge horder)
      have hbelow : N * ij.2 ≤ ij.1 ^ 2 := by
        simpa [suzukiNaturalApertureBelowHyperbola, horder] using hij.2
      let P : SuzukiNaturalApertureHyperbolaPair :=
        { aperture := N
          shallowIndex := ij.1
          deepIndex := ij.2
          two_le_deepIndex := hjIcc.1
          deepIndex_le_shallowIndex := horder'
          shallowIndex_le_aperture := hiIcc.2
          belowHyperbola := hbelow }
      have hdeepNonneg : 0 ≤ Real.log N - Real.log ij.2 := by
        exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn
          (by show (0 : ℝ) < ij.2
              exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hjIcc.1))
          (by show (0 : ℝ) < N
              exact_mod_cast (lt_of_lt_of_le
            (lt_of_lt_of_le Nat.zero_lt_two hiIcc.1) hiIcc.2))
          (by exact_mod_cast hjIcc.2))
      have hshallowNonneg : 0 ≤ Real.log N - Real.log ij.1 := by
        exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn
          (by show (0 : ℝ) < ij.1
              exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hiIcc.1))
          (by show (0 : ℝ) < N
              exact_mod_cast (lt_of_lt_of_le
            (lt_of_lt_of_le Nat.zero_lt_two hiIcc.1) hiIcc.2))
          (by exact_mod_cast hiIcc.2))
      have hdeep : suzukiNaturalApertureLag N ij.2 = P.deepLag := by
        rw [suzukiNaturalApertureLag, Real.toNNReal_of_nonneg hdeepNonneg]
        rfl
      have hshallow : suzukiNaturalApertureLag N ij.1 = P.shallowLag := by
        rw [suzukiNaturalApertureLag, Real.toNNReal_of_nonneg hshallowNonneg]
        rfl
      rw [hshallow, hdeep]
      exact P.reporterSecantCauchyGram_nonpos
  dsimp [suzukiNaturalApertureCauchyPairTerm]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hwi hgram) hwj

/-- **Hyperbola localization of the literal prime energy.** The full Mangoldt Cauchy-secant
energy is bounded above by its restriction to `max(j,k)^2 < N * min(j,k)`; all deleted terms
have the favorable sign. -/
theorem suzukiNaturalApertureCauchyEnergy_le_nearHyperbola (N : ℕ) :
    suzukiNaturalApertureCauchyEnergy N ≤
      suzukiNaturalApertureNearHyperbolaCauchyEnergy N := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (suzukiNaturalAperturePairSet N)
    (suzukiNaturalApertureBelowHyperbola N)
    (suzukiNaturalApertureCauchyPairTerm N)
  have hfar := suzukiNaturalApertureFarHyperbolaCauchyEnergy_nonpos N
  unfold suzukiNaturalApertureFarHyperbolaCauchyEnergy at hfar
  unfold suzukiNaturalApertureCauchyEnergy
    suzukiNaturalApertureNearHyperbolaCauchyEnergy
  rw [← hsplit]
  exact add_le_of_nonpos_left hfar

theorem suzukiReporterSecantPacket_anchorCorrelation_eq
    {N : ℕ} (p : Fin N → ℝ≥0) (c : Fin N → ℝ) :
    ∑ k, suzukiReporterSecantPacketCoefficients c k *
        cauchyHalfExponentialKernel (suzukiReporterSecantPacketNodes p k) =
      suzukiReporterSecantPacketLowerHardyAmplitude p c := by
  simp only [suzukiReporterSecantPacketCoefficients,
    suzukiReporterSecantPacketNodes, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right,
    suzukiReporterSecantPacketLowerHardyAmplitude,
    cauchyHalfExponentialKernel, _root_.RHTower.unitRieszSuzukiReporter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hp : 0 ≤ (p i : ℝ) := (p i).property
  rw [abs_neg, abs_of_nonneg hp]
  have habs2 : |-2 * (p i : ℝ)| = 2 * (p i : ℝ) := by
    rw [abs_mul, abs_of_nonneg hp]
    norm_num
  rw [habs2]
  ring_nf

/-- **Finite Suzuki Ward capacity.**  Every real packet of nonnegative wall lags has lower-Hardy
reporter amplitude bounded by its exact doubled-node Cauchy wall Gram energy. -/
theorem suzukiReporterSecantPacket_lowerHardy_sq_le_cauchyEnergy
    {N : ℕ} (p : Fin N → ℝ≥0) (c : Fin N → ℝ) :
    suzukiReporterSecantPacketLowerHardyAmplitude p c ^ 2 ≤
      suzukiReporterSecantPacketCauchyEnergy p c := by
  have h := HTGeometry.anchorCorrelation_sq_le_gramEnergy_of_positiveDefinite
    cauchyHalfExponentialKernel
    positiveDefiniteOnReal_cauchyHalfExponentialKernel
    (by norm_num [cauchyHalfExponentialKernel])
    (fun y => by simp [cauchyHalfExponentialKernel, abs_neg])
    (suzukiReporterSecantPacketNodes p)
    (suzukiReporterSecantPacketCoefficients c)
  rw [suzukiReporterSecantPacket_anchorCorrelation_eq] at h
  rw [suzukiReporterSecantPacketCauchyEnergy]
  exact h

end

end GaloisForLFunctions.RHTower
