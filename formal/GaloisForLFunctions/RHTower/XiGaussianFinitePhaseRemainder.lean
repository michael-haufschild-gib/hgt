import GaloisForLFunctions.RHTower.XiGaussianCoefficientTail

/-!
# A finite exact imaginary-channel remainder

Critical-line copies have zero imaginary-channel energy. After splitting at an
arbitrary spectral cutoff, the complete trace is bounded below by its real
channel minus the exact finite head phase energy and the full positive tail.
No low spectral copy is presumed real, and no mixed polynomial term is removed.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

/-- Half of the native phase-debt summand. -/
def xiGaussianImaginaryChannelAtom (Q : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) : ℝ :=
  (‖xiPolynomialGaussianHeatTerm Q t q‖ - (xiPolynomialGaussianHeatTerm Q t q).re) / 2

theorem xiGaussianImaginaryChannelAtom_nonneg (Q : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    0 ≤ xiGaussianImaginaryChannelAtom Q t q :=
  div_nonneg (sub_nonneg.mpr (Complex.re_le_norm _)) (by positivity)

theorem xiGaussianImaginaryChannelAtom_le_norm (Q : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    xiGaussianImaginaryChannelAtom Q t q ≤ ‖xiPolynomialGaussianHeatTerm Q t q‖ := by
  have h := (abs_le.mp (Complex.abs_re_le_norm (xiPolynomialGaussianHeatTerm Q t q))).1
  unfold xiGaussianImaginaryChannelAtom
  linarith only [h]

theorem summable_xiGaussianImaginaryChannelAtom (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    Summable (xiGaussianImaginaryChannelAtom Q t) := by
  have hs := summable_xiPolynomialGaussianHeatTerm t.property Q
  exact (hs.norm.sub (Complex.hasSum_re hs.hasSum).summable).div_const 2

/-- The imaginary channel vanishes at every actual critical-line copy. -/
theorem xiGaussianImaginaryChannelAtom_of_real (Q : Polynomial ℝ) (t : ℝ)
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im = 0}) :
    xiGaussianImaginaryChannelAtom Q t q.1 = 0 := by
  let x := (xiSpectralPoint q.1).re
  have hq : xiSpectralPoint q.1 = (x : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using q.property
  have he : xiPolynomialGaussianHeatTerm Q t q.1 =
      (((Q.eval (x ^ 2)) ^ 2 * Real.exp (-(t * x ^ 2)) : ℝ) : ℂ) := by
    simp only [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, hq,
      ← Complex.ofReal_pow, evalRealPolynomial_ofReal, ← Complex.ofReal_neg,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp, neg_mul]
  simp only [xiGaussianImaginaryChannelAtom, he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Q.eval (x ^ 2)) ^ 2 * Real.exp (-(t * x ^ 2))),
    Complex.ofReal_re, sub_self, zero_div]

/-- Exact phase energy in the finite low spectral shell, with all polynomial cross terms. -/
def xiGaussianHeadPhaseEnergy (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (R : ℝ) : ℝ :=
  ∑ q ∈ (finite_xiHeatShell R).toFinset, xiGaussianImaginaryChannelAtom Q t q

theorem xiGaussianHeadPhaseEnergy_nonneg (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (R : ℝ) :
    0 ≤ xiGaussianHeadPhaseEnergy Q t R :=
  Finset.sum_nonneg fun q _ => xiGaussianImaginaryChannelAtom_nonneg Q t q

/-- Only off-critical copies contribute to the exact finite head phase remainder. -/
theorem xiGaussianHeadPhaseEnergy_eq_offReal (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (R : ℝ) :
    xiGaussianHeadPhaseEnergy Q t R =
      ∑ q ∈ (finite_xiHeatShell R).toFinset.filter (fun q => (xiSpectralPoint q).im ≠ 0),
        xiGaussianImaginaryChannelAtom Q t q := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hnot
  have hi : (xiSpectralPoint q).im = 0 := by
    simpa only [Finset.mem_filter, hq, true_and, not_not] using hnot
  exact xiGaussianImaginaryChannelAtom_of_real Q t ⟨q, hi⟩

/-- The complete actual trace keeps its real reserve and the exact finite phase remainder. -/
theorem xiGaussianTrace_ge_realChannel_sub_headPhase_sub_tail
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (R : ℝ) :
    xiGaussianRealChannelEnergy Q t - xiGaussianHeadPhaseEnergy Q t R -
      xiGaussianTailEnergy Q t R ≤ xiPolynomialGaussianHeatTraceReal Q t := by
  classical
  let S := (finite_xiHeatShell R).toFinset
  have hset : (S : Set XiZeroCopy)ᶜ = {q : XiZeroCopy | R < (xiSpectralPoint q ^ 2).re} := by
    ext q
    simp only [Set.mem_compl_iff, Finset.mem_coe, S, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_le]
  have hs := summable_xiPolynomialGaussianHeatTerm t.property Q
  have hre := (Complex.hasSum_re hs.hasSum).summable
  have hI := summable_xiGaussianImaginaryChannelAtom Q t
  have hsplit := hI.sum_add_tsum_compl (s := S)
  rw [hset] at hsplit
  have htotal : (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t q) =
      ((∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm Q t q‖) -
        xiPolynomialGaussianHeatTraceReal Q t) / 2 := by
    rw [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace, Complex.re_tsum hs]
    simp only [xiGaussianImaginaryChannelAtom, tsum_div_const, hs.norm.tsum_sub hre]
  rw [htotal] at hsplit
  have htail : (∑' q : {q : XiZeroCopy // R < (xiSpectralPoint q ^ 2).re},
      xiGaussianImaginaryChannelAtom Q t q.1) ≤ xiGaussianTailEnergy Q t R := by
    exact Summable.tsum_le_tsum (fun q => xiGaussianImaginaryChannelAtom_le_norm Q t q.1)
      (hI.subtype _) (hs.norm.subtype _)
  have hJ := xiGaussianRealChannelEnergy_eq_half_energy_add_trace Q t
  let I := ∑' q : {q : XiZeroCopy // R < (xiSpectralPoint q ^ 2).re},
    xiGaussianImaginaryChannelAtom Q t q.1
  change I ≤ xiGaussianTailEnergy Q t R at htail
  change xiGaussianHeadPhaseEnergy Q t R + I =
    ((∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm Q t q‖) -
      xiPolynomialGaussianHeatTraceReal Q t) / 2 at hsplit
  linarith only [hsplit, htail, hJ]

end RHTower
