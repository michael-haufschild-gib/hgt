import GaloisForLFunctions.RHTower.XiGaussianOrbitProduct
import GaloisForLFunctions.RHTower.XiGaussianSampledPerturbation
import GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect

/-!
# Complete negative-orbit localization at a prescribed heat time

An off-real squared divisor node can be isolated by real polynomials at
every fixed positive heat time. All copies of its conjugate orbit survive;
all other copies tend to zero under one summable majorant. The limiting
signed trace is the negative of the limiting positive energy.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The complete multiplicity-counted conjugate orbit of a squared node. -/
def xiGaussianConjugateOrbit (q₀ : XiZeroCopy) : Finset XiZeroCopy := by
  classical
  exact (xiHeatShell (xiSpectralPoint q₀ ^ 2).re).filter
    (fun q => xiSpectralPoint q ^ 2 = xiSpectralPoint q₀ ^ 2 ∨
      xiSpectralPoint q ^ 2 = (starRingEnd ℂ) (xiSpectralPoint q₀ ^ 2))

theorem mem_xiGaussianConjugateOrbit (q₀ q : XiZeroCopy) :
    q ∈ xiGaussianConjugateOrbit q₀ ↔
      xiSpectralPoint q ^ 2 = xiSpectralPoint q₀ ^ 2 ∨
      xiSpectralPoint q ^ 2 = (starRingEnd ℂ) (xiSpectralPoint q₀ ^ 2) := by
  classical
  rw [xiGaussianConjugateOrbit, Finset.mem_filter, mem_xiHeatShell]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with h | h
    · rw [h]
    · rw [h, Complex.conj_re]

theorem xiGaussianConjugateOrbit_card_pos (q₀ : XiZeroCopy) :
    0 < (xiGaussianConjugateOrbit q₀).card :=
  Finset.card_pos.mpr ⟨q₀, (mem_xiGaussianConjugateOrbit q₀ q₀).mpr (Or.inl rfl)⟩

/-- Localization saturates the negative energy bound at each prescribed
positive time, with no simplicity or finite-divisor truncation assumption. -/
theorem exists_xiGaussian_fixedTime_negative_localization
    (t : {t : ℝ // 0 < t})
    (q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0}) :
    ∃ P : Finset XiZeroCopy → Polynomial ℝ,
      Tendsto (fun F => xiGaussianNativeEnergy (P F) t) atTop
        (𝓝 ((xiGaussianConjugateOrbit q₀.1).card : ℝ)) ∧
      Tendsto (fun F => xiPolynomialGaussianHeatTraceReal (P F) t) atTop
        (𝓝 (-((xiGaussianConjugateOrbit q₀.1).card : ℝ))) := by
  classical
  let z := xiSpectralPoint q₀.1 ^ 2
  let O := xiGaussianConjugateOrbit q₀.1
  let S := xiGaussianOrbitComplement z
  obtain ⟨a, ha, hlim⟩ := exists_xiGaussianOrbitProduct_nonzero_limit z
  let c := Complex.I * Complex.exp (((t : ℝ) : ℂ) * z / 2)
  let Q := realLinearInterpolator z (c / a)
  let P := fun F : Finset XiZeroCopy => Q * xiGaussianSelectedAnnihilator S F
  have hQ : evalRealPolynomial Q z = c / a := evalRealLinearInterpolator q₀.property
  have heval : Tendsto (fun F => evalRealPolynomial (P F) z) atTop (𝓝 c) := by
    have hh := hlim.const_mul (c / a)
    rw [div_mul_cancel₀ _ ha] at hh
    simpa only [P, evalRealPolynomial_mul, hQ] using hh
  have hc : c ^ 2 * Complex.exp (-((t : ℝ) : ℂ) * z) = -1 := by
    dsimp only [c]
    rw [mul_pow, Complex.I_sq, pow_two, ← Complex.exp_add, mul_assoc,
      ← Complex.exp_add]
    have he : ((t : ℝ) : ℂ) * z / 2 + ((t : ℝ) : ℂ) * z / 2 +
        -((t : ℝ) : ℂ) * z = 0 := by ring
    rw [he, Complex.exp_zero, mul_one]
  have hbase : Tendsto (fun F => evalRealPolynomial (P F) z ^ 2 *
      Complex.exp (-((t : ℝ) : ℂ) * z)) atTop (𝓝 (-1 : ℂ)) := by
    simpa only [hc] using (heval.pow 2).mul_const (Complex.exp (-((t : ℝ) : ℂ) * z))
  have hpoint (q : XiZeroCopy) : Tendsto
      (fun F => xiPolynomialGaussianHeatTerm (P F) t q) atTop
      (𝓝 (if q ∈ O then (-1 : ℂ) else 0)) := by
    by_cases hq : q ∈ O
    · rw [if_pos hq]
      rcases (mem_xiGaussianConjugateOrbit q₀.1 q).mp hq with hz | hz
      · simpa only [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, hz, z] using hbase
      · have hconj := Complex.continuous_conj.continuousAt.tendsto.comp hbase
        change xiSpectralPoint q ^ 2 = (starRingEnd ℂ) z at hz
        have heq (F : Finset XiZeroCopy) : xiPolynomialGaussianHeatTerm (P F) t q =
            (starRingEnd ℂ) (evalRealPolynomial (P F) z ^ 2 *
              Complex.exp (-((t : ℝ) : ℂ) * z)) := by
          rw [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, hz,
            evalRealPolynomial_conj, map_mul, map_pow, ← Complex.exp_conj]
          simp only [map_mul, map_neg, Complex.conj_ofReal, map_pow, z]
        change Tendsto (fun F => (starRingEnd ℂ) (evalRealPolynomial (P F) z ^ 2 *
          Complex.exp (-((t : ℝ) : ℂ) * z))) atTop (𝓝 ((starRingEnd ℂ) (-1))) at hconj
        simpa only [← heq, map_neg, map_one] using hconj
    · rw [if_neg hq]
      have hS : q ∈ S := by
        simpa only [S, xiGaussianOrbitComplement, Set.mem_setOf_eq, z, not_or] using
          (not_congr (mem_xiGaussianConjugateOrbit q₀.1 q)).mp hq
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_xiGaussianOrbitProduct_eval_zero z ⟨q, hS⟩] with F hF
      simp only [P, S, xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul, hF,
        mul_zero, zero_pow two_ne_zero, zero_mul]
  obtain ⟨H, hH⟩ := exists_xiGaussianSelectedAnnihilator_dominating_head S Q t
  have hs := summable_norm_xiPolynomialGaussianHeatTerm
    (div_pos t.property (show (0 : ℝ) < 2 by positivity))
    (Q * xiGaussianSelectedAnnihilator S H)
  have htrace := tendsto_tsum_of_dominated_convergence hs hpoint hH
  have henergy := tendsto_tsum_of_dominated_convergence hs (fun q => (hpoint q).norm)
    (hH.mono fun F hF q => by simpa only [norm_norm] using hF q)
  have hsum : (∑' q : XiZeroCopy, if q ∈ O then (-1 : ℂ) else 0) = -(O.card : ℂ) := by
    rw [tsum_eq_sum (s := O) (fun q hq => if_neg hq)]
    simp
  have hsumNorm : (∑' q : XiZeroCopy, ‖if q ∈ O then (-1 : ℂ) else 0‖) =
      (O.card : ℝ) := by
    simp only [apply_ite norm, norm_neg, norm_one, norm_zero]
    rw [tsum_eq_sum (s := O) (fun q hq => if_neg hq)]
    simp
  rw [hsum] at htrace
  rw [hsumNorm] at henergy
  refine ⟨P, henergy, ?_⟩
  simpa only [Function.comp_def, xiPolynomialGaussianHeatTraceReal,
    xiPolynomialGaussianHeatTrace, Complex.neg_re, Complex.natCast_re] using
      Complex.continuous_re.continuousAt.tendsto.comp htrace

end RHTower
