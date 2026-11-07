import GaloisForLFunctions.ArithmeticPositiveDuality.ARationalPrimeBeurlingOneOff
import GaloisForLFunctions.ArithmeticPositiveDuality.IntegerOccupationCoefficients
import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerNormOneOffHasLinearCounting

/-!
# Multiplicative coefficients and linear counting with a finite zero layer

The rational-prime occupation product has multiplicative natural coefficients. Its numerator
after removing the pole at `1` is holomorphic on `Re s > 17/30` and positive at `1`.
Wiener–Ikehara therefore gives positive linear counting, while the zero set remains exactly
the prescribed pair `3/5 ± iγ`.
-/

set_option autoImplicit false

open Complex Filter Topology Set
open scoped BigOperators
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff

namespace GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff

noncomputable section

def integerCoeff (P : Params) : ℕ → ℕ := IntegerOccupation.coeff (primeNorm P)

theorem hasSum_integerCoeff (P : Params) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (integerCoeff P n : ℂ)) s (continuation P s) :=
  IntegerOccupation.hasSum_coeff (fun k => (primeNorm_prime P k).two_le)
    (fun _ ha => summable_exp_roundedAtom P ha) hs (hasProd_continuation P hs)

/-- Quotient between prime rounding and integer rounding, expressed as an exponential. -/
def logCorrection (P : Params) (s : ℂ) : ℂ :=
  IntegerNormOneOff.primeCorrection P.atom (roundedAtom P) s -
    IntegerNormOneOff.primeCorrection P.atom (IntegerNormOneOff.roundedAtom P) s +
      primePowerRemainder (roundedAtom P) s -
        primePowerRemainder (IntegerNormOneOff.roundedAtom P) s

def poleFactor (P : Params) (s : ℂ) : ℂ :=
  IntegerNormOneOff.poleFactor P s * cexp (logCorrection P s)

theorem continuation_eq_poleFactor (P : Params) (s : ℂ) :
    continuation P s = poleFactor P s / (s - 1) := by
  have he : continuation P s = IntegerNormOneOff.roundedContinuation P s *
      cexp (logCorrection P s) := by
    rw [continuation, IntegerNormOneOff.roundedContinuation, mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    unfold logCorrection
    ring
  rw [he, IntegerNormOneOff.roundedContinuation_eq_poleFactor, poleFactor]
  ring

theorem differentiableOn_poleFactor (P : Params) :
    DifferentiableOn ℂ (poleFactor P) {s : ℂ | 17 / 30 < s.re} := by
  intro s hs
  change 17 / 30 < s.re at hs
  have hhalf : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpos : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hround : IsOpen {s : ℂ | 17 / 30 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsHalf : 1 / 2 < s.re := by linarith only [hs]
  have hH := (IntegerNormOneOff.differentiableOn_poleFactor P).differentiableAt
    (hhalf.mem_nhds hsHalf)
  have hC := (differentiableOn_primeCorrection P).differentiableAt (hround.mem_nhds hs)
  have hI := (IntegerNormOneOff.differentiableOn_primeCorrection P.atom_pos
    (IntegerNormOneOff.atom_le_roundedAtom P) (IntegerNormOneOff.roundedAtom_le P)
    (fun a ha => P.summable_exp_atom ha)).differentiableAt
      (hpos.mem_nhds (by change 0 < s.re; linarith only [hs]))
  have hR := (differentiableOn_primePowerRemainder (roundedAtom_pos P) (roundedAtom_zero_le P)
    (fun a ha => summable_exp_roundedAtom P ha)).differentiableAt (hhalf.mem_nhds hsHalf)
  have hQ := (differentiableOn_primePowerRemainder (IntegerNormOneOff.roundedAtom_pos P)
    (IntegerNormOneOff.roundedAtom_zero_le P)
    (fun a ha => IntegerNormOneOff.summable_exp_roundedAtom P ha)).differentiableAt
      (hhalf.mem_nhds hsHalf)
  exact (hH.mul (((hC.sub hI).add hR).sub hQ).cexp).differentiableWithinAt

theorem poleFactor_one_ne_zero (P : Params) : poleFactor P 1 ≠ 0 :=
  mul_ne_zero (IntegerNormOneOff.poleFactor_one_ne_zero P) (Complex.exp_ne_zero _)

private theorem continuation_ofReal (P : Params) {σ : ℝ} (hσ : 1 < σ) :
    (continuation P σ).im = 0 ∧ 0 ≤ (continuation P σ).re := by
  have h := IntegerOccupation.hasSum_coeff_exp (fun k => (primeNorm_prime P k).two_le)
    (fun a ha => summable_exp_roundedAtom P ha) (s := (σ : ℂ)) hσ
      (hasProd_continuation P hσ)
  have he (n : ℕ) : (IntegerOccupation.coeff (primeNorm P) n : ℂ) *
      cexp (-((σ : ℂ) * Real.log n)) =
        (((integerCoeff P n : ℝ) * Real.exp (-(σ * Real.log n)) : ℝ) : ℂ) := by
    simp only [integerCoeff, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_exp,
      Complex.ofReal_natCast]
  constructor
  · have hi := (Complex.hasSum_im h).tsum_eq.symm
    simpa only [he, Complex.ofReal_im, tsum_zero] using hi
  · rw [← (Complex.hasSum_re h).tsum_eq]
    exact tsum_nonneg fun n => by
      rw [he, Complex.ofReal_re]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le

private theorem poleFactor_ofReal (P : Params) {σ : ℝ} (hσ : 1 < σ) :
    (poleFactor P σ).im = 0 ∧ 0 ≤ (poleFactor P σ).re := by
  have hz : (σ : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith only [this, hσ]
  have he : poleFactor P σ = continuation P σ * ((σ : ℂ) - 1) := by
    rw [continuation_eq_poleFactor, div_mul_cancel₀ _ hz]
  obtain ⟨hi, hr⟩ := continuation_ofReal P hσ
  rw [he]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    hi, sub_zero, mul_zero, zero_mul, add_zero]
  exact ⟨True.intro, mul_nonneg hr (sub_nonneg.mpr hσ.le)⟩

def countingDensity (P : Params) : ℝ := (poleFactor P 1).re

theorem poleFactor_one_real_pos (P : Params) :
    poleFactor P 1 = (countingDensity P : ℂ) ∧ 0 < countingDensity P := by
  have hopen : IsOpen {s : ℂ | 17 / 30 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hc := (differentiableOn_poleFactor P).differentiableAt
    (hopen.mem_nhds (by norm_num : (1 : ℂ) ∈ {s : ℂ | 17 / 30 < s.re}))
  have hlim : Tendsto (fun x : ℝ => poleFactor P (x : ℂ)) (𝓝[>] 1)
      (𝓝 (poleFactor P 1)) :=
    hc.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hi0 : Tendsto (fun x : ℝ => (poleFactor P (x : ℂ)).im) (𝓝[>] 1) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (poleFactor_ofReal P hx).1.symm
  have hi : (poleFactor P 1).im = 0 :=
    tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hlim) hi0
  have hr : 0 ≤ countingDensity P := by
    apply ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (poleFactor_ofReal P hx).2
  have he : poleFactor P 1 = (countingDensity P : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hi
  refine ⟨he, lt_of_le_of_ne hr ?_⟩
  intro hz
  exact poleFactor_one_ne_zero P (by rw [he, ← hz, Complex.ofReal_zero])

/-- Positive residue and the continuous boundary value give the linear counting law. -/
theorem tendsto_integerCoeff_count (P : Params) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (integerCoeff P n : ℝ)) / N)
      atTop (𝓝 (countingDensity P)) := by
  let G := dslope (poleFactor P) 1
  have hopen : IsOpen {s : ℂ | 17 / 30 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hn : {s : ℂ | 17 / 30 < s.re} ∈ 𝓝 (1 : ℂ) := hopen.mem_nhds (by norm_num)
  have hdiff := differentiableOn_poleFactor P
  have hG : ContinuousOn G {s : ℂ | 1 ≤ s.re} :=
    ((continuousOn_dslope hn).2
      ⟨hdiff.continuousOn, hdiff.differentiableAt hn⟩).mono
      (fun s hs => by change 1 ≤ s.re at hs; change 17 / 30 < s.re; linarith only [hs])
  have hG' : Set.EqOn G
      (fun s => LSeries (fun n => ((integerCoeff P n : ℝ) : ℂ)) s -
        (countingDensity P : ℂ) / (s - 1)) {s : ℂ | 1 < s.re} := by
    intro s hs
    change 1 < s.re at hs
    change dslope (poleFactor P) 1 s =
      LSeries (fun n => ((integerCoeff P n : ℝ) : ℂ)) s -
        (countingDensity P : ℂ) / (s - 1)
    have hs1 : s ≠ 1 := by intro he; subst s; norm_num at hs
    rw [show (fun n => ((integerCoeff P n : ℝ) : ℂ)) =
      (fun n => (integerCoeff P n : ℂ)) by funext n; simp only [Complex.ofReal_natCast]]
    rw [(hasSum_integerCoeff P hs).LSeries_eq, continuation_eq_poleFactor,
      ← (poleFactor_one_real_pos P).1, ← sub_div, dslope_of_ne _ hs1, slope_def_field]
  have hf : ∀ σ : ℝ, 1 < σ →
      Summable (nterm (fun n => ((integerCoeff P n : ℝ) : ℂ)) σ) := by
    intro σ hσ
    have h := (hasSum_integerCoeff P (s := (σ : ℂ)) hσ).summable.norm
    change Summable (fun n => nterm (fun n => ((integerCoeff P n : ℝ) : ℂ)) σ n)
    simp only [nterm_eq_norm_term, Complex.ofReal_natCast]
    exact h
  simpa only [cumsum] using WienerIkeharaTheorem''
    (f := fun n => (integerCoeff P n : ℝ)) (A := countingDensity P) (G := G)
    (fun n => Nat.cast_nonneg _) hf hG hG'

/-- A rational-prime Euler product with multiplicative natural coefficients, positive linear
counting, and exactly the prescribed zero pair on `Re s > 17/30`, away from `1`. -/
theorem exists_rational_prime_multiplicative_linear_count_one_off (γ : ℝ) :
    ∃ q a : ℕ → ℕ, (∀ k, (q k).Prime) ∧ a 0 = 0 ∧ a 1 = 1 ∧
      (∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n) ∧
      ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧
        (∀ s : ℂ, 1 < s.re →
          HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
          LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
        Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
        DifferentiableOn ℂ F {s : ℂ | 17 / 30 < s.re ∧ s ≠ 1} ∧
        {s : ℂ | 17 / 30 < s.re ∧ s ≠ 1 ∧ F s = 0} =
          {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} := by
  let P := IntegerNormOneOff.fixedParams γ
  refine ⟨primeNorm P, integerCoeff P, primeNorm_prime P,
    IntegerOccupation.coeff_zero (fun k => (primeNorm_prime P k).two_le),
    IntegerOccupation.coeff_one (fun k => (primeNorm_prime P k).two_le),
    fun _ _ h => IntegerOccupation.coeff_mul_of_coprime (primeNorm_prime P) h,
    continuation P, countingDensity P, (poleFactor_one_real_pos P).2,
    fun s hs => ⟨hasProd_continuation P hs, hasSum_integerCoeff P hs⟩,
    tendsto_integerCoeff_count P, differentiableOn_continuation P, ?_⟩
  simp only [continuation_eq_zero_iff]
  have hz := P.zeros_right_of_eq_pair (h := (1 / 15 : ℝ))
    (by norm_num [P, IntegerNormOneOff.fixedParams]) (by norm_num)
  norm_num [P, IntegerNormOneOff.fixedParams] at hz ⊢
  exact hz

end
end GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff.exists_rational_prime_multiplicative_linear_count_one_off
