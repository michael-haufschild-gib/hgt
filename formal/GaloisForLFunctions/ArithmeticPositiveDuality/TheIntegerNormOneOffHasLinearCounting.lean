import GaloisForLFunctions.ArithmeticPositiveDuality.AnIntegerNormBeurlingOneOff
import GaloisForLFunctions.HTGeometry.OccupationEulerProduct
import GaloisForLFunctions.PNTPlus.Wiener

/-!
# Linear counting for an integer-norm Euler product with a finite zero layer

Collect the occupation expansion of the rounded Euler product by its natural-number norms.
The resulting coefficients are nonnegative integers. Removing the simple pole at `1` leaves
an analytic function on `Re s > 1/2`, so Wiener–Ikehara gives linear counting without any
vertical growth hypothesis.
-/

set_option autoImplicit false

open Complex Filter Topology Set
open scoped BigOperators
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff

namespace GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

noncomputable section

/-- The natural-number norm of a finite occupation of the rounded generators. -/
def integerNorm (P : Params) (v : ℕ →₀ ℕ) : ℕ :=
  v.prod fun k m => primeNorm P k ^ m

theorem integerNorm_pos (P : Params) (v : ℕ →₀ ℕ) : 0 < integerNorm P v := by
  classical
  unfold integerNorm Finsupp.prod
  exact Finset.prod_pos fun k _ => pow_pos (lt_of_lt_of_le (by norm_num) (primeNorm_ge_two P k)) _

/-- Multiplicity of an ordinary integer in the free multiplicative system. -/
def integerCoeff (P : Params) (n : ℕ) : ℕ :=
  Nat.card {v : ℕ →₀ ℕ // integerNorm P v = n}

private def occupationTerm (P : Params) (s : ℂ) (v : ℕ →₀ ℕ) : ℂ :=
  cexp (-(s * Real.log (integerNorm P v)))

private theorem occupationTerm_eq (P : Params) (s : ℂ) (v : ℕ →₀ ℕ) :
    occupationTerm P s v =
      _root_.HTGeometry.nomeMonomial (fun k => cexp (-(s * roundedAtom P k))) v := by
  classical
  have hlog : Real.log (integerNorm P v) =
      ∑ k ∈ v.support, (v k : ℝ) * roundedAtom P k := by
    unfold integerNorm Finsupp.prod
    push_cast
    rw [Real.log_prod (fun k _ => pow_ne_zero _ (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (primeNorm_ge_two P k)).ne'))]
    simp only [Real.log_pow, roundedAtom]
  rw [occupationTerm, hlog, _root_.HTGeometry.nomeMonomial, Finsupp.prod]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem primeTerm_norm_lt (P : Params) {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    ‖cexp (-(s * roundedAtom P k))‖ < 1 := by
  rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
  have hp := roundedAtom_pos P k
  nlinarith only [hs, hp]

private theorem summable_occupationTerm_norm (P : Params) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v => ‖occupationTerm P s v‖ := by
  have h := (_root_.HTGeometry.summable_nomeMonomial_pow_iff 0
    (fun k => cexp (-(s * roundedAtom P k))) (primeTerm_norm_lt P hs)).2 (by
      simpa only [zero_add, pow_one, norm_cexp_neg_mul] using summable_exp_roundedAtom P hs)
  simpa only [zero_add, pow_one, occupationTerm_eq] using h

private theorem hasSum_occupationTerm (P : Params) {s : ℂ} (hs : 1 < s.re) :
    HasSum (occupationTerm P s) (roundedContinuation P s) := by
  have hprod := _root_.HTGeometry.hasProd_inv_one_sub_nome
    (fun k => cexp (-(s * roundedAtom P k))) (primeTerm_norm_lt P hs)
    (by simpa only [norm_cexp_neg_mul] using summable_exp_roundedAtom P hs)
  have heq := hprod.unique (hasProd_roundedContinuation P hs)
  rw [← heq]
  simpa only [occupationTerm_eq] using (summable_occupationTerm_norm P hs).of_norm.hasSum

/-- Every ordinary integer has only finitely many occupation representations. -/
theorem finite_integerNorm_fiber (P : Params) (n : ℕ) :
    Finite {v : ℕ →₀ ℕ // integerNorm P v = n} := by
  have h := (summable_occupationTerm_norm P (s := 2) (by norm_num)).subtype
    (fun v => integerNorm P v = n)
  have hc : Summable (fun _ : {v : ℕ →₀ ℕ // integerNorm P v = n} =>
      Real.exp (-(2 * Real.log n))) := h.congr fun v => by
    change ‖cexp (-((2 : ℂ) * Real.log (integerNorm P v.1)))‖ = _
    rw [v.2, norm_cexp_neg_mul]
    norm_num
  exact Finite.of_summable_const (Real.exp_pos _) hc

private theorem occupation_fiber_sum (P : Params) (s : ℂ) (n : ℕ) :
    (∑' v : {v : ℕ →₀ ℕ // integerNorm P v = n}, occupationTerm P s v.1) =
      (integerCoeff P n : ℂ) * cexp (-(s * Real.log n)) := by
  letI := finite_integerNorm_fiber P n
  letI := Fintype.ofFinite {v : ℕ →₀ ℕ // integerNorm P v = n}
  have he (v : {v : ℕ →₀ ℕ // integerNorm P v = n}) :
      occupationTerm P s v.1 = cexp (-(s * Real.log n)) := by
    unfold occupationTerm
    rw [v.2]
  simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    integerCoeff, Nat.card_eq_fintype_card]

private theorem hasSum_coeff_exp (P : Params) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => (integerCoeff P n : ℂ) * cexp (-(s * Real.log n)))
      (roundedContinuation P s) := by
  have h := (hasSum_occupationTerm P hs).tsum_fiberwise (integerNorm P)
  exact h.congr_fun fun n => (occupation_fiber_sum P s n).symm

@[simp] theorem integerCoeff_zero (P : Params) : integerCoeff P 0 = 0 := by
  haveI : IsEmpty {v : ℕ →₀ ℕ // integerNorm P v = 0} :=
    ⟨fun v => (integerNorm_pos P v.1).ne' v.2⟩
  simp [integerCoeff]

private theorem coeff_term_eq (P : Params) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (integerCoeff P n : ℂ)) s n =
      (integerCoeff P n : ℂ) * cexp (-(s * Real.log n)) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [LSeries.term, if_neg hn, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
      hlog, div_eq_mul_inv, ← Complex.exp_neg]
    congr 2
    ring

/-- The Euler product is an absolutely convergent Dirichlet series with natural coefficients. -/
theorem hasSum_integerCoeff (P : Params) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (integerCoeff P n : ℂ)) s (roundedContinuation P s) := by
  exact (hasSum_coeff_exp P hs).congr_fun fun n => coeff_term_eq P s n

theorem lseries_integerCoeff (P : Params) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (integerCoeff P n : ℂ)) s = roundedContinuation P s :=
  (hasSum_integerCoeff P hs).LSeries_eq

/-- Analytic numerator after removing the pole at `1`. -/
def poleFactor (P : Params) (s : ℂ) : ℂ :=
  (((s - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2) * (s + (4 * P.μ - 1)) /
    ((s + (3 * P.μ - 1 - P.ν)) * (s + (3 * P.μ - 1 + P.ν)))) *
      cexp (s * boundedLaplace P.discrepancy s +
        primeCorrection P.atom (roundedAtom P) s + primePowerRemainder (roundedAtom P) s)

theorem roundedContinuation_eq_poleFactor (P : Params) (s : ℂ) :
    roundedContinuation P s = poleFactor P s / (s - 1) := by
  rw [roundedContinuation, Params.continuation, mul_assoc, ← Complex.exp_add]
  have he : s * boundedLaplace P.discrepancy s + primePowerRemainder P.atom s +
      (primeCorrection P.atom (roundedAtom P) s +
        primePowerRemainder (roundedAtom P) s - primePowerRemainder P.atom s) =
      s * boundedLaplace P.discrepancy s + primeCorrection P.atom (roundedAtom P) s +
        primePowerRemainder (roundedAtom P) s := by ring
  rw [he, poleFactor, RHTower.BeurlingOverRegularIntegers.overRegularZeta]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem differentiableOn_poleFactor (P : Params) :
    DifferentiableOn ℂ (poleFactor P) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  change 1 / 2 < s.re at hs
  have hhalf : IsOpen {z : ℂ | 1 / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hpos : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hlow : s + (3 * P.μ - 1 - P.ν) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith only [P.hlow, hs, hr]
  have hhigh : s + (3 * P.μ - 1 + P.ν) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith only [P.hhigh, hs, hr]
  have hrat : DifferentiableAt ℂ (fun z : ℂ =>
      ((z - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2) * (z + (4 * P.μ - 1)) /
        ((z + (3 * P.μ - 1 - P.ν)) * (z + (3 * P.μ - 1 + P.ν)))) s :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (mul_ne_zero hlow hhigh)
  have hΛ := (differentiableOn_boundedLaplace P.measurable_discrepancy
    P.abs_discrepancy_le).differentiableAt
      (hpos.mem_nhds (by change 0 < s.re; linarith only [hs]))
  have hC := (differentiableOn_primeCorrection P.atom_pos (atom_le_roundedAtom P)
    (roundedAtom_le P) (fun a ha => P.summable_exp_atom ha)).differentiableAt
      (hpos.mem_nhds (by change 0 < s.re; linarith only [hs]))
  have hR := (differentiableOn_primePowerRemainder (roundedAtom_pos P)
    (roundedAtom_zero_le P) (fun a ha => summable_exp_roundedAtom P ha)).differentiableAt
      (hhalf.mem_nhds hs)
  exact (hrat.mul (((differentiableAt_id.mul hΛ).add hC).add hR).cexp).differentiableWithinAt

theorem poleFactor_one_ne_zero (P : Params) : poleFactor P 1 ≠ 0 := by
  have hμ : 0 < P.μ := by linarith only [P.hμ1]
  have hlow : 0 < 3 * P.μ - P.ν := by linarith only [P.hν]
  have hhigh : 0 < 3 * P.μ + P.ν := by linarith only [hμ, P.hν0]
  have hnum : 0 < (P.μ ^ 2 + P.γ ^ 2) * (4 * P.μ) := by positivity
  have hden : 0 < (3 * P.μ - P.ν) * (3 * P.μ + P.ν) := mul_pos hlow hhigh
  have hrat : (((1 : ℂ) - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2) *
      (1 + (4 * P.μ - 1)) /
        ((1 + (3 * P.μ - 1 - P.ν)) * (1 + (3 * P.μ - 1 + P.ν))) =
      (((P.μ ^ 2 + P.γ ^ 2) * (4 * P.μ) /
        ((3 * P.μ - P.ν) * (3 * P.μ + P.ν)) : ℝ) : ℂ) := by
    push_cast
    congr 1 <;> ring
  rw [poleFactor, hrat]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hnum hden).ne')
    (Complex.exp_ne_zero _)

private theorem continuation_ofReal (P : Params) {σ : ℝ} (hσ : 1 < σ) :
    (roundedContinuation P σ).im = 0 ∧ 0 ≤ (roundedContinuation P σ).re := by
  have h := hasSum_occupationTerm P (s := (σ : ℂ)) hσ
  have he (v : ℕ →₀ ℕ) : occupationTerm P (σ : ℂ) v =
      (Real.exp (-(σ * Real.log (integerNorm P v))) : ℂ) := by
    rw [occupationTerm, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_exp]
  constructor
  · have hi := (Complex.hasSum_im h).tsum_eq.symm
    simpa only [he, Complex.ofReal_im, tsum_zero] using hi
  · rw [← (Complex.hasSum_re h).tsum_eq]
    exact tsum_nonneg fun v => by rw [he, Complex.ofReal_re]; exact (Real.exp_pos _).le

private theorem poleFactor_ofReal (P : Params) {σ : ℝ} (hσ : 1 < σ) :
    (poleFactor P σ).im = 0 ∧ 0 ≤ (poleFactor P σ).re := by
  have hz : (σ : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith only [this, hσ]
  have he : poleFactor P σ = roundedContinuation P σ * ((σ : ℂ) - 1) := by
    rw [roundedContinuation_eq_poleFactor, div_mul_cancel₀ _ hz]
  obtain ⟨hi, hr⟩ := continuation_ofReal P hσ
  rw [he]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    hi, sub_zero, mul_zero, zero_mul, add_zero]
  exact ⟨True.intro, mul_nonneg hr (sub_nonneg.mpr hσ.le)⟩

/-- The simple-pole residue, expressed as a real number. -/
def countingDensity (P : Params) : ℝ := (poleFactor P 1).re

theorem poleFactor_one_real_pos (P : Params) :
    poleFactor P 1 = (countingDensity P : ℂ) ∧ 0 < countingDensity P := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hc := (differentiableOn_poleFactor P).differentiableAt
    (hopen.mem_nhds (by norm_num : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re}))
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

/-- Natural coefficient counting has a positive linear asymptotic. -/
theorem tendsto_integerCoeff_count (P : Params) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (integerCoeff P n : ℝ)) / N)
      atTop (𝓝 (countingDensity P)) := by
  let G := dslope (poleFactor P) 1
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hn : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
    hopen.mem_nhds (by norm_num)
  have hdiff := differentiableOn_poleFactor P
  have hG : ContinuousOn G {s : ℂ | 1 ≤ s.re} :=
    ((continuousOn_dslope hn).2
      ⟨hdiff.continuousOn, hdiff.differentiableAt hn⟩).mono
      (fun s hs => by change 1 ≤ s.re at hs; change 1 / 2 < s.re; linarith only [hs])
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
    rw [lseries_integerCoeff P hs, roundedContinuation_eq_poleFactor,
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

/-- Integer Euler norms and linear integer counting coexist with an isolated zero pair. -/
theorem exists_integer_norm_linear_count_one_off (γ : ℝ) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} := by
  let P := fixedParams γ
  refine ⟨primeNorm P, integerCoeff P, primeNorm_ge_two P, roundedContinuation P,
    countingDensity P, (poleFactor_one_real_pos P).2, ?_, tendsto_integerCoeff_count P,
    differentiableOn_roundedContinuation P, ?_⟩
  · intro s hs
    exact ⟨hasProd_roundedContinuation P hs, hasSum_integerCoeff P hs⟩
  · have hz := rounded_zeros_right_of_eq_pair P (h := 0) (by norm_num [P, fixedParams]) le_rfl
    norm_num [P, fixedParams] at hz ⊢
    exact hz

end
end GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff.exists_integer_norm_linear_count_one_off
