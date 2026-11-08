import GaloisForLFunctions.ArithmeticPositiveDuality.ADiscreteOneOffCrossesTheCriticalLine
import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerNormOneOffHasLinearCounting

/-!
# An integer-norm one-off with linear counting that crosses the critical line

Round the corrected discrete primes of `ADiscreteOneOffCrossesTheCriticalLine` up to natural
numbers `q_k = ⌈e^{t_k}⌉`. The rounding moves each logarithmic norm by at most `e^{-t_k}`, so the
prime and prime-square sums change by functions holomorphic on `Re s > 0`, and the Euler product
`Π_k (1 − q_k^{-s})^{-1}` keeps the continuation to `Re s > 1/3`, `s ≠ 1`, with the single
off-line pair as zeros there.

* **Natural coefficients** (`hasSum_genCoeff`). For any generators `q_k ≥ 2` with
  `Σ_k q_k^{-a} < ∞` (`a > 1`), the Euler product is the Dirichlet series `Σ_n a_n n^{-s}`,
  `a_n = #{occupations of norm n} ∈ ℕ`.
* **Linear counting** (`tendsto_genCoeff_count`). If the Euler product is `H(s)/(s − 1)` with `H`
  holomorphic on a half-plane `Re s > σ₁`, `σ₁ < 1`, and `H(1) ≠ 0`, then `H(1) > 0` and
  `Σ_{n<N} a_n / N → H(1)` (Wiener–Ikehara; no vertical growth hypothesis).
* **The integer-norm one-off across the line** (`exists_integer_norm_linear_count_one_off_across`).
  For every height `γ` there are natural numbers `q_k ≥ 2` and `a_n` with
  `Π_k (1 − q_k^{-s})^{-1} = Σ_n a_n n^{-s}` on `Re s > 1`, `Σ_{n<N} a_n ∼ A N` with `A > 0`,
  continuation holomorphic on `Re s > 1/3`, `s ≠ 1`, whose zeros there are exactly `3/5 ± iγ`, and
  which has no zero on the critical line.

So positive integer Euler products with linear counting and continuation across `Re s = 1/2`
carry a finite off-line layer: of the hypotheses "Euler product, integrality, linear counting,
continuation across the line, functional equation", only the functional equation can exclude it.
-/

set_option autoImplicit false

open Complex Filter Topology Set
open scoped BigOperators
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff

namespace GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

noncomputable section

/-! ### Euler products over natural generators -/

/-- The natural-number norm of a finite occupation of the generators `q`. -/
def genNorm (q : ℕ → ℕ) (v : ℕ →₀ ℕ) : ℕ := v.prod fun k m => q k ^ m

theorem genNorm_pos {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) (v : ℕ →₀ ℕ) : 0 < genNorm q v := by
  classical
  unfold genNorm Finsupp.prod
  exact Finset.prod_pos fun k _ => pow_pos (lt_of_lt_of_le (by norm_num) (hq k)) _

/-- The number `a_n` of occupations of norm `n`. -/
def genCoeff (q : ℕ → ℕ) (n : ℕ) : ℕ := Nat.card {v : ℕ →₀ ℕ // genNorm q v = n}

private def genTerm (q : ℕ → ℕ) (s : ℂ) (v : ℕ →₀ ℕ) : ℂ :=
  cexp (-(s * Real.log (genNorm q v)))

private theorem genTerm_eq {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) (s : ℂ) (v : ℕ →₀ ℕ) :
    genTerm q s v = _root_.HTGeometry.nomeMonomial (fun k => cexp (-(s * Real.log (q k)))) v := by
  classical
  have hlog : Real.log (genNorm q v) = ∑ k ∈ v.support, (v k : ℝ) * Real.log (q k) := by
    unfold genNorm Finsupp.prod
    push_cast
    rw [Real.log_prod (fun k _ => pow_ne_zero _ (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (hq k)).ne'))]
    simp only [Real.log_pow]
  rw [genTerm, hlog, _root_.HTGeometry.nomeMonomial, Finsupp.prod]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem log_gen_pos {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) (k : ℕ) : 0 < Real.log (q k) :=
  Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two (hq k)))

private theorem genPrime_norm_lt {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) {s : ℂ} (hs : 1 < s.re)
    (k : ℕ) : ‖cexp (-(s * Real.log (q k)))‖ < 1 := by
  rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
  have hp := log_gen_pos hq k
  nlinarith only [hs, hp]

private theorem summable_genTerm_norm {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k))))
    {s : ℂ} (hs : 1 < s.re) : Summable fun v => ‖genTerm q s v‖ := by
  have h := (_root_.HTGeometry.summable_nomeMonomial_pow_iff 0
    (fun k => cexp (-(s * Real.log (q k)))) (genPrime_norm_lt hq hs)).2 (by
      simpa only [zero_add, pow_one, norm_cexp_neg_mul] using hsum s.re hs)
  simpa only [zero_add, pow_one, genTerm_eq hq] using h

/-- The Euler logarithm of the generators `q`. -/
def genEulerLog (q : ℕ → ℕ) (s : ℂ) : ℂ := ∑' k, -Complex.log (1 - cexp (-(s * Real.log (q k))))

private theorem hasSum_genTerm {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hmono : ∀ k, Real.log (q 0) ≤ Real.log (q k))
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k))))
    {s : ℂ} (hs : 1 < s.re) : HasSum (genTerm q s) (cexp (genEulerLog q s)) := by
  have hprod := _root_.HTGeometry.hasProd_inv_one_sub_nome
    (fun k => cexp (-(s * Real.log (q k)))) (genPrime_norm_lt hq hs)
    (by simpa only [norm_cexp_neg_mul] using hsum s.re hs)
  have heq := hprod.unique (hasProd_euler (log_gen_pos hq) hmono hsum hs)
  rw [genEulerLog, ← heq]
  simpa only [genTerm_eq hq] using (summable_genTerm_norm hq hsum hs).of_norm.hasSum

theorem finite_genNorm_fiber {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k)))) (n : ℕ) :
    Finite {v : ℕ →₀ ℕ // genNorm q v = n} := by
  have h := (summable_genTerm_norm hq hsum (s := 2) (by norm_num)).subtype
    (fun v => genNorm q v = n)
  have hc : Summable (fun _ : {v : ℕ →₀ ℕ // genNorm q v = n} =>
      Real.exp (-(2 * Real.log n))) := h.congr fun v => by
    change ‖cexp (-((2 : ℂ) * Real.log (genNorm q v.1)))‖ = _
    rw [v.2, norm_cexp_neg_mul]
    norm_num
  exact Finite.of_summable_const (Real.exp_pos _) hc

private theorem gen_fiber_sum {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k)))) (s : ℂ) (n : ℕ) :
    (∑' v : {v : ℕ →₀ ℕ // genNorm q v = n}, genTerm q s v.1) =
      (genCoeff q n : ℂ) * cexp (-(s * Real.log n)) := by
  letI := finite_genNorm_fiber hq hsum n
  letI := Fintype.ofFinite {v : ℕ →₀ ℕ // genNorm q v = n}
  have he (v : {v : ℕ →₀ ℕ // genNorm q v = n}) :
      genTerm q s v.1 = cexp (-(s * Real.log n)) := by
    unfold genTerm
    rw [v.2]
  simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    genCoeff, Nat.card_eq_fintype_card]

theorem genCoeff_zero {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) : genCoeff q 0 = 0 := by
  haveI : IsEmpty {v : ℕ →₀ ℕ // genNorm q v = 0} :=
    ⟨fun v => (genNorm_pos hq v.1).ne' v.2⟩
  simp [genCoeff]

private theorem gen_term_eq {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (genCoeff q n : ℂ)) s n =
      (genCoeff q n : ℂ) * cexp (-(s * Real.log n)) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, genCoeff_zero hq]
  · have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [LSeries.term, if_neg hn, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
      hlog, div_eq_mul_inv, ← Complex.exp_neg]
    congr 2
    ring

/-- **The Euler product is a Dirichlet series with natural coefficients.** -/
theorem hasSum_genCoeff {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hmono : ∀ k, Real.log (q 0) ≤ Real.log (q k))
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k))))
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (genCoeff q n : ℂ)) s (cexp (genEulerLog q s)) := by
  have h := (hasSum_genTerm hq hmono hsum hs).tsum_fiberwise (genNorm q)
  exact (h.congr_fun fun n => (gen_fiber_sum hq hsum s n).symm).congr_fun
    fun n => gen_term_eq hq s n

private theorem genEuler_ofReal {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hmono : ∀ k, Real.log (q 0) ≤ Real.log (q k))
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k))))
    {σ : ℝ} (hσ : 1 < σ) :
    (cexp (genEulerLog q σ)).im = 0 ∧ 0 ≤ (cexp (genEulerLog q σ)).re := by
  have h := hasSum_genTerm hq hmono hsum (s := (σ : ℂ)) hσ
  have he (v : ℕ →₀ ℕ) : genTerm q (σ : ℂ) v =
      (Real.exp (-(σ * Real.log (genNorm q v))) : ℂ) := by
    rw [genTerm, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_exp]
  constructor
  · have hi := (Complex.hasSum_im h).tsum_eq.symm
    simpa only [he, Complex.ofReal_im, tsum_zero] using hi
  · rw [← (Complex.hasSum_re h).tsum_eq]
    exact tsum_nonneg fun v => by rw [he, Complex.ofReal_re]; exact (Real.exp_pos _).le

/-- **Linear counting.** If the Euler product of natural generators is `H(s)/(s − 1)` on
`Re s > 1`, with `H` holomorphic on `Re s > σ₁` (`σ₁ < 1`) and `H(1) ≠ 0`, then `H(1)` is a
positive real `A` and `Σ_{n<N} a_n / N → A`. -/
theorem tendsto_genCoeff_count {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hmono : ∀ k, Real.log (q 0) ≤ Real.log (q k))
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k))))
    {H : ℂ → ℂ} {σ₁ : ℝ} (hσ₁ : σ₁ < 1) (hH : DifferentiableOn ℂ H {s : ℂ | σ₁ < s.re})
    (hH1 : H 1 ≠ 0) (hF : ∀ s : ℂ, 1 < s.re → cexp (genEulerLog q s) = H s / (s - 1)) :
    ∃ A : ℝ, 0 < A ∧ H 1 = A ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (genCoeff q n : ℝ)) / N) atTop (𝓝 A) := by
  have hopen : IsOpen {s : ℂ | σ₁ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hn : {s : ℂ | σ₁ < s.re} ∈ 𝓝 (1 : ℂ) := hopen.mem_nhds (by simpa using hσ₁)
  -- `H` is real and nonnegative on `(1, ∞)`, hence at `1`
  have hHreal : ∀ σ : ℝ, 1 < σ → (H σ).im = 0 ∧ 0 ≤ (H σ).re := by
    intro σ hσ
    have hz : (σ : ℂ) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have := congrArg Complex.re he
      simp only [Complex.ofReal_re, Complex.one_re] at this
      linarith only [this, hσ]
    have he : H σ = cexp (genEulerLog q σ) * ((σ : ℂ) - 1) := by
      rw [hF σ (by simpa using hσ), div_mul_cancel₀ _ hz]
    obtain ⟨hi, hr⟩ := genEuler_ofReal hq hmono hsum hσ
    rw [he]
    simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      hi, sub_zero, mul_zero, zero_mul, add_zero]
    exact ⟨True.intro, mul_nonneg hr (sub_nonneg.mpr hσ.le)⟩
  have hc := hH.differentiableAt hn
  have hlim : Tendsto (fun x : ℝ => H (x : ℂ)) (𝓝[>] 1) (𝓝 (H 1)) :=
    hc.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hi0 : Tendsto (fun x : ℝ => (H (x : ℂ)).im) (𝓝[>] 1) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hHreal x hx).1.symm
  have hi : (H 1).im = 0 :=
    tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hlim) hi0
  have hr : 0 ≤ (H 1).re := by
    apply ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hHreal x hx).2
  have he : H 1 = ((H 1).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hi
  have hA : 0 < (H 1).re := lt_of_le_of_ne hr fun hz => hH1 (by rw [he, ← hz, Complex.ofReal_zero])
  refine ⟨(H 1).re, hA, he, ?_⟩
  let G := dslope H 1
  have hG : ContinuousOn G {s : ℂ | 1 ≤ s.re} :=
    ((continuousOn_dslope hn).2 ⟨hH.continuousOn, hc⟩).mono
      (fun s hs => by change 1 ≤ s.re at hs; change σ₁ < s.re; linarith only [hs, hσ₁])
  have hG' : Set.EqOn G
      (fun s => LSeries (fun n => ((genCoeff q n : ℝ) : ℂ)) s - ((H 1).re : ℂ) / (s - 1))
      {s : ℂ | 1 < s.re} := by
    intro s hs
    change 1 < s.re at hs
    change dslope H 1 s = LSeries (fun n => ((genCoeff q n : ℝ) : ℂ)) s - ((H 1).re : ℂ) / (s - 1)
    have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
    rw [show (fun n => ((genCoeff q n : ℝ) : ℂ)) = (fun n => (genCoeff q n : ℂ)) by
      funext n; simp only [Complex.ofReal_natCast]]
    rw [(hasSum_genCoeff hq hmono hsum hs).LSeries_eq, hF s hs, ← he, ← sub_div,
      dslope_of_ne _ hs1, slope_def_field]
  have hf : ∀ σ : ℝ, 1 < σ → Summable (nterm (fun n => ((genCoeff q n : ℝ) : ℂ)) σ) := by
    intro σ hσ
    have h := (hasSum_genCoeff hq hmono hsum (s := (σ : ℂ)) hσ).summable.norm
    change Summable (fun n => nterm (fun n => ((genCoeff q n : ℝ) : ℂ)) σ n)
    simp only [nterm_eq_norm_term, Complex.ofReal_natCast]
    exact h
  simpa only [cumsum] using WienerIkeharaTheorem''
    (f := fun n => (genCoeff q n : ℝ)) (A := (H 1).re) (G := G)
    (fun n => Nat.cast_nonneg _) hf hG hG'

/-! ### The rounded corrected one-off -/

end

end GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

namespace GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff.Params

noncomputable section

open GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

variable (P : Params)

/-- Natural-number norms `q_k = ⌈e^{t_k}⌉` of the corrected discrete primes. -/
def cPrimeNorm (k : ℕ) : ℕ := ⌈Real.exp (P.catom k)⌉₊

/-- Their logarithms `log q_k`. -/
def cRounded (k : ℕ) : ℝ := Real.log (P.cPrimeNorm k)

theorem cPrimeNorm_ge_two (k : ℕ) : 2 ≤ P.cPrimeNorm k := by
  have h : (1 : ℝ) < P.cPrimeNorm k :=
    (Real.one_lt_exp_iff.mpr (P.catom_pos k)).trans_le (Nat.le_ceil _)
  exact_mod_cast h

theorem catom_le_cRounded (k : ℕ) : P.catom k ≤ P.cRounded k := (roundedLog_bounds (P.catom k)).1

theorem cRounded_le (k : ℕ) : P.cRounded k ≤ P.catom k + Real.exp (-(P.catom k)) :=
  (roundedLog_bounds (P.catom k)).2

theorem cRounded_pos (k : ℕ) : 0 < P.cRounded k := (P.catom_pos k).trans_le (P.catom_le_cRounded k)

theorem cRounded_zero_le (k : ℕ) : P.cRounded 0 ≤ P.cRounded k :=
  roundedLog_mono (P.catom_zero_le k)

theorem summable_exp_cRounded {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * P.cRounded k)) := by
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (P.summable_exp_catom ha)
  exact Real.exp_le_exp.mpr (by nlinarith only [ha, P.catom_le_cRounded k, P.catom_pos k])

/-- The rounding exponent `C(s) + C(2s)/2 + R₃^q(s) − R₃^t(s)`, `C` the prime-sum correction. -/
def roundingExponent (s : ℂ) : ℂ :=
  primeCorrection P.catom P.cRounded s + primeCorrection P.catom P.cRounded (2 * s) / 2 +
    primeCubeRemainder P.cRounded s - primeCubeRemainder P.catom s

/-- The continuation of the integer-norm Euler product. -/
def crContinuation (s : ℂ) : ℂ := P.cContinuation s * cexp (P.roundingExponent s)

/-- **The integer-norm Euler product is the continuation on `Re s > 1`.** -/
theorem genEulerLog_eq_crContinuation {s : ℂ} (hs : 1 < s.re) :
    cexp (genEulerLog P.cPrimeNorm s) = P.crContinuation s := by
  have hs2 : 1 < (2 * s).re := by simp; linarith
  obtain ⟨ht1, _⟩ := summable_neg_log P.catom_pos P.catom_zero_le
    (fun a ha => P.summable_exp_catom ha) hs
  obtain ⟨hu1, _⟩ := summable_neg_log P.cRounded_pos P.cRounded_zero_le
    (fun a ha => P.summable_exp_cRounded ha) hs
  obtain ⟨ht2, _⟩ := summable_neg_log P.catom_pos P.catom_zero_le
    (fun a ha => P.summable_exp_catom ha) hs2
  obtain ⟨hu2, _⟩ := summable_neg_log P.cRounded_pos P.cRounded_zero_le
    (fun a ha => P.summable_exp_cRounded ha) hs2
  have hc1 : primeCorrection P.catom P.cRounded s =
      (∑' k, cexp (-(s * P.cRounded k))) - ∑' k, cexp (-(s * P.catom k)) := hu1.tsum_sub ht1
  have hc2 : primeCorrection P.catom P.cRounded (2 * s) =
      (∑' k, cexp (-((2 * s) * P.cRounded k))) - ∑' k, cexp (-((2 * s) * P.catom k)) :=
    hu2.tsum_sub ht2
  have hlogu : genEulerLog P.cPrimeNorm s = ∑' k, -Complex.log (1 - cexp (-(s * P.cRounded k))) :=
    rfl
  rw [hlogu, tsum_neg_log_eq_cube P.cRounded_pos P.cRounded_zero_le
    (fun a ha => P.summable_exp_cRounded ha) hs, crContinuation,
    ← P.correctedZeta_eq_cContinuation hs, correctedZeta, cEulerLog,
    tsum_neg_log_eq_cube P.catom_pos P.catom_zero_le (fun a ha => P.summable_exp_catom ha) hs,
    ← Complex.exp_add, roundingExponent, hc1, hc2]
  congr 1
  ring

/-- **The Euler product over the natural norms `q_k`.** -/
theorem hasProd_crContinuation {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun k => (1 - cexp (-(s * Real.log (P.cPrimeNorm k))))⁻¹) (P.crContinuation s) := by
  rw [← P.genEulerLog_eq_crContinuation hs]
  exact hasProd_euler P.cRounded_pos P.cRounded_zero_le
    (fun a ha => P.summable_exp_cRounded ha) hs

theorem differentiableOn_roundingExponent :
    DifferentiableOn ℂ P.roundingExponent {s : ℂ | 1 / 3 < s.re} := by
  intro s hs
  have hs' : 1 / 3 < s.re := hs
  have hopen : ∀ c : ℝ, ∀ z : ℂ, c < z.re → {w : ℂ | c < w.re} ∈ 𝓝 z := fun c z hz =>
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hC := differentiableOn_primeCorrection P.catom_pos P.catom_le_cRounded P.cRounded_le
    (fun a ha => P.summable_exp_catom ha)
  have hC1 : DifferentiableAt ℂ (primeCorrection P.catom P.cRounded) s :=
    hC.differentiableAt (hopen 0 s (by linarith))
  have hC2 : DifferentiableAt ℂ (fun s : ℂ => primeCorrection P.catom P.cRounded (2 * s)) s :=
    (hC.differentiableAt (hopen 0 (2 * s) (by simp; linarith))).comp s
      (differentiableAt_id.const_mul 2)
  have hRu : DifferentiableAt ℂ (primeCubeRemainder P.cRounded) s :=
    (differentiableOn_primeCubeRemainder P.cRounded_pos P.cRounded_zero_le
      (fun a ha => P.summable_exp_cRounded ha)).differentiableAt (hopen (1 / 3) s hs')
  have hRt : DifferentiableAt ℂ (primeCubeRemainder P.catom) s :=
    (differentiableOn_primeCubeRemainder P.catom_pos P.catom_zero_le
      (fun a ha => P.summable_exp_catom ha)).differentiableAt (hopen (1 / 3) s hs')
  exact (((hC1.add (hC2.div_const 2)).add hRu).sub hRt).differentiableWithinAt

/-- **The continuation is holomorphic on `Re s > 1/3`, `s ≠ 1`.** -/
theorem differentiableOn_crContinuation :
    DifferentiableOn ℂ P.crContinuation {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} := by
  intro s hs
  have hdom : IsOpen {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have h1 := P.differentiableOn_cContinuation.differentiableAt (hdom.mem_nhds hs)
  have h2 := P.differentiableOn_roundingExponent.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs.1)
  exact (h1.mul h2.cexp).differentiableWithinAt

theorem crContinuation_eq_zero_iff (s : ℂ) :
    P.crContinuation s = 0 ↔ P.cContinuation s = 0 := by
  rw [crContinuation, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _)]

/-- The numerator `H` with `crContinuation = H/(s − 1)`. -/
def crPoleFactor (s : ℂ) : ℂ :=
  (((s - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2) * (s + (4 * P.μ - 1)) /
    ((s + (3 * P.μ - 1 - P.ν)) * (s + (3 * P.μ - 1 + P.ν)))) *
      cexp (-(P.logZeta (4 * s)) / 4 + s * boundedLaplace P.cerror s +
        s * boundedLaplace P.cerror (2 * s) + primeCubeRemainder P.catom s) *
      cexp (P.roundingExponent s)

theorem crContinuation_eq_poleFactor (s : ℂ) : P.crContinuation s = P.crPoleFactor s / (s - 1) := by
  rw [crContinuation, cContinuation, crPoleFactor,
    RHTower.BeurlingOverRegularIntegers.overRegularZeta]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem differentiableOn_crPoleFactor :
    DifferentiableOn ℂ P.crPoleFactor {s : ℂ | 1 / 3 < s.re} := by
  intro s hs
  have hs' : 1 / 3 < s.re := hs
  have hopen : ∀ c : ℝ, ∀ z : ℂ, c < z.re → {w : ℂ | c < w.re} ∈ 𝓝 z := fun c z hz =>
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hlow : s + (3 * P.μ - 1 - P.ν) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith only [P.hlow, hs', hr]
  have hhigh : s + (3 * P.μ - 1 + P.ν) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith only [P.hhigh, hs', hr]
  have hrat : DifferentiableAt ℂ (fun z : ℂ =>
      ((z - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2) * (z + (4 * P.μ - 1)) /
        ((z + (3 * P.μ - 1 - P.ν)) * (z + (3 * P.μ - 1 + P.ν)))) s :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (mul_ne_zero hlow hhigh)
  have hL : DifferentiableAt ℂ (fun s : ℂ => P.logZeta (4 * s)) s :=
    (P.differentiableOn_logZeta.differentiableAt (hopen 1 (4 * s) (by simp; linarith))).comp s
      (differentiableAt_id.const_mul 4)
  have hΛ := differentiableOn_boundedLaplace_of_le P.measurable_cerror P.cbound_pos P.abs_cerror_le
  have hΛ1 : DifferentiableAt ℂ (boundedLaplace P.cerror) s :=
    hΛ.differentiableAt (hopen 0 s (by linarith))
  have hΛ2 : DifferentiableAt ℂ (fun s : ℂ => boundedLaplace P.cerror (2 * s)) s :=
    (hΛ.differentiableAt (hopen 0 (2 * s) (by simp; linarith))).comp s
      (differentiableAt_id.const_mul 2)
  have hR : DifferentiableAt ℂ (primeCubeRemainder P.catom) s :=
    (differentiableOn_primeCubeRemainder P.catom_pos P.catom_zero_le
      (fun a ha => P.summable_exp_catom ha)).differentiableAt (hopen (1 / 3) s hs')
  have hE := P.differentiableOn_roundingExponent.differentiableAt (hopen (1 / 3) s hs')
  exact ((hrat.mul ((((hL.neg.div_const 4).add (differentiableAt_id.mul hΛ1)).add
    (differentiableAt_id.mul hΛ2)).add hR).cexp).mul hE.cexp).differentiableWithinAt

theorem crPoleFactor_one_ne_zero : P.crPoleFactor 1 ≠ 0 := by
  have hμ : 0 < P.μ := by linarith only [P.hμ1]
  have hlow : 0 < 3 * P.μ - P.ν := by linarith only [P.hν]
  have hhigh : 0 < 3 * P.μ + P.ν := by linarith only [hμ, P.hν0]
  have hnum : 0 < (P.μ ^ 2 + P.γ ^ 2) * (4 * P.μ) := by positivity
  have hden : 0 < (3 * P.μ - P.ν) * (3 * P.μ + P.ν) := mul_pos hlow hhigh
  have hrat : (((1 : ℂ) - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2) * (1 + (4 * P.μ - 1)) /
        ((1 + (3 * P.μ - 1 - P.ν)) * (1 + (3 * P.μ - 1 + P.ν))) =
      (((P.μ ^ 2 + P.γ ^ 2) * (4 * P.μ) / ((3 * P.μ - P.ν) * (3 * P.μ + P.ν)) : ℝ) : ℂ) := by
    push_cast
    congr 1 <;> ring
  rw [crPoleFactor, hrat]
  exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hnum hden).ne')
    (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)

end

end GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff.Params

namespace GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

noncomputable section

/-- **An integer-norm one-off with linear counting across the critical line.** For every height
`γ` there are natural generators `q_k ≥ 2` and natural coefficients `a_n` with
`Π_k (1 − q_k^{-s})^{-1} = Σ_n a_n n^{-s} = F(s)` on `Re s > 1`, `Σ_{n<N} a_n ∼ A N` with `A > 0`,
`F` holomorphic on `Re s > 1/3`, `s ≠ 1`, with zeros there exactly `3/5 ± iγ`, and `F ≠ 0` on the
critical line. -/
theorem exists_integer_norm_linear_count_one_off_across (γ : ℝ) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} ∧
      ∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0 := by
  let P := fixedParams γ
  have hq := Params.cPrimeNorm_ge_two P
  have hmono : ∀ k, Real.log (Params.cPrimeNorm P 0) ≤ Real.log (Params.cPrimeNorm P k) :=
    Params.cRounded_zero_le P
  have hsum : ∀ a : ℝ, 1 < a →
      Summable fun k => Real.exp (-(a * Real.log (Params.cPrimeNorm P k))) :=
    fun a ha => Params.summable_exp_cRounded P ha
  obtain ⟨A, hA, -, hcount⟩ := tendsto_genCoeff_count hq hmono hsum (H := Params.crPoleFactor P)
    (σ₁ := 1 / 3) (by norm_num) (Params.differentiableOn_crPoleFactor P)
    (Params.crPoleFactor_one_ne_zero P) fun s hs => by
      rw [Params.genEulerLog_eq_crContinuation P hs, Params.crContinuation_eq_poleFactor]
  refine ⟨Params.cPrimeNorm P, genCoeff (Params.cPrimeNorm P), hq, Params.crContinuation P, A, hA,
    fun s hs => ⟨Params.hasProd_crContinuation P hs, ?_⟩, hcount,
    Params.differentiableOn_crContinuation P, ?_, ?_⟩
  · rw [← Params.genEulerLog_eq_crContinuation P hs]
    exact hasSum_genCoeff hq hmono hsum hs
  · have hz := DiscreteOneOff.Params.cZeros_right_eq_pair P
    simp only [Params.crContinuation_eq_zero_iff]
    rw [hz]
    norm_num [P, fixedParams]
  · intro s hs
    rw [Ne, Params.crContinuation_eq_zero_iff]
    exact (DiscreteOneOff.Params.cContinuation_critical_line P hs).2

end

end GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff
