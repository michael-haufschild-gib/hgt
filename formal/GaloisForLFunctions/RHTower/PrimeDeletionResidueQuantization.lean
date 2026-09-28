import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
import GaloisForLFunctions.RHTower.FractionalPartZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Linearity
import GaloisForLFunctions.HTGeometry.HalfPlaneMellinAnalytic

/-!
# Residue quantization for integers free of a set of primes

Let `Q` be a set of natural numbers and let `S` be the set of positive integers with no prime
factor in `Q`.  Write `N_Q(x) = #(S ∩ [1, x])` and `ψ_Q(x) = ∑_{n ≤ x, n = q^k, q ∈ Q} log q` for
the Chebyshev function of the deleted primes.

**Theorem.**  Suppose `N_Q(x) = a x + O(x^θ)` with `θ ≥ 0` and
`ψ_Q(x) = ∑_{ρ ∈ J} c_ρ x^ρ + O(x^η)` for a finite set `J` of real exponents.  Then every
exponent `ρ ∈ J` with `max θ η < ρ < 1` carries a quantized coefficient: `ρ c_ρ ∈ ℕ`.

*Proof.*  On `Re s > 1`, `F = L(1_S)/ζ` has logarithmic derivative `F'/F = L(Λ_Q)`.  The integer
count continues `F` analytically to `Re s > θ` away from the zeros of `ζ`.  The Chebyshev
expansion continues `L(Λ_Q)` meromorphically to `Re s > η`, with residue `ρ c_ρ` at `ρ`.  Along a
thin tube around the real axis, where `ζ` does not vanish, the identity `F' = F · L(Λ_Q)`
persists.  At `ρ` the residue of `F'/F` is the order of vanishing of `F`, a natural number.

For the deletion of a set of primes with counting function `λ ∫^x t^{κ-1} dt / log t + O(x^η)`
the expansion is `ψ_Q(x) = (λ/κ) x^κ + (λ/κ) x^{κ/2} + ...`, whose coefficient at `κ/2` gives
`λ/2 ∈ ℕ`.  So for odd `λ` the integer count of `ℙ ∖ Q` cannot have a power saving below
`x^{κ/2}`, although its primes deviate from `ℙ` by `x^κ`.
-/

open Filter Topology Complex Asymptotics MeasureTheory Set ArithmeticFunction LSeries
open scoped LSeries.notation

namespace RHTower

noncomputable section

namespace PrimeDeletion

variable (Q : Set ℕ)

open scoped Classical in
/-- Indicator of the positive integers with no prime factor in `Q`. -/
def qFreeIndicator (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∉ Q then 1 else 0

/-- The indicator as a complex sequence. -/
def qFreeSeq (n : ℕ) : ℂ := (qFreeIndicator Q n : ℂ)

/-- The number of positive `Q`-free integers up to `x`. -/
def qFreeCount (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, qFreeIndicator Q k

/-- The von Mangoldt function restricted to powers of primes in `Q`. -/
def deletedVonMangoldt (n : ℕ) : ℝ := Λ n * (1 - qFreeIndicator Q n)

/-- The Chebyshev function of the deleted primes. -/
def deletedChebyshev (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, deletedVonMangoldt Q k

theorem qFreeIndicator_nonneg (n : ℕ) : 0 ≤ qFreeIndicator Q n := by
  unfold qFreeIndicator
  split_ifs <;> norm_num

theorem qFreeIndicator_le_one (n : ℕ) : qFreeIndicator Q n ≤ 1 := by
  unfold qFreeIndicator
  split_ifs <;> norm_num

theorem qFreeIndicator_one : qFreeIndicator Q 1 = 1 := by
  simp [qFreeIndicator]

/-- The indicator is completely multiplicative. -/
theorem qFreeIndicator_mul (m n : ℕ) :
    qFreeIndicator Q (m * n) = qFreeIndicator Q m * qFreeIndicator Q n := by
  classical
  rcases eq_or_ne m 0 with rfl | hm
  · simp [qFreeIndicator]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [qFreeIndicator]
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  have hiff : (∀ p ∈ (m * n).primeFactors, p ∉ Q) ↔
      (∀ p ∈ m.primeFactors, p ∉ Q) ∧ (∀ p ∈ n.primeFactors, p ∉ Q) := by
    rw [Nat.primeFactors_mul hm hn]
    simp only [Finset.mem_union]
    constructor
    · intro h
      exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨h1, h2⟩ p (hp | hp)
      · exact h1 p hp
      · exact h2 p hp
  unfold qFreeIndicator
  by_cases h1 : ∀ p ∈ m.primeFactors, p ∉ Q
  · by_cases h2 : ∀ p ∈ n.primeFactors, p ∉ Q
    · rw [if_pos ⟨hmn, hiff.mpr ⟨h1, h2⟩⟩, if_pos ⟨hm, h1⟩, if_pos ⟨hn, h2⟩, mul_one]
    · rw [if_neg (fun h => h2 (hiff.mp h.2).2), if_pos ⟨hm, h1⟩, if_neg (fun h => h2 h.2),
        mul_zero]
  · rw [if_neg (fun h => h1 (hiff.mp h.2).1), if_neg (fun h => h1 h.2), zero_mul]

theorem deletedVonMangoldt_nonneg (n : ℕ) : 0 ≤ deletedVonMangoldt Q n :=
  mul_nonneg vonMangoldt_nonneg (by linarith [qFreeIndicator_le_one Q n])

theorem deletedVonMangoldt_le (n : ℕ) : deletedVonMangoldt Q n ≤ n := by
  have h1 : deletedVonMangoldt Q n ≤ Λ n := by
    have := qFreeIndicator_nonneg Q n
    unfold deletedVonMangoldt
    nlinarith [vonMangoldt_nonneg (n := n)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [deletedVonMangoldt]
  have hlog : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)
    linarith
  exact h1.trans (vonMangoldt_le_log.trans hlog)

/-! ### The logarithmic derivative on `Re s > 2` -/

/-- `(1_S Λ) ⋆ 1_S = log · 1_S`, from complete multiplicativity and `Λ ⋆ 1 = log`. -/
theorem convolution_twist_vonMangoldt :
    (fun n => qFreeSeq Q n * (Λ n : ℂ)) ⍟ qFreeSeq Q = logMul (qFreeSeq Q) := by
  ext n
  rw [LSeries.convolution_def]
  dsimp only
  have hterm : ∀ p ∈ n.divisorsAntidiagonal,
      qFreeSeq Q p.1 * (Λ p.1 : ℂ) * qFreeSeq Q p.2 = qFreeSeq Q n * (Λ p.1 : ℂ) := by
    intro p hp
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1]
    simp only [qFreeSeq, qFreeIndicator_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [qFreeSeq, qFreeIndicator]
  have hsum : ∑ p ∈ n.divisorsAntidiagonal, (Λ p.1 : ℂ) = Complex.log n := by
    rw [Nat.sum_divisorsAntidiagonal (fun a _ => (Λ a : ℂ)), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg n)]
    exact_mod_cast vonMangoldt_sum
  rw [hsum, logMul, mul_comm]

theorem qFreeSeq_isBigO : qFreeSeq Q =O[atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  rw [Real.rpow_zero, norm_one, one_mul, qFreeSeq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (qFreeIndicator_nonneg Q n)]
  exact qFreeIndicator_le_one Q n

theorem abscissa_qFreeSeq_le : abscissaOfAbsConv (qFreeSeq Q) ≤ 1 := by
  have := LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (qFreeSeq_isBigO Q)
  simpa using this

theorem summable_qFreeSeq {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (qFreeSeq Q) s :=
  LSeriesSummable_of_isBigO_rpow (x := 1) hs (by simpa using qFreeSeq_isBigO Q)

theorem summable_twist_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => qFreeSeq Q n * (Λ n : ℂ)) s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeriesSummable, ← summable_norm_iff] at hΛ ⊢
  refine hΛ.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => LSeries.norm_term_le s ?_)
  rw [norm_mul, qFreeSeq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (qFreeIndicator_nonneg Q n)]
  exact mul_le_of_le_one_left (norm_nonneg _) (qFreeIndicator_le_one Q n)

/-- The negative logarithmic derivative of `L(1_S)` is `L(1_S Λ)`. -/
theorem deriv_LSeries_qFreeSeq {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries (qFreeSeq Q)) s =
      -(LSeries (fun n => qFreeSeq Q n * (Λ n : ℂ)) s * LSeries (qFreeSeq Q) s) := by
  have habs : abscissaOfAbsConv (qFreeSeq Q) < s.re :=
    (abscissa_qFreeSeq_le Q).trans_lt (by exact_mod_cast hs)
  rw [LSeries_deriv habs, ← convolution_twist_vonMangoldt,
    LSeries_convolution' (summable_twist_vonMangoldt Q hs) (summable_qFreeSeq Q hs)]

/-- `Λ − 1_S Λ` is the deleted von Mangoldt function. -/
theorem deletedVonMangoldt_eq_sub :
    (fun n => (deletedVonMangoldt Q n : ℂ)) =
      (fun n => (Λ n : ℂ)) - fun n => qFreeSeq Q n * (Λ n : ℂ) := by
  ext n
  simp only [deletedVonMangoldt, qFreeSeq, Pi.sub_apply]
  push_cast
  ring

/-- **Logarithmic derivative of `L(1_S)/ζ`.**  On `Re s > 1`,
`(L(1_S)/ζ)' = (L(1_S)/ζ) · L(Λ_Q)`. -/
theorem deriv_LSeries_div_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    deriv (fun z => LSeries (qFreeSeq Q) z / riemannZeta z) s =
      LSeries (qFreeSeq Q) s / riemannZeta s *
        LSeries (fun n => (deletedVonMangoldt Q n : ℂ)) s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have habs : abscissaOfAbsConv (qFreeSeq Q) < s.re :=
    (abscissa_qFreeSeq_le Q).trans_lt (by exact_mod_cast hs)
  have hdL : DifferentiableAt ℂ (LSeries (qFreeSeq Q)) s :=
    (LSeries_hasDerivAt habs).differentiableAt
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hζ' : deriv riemannZeta s =
      -(riemannZeta s * LSeries (fun n => (Λ n : ℂ)) s) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    field_simp
  have hquot := deriv_div hdL hdζ hζ
  simp only [Pi.div_def] at hquot
  rw [hquot, deriv_LSeries_qFreeSeq Q hs, hζ', deletedVonMangoldt_eq_sub Q,
    LSeries_sub (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
      (summable_twist_vonMangoldt Q hs)]
  field_simp
  ring

/-! ### Mellin integrals of partial sums -/

/-- A partial-sum step function is interval integrable. -/
theorem intervalIntegrable_floorSum (g : ℕ → ℂ) (y : ℝ) :
    IntervalIntegrable (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, g k) volume 1 y := by
  have hmeas : Measurable (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, g k) :=
    (measurable_from_nat (f := fun n => ∑ k ∈ Finset.Icc 1 n, g k)).comp Nat.measurable_floor
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := ∑ k ∈ Finset.Icc 1 ⌊max 1 y⌋₊, ‖g k‖) ?_
    hmeas.aestronglyMeasurable ?_
  · rw [Set.uIoc, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_
    have hty : t ≤ max 1 y := by
      rw [Set.uIoc] at ht
      exact ht.2
    calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, g k‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖g k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 ⌊max 1 y⌋₊, ‖g k‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hty)) (fun _ _ _ => norm_nonneg _)

/-- The Mellin integral `∫_1^∞ G(t) t^{-(s+1)} dt` of an `O(t^r)` function is complex
differentiable on `Re s > r`. -/
theorem differentiableAt_integral_cpow {G : ℝ → ℂ} {r : ℝ}
    (hint : ∀ y : ℝ, 1 ≤ y → IntervalIntegrable G volume 1 y)
    (hO : G =O[atTop] fun t : ℝ => t ^ r) {s : ℂ} (hs : r < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ t in Ioi (1:ℝ), G t * (t : ℂ) ^ (-(z + 1))) s := by
  have hev : G =ᶠ[atTop] Set.indicator (Set.Ioi (1:ℝ)) G := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    rw [Set.indicator_of_mem (show t ∈ Set.Ioi (1:ℝ) from ht)]
  have hmel : DifferentiableAt ℂ (mellin (Set.indicator (Set.Ioi (1:ℝ)) G)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -r) (b := -s.re - 1)
      (GaloisForLFunctions.HTGeometry.locallyIntegrableOn_indicator_of_intervalIntegrable hint)
      ?_ ?_ ?_ ?_
    · simpa only [neg_neg] using hO.congr' hev EventuallyEq.rfl
    · rw [Complex.neg_re]
      linarith
    · exact GaloisForLFunctions.HTGeometry.isBigO_zero_indicator G _
    · rw [Complex.neg_re]
      linarith
  have hfun : (fun z : ℂ => ∫ t in Ioi (1:ℝ), G t * (t : ℂ) ^ (-(z + 1))) =
      (mellin (Set.indicator (Set.Ioi (1:ℝ)) G)) ∘ (fun z : ℂ => 1 - (z + 1)) := by
    funext z
    rw [Function.comp_apply, ← GaloisForLFunctions.HTGeometry.halfPlaneMellin_eq_mellin]
    rfl
  rw [hfun]
  refine DifferentiableAt.comp s ?_
    ((differentiableAt_const _).sub (differentiableAt_id.add (differentiableAt_const _)))
  rw [show (1 : ℂ) - (s + 1) = -s by ring]
  exact hmel

/-- The Mellin integral of an `O(t^r)` function converges on `Re s > r`. -/
theorem integrableOn_mul_cpow {G : ℝ → ℂ} {r : ℝ}
    (hint : ∀ y : ℝ, 1 ≤ y → IntervalIntegrable G volume 1 y)
    (hO : G =O[atTop] fun t : ℝ => t ^ r) {s : ℂ} (hs : r < s.re) :
    IntegrableOn (fun t : ℝ => G t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hev : G =ᶠ[atTop] Set.indicator (Set.Ioi (1:ℝ)) G := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    rw [Set.indicator_of_mem (show t ∈ Set.Ioi (1:ℝ) from ht)]
  have hconv : MellinConvergent (Set.indicator (Set.Ioi (1:ℝ)) G) (-s) := by
    refine mellinConvergent_of_isBigO_rpow (a := -r) (b := -s.re - 1)
      (GaloisForLFunctions.HTGeometry.locallyIntegrableOn_indicator_of_intervalIntegrable hint)
      ?_ ?_ ?_ ?_
    · simpa only [neg_neg] using hO.congr' hev EventuallyEq.rfl
    · rw [Complex.neg_re]
      linarith
    · exact GaloisForLFunctions.HTGeometry.isBigO_zero_indicator G _
    · rw [Complex.neg_re]
      linarith
  rw [MellinConvergent] at hconv
  have hfun : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • Set.indicator (Set.Ioi (1:ℝ)) G t) =
      Set.indicator (Set.Ioi (1:ℝ)) (fun t : ℝ => G t * (t : ℂ) ^ (-(s + 1))) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1:ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
      ring_nf
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  rw [hfun, integrableOn_indicator_iff measurableSet_Ioi] at hconv
  refine hconv.mono_set fun t ht => ⟨ht, Set.mem_Ioi.2 (zero_lt_one.trans ht)⟩

/-! ### Continuation of `L(1_S) − a ζ` -/

/-- The sequence `1_S − a`. -/
def countDefectSeq (a : ℝ) (n : ℕ) : ℂ := qFreeSeq Q n - (a : ℂ)

theorem countDefectSeq_eq (a : ℝ) : countDefectSeq Q a = qFreeSeq Q - (a : ℂ) • 1 := by
  funext n
  simp [countDefectSeq]

theorem sum_countDefectSeq (a t : ℝ) :
    ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq Q a k = ((qFreeCount Q t - a * ⌊t⌋₊ : ℝ) : ℂ) := by
  simp only [countDefectSeq, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, qFreeCount, qFreeSeq]
  push_cast
  ring

theorem countDefect_isBigO {a θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ) :
    (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq Q a k) =O[atTop] fun t => t ^ θ := by
  have h1 : (fun t : ℝ => a * (t - ⌊t⌋₊)) =O[atTop] fun t : ℝ => t ^ θ := by
    refine IsBigO.of_bound |a| ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have h0 : 0 ≤ t - ⌊t⌋₊ := sub_nonneg.mpr (Nat.floor_le (by linarith))
    have h1' : t - ⌊t⌋₊ ≤ 1 := by
      have := Nat.lt_floor_add_one t
      linarith
    have hpow : 1 ≤ t ^ θ := Real.one_le_rpow ht hθ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) θ)]
    exact mul_le_mul_of_nonneg_left (h1'.trans hpow) (abs_nonneg a)
  have h2 := hN.add h1
  refine IsBigO.of_norm_left ?_
  refine h2.norm_left.congr_left fun t => ?_
  rw [sum_countDefectSeq, Complex.norm_real]
  congr 1
  ring

/-- The Mellin integral continuing `L(1_S) − a ζ` to `Re s > θ`. -/
def countDefectIntegral (a : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq Q a k) * (t : ℂ) ^ (-(z + 1))

theorem differentiableAt_countDefectIntegral {a θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ) {s : ℂ}
    (hs : θ < s.re) : DifferentiableAt ℂ (countDefectIntegral Q a) s :=
  differentiableAt_integral_cpow (fun y _ => intervalIntegrable_floorSum _ y)
    (countDefect_isBigO Q hθ hN) hs

theorem LSeries_qFreeSeq_sub {a θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ) {s : ℂ}
    (hs : 1 < s.re) (hθs : θ < s.re) :
    LSeries (qFreeSeq Q) s - a * riemannZeta s = s * countDefectIntegral Q a s := by
  have hseq : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, countDefectSeq Q a k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ θ := by
    have := (countDefect_isBigO Q hθ hN).comp_tendsto tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, Nat.floor_natCast] using this
  have hone : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hsum : LSeriesSummable (countDefectSeq Q a) s := by
    rw [countDefectSeq_eq]
    exact (summable_qFreeSeq Q hs).sub (hone.smul _)
  rw [countDefectIntegral, ← LSeries_eq_mul_integral _ hθ hθs hsum hseq, countDefectSeq_eq,
    LSeries_sub (summable_qFreeSeq Q hs) (hone.smul _), LSeries_smul,
    LSeries_one_eq_riemannZeta hs]

/-! ### Continuation of `L(Λ_Q)` -/

/-- The deleted von Mangoldt function as a complex sequence. -/
def deletedSeq (n : ℕ) : ℂ := (deletedVonMangoldt Q n : ℂ)

/-- The remainder of the Chebyshev expansion. -/
def chebyshevRemainder (J : Finset ℝ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  deletedChebyshev Q t - ∑ ρ ∈ J, c ρ * t ^ ρ

/-- The Mellin integral of the remainder. -/
def remainderIntegral (J : Finset ℝ) (c : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (1:ℝ), (chebyshevRemainder Q J c t : ℂ) * (t : ℂ) ^ (-(z + 1))

theorem intervalIntegrable_remainder (J : Finset ℝ) (c : ℝ → ℝ) (y : ℝ) (hy : 1 ≤ y) :
    IntervalIntegrable (fun t : ℝ => (chebyshevRemainder Q J c t : ℂ)) volume 1 y := by
  have hstep := intervalIntegrable_floorSum (deletedSeq Q) y
  have hcont : ContinuousOn (fun t : ℝ => ((∑ ρ ∈ J, c ρ * t ^ ρ : ℝ) : ℂ)) (Set.uIcc 1 y) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine continuousOn_finsetSum _ fun ρ _ => continuousOn_const.mul ?_
    refine continuousOn_id.rpow_const fun t ht => Or.inl ?_
    rw [Set.uIcc_of_le hy] at ht
    exact (zero_lt_one.trans_le ht.1).ne'
  refine (hstep.sub hcont.intervalIntegrable).congr fun t _ => ?_
  simp only [chebyshevRemainder, deletedChebyshev, deletedSeq]
  push_cast
  rfl

theorem differentiableAt_remainderIntegral {J : Finset ℝ} {c : ℝ → ℝ} {η : ℝ}
    (hψ : (fun x : ℝ => deletedChebyshev Q x - ∑ ρ ∈ J, c ρ * x ^ ρ) =O[atTop] fun x => x ^ η)
    {s : ℂ} (hs : η < s.re) : DifferentiableAt ℂ (remainderIntegral Q J c) s := by
  refine differentiableAt_integral_cpow (intervalIntegrable_remainder Q J c) ?_ hs
  refine IsBigO.of_norm_left ?_
  refine hψ.norm_left.congr_left fun t => ?_
  rw [Complex.norm_real]
  rfl

theorem deletedSeq_isBigO : deletedSeq Q =O[atTop] fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul, deletedSeq, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (deletedVonMangoldt_nonneg Q n),
    abs_of_nonneg (Nat.cast_nonneg n)]
  exact deletedVonMangoldt_le Q n

theorem sum_deletedSeq_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, deletedSeq Q k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have hle : ∀ k ∈ Finset.Icc 1 n, ‖deletedSeq Q k‖ ≤ n := by
    intro k hk
    rw [deletedSeq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (deletedVonMangoldt_nonneg Q k)]
    exact (deletedVonMangoldt_le Q k).trans (by exact_mod_cast (Finset.mem_Icc.mp hk).2)
  calc ‖∑ k ∈ Finset.Icc 1 n, deletedSeq Q k‖ ≤ ∑ k ∈ Finset.Icc 1 n, ‖deletedSeq Q k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, (n : ℝ) := Finset.sum_le_sum hle
    _ = 1 * ‖(n : ℝ) ^ (2 : ℝ)‖ := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, one_mul,
          Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_two, sq]

/-- `∫_1^∞ t^ρ t^{-(s+1)} dt = 1/(s-ρ)` for `Re s > ρ`. -/
theorem integral_rpow_mul_cpow {ρ : ℝ} {s : ℂ} (hs : ρ < s.re) :
    ∫ t in Ioi (1:ℝ), (t : ℂ) ^ (ρ : ℂ) * (t : ℂ) ^ (-(s + 1)) = 1 / (s - ρ) := by
  have hre : ((ρ : ℂ) + -(s + 1)).re < -1 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => (t : ℂ) ^ ((ρ : ℂ) + -(s + 1)))
    fun t ht => (Complex.cpow_add _ _ (by exact_mod_cast (zero_lt_one.trans ht).ne')).symm,
    integral_Ioi_cpow_of_lt hre zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
  have hne : (ρ : ℂ) + -(s + 1) + 1 ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re,
      Complex.zero_re] at this
    linarith
  have hne' : s - ρ ≠ 0 := by
    intro h
    apply hne
    linear_combination -h
  field_simp
  ring

theorem integrableOn_rpow_mul_cpow {ρ : ℝ} {s : ℂ} (hs : ρ < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (ρ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hre : ((ρ : ℂ) + -(s + 1)).re < -1 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re]
    linarith
  refine (integrableOn_Ioi_cpow_of_lt hre zero_lt_one).congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact Complex.cpow_add _ _ (by exact_mod_cast (zero_lt_one.trans ht).ne')

/-- **Continuation of `L(Λ_Q)`.**  For `Re s` beyond every exponent,
`L(Λ_Q)(s) = s (∑_ρ c_ρ/(s-ρ) + ∫_1^∞ R(t) t^{-(s+1)} dt)`. -/
theorem LSeries_deletedSeq_eq {J : Finset ℝ} {c : ℝ → ℝ} {η : ℝ}
    (hψ : (fun x : ℝ => deletedChebyshev Q x - ∑ ρ ∈ J, c ρ * x ^ ρ) =O[atTop] fun x => x ^ η)
    {s : ℂ} (hs : 2 < s.re) (hηs : η < s.re) (hJ : ∀ ρ ∈ J, ρ < s.re) :
    LSeries (deletedSeq Q) s =
      s * (∑ ρ ∈ J, (c ρ : ℂ) / (s - ρ) + remainderIntegral Q J c s) := by
  have hsum : LSeriesSummable (deletedSeq Q) s :=
    LSeriesSummable_of_isBigO_rpow (x := 2) hs (deletedSeq_isBigO Q)
  rw [LSeries_eq_mul_integral _ (by norm_num : (0:ℝ) ≤ 2) hs hsum (sum_deletedSeq_isBigO Q)]
  congr 1
  have hR : IntegrableOn (fun t : ℝ => (chebyshevRemainder Q J c t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
    refine integrableOn_mul_cpow (intervalIntegrable_remainder Q J c) ?_ hηs
    refine IsBigO.of_norm_left ?_
    refine hψ.norm_left.congr_left fun t => ?_
    rw [Complex.norm_real]
    rfl
  have hsplit : ∀ t ∈ Ioi (1:ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, deletedSeq Q k) * (t : ℂ) ^ (-(s + 1)) =
        (chebyshevRemainder Q J c t : ℂ) * (t : ℂ) ^ (-(s + 1)) +
          ∑ ρ ∈ J, (c ρ : ℂ) * ((t : ℂ) ^ (ρ : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := (zero_lt_one.trans ht).le
    have hcast : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, deletedSeq Q k =
        (chebyshevRemainder Q J c t : ℂ) + ∑ ρ ∈ J, (c ρ : ℂ) * (t : ℂ) ^ (ρ : ℂ) := by
      have hJsum : ∑ ρ ∈ J, (c ρ : ℂ) * (t : ℂ) ^ (ρ : ℂ) =
          ((∑ ρ ∈ J, c ρ * t ^ ρ : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Complex.ofReal_cpow ht0]
      rw [hJsum]
      simp only [chebyshevRemainder, deletedChebyshev, deletedSeq]
      push_cast
      ring
    rw [hcast, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add hR, integral_finsetSum]
  · rw [add_comm, remainderIntegral]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [integral_const_mul, integral_rpow_mul_cpow (hJ ρ hρ), mul_one_div]
  · intro ρ hρ
    exact (integrableOn_rpow_mul_cpow (hJ ρ hρ)).const_mul _
  · refine integrable_finset_sum _ fun ρ hρ => ?_
    exact (integrableOn_rpow_mul_cpow (hJ ρ hρ)).const_mul _

end PrimeDeletion

end

end RHTower
