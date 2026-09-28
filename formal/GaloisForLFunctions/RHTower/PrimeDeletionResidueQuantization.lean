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
`ψ_Q(x) = ∑_{ρ ∈ J} c_ρ x^ρ + O(x^η)` for a finite set `J` of complex exponents.  Then every
`ρ ∈ J` with `Re ρ > max θ η` at which `(s-1)ζ(s)` does not vanish carries a quantized
coefficient: `ρ c_ρ ∈ ℕ`.  For real `ρ ∈ (max θ η, 1)` the nonvanishing is automatic.

*Proof.*  On `Re s > 1`, `F = L(1_S)/ζ` has logarithmic derivative `F'/F = L(Λ_Q)`.  The integer
count continues the numerator `(s-1)L(1_S)` analytically to `Re s > θ`, and `(s-1)ζ(s)` is entire.
The Chebyshev expansion continues `L(Λ_Q)` meromorphically to `Re s > η`, with residue `ρ c_ρ` at
`ρ`.  After clearing all denominators the identity `F' = F · L(Λ_Q)` is an identity between
functions analytic on the convex half-plane `Re s > max θ η`, so it persists there.  At `ρ` the
residue of `F'/F` is the order of vanishing of `F`, a natural number.

For the deletion of a set of primes with counting function `λ ∫^x t^{κ-1} dt / log t + O(x^η)`
the expansion is `ψ_Q(x) = (λ/κ) x^κ + (λ/κ) x^{κ/2} + ...`, whose coefficient at `κ/2` gives
`λ/2 ∈ ℕ`.  So for odd `λ` the integer count of `ℙ ∖ Q` cannot have a power saving below
`x^{κ/2}`, although its primes deviate from `ℙ` by `x^κ`.  The same holds for deletions that
imitate a zero of odd multiplicity at a complex `ρ`, provided `ζ(ρ/2) ≠ 0`.
-/

open Filter Topology Complex Asymptotics MeasureTheory Set ArithmeticFunction LSeries
open scoped LSeries.notation ComplexOrder

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

/-- The remainder of a (complex) power expansion of the deleted Chebyshev function. -/
def chebyshevRemainder (J : Finset ℂ) (c : ℂ → ℂ) (t : ℝ) : ℂ :=
  (deletedChebyshev Q t : ℂ) - ∑ ρ ∈ J, c ρ * (t : ℂ) ^ ρ

/-- The Mellin integral of the remainder. -/
def remainderIntegral (J : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (1:ℝ), chebyshevRemainder Q J c t * (t : ℂ) ^ (-(z + 1))

theorem intervalIntegrable_remainder (J : Finset ℂ) (c : ℂ → ℂ) (y : ℝ) (hy : 1 ≤ y) :
    IntervalIntegrable (chebyshevRemainder Q J c) volume 1 y := by
  have hstep := intervalIntegrable_floorSum (deletedSeq Q) y
  have hcont : ContinuousOn (fun t : ℝ => ∑ ρ ∈ J, c ρ * (t : ℂ) ^ ρ) (Set.uIcc 1 y) := by
    refine continuousOn_finsetSum _ fun ρ _ => continuousOn_const.mul ?_
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    exact ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.mpr (zero_lt_one.trans_le ht.1))).continuousWithinAt
  refine (hstep.sub hcont.intervalIntegrable).congr fun t _ => ?_
  simp only [chebyshevRemainder, deletedChebyshev, deletedSeq]
  push_cast
  rfl

theorem differentiableAt_remainderIntegral {J : Finset ℂ} {c : ℂ → ℂ} {η : ℝ}
    (hψ : (fun x : ℝ => (deletedChebyshev Q x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    {s : ℂ} (hs : η < s.re) : DifferentiableAt ℂ (remainderIntegral Q J c) s :=
  differentiableAt_integral_cpow (intervalIntegrable_remainder Q J c) hψ hs

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

/-- `∫_1^∞ t^ρ t^{-(s+1)} dt = 1/(s-ρ)` for `Re s > Re ρ`. -/
theorem integral_cpow_mul_cpow {ρ s : ℂ} (hs : ρ.re < s.re) :
    ∫ t in Ioi (1:ℝ), (t : ℂ) ^ ρ * (t : ℂ) ^ (-(s + 1)) = 1 / (s - ρ) := by
  have hre : (ρ + -(s + 1)).re < -1 := by
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => (t : ℂ) ^ (ρ + -(s + 1)))
    fun t ht => (Complex.cpow_add _ _ (by exact_mod_cast (zero_lt_one.trans ht).ne')).symm,
    integral_Ioi_cpow_of_lt hre zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
  have hne : ρ + -(s + 1) + 1 ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hne' : s - ρ ≠ 0 := by
    intro h
    apply hne
    linear_combination -h
  field_simp
  ring

theorem integrableOn_cpow_mul_cpow {ρ s : ℂ} (hs : ρ.re < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ ρ * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hre : (ρ + -(s + 1)).re < -1 := by
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re]
    linarith
  refine (integrableOn_Ioi_cpow_of_lt hre zero_lt_one).congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact Complex.cpow_add _ _ (by exact_mod_cast (zero_lt_one.trans ht).ne')

/-- **Continuation of `L(Λ_Q)`.**  For `Re s` beyond every exponent,
`L(Λ_Q)(s) = s (∑_ρ c_ρ/(s-ρ) + ∫_1^∞ R(t) t^{-(s+1)} dt)`. -/
theorem LSeries_deletedSeq_eq {J : Finset ℂ} {c : ℂ → ℂ} {η : ℝ}
    (hψ : (fun x : ℝ => (deletedChebyshev Q x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    {s : ℂ} (hs : 2 < s.re) (hηs : η < s.re) (hJ : ∀ ρ ∈ J, ρ.re < s.re) :
    LSeries (deletedSeq Q) s =
      s * (∑ ρ ∈ J, c ρ / (s - ρ) + remainderIntegral Q J c s) := by
  have hsum : LSeriesSummable (deletedSeq Q) s :=
    LSeriesSummable_of_isBigO_rpow (x := 2) hs (deletedSeq_isBigO Q)
  rw [LSeries_eq_mul_integral _ (by norm_num : (0:ℝ) ≤ 2) hs hsum (sum_deletedSeq_isBigO Q)]
  congr 1
  have hR : IntegrableOn (fun t : ℝ => chebyshevRemainder Q J c t * (t : ℂ) ^ (-(s + 1)))
      (Ioi 1) :=
    integrableOn_mul_cpow (intervalIntegrable_remainder Q J c) hψ hηs
  have hsplit : ∀ t ∈ Ioi (1:ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, deletedSeq Q k) * (t : ℂ) ^ (-(s + 1)) =
        chebyshevRemainder Q J c t * (t : ℂ) ^ (-(s + 1)) +
          ∑ ρ ∈ J, c ρ * ((t : ℂ) ^ ρ * (t : ℂ) ^ (-(s + 1))) := by
    intro t _
    have hcast : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, deletedSeq Q k =
        chebyshevRemainder Q J c t + ∑ ρ ∈ J, c ρ * (t : ℂ) ^ ρ := by
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
    rw [integral_const_mul, integral_cpow_mul_cpow (hJ ρ hρ), mul_one_div]
  · intro ρ hρ
    exact (integrableOn_cpow_mul_cpow (hJ ρ hρ)).const_mul _
  · refine integrable_finsetSum _ fun ρ hρ => ?_
    exact (integrableOn_cpow_mul_cpow (hJ ρ hρ)).const_mul _

/-! ### The quantization theorem -/

/-- `∏_{ρ ∈ J} (z − ρ)`. -/
def exponentPoly (J : Finset ℂ) (z : ℂ) : ℂ := ∏ ρ ∈ J, (z - ρ)

/-- `∏_{ρ ∈ J} (z − ρ)` times the continuation of `L(Λ_Q)`, written without denominators. -/
def clearedLogDeriv (J : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ :=
  (∑ ρ ∈ J, z * c ρ * ∏ ρ' ∈ J.erase ρ, (z - ρ')) +
    exponentPoly J z * z * remainderIntegral Q J c z

/-- `(s-1) L(1_S)(s)`, continued to `Re s > θ`. -/
def deletionNumerator (a : ℝ) (z : ℂ) : ℂ :=
  a * zetaResidueFactor z + (z - 1) * z * countDefectIntegral Q a z

/-- `L(1_S)/ζ`, continued through the entire function `(s-1)ζ(s)`. -/
def deletionQuotient (a : ℝ) (z : ℂ) : ℂ := deletionNumerator Q a z / zetaResidueFactor z

theorem deletionNumerator_eq {a θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ) {z : ℂ}
    (hz : 1 < z.re) (hθz : θ < z.re) :
    deletionNumerator Q a z = (z - 1) * LSeries (qFreeSeq Q) z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hz
    exact lt_irrefl _ hz
  have h := LSeries_qFreeSeq_sub Q hθ hN hz hθz
  rw [deletionNumerator, zetaResidueFactor_of_ne hz1,
    show (z - 1) * z * countDefectIntegral Q a z = (z - 1) * (z * countDefectIntegral Q a z) by
      ring, ← h]
  ring

theorem deletionQuotient_eq {a θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ) {z : ℂ}
    (hz : 1 < z.re) (hθz : θ < z.re) :
    deletionQuotient Q a z = LSeries (qFreeSeq Q) z / riemannZeta z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hz
    exact lt_irrefl _ hz
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz.le
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [deletionQuotient, deletionNumerator_eq Q hθ hN hz hθz, zetaResidueFactor_of_ne hz1]
  field_simp

theorem exponentPoly_mul_eq {J : Finset ℂ} {c : ℂ → ℂ} {z : ℂ} (hz : ∀ ρ ∈ J, z ≠ ρ) (R : ℂ) :
    exponentPoly J z * (z * (∑ ρ ∈ J, c ρ / (z - ρ) + R)) =
      (∑ ρ ∈ J, z * c ρ * ∏ ρ' ∈ J.erase ρ, (z - ρ')) + exponentPoly J z * z * R := by
  classical
  have hterm : ∀ ρ ∈ J, exponentPoly J z * (z * (c ρ / (z - ρ))) =
      z * c ρ * ∏ ρ' ∈ J.erase ρ, (z - ρ') := by
    intro ρ hρ
    have hne : z - ρ ≠ 0 := sub_ne_zero.mpr (hz ρ hρ)
    rw [exponentPoly, ← Finset.mul_prod_erase J (fun ρ' : ℂ => z - ρ') hρ]
    field_simp
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_congr rfl hterm]
  ring

/-- The identity `F' · P = F · (P · L(Λ_Q))` far to the right. -/
theorem deriv_deletionQuotient_mul {a θ η : ℝ} (hθ : 0 ≤ θ) {J : Finset ℂ} {c : ℂ → ℂ}
    (hN : (fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ)
    (hψ : (fun x : ℝ => (deletedChebyshev Q x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    {z : ℂ} (hz : 2 + θ + |η| + ∑ ρ ∈ J, ‖ρ‖ < z.re) :
    deriv (deletionQuotient Q a) z * exponentPoly J z =
      deletionQuotient Q a z * clearedLogDeriv Q J c z := by
  have hsumabs : 0 ≤ ∑ ρ ∈ J, ‖ρ‖ := Finset.sum_nonneg fun ρ _ => norm_nonneg ρ
  have hJ : ∀ ρ ∈ J, ρ.re < z.re := by
    intro ρ hρ
    have := Finset.single_le_sum (fun ρ _ => norm_nonneg ρ) hρ
    linarith [Complex.re_le_norm ρ, abs_nonneg η]
  have hz2 : 2 < z.re := by linarith [abs_nonneg η]
  have hθz : θ < z.re := by linarith [abs_nonneg η]
  have hηz : η < z.re := by linarith [le_abs_self η]
  have hopen : IsOpen {w : ℂ | 2 + θ + |η| + ∑ ρ ∈ J, ‖ρ‖ < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : deletionQuotient Q a =ᶠ[𝓝 z] fun w => LSeries (qFreeSeq Q) w / riemannZeta w := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact deletionQuotient_eq Q hθ hN (by linarith [abs_nonneg η])
      (by linarith [abs_nonneg η])
  rw [hev.deriv_eq, deriv_LSeries_div_riemannZeta Q (by linarith),
    deletionQuotient_eq Q hθ hN (by linarith) hθz]
  have hL : LSeries (fun n => (deletedVonMangoldt Q n : ℂ)) z =
      z * (∑ ρ ∈ J, c ρ / (z - ρ) + remainderIntegral Q J c z) :=
    LSeries_deletedSeq_eq Q hψ hz2 hηz hJ
  rw [hL, clearedLogDeriv, ← exponentPoly_mul_eq (c := c) (fun ρ hρ h => by
    have := congr_arg Complex.re h
    linarith [hJ ρ hρ])]
  ring

/-- **Residue quantization.**  If the `Q`-free integers have counting function
`a x + O(x^θ)` (`θ ≥ 0`) and the deleted Chebyshev function has the complex power expansion
`∑_{ρ ∈ J} c_ρ x^ρ + O(x^η)`, then `ρ₀ c_{ρ₀}` is a natural number for every `ρ₀ ∈ J` with
`Re ρ₀ > max θ η` at which `(s-1)ζ(s)` does not vanish. -/
theorem residue_quantization_complex {a θ η : ℝ} (hθ : 0 ≤ θ) {J : Finset ℂ} {c : ℂ → ℂ}
    (hN : (fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ)
    (hψ : (fun x : ℝ => (deletedChebyshev Q x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ J) (hθρ : θ < ρ₀.re) (hηρ : η < ρ₀.re)
    (hZρ : zetaResidueFactor ρ₀ ≠ 0) :
    ∃ m : ℕ, ρ₀ * c ρ₀ = m := by
  classical
  set Z := zetaResidueFactor with hZdef
  set Num := deletionNumerator Q a with hNumdef
  set F := deletionQuotient Q a with hFdef
  set P := exponentPoly J with hPdef
  set PM := clearedLogDeriv Q J c with hPMdef
  -- the half-plane `H`
  set H : Set ℂ := {w | max θ η < w.re} with hHdef
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHconv : Convex ℝ H := convex_halfSpace_re_gt _
  have hHθ : ∀ w ∈ H, θ < w.re := fun w hw => (le_max_left θ η).trans_lt hw
  have hHη : ∀ w ∈ H, η < w.re := fun w hw => (le_max_right θ η).trans_lt hw
  have hρ₀H : ρ₀ ∈ H := max_lt hθρ hηρ
  -- analyticity
  have hZdiff : Differentiable ℂ Z := differentiable_zetaResidueFactor
  have hNumdiff : DifferentiableOn ℂ Num H := by
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    have hC := differentiableAt_countDefectIntegral Q hθ hN (hHθ w hw)
    have hZw : DifferentiableAt ℂ zetaResidueFactor w := differentiable_zetaResidueFactor w
    rw [hNumdef]
    unfold deletionNumerator
    fun_prop
  have hNuman : AnalyticOnNhd ℂ Num H := hNumdiff.analyticOnNhd hHopen
  have hZan : AnalyticOnNhd ℂ Z H := hZdiff.differentiableOn.analyticOnNhd hHopen
  have hPdiff : Differentiable ℂ P := by
    rw [hPdef]
    unfold exponentPoly
    fun_prop
  have hPan : AnalyticOnNhd ℂ P H := hPdiff.differentiableOn.analyticOnNhd hHopen
  have hPMdiff : DifferentiableOn ℂ PM H := by
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    have hR := differentiableAt_remainderIntegral Q hψ (hHη w hw)
    have hPw := hPdiff w
    rw [hPMdef]
    unfold clearedLogDeriv
    rw [← hPdef]
    fun_prop
  have hPMan : AnalyticOnNhd ℂ PM H := hPMdiff.analyticOnNhd hHopen
  -- `F = Num / Z` and its derivative wherever `Z ≠ 0`
  have hFeq : ∀ w, F w = Num w / Z w := fun w => rfl
  have hderivF : ∀ w ∈ H, Z w ≠ 0 →
      deriv F w = (deriv Num w * Z w - Num w * deriv Z w) / Z w ^ 2 := by
    intro w hw hZw
    have := deriv_div ((hNuman w hw).differentiableAt) (hZdiff w) hZw
    simp only [Pi.div_def] at this
    have hF' : F = fun i => Num i / Z i := rfl
    rw [hF']
    exact this
  -- the cleared identity on `H`
  set R₀ : ℝ := 2 + θ + |η| + ∑ ρ ∈ J, ‖ρ‖ with hR₀
  have hsumabs : 0 ≤ ∑ ρ ∈ J, ‖ρ‖ := Finset.sum_nonneg fun ρ _ => norm_nonneg ρ
  set z₀ : ℂ := ((R₀ + 1 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = R₀ + 1 := Complex.ofReal_re _
  have hz₀H : z₀ ∈ H := by
    show max θ η < z₀.re
    rw [hz₀re, hR₀]
    refine max_lt ?_ ?_ <;> linarith [abs_nonneg η, le_abs_self η]
  have hcleared_near : (fun w => (deriv Num w * Z w - Num w * deriv Z w) * P w) =ᶠ[𝓝 z₀]
      fun w => Num w * Z w * PM w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show R₀ < z₀.re by rw [hz₀re]; linarith)] with w hw
    have hw1 : 1 < w.re := by linarith [abs_nonneg η]
    have hwH : w ∈ H := by
      show max θ η < w.re
      refine max_lt ?_ ?_ <;> linarith [abs_nonneg η, le_abs_self η]
    have hw1' : w ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hw1
      exact lt_irrefl _ hw1
    have hZw : Z w ≠ 0 := by
      rw [hZdef, zetaResidueFactor_of_ne hw1']
      exact mul_ne_zero (sub_ne_zero.mpr hw1') (riemannZeta_ne_zero_of_one_le_re hw1.le)
    have hid := deriv_deletionQuotient_mul Q hθ hN hψ hw
    rw [← hFdef, ← hPdef, ← hPMdef, hderivF w hwH hZw, hFeq] at hid
    field_simp at hid
    linear_combination hid
  have hcleared : Set.EqOn (fun w => (deriv Num w * Z w - Num w * deriv Z w) * P w)
      (fun w => Num w * Z w * PM w) H :=
    (((hNuman.deriv.mul hZan).sub (hNuman.mul hZan.deriv)).mul hPan).eqOn_of_preconnected_of_eventuallyEq
      ((hNuman.mul hZan).mul hPMan) hHconv.isPreconnected hz₀H hcleared_near
  -- `F` is not identically zero near `ρ₀`
  have hNumz₀ : Num z₀ ≠ 0 := by
    have hz₀1 : 1 < z₀.re := by rw [hz₀re]; linarith [abs_nonneg η]
    have hθz₀ : θ < z₀.re := by rw [hz₀re]; linarith [abs_nonneg η]
    rw [hNumdef, deletionNumerator_eq Q hθ hN hz₀1 hθz₀]
    refine mul_ne_zero ?_ ?_
    · refine sub_ne_zero.mpr fun h => ?_
      have := congr_arg Complex.re h
      rw [Complex.one_re, hz₀re] at this
      linarith [abs_nonneg η]
    · have hpos : 0 < LSeries (qFreeSeq Q) ((R₀ + 1 : ℝ) : ℂ) := by
        refine LSeries.positive (fun n => ?_) ?_ ?_
        · simp only [Pi.zero_apply, qFreeSeq]
          exact Complex.zero_le_real.mpr (qFreeIndicator_nonneg Q n)
        · simp [qFreeSeq, qFreeIndicator_one]
        · refine (abscissa_qFreeSeq_le Q).trans_lt ?_
          exact_mod_cast (show (1 : ℝ) < R₀ + 1 by linarith [abs_nonneg η])
      exact hpos.ne'
  have hZev : ∀ᶠ w in 𝓝 ρ₀, Z w ≠ 0 :=
    (hZdiff.continuous.continuousAt).eventually_ne hZρ
  have hFan : AnalyticAt ℂ F ρ₀ := (hNuman ρ₀ hρ₀H).div (hZan ρ₀ hρ₀H) hZρ
  have hnot : ¬∀ᶠ w in 𝓝 ρ₀, F w = 0 := by
    intro h
    have hNum0 : Num =ᶠ[𝓝 ρ₀] 0 := by
      filter_upwards [h, hZev] with w hw hZw
      rw [hFeq, div_eq_zero_iff] at hw
      exact hw.resolve_right hZw
    exact hNumz₀ (hNuman.eqOn_zero_of_preconnected_of_eventuallyEq_zero hHconv.isPreconnected
      hρ₀H hNum0 hz₀H)
  obtain ⟨m, u, hu, hu0, hFu⟩ := (hFan.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  refine ⟨m, ?_⟩
  -- local analysis at `ρ₀`
  set P₀ : ℂ → ℂ := fun w => ∏ ρ ∈ J.erase ρ₀, (w - ρ) with hP₀
  have hPfac : ∀ w, P w = (w - ρ₀) * P₀ w := fun w =>
    (Finset.mul_prod_erase J (fun ρ : ℂ => w - ρ) hρ₀).symm
  set φ₁ : ℂ → ℂ := fun w => (m * u w + (w - ρ₀) * deriv u w) * P₀ w with hφ₁
  set φ₂ : ℂ → ℂ := fun w => u w * PM w with hφ₂
  have hloc : ∀ᶠ w in 𝓝[≠] ρ₀, φ₁ w = φ₂ w := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hFu.eventually_nhds, hu.eventually_analyticAt, hHopen.mem_nhds hρ₀H,
      hFu, hZev] with w hwF hwu hwH hFw hZw hwne
    have hwne' : w - ρ₀ ≠ 0 := sub_ne_zero.mpr hwne
    have hderiv : HasDerivAt (fun w' => (w' - ρ₀) ^ m * u w')
        (m * (w - ρ₀) ^ (m - 1) * 1 * u w + (w - ρ₀) ^ m * deriv u w) w :=
      ((hasDerivAt_id w).sub_const ρ₀).pow m |>.mul hwu.differentiableAt.hasDerivAt
    have hFeq' : F =ᶠ[𝓝 w] fun w' => (w' - ρ₀) ^ m * u w' := by
      filter_upwards [hwF] with w' hw'
      rw [hw', smul_eq_mul]
    have hdF : deriv F w = m * (w - ρ₀) ^ (m - 1) * 1 * u w + (w - ρ₀) ^ m * deriv u w := by
      rw [hFeq'.deriv_eq]
      exact hderiv.deriv
    -- the uncleared identity at `w`
    have hkey : deriv F w * P w = F w * PM w := by
      have hc := hcleared hwH
      simp only at hc
      rw [hderivF w hwH hZw, hFeq]
      field_simp
      linear_combination hc
    rw [hdF, hPfac, hFw, smul_eq_mul] at hkey
    have hpow : (w - ρ₀) * (m * (w - ρ₀) ^ (m - 1)) = m * (w - ρ₀) ^ m := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]
        ring
    have hcancel : (w - ρ₀) ^ m * φ₁ w = (w - ρ₀) ^ m * φ₂ w := by
      simp only [hφ₁, hφ₂]
      linear_combination hkey - (u w * P₀ w) * hpow
    exact mul_left_cancel₀ (pow_ne_zero m hwne') hcancel
  -- pass to the limit
  have hPMcont : ContinuousAt PM ρ₀ := (hPMan _ hρ₀H).continuousAt
  have hucont : ContinuousAt u ρ₀ := hu.continuousAt
  have hu'cont : ContinuousAt (deriv u) ρ₀ := hu.deriv.continuousAt
  have hP₀cont : Continuous P₀ :=
    continuous_finsetProd _ fun ρ _ => continuous_id.sub continuous_const
  have hφ₁cont : ContinuousAt φ₁ ρ₀ :=
    ((continuousAt_const.mul hucont).add
      ((continuousAt_id.sub continuousAt_const).mul hu'cont)).mul hP₀cont.continuousAt
  have hφ₂cont : ContinuousAt φ₂ ρ₀ := hucont.mul hPMcont
  have hlim : φ₁ ρ₀ = φ₂ ρ₀ :=
    tendsto_nhds_unique ((hφ₁cont.tendsto.mono_left nhdsWithin_le_nhds).congr' hloc)
      (hφ₂cont.tendsto.mono_left nhdsWithin_le_nhds)
  -- evaluate at `ρ₀`
  have hP₀ne : P₀ ρ₀ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => sub_ne_zero.mpr ?_
    exact fun h => (Finset.mem_erase.mp hρ).1 h.symm
  have hPρ₀ : P ρ₀ = 0 := Finset.prod_eq_zero hρ₀ (sub_self _)
  have hPMρ₀ : PM ρ₀ = ρ₀ * c ρ₀ * P₀ ρ₀ := by
    rw [hPMdef, clearedLogDeriv, ← hPdef, hPρ₀, zero_mul, zero_mul, add_zero]
    rw [Finset.sum_eq_single ρ₀]
    · intro ρ hρ hne
      rw [Finset.prod_eq_zero (f := fun ρ' : ℂ => ρ₀ - ρ')
        (Finset.mem_erase.mpr ⟨Ne.symm hne, hρ₀⟩) (sub_self _), mul_zero]
    · intro h
      exact absurd hρ₀ h
  simp only [hφ₁, hφ₂, sub_self, zero_mul, add_zero, hPMρ₀] at hlim
  have hmain : ((m : ℂ) - ρ₀ * c ρ₀) * (u ρ₀ * P₀ ρ₀) = 0 := by
    linear_combination hlim
  rcases mul_eq_zero.mp hmain with h | h
  · linear_combination -h
  · exact absurd h (mul_ne_zero hu0 hP₀ne)

/-- **Residue quantization, real exponents.**  If `N_Q(x) = a x + O(x^θ)` and
`ψ_Q(x) = ∑_{ρ ∈ J} c_ρ x^ρ + O(x^η)` with real exponents, then `ρ c_ρ ∈ ℕ` for every
`ρ ∈ J` with `max θ η < ρ < 1`. -/
theorem residue_quantization {a θ η : ℝ} (hθ : 0 ≤ θ) {J : Finset ℝ} {c : ℝ → ℝ}
    (hN : (fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ)
    (hψ : (fun x : ℝ => deletedChebyshev Q x - ∑ ρ ∈ J, c ρ * x ^ ρ) =O[atTop] fun x => x ^ η)
    {ρ₀ : ℝ} (hρ₀ : ρ₀ ∈ J) (hθρ : θ < ρ₀) (hηρ : η < ρ₀) (hρ1 : ρ₀ < 1) :
    ∃ m : ℕ, ρ₀ * c ρ₀ = m := by
  classical
  have hinj : Set.InjOn (fun ρ : ℝ => (ρ : ℂ)) (J : Set ℝ) :=
    fun _ _ _ _ h => Complex.ofReal_injective h
  set J' : Finset ℂ := J.image fun ρ : ℝ => (ρ : ℂ) with hJ'
  set c' : ℂ → ℂ := fun z => (c z.re : ℂ) with hc'
  have hψ' : (fun x : ℝ => (deletedChebyshev Q x : ℂ) - ∑ ρ ∈ J', c' ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η := by
    refine IsBigO.of_norm_left ?_
    refine hψ.norm_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    rw [hJ', Finset.sum_image hinj, ← Complex.norm_real]
    congr 1
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hc', Complex.ofReal_re]
    rw [Complex.ofReal_cpow hx]
  have hρ₀' : (ρ₀ : ℂ) ∈ J' := Finset.mem_image_of_mem _ hρ₀
  have hZρ : zetaResidueFactor (ρ₀ : ℂ) ≠ 0 := by
    have hne : (ρ₀ : ℂ) ≠ 1 := by
      intro h
      have := congr_arg Complex.re h
      simp at this
      linarith
    rw [zetaResidueFactor_of_ne hne]
    exact mul_ne_zero (sub_ne_zero.mpr hne)
      (riemannZeta_ne_zero_of_ofReal_mem_Ioo (hθ.trans_lt hθρ) hρ1)
  obtain ⟨m, hm⟩ := residue_quantization_complex Q hθ hN hψ' hρ₀'
    (by simpa using hθρ) (by simpa using hηρ) hZρ
  refine ⟨m, ?_⟩
  have hm' : ((ρ₀ * c ρ₀ : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by
    simp only [hc', Complex.ofReal_re] at hm
    push_cast
    exact hm
  exact_mod_cast Complex.ofReal_injective hm'

/-- **Odd-weight deletions obey the half-dimension uncertainty.**  Suppose the deleted
Chebyshev function has the shape `(λ/κ)(x^κ + x^{κ/2}) + O(x^η)` with `λ` odd, `η < κ/2` and
`0 < κ < 1`.  This is the shape produced by deleting primes with counting function
`λ ∫^x t^{κ-1} dt / log t + O(x^{η'})`, `η' < κ/2`, whose squares contribute the `x^{κ/2}` term.
Then the `Q`-free integers admit no power saving `x^θ` with `θ < κ/2`, although the deleted
primes perturb the prime count by `x^κ`. -/
theorem not_isBigO_qFreeCount_of_odd {a θ η κ : ℝ} {l : ℕ} (hl : Odd l) (hθ : 0 ≤ θ)
    (hθκ : θ < κ / 2) (hηκ : η < κ / 2) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hψ : (fun x : ℝ => deletedChebyshev Q x - (l / κ) * (x ^ κ + x ^ (κ / 2))) =O[atTop]
      fun x => x ^ η) :
    ¬(fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ := by
  intro hN
  have hne : κ ≠ κ / 2 := by
    intro h
    linarith
  have hψ' : (fun x : ℝ => deletedChebyshev Q x -
      ∑ ρ ∈ ({κ, κ / 2} : Finset ℝ), (fun _ : ℝ => (l : ℝ) / κ) ρ * x ^ ρ) =O[atTop]
      fun x => x ^ η := by
    refine hψ.congr_left fun x => ?_
    rw [Finset.sum_pair hne]
    ring
  obtain ⟨m, hm⟩ := residue_quantization Q hθ hN hψ' (by simp) hθκ hηκ (by linarith)
  have hl2 : (l : ℝ) = 2 * m := by
    have hκne : κ ≠ 0 := hκ0.ne'
    field_simp at hm
    linarith
  have hl2' : l = 2 * m := by exact_mod_cast hl2
  obtain ⟨k, hk⟩ := hl
  omega

/-- **Zero-mimicking deletions.**  If the deleted Chebyshev function contains the term
`(λ/ρ) x^{ρ/2}` with `λ` odd — the square-term of a deletion imitating a zero of odd
multiplicity `λ` at `ρ` — and `ζ(ρ/2) ≠ 0`, then the `Q`-free integers admit no power saving
`x^θ` with `θ < Re ρ / 2`. -/
theorem not_isBigO_qFreeCount_of_odd_charge {a θ η : ℝ} {J : Finset ℂ} {c : ℂ → ℂ} {ρ : ℂ}
    {l : ℕ} (hl : Odd l) (hθ : 0 ≤ θ) (hρ0 : ρ ≠ 0)
    (hψ : (fun x : ℝ => (deletedChebyshev Q x : ℂ) - ∑ ρ' ∈ J, c ρ' * (x : ℂ) ^ ρ') =O[atTop]
      fun x : ℝ => x ^ η)
    (hmem : ρ / 2 ∈ J) (hc : c (ρ / 2) = l / ρ) (hθρ : θ < (ρ / 2).re) (hηρ : η < (ρ / 2).re)
    (hζ : riemannZeta (ρ / 2) ≠ 0) :
    ¬(fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ := by
  intro hN
  have hZ : zetaResidueFactor (ρ / 2) ≠ 0 := by
    by_cases h1 : ρ / 2 = 1
    · rw [h1, zetaResidueFactor_one]
      exact one_ne_zero
    · rw [zetaResidueFactor_of_ne h1]
      exact mul_ne_zero (sub_ne_zero.mpr h1) hζ
  obtain ⟨m, hm⟩ := residue_quantization_complex Q hθ hN hψ hmem hθρ hηρ hZ
  rw [hc] at hm
  have hl2 : (l : ℂ) = 2 * m := by
    field_simp at hm
    linear_combination hm
  have hl2' : l = 2 * m := by exact_mod_cast hl2
  obtain ⟨k, hk⟩ := hl
  omega

end PrimeDeletion

end

end RHTower
