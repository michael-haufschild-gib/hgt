import GaloisForLFunctions.RHTower.PrimeDeletionResidueQuantization

/-!
# Integer-supported Beurling systems as perturbations of the integers

A Beurling system whose generalized integers are positive integers is described by its integer
masses `a : ℕ → ℝ` (`a n` is the multiplicity of `n`, here `|a n| ≤ 1`) and by the von Mangoldt
function `ℓ` of its generators, linked by `ℓ ⋆ a = a · log`.  Writing `ℓ = Λ - e`, the system is a
perturbation `e` of the rational primes: a set of deleted primes gives `e = Λ_Q ≥ 0`, added
composite generators give negative values.

With `L(a)` and `ζ` the Dirichlet series of `a` and of `1`, the quotient `L(a)/ζ` has logarithmic
derivative `L(e)` on `Re s > 1` (`deriv_LSeries_div_riemannZeta`).  A regular integer count
`Σ_{n ≤ x} a n = A x + O(x^θ)` continues `(s-1)L(a)(s)` to `Re s > θ` (`numerator_eq`), and a
power expansion `Σ_{n ≤ x} e n = Σ_ρ c_ρ x^ρ + O(x^η)` continues `L(e)` to `Re s > η`
(`LSeries_pertSeq_eq`).
-/

open Filter Topology Complex Asymptotics MeasureTheory Set ArithmeticFunction LSeries
open scoped LSeries.notation

namespace RHTower

noncomputable section

namespace IntegerBeurling

open PrimeDeletion (intervalIntegrable_floorSum differentiableAt_integral_cpow integrableOn_mul_cpow
  integral_cpow_mul_cpow integrableOn_cpow_mul_cpow)

variable (a e : ℕ → ℝ)

/-- The integer masses as a complex sequence. -/
def countSeq (n : ℕ) : ℂ := (a n : ℂ)

/-- The integer count `Σ_{n ≤ x} a n`. -/
def count (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, a k

/-- The perturbation as a complex sequence. -/
def pertSeq (n : ℕ) : ℂ := (e n : ℂ)

/-- The Chebyshev function `Σ_{n ≤ x} e n` of the perturbation. -/
def pertChebyshev (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, e k

/-! ### The logarithmic derivative of `L(a)/ζ` -/

variable {a e}

theorem countSeq_isBigO (ha : ∀ n, |a n| ≤ 1) :
    countSeq a =O[atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  rw [Real.rpow_zero, norm_one, one_mul, countSeq, Complex.norm_real, Real.norm_eq_abs]
  exact ha n

theorem abscissa_countSeq_le (ha : ∀ n, |a n| ≤ 1) : abscissaOfAbsConv (countSeq a) ≤ 1 := by
  have := LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (countSeq_isBigO ha)
  simpa using this

theorem summable_countSeq (ha : ∀ n, |a n| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (countSeq a) s :=
  LSeriesSummable_of_isBigO_rpow (x := 1) hs (by simpa using countSeq_isBigO ha)

/-- A sequence bounded by `C log n` has a summable Dirichlet series on `Re s > 1`. -/
theorem summable_of_abs_le_log {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C * Real.log n) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n => (f n : ℂ)) s := by
  have h1 : abscissaOfAbsConv (1 : ℕ → ℂ) < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  have hlog : LSeriesSummable (fun n => (C : ℂ) * logMul (1 : ℕ → ℂ) n) s :=
    (LSeriesSummable_logMul_of_lt_re h1).smul (C : ℂ)
  rw [LSeriesSummable, ← summable_norm_iff] at hlog ⊢
  refine hlog.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => LSeries.norm_term_le s ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, logMul, Pi.one_apply, mul_one, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n), ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact (hf n).trans (le_abs_self _)

/-- **Logarithmic derivative of `L(a)/ζ`.**  If `(Λ - e) ⋆ a = a · log` with `|a n| ≤ 1` and
`|e n| ≤ log n`, then on `Re s > 1`, `(L(a)/ζ)' = (L(a)/ζ) · L(e)`. -/
theorem deriv_LSeries_div_riemannZeta (ha : ∀ n, |a n| ≤ 1) (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : (fun n => ((Λ n - e n : ℝ) : ℂ)) ⍟ countSeq a = logMul (countSeq a)) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (fun z => LSeries (countSeq a) z / riemannZeta z) s =
      LSeries (countSeq a) s / riemannZeta s * LSeries (pertSeq e) s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have habs : abscissaOfAbsConv (countSeq a) < s.re :=
    (abscissa_countSeq_le ha).trans_lt (by exact_mod_cast hs)
  have hdL : DifferentiableAt ℂ (LSeries (countSeq a)) s :=
    (LSeries_hasDerivAt habs).differentiableAt
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hζ' : deriv riemannZeta s =
      -(riemannZeta s * LSeries (fun n => (Λ n : ℂ)) s) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    field_simp
  have hΛe : ∀ n, |Λ n - e n| ≤ 2 * Real.log n := fun n => by
    have h1 := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have h2 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have h3 := he n
    rw [abs_le] at h3 ⊢
    constructor <;> linarith
  have hsumℓ := summable_of_abs_le_log hΛe hs
  have hsume : LSeriesSummable (pertSeq e) s :=
    summable_of_abs_le_log (C := 1) (fun n => by rw [one_mul]; exact he n) hs
  have hderiv : deriv (LSeries (countSeq a)) s =
      -(LSeries (fun n => ((Λ n - e n : ℝ) : ℂ)) s * LSeries (countSeq a) s) := by
    rw [LSeries_deriv habs, ← hconv, LSeries_convolution' hsumℓ (summable_countSeq ha hs)]
  have hsplit : (fun n => ((Λ n - e n : ℝ) : ℂ)) = (fun n => (Λ n : ℂ)) - pertSeq e := by
    funext n
    simp [pertSeq]
  have hquot := deriv_div hdL hdζ hζ
  simp only [Pi.div_def] at hquot
  rw [hquot, hderiv, hζ', hsplit,
    LSeries_sub (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) hsume]
  field_simp
  ring

/-! ### Continuation of the numerator `(s-1)L(a)(s)` -/

/-- The sequence `a - A`. -/
def countDefectSeq (a : ℕ → ℝ) (A : ℝ) (n : ℕ) : ℂ := countSeq a n - (A : ℂ)

theorem countDefectSeq_eq (A : ℝ) : countDefectSeq a A = countSeq a - (A : ℂ) • 1 := by
  funext n
  simp [countDefectSeq]

theorem sum_countDefectSeq (A t : ℝ) :
    ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq a A k = ((count a t - A * ⌊t⌋₊ : ℝ) : ℂ) := by
  simp only [countDefectSeq, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, count, countSeq]
  push_cast
  ring

theorem countDefect_isBigO {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) :
    (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq a A k) =O[atTop] fun t => t ^ θ := by
  have h1 : (fun t : ℝ => A * (t - ⌊t⌋₊)) =O[atTop] fun t : ℝ => t ^ θ := by
    refine IsBigO.of_bound |A| ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have h0 : 0 ≤ t - ⌊t⌋₊ := sub_nonneg.mpr (Nat.floor_le (by linarith))
    have h1' : t - ⌊t⌋₊ ≤ 1 := by
      have := Nat.lt_floor_add_one t
      linarith
    have hpow : 1 ≤ t ^ θ := Real.one_le_rpow ht hθ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) θ)]
    exact mul_le_mul_of_nonneg_left (h1'.trans hpow) (abs_nonneg A)
  refine IsBigO.of_norm_left ?_
  refine (hN.add h1).norm_left.congr_left fun t => ?_
  rw [sum_countDefectSeq, Complex.norm_real]
  congr 1
  ring

/-- The Mellin integral continuing `L(a) - A ζ` to `Re s > θ`. -/
def countDefectIntegral (a : ℕ → ℝ) (A : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq a A k) * (t : ℂ) ^ (-(z + 1))

theorem differentiableAt_countDefectIntegral {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) {s : ℂ}
    (hs : θ < s.re) : DifferentiableAt ℂ (countDefectIntegral a A) s :=
  differentiableAt_integral_cpow (fun y _ => intervalIntegrable_floorSum _ y)
    (countDefect_isBigO hθ hN) hs

theorem LSeries_countSeq_sub (ha : ∀ n, |a n| ≤ 1) {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) {s : ℂ}
    (hs : 1 < s.re) (hθs : θ < s.re) :
    LSeries (countSeq a) s - A * riemannZeta s = s * countDefectIntegral a A s := by
  have hseq : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, countDefectSeq a A k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ θ := by
    have := (countDefect_isBigO hθ hN).comp_tendsto tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, Nat.floor_natCast] using this
  have hone : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hsum : LSeriesSummable (countDefectSeq a A) s := by
    rw [countDefectSeq_eq]
    exact (summable_countSeq ha hs).sub (hone.smul _)
  rw [countDefectIntegral, ← LSeries_eq_mul_integral _ hθ hθs hsum hseq, countDefectSeq_eq,
    LSeries_sub (summable_countSeq ha hs) (hone.smul _), LSeries_smul,
    LSeries_one_eq_riemannZeta hs]

/-- `(s-1) L(a)(s)`, continued to `Re s > θ`. -/
def numerator (a : ℕ → ℝ) (A : ℝ) (z : ℂ) : ℂ :=
  A * zetaResidueFactor z + (z - 1) * z * countDefectIntegral a A z

theorem numerator_eq (ha : ∀ n, |a n| ≤ 1) {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) {z : ℂ}
    (hz : 1 < z.re) (hθz : θ < z.re) :
    numerator a A z = (z - 1) * LSeries (countSeq a) z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hz
    exact lt_irrefl _ hz
  have h := LSeries_countSeq_sub ha hθ hN hz hθz
  rw [numerator, zetaResidueFactor_of_ne hz1,
    show (z - 1) * z * countDefectIntegral a A z = (z - 1) * (z * countDefectIntegral a A z) by
      ring, ← h]
  ring

theorem differentiableAt_numerator {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) {z : ℂ}
    (hz : θ < z.re) : DifferentiableAt ℂ (numerator a A) z := by
  unfold numerator
  exact ((differentiableAt_const _).mul (differentiable_zetaResidueFactor z)).add
    (((differentiableAt_id.sub (differentiableAt_const _)).mul differentiableAt_id).mul
      (differentiableAt_countDefectIntegral hθ hN hz))

/-! ### Continuation of `L(e)` -/

variable (e) in
/-- The remainder of a complex power expansion of the perturbation's Chebyshev function. -/
def remainder (J : Finset ℂ) (c : ℂ → ℂ) (t : ℝ) : ℂ :=
  (pertChebyshev e t : ℂ) - ∑ ρ ∈ J, c ρ * (t : ℂ) ^ ρ

variable (e) in
/-- The Mellin integral of the remainder. -/
def remainderIntegral (J : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (1:ℝ), remainder e J c t * (t : ℂ) ^ (-(z + 1))

theorem intervalIntegrable_remainder (J : Finset ℂ) (c : ℂ → ℂ) (y : ℝ) (hy : 1 ≤ y) :
    IntervalIntegrable (remainder e J c) volume 1 y := by
  have hstep := intervalIntegrable_floorSum (pertSeq e) y
  have hcont : ContinuousOn (fun t : ℝ => ∑ ρ ∈ J, c ρ * (t : ℂ) ^ ρ) (Set.uIcc 1 y) := by
    refine continuousOn_finsetSum _ fun ρ _ => continuousOn_const.mul ?_
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    exact ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.mpr (zero_lt_one.trans_le ht.1))).continuousWithinAt
  refine (hstep.sub hcont.intervalIntegrable).congr fun t _ => ?_
  simp only [remainder, pertChebyshev, pertSeq]
  push_cast
  rfl

theorem differentiableAt_remainderIntegral {J : Finset ℂ} {c : ℂ → ℂ} {η : ℝ}
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    {s : ℂ} (hs : η < s.re) : DifferentiableAt ℂ (remainderIntegral e J c) s :=
  differentiableAt_integral_cpow (intervalIntegrable_remainder J c) hψ hs

theorem abs_le_self_of_abs_le_log (he : ∀ n, |e n| ≤ Real.log n) (n : ℕ) : |e n| ≤ n := by
  refine (he n).trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)
  linarith

theorem pertSeq_isBigO (he : ∀ n, |e n| ≤ Real.log n) :
    pertSeq e =O[atTop] fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul, pertSeq, Complex.norm_real,
    Real.norm_of_nonneg (Nat.cast_nonneg n), Real.norm_eq_abs]
  exact abs_le_self_of_abs_le_log he n

theorem sum_pertSeq_isBigO (he : ∀ n, |e n| ≤ Real.log n) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, pertSeq e k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have hle : ∀ k ∈ Finset.Icc 1 n, ‖pertSeq e k‖ ≤ n := by
    intro k hk
    rw [pertSeq, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le_self_of_abs_le_log he k).trans (by exact_mod_cast (Finset.mem_Icc.mp hk).2)
  calc ‖∑ k ∈ Finset.Icc 1 n, pertSeq e k‖ ≤ ∑ k ∈ Finset.Icc 1 n, ‖pertSeq e k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, (n : ℝ) := Finset.sum_le_sum hle
    _ = 1 * ‖(n : ℝ) ^ (2 : ℝ)‖ := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, one_mul,
          Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_two, sq]

/-- **Continuation of `L(e)`.**  For `Re s` beyond every exponent,
`L(e)(s) = s (Σ_ρ c_ρ/(s-ρ) + ∫_1^∞ R(t) t^{-(s+1)} dt)`. -/
theorem LSeries_pertSeq_eq (he : ∀ n, |e n| ≤ Real.log n) {J : Finset ℂ} {c : ℂ → ℂ} {η : ℝ}
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    {s : ℂ} (hs : 2 < s.re) (hηs : η < s.re) (hJ : ∀ ρ ∈ J, ρ.re < s.re) :
    LSeries (pertSeq e) s = s * (∑ ρ ∈ J, c ρ / (s - ρ) + remainderIntegral e J c s) := by
  have hsum : LSeriesSummable (pertSeq e) s :=
    LSeriesSummable_of_isBigO_rpow (x := 2) hs (pertSeq_isBigO he)
  rw [LSeries_eq_mul_integral _ (by norm_num : (0:ℝ) ≤ 2) hs hsum (sum_pertSeq_isBigO he)]
  congr 1
  have hR : IntegrableOn (fun t : ℝ => remainder e J c t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_mul_cpow (intervalIntegrable_remainder J c) hψ hηs
  have hsplit : ∀ t ∈ Ioi (1:ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, pertSeq e k) * (t : ℂ) ^ (-(s + 1)) =
        remainder e J c t * (t : ℂ) ^ (-(s + 1)) +
          ∑ ρ ∈ J, c ρ * ((t : ℂ) ^ ρ * (t : ℂ) ^ (-(s + 1))) := by
    intro t _
    have hcast : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, pertSeq e k =
        remainder e J c t + ∑ ρ ∈ J, c ρ * (t : ℂ) ^ ρ := by
      simp only [remainder, pertChebyshev, pertSeq]
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

end IntegerBeurling

end

end RHTower
