import Mathlib
import GaloisForLFunctions.HTGeometry.BorelGrowthLemma

/-!
# The maximum term and the central index

For the Taylor coefficients `a` of an entire function, every radius `r > 0` has `‖a n‖ rⁿ → 0`, so
the terms of the series have a largest one.  The value of that largest term is the **maximum term**
`μ(r)`, and the largest index attaining it is the **central index** `ν(r)`.  These are the two
quantities Wiman–Valiron theory runs on.

This file builds them from the decay hypothesis alone:

* the terms are bounded and the supremum is attained (`exists_maxTerm_eq`);
* the set of attaining indices is finite, so a largest one exists (`centralIndex_mem`);
* `μ` is monotone in the radius, and so is `ν`.

The monotonicity of `ν` is the only step with content: if `ν(s) < ν(r)` for `r < s`, multiplying the
two maximality inequalities cancels the coefficients and leaves `(r/s)^ν(r) ≥ (r/s)^ν(s)` with a
ratio below one, which is false.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- The Taylor coefficients of an entire function: every radius decays. -/
def EntireCoeffs (a : ℕ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → Tendsto (fun n => ‖a n‖ * r ^ n) atTop (nhds 0)

variable {a : ℕ → ℂ} {r s : ℝ}

theorem term_nonneg (a : ℕ → ℂ) (hr : 0 < r) (n : ℕ) : 0 ≤ ‖a n‖ * r ^ n :=
  mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _)

/-- Only finitely many terms exceed a positive level. -/
theorem finite_setOf_le_term (ha : EntireCoeffs a) (hr : 0 < r) {c : ℝ} (hc : 0 < c) :
    {n : ℕ | c ≤ ‖a n‖ * r ^ n}.Finite := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (ha r hr) c hc
  refine Set.Finite.subset (Set.finite_Iio N) fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn
  by_contra hcon
  simp only [Set.mem_Iio, not_lt] at hcon
  have hd := hN n hcon
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (term_nonneg a hr n)] at hd
  linarith

theorem bddAbove_termRange (ha : EntireCoeffs a) (hr : 0 < r) :
    BddAbove (Set.range fun n => ‖a n‖ * r ^ n) := by
  have hfin : {n : ℕ | 1 ≤ ‖a n‖ * r ^ n}.Finite := finite_setOf_le_term ha hr one_pos
  have hsplit : (Set.range fun n => ‖a n‖ * r ^ n)
      ⊆ ((fun n => ‖a n‖ * r ^ n) '' {n : ℕ | 1 ≤ ‖a n‖ * r ^ n}) ∪ Set.Iic 1 := by
    rintro _ ⟨n, rfl⟩
    by_cases h : 1 ≤ ‖a n‖ * r ^ n
    · exact Or.inl ⟨n, h, rfl⟩
    · exact Or.inr (le_of_lt (not_le.mp h))
  exact BddAbove.mono hsplit ((hfin.image _).bddAbove.union bddAbove_Iic)

/-- The maximum term `μ(r) = sup_n ‖a n‖ rⁿ`. -/
noncomputable def maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ := ⨆ n, ‖a n‖ * r ^ n

theorem term_le_maxTerm (ha : EntireCoeffs a) (hr : 0 < r) (n : ℕ) :
    ‖a n‖ * r ^ n ≤ maxTerm a r :=
  le_ciSup (bddAbove_termRange ha hr) n

/-- **The maximum term is attained.**  A nonzero coefficient forces a positive maximum, and the
decay confines the competition to a finite set. -/
theorem exists_maxTerm_eq (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∃ N : ℕ, ‖a N‖ * r ^ N = maxTerm a r ∧ 0 < maxTerm a r := by
  classical
  have hpos₀ : 0 < ‖a n₀‖ * r ^ n₀ :=
    mul_pos (norm_pos_iff.mpr hn₀) (pow_pos hr _)
  have hfin : {n : ℕ | ‖a n₀‖ * r ^ n₀ ≤ ‖a n‖ * r ^ n}.Finite :=
    finite_setOf_le_term ha hr hpos₀
  have hmem : n₀ ∈ hfin.toFinset := by simp [Set.Finite.mem_toFinset]
  obtain ⟨N, hNmem, hNmax⟩ :=
    hfin.toFinset.exists_max_image (fun n => ‖a n‖ * r ^ n) ⟨n₀, hmem⟩
  have hN₀ : ‖a n₀‖ * r ^ n₀ ≤ ‖a N‖ * r ^ N := hNmax n₀ hmem
  have hall : ∀ n : ℕ, ‖a n‖ * r ^ n ≤ ‖a N‖ * r ^ N := by
    intro n
    by_cases hn : ‖a n₀‖ * r ^ n₀ ≤ ‖a n‖ * r ^ n
    · exact hNmax n (by simp [Set.Finite.mem_toFinset, hn])
    · exact le_trans (le_of_lt (not_le.mp hn)) hN₀
  have heq : ‖a N‖ * r ^ N = maxTerm a r :=
    le_antisymm (term_le_maxTerm ha hr N) (ciSup_le hall)
  exact ⟨N, heq, heq ▸ lt_of_lt_of_le hpos₀ hN₀⟩

/-- The indices attaining the maximum term. -/
def maxTermAttained (a : ℕ → ℂ) (r : ℝ) : Set ℕ := {n : ℕ | ‖a n‖ * r ^ n = maxTerm a r}

/-- The **central index** `ν(r)`: the largest index attaining the maximum term. -/
noncomputable def centralIndex (a : ℕ → ℂ) (r : ℝ) : ℕ := sSup (maxTermAttained a r)

theorem finite_maxTermAttained (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    (maxTermAttained a r).Finite := by
  obtain ⟨_, _, hpos⟩ := exists_maxTerm_eq ha hr hn₀
  refine Set.Finite.subset (finite_setOf_le_term ha hr hpos) fun n hn => ?_
  simp only [maxTermAttained, Set.mem_setOf_eq] at hn
  simp [Set.mem_setOf_eq, hn]

/-- The central index attains the maximum term. -/
theorem centralIndex_mem (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    centralIndex a r ∈ maxTermAttained a r := by
  obtain ⟨N, hN, _⟩ := exists_maxTerm_eq ha hr hn₀
  exact Nat.sSup_mem ⟨N, hN⟩ (finite_maxTermAttained ha hr hn₀).bddAbove

theorem term_centralIndex_eq (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ‖a (centralIndex a r)‖ * r ^ centralIndex a r = maxTerm a r :=
  centralIndex_mem ha hr hn₀

/-- No index above the central index attains the maximum term. -/
theorem le_centralIndex (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {n : ℕ} (hn : n ∈ maxTermAttained a r) : n ≤ centralIndex a r :=
  le_csSup (finite_maxTermAttained ha hr hn₀).bddAbove hn

theorem coeff_centralIndex_ne_zero (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    a (centralIndex a r) ≠ 0 := by
  obtain ⟨_, _, hpos⟩ := exists_maxTerm_eq ha hr hn₀
  intro hz
  rw [term_centralIndex_eq ha hr hn₀ |>.symm, hz] at hpos
  simp at hpos

/-! ## Monotonicity -/

/-- The maximum term is nondecreasing in the radius. -/
theorem maxTerm_mono (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r ≤ s) :
    maxTerm a r ≤ maxTerm a s := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  refine ciSup_le fun n => le_trans ?_ (term_le_maxTerm ha hs n)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrs n) (norm_nonneg _)

/-- **The central index is nondecreasing in the radius.**  The coefficients cancel when the two
maximality inequalities are multiplied, leaving an impossible comparison of powers of `r/s < 1`. -/
theorem centralIndex_mono (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r ≤ s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    centralIndex a r ≤ centralIndex a s := by
  rcases eq_or_lt_of_le hrs with heq | hlt
  · subst heq
    exact le_rfl
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  set m := centralIndex a r with hm
  set k := centralIndex a s with hk
  by_contra hcon
  have hkm : k < m := by omega
  have hamne : a m ≠ 0 := coeff_centralIndex_ne_zero ha hr hn₀
  have hakne : a k ≠ 0 := coeff_centralIndex_ne_zero ha hs hn₀
  have ham : 0 < ‖a m‖ := norm_pos_iff.mpr hamne
  have hak : 0 < ‖a k‖ := norm_pos_iff.mpr hakne
  -- `m` is maximal at radius `r`, `k` is maximal at radius `s`
  have h1 : ‖a k‖ * r ^ k ≤ ‖a m‖ * r ^ m := by
    rw [term_centralIndex_eq ha hr hn₀]
    exact term_le_maxTerm ha hr k
  have h2 : ‖a m‖ * s ^ m ≤ ‖a k‖ * s ^ k := by
    rw [term_centralIndex_eq ha hs hn₀]
    exact term_le_maxTerm ha hs m
  have hprod : (‖a k‖ * r ^ k) * (‖a m‖ * s ^ m) ≤ (‖a m‖ * r ^ m) * (‖a k‖ * s ^ k) :=
    mul_le_mul h1 h2 (mul_nonneg (norm_nonneg _) (pow_nonneg hs.le _))
      (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _))
  have hcancel : r ^ k * s ^ m ≤ r ^ m * s ^ k := by
    have hcoef : 0 < ‖a k‖ * ‖a m‖ := mul_pos hak ham
    have hrw : (‖a k‖ * r ^ k) * (‖a m‖ * s ^ m) = (‖a k‖ * ‖a m‖) * (r ^ k * s ^ m) := by ring
    have hrw2 : (‖a m‖ * r ^ m) * (‖a k‖ * s ^ k) = (‖a k‖ * ‖a m‖) * (r ^ m * s ^ k) := by ring
    rw [hrw, hrw2] at hprod
    exact le_of_mul_le_mul_left hprod hcoef
  -- but `r^k s^m > r^m s^k` because `k < m` and `r ≤ s`
  have hstrict : r ^ m * s ^ k < r ^ k * s ^ m := by
    have hsplit : r ^ m * s ^ k = (r ^ k * s ^ k) * r ^ (m - k) := by
      rw [mul_assoc, mul_comm (s ^ k), ← mul_assoc, ← pow_add]
      congr 2
      omega
    have hsplit2 : r ^ k * s ^ m = (r ^ k * s ^ k) * s ^ (m - k) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hsplit, hsplit2]
    refine mul_lt_mul_of_pos_left ?_ (mul_pos (pow_pos hr _) (pow_pos hs _))
    exact pow_lt_pow_left₀ hlt hr.le (by omega)
  linarith


/-! ## The two-sided growth law

The discrete form of `log mu(s) - log mu(r) = int_r^s nu(t) dt/t`: the central index at the two
endpoints bounds the growth of the maximum term from both sides, with no integration theory. -/

/-- **Lower growth law.**  The maximum term grows at least like the `nu(r)`-th power. -/
theorem mul_pow_le_maxTerm (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r ≤ s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    maxTerm a r * (s / r) ^ centralIndex a r ≤ maxTerm a s := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  set m := centralIndex a r with hm
  have hterm : ‖a m‖ * r ^ m = maxTerm a r := term_centralIndex_eq ha hr hn₀
  have hkey : maxTerm a r * (s / r) ^ m = ‖a m‖ * s ^ m := by
    rw [← hterm, mul_assoc, ← mul_pow, mul_div_cancel₀ _ (ne_of_gt hr)]
  rw [hkey]
  exact term_le_maxTerm ha hs m

/-- **Upper growth law.**  The maximum term grows at most like the `nu(s)`-th power. -/
theorem maxTerm_le_mul_pow (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r ≤ s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    maxTerm a s ≤ maxTerm a r * (s / r) ^ centralIndex a s := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  set k := centralIndex a s with hk
  have hterm : ‖a k‖ * s ^ k = maxTerm a s := term_centralIndex_eq ha hs hn₀
  have hle : maxTerm a s * (r / s) ^ k ≤ maxTerm a r := by
    have hkey : maxTerm a s * (r / s) ^ k = ‖a k‖ * r ^ k := by
      rw [← hterm, mul_assoc, ← mul_pow, mul_div_cancel₀ _ (ne_of_gt hs)]
    rw [hkey]
    exact term_le_maxTerm ha hr k
  have hpos : (0 : ℝ) < (s / r) ^ k := pow_pos (div_pos hs hr) k
  have hcancel : (r / s) ^ k * (s / r) ^ k = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm r s, div_self (by positivity), one_pow]
  calc maxTerm a s = maxTerm a s * ((r / s) ^ k * (s / r) ^ k) := by rw [hcancel, mul_one]
    _ = (maxTerm a s * (r / s) ^ k) * (s / r) ^ k := by ring
    _ ≤ maxTerm a r * (s / r) ^ k := mul_le_mul_of_nonneg_right hle (le_of_lt hpos)

/-- Logarithmic form of the lower growth law. -/
theorem centralIndex_mul_log_le_log_maxTerm_sub (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r ≤ s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    (centralIndex a r : ℝ) * Real.log (s / r)
      ≤ Real.log (maxTerm a s) - Real.log (maxTerm a r) := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  obtain ⟨_, _, hμr⟩ := exists_maxTerm_eq ha hr hn₀
  obtain ⟨_, _, hμs⟩ := exists_maxTerm_eq ha hs hn₀
  have hpow : (0 : ℝ) < (s / r) ^ centralIndex a r := pow_pos (div_pos hs hr) _
  have hle := mul_pow_le_maxTerm ha hr hrs hn₀
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (ne_of_gt hμr) (ne_of_gt hpow), Real.log_pow] at hlog
  linarith

/-- Logarithmic form of the upper growth law. -/
theorem log_maxTerm_sub_le_centralIndex_mul_log (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r ≤ s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    Real.log (maxTerm a s) - Real.log (maxTerm a r)
      ≤ (centralIndex a s : ℝ) * Real.log (s / r) := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  obtain ⟨_, _, hμr⟩ := exists_maxTerm_eq ha hr hn₀
  obtain ⟨_, _, hμs⟩ := exists_maxTerm_eq ha hs hn₀
  have hpow : (0 : ℝ) < (s / r) ^ centralIndex a s := pow_pos (div_pos hs hr) _
  have hle := maxTerm_le_mul_pow ha hr hrs hn₀
  have hlog := Real.log_le_log hμs hle
  rw [Real.log_mul (ne_of_gt hμr) (ne_of_gt hpow), Real.log_pow] at hlog
  linarith

/-- **The central index is bounded by the growth of the maximum term.**  Comparing the radii `r` and
`e r` turns the lower growth law into a bound on `nu(r)` itself. -/
theorem centralIndex_le_log_maxTerm_sub (ha : EntireCoeffs a) (hr : 0 < r)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    (centralIndex a r : ℝ)
      ≤ Real.log (maxTerm a (Real.exp 1 * r)) - Real.log (maxTerm a r) := by
  have hrs : r ≤ Real.exp 1 * r := by
    nlinarith [Real.add_one_le_exp (1 : ℝ), hr]
  have h := centralIndex_mul_log_le_log_maxTerm_sub ha hr hrs hn₀
  rwa [mul_div_assoc, div_self (ne_of_gt hr), mul_one, Real.log_exp, mul_one] at h

/-- **The maximum term is bounded by the central index.**  Comparing the radii `1` and `r` turns the
upper growth law into `log mu(r) <= log mu(1) + nu(r) log r`. -/
theorem log_maxTerm_le_centralIndex_mul_log (ha : EntireCoeffs a) (hr : 1 ≤ r)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    Real.log (maxTerm a r)
      ≤ Real.log (maxTerm a 1) + (centralIndex a r : ℝ) * Real.log r := by
  have h := log_maxTerm_sub_le_centralIndex_mul_log ha one_pos hr hn₀
  rw [div_one] at h
  linarith
  

/-- **Order transfer, one direction.**  Once the maximum term is at least one, the central index is
bounded by `log mu` at the slightly larger radius `e r`.  Since `log (e r) / log r -> 1`, this is the
inequality `limsup log nu(r) / log r <= limsup log log mu(r) / log r`. -/
theorem centralIndex_le_log_maxTerm (ha : EntireCoeffs a) (hr : 0 < r)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) (h1 : 1 ≤ maxTerm a r) :
    (centralIndex a r : ℝ) ≤ Real.log (maxTerm a (Real.exp 1 * r)) := by
  have h := centralIndex_le_log_maxTerm_sub ha hr hn₀
  have hlog : 0 ≤ Real.log (maxTerm a r) := Real.log_nonneg h1
  linarith


/-! ## The majorant sum

The maximum term and the full majorant `S(r) = sum ||a_n|| r^n` differ by no more than a doubling of
the radius, so they have the same order of growth.  This is the coefficient-side half of "the maximum
term has the order of the function". -/

/-- Halving the geometric weight against the doubled radius. -/
theorem term_le_maxTerm_two_mul (ha : EntireCoeffs a) (hr : 0 < r) (n : ℕ) :
    ‖a n‖ * r ^ n ≤ maxTerm a (2 * r) * (1 / 2 : ℝ) ^ n := by
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have h := term_le_maxTerm ha h2r n
  have hrw : (‖a n‖ * (2 * r) ^ n) * (1 / 2 : ℝ) ^ n = ‖a n‖ * r ^ n := by
    calc (‖a n‖ * (2 * r) ^ n) * (1 / 2 : ℝ) ^ n
        = ‖a n‖ * ((2 * r) ^ n * (1 / 2 : ℝ) ^ n) := by ring
      _ = ‖a n‖ * ((2 * r) * (1 / 2 : ℝ)) ^ n := by rw [← mul_pow]
      _ = ‖a n‖ * r ^ n := by rw [show (2 * r) * (1 / 2 : ℝ) = r by ring]
  rw [← hrw]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- The decay hypothesis already forces absolute convergence at every radius. -/
theorem summable_term (ha : EntireCoeffs a) (hr : 0 < r) :
    Summable fun n => ‖a n‖ * r ^ n := by
  refine Summable.of_nonneg_of_le (fun n => term_nonneg a hr n)
    (fun n => term_le_maxTerm_two_mul ha hr n) ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- The majorant `S(r) = sum ||a_n|| r^n`. -/
noncomputable def coeffSum (a : ℕ → ℂ) (r : ℝ) : ℝ := ∑' n, ‖a n‖ * r ^ n

/-- The maximum term is a single term of the majorant. -/
theorem maxTerm_le_coeffSum (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    maxTerm a r ≤ coeffSum a r := by
  obtain ⟨N, hN, _⟩ := exists_maxTerm_eq ha hr hn₀
  rw [← hN]
  exact (summable_term ha hr).le_tsum N fun j _ => term_nonneg a hr j

/-- **The majorant costs only a doubling of the radius.**  Summing the geometric bound gives
`S(r) <= 2 mu(2r)`, so the maximum term and the majorant have the same order. -/
theorem coeffSum_le_two_mul_maxTerm (ha : EntireCoeffs a) (hr : 0 < r) :
    coeffSum a r ≤ 2 * maxTerm a (2 * r) := by
  have hgeom : Summable fun n : ℕ => maxTerm a (2 * r) * (1 / 2 : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : coeffSum a r ≤ ∑' n : ℕ, maxTerm a (2 * r) * (1 / 2 : ℝ) ^ n :=
    Summable.tsum_le_tsum (fun n => term_le_maxTerm_two_mul ha hr n) (summable_term ha hr) hgeom
  have hsum : (∑' n : ℕ, maxTerm a (2 * r) * (1 / 2 : ℝ) ^ n) = 2 * maxTerm a (2 * r) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num),
      show ((1 : ℝ) - 1 / 2)⁻¹ = 2 by norm_num]
    ring
  rwa [hsum] at hle


/-! ## Cauchy's estimate: the maximum term is below the maximum modulus -/

/-- **Cauchy's estimate in term form.**  Every term `||a_n|| r^n` of the Taylor series is bounded by
any bound for `f` on the circle of radius `r`. -/
theorem taylorCoeff_norm_mul_pow_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ C) (n : ℕ) :
    ‖iteratedDeriv n f 0 / (n.factorial : ℂ)‖ * r ^ n ≤ C := by
  have hd : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) r) := hf.diffContOnCl
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hd hC
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hrn : (0 : ℝ) < r ^ n := pow_pos hr n
  rw [norm_div, Complex.norm_natCast, div_mul_eq_mul_div, div_le_iff₀ hfact]
  have h2 : ‖iteratedDeriv n f 0‖ * r ^ n ≤ ((n.factorial : ℝ) * C / r ^ n) * r ^ n :=
    mul_le_mul_of_nonneg_right h hrn.le
  rw [div_mul_cancel₀ _ (ne_of_gt hrn)] at h2
  linarith

/-- **The maximum term is below the maximum modulus.**  Together with `maxTerm_le_coeffSum` and
`coeffSum_le_two_mul_maxTerm` this sandwiches the maximum modulus between `mu(r)` and `2 mu(2r)`, so
the function, its majorant and its maximum term all have the same order of growth. -/
theorem maxTerm_le_of_forall_mem_sphere_norm_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℕ → ℂ}
    (hcoeff : ∀ n, a n = iteratedDeriv n f 0 / (n.factorial : ℂ))
    {r C : ℝ} (hr : 0 < r) (hC : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ C) :
    maxTerm a r ≤ C := by
  refine ciSup_le fun n => ?_
  rw [hcoeff n]
  exact taylorCoeff_norm_mul_pow_le hf hr hC n


/-! ## The order comparison

The maximum term and the central index have the same order: each eventual power bound on one gives an
eventual power bound on the other, at any strictly larger exponent.  This is the usable form of
`limsup log nu(r) / log r = limsup log log mu(r) / log r`. -/

/-- A nonzero coefficient of positive index sends the maximum term to infinity. -/
theorem tendsto_maxTerm_atTop (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) (hpos : 0 < n₀) :
    Filter.Tendsto (fun r : ℝ => maxTerm a r) atTop atTop := by
  have hcoef : (0 : ℝ) < ‖a n₀‖ := norm_pos_iff.mpr hn₀
  have hmono : Filter.Tendsto (fun r : ℝ => ‖a n₀‖ * r ^ n₀) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hcoef (tendsto_pow_atTop hpos.ne')
  refine tendsto_atTop_mono' _ ?_ hmono
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact term_le_maxTerm ha hr n₀

/-- **A power bound on the maximum term bounds the central index.** -/
theorem centralIndex_le_rpow_of_log_maxTerm_le_rpow
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) (hpos : 0 < n₀)
    {σ σ' : ℝ} (hlt : σ < σ')
    (h : ∀ᶠ r : ℝ in atTop, Real.log (maxTerm a r) ≤ r ^ σ) :
    ∀ᶠ r : ℝ in atTop, (centralIndex a r : ℝ) ≤ r ^ σ' := by
  have hE : Filter.Tendsto (fun r : ℝ => Real.exp 1 * r) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (Real.exp_pos 1) tendsto_id
  have h1 : ∀ᶠ r : ℝ in atTop, Real.log (maxTerm a (Real.exp 1 * r)) ≤ (Real.exp 1 * r) ^ σ :=
    hE.eventually h
  have h2 : ∀ᶠ r : ℝ in atTop, (1 : ℝ) ≤ maxTerm a r :=
    (tendsto_maxTerm_atTop ha hn₀ hpos).eventually_ge_atTop 1
  have h3 : ∀ᶠ r : ℝ in atTop, Real.exp 1 ^ σ ≤ r ^ (σ' - σ) :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < σ' - σ)).eventually_ge_atTop _
  filter_upwards [h1, h2, h3, eventually_gt_atTop (0 : ℝ)] with r hr1 hr2 hr3 hr4
  calc (centralIndex a r : ℝ)
      ≤ Real.log (maxTerm a (Real.exp 1 * r)) := centralIndex_le_log_maxTerm ha hr4 hn₀ hr2
    _ ≤ (Real.exp 1 * r) ^ σ := hr1
    _ = Real.exp 1 ^ σ * r ^ σ := Real.mul_rpow (Real.exp_pos 1).le hr4.le
    _ ≤ r ^ (σ' - σ) * r ^ σ := mul_le_mul_of_nonneg_right hr3 (Real.rpow_nonneg hr4.le σ)
    _ = r ^ σ' := by rw [← Real.rpow_add hr4]; ring_nf

/-- **A power bound on the central index bounds the maximum term.** -/
theorem log_maxTerm_le_rpow_of_centralIndex_le_rpow
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {σ σ' : ℝ} (hσ : 0 < σ) (hlt : σ < σ')
    (h : ∀ᶠ r : ℝ in atTop, (centralIndex a r : ℝ) ≤ r ^ σ) :
    ∀ᶠ r : ℝ in atTop, Real.log (maxTerm a r) ≤ r ^ σ' := by
  have hgap : (0 : ℝ) < σ' - σ := by linarith
  have hlog : ∀ᶠ r : ℝ in atTop, Real.log r ≤ (1 / 2) * r ^ (σ' - σ) := by
    have hlo := (isLittleO_log_rpow_atTop hgap).def (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with r hr hr1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hr1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hr
    linarith
  have hconst : ∀ᶠ r : ℝ in atTop, Real.log (maxTerm a 1) ≤ (1 / 2) * r ^ σ' := by
    have htop : Filter.Tendsto (fun r : ℝ => (1 / 2 : ℝ) * r ^ σ') atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) (tendsto_rpow_atTop (by linarith))
    exact htop.eventually_ge_atTop _
  filter_upwards [h, hlog, hconst, eventually_ge_atTop (1 : ℝ)] with r hrν hrlog hrc hr1
  have hpos : (0 : ℝ) < r := by linarith
  have hlogr : (0 : ℝ) ≤ Real.log r := Real.log_nonneg hr1
  have hstep : (centralIndex a r : ℝ) * Real.log r ≤ r ^ σ * ((1 / 2) * r ^ (σ' - σ)) := by
    refine mul_le_mul hrν hrlog hlogr (Real.rpow_nonneg hpos.le σ)
  have hsplit : r ^ σ * ((1 / 2) * r ^ (σ' - σ)) = (1 / 2) * r ^ σ' := by
    rw [show r ^ σ * ((1 / 2) * r ^ (σ' - σ)) = (1 / 2) * (r ^ σ * r ^ (σ' - σ)) by ring,
      ← Real.rpow_add hpos]
    ring_nf
  have hμ := log_maxTerm_le_centralIndex_mul_log ha hr1 hn₀
  rw [hsplit] at hstep
  linarith


/-! ## Geometric decay away from the central index

Outside the window cut out by the central indices at a smaller and a larger radius, the terms decay
geometrically relative to the maximum term, with ratio the radius ratio and uniformly in the
coefficients.  This is the mechanism behind "the central terms dominate". -/

/-- **Decay above the central index.**  Beyond the central index at the larger radius `s`, the term
at radius `r` is at most `mu(r)` times `(r/s)` to the excess. -/
theorem term_le_maxTerm_mul_pow_of_centralIndex_le
    (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r ≤ s) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {n : ℕ} (hn : centralIndex a s ≤ n) :
    ‖a n‖ * r ^ n ≤ maxTerm a r * (r / s) ^ (n - centralIndex a s) := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  set k := centralIndex a s with hk
  have hprod : (s / r) ^ k * (r / s) ^ k = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm s r, div_self (by positivity), one_pow]
  have hpowsplit : (r / s) ^ n = (r / s) ^ k * (r / s) ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hterm : ‖a n‖ * r ^ n = (‖a n‖ * s ^ n) * (r / s) ^ n := by
    rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ (ne_of_gt hs)]
  have h1 : ‖a n‖ * s ^ n ≤ maxTerm a s := term_le_maxTerm ha hs n
  have h2 : maxTerm a s ≤ maxTerm a r * (s / r) ^ k := maxTerm_le_mul_pow ha hr hrs hn₀
  calc ‖a n‖ * r ^ n = (‖a n‖ * s ^ n) * (r / s) ^ n := hterm
    _ ≤ (maxTerm a r * (s / r) ^ k) * (r / s) ^ n :=
        mul_le_mul_of_nonneg_right (le_trans h1 h2) (pow_nonneg (by positivity) n)
    _ = maxTerm a r * ((s / r) ^ k * (r / s) ^ k) * (r / s) ^ (n - k) := by
        rw [hpowsplit]; ring
    _ = maxTerm a r * (r / s) ^ (n - k) := by rw [hprod]; ring

/-- **Decay below the central index.**  Under the central index at the smaller radius `t`, the term
at radius `r` is at most `mu(r)` times `(t/r)` to the deficit. -/
theorem term_le_maxTerm_mul_pow_of_le_centralIndex
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t ≤ r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {n : ℕ} (hn : n ≤ centralIndex a t) :
    ‖a n‖ * r ^ n ≤ maxTerm a r * (t / r) ^ (centralIndex a t - n) := by
  have hr : 0 < r := lt_of_lt_of_le ht htr
  set k := centralIndex a t with hk
  have hprod : (t / r) ^ n * (r / t) ^ n = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm t r, div_self (by positivity), one_pow]
  have hpowsplit : (t / r) ^ k = (t / r) ^ n * (t / r) ^ (k - n) := by
    rw [← pow_add]
    congr 1
    omega
  have hterm : ‖a n‖ * r ^ n = (‖a n‖ * t ^ n) * (r / t) ^ n := by
    rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ (ne_of_gt ht)]
  have h1 : ‖a n‖ * t ^ n ≤ maxTerm a t := term_le_maxTerm ha ht n
  have h2 : maxTerm a t ≤ maxTerm a r * (t / r) ^ k := by
    have hinv : (r / t) ^ k * (t / r) ^ k = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm r t, div_self (by positivity), one_pow]
    have hstep := mul_le_mul_of_nonneg_right (mul_pow_le_maxTerm ha ht htr hn₀)
      (pow_nonneg (by positivity : (0:ℝ) ≤ t / r) k)
    calc maxTerm a t = maxTerm a t * ((r / t) ^ k * (t / r) ^ k) := by rw [hinv, mul_one]
      _ = (maxTerm a t * (r / t) ^ k) * (t / r) ^ k := by ring
      _ ≤ maxTerm a r * (t / r) ^ k := hstep
  calc ‖a n‖ * r ^ n = (‖a n‖ * t ^ n) * (r / t) ^ n := hterm
    _ ≤ (maxTerm a r * (t / r) ^ k) * (r / t) ^ n :=
        mul_le_mul_of_nonneg_right (le_trans h1 h2) (pow_nonneg (by positivity) n)
    _ = maxTerm a r * ((t / r) ^ n * (r / t) ^ n) * (t / r) ^ (k - n) := by
        rw [hpowsplit]; ring
    _ = maxTerm a r * (t / r) ^ (k - n) := by rw [hprod]; ring

set_option maxHeartbeats 1000000 in
/-- **The upper tail is a geometric remainder.**  Everything strictly beyond the central index at the
larger radius sums to at most `mu(r) (r/s) / (1 - r/s)`. -/
theorem tsum_upper_tail_le
    (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r < s) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑' j : ℕ, ‖a (j + (centralIndex a s + 1))‖ * r ^ (j + (centralIndex a s + 1))
      ≤ maxTerm a r * (r / s) / (1 - r / s) := by
  have hs : 0 < s := lt_trans hr hrs
  set k := centralIndex a s with hk
  set q : ℝ := r / s with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hs]
    exact hrs
  have hbound : ∀ j : ℕ,
      ‖a (j + (k + 1))‖ * r ^ (j + (k + 1)) ≤ maxTerm a r * q ^ (j + 1) := by
    intro j
    have h := term_le_maxTerm_mul_pow_of_centralIndex_le ha hr hrs.le hn₀
      (n := j + (k + 1)) (by omega)
    rwa [show j + (k + 1) - k = j + 1 by omega] at h
  have hsumL : Summable fun j : ℕ => ‖a (j + (k + 1))‖ * r ^ (j + (k + 1)) :=
    (summable_nat_add_iff (k + 1)).mpr (summable_term ha hr)
  have hgeomSummable : Summable fun j : ℕ => q ^ (j + 1) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0.le hq1)
  have hsumR : Summable fun j : ℕ => maxTerm a r * q ^ (j + 1) := hgeomSummable.mul_left _
  have hle := Summable.tsum_le_tsum hbound hsumL hsumR
  have hcalc : (∑' j : ℕ, maxTerm a r * q ^ (j + 1)) = maxTerm a r * q / (1 - q) := by
    rw [tsum_mul_left]
    have hgeom : (∑' j : ℕ, q ^ (j + 1)) = q / (1 - q) := by
      have h1 : (∑' j : ℕ, q ^ (j + 1)) = ∑' j : ℕ, q * q ^ j := by
        refine tsum_congr fun j => ?_
        rw [pow_succ, mul_comm]
      rw [h1, tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1, div_eq_mul_inv]
    rw [hgeom]
    ring
  rwa [hcalc] at hle


set_option maxHeartbeats 1000000 in
/-- **The lower tail is a geometric remainder.**  Everything strictly below the central index at the
smaller radius sums to at most `mu(r) (t/r) / (1 - t/r)`. -/
theorem sum_lower_tail_le
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑ n ∈ Finset.range (centralIndex a t), ‖a n‖ * r ^ n
      ≤ maxTerm a r * (t / r) / (1 - t / r) := by
  have hr : 0 < r := lt_trans ht htr
  set k := centralIndex a t with hk
  set q : ℝ := t / r with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hr]
    exact htr
  have hμ : (0 : ℝ) ≤ maxTerm a r :=
    le_trans (term_nonneg a hr 0) (term_le_maxTerm ha hr 0)
  have hstep : ∑ n ∈ Finset.range k, ‖a n‖ * r ^ n
      ≤ ∑ n ∈ Finset.range k, maxTerm a r * q ^ (k - n) := by
    refine Finset.sum_le_sum fun n hn => ?_
    exact term_le_maxTerm_mul_pow_of_le_centralIndex ha ht htr.le hn₀
      (by have := Finset.mem_range.mp hn; omega)
  have hreflect : ∑ n ∈ Finset.range k, q ^ (k - n) = ∑ j ∈ Finset.range k, q ^ (j + 1) := by
    have h := Finset.sum_range_reflect (fun j : ℕ => q ^ (j + 1)) k
    rw [← h]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk := Finset.mem_range.mp hj
    congr 1
    omega
  have hgeom : ∑ j ∈ Finset.range k, q ^ (j + 1) ≤ q / (1 - q) := by
    have hsplit : ∑ j ∈ Finset.range k, q ^ (j + 1) = q * ∑ j ∈ Finset.range k, q ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_succ, mul_comm]
    have hsum : ∑ j ∈ Finset.range k, q ^ j ≤ (1 - q)⁻¹ := by
      have hb := Summable.sum_le_tsum (Finset.range k) (fun j _ => pow_nonneg hq0.le j)
        (summable_geometric_of_lt_one hq0.le hq1)
      rwa [tsum_geometric_of_lt_one hq0.le hq1] at hb
    rw [hsplit, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hsum hq0.le
  calc ∑ n ∈ Finset.range k, ‖a n‖ * r ^ n
      ≤ ∑ n ∈ Finset.range k, maxTerm a r * q ^ (k - n) := hstep
    _ = maxTerm a r * ∑ n ∈ Finset.range k, q ^ (k - n) := by rw [Finset.mul_sum]
    _ = maxTerm a r * ∑ j ∈ Finset.range k, q ^ (j + 1) := by rw [hreflect]
    _ ≤ maxTerm a r * (q / (1 - q)) := mul_le_mul_of_nonneg_left hgeom hμ
    _ = maxTerm a r * q / (1 - q) := by ring

set_option maxHeartbeats 1000000 in
/-- **The central window carries everything.**  The majorant at radius `r` equals the sum over the
window between the central indices at `t < r` and `s > r`, plus two geometric remainders each
proportional to the maximum term. -/
theorem coeffSum_le_window_add_tails
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    coeffSum a r
      ≤ (∑ n ∈ Finset.Ico (centralIndex a t) (centralIndex a s + 1), ‖a n‖ * r ^ n)
        + (maxTerm a r * (t / r) / (1 - t / r) + maxTerm a r * (r / s) / (1 - r / s)) := by
  have hr : 0 < r := lt_trans ht htr
  have hs : 0 < s := lt_trans hr hrs
  have hsum := summable_term ha hr
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun n => ‖a n‖ * r ^ n)
    (centralIndex a s + 1) hsum
  have hmono : centralIndex a t ≤ centralIndex a s :=
    le_trans (centralIndex_mono ha ht htr.le hn₀) (centralIndex_mono ha hr hrs.le hn₀)
  have hcons : (∑ n ∈ Finset.Ico 0 (centralIndex a t), ‖a n‖ * r ^ n)
      + ∑ n ∈ Finset.Ico (centralIndex a t) (centralIndex a s + 1), ‖a n‖ * r ^ n
      = ∑ n ∈ Finset.Ico 0 (centralIndex a s + 1), ‖a n‖ * r ^ n :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  rw [Finset.range_eq_Ico] at hsplit
  have hlow := sum_lower_tail_le ha ht htr hn₀
  have hup := tsum_upper_tail_le ha hr hrs hn₀
  rw [Finset.range_eq_Ico] at hlow
  calc coeffSum a r
      = (∑ n ∈ Finset.Ico 0 (centralIndex a s + 1), ‖a n‖ * r ^ n)
        + ∑' j : ℕ, ‖a (j + (centralIndex a s + 1))‖ * r ^ (j + (centralIndex a s + 1)) :=
        hsplit.symm
    _ = (∑ n ∈ Finset.Ico 0 (centralIndex a t), ‖a n‖ * r ^ n)
        + (∑ n ∈ Finset.Ico (centralIndex a t) (centralIndex a s + 1), ‖a n‖ * r ^ n)
        + ∑' j : ℕ, ‖a (j + (centralIndex a s + 1))‖ * r ^ (j + (centralIndex a s + 1)) := by
        rw [hcons]
    _ ≤ maxTerm a r * (t / r) / (1 - t / r)
        + (∑ n ∈ Finset.Ico (centralIndex a t) (centralIndex a s + 1), ‖a n‖ * r ^ n)
        + maxTerm a r * (r / s) / (1 - r / s) := by
        gcongr
    _ = (∑ n ∈ Finset.Ico (centralIndex a t) (centralIndex a s + 1), ‖a n‖ * r ^ n)
        + (maxTerm a r * (t / r) / (1 - t / r) + maxTerm a r * (r / s) / (1 - r / s)) := by
        ring


/-! ## Continuity

On a compact positive interval only finitely many terms can compete for the maximum, so the maximum
term is locally the maximum of finitely many monomials, hence continuous.  Continuity is what lets
the Borel growth lemma be applied to `log mu`. -/

set_option maxHeartbeats 1000000 in
/-- On `[r₁, r₂]` the maximum term is the maximum of a fixed finite family of monomials. -/
theorem exists_finset_maxTerm_eq_sup'
    (ha : EntireCoeffs a) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle : r₁ ≤ r₂)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∃ (F : Finset ℕ) (hF : F.Nonempty),
      ∀ x ∈ Set.Icc r₁ r₂, maxTerm a x = F.sup' hF fun n => ‖a n‖ * x ^ n := by
  classical
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hle
  obtain ⟨N, hN, hpos⟩ := exists_maxTerm_eq ha hr₁ hn₀
  have hfin : {n : ℕ | maxTerm a r₁ ≤ ‖a n‖ * r₂ ^ n}.Finite :=
    finite_setOf_le_term ha hr₂ hpos
  have hNmem : N ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show maxTerm a r₁ ≤ ‖a N‖ * r₂ ^ N
    rw [← hN]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₁.le hle N) (norm_nonneg _)
  refine ⟨hfin.toFinset, ⟨N, hNmem⟩, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hxpos : 0 < x := lt_of_lt_of_le hr₁ hx1
  have hNle : maxTerm a r₁ ≤ ‖a N‖ * x ^ N := by
    rw [← hN]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₁.le hx1 N) (norm_nonneg _)
  refine le_antisymm (ciSup_le fun n => ?_)
    (Finset.sup'_le _ _ fun n _ => term_le_maxTerm ha hxpos n)
  by_cases hn : n ∈ hfin.toFinset
  · exact Finset.le_sup' (fun n => ‖a n‖ * x ^ n) hn
  · have hnot : ¬ (maxTerm a r₁ ≤ ‖a n‖ * r₂ ^ n) := by
      rw [Set.Finite.mem_toFinset] at hn
      exact hn
    have h1 : ‖a n‖ * x ^ n ≤ ‖a n‖ * r₂ ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxpos.le hx2 n) (norm_nonneg _)
    have h2 : ‖a n‖ * x ^ n ≤ ‖a N‖ * x ^ N := by
      have := not_le.mp hnot
      linarith
    exact le_trans h2 (Finset.le_sup' (fun n => ‖a n‖ * x ^ n) hNmem)

/-- **The maximum term is continuous on the positive ray.** -/
theorem continuousOn_maxTerm (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ContinuousOn (maxTerm a) (Set.Ioi 0) := by
  intro r hr
  have hr0 : (0 : ℝ) < r := hr
  obtain ⟨F, hF, hEq⟩ := exists_finset_maxTerm_eq_sup' ha (r₁ := r / 2) (r₂ := 2 * r)
    (by linarith) (by linarith) hn₀
  have hcont : Continuous fun x : ℝ => F.sup' hF fun n => ‖a n‖ * x ^ n :=
    Continuous.finset_sup'_apply hF fun n _ => continuous_const.mul (continuous_pow n)
  have hmem : Set.Ioo (r / 2) (2 * r) ∈ nhds r :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have heq : (fun x : ℝ => F.sup' hF fun n => ‖a n‖ * x ^ n) =ᶠ[nhds r] maxTerm a := by
    filter_upwards [hmem] with x hx
    exact (hEq x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).symm
  exact (hcont.continuousAt.congr heq).continuousWithinAt


/-! ## Good radii for the maximum term

The Borel growth lemma needs a continuous monotone majorant, which the central index -- a step
function -- is not.  The maximum term is continuous, so the lemma applies to `1 + log mu` and the
resulting bound is transferred to the central index through the two-sided growth law. -/

/-- The continuous monotone majorant `1 + log mu`, clamped below at `r₀`. -/
noncomputable def logMaxTermMajorant (a : ℕ → ℂ) (r₀ : ℝ) : ℝ → ℝ :=
  fun x => 1 + Real.log (maxTerm a (max x r₀))

set_option maxHeartbeats 1000000 in
/-- **Good radii for the maximum term.**  Beyond every bound there is a radius at which `1 + log mu`
does not double when the radius is scaled by `1 + 1/(1 + log mu(r))`. -/
theorem exists_ge_borel_maxTerm
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hμ₀ : 1 ≤ maxTerm a r₀) (R : ℝ) :
    ∃ r, max r₀ R ≤ r ∧
      Real.log (maxTerm a (r * (1 + (1 + Real.log (maxTerm a r))⁻¹)))
        < 1 + 2 * Real.log (maxTerm a r) := by
  have hbig : ∀ x : ℝ, (1 : ℝ) ≤ maxTerm a (max x r₀) :=
    fun x => le_trans hμ₀ (maxTerm_mono ha hr₀ (le_max_right x r₀))
  have hposμ : ∀ x : ℝ, (0 : ℝ) < maxTerm a (max x r₀) :=
    fun x => lt_of_lt_of_le one_pos (hbig x)
  have hmonoT : Monotone (logMaxTermMajorant a r₀) := by
    intro x y hxy
    have hx : (0 : ℝ) < max x r₀ := lt_of_lt_of_le hr₀ (le_max_right _ _)
    have hlog := Real.log_le_log (hposμ x) (maxTerm_mono ha hx (max_le_max hxy le_rfl))
    simp only [logMaxTermMajorant]
    linarith
  have hcontT : Continuous (logMaxTermMajorant a r₀) := by
    have h1 : Continuous fun x : ℝ => max x r₀ := continuous_id.max continuous_const
    have h3 : Continuous fun x : ℝ => maxTerm a (max x r₀) :=
      (continuousOn_maxTerm ha hn₀).comp_continuous h1
        (fun x => lt_of_lt_of_le hr₀ (le_max_right x r₀))
    exact continuous_const.add (h3.log fun x => ne_of_gt (hposμ x))
  have hT1 : ∀ x : ℝ, (1 : ℝ) ≤ logMaxTermMajorant a r₀ x := by
    intro x
    have := Real.log_nonneg (hbig x)
    simp only [logMaxTermMajorant]
    linarith
  obtain ⟨r, hr, hlt⟩ :=
    GaloisForLFunctions.Nevanlinna.exists_ge_lt_two_mul_scaled hcontT hmonoT hT1
      (R := max r₀ R) (lt_of_lt_of_le hr₀ (le_max_left r₀ R))
  refine ⟨r, hr, ?_⟩
  have hrr₀ : r₀ ≤ r := le_trans (le_max_left r₀ R) hr
  have hmaxr : max r r₀ = r := max_eq_left hrr₀
  have hTr : logMaxTermMajorant a r₀ r = 1 + Real.log (maxTerm a r) := by
    simp only [logMaxTermMajorant, hmaxr]
  have hTrpos : (0 : ℝ) < logMaxTermMajorant a r₀ r := lt_of_lt_of_le one_pos (hT1 r)
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le hr₀ hrr₀
  have hstepge : r ≤ r * (1 + (logMaxTermMajorant a r₀ r)⁻¹) := by
    nlinarith [inv_pos.mpr hTrpos]
  have hmaxs : max (r * (1 + (logMaxTermMajorant a r₀ r)⁻¹)) r₀
      = r * (1 + (logMaxTermMajorant a r₀ r)⁻¹) :=
    max_eq_left (le_trans hrr₀ hstepge)
  rw [logMaxTermMajorant, hmaxs, hTr] at hlt
  linarith

/-- **The central index at a good radius.**  At the radii produced by the growth lemma the central
index is bounded by twice the square of `1 + log mu`. -/
theorem centralIndex_le_of_borel_maxTerm
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {r : ℝ} (hr : 0 < r)
    (hμ : 1 ≤ maxTerm a r)
    (hgood : Real.log (maxTerm a (r * (1 + (1 + Real.log (maxTerm a r))⁻¹)))
        < 1 + 2 * Real.log (maxTerm a r)) :
    (centralIndex a r : ℝ) ≤ 2 * (1 + Real.log (maxTerm a r)) ^ 2 := by
  set L : ℝ := Real.log (maxTerm a r) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hμ
  set T : ℝ := 1 + L with hT
  have hT1 : (1 : ℝ) ≤ T := by rw [hT]; linarith
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  set x : ℝ := T⁻¹ with hx
  have hx0 : 0 < x := inv_pos.mpr hTpos
  have hx1 : x ≤ 1 := by
    rw [hx, inv_le_one_iff₀]
    exact Or.inr hT1
  set s : ℝ := r * (1 + x) with hs
  have hrs : r ≤ s := by rw [hs]; nlinarith
  -- the growth law bounds the central index by the increment of `log mu`
  have hgrow := centralIndex_mul_log_le_log_maxTerm_sub ha hr hrs hn₀
  have hsr : s / r = 1 + x := by
    rw [hs, mul_comm, mul_div_assoc, div_self (ne_of_gt hr), mul_one]
  -- `log (1 + x) ≥ x / 2` for `0 ≤ x ≤ 1`
  have hlog : x / 2 ≤ Real.log (1 + x) := by
    have hy : (0 : ℝ) < 1 / (1 + x) := by positivity
    have hle := Real.log_le_sub_one_of_pos hy
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub] at hle
    have hfrac : x / (1 + x) ≤ Real.log (1 + x) := by
      have hrw : (1 : ℝ) / (1 + x) - 1 = -(x / (1 + x)) := by
        field_simp
        ring
      rw [hrw] at hle
      linarith
    have hcmp : x / 2 ≤ x / (1 + x) := by
      apply div_le_div_of_nonneg_left hx0.le (by positivity)
      linarith
    linarith
  rw [hsr, ← hL] at hgrow
  have hnum : Real.log (maxTerm a s) - L < 1 + L := by linarith
  have hν0 : (0 : ℝ) ≤ (centralIndex a r : ℝ) := Nat.cast_nonneg _
  have hstep : (centralIndex a r : ℝ) * (x / 2) ≤ (centralIndex a r : ℝ) * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left hlog hν0
  have hcomb : (centralIndex a r : ℝ) * (x / 2) < T := by
    rw [hT]
    linarith
  have h2T : (0 : ℝ) < 2 * T := by linarith
  have hmul := mul_lt_mul_of_pos_right hcomb h2T
  have hxT : (x / 2) * (2 * T) = 1 := by
    rw [hx]
    field_simp
  have hfinal : (centralIndex a r : ℝ) < 2 * T ^ 2 := by
    calc (centralIndex a r : ℝ) = (centralIndex a r : ℝ) * ((x / 2) * (2 * T)) := by
          rw [hxT, mul_one]
      _ = ((centralIndex a r : ℝ) * (x / 2)) * (2 * T) := by ring
      _ < T * (2 * T) := hmul
      _ = 2 * T ^ 2 := by ring
  rw [hT] at hfinal
  linarith


/-! ## The derivative coefficients

`z f'(z) = sum n a_n z^n`, so the local analysis at a maximum-modulus point runs on the sequence
`n a_n`.  It satisfies the same decay hypothesis, and its maximum term is controlled by the central
index times the maximum term of `a`. -/

/-- **The derivative coefficients are again entire.**  Multiplying by the index costs only a
geometric factor, which the doubled radius absorbs. -/
theorem entireCoeffs_mul_index (ha : EntireCoeffs a) :
    EntireCoeffs (fun n => (n : ℂ) * a n) := by
  intro r hr
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hsummable : Summable fun n : ℕ => (n : ℝ) ^ 1 * ((1 : ℝ) / 2) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs]; norm_num)
  have hzero : Filter.Tendsto
      (fun n : ℕ => maxTerm a (2 * r) * ((n : ℝ) * ((1 : ℝ) / 2) ^ n)) atTop (nhds 0) := by
    have h := (hsummable.tendsto_atTop_zero).const_mul (maxTerm a (2 * r))
    simpa using h
  refine squeeze_zero (fun n => term_nonneg (fun n => (n : ℂ) * a n) hr n) (fun n => ?_) hzero
  have hnorm : ‖(n : ℂ) * a n‖ = (n : ℝ) * ‖a n‖ := by
    rw [norm_mul, Complex.norm_natCast]
  rw [hnorm, mul_assoc]
  have hbase := term_le_maxTerm_two_mul ha hr n
  calc (n : ℝ) * (‖a n‖ * r ^ n)
      ≤ (n : ℝ) * (maxTerm a (2 * r) * ((1 : ℝ) / 2) ^ n) :=
        mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg n)
    _ = maxTerm a (2 * r) * ((n : ℝ) * ((1 : ℝ) / 2) ^ n) := by ring

set_option maxHeartbeats 1000000 in
/-- **The derivative maximum term.**  Beyond the central index at a larger radius the extra factor
`n` is absorbed by the geometric decay, so `mu'` is at most `mu` times the central index plus a
constant depending only on the radius ratio. -/
theorem maxTerm_mul_index_le
    (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r < s) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    maxTerm (fun n => (n : ℂ) * a n) r
      ≤ maxTerm a r * ((centralIndex a s : ℝ) + ∑' j : ℕ, (j : ℝ) * (r / s) ^ j) := by
  have hs : 0 < s := lt_trans hr hrs
  set k := centralIndex a s with hk
  set q : ℝ := r / s with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hs]
    exact hrs
  have hμ : (0 : ℝ) ≤ maxTerm a r :=
    le_trans (term_nonneg a hr 0) (term_le_maxTerm ha hr 0)
  have hsummable : Summable fun j : ℕ => (j : ℝ) * q ^ j := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    simpa using h
  have hgeo : ∀ j : ℕ, (j : ℝ) * q ^ j ≤ ∑' i : ℕ, (i : ℝ) * q ^ i := fun j =>
    hsummable.le_tsum j fun i _ => by positivity
  have htail : (0 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) * q ^ i :=
    le_trans (by positivity) (hgeo 0)
  refine ciSup_le fun n => ?_
  have hnorm : ‖(n : ℂ) * a n‖ = (n : ℝ) * ‖a n‖ := by
    rw [norm_mul, Complex.norm_natCast]
  rw [hnorm, mul_assoc]
  rcases Nat.lt_or_ge n (k + 1) with hlt | hge
  · -- inside the window: the index is at most `k`
    have hnk : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hlt
    calc (n : ℝ) * (‖a n‖ * r ^ n)
        ≤ (k : ℝ) * maxTerm a r := by
          refine mul_le_mul hnk (term_le_maxTerm ha hr n) (term_nonneg a hr n)
            (le_trans (Nat.cast_nonneg n) hnk)
      _ ≤ maxTerm a r * ((k : ℝ) + ∑' i : ℕ, (i : ℝ) * q ^ i) := by nlinarith
  · -- beyond the window: geometric decay beats the factor `n`
    have hdecay := term_le_maxTerm_mul_pow_of_centralIndex_le ha hr hrs.le hn₀
      (n := n) (by omega)
    rw [← hk, ← hq] at hdecay
    have hsplit : (n : ℝ) = (k : ℝ) + ((n - k : ℕ) : ℝ) := by
      have : k ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hqpow : q ^ (n - k) ≤ 1 := pow_le_one₀ hq0.le hq1.le
    calc (n : ℝ) * (‖a n‖ * r ^ n)
        ≤ (n : ℝ) * (maxTerm a r * q ^ (n - k)) :=
          mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg n)
      _ = maxTerm a r * ((k : ℝ) * q ^ (n - k) + ((n - k : ℕ) : ℝ) * q ^ (n - k)) := by
          rw [hsplit]; ring
      _ ≤ maxTerm a r * ((k : ℝ) + ∑' i : ℕ, (i : ℝ) * q ^ i) := by
          refine mul_le_mul_of_nonneg_left ?_ hμ
          have h1 : (k : ℝ) * q ^ (n - k) ≤ (k : ℝ) := by
            nlinarith [Nat.cast_nonneg (α := ℝ) k, pow_nonneg hq0.le (n - k)]
          have h2 := hgeo (n - k)
          linarith


/-! ## The index deviation

`z f'(z) - k f(z) = sum (n - k) a_n z^n`, so the logarithmic derivative is close to `k/z` exactly
when the deviation series `sum |n - k| ||a_n|| r^n` is small compared with the function.  Inside the
window the deviation is at most the window width. -/

/-- The deviation series converges at every radius. -/
theorem summable_index_deviation (ha : EntireCoeffs a) (hr : 0 < r) (k : ℕ) :
    Summable fun n : ℕ => |(n : ℝ) - (k : ℝ)| * (‖a n‖ * r ^ n) := by
  have h1 : Summable fun n : ℕ => ‖a n‖ * r ^ n := summable_term ha hr
  have h2 : Summable fun n : ℕ => (n : ℝ) * (‖a n‖ * r ^ n) := by
    refine (summable_term (entireCoeffs_mul_index ha) hr).congr fun n => ?_
    rw [norm_mul, Complex.norm_natCast, mul_assoc]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (h2.add (h1.mul_left (k : ℝ)))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have habs : |(n : ℝ) - (k : ℝ)| ≤ (n : ℝ) + (k : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hT : (0 : ℝ) ≤ ‖a n‖ * r ^ n := term_nonneg a hr n
  calc |(n : ℝ) - (k : ℝ)| * (‖a n‖ * r ^ n)
      ≤ ((n : ℝ) + (k : ℝ)) * (‖a n‖ * r ^ n) := mul_le_mul_of_nonneg_right habs hT
    _ = (n : ℝ) * (‖a n‖ * r ^ n) + (k : ℝ) * (‖a n‖ * r ^ n) := by ring

/-- **The window width controls the deviation.**  Inside the window between the central indices at
`t < r` and `s > r` every index differs from `nu(r)` by at most the window width. -/
theorem sum_window_index_deviation_le
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑ n ∈ Finset.Ico (centralIndex a t) (centralIndex a s + 1),
        |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n)
      ≤ ((centralIndex a s : ℝ) - (centralIndex a t : ℝ))
        * ∑ n ∈ Finset.Ico (centralIndex a t) (centralIndex a s + 1), ‖a n‖ * r ^ n := by
  have hr : 0 < r := lt_trans ht htr
  have hνtr : centralIndex a t ≤ centralIndex a r := centralIndex_mono ha ht htr.le hn₀
  have hνrs : centralIndex a r ≤ centralIndex a s := centralIndex_mono ha hr hrs.le hn₀
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
  have hnt : (centralIndex a t : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hns : (n : ℝ) ≤ (centralIndex a s : ℝ) := by
    have : n ≤ centralIndex a s := by omega
    exact_mod_cast this
  have hrt : (centralIndex a t : ℝ) ≤ (centralIndex a r : ℝ) := by exact_mod_cast hνtr
  have hrs' : (centralIndex a r : ℝ) ≤ (centralIndex a s : ℝ) := by exact_mod_cast hνrs
  have habs : |(n : ℝ) - (centralIndex a r : ℝ)|
      ≤ (centralIndex a s : ℝ) - (centralIndex a t : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact mul_le_mul_of_nonneg_right habs (term_nonneg a hr n)


set_option maxHeartbeats 1000000 in
/-- **The full deviation estimate.**  Splitting at the two central indices bounds the deviation
series by the window width times the majorant, plus two remainders each proportional to the maximum
term, with constants fixed by the radius ratios alone. -/
theorem tsum_index_deviation_le_of_window_le
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {W : ℝ}
    (hW : ∑ n ∈ Finset.Ico (centralIndex a t) (centralIndex a s + 1), ‖a n‖ * r ^ n ≤ W) :
    ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n)
      ≤ ((centralIndex a s : ℝ) - (centralIndex a t : ℝ)) * W
        + (centralIndex a r : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
        + maxTerm a r * ((centralIndex a s : ℝ) + 1)
            * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1) := by
  have hr : 0 < r := lt_trans ht htr
  have hs : 0 < s := lt_trans hr hrs
  set q : ℝ := r / s with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hs]
    exact hrs
  set k := centralIndex a s with hk
  set m := centralIndex a t with hm
  set v := centralIndex a r with hv
  have hmv : m ≤ v := centralIndex_mono ha ht htr.le hn₀
  have hvk : v ≤ k := centralIndex_mono ha hr hrs.le hn₀
  set D : ℕ → ℝ := fun n => |(n : ℝ) - (v : ℝ)| * (‖a n‖ * r ^ n) with hD
  have hDnonneg : ∀ n, 0 ≤ D n := fun n =>
    mul_nonneg (abs_nonneg _) (term_nonneg a hr n)
  have hDsum : Summable D := summable_index_deviation ha hr v
  have hμ : (0 : ℝ) ≤ maxTerm a r :=
    le_trans (term_nonneg a hr 0) (term_le_maxTerm ha hr 0)
  -- the geometric majorant of the upper tail
  have hgsum : Summable fun j : ℕ => ((1 : ℝ) + j) * q ^ (j + 1) := by
    have h1 : Summable fun j : ℕ => (j : ℝ) * q ^ j := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    have h2 : Summable fun j : ℕ => q ^ j := summable_geometric_of_lt_one hq0.le hq1
    have h3 : Summable fun j : ℕ => ((1 : ℝ) + j) * q ^ j := by
      refine (h2.add h1).congr fun j => ?_
      ring
    simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using h3.mul_right q
  have hgnonneg : ∀ j : ℕ, (0 : ℝ) ≤ ((1 : ℝ) + j) * q ^ (j + 1) := fun j => by positivity
  -- the three pieces
  have hsplit := Summable.sum_add_tsum_nat_add (f := D) (k + 1) hDsum
  have hcons : (∑ n ∈ Finset.Ico 0 m, D n) + ∑ n ∈ Finset.Ico m (k + 1), D n
      = ∑ n ∈ Finset.Ico 0 (k + 1), D n :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  -- lower part
  have hlow : ∑ n ∈ Finset.Ico 0 m, D n
      ≤ (v : ℝ) * (maxTerm a r * (t / r) / (1 - t / r)) := by
    have hpt : ∀ n ∈ Finset.Ico 0 m, D n ≤ (v : ℝ) * (‖a n‖ * r ^ n) := by
      intro n hn
      obtain ⟨-, hn2⟩ := Finset.mem_Ico.mp hn
      have hnv : (n : ℝ) ≤ (v : ℝ) := by
        have : n ≤ v := by omega
        exact_mod_cast this
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have habs : |(n : ℝ) - (v : ℝ)| ≤ (v : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
      exact mul_le_mul_of_nonneg_right habs (term_nonneg a hr n)
    have hstep := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum] at hstep
    refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg v))
    have := sum_lower_tail_le ha ht htr hn₀
    rwa [Finset.range_eq_Ico] at this
  -- window part
  have hwin : ∑ n ∈ Finset.Ico m (k + 1), D n
      ≤ ((k : ℝ) - (m : ℝ)) * W := by
    have hstep := sum_window_index_deviation_le ha ht htr hrs hn₀
    rw [← hk, ← hm, ← hv] at hstep
    refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ (by
      have : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hmv hvk
      linarith))
    exact hW
  -- upper tail
  have hup : ∑' j : ℕ, D (j + (k + 1))
      ≤ maxTerm a r * ((k : ℝ) + 1) * ∑' j : ℕ, ((1 : ℝ) + j) * q ^ (j + 1) := by
    have hpt : ∀ j : ℕ, D (j + (k + 1))
        ≤ maxTerm a r * ((k : ℝ) + 1) * (((1 : ℝ) + j) * q ^ (j + 1)) := by
      intro j
      have hdecay := term_le_maxTerm_mul_pow_of_centralIndex_le ha hr hrs.le hn₀
        (n := j + (k + 1)) (by omega)
      rw [← hk, ← hq, show j + (k + 1) - k = j + 1 by omega] at hdecay
      have hidx : |((j + (k + 1) : ℕ) : ℝ) - (v : ℝ)| ≤ ((k : ℝ) + 1) * ((1 : ℝ) + j) := by
        have hvle : (v : ℝ) ≤ (k : ℝ) := by exact_mod_cast hvk
        have hcast : ((j + (k + 1) : ℕ) : ℝ) = (j : ℝ) + ((k : ℝ) + 1) := by push_cast; ring
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hv0 : (0 : ℝ) ≤ (v : ℝ) := Nat.cast_nonneg v
        rw [hcast]
        refine abs_le.mpr ⟨by nlinarith, by nlinarith⟩
      calc D (j + (k + 1))
          ≤ (((k : ℝ) + 1) * ((1 : ℝ) + j)) * (‖a (j + (k + 1))‖ * r ^ (j + (k + 1))) :=
            mul_le_mul_of_nonneg_right hidx (term_nonneg a hr _)
        _ ≤ (((k : ℝ) + 1) * ((1 : ℝ) + j)) * (maxTerm a r * q ^ (j + 1)) := by
            refine mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ = maxTerm a r * ((k : ℝ) + 1) * (((1 : ℝ) + j) * q ^ (j + 1)) := by ring
    have hsumL : Summable fun j : ℕ => D (j + (k + 1)) :=
      (summable_nat_add_iff (k + 1)).mpr hDsum
    have hsumR : Summable fun j : ℕ =>
        maxTerm a r * ((k : ℝ) + 1) * (((1 : ℝ) + j) * q ^ (j + 1)) := hgsum.mul_left _
    have := Summable.tsum_le_tsum hpt hsumL hsumR
    rwa [tsum_mul_left] at this
  calc ∑' n : ℕ, D n
      = (∑ n ∈ Finset.Ico 0 (k + 1), D n) + ∑' j : ℕ, D (j + (k + 1)) := by
        rw [← hsplit, Finset.range_eq_Ico]
    _ = (∑ n ∈ Finset.Ico 0 m, D n) + (∑ n ∈ Finset.Ico m (k + 1), D n)
        + ∑' j : ℕ, D (j + (k + 1)) := by rw [hcons]
    _ ≤ (v : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
        + ((k : ℝ) - (m : ℝ)) * W
        + maxTerm a r * ((k : ℝ) + 1) * ∑' j : ℕ, ((1 : ℝ) + j) * q ^ (j + 1) := by
        gcongr
    _ = ((k : ℝ) - (m : ℝ)) * W
        + (v : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
        + maxTerm a r * ((k : ℝ) + 1) * ∑' j : ℕ, ((1 : ℝ) + j) * q ^ (j + 1) := by ring

/-- The deviation estimate with the window bounded by the whole majorant. -/
theorem tsum_index_deviation_le
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n)
      ≤ ((centralIndex a s : ℝ) - (centralIndex a t : ℝ)) * coeffSum a r
        + (centralIndex a r : ℝ) * (maxTerm a r * (t / r) / (1 - t / r))
        + maxTerm a r * ((centralIndex a s : ℝ) + 1)
            * ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1) :=
  tsum_index_deviation_le_of_window_le ha ht htr hrs hn₀
    ((summable_term ha (lt_trans ht htr)).sum_le_tsum _
      (fun n _ => term_nonneg a (lt_trans ht htr) n))


/-! ## Log-convexity

`log mu` is a convex function of `log r`, because `mu(e^u) = sup_n ||a_n|| e^(n u)` is a supremum of
exponentials of affine functions.  This is the second-order information that the geometric decay
bounds do not carry: the two-sided growth law only says the difference quotients of `log mu` are
squeezed between the central indices, whereas convexity makes those quotients monotone. -/

set_option maxHeartbeats 1000000 in
/-- **Log-convexity of the maximum term.**  `u ↦ log mu(e^u)` is convex. -/
theorem convexOn_log_maxTerm_exp (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ConvexOn ℝ Set.univ (fun u : ℝ => Real.log (maxTerm a (Real.exp u))) := by
  refine ⟨convex_univ, fun u _ w _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  set v : ℝ := p * u + q * w with hv
  set N : ℕ := centralIndex a (Real.exp v) with hN
  have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have heu : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hew : (0 : ℝ) < Real.exp w := Real.exp_pos w
  have hterm : ‖a N‖ * (Real.exp v) ^ N = maxTerm a (Real.exp v) :=
    term_centralIndex_eq ha hev hn₀
  have hane : a N ≠ 0 := coeff_centralIndex_ne_zero ha hev hn₀
  have hapos : (0 : ℝ) < ‖a N‖ := norm_pos_iff.mpr hane
  obtain ⟨-, -, hμv⟩ := exists_maxTerm_eq ha hev hn₀
  obtain ⟨-, -, hμu⟩ := exists_maxTerm_eq ha heu hn₀
  obtain ⟨-, -, hμw⟩ := exists_maxTerm_eq ha hew hn₀
  -- split the term at the interpolated radius
  have hsplit : ‖a N‖ * (Real.exp v) ^ N
      = (‖a N‖ * (Real.exp u) ^ N) ^ p * (‖a N‖ * (Real.exp w) ^ N) ^ q := by
    have hexpv : (Real.exp v) ^ N = ((Real.exp u) ^ N) ^ p * ((Real.exp w) ^ N) ^ q := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_mul,
        ← Real.exp_mul, ← Real.exp_add, hv]
      congr 1
      ring
    have hanorm : ‖a N‖ = ‖a N‖ ^ p * ‖a N‖ ^ q := by
      rw [← Real.rpow_add hapos, hpq, Real.rpow_one]
    rw [hexpv]
    nth_rewrite 1 [hanorm]
    rw [Real.mul_rpow hapos.le (by positivity), Real.mul_rpow hapos.le (by positivity)]
    ring
  -- each factor is at most the maximum term at the corresponding radius
  have hbu : ‖a N‖ * (Real.exp u) ^ N ≤ maxTerm a (Real.exp u) := term_le_maxTerm ha heu N
  have hbw : ‖a N‖ * (Real.exp w) ^ N ≤ maxTerm a (Real.exp w) := term_le_maxTerm ha hew N
  have hprod : maxTerm a (Real.exp v)
      ≤ (maxTerm a (Real.exp u)) ^ p * (maxTerm a (Real.exp w)) ^ q := by
    rw [← hterm, hsplit]
    refine mul_le_mul (Real.rpow_le_rpow (by positivity) hbu hp)
      (Real.rpow_le_rpow (by positivity) hbw hq) (by positivity) (by positivity)
  -- take logarithms
  have hlog := Real.log_le_log hμv hprod
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hμu, Real.log_rpow hμw] at hlog
  exact hlog


/-! ## Exponential concentration

The geometric decay bounds, written on the exponential scale, say that a term at distance `j` from
the central index of the enlarged radius `r(1+delta)` is smaller than the maximum term by a factor
`exp(-j delta / 2)`.  The narrower the enlargement, the further out the concentration has to reach
before it bites -- which is the trade-off the Wiman--Valiron radius choice has to balance. -/

/-- `log (1 + x) >= x / 2` on `(0, 1]`. -/
private theorem half_le_log_one_add {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have hy : (0 : ℝ) < 1 / (1 + x) := by positivity
  have hle := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub] at hle
  have hrw : (1 : ℝ) / (1 + x) - 1 = -(x / (1 + x)) := by
    field_simp
    ring
  rw [hrw] at hle
  have hcmp : x / 2 ≤ x / (1 + x) := by
    apply div_le_div_of_nonneg_left hx0.le (by positivity)
    linarith
  linarith

/-- **Exponential decay above the central index.**  Beyond the central index at the enlarged radius
`r(1+delta)`, the terms fall off exponentially in the excess, at rate `delta / 2`. -/
theorem term_le_maxTerm_mul_exp_of_centralIndex_le
    (ha : EntireCoeffs a) (hr : 0 < r) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {n : ℕ} (hn : centralIndex a (r * (1 + δ)) ≤ n) :
    ‖a n‖ * r ^ n
      ≤ maxTerm a r
        * Real.exp (-(((n - centralIndex a (r * (1 + δ)) : ℕ) : ℝ) * (δ / 2))) := by
  have hbase : (0 : ℝ) < 1 + δ := by linarith
  have hs : r < r * (1 + δ) := by nlinarith
  have hμ : (0 : ℝ) ≤ maxTerm a r :=
    le_trans (term_nonneg a hr 0) (term_le_maxTerm ha hr 0)
  have hdecay := term_le_maxTerm_mul_pow_of_centralIndex_le ha hr hs.le hn₀ hn
  set k := centralIndex a (r * (1 + δ)) with hk
  set m : ℕ := n - k with hm
  have hq : r / (r * (1 + δ)) = (1 + δ)⁻¹ := by
    field_simp
  rw [hq] at hdecay
  have hpow : Real.exp ((m : ℝ) * (δ / 2)) ≤ (1 + δ) ^ m := by
    have h1 : Real.exp ((m : ℝ) * (δ / 2)) ≤ Real.exp ((m : ℝ) * Real.log (1 + δ)) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (half_le_log_one_add hδ0 hδ1) (Nat.cast_nonneg m))
    have h2 : Real.exp ((m : ℝ) * Real.log (1 + δ)) = (1 + δ) ^ m := by
      rw [Real.exp_nat_mul, Real.exp_log hbase]
    rwa [h2] at h1
  have hkey : ((1 + δ)⁻¹) ^ m ≤ Real.exp (-((m : ℝ) * (δ / 2))) := by
    rw [Real.exp_neg, inv_pow]
    exact inv_anti₀ (Real.exp_pos _) hpow
  exact le_trans hdecay (mul_le_mul_of_nonneg_left hkey hμ)

/-- **Exponential decay below the central index.**  Under the central index at the shrunken radius
`r/(1+delta)`, the terms fall off exponentially in the deficit, at the same rate. -/
theorem term_le_maxTerm_mul_exp_of_le_centralIndex
    (ha : EntireCoeffs a) (hr : 0 < r) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {n : ℕ} (hn : n ≤ centralIndex a (r / (1 + δ))) :
    ‖a n‖ * r ^ n
      ≤ maxTerm a r
        * Real.exp (-(((centralIndex a (r / (1 + δ)) - n : ℕ) : ℝ) * (δ / 2))) := by
  have hbase : (0 : ℝ) < 1 + δ := by linarith
  have ht : (0 : ℝ) < r / (1 + δ) := by positivity
  have htr : r / (1 + δ) ≤ r := by
    rw [div_le_iff₀ hbase]
    nlinarith
  have hμ : (0 : ℝ) ≤ maxTerm a r :=
    le_trans (term_nonneg a hr 0) (term_le_maxTerm ha hr 0)
  have hdecay := term_le_maxTerm_mul_pow_of_le_centralIndex ha ht htr hn₀ hn
  set k := centralIndex a (r / (1 + δ)) with hk
  set m : ℕ := k - n with hm
  have hq : (r / (1 + δ)) / r = (1 + δ)⁻¹ := by
    field_simp
  rw [hq] at hdecay
  have hpow : Real.exp ((m : ℝ) * (δ / 2)) ≤ (1 + δ) ^ m := by
    have h1 : Real.exp ((m : ℝ) * (δ / 2)) ≤ Real.exp ((m : ℝ) * Real.log (1 + δ)) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (half_le_log_one_add hδ0 hδ1) (Nat.cast_nonneg m))
    have h2 : Real.exp ((m : ℝ) * Real.log (1 + δ)) = (1 + δ) ^ m := by
      rw [Real.exp_nat_mul, Real.exp_log hbase]
    rwa [h2] at h1
  have hkey : ((1 + δ)⁻¹) ^ m ≤ Real.exp (-((m : ℝ) * (δ / 2))) := by
    rw [Real.exp_neg, inv_pow]
    exact inv_anti₀ (Real.exp_pos _) hpow
  exact le_trans hdecay (mul_le_mul_of_nonneg_left hkey hμ)


/-! ## The growth law in logarithmic coordinates

Writing `L(u) = log mu(e^u)`, the two-sided growth law says the increments of `L` are squeezed
between the central indices at the two endpoints.  This is the precise sense in which `nu` is the
derivative of `log mu` with respect to `log r`, and it is the form every Wiman--Valiron estimate
uses. -/

theorem log_maxTerm_exp_sub_le_centralIndex_mul
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {u v : ℝ} (huv : u ≤ v) :
    Real.log (maxTerm a (Real.exp v)) - Real.log (maxTerm a (Real.exp u))
      ≤ (centralIndex a (Real.exp v) : ℝ) * (v - u) := by
  have hlog : Real.log (Real.exp v / Real.exp u) = v - u := by
    rw [← Real.exp_sub, Real.log_exp]
  have h := log_maxTerm_sub_le_centralIndex_mul_log ha (Real.exp_pos u)
    (Real.exp_le_exp.mpr huv) hn₀
  rwa [hlog] at h

theorem centralIndex_mul_le_log_maxTerm_exp_sub
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {u v : ℝ} (huv : u ≤ v) :
    (centralIndex a (Real.exp u) : ℝ) * (v - u)
      ≤ Real.log (maxTerm a (Real.exp v)) - Real.log (maxTerm a (Real.exp u)) := by
  have hlog : Real.log (Real.exp v / Real.exp u) = v - u := by
    rw [← Real.exp_sub, Real.log_exp]
  have h := centralIndex_mul_log_le_log_maxTerm_sub ha (Real.exp_pos u)
    (Real.exp_le_exp.mpr huv) hn₀
  rwa [hlog] at h

/-- **The central index sits between adjacent increments of `log mu`.**  For `u < v < w` the
increment on the left is at most `nu(e^v)` times its width, and `nu(e^v)` times the right width is at
most the increment on the right. -/
theorem centralIndex_between_log_increments
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {u v w : ℝ} (huv : u < v) (hvw : v < w) :
    (Real.log (maxTerm a (Real.exp v)) - Real.log (maxTerm a (Real.exp u))) / (v - u)
        ≤ (centralIndex a (Real.exp v) : ℝ)
      ∧ (centralIndex a (Real.exp v) : ℝ)
        ≤ (Real.log (maxTerm a (Real.exp w)) - Real.log (maxTerm a (Real.exp v))) / (w - v) := by
  constructor
  · rw [div_le_iff₀ (by linarith)]
    exact log_maxTerm_exp_sub_le_centralIndex_mul ha hn₀ huv.le
  · rw [le_div_iff₀ (by linarith)]
    exact centralIndex_mul_le_log_maxTerm_exp_sub ha hn₀ hvw.le


/-! ## Entire functions -/

/-- The coefficients of a power series with infinite radius of convergence satisfy the decay
hypothesis, so an entire function has a maximum term and a central index at every radius. -/
theorem entireCoeffs_coeff_of_radius_eq_top
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (h : p.radius = ⊤) :
    EntireCoeffs (fun n => p.coeff n) := by
  intro r hr
  have hcoe : ((r.toNNReal : NNReal) : ℝ) = r := Real.coe_toNNReal r hr.le
  have hlt : ((r.toNNReal : NNReal) : ENNReal) < p.radius := by
    rw [h]
    exact ENNReal.coe_lt_top
  have hsum : Summable fun n => ‖p n‖ * r ^ n := by
    simpa [hcoe] using p.summable_norm_mul_pow hlt
  refine squeeze_zero (fun n => term_nonneg _ hr n) (fun n => ?_) hsum.tendsto_atTop_zero
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr.le n)
  have hle := (p n).le_opNorm (fun _ : Fin n => (1 : ℂ))
  simp only [norm_one, Finset.prod_const_one, mul_one] at hle
  exact hle

end GaloisForLFunctions.HTGeometry
