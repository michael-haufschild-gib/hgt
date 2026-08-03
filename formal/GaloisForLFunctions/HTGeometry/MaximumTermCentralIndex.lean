import Mathlib

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
