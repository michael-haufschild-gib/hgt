import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex

/-!
# Concentration of the terms about the central index

Second-order and localisation properties of the maximum term: `log μ` is convex in `log r`, the terms
fall off exponentially away from the central index, the central index is a subderivative of `log μ`,
a pigeonhole on a chain of radii produces a step across which it barely moves, and the majorant is
bounded back by the maximum term.  The section closes with the normalised coefficients — every term
divided by the central one lies in the closed unit disc — and with the differentiated majorant, whose
first moment is the mean-minus-mode gap.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ} {r s : ℝ}

/-! ## Log-convexity

`log mu` is a convex function of `log r`, because `mu(e^u) = sup_n ||a_n|| e^(n u)` is a supremum of
exponentials of affine functions.  This is the second-order information that the geometric decay
bounds do not carry: the two-sided growth law only says the difference quotients of `log mu` are
squeezed between the central indices, whereas convexity makes those quotients monotone. -/

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


/-! ## A radius where the central index barely moves

The Borel growth lemma cannot be applied to `nu` directly, because `nu` is a step function and the
lemma needs continuity.  The substitute is a pigeonhole on a chain of radii: the increments of a
monotone function telescope, so along `N` consecutive steps at least one increment is at most the
total rise divided by `N`.  Applied to the central index this produces a radius across which `nu`
moves by an arbitrarily small fraction of its total growth. -/

/-- **Telescoping pigeonhole.**  Along `N` steps of a monotone sequence some increment is at most the
average. -/
theorem exists_increment_le_average (g : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ i < N, g (i + 1) - g i ≤ (g N - g 0) / N := by
  by_contra hcon
  have hall : ∀ i < N, (g N - g 0) / N < g (i + 1) - g i := by
    intro i hi
    by_contra h
    exact hcon ⟨i, hi, not_lt.mp h⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have htel : ∑ i ∈ Finset.range N, (g (i + 1) - g i) = g N - g 0 :=
    Finset.sum_range_sub g N
  have hlt : (N : ℝ) * ((g N - g 0) / N) < ∑ i ∈ Finset.range N, (g (i + 1) - g i) := by
    have h := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hN.ne')
      (fun i hi => hall i (Finset.mem_range.mp hi))
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  rw [htel, mul_div_cancel₀ _ (ne_of_gt hNpos)] at hlt
  exact lt_irrefl _ hlt

/-- **A step with a small central-index increment.**  Along a geometric chain of `N` radii some step
raises the central index -- it never lowers it -- by at most the total rise divided by `N`. -/
theorem exists_small_centralIndex_increment
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {u h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) :
    ∃ i < N,
      centralIndex a (Real.exp (u + (i : ℝ) * h))
          ≤ centralIndex a (Real.exp (u + ((i : ℝ) + 1) * h))
        ∧ (centralIndex a (Real.exp (u + ((i : ℝ) + 1) * h)) : ℝ)
            - (centralIndex a (Real.exp (u + (i : ℝ) * h)) : ℝ)
          ≤ ((centralIndex a (Real.exp (u + (N : ℝ) * h)) : ℝ)
              - (centralIndex a (Real.exp u) : ℝ)) / N := by
  set g : ℕ → ℝ := fun i => (centralIndex a (Real.exp (u + (i : ℝ) * h)) : ℝ) with hg
  obtain ⟨i, hi, hle⟩ := exists_increment_le_average g hN
  have hstep : u + (i : ℝ) * h ≤ u + ((i : ℝ) + 1) * h := by nlinarith
  have hmono : centralIndex a (Real.exp (u + (i : ℝ) * h))
      ≤ centralIndex a (Real.exp (u + ((i : ℝ) + 1) * h)) :=
    centralIndex_mono ha (Real.exp_pos _) (Real.exp_le_exp.mpr hstep) hn₀
  refine ⟨i, hi, hmono, ?_⟩
  have hg0 : g 0 = (centralIndex a (Real.exp u) : ℝ) := by simp [hg]
  have hgN : g N = (centralIndex a (Real.exp (u + (N : ℝ) * h)) : ℝ) := rfl
  have hgi : g (i + 1) = (centralIndex a (Real.exp (u + ((i : ℝ) + 1) * h)) : ℝ) := by
    simp only [hg]
    push_cast
    ring_nf
  rw [← hgi, ← hg0, ← hgN]
  exact hle

/-! ## The majorant against the central index

The maximum term is below the maximum modulus, and the maximum modulus is below the majorant; this
bounds the majorant back in terms of the maximum term, with the central index as the only cost.  All
three quantities therefore agree up to a factor linear in `nu`. -/

/-- **The majorant costs one central index.**  `S(r) <= mu(r) (nu(s) + 1 + (r/s)/(1 - r/s))` for any
`s > r`: the terms up to `nu(s)` are each at most `mu(r)`, and the rest is the geometric tail. -/
theorem coeffSum_le_maxTerm_mul_centralIndex
    (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r < s) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    coeffSum a r
      ≤ maxTerm a r * (((centralIndex a s : ℝ) + 1) + (r / s) / (1 - r / s)) := by
  classical
  have hs : 0 < s := lt_trans hr hrs
  set k := centralIndex a s with hk
  have hμ : (0 : ℝ) ≤ maxTerm a r :=
    le_trans (term_nonneg a hr 0) (term_le_maxTerm ha hr 0)
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun n => ‖a n‖ * r ^ n) (k + 1)
    (summable_term ha hr)
  have hhead : ∑ n ∈ Finset.range (k + 1), ‖a n‖ * r ^ n ≤ ((k : ℝ) + 1) * maxTerm a r := by
    have hbd : ∀ n ∈ Finset.range (k + 1), ‖a n‖ * r ^ n ≤ maxTerm a r :=
      fun n _ => term_le_maxTerm ha hr n
    have h := Finset.sum_le_card_nsmul _ _ _ hbd
    rw [Finset.card_range, nsmul_eq_mul] at h
    calc ∑ n ∈ Finset.range (k + 1), ‖a n‖ * r ^ n ≤ ((k + 1 : ℕ) : ℝ) * maxTerm a r := h
      _ = ((k : ℝ) + 1) * maxTerm a r := by push_cast; ring
  have htail := tsum_upper_tail_le ha hr hrs hn₀
  rw [← hk] at htail
  calc coeffSum a r
      = (∑ n ∈ Finset.range (k + 1), ‖a n‖ * r ^ n)
        + ∑' j : ℕ, ‖a (j + (k + 1))‖ * r ^ (j + (k + 1)) := hsplit.symm
    _ ≤ ((k : ℝ) + 1) * maxTerm a r + maxTerm a r * (r / s) / (1 - r / s) := by
        exact add_le_add hhead htail
    _ = maxTerm a r * (((k : ℝ) + 1) + (r / s) / (1 - r / s)) := by ring


/-! ## The normalised coefficients

Dividing the series by its central term normalises every coefficient to modulus at most one, with
the central one equal to one.  This is the starting point of the local analysis: the function is the
central term times a series whose coefficients are all bounded by one. -/

/-- **Every term is dominated by the central term.** -/
theorem term_le_central_term (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (n : ℕ) :
    ‖a n‖ * r ^ n ≤ ‖a (centralIndex a r)‖ * r ^ centralIndex a r := by
  rw [term_centralIndex_eq ha hr hn₀]
  exact term_le_maxTerm ha hr n

/-- The same bound for the values on a circle of radius `r`. -/
theorem norm_term_le_norm_central_term (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ}
    (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) (n : ℕ) :
    ‖a n * z ^ n‖ ≤ ‖a (centralIndex a r) * z ^ centralIndex a r‖ := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, hz]
  exact term_le_central_term ha hr hn₀ n

/-- The central term is nonzero on a circle of positive radius. -/
theorem central_term_ne_zero (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {z : ℂ} (hz : ‖z‖ = r) :
    a (centralIndex a r) * z ^ centralIndex a r ≠ 0 := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact absurd hz.symm (ne_of_gt hr)
  exact mul_ne_zero (coeff_centralIndex_ne_zero ha hr hn₀) (pow_ne_zero _ hzne)

/-- **The normalised coefficients have modulus at most one**, and the central one is one. -/
theorem norm_normalised_coeff_le_one (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ}
    (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) (n : ℕ) :
    ‖a n * z ^ n / (a (centralIndex a r) * z ^ centralIndex a r)‖ ≤ 1 := by
  rw [norm_div, div_le_one (by
    have := central_term_ne_zero ha hr hn₀ hz
    positivity)]
  exact norm_term_le_norm_central_term ha hr hn₀ hz n

@[simp] theorem normalised_coeff_centralIndex (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ}
    (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) :
    a (centralIndex a r) * z ^ centralIndex a r / (a (centralIndex a r) * z ^ centralIndex a r)
      = 1 :=
  div_self (central_term_ne_zero ha hr hn₀ hz)


/-! ## Differentiating the majorant

The majorant `S(r) = sum ||a_n|| r^n` is differentiated term by term, exactly as the function itself
was.  The combination `r S'(r)` is the first moment of the modulus profile, which is the quantity the
logarithmic-derivative estimate still has to control. -/

/-- **Termwise differentiation of the majorant.** -/
theorem hasDerivAt_coeffSum (ha : EntireCoeffs a) (hr : 0 < r) :
    HasDerivAt (coeffSum a) (∑' n : ℕ, (n : ℝ) * ‖a n‖ * r ^ (n - 1)) r := by
  classical
  set R : ℝ := 2 * r with hRdef
  have hR0 : (0 : ℝ) < R := by rw [hRdef]; linarith
  have hpow : ∀ n : ℕ, (n : ℝ) * R ^ (n - 1) = (1 / R) * ((n : ℝ) * R ^ n) := by
    intro n
    cases n with
    | zero => simp
    | succ m =>
        simp only [Nat.add_sub_cancel]
        field_simp
        ring
  have hidx : Summable fun n : ℕ => (n : ℝ) * (‖a n‖ * R ^ n) := by
    refine (summable_term (entireCoeffs_mul_index ha) hR0).congr fun n => ?_
    rw [norm_mul, Complex.norm_natCast, mul_assoc]
  have hu' : Summable fun n : ℕ => (1 / R) * ((n : ℝ) * (‖a n‖ * R ^ n)) := hidx.mul_left _
  have hu : Summable fun n : ℕ => ‖a n‖ * R ^ n := summable_term ha hR0
  refine hasDerivAt_of_tendstoLocallyUniformlyOn (l := (atTop : Filter (Finset ℕ)))
    (f := fun t (x : ℝ) => ∑ n ∈ t, ‖a n‖ * x ^ n)
    (f' := fun t (x : ℝ) => ∑ n ∈ t, (n : ℝ) * ‖a n‖ * x ^ (n - 1))
    (g := coeffSum a)
    (g' := fun x : ℝ => ∑' n : ℕ, (n : ℝ) * ‖a n‖ * x ^ (n - 1))
    (s := Set.Ioo (r / 2) R) isOpen_Ioo ?_ ?_ ?_ (by constructor <;> [linarith; linarith])
  · refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
    refine tendstoUniformlyOn_tsum hu' fun n x hx => ?_
    have hx0 : (0 : ℝ) < x := by linarith [hx.1, hr]
    have hxR : x ≤ R := le_of_lt hx.2
    have hbase : (n : ℝ) * ‖a n‖ * x ^ (n - 1) ≤ (n : ℝ) * ‖a n‖ * R ^ (n - 1) := by
      gcongr
    calc ‖(n : ℝ) * ‖a n‖ * x ^ (n - 1)‖ = (n : ℝ) * ‖a n‖ * x ^ (n - 1) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (n : ℝ) * ‖a n‖ * R ^ (n - 1) := hbase
      _ = (1 / R) * ((n : ℝ) * (‖a n‖ * R ^ n)) := by
          rw [show (n : ℝ) * ‖a n‖ * R ^ (n - 1) = ‖a n‖ * ((n : ℝ) * R ^ (n - 1)) by ring,
            hpow n]
          ring
  · refine Filter.Eventually.of_forall fun t x _ => ?_
    have hterm : ∀ n : ℕ, HasDerivAt (fun y : ℝ => ‖a n‖ * y ^ n)
        ((n : ℝ) * ‖a n‖ * x ^ (n - 1)) x := by
      intro n
      have h := (hasDerivAt_pow n x).const_mul ‖a n‖
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    exact HasDerivAt.fun_sum fun n _ => hterm n
  · intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1, hr]
    have hxR : x ≤ R := le_of_lt hx.2
    have hsummable : Summable fun n : ℕ => ‖a n‖ * x ^ n := by
      refine Summable.of_nonneg_of_le (fun n => term_nonneg a hx0 n) (fun n => ?_) hu
      gcongr
    exact hsummable.hasSum


/-- The index-weighted majorant, `r S'(r) = sum n ||a_n|| r^n`. -/
theorem mul_deriv_coeffSum_eq (r : ℝ) :
    r * (∑' n : ℕ, (n : ℝ) * ‖a n‖ * r ^ (n - 1))
      = ∑' n : ℕ, (n : ℝ) * (‖a n‖ * r ^ n) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  cases n with
  | zero => simp
  | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      ring

/-- **The first moment of the modulus profile.**  The deviation of the index from any fixed centre,
weighted by the terms, is the index-weighted majorant minus the centre times the majorant. -/
theorem tsum_index_sub_mul_term (ha : EntireCoeffs a) (hr : 0 < r) (k : ℕ) :
    ∑' n : ℕ, ((n : ℝ) - (k : ℝ)) * (‖a n‖ * r ^ n)
      = (∑' n : ℕ, (n : ℝ) * (‖a n‖ * r ^ n)) - (k : ℝ) * coeffSum a r := by
  have hidx : Summable fun n : ℕ => (n : ℝ) * (‖a n‖ * r ^ n) := by
    refine (summable_term (entireCoeffs_mul_index ha) hr).congr fun n => ?_
    rw [norm_mul, Complex.norm_natCast, mul_assoc]
  have hbase : Summable fun n : ℕ => (k : ℝ) * (‖a n‖ * r ^ n) :=
    (summable_term ha hr).mul_left _
  rw [coeffSum, ← tsum_mul_left, ← Summable.tsum_sub hidx hbase]
  exact tsum_congr fun n => by ring


set_option maxHeartbeats 400000 in
/-- **The weighted lower tail, sharply.**  Below the central index at the smaller radius, splitting
the index deviation as `(nu(r) - nu(t)) + (nu(t) - n)` costs the window half-width times the
geometric tail, plus a constant depending only on the radius ratio -- in place of the crude factor
`nu(r)`. -/
theorem sum_lower_tail_weighted_le
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑ n ∈ Finset.range (centralIndex a t),
        |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n)
      ≤ maxTerm a r * (((centralIndex a r : ℝ) - (centralIndex a t : ℝ)) * ((t / r) / (1 - t / r))
          + ∑' j : ℕ, ((1 : ℝ) + j) * (t / r) ^ (j + 1)) := by
  classical
  have hr : 0 < r := lt_trans ht htr
  set k := centralIndex a t with hk
  set q : ℝ := t / r with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hr]
    exact htr
  have hμ : (0 : ℝ) ≤ maxTerm a r :=
    le_trans (term_nonneg a hr 0) (term_le_maxTerm ha hr 0)
  have hkr : (k : ℝ) ≤ (centralIndex a r : ℝ) := by
    exact_mod_cast centralIndex_mono ha ht htr.le hn₀
  have hgeom : Summable fun j : ℕ => ((1 : ℝ) + j) * q ^ (j + 1) := by
    have h1 : Summable fun j : ℕ => (j : ℝ) * q ^ j := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    have h2 : Summable fun j : ℕ => q ^ j := summable_geometric_of_lt_one hq0.le hq1
    have h3 : Summable fun j : ℕ => ((1 : ℝ) + j) * q ^ j := by
      refine (h2.add h1).congr fun j => ?_
      ring
    simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using h3.mul_right q
  -- termwise
  have hpt : ∀ n ∈ Finset.range k,
      |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n)
        ≤ maxTerm a r * ((((centralIndex a r : ℝ) - (k : ℝ)) + ((k - n : ℕ) : ℝ)) * q ^ (k - n)) := by
    intro n hn
    have hnk : n < k := Finset.mem_range.mp hn
    have hdecay := term_le_maxTerm_mul_pow_of_le_centralIndex ha ht htr.le hn₀
      (n := n) (by omega)
    rw [← hk, ← hq] at hdecay
    have hidx : |(n : ℝ) - (centralIndex a r : ℝ)|
        ≤ ((centralIndex a r : ℝ) - (k : ℝ)) + ((k - n : ℕ) : ℝ) := by
      have hcast : ((k - n : ℕ) : ℝ) = (k : ℝ) - (n : ℝ) := by
        have : n ≤ k := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      have hnr : (n : ℝ) ≤ (centralIndex a r : ℝ) := by
        have : n ≤ centralIndex a r := by
          have := centralIndex_mono ha ht htr.le hn₀
          omega
        exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]
      linarith
    calc |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n)
        ≤ (((centralIndex a r : ℝ) - (k : ℝ)) + ((k - n : ℕ) : ℝ)) * (‖a n‖ * r ^ n) :=
          mul_le_mul_of_nonneg_right hidx (term_nonneg a hr n)
      _ ≤ (((centralIndex a r : ℝ) - (k : ℝ)) + ((k - n : ℕ) : ℝ))
          * (maxTerm a r * q ^ (k - n)) := by
          refine mul_le_mul_of_nonneg_left hdecay (by
            have : (0 : ℝ) ≤ ((k - n : ℕ) : ℝ) := Nat.cast_nonneg _
            linarith)
      _ = maxTerm a r * ((((centralIndex a r : ℝ) - (k : ℝ)) + ((k - n : ℕ) : ℝ)) * q ^ (k - n)) := by
          ring
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hμ
  -- reindex and split
  have hreflect : ∑ n ∈ Finset.range k,
      (((centralIndex a r : ℝ) - (k : ℝ)) + ((k - n : ℕ) : ℝ)) * q ^ (k - n)
      = ∑ j ∈ Finset.range k,
        (((centralIndex a r : ℝ) - (k : ℝ)) + ((j : ℝ) + 1)) * q ^ (j + 1) := by
    have h := Finset.sum_range_reflect
      (fun j : ℕ => (((centralIndex a r : ℝ) - (k : ℝ)) + ((j : ℝ) + 1)) * q ^ (j + 1)) k
    rw [← h]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk := Finset.mem_range.mp hj
    have h1 : k - 1 - j + 1 = k - j := by omega
    have h2 : ((k - j : ℕ) : ℝ) = ((k - 1 - j : ℕ) : ℝ) + 1 := by
      have : k - j = (k - 1 - j) + 1 := by omega
      rw [this]
      push_cast
      ring
    rw [h1, h2]
  rw [hreflect]
  have hsplit : ∀ j : ℕ,
      (((centralIndex a r : ℝ) - (k : ℝ)) + ((j : ℝ) + 1)) * q ^ (j + 1)
      = ((centralIndex a r : ℝ) - (k : ℝ)) * q ^ (j + 1) + ((1 : ℝ) + j) * q ^ (j + 1) := by
    intro j; ring
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hA : ∑ j ∈ Finset.range k, q ^ (j + 1) ≤ q / (1 - q) := by
    have hfac : ∑ j ∈ Finset.range k, q ^ (j + 1) = q * ∑ j ∈ Finset.range k, q ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_succ, mul_comm]
    have hsum : ∑ j ∈ Finset.range k, q ^ j ≤ (1 - q)⁻¹ := by
      have hb := Summable.sum_le_tsum (Finset.range k) (fun j _ => pow_nonneg hq0.le j)
        (summable_geometric_of_lt_one hq0.le hq1)
      rwa [tsum_geometric_of_lt_one hq0.le hq1] at hb
    rw [hfac, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hsum hq0.le
  have hB : ∑ j ∈ Finset.range k, ((1 : ℝ) + j) * q ^ (j + 1)
      ≤ ∑' j : ℕ, ((1 : ℝ) + j) * q ^ (j + 1) :=
    Summable.sum_le_tsum _ (fun j _ => by positivity) hgeom
  have hcoef : (0 : ℝ) ≤ (centralIndex a r : ℝ) - (k : ℝ) := by linarith
  exact add_le_add (mul_le_mul_of_nonneg_left hA hcoef) hB


/-- Summability of the weighted geometric series. -/
private theorem summable_one_add_mul_geom {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun j : ℕ => ((1 : ℝ) + j) * q ^ (j + 1) := by
  have h1 : Summable fun j : ℕ => (j : ℝ) * q ^ j := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
  have h2 : Summable fun j : ℕ => q ^ j := summable_geometric_of_lt_one hq0.le hq1
  have h3 : Summable fun j : ℕ => ((1 : ℝ) + j) * q ^ j := by
    refine (h2.add h1).congr fun j => ?_
    ring
  simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using h3.mul_right q

set_option maxHeartbeats 400000 in
/-- **The sharp upper tail.**  Beyond the central index at the larger radius `s` the weight
`|n - nu(r)|` splits as `(nu(s) - nu(r))` plus the distance past `nu(s)`, so the geometric decay
absorbs the second piece entirely and only the window half-width survives as a linear factor. -/
theorem tsum_upper_tail_weighted_le
    (ha : EntireCoeffs a) (hr : 0 < r) (hrs : r < s) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑' j : ℕ, |((j + (centralIndex a s + 1) : ℕ) : ℝ) - (centralIndex a r : ℝ)|
        * (‖a (j + (centralIndex a s + 1))‖ * r ^ (j + (centralIndex a s + 1)))
      ≤ maxTerm a r * (((centralIndex a s : ℝ) - (centralIndex a r : ℝ))
            * ((r / s) / (1 - r / s))
          + ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) := by
  have hs : 0 < s := lt_trans hr hrs
  set k := centralIndex a s with hk
  set v := centralIndex a r with hv
  have hvk : v ≤ k := centralIndex_mono ha hr hrs.le hn₀
  set q : ℝ := r / s with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hs]; exact hrs
  have hgeom : Summable fun j : ℕ => q ^ (j + 1) :=
    ((summable_geometric_of_lt_one hq0.le hq1).mul_right q).congr fun j => by
      rw [pow_succ]
  have hgw : Summable fun j : ℕ => ((1 : ℝ) + j) * q ^ (j + 1) :=
    summable_one_add_mul_geom hq0 hq1
  have hgeomval : ∑' j : ℕ, q ^ (j + 1) = q / (1 - q) := by
    have h : ∑' j : ℕ, q ^ (j + 1) = (∑' j : ℕ, q ^ j) * q := by
      rw [← tsum_mul_right]
      exact tsum_congr fun j => by rw [pow_succ]
    rw [h, tsum_geometric_of_lt_one hq0.le hq1]
    field_simp
  have hkv : (0 : ℝ) ≤ (k : ℝ) - (v : ℝ) := by
    have : (v : ℝ) ≤ (k : ℝ) := by exact_mod_cast hvk
    linarith
  have hpt : ∀ j : ℕ, |((j + (k + 1) : ℕ) : ℝ) - (v : ℝ)|
      * (‖a (j + (k + 1))‖ * r ^ (j + (k + 1)))
      ≤ maxTerm a r * (((k : ℝ) - (v : ℝ)) * q ^ (j + 1) + ((1 : ℝ) + j) * q ^ (j + 1)) := by
    intro j
    have hdecay := term_le_maxTerm_mul_pow_of_centralIndex_le ha hr hrs.le hn₀
      (n := j + (k + 1)) (by omega)
    rw [← hk, show j + (k + 1) - k = j + 1 by omega, ← hq] at hdecay
    have hidx : |((j + (k + 1) : ℕ) : ℝ) - (v : ℝ)| = ((k : ℝ) - (v : ℝ)) + ((1 : ℝ) + j) := by
      have hcast : ((j + (k + 1) : ℕ) : ℝ) = (j : ℝ) + ((k : ℝ) + 1) := by push_cast; ring
      rw [hcast, abs_of_nonneg (by have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j; linarith)]
      ring
    rw [hidx]
    calc (((k : ℝ) - (v : ℝ)) + ((1 : ℝ) + j)) * (‖a (j + (k + 1))‖ * r ^ (j + (k + 1)))
        ≤ (((k : ℝ) - (v : ℝ)) + ((1 : ℝ) + j)) * (maxTerm a r * q ^ (j + 1)) := by
          refine mul_le_mul_of_nonneg_left hdecay ?_
          have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
          linarith
      _ = maxTerm a r * (((k : ℝ) - (v : ℝ)) * q ^ (j + 1) + ((1 : ℝ) + j) * q ^ (j + 1)) := by
          ring
  have hsumL : Summable fun j : ℕ => |((j + (k + 1) : ℕ) : ℝ) - (v : ℝ)|
      * (‖a (j + (k + 1))‖ * r ^ (j + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).mpr (summable_index_deviation ha hr v)
  have hsumR : Summable fun j : ℕ =>
      maxTerm a r * (((k : ℝ) - (v : ℝ)) * q ^ (j + 1) + ((1 : ℝ) + j) * q ^ (j + 1)) :=
    ((hgeom.mul_left _).add hgw).mul_left _
  have hle := Summable.tsum_le_tsum hpt hsumL hsumR
  refine le_trans hle (le_of_eq ?_)
  rw [tsum_mul_left, Summable.tsum_add (hgeom.mul_left _) hgw, tsum_mul_left, hgeomval]

set_option maxHeartbeats 400000 in
/-- **The sharp deviation estimate.**  The same three-way split as the coarse bound, but with both
tails weighted: on each side the factor `nu(r)` is replaced by the corresponding window half-width,
so the whole remainder is proportional to the spread of the central index across `[t, s]` rather than
to its size. -/
theorem tsum_index_deviation_le_sharp
    (ha : EntireCoeffs a) (ht : 0 < t) (htr : t < r) (hrs : r < s)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)| * (‖a n‖ * r ^ n)
      ≤ maxTerm a r * (((centralIndex a s : ℝ) - (centralIndex a t : ℝ))
            * ((centralIndex a s + 1 - centralIndex a t : ℕ) : ℝ))
        + maxTerm a r * (((centralIndex a r : ℝ) - (centralIndex a t : ℝ))
              * ((t / r) / (1 - t / r))
            + ∑' j : ℕ, ((1 : ℝ) + j) * (t / r) ^ (j + 1))
        + maxTerm a r * (((centralIndex a s : ℝ) - (centralIndex a r : ℝ))
              * ((r / s) / (1 - r / s))
            + ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) := by
  classical
  have hr : 0 < r := lt_trans ht htr
  have hs : 0 < s := lt_trans hr hrs
  set k := centralIndex a s with hk
  set m := centralIndex a t with hm
  set v := centralIndex a r with hv
  have hmv : m ≤ v := centralIndex_mono ha ht htr.le hn₀
  have hvk : v ≤ k := centralIndex_mono ha hr hrs.le hn₀
  set D : ℕ → ℝ := fun n => |(n : ℝ) - (v : ℝ)| * (‖a n‖ * r ^ n) with hD
  have hDsum : Summable D := summable_index_deviation ha hr v
  have hsplit := Summable.sum_add_tsum_nat_add (f := D) (k + 1) hDsum
  have hcons : (∑ n ∈ Finset.Ico 0 m, D n) + ∑ n ∈ Finset.Ico m (k + 1), D n
      = ∑ n ∈ Finset.Ico 0 (k + 1), D n :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  have hlow : ∑ n ∈ Finset.Ico 0 m, D n
      ≤ maxTerm a r * (((v : ℝ) - (m : ℝ)) * ((t / r) / (1 - t / r))
          + ∑' j : ℕ, ((1 : ℝ) + j) * (t / r) ^ (j + 1)) := by
    have h := sum_lower_tail_weighted_le ha ht htr hn₀
    rw [Finset.range_eq_Ico, ← hm, ← hv] at h
    exact h
  have hwin : ∑ n ∈ Finset.Ico m (k + 1), D n
      ≤ maxTerm a r * (((k : ℝ) - (m : ℝ)) * ((k + 1 - m : ℕ) : ℝ)) := by
    have hstep := sum_window_index_deviation_le ha ht htr hrs hn₀
    rw [← hk, ← hm, ← hv] at hstep
    refine le_trans hstep ?_
    have hcount : ∑ n ∈ Finset.Ico m (k + 1), ‖a n‖ * r ^ n
        ≤ ((k + 1 - m : ℕ) : ℝ) * maxTerm a r := by
      have hcard : (Finset.Ico m (k + 1)).card = k + 1 - m := Nat.card_Ico m (k + 1)
      have hbd : ∀ n ∈ Finset.Ico m (k + 1), ‖a n‖ * r ^ n ≤ maxTerm a r :=
        fun n _ => term_le_maxTerm ha hr n
      have h := Finset.sum_le_card_nsmul (Finset.Ico m (k + 1))
        (fun n => ‖a n‖ * r ^ n) (maxTerm a r) hbd
      rwa [hcard, nsmul_eq_mul] at h
    have hkm : (0 : ℝ) ≤ (k : ℝ) - (m : ℝ) := by
      have : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hmv hvk
      linarith
    calc ((k : ℝ) - (m : ℝ)) * ∑ n ∈ Finset.Ico m (k + 1), ‖a n‖ * r ^ n
        ≤ ((k : ℝ) - (m : ℝ)) * (((k + 1 - m : ℕ) : ℝ) * maxTerm a r) :=
          mul_le_mul_of_nonneg_left hcount hkm
      _ = maxTerm a r * (((k : ℝ) - (m : ℝ)) * ((k + 1 - m : ℕ) : ℝ)) := by ring
  have hup : ∑' j : ℕ, D (j + (k + 1))
      ≤ maxTerm a r * (((k : ℝ) - (v : ℝ)) * ((r / s) / (1 - r / s))
          + ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) := by
    have h := tsum_upper_tail_weighted_le ha hr hrs hn₀
    rw [← hk, ← hv] at h
    exact h
  calc ∑' n : ℕ, D n
      = (∑ n ∈ Finset.Ico 0 (k + 1), D n) + ∑' j : ℕ, D (j + (k + 1)) := by
        rw [← hsplit, Finset.range_eq_Ico]
    _ = (∑ n ∈ Finset.Ico 0 m, D n) + (∑ n ∈ Finset.Ico m (k + 1), D n)
        + ∑' j : ℕ, D (j + (k + 1)) := by rw [hcons]
    _ ≤ maxTerm a r * (((v : ℝ) - (m : ℝ)) * ((t / r) / (1 - t / r))
          + ∑' j : ℕ, ((1 : ℝ) + j) * (t / r) ^ (j + 1))
        + maxTerm a r * (((k : ℝ) - (m : ℝ)) * ((k + 1 - m : ℕ) : ℝ))
        + maxTerm a r * (((k : ℝ) - (v : ℝ)) * ((r / s) / (1 - r / s))
          + ∑' j : ℕ, ((1 : ℝ) + j) * (r / s) ^ (j + 1)) := by gcongr
    _ = _ := by ring


end GaloisForLFunctions.HTGeometry
