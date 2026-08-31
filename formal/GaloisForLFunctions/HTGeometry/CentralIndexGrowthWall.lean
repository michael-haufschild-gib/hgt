import GaloisForLFunctions.HTGeometry.CentralIndexDivergence

/-!
# The growth wall of the central index

The lower growth law `ν(r)·log(s/r) ≤ log μ(s) − log μ(r)` says that on the logarithmic radius
scale the function `φ(t) = log μ(eᵗ)` has all its difference quotients bounded below by the central
index.  If the central index is itself at least an exponential of `σ·φ`, the time needed for `φ` to
climb by one is at most `e^{−σ}` times the time the previous unit climb needed.  The total time is a
convergent geometric series, so `φ` exceeds every bound at a *finite* radius — impossible for an
entire function.

This is the growth wall that first-order algebraic differential equations run into: a relation
forcing `ν(r) ≳ μ(r)^σ` with `σ > 0` has no entire solution at all.
-/

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The logarithm of the maximum term, on the logarithmic radius scale. -/
noncomputable def logMaxTerm (a : ℕ → ℂ) (t : ℝ) : ℝ := Real.log (maxTerm a (Real.exp t))

theorem maxTerm_pos (ha : EntireCoeffs a) {r : ℝ} (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    0 < maxTerm a r :=
  (exists_maxTerm_eq ha hr hn₀).choose_spec.2

theorem logMaxTerm_mono (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {t s : ℝ} (hts : t ≤ s) :
    logMaxTerm a t ≤ logMaxTerm a s :=
  Real.log_le_log (maxTerm_pos ha (Real.exp_pos t) hn₀)
    (maxTerm_mono ha (Real.exp_pos t) (Real.exp_le_exp.mpr hts))

/-- **The lower growth law on the logarithmic scale.**  Every difference quotient of `φ` is at least
the central index at the left endpoint. -/
theorem centralIndex_mul_le_logMaxTerm_sub (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {t s : ℝ} (hts : t ≤ s) :
    (centralIndex a (Real.exp t) : ℝ) * (s - t) ≤ logMaxTerm a s - logMaxTerm a t := by
  have h := centralIndex_mul_log_le_log_maxTerm_sub ha (Real.exp_pos t)
    (Real.exp_le_exp.mpr hts) hn₀
  rwa [← Real.exp_sub, Real.log_exp] at h

/-- **The growth wall.**  No entire function has central index bounded below by a positive power of
its maximum term: the unit climbs of `log μ` take geometrically shrinking time, so `log μ` would be
infinite at a finite radius. -/
theorem false_of_centralIndex_ge_exp_mul_logMaxTerm (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {c σ t₀ : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hbd : ∀ t : ℝ, t₀ ≤ t →
      c * Real.exp (σ * logMaxTerm a t) ≤ (centralIndex a (Real.exp t) : ℝ)) :
    False := by
  set A : ℝ := logMaxTerm a t₀ with hA
  set q : ℝ := Real.exp (-σ) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  set K : ℝ := 1 / (c * Real.exp (σ * A)) with hK
  have hK0 : 0 < K := by
    rw [hK]
    positivity
  -- the marching times
  set u : ℕ → ℝ := fun n => t₀ + K * ∑ k ∈ Finset.range n, q ^ k with hu
  have hu0 : ∀ n : ℕ, t₀ ≤ u n := by
    intro n
    have hsum : 0 ≤ ∑ k ∈ Finset.range n, q ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg hq0.le k
    have : 0 ≤ K * ∑ k ∈ Finset.range n, q ^ k := mul_nonneg hK0.le hsum
    rw [hu]
    linarith
  -- one unit climb per marching step
  have hclimb : ∀ n : ℕ, A + (n : ℝ) ≤ logMaxTerm a (u n) := by
    intro n
    induction n with
    | zero => simp [hu, hA]
    | succ n ih =>
        have hune : u (n + 1) = u n + K * q ^ n := by
          rw [hu]
          simp only [Finset.sum_range_succ]
          ring
        have hstep : (centralIndex a (Real.exp (u n)) : ℝ) * (u (n + 1) - u n)
            ≤ logMaxTerm a (u (n + 1)) - logMaxTerm a (u n) := by
          refine centralIndex_mul_le_logMaxTerm_sub ha hn₀ ?_
          rw [hune]
          have : 0 ≤ K * q ^ n := mul_nonneg hK0.le (pow_nonneg hq0.le n)
          linarith
        have hnu : c * Real.exp (σ * logMaxTerm a (u n))
            ≤ (centralIndex a (Real.exp (u n)) : ℝ) := hbd (u n) (hu0 n)
        have hexp : Real.exp (σ * (A + n)) ≤ Real.exp (σ * logMaxTerm a (u n)) := by
          refine Real.exp_le_exp.mpr ?_
          exact mul_le_mul_of_nonneg_left ih hσ.le
        have hone : (1 : ℝ) ≤ (c * Real.exp (σ * logMaxTerm a (u n))) * (K * q ^ n) := by
          have hqn : q ^ n = Real.exp (-(σ * n)) := by
            rw [hq, ← Real.exp_nat_mul]
            ring_nf
          have hkey : (c * Real.exp (σ * (A + n))) * (K * q ^ n) = 1 := by
            rw [hqn, hK]
            rw [mul_add, Real.exp_add]
            field_simp
            rw [← Real.exp_add]
            ring_nf
            exact Real.exp_zero
          have hmono : (c * Real.exp (σ * (A + n))) * (K * q ^ n)
              ≤ (c * Real.exp (σ * logMaxTerm a (u n))) * (K * q ^ n) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hexp hc.le
          linarith [hkey, hmono]
        have hprod : (c * Real.exp (σ * logMaxTerm a (u n))) * (K * q ^ n)
            ≤ (centralIndex a (Real.exp (u n)) : ℝ) * (u (n + 1) - u n) := by
          rw [hune]
          have : u n + K * q ^ n - u n = K * q ^ n := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hnu (by positivity)
        push_cast
        linarith
  -- the marching times stay below a finite bound
  set T : ℝ := t₀ + K / (1 - q) with hT
  have hub : ∀ n : ℕ, u n ≤ T := by
    intro n
    have hgeom : ∑ k ∈ Finset.range n, q ^ k ≤ 1 / (1 - q) := by
      have hmul : (∑ k ∈ Finset.range n, q ^ k) * (q - 1) = q ^ n - 1 := geom_sum_mul q n
      have hpos : 0 < 1 - q := by linarith
      rw [le_div_iff₀ hpos]
      nlinarith [pow_nonneg hq0.le n]
    rw [hu, hT, div_eq_mul_one_div]
    have := mul_le_mul_of_nonneg_left hgeom hK0.le
    linarith
  -- but then `φ(T)` exceeds every bound
  obtain ⟨N, hN⟩ := exists_nat_gt (logMaxTerm a T - A)
  have hfin : A + (N : ℝ) ≤ logMaxTerm a T :=
    le_trans (hclimb N) (logMaxTerm_mono ha hn₀ (hub N))
  linarith

/-- **The growth wall, in the power form.**  No entire function satisfies `ν(r) ≥ c·μ(r)^σ` beyond
some radius, for any `c, σ > 0`. -/
theorem false_of_centralIndex_ge_rpow (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {c σ r₀ : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hr₀ : 0 < r₀)
    (hbd : ∀ r : ℝ, r₀ ≤ r → c * maxTerm a r ^ σ ≤ (centralIndex a r : ℝ)) : False := by
  refine false_of_centralIndex_ge_exp_mul_logMaxTerm ha hn₀ hc hσ (t₀ := Real.log r₀) ?_
  intro t ht
  have hrge : r₀ ≤ Real.exp t := by
    calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log hr₀).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ht
  have hrw : maxTerm a (Real.exp t) ^ σ = Real.exp (σ * logMaxTerm a t) := by
    rw [logMaxTerm, Real.rpow_def_of_pos (maxTerm_pos ha (Real.exp_pos t) hn₀)]
    ring_nf
  have h := hbd (Real.exp t) hrge
  rwa [hrw] at h

/-- **A bounded central index means a polynomial.**  If the central index stays below a fixed level
along a cofinal set of radii, all but finitely many Taylor coefficients vanish. -/
theorem exists_forall_coeff_eq_zero_of_centralIndex_le (ha : EntireCoeffs a) {N : ℝ}
    (hN : ∀ᶠ r in Filter.atTop, (centralIndex a r : ℝ) ≤ N) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → a n = 0 := by
  by_contra hcon
  push Not at hcon
  have htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0 := by
    intro M
    obtain ⟨n, hn, hne⟩ := hcon M
    exact ⟨n, hn, hne⟩
  have htop := tendsto_centralIndex_atTop ha htrans
  obtain ⟨M', hM'⟩ := exists_nat_gt N
  have h1 : ∀ᶠ r in Filter.atTop, M' + 1 ≤ centralIndex a r := htop.eventually_ge_atTop (M' + 1)
  obtain ⟨r, h2, h3⟩ := (h1.and hN).exists
  have hcast : ((M' + 1 : ℕ) : ℝ) ≤ (centralIndex a r : ℝ) := by exact_mod_cast h2
  push_cast at hcast
  linarith

end GaloisForLFunctions.HTGeometry
