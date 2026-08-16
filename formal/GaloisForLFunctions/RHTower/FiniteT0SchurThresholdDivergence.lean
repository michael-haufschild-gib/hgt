import Mathlib

/-!
# No finite zeroth moment repairs the unshifted tower

Let `y : ι → (0, R]` be an infinite family of atoms with summable first moment — a compact
reciprocal Stieltjes model of infinite total mass and finite positive moments.  Then no finite value
`a` of the zeroth moment makes the unshifted Hankel tower positive semidefinite at all orders.

The obstruction is a single telescoping test.  The polynomials

`Q_n(t) = R⁻¹ ∑_{j<n} (1 - t/R)^j`,  so  `t·Q_n(t) = 1 - (1 - t/R)^n`,

have `0 ≤ t Q_n(t) ≤ 1` on `[0,R]`, `t Q_n(t) ≤ n t / R`, and `t Q_n(t) → 1` for every `t > 0`.
Positivity of the quadratic form at the pair `(c₀, Q_n) = (-1, Q_n)` gives

`∑ᵢ t Q_n(t) ≤ a`

for every `n`, while the left side diverges because the family is infinite.

## Main results

* `eval_telescope` — the telescoping identity `t Q_n(t) = 1 - (1 - t/R)^n`;
* `summable_telescopeValue` — the test values are summable;
* `tendsto_tsum_telescopeValue_atTop` — their sums diverge;
* `not_forall_regularizedUnshiftedForm_nonneg` — hence no finite zeroth moment works;
* `schurThreshold_unbounded` — equivalently the Schur thresholds are unbounded.
-/

noncomputable section

namespace RHTower

open scoped BigOperators

/-! ### The telescoping test polynomials -/

/-- The `n`-th telescoping test polynomial, characterized by `t · Q_n(t) = 1 - (1 - t/R)^n`. -/
def telescopeTest (R : ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.C R⁻¹ * ∑ j ∈ Finset.range n, (1 - Polynomial.C R⁻¹ * Polynomial.X) ^ j

/-- The value of the telescoping test after multiplying by the coordinate. -/
def telescopeValue (R : ℝ) (n : ℕ) (t : ℝ) : ℝ := 1 - (1 - t / R) ^ n

theorem eval_telescope (R : ℝ) (n : ℕ) (t : ℝ) :
    t * (telescopeTest R n).eval t = telescopeValue R n t := by
  have hgeom : (∑ j ∈ Finset.range n, (1 - t / R) ^ j) * ((1 - t / R) - 1)
      = (1 - t / R) ^ n - 1 := geom_sum_mul _ n
  have hstep : ((1 - t / R) - 1) = -(t / R) := by ring
  rw [hstep] at hgeom
  rw [telescopeTest, telescopeValue]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  have hinv : R⁻¹ * t = t / R := by
    rw [div_eq_inv_mul]
  have hkey : t * (R⁻¹ * ∑ j ∈ Finset.range n, (1 - R⁻¹ * t) ^ j)
      = (t / R) * ∑ j ∈ Finset.range n, (1 - t / R) ^ j := by
    rw [← hinv]
    ring
  rw [hkey]
  have : (t / R) * ∑ j ∈ Finset.range n, (1 - t / R) ^ j
      = -((∑ j ∈ Finset.range n, (1 - t / R) ^ j) * (-(t / R))) := by ring
  rw [this, hgeom]
  ring

theorem telescopeValue_nonneg {R t : ℝ} (hR : 0 < R) (ht0 : 0 ≤ t) (htR : t ≤ R) (n : ℕ) :
    0 ≤ telescopeValue R n t := by
  have h1 : 0 ≤ 1 - t / R := by
    have : t / R ≤ 1 := by rw [div_le_one hR]; exact htR
    linarith
  have h2 : (1 - t / R) ^ n ≤ 1 := pow_le_one₀ h1 (by
    have : 0 ≤ t / R := by positivity
    linarith)
  rw [telescopeValue]
  linarith

theorem telescopeValue_le_one {R t : ℝ} (hR : 0 < R) (htR : t ≤ R) (n : ℕ) :
    telescopeValue R n t ≤ 1 := by
  have h1 : 0 ≤ 1 - t / R := by
    have : t / R ≤ 1 := by rw [div_le_one hR]; exact htR
    linarith
  have : 0 ≤ (1 - t / R) ^ n := pow_nonneg h1 n
  rw [telescopeValue]
  linarith

/-- Bernoulli's inequality bounds the test by a multiple of the coordinate. -/
theorem telescopeValue_le_mul {R t : ℝ} (hR : 0 < R) (htR : t ≤ R) (n : ℕ) :
    telescopeValue R n t ≤ (n : ℝ) / R * t := by
  have hx : (-2 : ℝ) ≤ -(t / R) := by
    have : t / R ≤ 1 := by rw [div_le_one hR]; exact htR
    linarith
  have hb := one_add_mul_le_pow hx n
  have hrw : (1 : ℝ) + -(t / R) = 1 - t / R := by ring
  rw [hrw] at hb
  rw [telescopeValue]
  have : (n : ℝ) / R * t = (n : ℝ) * (t / R) := by
    field_simp
  rw [this]
  linarith

theorem tendsto_telescopeValue {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (htR : t ≤ R) :
    Filter.Tendsto (fun n : ℕ => telescopeValue R n t) Filter.atTop (nhds 1) := by
  have habs : |1 - t / R| < 1 := by
    have h1 : 0 < t / R := by positivity
    have h2 : t / R ≤ 1 := by rw [div_le_one hR]; exact htR
    rw [abs_lt]
    constructor <;> linarith
  have hpow : Filter.Tendsto (fun n : ℕ => (1 - t / R) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs
  have := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℕ))).sub hpow
  simpa [telescopeValue] using this

/-! ### The divergence of the test sums -/

variable {ι : Type*} {y : ι → ℝ} {R : ℝ}

theorem summable_telescopeValue (hR : 0 < R) (hy0 : ∀ i, 0 ≤ y i) (hyR : ∀ i, y i ≤ R)
    (hsum : Summable y) (n : ℕ) : Summable (fun i => telescopeValue R n (y i)) := by
  refine Summable.of_nonneg_of_le (fun i => telescopeValue_nonneg hR (hy0 i) (hyR i) n)
    (fun i => telescopeValue_le_mul hR (hyR i) n) ?_
  exact hsum.mul_left _

/-- **The test sums diverge.**  Infinite total mass makes every finite bound eventually fail. -/
theorem exists_tsum_telescopeValue_gt [Infinite ι] (hR : 0 < R) (hy : ∀ i, 0 < y i)
    (hyR : ∀ i, y i ≤ R) (hsum : Summable y) (M : ℝ) :
    ∃ n : ℕ, M < ∑' i, telescopeValue R n (y i) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (max M 0 + 1)
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ι N
  have hpos : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    linarith
  set eps : ℝ := (max M 0 + 1) / N with heps
  have heps1 : eps < 1 := by
    rw [heps, div_lt_one hpos]
    exact hN
  -- choose `n` making every selected test value exceed `eps`
  have hchoice : ∀ i ∈ s, ∃ n₀ : ℕ, ∀ n ≥ n₀, eps < telescopeValue R n (y i) := by
    intro i _
    have h := tendsto_telescopeValue hR (hy i) (hyR i)
    have := h.eventually (eventually_gt_nhds heps1)
    exact this.exists_forall_of_atTop
  choose n₀ hn₀ using hchoice
  set n : ℕ := s.attach.sup (fun i => n₀ i.1 i.2) with hn
  refine ⟨n, ?_⟩
  have hsummable := summable_telescopeValue hR (fun i => (hy i).le) hyR hsum n
  have hlow : (s.card : ℝ) * eps ≤ ∑ i ∈ s, telescopeValue R n (y i) := by
    have hstep : ∑ _i ∈ s, eps ≤ ∑ i ∈ s, telescopeValue R n (y i) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      refine le_of_lt (hn₀ i hi n ?_)
      exact Finset.le_sup (f := fun i : {x // x ∈ s} => n₀ i.1 i.2) (Finset.mem_attach s ⟨i, hi⟩)
    simpa [Finset.sum_const, nsmul_eq_mul] using hstep
  have hpart : ∑ i ∈ s, telescopeValue R n (y i) ≤ ∑' i, telescopeValue R n (y i) :=
    hsummable.sum_le_tsum s (fun i _ => telescopeValue_nonneg hR (hy i).le (hyR i) n)
  have hcard : (s.card : ℝ) = (N : ℝ) := by rw [hs]
  rw [hcard] at hlow
  have hval : (N : ℝ) * eps = max M 0 + 1 := by
    rw [heps]
    field_simp
  rw [hval] at hlow
  have : M ≤ max M 0 := le_max_left _ _
  linarith

/-! ### No finite zeroth moment -/

/-- The regularized unshifted quadratic form: the zeroth moment is replaced by the finite part `a`,
and the remaining moments come from the atoms. -/
def regularizedUnshiftedForm (y : ι → ℝ) (a : ℝ) (c : ℝ) (Q : Polynomial ℝ) : ℝ :=
  c ^ 2 * a + 2 * c * (∑' i, y i * Q.eval (y i)) + ∑' i, (y i * Q.eval (y i)) ^ 2

/-- **No finite zeroth moment repairs the unshifted tower.** -/
theorem not_forall_regularizedUnshiftedForm_nonneg [Infinite ι] (hR : 0 < R)
    (hy : ∀ i, 0 < y i) (hyR : ∀ i, y i ≤ R) (hsum : Summable y) (a : ℝ)
    (hnn : ∀ (c : ℝ) (Q : Polynomial ℝ), 0 ≤ regularizedUnshiftedForm y a c Q) : False := by
  obtain ⟨n, hn⟩ := exists_tsum_telescopeValue_gt hR hy hyR hsum a
  have hval : ∀ i, y i * (telescopeTest R n).eval (y i) = telescopeValue R n (y i) :=
    fun i => eval_telescope R n (y i)
  have hsummable := summable_telescopeValue hR (fun i => (hy i).le) hyR hsum n
  have hsq : Summable (fun i => (telescopeValue R n (y i)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hsummable
    have h0 := telescopeValue_nonneg hR (hy i).le (hyR i) n
    have h1 := telescopeValue_le_one hR (hyR i) n
    nlinarith
  have hsqle : (∑' i, (telescopeValue R n (y i)) ^ 2) ≤ ∑' i, telescopeValue R n (y i) := by
    refine hsq.tsum_le_tsum (fun i => ?_) hsummable
    have h0 := telescopeValue_nonneg hR (hy i).le (hyR i) n
    have h1 := telescopeValue_le_one hR (hyR i) n
    nlinarith
  have hform := hnn (-1) (telescopeTest R n)
  rw [regularizedUnshiftedForm] at hform
  have hA : (∑' i, y i * (telescopeTest R n).eval (y i)) = ∑' i, telescopeValue R n (y i) :=
    tsum_congr hval
  have hB : (∑' i, (y i * (telescopeTest R n).eval (y i)) ^ 2)
      = ∑' i, (telescopeValue R n (y i)) ^ 2 :=
    tsum_congr (fun i => by rw [hval i])
  rw [hA, hB] at hform
  simp only [neg_one_sq, one_mul, mul_neg, mul_one] at hform
  linarith


/-! ### The Hankel tower -/

/-- The unshifted moment tower with a chosen finite part for the zeroth moment. -/
def unshiftedTower (y : ι → ℝ) (a : ℝ) : ℕ → ℝ
  | 0 => a
  | (k + 1) => ∑' i, (y i) ^ (k + 1)

/-- The Hankel quadratic form of the tower at a polynomial's coefficient vector. -/
def hankelForm (y : ι → ℝ) (a : ℝ) (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), ∑ j ∈ Finset.range (p.natDegree + 1),
    p.coeff i * p.coeff j * unshiftedTower y a (i + j)

theorem summable_pow_of_pos (hy0 : ∀ i, 0 ≤ y i) (hyR : ∀ i, y i ≤ R)
    (hsum : Summable y) {k : ℕ} (hk : 1 ≤ k) : Summable (fun i => (y i) ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine Summable.of_nonneg_of_le (fun i => pow_nonneg (hy0 i) _) (fun i => ?_)
    ((hsum.mul_left (R ^ m)))
  calc (y i) ^ (m + 1) = (y i) ^ m * y i := by ring
    _ ≤ R ^ m * y i := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hy0 i) (hyR i) m) (hy0 i)

/-- **The Hankel form in the split coordinates.**  Separating the zeroth coefficient turns the
Hankel quadratic form into the regularized unshifted form. -/
theorem hankelForm_eq_regularized (hy0 : ∀ i, 0 ≤ y i) (hyR : ∀ i, y i ≤ R)
    (hsum : Summable y) (a : ℝ) (p : Polynomial ℝ) :
    hankelForm y a p = regularizedUnshiftedForm y a (p.coeff 0) p.divX := by
  classical
  set d : ℕ := p.natDegree with hd
  have hdivX : ∀ t : ℝ, t * p.divX.eval t = ∑ i ∈ Finset.range d, p.coeff (i + 1) * t ^ (i + 1) := by
    intro t
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · have hdeg : p.divX = 0 := by
        refine Polynomial.divX_eq_zero_iff.mpr ?_
        exact Polynomial.eq_C_of_natDegree_eq_zero (by omega)
      rw [hdeg, hd0]
      simp
    · have hlt : p.divX.natDegree < d := by
        have hle : p.divX.natDegree ≤ d - 1 := by
          refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => ?_)
          rw [Polynomial.coeff_divX]
          refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
          omega
        omega
      rw [Polynomial.eval_eq_sum_range' hlt, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Polynomial.coeff_divX]
      ring
  have hsumA : Summable (fun i => y i * p.divX.eval (y i)) := by
    have : ∀ i, y i * p.divX.eval (y i)
        = ∑ k ∈ Finset.range d, p.coeff (k + 1) * (y i) ^ (k + 1) := fun i => hdivX (y i)
    refine Summable.congr ?_ (fun i => (this i).symm)
    refine summable_sum (fun k _ => ?_)
    exact (summable_pow_of_pos hy0 hyR hsum (by omega)).mul_left _
  have hexpand : ∀ i : ι, (y i * p.divX.eval (y i)) ^ 2
      = ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d,
          p.coeff (k + 1) * p.coeff (l + 1) * (y i) ^ (k + l + 2) := by
    intro i
    rw [hdivX (y i), pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hsumB : Summable (fun i => (y i * p.divX.eval (y i)) ^ 2) := by
    refine Summable.congr ?_ (fun i => (hexpand i).symm)
    refine summable_sum (fun k _ => summable_sum (fun l _ => ?_))
    exact (summable_pow_of_pos hy0 hyR hsum (by omega)).mul_left _
  -- expand the Hankel double sum
  rw [hankelForm, regularizedUnshiftedForm]
  rw [Finset.sum_range_succ' (fun i => ∑ j ∈ Finset.range (d + 1),
    p.coeff i * p.coeff j * unshiftedTower y a (i + j)) d]
  rw [Finset.sum_range_succ' (fun j => p.coeff 0 * p.coeff j * unshiftedTower y a (0 + j)) d]
  have hrow : ∀ i ∈ Finset.range d,
      (∑ j ∈ Finset.range (d + 1), p.coeff (i + 1) * p.coeff j * unshiftedTower y a (i + 1 + j))
        = (∑ j ∈ Finset.range d, p.coeff (i + 1) * p.coeff (j + 1)
              * unshiftedTower y a (i + j + 2))
          + p.coeff (i + 1) * p.coeff 0 * unshiftedTower y a (i + 1 + 0) := by
    intro i _
    rw [Finset.sum_range_succ' (fun j => p.coeff (i + 1) * p.coeff j
      * unshiftedTower y a (i + 1 + j)) d]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 2
    omega
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
  simp only [Nat.add_zero]
  -- identify the three surviving blocks
  have hA : (∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d,
      p.coeff (i + 1) * p.coeff (j + 1) * unshiftedTower y a (i + j + 2))
      = ∑' i, (y i * p.divX.eval (y i)) ^ 2 := by
    rw [tsum_congr hexpand]
    rw [Summable.tsum_finsetSum (fun k _ => summable_sum (fun l _ =>
      (summable_pow_of_pos hy0 hyR hsum (by omega)).mul_left _))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Summable.tsum_finsetSum (fun l _ =>
      (summable_pow_of_pos hy0 hyR hsum (by omega)).mul_left _)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [tsum_mul_left]
    rfl
  have hB : (∑ i ∈ Finset.range d, p.coeff (i + 1) * p.coeff 0 * unshiftedTower y a (i + 1))
      = p.coeff 0 * ∑' i, y i * p.divX.eval (y i) := by
    rw [tsum_congr (fun i => hdivX (y i))]
    rw [Summable.tsum_finsetSum (fun k _ =>
      (summable_pow_of_pos hy0 hyR hsum (by omega)).mul_left _)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [tsum_mul_left]
    show p.coeff (k + 1) * p.coeff 0 * (∑' i, (y i) ^ (k + 1)) = _
    ring
  have hC : (∑ j ∈ Finset.range d, p.coeff 0 * p.coeff (j + 1) * unshiftedTower y a (0 + (j + 1)))
      = p.coeff 0 * ∑' i, y i * p.divX.eval (y i) := by
    rw [← hB]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show (0 : ℕ) + (j + 1) = j + 1 from by omega]
    ring
  rw [hA, hC, hB]
  show _ = p.coeff 0 ^ 2 * a + 2 * p.coeff 0 * (∑' i, y i * p.divX.eval (y i))
    + ∑' i, (y i * p.divX.eval (y i)) ^ 2
  have hzero : p.coeff 0 * p.coeff 0 * unshiftedTower y a (0 + 0) = p.coeff 0 ^ 2 * a := by
    show p.coeff 0 * p.coeff 0 * a = _
    ring
  rw [hzero]
  ring

/-- **No finite zeroth moment makes the unshifted Hankel tower positive semidefinite.** -/
theorem not_forall_hankelForm_nonneg [Infinite ι] (hR : 0 < R) (hy : ∀ i, 0 < y i)
    (hyR : ∀ i, y i ≤ R) (hsum : Summable y) (a : ℝ)
    (hnn : ∀ p : Polynomial ℝ, 0 ≤ hankelForm y a p) : False := by
  refine not_forall_regularizedUnshiftedForm_nonneg hR hy hyR hsum a (fun c Q => ?_)
  have hp := hnn (Polynomial.C c + Polynomial.X * Q)
  rw [hankelForm_eq_regularized (fun i => (hy i).le) hyR hsum] at hp
  have hc0 : (Polynomial.C c + Polynomial.X * Q).coeff 0 = c := by
    simp
  have hdX : (Polynomial.C c + Polynomial.X * Q).divX = Q := by
    ext k
    rw [Polynomial.coeff_divX, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_X_mul]
    simp
  rw [hc0, hdX] at hp
  exact hp

/-- **The Schur thresholds are unbounded.**  Equivalently: for every finite `a` there is a test
polynomial whose Schur inequality fails. -/
theorem schurThreshold_unbounded [Infinite ι] (hR : 0 < R) (hy : ∀ i, 0 < y i)
    (hyR : ∀ i, y i ≤ R) (hsum : Summable y) (a : ℝ) :
    ∃ (c : ℝ) (Q : Polynomial ℝ), regularizedUnshiftedForm y a c Q < 0 := by
  by_contra hcon
  push Not at hcon
  exact not_forall_regularizedUnshiftedForm_nonneg hR hy hyR hsum a (fun c Q => hcon c Q)

end RHTower
