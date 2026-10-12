import GaloisForLFunctions.RHTower.XiSliceHeatCoshCountermodel

/-!
# The sharp heat threshold of the cosh model is half the offset

Let `g(x) = (δ² − x²)² cosh(Lx)` be the slice of the cosh model (`coshModel`): a critical background of
zero density `L/2π` together with one off-line pair at offset `δ` at the height of the slice.  Heat
`λ = κ/L` turns `g` into `H = E[g(· + √λ Z)]` (`coshModelHeat`), whose Taylor coefficients at `0` are
`coshModelHeatCoeff δ L λ n`.

**Theorem.**  For `0 < κ` and `δ > 0`:

* if `2κ < δ`, then for all large `L` some even Taylor coefficient of `H` is negative
  (`exists_coshModelHeatCoeff_neg`), so `H` has no power series at `0` with nonnegative coefficients
  (`not_exists_nonneg_hasSum_coshModelHeat`);
* if `δ < 2κ`, then for all large `L` every Taylor coefficient of `H` is nonnegative
  (`exists_coshModelHeatCoeff_nonneg`).

So in this model the heat `κ/L` detects the off-line pair exactly when `κ < δ/2`.  With `L = log t`, an
every-height heat rate `κ` excludes, in the dense model, exactly the off-line offsets above `2κ`: rates
`κ ≥ ¼` exclude nothing (every offset is below `½`), while rates `κ < ¼` exclude the offsets in
`(2κ, ½)`, a zero-free strip.

Proof.  By `coshModelHeat_eq`, `H(x) = ½ e^{λL²/2}(e^{Lx}P(x + κ) + e^{−Lx}P(κ − x))` with the heated
quartic `P`.  The even coefficients are `e^{λL²/2} c_n` with `c_n = Σ_{j ≤ 4} P^{(j)}(κ)/j! · L^{n−j}/(n−j)!`,
and `c_n · n! · L⁴ = Lⁿ R(n)` with (`coshModelSeriesCoeff_mul_factorial`, `coshModelSignPoly_eq`)

  `R(y) = ((a+y)² − b²)² + (a − y)(6(a+y)² − 2b²) + 3a² + 2ay + 11y² − 6y`,  `a = κL`, `b = δL`.

The falling factorials `n!/(n−j)!` act on `P` as a backward heat of variance `n/L²`, which is the
term `(a − y)(…)`.  For `2κ < δ` take `n` even with `a + n ∈ (b − 2, b]`: then the first term is
`≤ 16b²`, the second `≤ (2 − (δ − 2κ)L) b²`, the rest `≤ 13b²`, so `R(n) < 0` once `(δ − 2κ)L > 31`.  For
`2κ > δ`, `R(y) ≥ 0` for every `y ≥ 0`: for `y ≤ a` either `6(a+y)² ≥ 2b²` (every term is `≥ 0` up to
`−1`) or `(a+y)² < b²/3` and the first term `≥ 4b⁴/9` dominates; for `y > a`, `a + y > 2a > b` and
`((a+y)² − b²)² ≥ θ²(a+y)⁴` with `θ = 1 − (δ/2κ)²`.
-/

open Filter Topology

namespace RHTower.DeBruijn

noncomputable section

/-- The Taylor coefficients at `0` of the heated cosh model. -/
def coshModelHeatCoeff (δ L lam : ℝ) (n : ℕ) : ℝ :=
  Real.exp (lam * L ^ 2 / 2) / 2 *
    (coshModelSeriesCoeff δ L lam (lam * L) n + (-1) ^ n * coshModelSeriesCoeff δ L lam (lam * L) n)

/-- The heated cosh model is the sum of its power series at `0`, for every heat `λ > 0`. -/
theorem hasSum_coshModelHeatCoeff {δ L lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    HasSum (fun n : ℕ => coshModelHeatCoeff δ L lam n * x ^ n) (coshModelHeat δ L lam x) := by
  have h1 := hasSum_exp_mul_coshModelQuartic δ L lam (lam * L) x
  have h2 := hasSum_exp_mul_coshModelQuartic δ L lam (lam * L) (-x)
  rw [coshModelHeat_eq hlam]
  have e : Real.exp (L * -x) * coshModelQuartic δ lam (-x + lam * L)
      = Real.exp (-(L * x)) * coshModelQuartic δ lam (lam * L - x) := by
    rw [show L * -x = -(L * x) by ring, show -x + lam * L = lam * L - x by ring]
  rw [e] at h2
  refine ((h1.add h2).mul_left (Real.exp (lam * L ^ 2 / 2) / 2)).congr_fun fun n => ?_
  unfold coshModelHeatCoeff
  rw [neg_pow]
  ring

/-- Two power series that sum to the same real function everywhere have the same coefficients. -/
private theorem coeff_eq_of_hasSum {f : ℝ → ℝ} {a b : ℕ → ℝ}
    (ha : ∀ x, HasSum (fun n : ℕ => a n * x ^ n) (f x))
    (hb : ∀ x, HasSum (fun n : ℕ => b n * x ^ n) (f x)) : a = b := by
  have key : ∀ c : ℕ → ℝ, (∀ x, HasSum (fun n : ℕ => c n * x ^ n) (f x)) →
      HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ c) 0 := by
    intro c hc
    rw [hasFPowerSeriesAt_iff]
    refine Eventually.of_forall fun z => ?_
    simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add]
    exact (hc z).congr_fun fun n => by ring
  have h := (key a ha).eq_formalMultilinearSeries (key b hb)
  funext n
  have := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff n) h
  simpa [FormalMultilinearSeries.coeff_ofScalars] using this

/-- The sign polynomial `R(y) = Σ_{j ≤ 4} q_j (y)_j L^{4−j}`, where `q_j` are the coefficients of
`P(x + κ)` and `(y)_j` is the falling factorial. -/
def coshModelSignPoly (δ L lam y : ℝ) : ℝ :=
  coshModelShiftCoeff δ lam (lam * L) 0 * L ^ 4
    + coshModelShiftCoeff δ lam (lam * L) 1 * y * L ^ 3
    + coshModelShiftCoeff δ lam (lam * L) 2 * (y * (y - 1)) * L ^ 2
    + coshModelShiftCoeff δ lam (lam * L) 3 * (y * (y - 1) * (y - 2)) * L
    + y * (y - 1) * (y - 2) * (y - 3)

private theorem descFactorial_cast (n j : ℕ) :
    (n.descFactorial j : ℝ) = ∏ i ∈ Finset.range j, ((n : ℝ) - i) := by
  rw [← descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_prod_range]

/-- **Falling factorials.**  `c_n · n! · L⁴ = Lⁿ R(n)`. -/
theorem coshModelSeriesCoeff_mul_factorial (δ L lam : ℝ) (n : ℕ) :
    coshModelSeriesCoeff δ L lam (lam * L) n * (n.factorial : ℝ) * L ^ 4
      = L ^ n * coshModelSignPoly δ L lam n := by
  have hd : ∀ j ∈ Finset.range 5,
      (if j ≤ n then coshModelShiftCoeff δ lam (lam * L) j * (L ^ (n - j) / ((n - j).factorial : ℝ))
          else 0) * (n.factorial : ℝ) * L ^ 4
        = coshModelShiftCoeff δ lam (lam * L) j * (n.descFactorial j : ℝ) * (L ^ n * L ^ (4 - j)) := by
    intro j hj
    have hj4 : j ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    split_ifs with hjn
    · have hcast : (n.factorial : ℝ) = ((n - j).factorial : ℝ) * (n.descFactorial j : ℝ) := by
        exact_mod_cast (Nat.factorial_mul_descFactorial hjn).symm
      have hpos : ((n - j).factorial : ℝ) ≠ 0 := by positivity
      have hL : L ^ n * L ^ (4 - j) = L ^ (n - j) * L ^ 4 := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [hcast, hL]
      field_simp
    · have h0 : n.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [h0]
  have h4 : coshModelShiftCoeff δ lam (lam * L) 4 = 1 := by simp [coshModelShiftCoeff]
  unfold coshModelSeriesCoeff
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_congr rfl hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, descFactorial_cast, Finset.prod_range_succ,
    Finset.prod_range_zero, coshModelSignPoly, h4]
  norm_num
  ring

/-- **The sign polynomial in scaled form.**  With `a = κL`, `b = δL` and `λ = κ/L`:
`R(y) = ((a+y)² − b²)² + (a − y)(6(a+y)² − 2b²) + 3a² + 2ay + 11y² − 6y`. -/
theorem coshModelSignPoly_eq {κ δ L : ℝ} (hL : L ≠ 0) (y : ℝ) :
    coshModelSignPoly δ L (κ / L) y
      = ((κ * L + y) ^ 2 - (δ * L) ^ 2) ^ 2
        + (κ * L - y) * (6 * (κ * L + y) ^ 2 - 2 * (δ * L) ^ 2)
        + 3 * (κ * L) ^ 2 + 2 * (κ * L) * y + 11 * y ^ 2 - 6 * y := by
  have hκ : κ / L * L = κ := by field_simp
  unfold coshModelSignPoly coshModelShiftCoeff
  simp only [hκ]
  norm_num
  field_simp
  ring

/-- The even coefficients are `e^{λL²/2} c_n`. -/
theorem coshModelHeatCoeff_even (δ L lam : ℝ) (m : ℕ) :
    coshModelHeatCoeff δ L lam (2 * m)
      = Real.exp (lam * L ^ 2 / 2) * coshModelSeriesCoeff δ L lam (lam * L) (2 * m) := by
  unfold coshModelHeatCoeff
  rw [pow_mul, neg_one_sq, one_pow]
  ring

/-- The scaled sign polynomial `R(a, b, y)`. -/
def coshModelScaledSign (a b y : ℝ) : ℝ :=
  ((a + y) ^ 2 - b ^ 2) ^ 2 + (a - y) * (6 * (a + y) ^ 2 - 2 * b ^ 2)
    + 3 * a ^ 2 + 2 * a * y + 11 * y ^ 2 - 6 * y

/-- **Negativity at the offset.**  If `a + y ∈ (b − 2, b]`, `b ≥ 8` and `b − 2a ≥ 32`, then
`R(a, b, y) < 0`. -/
theorem coshModelScaledSign_neg {a b y : ℝ} (ha : 0 < a) (hb : 8 ≤ b) (hy : 0 ≤ y)
    (hlo : -2 < a + y - b) (hhi : a + y - b ≤ 0) (hgap : 32 ≤ b - 2 * a) :
    coshModelScaledSign a b y < 0 := by
  obtain ⟨e, he⟩ : ∃ e, e = a + y - b := ⟨_, rfl⟩
  have hc : a + y = b + e := by rw [he]; ring
  have he2 : -2 < e := by rw [he]; exact hlo
  have he0 : e ≤ 0 := by rw [he]; exact hhi
  have h1 : ((a + y) ^ 2 - b ^ 2) ^ 2 ≤ 16 * b ^ 2 := by
    have hk : (a + y) ^ 2 - b ^ 2 = e * (2 * b + e) := by rw [hc]; ring
    have hpos : 0 < 2 * b + e := by linarith
    have hlo' : -(4 * b) ≤ e * (2 * b + e) := by nlinarith
    have hhi' : e * (2 * b + e) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he0 hpos.le
    rw [hk]
    nlinarith
  have hF : b ^ 2 ≤ 6 * (a + y) ^ 2 - 2 * b ^ 2 := by
    have h34 : 3 * b / 4 ≤ a + y := by rw [hc]; linarith
    have hsq : (3 * b / 4) ^ 2 ≤ (a + y) ^ 2 := pow_le_pow_left₀ (by linarith) h34 2
    nlinarith
  have hay : a - y ≤ 2 * a - b + 2 := by linarith
  have hay0 : a - y ≤ 0 := by linarith
  have h2 : (a - y) * (6 * (a + y) ^ 2 - 2 * b ^ 2) ≤ (2 * a - b + 2) * b ^ 2 :=
    calc (a - y) * (6 * (a + y) ^ 2 - 2 * b ^ 2) ≤ (a - y) * b ^ 2 :=
          mul_le_mul_of_nonpos_left hF hay0
      _ ≤ (2 * a - b + 2) * b ^ 2 := mul_le_mul_of_nonneg_right hay (sq_nonneg b)
  have hyb : y ≤ b := by linarith
  have h2a : 2 * a ≤ b := by linarith
  have h3 : 3 * a ^ 2 + 2 * a * y + 11 * y ^ 2 - 6 * y ≤ 13 * b ^ 2 := by
    have t1 : 4 * a ^ 2 ≤ b ^ 2 := by nlinarith
    have t2 : 2 * a * y ≤ b ^ 2 := by nlinarith
    have t3 : y ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith
  have hb2 : 0 < b ^ 2 := by positivity
  have hsum : coshModelScaledSign a b y ≤ (31 + 2 * a - b) * b ^ 2 := by
    unfold coshModelScaledSign
    nlinarith
  have hneg : (31 + 2 * a - b) * b ^ 2 < 0 := mul_neg_of_neg_of_pos (by linarith) hb2
  linarith

/-- **Positivity above half the offset.**  If `b < 2a` with `b² = (1 − θ)(2a)²`, `θ > 0`, `a ≥ 1`,
`b ≥ 5` and `7 ≤ θ² · 2a`, then `R(a, b, y) ≥ 1` for every `y ≥ 0`. -/
theorem one_le_coshModelScaledSign {a b y θ : ℝ} (ha : 1 ≤ a) (hb : 5 ≤ b) (hθ : 0 < θ)
    (hbθ : b ^ 2 = (1 - θ) * (2 * a) ^ 2) (hθa : 7 ≤ θ ^ 2 * (2 * a)) (hy : 0 ≤ y) :
    1 ≤ coshModelScaledSign a b y := by
  have hθ1 : θ ≤ 1 := by
    by_contra h
    have : (1 - θ) * (2 * a) ^ 2 < 0 := mul_neg_of_neg_of_pos (by linarith) (by positivity)
    nlinarith [sq_nonneg b]
  have hba : b < 2 * a := by
    have : b ^ 2 < (2 * a) ^ 2 := by
      rw [hbθ]; have : 0 < (2 * a) ^ 2 := by positivity
      nlinarith
    nlinarith
  have h3 : -1 ≤ 3 * a ^ 2 + 2 * a * y + 11 * y ^ 2 - 6 * y := by
    have : 0 ≤ 3 * a ^ 2 + 2 * a * y := by positivity
    nlinarith [sq_nonneg (11 * y - 3)]
  unfold coshModelScaledSign
  rcases le_or_gt y a with hya | hya
  · rcases le_or_gt (2 * b ^ 2) (6 * (a + y) ^ 2) with hc | hc
    · have h2 : 0 ≤ (a - y) * (6 * (a + y) ^ 2 - 2 * b ^ 2) :=
        mul_nonneg (by linarith) (by linarith)
      have h3' : 1 ≤ 3 * a ^ 2 + 2 * a * y + 11 * y ^ 2 - 6 * y := by
        have t : 3 ≤ 3 * a ^ 2 := by nlinarith
        have t' : 0 ≤ 2 * a * y := by positivity
        nlinarith [sq_nonneg (11 * y - 3)]
      have h1 : 0 ≤ ((a + y) ^ 2 - b ^ 2) ^ 2 := sq_nonneg _
      linarith
    · have hcb : 3 * (a + y) ^ 2 < b ^ 2 := by linarith
      have hd : 2 * b ^ 2 / 3 ≤ b ^ 2 - (a + y) ^ 2 := by linarith
      have hd0 : 0 ≤ 2 * b ^ 2 / 3 := by positivity
      have h1 : (2 * b ^ 2 / 3) ^ 2 ≤ ((a + y) ^ 2 - b ^ 2) ^ 2 := by
        rw [show ((a + y) ^ 2 - b ^ 2) ^ 2 = (b ^ 2 - (a + y) ^ 2) ^ 2 by ring]
        exact pow_le_pow_left₀ hd0 hd 2
      have hay : 0 ≤ a - y := by linarith
      have h2 : -(2 * a * b ^ 2) ≤ (a - y) * (6 * (a + y) ^ 2 - 2 * b ^ 2) := by
        have hle : a - y ≤ a := by linarith
        have hpos6 : 0 ≤ 6 * (a + y) ^ 2 := by positivity
        have : (a - y) * (-(2 * b ^ 2)) ≤ (a - y) * (6 * (a + y) ^ 2 - 2 * b ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hay
        have : a * (-(2 * b ^ 2)) ≤ (a - y) * (-(2 * b ^ 2)) :=
          mul_le_mul_of_nonpos_right hle (by nlinarith [sq_nonneg b])
        linarith
      have ha3 : 3 * a ^ 2 < b ^ 2 := by
        have : a ^ 2 ≤ (a + y) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith
      have hab : a < b := by nlinarith
      have hb0 : 0 < b := by linarith
      have hkey : 2 * a * b ^ 2 + 2 ≤ (2 * b ^ 2 / 3) ^ 2 := by
        have t1 : 2 * a * b ^ 2 ≤ 2 * b ^ 3 / 1 := by
          have : a * b ^ 2 ≤ b * b ^ 2 := mul_le_mul_of_nonneg_right hab.le (sq_nonneg b)
          nlinarith
        have t2 : 125 ≤ b ^ 3 := by
          have : (5:ℝ) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by norm_num) hb 3
          linarith
        have t3 : (2 * b ^ 2 / 3) ^ 2 = 4 / 9 * b * b ^ 3 := by ring
        rw [t3]
        nlinarith
      linarith
  · obtain ⟨c, hcdef⟩ : ∃ c, c = a + y := ⟨_, rfl⟩
    rw [← hcdef]
    have hc2a : 2 * a < c := by rw [hcdef]; linarith
    have hcb : b < c := by linarith
    have hc0 : 0 < c := by linarith
    have hθc : θ * c ^ 2 ≤ c ^ 2 - b ^ 2 := by
      have hsq : (2 * a) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by linarith) hc2a.le 2
      have : b ^ 2 ≤ (1 - θ) * c ^ 2 := by
        rw [hbθ]; exact mul_le_mul_of_nonneg_left hsq (by linarith)
      linarith
    have h1 : θ ^ 2 * c ^ 4 ≤ (c ^ 2 - b ^ 2) ^ 2 := by
      have hθc0 : 0 ≤ θ * c ^ 2 := by positivity
      calc θ ^ 2 * c ^ 4 = (θ * c ^ 2) ^ 2 := by ring
        _ ≤ (c ^ 2 - b ^ 2) ^ 2 := pow_le_pow_left₀ hθc0 hθc 2
    have hF : 0 ≤ 6 * c ^ 2 - 2 * b ^ 2 := by nlinarith
    have hyc : y - a ≤ c := by rw [hcdef]; linarith
    have h2 : -(6 * c ^ 3) ≤ (a - y) * (6 * c ^ 2 - 2 * b ^ 2) := by
      have t1 : (y - a) * (6 * c ^ 2 - 2 * b ^ 2) ≤ c * (6 * c ^ 2 - 2 * b ^ 2) :=
        mul_le_mul_of_nonneg_right hyc hF
      have t2 : c * (6 * c ^ 2 - 2 * b ^ 2) ≤ 6 * c ^ 3 := by nlinarith [sq_nonneg b]
      linarith
    have h7 : 7 ≤ θ ^ 2 * c := by
      have : θ ^ 2 * (2 * a) ≤ θ ^ 2 * c := mul_le_mul_of_nonneg_left hc2a.le (by positivity)
      linarith
    have hc1 : 1 ≤ c := by linarith
    have hc3 : 7 * c ^ 3 ≤ θ ^ 2 * c ^ 4 := by
      have : 7 * c ^ 3 ≤ (θ ^ 2 * c) * c ^ 3 := mul_le_mul_of_nonneg_right h7 (by positivity)
      calc 7 * c ^ 3 ≤ (θ ^ 2 * c) * c ^ 3 := this
        _ = θ ^ 2 * c ^ 4 := by ring
    have hc2 : 2 ≤ c := by linarith
    have hc31 : 8 ≤ c ^ 3 := by
      have : (2:ℝ) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (by norm_num) hc2 3
      linarith
    linarith

/-- The sign of the even coefficient `c_n` is the sign of `R(κL, δL, n)`. -/
theorem coshModelSeriesCoeff_scaled {κ δ L : ℝ} (hL : 0 < L) (n : ℕ) :
    coshModelSeriesCoeff δ L (κ / L) κ n * ((n.factorial : ℝ) * L ^ 4)
      = L ^ n * coshModelScaledSign (κ * L) (δ * L) n := by
  have hfac := coshModelSeriesCoeff_mul_factorial δ L (κ / L) n
  have hκL : κ / L * L = κ := by field_simp
  rw [hκL, coshModelSignPoly_eq hL.ne' (n : ℝ)] at hfac
  rw [← mul_assoc, hfac]
  rfl

/-- **Detection below half the offset.**  If `0 < κ` and `2κ < δ`, then for all large `L` the heated
cosh model at heat `κ/L` has a negative even Taylor coefficient at `0`. -/
theorem exists_coshModelHeatCoeff_neg {δ κ : ℝ} (hκ : 0 < κ) (hδκ : 2 * κ < δ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, ∃ n : ℕ, 6 ≤ n ∧ coshModelHeatCoeff δ L (κ / L) n < 0 := by
  have hδ : 0 < δ := by linarith
  have hD0 : 0 < δ - 2 * κ := by linarith
  have hDk : 0 < δ - κ := by linarith
  refine ⟨max (max (8 / δ) (32 / (δ - 2 * κ))) (6 / (δ - κ)),
    lt_max_of_lt_right (by positivity), fun L hL => ?_⟩
  have hL8 : 8 / δ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL32 : 32 / (δ - 2 * κ) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL6 : 6 / (δ - κ) ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL8
  have hb8 : 8 ≤ δ * L := by rw [div_le_iff₀ hδ] at hL8; linarith
  have hDL : 32 ≤ δ * L - 2 * (κ * L) := by rw [div_le_iff₀ hD0] at hL32; linarith
  have hnn : 0 ≤ (δ - κ) * L / 2 := by
    have : 0 ≤ δ - κ := by linarith
    positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊(δ - κ) * L / 2⌋₊ := ⟨_, rfl⟩
  have hm_le : (m : ℝ) ≤ (δ - κ) * L / 2 := by rw [hm]; exact Nat.floor_le hnn
  have hm_gt : (δ - κ) * L / 2 < (m : ℝ) + 1 := by rw [hm]; exact Nat.lt_floor_add_one _
  have hm3 : 3 ≤ m := by
    rw [hm]; refine Nat.le_floor ?_
    rw [div_le_iff₀ hDk] at hL6; push_cast; linarith
  refine ⟨2 * m, by omega, ?_⟩
  rw [coshModelHeatCoeff_even]
  have hκL : κ / L * L = κ := by field_simp
  rw [hκL]
  refine mul_neg_of_pos_of_neg (Real.exp_pos _) ?_
  have hy : (((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) := by push_cast; ring
  have hR : coshModelScaledSign (κ * L) (δ * L) ((2 * m : ℕ) : ℝ) < 0 := by
    rw [hy]
    refine coshModelScaledSign_neg (by positivity) hb8 (by positivity) ?_ ?_ hDL
    · nlinarith
    · nlinarith
  have hS := coshModelSeriesCoeff_scaled (κ := κ) (δ := δ) hL0 (2 * m)
  have hpos : 0 < ((2 * m).factorial : ℝ) * L ^ 4 := by positivity
  have hrhs : L ^ (2 * m) * coshModelScaledSign (κ * L) (δ * L) ((2 * m : ℕ) : ℝ) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hR
  rw [← hS] at hrhs
  by_contra hc
  exact absurd hrhs (not_lt.mpr (mul_nonneg (not_lt.mp hc) hpos.le))

/-- **No nonnegative power series below half the offset.** -/
theorem not_exists_nonneg_hasSum_coshModelHeat {δ κ : ℝ} (hκ : 0 < κ) (hδκ : 2 * κ < δ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, ¬ ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧
      ∀ x : ℝ, HasSum (fun n : ℕ => a n * x ^ n) (coshModelHeat δ L (κ / L) x) := by
  obtain ⟨L₀, hL₀, h⟩ := exists_coshModelHeatCoeff_neg hκ hδκ
  refine ⟨L₀, hL₀, fun L hL ⟨a, ha0, ha⟩ => ?_⟩
  obtain ⟨n, -, hn⟩ := h L hL
  have hL0 : 0 < L := lt_of_lt_of_le hL₀ hL
  have hlam : 0 < κ / L := by positivity
  have heq := coeff_eq_of_hasSum ha (fun x => hasSum_coshModelHeatCoeff (δ := δ) (L := L) hlam x)
  have := ha0 n
  rw [heq] at this
  linarith

/-- **Positivity above half the offset.**  If `0 < δ < 2κ`, then for all large `L` every Taylor
coefficient of the heated cosh model at heat `κ/L` is nonnegative. -/
theorem exists_coshModelHeatCoeff_nonneg {δ κ : ℝ} (hδ : 0 < δ) (hδκ : δ < 2 * κ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, 0 ≤ coshModelHeatCoeff δ L (κ / L) n := by
  have hκ : 0 < κ := by linarith
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = 1 - (δ / (2 * κ)) ^ 2 := ⟨_, rfl⟩
  have hρ : δ / (2 * κ) < 1 := by rw [div_lt_one (by positivity)]; exact hδκ
  have hρ0 : 0 < δ / (2 * κ) := by positivity
  have hθ0 : 0 < θ := by
    rw [hθ]
    have : (δ / (2 * κ)) ^ 2 < 1 := by nlinarith
    linarith
  refine ⟨max (max (1 / κ) (5 / δ)) (7 / (2 * κ * θ ^ 2)), by positivity, fun L hL n => ?_⟩
  have hL1 : 1 / κ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL3 : 5 / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL7 : 7 / (2 * κ * θ ^ 2) ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL1
  have ha1 : 1 ≤ κ * L := by rw [div_le_iff₀ hκ] at hL1; linarith
  have hb3 : 5 ≤ δ * L := by rw [div_le_iff₀ hδ] at hL3; linarith
  have hθa : 7 ≤ θ ^ 2 * (2 * (κ * L)) := by
    rw [div_le_iff₀ (by positivity)] at hL7; linarith
  have hbθ : (δ * L) ^ 2 = (1 - θ) * (2 * (κ * L)) ^ 2 := by
    rw [hθ]; field_simp; ring
  have hR : 0 ≤ coshModelScaledSign (κ * L) (δ * L) n :=
    le_trans zero_le_one (one_le_coshModelScaledSign ha1 hb3 hθ0 hbθ hθa (Nat.cast_nonneg n))
  have hS := coshModelSeriesCoeff_scaled (κ := κ) (δ := δ) hL0 n
  have hpos : 0 < (n.factorial : ℝ) * L ^ 4 := by positivity
  have hcn : 0 ≤ coshModelSeriesCoeff δ L (κ / L) κ n := by
    have hr : 0 ≤ L ^ n * coshModelScaledSign (κ * L) (δ * L) n := mul_nonneg (by positivity) hR
    rw [← hS] at hr
    exact nonneg_of_mul_nonneg_left hr hpos
  have hκL : κ / L * L = κ := by field_simp
  unfold coshModelHeatCoeff
  rw [hκL]
  have h2 : 0 ≤ coshModelSeriesCoeff δ L (κ / L) κ n
      + (-1) ^ n * coshModelSeriesCoeff δ L (κ / L) κ n := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> linarith
  positivity

/-- **Negativity on the detection window.**  If `a > 0`, `D = b − 2a ≥ 100` and `4s² ≤ D`, then
`R(a, b, b − a + s) < 0`. -/
theorem coshModelScaledSign_neg_window {a b s : ℝ} (ha : 0 < a) (hD : 100 ≤ b - 2 * a)
    (hs : 4 * s ^ 2 ≤ b - 2 * a) :
    coshModelScaledSign a b (b - a + s) < 0 := by
  obtain ⟨D, hDdef⟩ : ∃ D, D = b - 2 * a := ⟨_, rfl⟩
  rw [← hDdef] at hD hs
  have hDb : D ≤ b := by rw [hDdef]; linarith
  have hb : 100 ≤ b := le_trans hD hDb
  have hb0 : 0 < b := by linarith
  -- `|s| ≤ D/20 ≤ b/20`
  have hsD : s ^ 2 ≤ (D / 20) ^ 2 := by nlinarith
  have hsD' : |s| ≤ D / 20 := by
    rw [← abs_of_pos (show 0 < D / 20 by linarith)]; exact sq_le_sq.mp hsD
  have hsb : |s| ≤ b / 20 := le_trans hsD' (by linarith)
  have hs1 := abs_le.mp hsD'
  have hs2 := abs_le.mp hsb
  unfold coshModelScaledSign
  have hc : a + (b - a + s) = b + s := by ring
  rw [hc]
  -- `((b+s)² − b²)² = s²(2b+s)² ≤ (41/40)² · 4b² · D/4`
  have hT1 : ((b + s) ^ 2 - b ^ 2) ^ 2 ≤ (41 / 40) ^ 2 * b ^ 2 * D := by
    have hk : ((b + s) ^ 2 - b ^ 2) ^ 2 = s ^ 2 * (2 * b + s) ^ 2 := by ring
    have h2b : (2 * b + s) ^ 2 ≤ (41 / 20 * b) ^ 2 := by
      have h0 : 0 ≤ 2 * b + s := by linarith
      exact pow_le_pow_left₀ h0 (by linarith) 2
    rw [hk]
    calc s ^ 2 * (2 * b + s) ^ 2 ≤ (D / 4) * (41 / 20 * b) ^ 2 :=
          mul_le_mul (by linarith) h2b (sq_nonneg _) (by linarith)
      _ = (41 / 40) ^ 2 * b ^ 2 * D := by ring
  -- `(a − y)(6(b+s)² − 2b²) ≤ −(19/20)(17/5) b² D`
  have hT2 : (a - (b - a + s)) * (6 * (b + s) ^ 2 - 2 * b ^ 2) ≤ -(19 / 20 * (17 / 5)) * b ^ 2 * D := by
    have hay : a - (b - a + s) = -(D + s) := by rw [hDdef]; ring
    have hDs : 19 / 20 * D ≤ D + s := by linarith
    have hF : 17 / 5 * b ^ 2 ≤ 6 * (b + s) ^ 2 - 2 * b ^ 2 := by nlinarith
    rw [hay]
    have h1 : 19 / 20 * D * (17 / 5 * b ^ 2) ≤ (D + s) * (6 * (b + s) ^ 2 - 2 * b ^ 2) :=
      mul_le_mul hDs hF (by positivity) (by linarith)
    linarith
  -- the rest is `≤ 14 b²`
  have hT3 : 3 * a ^ 2 + 2 * a * (b - a + s) + 11 * (b - a + s) ^ 2 - 6 * (b - a + s) ≤ 14 * b ^ 2 := by
    have ha2 : 2 * a ≤ b := by linarith
    have hy0 : 0 ≤ b - a + s := by linarith
    have hy1 : b - a + s ≤ 21 / 20 * b := by linarith
    have t1 : 3 * a ^ 2 ≤ 3 / 4 * b ^ 2 := by nlinarith
    have t2 : 2 * a * (b - a + s) ≤ 21 / 20 * b ^ 2 := by nlinarith
    have t3 : 11 * (b - a + s) ^ 2 ≤ 11 * (21 / 20 * b) ^ 2 := by
      have := pow_le_pow_left₀ hy0 hy1 2; linarith
    nlinarith
  have hb2 : 0 < b ^ 2 := by positivity
  have hsum : ((b + s) ^ 2 - b ^ 2) ^ 2 + (a - (b - a + s)) * (6 * (b + s) ^ 2 - 2 * b ^ 2)
      + 3 * a ^ 2 + 2 * a * (b - a + s) + 11 * (b - a + s) ^ 2 - 6 * (b - a + s)
      ≤ b ^ 2 * ((41 / 40) ^ 2 * D - 19 / 20 * (17 / 5) * D + 14) := by nlinarith
  have hneg : (41 / 40) ^ 2 * D - 19 / 20 * (17 / 5) * D + 14 < 0 := by nlinarith
  have : b ^ 2 * ((41 / 40) ^ 2 * D - 19 / 20 * (17 / 5) * D + 14) < 0 := mul_neg_of_pos_of_neg hb2 hneg
  linarith

/-- **Many negative coefficients.**  If `0 < κ` and `2κ < δ`, then for all large `L` the heated cosh
model at heat `κ/L` has at least `√((δ − 2κ)L)/4` negative even Taylor coefficients at `0`: the negative
index of a single off-line pair at offset `δ` grows like `√((δ − 2κ) L)`. -/
theorem exists_many_coshModelHeatCoeff_neg {δ κ : ℝ} (hκ : 0 < κ) (hδκ : 2 * κ < δ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, ∃ S : Finset ℕ,
      (∀ m ∈ S, coshModelHeatCoeff δ L (κ / L) (2 * m) < 0) ∧
        Real.sqrt ((δ - 2 * κ) * L) / 4 ≤ (S.card : ℝ) := by
  have hD0 : 0 < δ - 2 * κ := by linarith
  refine ⟨256 / (δ - 2 * κ), by positivity, fun L hL => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hDL : 256 ≤ (δ - 2 * κ) * L := by
    have h := (div_le_iff₀ hD0).mp (show 256 / (δ - 2 * κ) ≤ L from hL); linarith
  obtain ⟨D, hDdef⟩ : ∃ D, D = (δ - 2 * κ) * L := ⟨_, rfl⟩
  rw [← hDdef] at hDL ⊢
  have hDeq : D = δ * L - 2 * (κ * L) := by rw [hDdef]; ring
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt D := ⟨_, rfl⟩
  have hr16 : 16 ≤ r := by
    rw [hr, show (16 : ℝ) = Real.sqrt 256 by rw [show (256 : ℝ) = 16 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hDL
  have hrr : r ^ 2 = D := by rw [hr]; exact Real.sq_sqrt (by linarith)
  -- the window `2m ∈ [y₀ − r/2, y₀ + r/2]`, `y₀ = δL − κL`
  set y₀ := δ * L - κ * L with hy₀
  have hy₀r : r / 2 ≤ y₀ := by
    have : D ≤ y₀ := by rw [hDeq, hy₀]; nlinarith
    nlinarith
  set m₁ := ⌈(y₀ - r / 2) / 2⌉₊ with hm₁
  set m₂ := ⌊(y₀ + r / 2) / 2⌋₊ with hm₂
  refine ⟨Finset.Icc m₁ m₂, fun m hm => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    have hlo : (y₀ - r / 2) / 2 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have hhi : (m : ℝ) ≤ (y₀ + r / 2) / 2 :=
      le_trans (by exact_mod_cast h2) (Nat.floor_le (by nlinarith))
    rw [coshModelHeatCoeff_even]
    have hκL : κ / L * L = κ := by field_simp
    rw [hκL]
    refine mul_neg_of_pos_of_neg (Real.exp_pos _) ?_
    have hy : ((2 * m : ℕ) : ℝ) = δ * L - κ * L + (2 * (m : ℝ) - y₀) := by push_cast; rw [hy₀]; ring
    have hR : coshModelScaledSign (κ * L) (δ * L) ((2 * m : ℕ) : ℝ) < 0 := by
      rw [hy]
      refine coshModelScaledSign_neg_window (by positivity) (by rw [← hDeq]; linarith) ?_
      rw [← hDeq, ← hrr]
      have : |2 * (m : ℝ) - y₀| ≤ r / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
      nlinarith
    have hS := coshModelSeriesCoeff_scaled (κ := κ) (δ := δ) hL0 (2 * m)
    have hpos : 0 < ((2 * m).factorial : ℝ) * L ^ 4 := by positivity
    have hrhs : L ^ (2 * m) * coshModelScaledSign (κ * L) (δ * L) ((2 * m : ℕ) : ℝ) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hR
    rw [← hS] at hrhs
    by_contra hc
    exact absurd hrhs (not_lt.mpr (mul_nonneg (not_lt.mp hc) hpos.le))
  · -- the window holds at least `r/2 − 1 ≥ r/4` integers
    have hcard : (m₂ : ℝ) + 1 - m₁ ≤ ((Finset.Icc m₁ m₂).card : ℝ) := by
      rw [Nat.card_Icc]
      rcases le_or_gt m₁ (m₂ + 1) with h | h
      · rw [Nat.cast_sub h]; push_cast; linarith
      · have : (m₂ : ℝ) + 1 < m₁ := by exact_mod_cast h
        linarith [Nat.cast_nonneg (α := ℝ) (m₂ + 1 - m₁)]
    have hm₁' : (m₁ : ℝ) < (y₀ - r / 2) / 2 + 1 := Nat.ceil_lt_add_one (by nlinarith)
    have hm₂' : (y₀ + r / 2) / 2 < (m₂ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [← hr]
    linarith

end

end RHTower.DeBruijn
