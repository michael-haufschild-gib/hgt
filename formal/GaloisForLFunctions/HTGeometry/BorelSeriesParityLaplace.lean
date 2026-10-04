import GaloisForLFunctions.HTGeometry.BorelSeriesConvolution

/-!
# Derivatives, order, parity and Laplace transforms of Borel series

For `B_a(t) = Σ_n a_n t^n/n!` with a geometric coefficient bound `|a_n| ≤ M R^n`:

* `B_a^{(m)} = B_{a(·+m)}` (`iteratedDeriv_borelSeries`);
* coefficientwise comparison is inherited on `t ≥ 0`, and nonnegative coefficients with one positive
  coefficient give a positive value on `t > 0`;
* the odd and even factorial series are Borel series of the parity spreads of their coefficients,
  and `t · Σ_j a_j t^{2j+1}/(2j+1)! = Σ_k 2k a_{k-1} t^{2k}/(2k)!`;
* `|B_a(t)| ≤ M e^{R|t|}`, and for `p > R` the Laplace transform is
  `∫_0^∞ B_a(t) e^{-pt} dt = Σ_n a_n p^{-n-1}`.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Derivatives -/

theorem geometricCoeffBound_shift_add {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R)
    (m : ℕ) : GeometricCoeffBound (fun n => a (n + m)) (M * R ^ m) R := fun n => by
  rw [mul_assoc, ← pow_add, add_comm m n]
  exact ha (n + m)

theorem iteratedDeriv_borelSeries {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R)
    (m : ℕ) : iteratedDeriv m (borelSeries a) = borelSeries (fun n => a (n + m)) := by
  induction m generalizing a M with
  | zero => simp
  | succ m ih =>
    have hd : deriv (borelSeries a) = borelSeries (fun n => a (n + 1)) :=
      funext fun t => (hasDerivAt_borelSeries ha t).deriv
    rw [iteratedDeriv_succ', hd, ih ha.shift]
    congr 1

/-! ## Linearity and order -/

theorem borelSeries_const_mul (c : ℝ) (a : ℕ → ℝ) (t : ℝ) :
    borelSeries (fun n => c * a n) t = c * borelSeries a t := by
  unfold borelSeries
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem borelSeries_neg (a : ℕ → ℝ) (t : ℝ) :
    borelSeries (fun n => -a n) t = -borelSeries a t := by
  simpa using borelSeries_const_mul (-1) a t

theorem borelSeries_add {a b : ℕ → ℝ} {M R M' R' : ℝ} (ha : GeometricCoeffBound a M R)
    (hb : GeometricCoeffBound b M' R') (t : ℝ) :
    borelSeries (fun n => a n + b n) t = borelSeries a t + borelSeries b t := by
  unfold borelSeries
  rw [← (summable_borelTerm ha t).tsum_add (summable_borelTerm hb t)]
  exact tsum_congr fun n => by ring

theorem dividedPowerFn_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ dividedPowerFn n t := by
  unfold dividedPowerFn; positivity

theorem dividedPowerFn_pos {t : ℝ} (ht : 0 < t) (n : ℕ) : 0 < dividedPowerFn n t := by
  unfold dividedPowerFn; positivity

/-- Coefficientwise comparison on nonnegative clocks. -/
theorem borelSeries_le_borelSeries {a b : ℕ → ℝ} {M R M' R' : ℝ}
    (ha : GeometricCoeffBound a M R) (hb : GeometricCoeffBound b M' R') (hab : ∀ n, a n ≤ b n)
    {t : ℝ} (ht : 0 ≤ t) : borelSeries a t ≤ borelSeries b t :=
  Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (hab n) (dividedPowerFn_nonneg ht n))
    (summable_borelTerm ha t) (summable_borelTerm hb t)

/-- Nonnegative coefficients with one positive coefficient give a positive value for `t > 0`. -/
theorem borelSeries_pos {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R)
    (hnn : ∀ n, 0 ≤ a n) {i : ℕ} (hi : 0 < a i) {t : ℝ} (ht : 0 < t) : 0 < borelSeries a t :=
  (summable_borelTerm ha t).tsum_pos (fun n => mul_nonneg (hnn n) (dividedPowerFn_nonneg ht.le n))
    i (mul_pos hi (dividedPowerFn_pos ht i))

/-! ## Parity spreads -/

/-- The even spread `N ↦ a_{N/2}` on even `N`, `0` on odd `N`. -/
def evenSpread (a : ℕ → ℝ) (N : ℕ) : ℝ := if N % 2 = 0 then a (N / 2) else 0

/-- The odd spread `N ↦ a_{N/2}` on odd `N`, `0` on even `N`. -/
def oddSpread (a : ℕ → ℝ) (N : ℕ) : ℝ := if N % 2 = 1 then a (N / 2) else 0

@[simp] theorem evenSpread_two_mul (a : ℕ → ℝ) (k : ℕ) : evenSpread a (2 * k) = a k := by
  unfold evenSpread; rw [if_pos (by omega), show 2 * k / 2 = k by omega]

@[simp] theorem evenSpread_two_mul_add_one (a : ℕ → ℝ) (k : ℕ) : evenSpread a (2 * k + 1) = 0 := by
  unfold evenSpread; rw [if_neg (by omega)]

@[simp] theorem oddSpread_two_mul (a : ℕ → ℝ) (k : ℕ) : oddSpread a (2 * k) = 0 := by
  unfold oddSpread; rw [if_neg (by omega)]

@[simp] theorem oddSpread_two_mul_add_one (a : ℕ → ℝ) (k : ℕ) : oddSpread a (2 * k + 1) = a k := by
  unfold oddSpread; rw [if_pos (by omega), show (2 * k + 1) / 2 = k by omega]

private theorem nonneg_of_geometricCoeffBound {a : ℕ → ℝ} {M R : ℝ}
    (ha : GeometricCoeffBound a M R) : 0 ≤ M := by
  have := (abs_nonneg _).trans (ha 0)
  simpa using this

theorem GeometricCoeffBound.evenSpread {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R)
    (hR : 0 ≤ R) : GeometricCoeffBound (HTGeometry.evenSpread a) M (max R 1) := by
  have hM := nonneg_of_geometricCoeffBound ha
  intro N
  unfold HTGeometry.evenSpread
  split_ifs
  · refine (ha _).trans (mul_le_mul_of_nonneg_left ?_ hM)
    exact (pow_le_pow_left₀ hR (le_max_left R 1) _).trans
      (pow_le_pow_right₀ (le_max_right R 1) (Nat.div_le_self N 2))
  · simp only [abs_zero]; positivity

theorem GeometricCoeffBound.oddSpread {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R)
    (hR : 0 ≤ R) : GeometricCoeffBound (HTGeometry.oddSpread a) M (max R 1) := by
  have hM := nonneg_of_geometricCoeffBound ha
  intro N
  unfold HTGeometry.oddSpread
  split_ifs
  · refine (ha _).trans (mul_le_mul_of_nonneg_left ?_ hM)
    exact (pow_le_pow_left₀ hR (le_max_left R 1) _).trans
      (pow_le_pow_right₀ (le_max_right R 1) (Nat.div_le_self N 2))
  · simp only [abs_zero]; positivity

theorem evenFactorialSeries_eq_borelSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) : evenFactorialSeries a = borelSeries (evenSpread a) := by
  funext t
  have hs := summable_borelTerm (ha.evenSpread hR) t
  have hse : Summable fun k : ℕ => evenSpread a (2 * k) * dividedPowerFn (2 * k) t :=
    hs.comp_injective (i := fun k : ℕ => 2 * k) fun x y h => by simpa using h
  have hso : Summable fun k : ℕ => evenSpread a (2 * k + 1) * dividedPowerFn (2 * k + 1) t :=
    hs.comp_injective (i := fun k : ℕ => 2 * k + 1) fun x y h => by simpa using h
  unfold borelSeries
  rw [← tsum_even_add_odd (f := fun n => evenSpread a n * dividedPowerFn n t) hse hso]
  simp only [evenSpread_two_mul, evenSpread_two_mul_add_one, zero_mul, tsum_zero, add_zero]
  unfold evenFactorialSeries dividedPowerFn
  exact tsum_congr fun k => by ring

theorem oddFactorialSeries_eq_borelSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) : oddFactorialSeries a = borelSeries (oddSpread a) := by
  funext t
  have hs := summable_borelTerm (ha.oddSpread hR) t
  have hse : Summable fun k : ℕ => oddSpread a (2 * k) * dividedPowerFn (2 * k) t :=
    hs.comp_injective (i := fun k : ℕ => 2 * k) fun x y h => by simpa using h
  have hso : Summable fun k : ℕ => oddSpread a (2 * k + 1) * dividedPowerFn (2 * k + 1) t :=
    hs.comp_injective (i := fun k : ℕ => 2 * k + 1) fun x y h => by simpa using h
  unfold borelSeries
  rw [← tsum_even_add_odd (f := fun n => oddSpread a n * dividedPowerFn n t) hse hso]
  simp only [oddSpread_two_mul, oddSpread_two_mul_add_one, zero_mul, tsum_zero, zero_add]
  unfold oddFactorialSeries dividedPowerFn
  exact tsum_congr fun k => by ring

theorem oddFactorialSeries_neg_arg (a : ℕ → ℝ) (t : ℝ) :
    oddFactorialSeries a (-t) = -oddFactorialSeries a t := by
  unfold oddFactorialSeries
  rw [← tsum_neg]
  exact tsum_congr fun j => by rw [Odd.neg_pow ⟨j, rfl⟩]; ring

theorem evenFactorialSeries_neg_arg (a : ℕ → ℝ) (t : ℝ) :
    evenFactorialSeries a (-t) = evenFactorialSeries a t := by
  unfold evenFactorialSeries
  exact tsum_congr fun j => by rw [Even.neg_pow ⟨j, by ring⟩]

theorem evenFactorialSeries_zero (a : ℕ → ℝ) : evenFactorialSeries a 0 = a 0 := by
  unfold evenFactorialSeries
  rw [tsum_eq_single 0]
  · simp
  · intro j hj; simp [hj]

theorem oddFactorialSeries_zero (a : ℕ → ℝ) : oddFactorialSeries a 0 = 0 := by
  unfold oddFactorialSeries; simp

/-- `t · Σ_j a_j t^{2j+1}/(2j+1)! = Σ_k 2k a_{k-1} t^{2k}/(2k)!`. -/
theorem hasSum_id_mul_oddFactorialSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) (t : ℝ) :
    HasSum (fun k : ℕ => 2 * (k : ℝ) * a (k - 1) * t ^ (2 * k) / ((2 * k).factorial : ℝ))
      (t * oddFactorialSeries a t) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, mul_zero, zero_mul,
    zero_div, sub_zero]
  have h := (summable_oddFactorialSeries_term hR ha t).hasSum.mul_left t
  refine h.congr_fun fun k => ?_
  rw [Nat.add_sub_cancel, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ]
  have hf : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp
  ring

/-! ## Exponential bound and Laplace transform -/

theorem hasSum_dividedPowerFn_exp (x : ℝ) : HasSum (fun n => dividedPowerFn n x) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  refine (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).congr_fun fun n => ?_
  unfold dividedPowerFn
  rw [smul_eq_mul]; ring

/-- `|B_a(t)| ≤ M e^{R|t|}`. -/
theorem abs_borelSeries_le {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R) (t : ℝ) :
    |borelSeries a t| ≤ M * Real.exp (R * |t|) := by
  have hn : ∀ n, ‖a n * dividedPowerFn n t‖ ≤ M * dividedPowerFn n (R * |t|) :=
    fun n => norm_borelTerm_le ha le_rfl n
  have hsum : Summable fun n => ‖a n * dividedPowerFn n t‖ :=
    ((summable_dividedPowerFn (R * |t|)).mul_left M).of_nonneg_of_le (fun n => norm_nonneg _) hn
  calc |borelSeries a t| = ‖∑' n, a n * dividedPowerFn n t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖a n * dividedPowerFn n t‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, M * dividedPowerFn n (R * |t|) :=
        Summable.tsum_le_tsum hn hsum ((summable_dividedPowerFn _).mul_left M)
    _ = M * Real.exp (R * |t|) := by rw [tsum_mul_left, (hasSum_dividedPowerFn_exp _).tsum_eq]

theorem integrableOn_dividedPowerFn_mul_exp_neg (n : ℕ) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => dividedPowerFn n t * Real.exp (-(p * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := p)
    (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) le_rfl hp
  have h' : IntegrableOn (fun x : ℝ => ((n.factorial : ℝ))⁻¹ * (x ^ (n : ℝ) *
      Real.exp (-p * x ^ (1 : ℝ)))) (Ioi 0) := h.const_mul _
  refine h'.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one, dividedPowerFn, neg_mul]
  ring

theorem integral_Ioi_dividedPowerFn_mul_exp_neg (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), dividedPowerFn n t * Real.exp (-(p * t)) = (p ^ (n + 1))⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := p) (by positivity) hp
  rw [Real.Gamma_nat_eq_factorial] at h
  have hcongr : ∫ t in Ioi (0 : ℝ), dividedPowerFn n t * Real.exp (-(p * t)) =
      ((n.factorial : ℝ))⁻¹ * ∫ t in Ioi (0 : ℝ), t ^ (((n : ℝ) + 1) - 1) * Real.exp (-(p * t)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show ((n : ℝ) + 1) - 1 = (n : ℝ) by ring, Real.rpow_natCast]
    unfold dividedPowerFn
    ring
  rw [hcongr, h, one_div, Real.inv_rpow hp.le,
    show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  field_simp

theorem integrableOn_borelSeries_mul_exp_neg {a : ℕ → ℝ} {M R p : ℝ}
    (ha : GeometricCoeffBound a M R) (hRp : R < p) :
    IntegrableOn (fun t => borelSeries a t * Real.exp (-(p * t))) (Ioi 0) := by
  have hg : IntegrableOn (fun t => M * Real.exp (-(p - R) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul M
  refine hg.mono' (((continuous_borelSeries ha).mul
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t)))).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht' : 0 < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |borelSeries a t| * Real.exp (-(p * t)) ≤ M * Real.exp (R * |t|) * Real.exp (-(p * t)) :=
        mul_le_mul_of_nonneg_right (abs_borelSeries_le ha t) (Real.exp_pos _).le
    _ = M * Real.exp (-(p - R) * t) := by
        rw [abs_of_pos ht', mul_assoc, ← Real.exp_add]; ring_nf

/-- **Laplace transform of a Borel series.**  For `p > R ≥ 0`,
`∫_0^∞ B_a(t) e^{-pt} dt = Σ_n a_n p^{-n-1}`. -/
theorem hasSum_integral_Ioi_borelSeries_mul_exp_neg {a : ℕ → ℝ} {M R p : ℝ}
    (ha : GeometricCoeffBound a M R) (hR : 0 ≤ R) (hRp : R < p) :
    HasSum (fun n => a n * (p ^ (n + 1))⁻¹)
      (∫ t in Ioi (0 : ℝ), borelSeries a t * Real.exp (-(p * t))) := by
  have hp : 0 < p := hR.trans_lt hRp
  have hM := nonneg_of_geometricCoeffBound ha
  set F : ℕ → ℝ → ℝ := fun n t => a n * (dividedPowerFn n t * Real.exp (-(p * t))) with hFdef
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (integrableOn_dividedPowerFn_mul_exp_neg n hp).const_mul (a n)
  have hnorm : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ = |a n| * (p ^ (n + 1))⁻¹ := by
    intro n
    rw [← integral_Ioi_dividedPowerFn_mul_exp_neg n hp, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    simp only [hFdef, Real.norm_eq_abs, abs_mul, abs_of_nonneg (dividedPowerFn_nonneg ht' n),
      abs_of_pos (Real.exp_pos _)]
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    simp_rw [hnorm]
    refine ((summable_geometric_of_lt_one (div_nonneg hR hp.le) ((div_lt_one hp).2 hRp)).mul_left
      (M / p)).of_nonneg_of_le (fun n => by positivity) fun n => ?_
    calc |a n| * (p ^ (n + 1))⁻¹ ≤ M * R ^ n * (p ^ (n + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right (ha n) (by positivity)
      _ = M / p * (R / p) ^ n := by rw [div_pow, pow_succ]; field_simp
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ n, ∫ t in Ioi (0 : ℝ), F n t = a n * (p ^ (n + 1))⁻¹ := by
    intro n
    simp only [hFdef]
    rw [integral_const_mul, integral_Ioi_dividedPowerFn_mul_exp_neg n hp]
  have hfun : (fun t => ∑' n, F n t) = fun t => borelSeries a t * Real.exp (-(p * t)) := by
    funext t
    simp only [hFdef, borelSeries]
    rw [← tsum_mul_right]
    exact tsum_congr fun n => by ring
  simp_rw [hval] at h
  rwa [hfun] at h

end GaloisForLFunctions.HTGeometry
