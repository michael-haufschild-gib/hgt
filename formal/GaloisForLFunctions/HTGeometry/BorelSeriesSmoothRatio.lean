import GaloisForLFunctions.HTGeometry.BorelSeriesParityLaplace

/-!
# Smoothness, remainders and ratio monotonicity of factorial series

* A Borel series with a geometric coefficient bound is `C^∞`.
* Remainders of odd and even factorial series: for `|t| ≤ 1`,
  `|O_a(t) - Σ_{j<n} a_j t^{2j+1}/(2j+1)!| ≤ M e^R |t|^{2n+1}`, and the same with `2n` for the
  even series.
* **Ratio monotonicity.**  If `q_j > 0`, `p_i q_j ≤ p_j q_i` for `i ≤ j`, strictly for one pair,
  and both series converge absolutely on `[0,∞)`, then `P/Q` is strictly increasing on `(0,∞)`:
  `P(t)Q(s) - P(s)Q(t) = ½ Σ_{i,j} (p_i q_j - p_j q_i)(t^i s^j - s^i t^j) > 0`.  Applied in
  `u = t²` it shows that `O_a/O_b` is strictly increasing on positive clocks when the coefficient
  ratios `a_j/b_j` increase.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Smoothness -/

theorem contDiff_borelSeries {a : ℕ → ℝ} {M R : ℝ} (ha : GeometricCoeffBound a M R) :
    ContDiff ℝ ∞ (borelSeries a) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [iteratedDeriv_borelSeries ha]
  exact fun t => (hasDerivAt_borelSeries (geometricCoeffBound_shift_add ha m) t).differentiableAt

theorem contDiff_oddFactorialSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) : ContDiff ℝ ∞ (oddFactorialSeries a) := by
  rw [oddFactorialSeries_eq_borelSeries hR ha]
  exact contDiff_borelSeries (ha.oddSpread hR)

theorem contDiff_evenFactorialSeries {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) : ContDiff ℝ ∞ (evenFactorialSeries a) := by
  rw [evenFactorialSeries_eq_borelSeries hR ha]
  exact contDiff_borelSeries (ha.evenSpread hR)

/-! ## Remainders -/

private theorem sum_pow_div_factorial_shift_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ∑' j : ℕ, R ^ (j + n) / ((j + n).factorial : ℝ) ≤ Real.exp R := by
  have hs := Real.summable_pow_div_factorial R
  have h := hs.sum_add_tsum_nat_add n
  rw [← (hasSum_dividedPowerFn_exp R).tsum_eq] at *
  have hfin : 0 ≤ ∑ i ∈ Finset.range n, R ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  have he : ∑' i : ℕ, dividedPowerFn i R = ∑' i : ℕ, R ^ i / (i.factorial : ℝ) := rfl
  rw [he]
  linarith

/-- **Odd remainder.**  For `|t| ≤ 1`,
`|O_a(t) - Σ_{j<n} a_j t^{2j+1}/(2j+1)!| ≤ M e^R |t|^{2n+1}`. -/
theorem abs_oddFactorialSeries_sub_sum_le {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    |oddFactorialSeries a t -
        ∑ j ∈ Finset.range n, a j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)| ≤
      M * Real.exp R * |t| ^ (2 * n + 1) := by
  have hM : 0 ≤ M := by have := (abs_nonneg _).trans (ha 0); simpa using this
  have hs := summable_oddFactorialSeries_term hR ha t
  have hsplit := hs.sum_add_tsum_nat_add n
  unfold oddFactorialSeries
  rw [← hsplit, add_sub_cancel_left]
  have hterm : ∀ j : ℕ, ‖a (j + n) * t ^ (2 * (j + n) + 1) / ((2 * (j + n) + 1).factorial : ℝ)‖ ≤
      M * |t| ^ (2 * n + 1) * (R ^ (j + n) / ((j + n).factorial : ℝ)) := by
    intro j
    have hf1 : (0 : ℝ) < ((2 * (j + n) + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hf2 : (0 : ℝ) < ((j + n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfle : ((j + n).factorial : ℝ) ≤ ((2 * (j + n) + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have htp : |t| ^ (2 * (j + n) + 1) ≤ |t| ^ (2 * n + 1) :=
      pow_le_pow_of_le_one (abs_nonneg t) ht (by omega)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hf1]
    calc |a (j + n)| * |t| ^ (2 * (j + n) + 1) / ((2 * (j + n) + 1).factorial : ℝ) ≤
        M * R ^ (j + n) * |t| ^ (2 * n + 1) / ((j + n).factorial : ℝ) := by
          gcongr
          · exact ha _
      _ = M * |t| ^ (2 * n + 1) * (R ^ (j + n) / ((j + n).factorial : ℝ)) := by ring
  have hsum : Summable fun j : ℕ => M * |t| ^ (2 * n + 1) * (R ^ (j + n) / ((j + n).factorial : ℝ)) :=
    ((summable_nat_add_iff n).2 (Real.summable_pow_div_factorial R)).mul_left _
  calc |∑' j, a (j + n) * t ^ (2 * (j + n) + 1) / ((2 * (j + n) + 1).factorial : ℝ)| =
      ‖∑' j, a (j + n) * t ^ (2 * (j + n) + 1) / ((2 * (j + n) + 1).factorial : ℝ)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, M * |t| ^ (2 * n + 1) * (R ^ (j + n) / ((j + n).factorial : ℝ)) :=
        tsum_of_norm_bounded hsum.hasSum hterm
    _ = M * |t| ^ (2 * n + 1) * ∑' j, R ^ (j + n) / ((j + n).factorial : ℝ) := tsum_mul_left
    _ ≤ M * |t| ^ (2 * n + 1) * Real.exp R :=
        mul_le_mul_of_nonneg_left (sum_pow_div_factorial_shift_le hR n) (by positivity)
    _ = M * Real.exp R * |t| ^ (2 * n + 1) := by ring

/-- **Even remainder.**  For `|t| ≤ 1`,
`|E_a(t) - Σ_{j<n} a_j t^{2j}/(2j)!| ≤ M e^R |t|^{2n}`. -/
theorem abs_evenFactorialSeries_sub_sum_le {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    |evenFactorialSeries a t -
        ∑ j ∈ Finset.range n, a j * t ^ (2 * j) / ((2 * j).factorial : ℝ)| ≤
      M * Real.exp R * |t| ^ (2 * n) := by
  have hM : 0 ≤ M := by have := (abs_nonneg _).trans (ha 0); simpa using this
  have hs := summable_evenFactorialSeries_term hR ha t
  have hsplit := hs.sum_add_tsum_nat_add n
  unfold evenFactorialSeries
  rw [← hsplit, add_sub_cancel_left]
  have hterm : ∀ j : ℕ, ‖a (j + n) * t ^ (2 * (j + n)) / ((2 * (j + n)).factorial : ℝ)‖ ≤
      M * |t| ^ (2 * n) * (R ^ (j + n) / ((j + n).factorial : ℝ)) := by
    intro j
    have hf1 : (0 : ℝ) < ((2 * (j + n)).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hf2 : (0 : ℝ) < ((j + n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfle : ((j + n).factorial : ℝ) ≤ ((2 * (j + n)).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have htp : |t| ^ (2 * (j + n)) ≤ |t| ^ (2 * n) :=
      pow_le_pow_of_le_one (abs_nonneg t) ht (by omega)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hf1]
    calc |a (j + n)| * |t| ^ (2 * (j + n)) / ((2 * (j + n)).factorial : ℝ) ≤
        M * R ^ (j + n) * |t| ^ (2 * n) / ((j + n).factorial : ℝ) := by
          gcongr
          · exact ha _
      _ = M * |t| ^ (2 * n) * (R ^ (j + n) / ((j + n).factorial : ℝ)) := by ring
  have hsum : Summable fun j : ℕ => M * |t| ^ (2 * n) * (R ^ (j + n) / ((j + n).factorial : ℝ)) :=
    ((summable_nat_add_iff n).2 (Real.summable_pow_div_factorial R)).mul_left _
  calc |∑' j, a (j + n) * t ^ (2 * (j + n)) / ((2 * (j + n)).factorial : ℝ)| =
      ‖∑' j, a (j + n) * t ^ (2 * (j + n)) / ((2 * (j + n)).factorial : ℝ)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, M * |t| ^ (2 * n) * (R ^ (j + n) / ((j + n).factorial : ℝ)) :=
        tsum_of_norm_bounded hsum.hasSum hterm
    _ = M * |t| ^ (2 * n) * ∑' j, R ^ (j + n) / ((j + n).factorial : ℝ) := tsum_mul_left
    _ ≤ M * |t| ^ (2 * n) * Real.exp R :=
        mul_le_mul_of_nonneg_left (sum_pow_div_factorial_shift_le hR n) (by positivity)
    _ = M * Real.exp R * |t| ^ (2 * n) := by ring

/-! ## Ratio monotonicity -/

private theorem pow_mul_pow_sub_nonpos {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {i j : ℕ} (hij : i ≤ j) :
    t ^ i * s ^ j - s ^ i * t ^ j ≤ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hst' : s ^ k ≤ t ^ k := pow_le_pow_left₀ hs hst k
  have e : t ^ i * s ^ (i + k) - s ^ i * t ^ (i + k) = (s * t) ^ i * (s ^ k - t ^ k) := by ring
  rw [e]
  exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (mul_nonneg hs (hs.trans hst)) i) (by linarith)

private theorem pow_mul_pow_sub_neg {s t : ℝ} (hs : 0 < s) (hst : s < t) {i j : ℕ} (hij : i < j) :
    t ^ i * s ^ j - s ^ i * t ^ j < 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have hst' : s ^ (k + 1) < t ^ (k + 1) := pow_lt_pow_left₀ hst hs.le (by omega)
  have e : t ^ i * s ^ (i + k + 1) - s ^ i * t ^ (i + k + 1) =
      (s * t) ^ i * (s ^ (k + 1) - t ^ (k + 1)) := by ring
  rw [e]
  exact mul_neg_of_pos_of_neg (pow_pos (mul_pos hs (hs.trans hst)) i) (by linarith)

/-- The antisymmetrized cross term of two power series at two clocks. -/
def ratioCross (p q : ℕ → ℝ) (s t : ℝ) (z : ℕ × ℕ) : ℝ :=
  p z.1 * t ^ z.1 * (q z.2 * s ^ z.2) - p z.1 * s ^ z.1 * (q z.2 * t ^ z.2)

/-- **Strict monotone ratio of positive power series.**  If `q_j > 0`, the coefficient ratio
`p_j/q_j` is nondecreasing (`p_i q_j ≤ p_j q_i` for `i ≤ j`) and increases strictly between some
`i₀ < j₀`, then `P(s) Q(t) < P(t) Q(s)` for `0 < s < t`. -/
theorem powerSeries_ratio_strictMono {p q : ℕ → ℝ} (hq : ∀ j, 0 < q j)
    (hpq : ∀ i j, i ≤ j → p i * q j ≤ p j * q i) {i₀ j₀ : ℕ} (hij₀ : i₀ < j₀)
    (hstrict : p i₀ * q j₀ < p j₀ * q i₀)
    (hps : ∀ u, 0 ≤ u → Summable fun j => |p j| * u ^ j)
    (hqs : ∀ u, 0 ≤ u → Summable fun j => q j * u ^ j) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    (∑' j, p j * s ^ j) * (∑' j, q j * t ^ j) < (∑' j, p j * t ^ j) * (∑' j, q j * s ^ j) := by
  have ht : 0 < t := hs.trans hst
  have hnp : ∀ u, 0 ≤ u → Summable fun j => ‖p j * u ^ j‖ := fun u hu =>
    (hps u hu).congr fun j => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu j)]
  have hnq : ∀ u, 0 ≤ u → Summable fun j => ‖q j * u ^ j‖ := fun u hu =>
    (hqs u hu).congr fun j => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq j).le (pow_nonneg hu j))]
  rw [tsum_mul_tsum_of_summable_norm (hnp s hs.le) (hnq t ht.le),
    tsum_mul_tsum_of_summable_norm (hnp t ht.le) (hnq s hs.le)]
  have hc := summable_mul_of_summable_norm (hnp s hs.le) (hnq t ht.le)
  have hc' := summable_mul_of_summable_norm (hnp t ht.le) (hnq s hs.le)
  have hd : Summable (ratioCross p q s t) := hc'.sub hc
  have hdswap : Summable fun z => ratioCross p q s t (Prod.swap z) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.2 hd
  have hswap : ∑' z, ratioCross p q s t (Prod.swap z) = ∑' z, ratioCross p q s t z :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (ratioCross p q s t)
  have he_eq : ∀ z : ℕ × ℕ, ratioCross p q s t z + ratioCross p q s t (Prod.swap z) =
      (p z.1 * q z.2 - p z.2 * q z.1) * (s ^ z.2 * t ^ z.1 - s ^ z.1 * t ^ z.2) := fun z => by
    simp only [ratioCross, Prod.fst_swap, Prod.snd_swap]; ring
  have he_nn : ∀ z : ℕ × ℕ, 0 ≤ ratioCross p q s t z + ratioCross p q s t (Prod.swap z) := by
    intro z
    rw [he_eq]
    rcases le_total z.1 z.2 with h | h
    · have h1 := hpq _ _ h
      have h2 := pow_mul_pow_sub_nonpos hs.le hst.le h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have h1 := hpq _ _ h
      have h2 := pow_mul_pow_sub_nonpos hs.le hst.le h
      exact mul_nonneg (by linarith) (by linarith)
  have he_pos : 0 < ratioCross p q s t (i₀, j₀) + ratioCross p q s t (Prod.swap (i₀, j₀)) := by
    rw [he_eq]
    have h2 := pow_mul_pow_sub_neg hs hst hij₀
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hpos := (hd.add hdswap).tsum_pos he_nn _ he_pos
  rw [hd.tsum_add hdswap, hswap] at hpos
  have hsub : ∑' z, ratioCross p q s t z =
      (∑' z : ℕ × ℕ, p z.1 * t ^ z.1 * (q z.2 * s ^ z.2)) -
        ∑' z : ℕ × ℕ, p z.1 * s ^ z.1 * (q z.2 * t ^ z.2) := hc'.tsum_sub hc
  linarith

/-- **Strict monotone ratio of odd factorial series.**  If `b_j > 0`, the ratios `a_j/b_j` are
nondecreasing and strictly increase between some `i₀ < j₀`, then `O_a/O_b` is strictly increasing
on positive clocks: `O_a(s) O_b(t) < O_a(t) O_b(s)` for `0 < s < t`. -/
theorem oddFactorialSeries_ratio_strictMono {a b : ℕ → ℝ} {M R M' R' : ℝ} (hR : 0 ≤ R)
    (hR' : 0 ≤ R') (ha : GeometricCoeffBound a M R) (hb : GeometricCoeffBound b M' R')
    (hbpos : ∀ j, 0 < b j) (hab : ∀ i j, i ≤ j → a i * b j ≤ a j * b i) {i₀ j₀ : ℕ}
    (hij₀ : i₀ < j₀) (hstrict : a i₀ * b j₀ < a j₀ * b i₀) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    oddFactorialSeries a s * oddFactorialSeries b t <
      oddFactorialSeries a t * oddFactorialSeries b s := by
  have hfac : ∀ j : ℕ, (0 : ℝ) < ((2 * j + 1).factorial : ℝ) := fun j => by
    exact_mod_cast Nat.factorial_pos _
  have hodd : ∀ (c : ℕ → ℝ) (x : ℝ), oddFactorialSeries c x =
      x * ∑' j, c j / ((2 * j + 1).factorial : ℝ) * (x ^ 2) ^ j := by
    intro c x
    unfold oddFactorialSeries
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [← pow_mul, pow_succ]; ring
  have hsum : ∀ (c : ℕ → ℝ) (Mc Rc : ℝ), 0 ≤ Rc → GeometricCoeffBound c Mc Rc → ∀ u, 0 ≤ u →
      Summable fun j => |c j / ((2 * j + 1).factorial : ℝ)| * u ^ j := by
    intro c Mc Rc hRc hc u hu
    have hMc : 0 ≤ Mc := by have := (abs_nonneg _).trans (hc 0); simpa using this
    refine ((Real.summable_pow_div_factorial (Rc * u)).mul_left Mc).of_nonneg_of_le
      (fun j => by positivity) fun j => ?_
    have hf2 : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have hfle : (j.factorial : ℝ) ≤ ((2 * j + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    rw [abs_div, abs_of_pos (hfac j), mul_pow]
    calc |c j| / ((2 * j + 1).factorial : ℝ) * u ^ j ≤ Mc * Rc ^ j / (j.factorial : ℝ) * u ^ j := by
          gcongr
          exact hc j
      _ = Mc * (Rc ^ j * u ^ j / (j.factorial : ℝ)) := by ring
  have hq : ∀ j, 0 < b j / ((2 * j + 1).factorial : ℝ) := fun j => div_pos (hbpos j) (hfac j)
  have hpq : ∀ i j, i ≤ j → a i / ((2 * i + 1).factorial : ℝ) * (b j / ((2 * j + 1).factorial : ℝ)) ≤
      a j / ((2 * j + 1).factorial : ℝ) * (b i / ((2 * i + 1).factorial : ℝ)) := by
    intro i j hij
    have h := hab i j hij
    rw [div_mul_div_comm, div_mul_div_comm, mul_comm ((2 * j + 1).factorial : ℝ)]
    exact div_le_div_of_nonneg_right h (mul_pos (hfac i) (hfac j)).le
  have hstr : a i₀ / ((2 * i₀ + 1).factorial : ℝ) * (b j₀ / ((2 * j₀ + 1).factorial : ℝ)) <
      a j₀ / ((2 * j₀ + 1).factorial : ℝ) * (b i₀ / ((2 * i₀ + 1).factorial : ℝ)) := by
    rw [div_mul_div_comm, div_mul_div_comm, mul_comm ((2 * j₀ + 1).factorial : ℝ)]
    exact div_lt_div_of_pos_right hstrict (mul_pos (hfac i₀) (hfac j₀))
  have hqs : ∀ u, 0 ≤ u → Summable fun j => b j / ((2 * j + 1).factorial : ℝ) * u ^ j :=
    fun u hu => (hsum b M' R' hR' hb u hu).congr fun j => by rw [abs_of_pos (hq j)]
  have hmain := powerSeries_ratio_strictMono hq hpq hij₀ hstr (hsum a M R hR ha) hqs
    (by positivity : 0 < s ^ 2) (by nlinarith : s ^ 2 < t ^ 2)
  rw [hodd a s, hodd b t, hodd a t, hodd b s]
  have ht : 0 < t := hs.trans hst
  have hst0 : 0 < s * t := mul_pos hs ht
  nlinarith [mul_lt_mul_of_pos_left hmain hst0]

/-- The antisymmetrized derivative cross term of two odd factorial series. -/
def oddDerivCross (a b : ℕ → ℝ) (t : ℝ) (z : ℕ × ℕ) : ℝ :=
  a z.1 * t ^ (2 * z.1 + 0) / ((2 * z.1 + 0).factorial : ℝ) *
      (b z.2 * t ^ (2 * z.2 + 1) / ((2 * z.2 + 1).factorial : ℝ)) -
    a z.1 * t ^ (2 * z.1 + 1) / ((2 * z.1 + 1).factorial : ℝ) *
      (b z.2 * t ^ (2 * z.2 + 0) / ((2 * z.2 + 0).factorial : ℝ))

private theorem summable_norm_term {a : ℕ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (ha : GeometricCoeffBound a M R) (t : ℝ) (k : ℕ) :
    Summable fun j => ‖a j * t ^ (2 * j + k) / ((2 * j + k).factorial : ℝ)‖ :=
  (summable_geometric_div_factorial (M := M) hR (abs_nonneg t) k).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun j => norm_oddEvenFactorialTerm_le ha le_rfl j k

/-- **Strict derivative cross inequality.**  Under the hypotheses of the ratio theorem,
`E_a(t) O_b(t) - O_a(t) E_b(t) > 0` for `t > 0`, i.e. `(O_a/O_b)' > 0` on positive clocks. -/
theorem oddFactorialSeries_deriv_cross_pos {a b : ℕ → ℝ} {M R M' R' : ℝ} (hR : 0 ≤ R)
    (hR' : 0 ≤ R') (ha : GeometricCoeffBound a M R) (hb : GeometricCoeffBound b M' R')
    (hab : ∀ i j, i ≤ j → a i * b j ≤ a j * b i) {i₀ j₀ : ℕ}
    (hij₀ : i₀ < j₀) (hstrict : a i₀ * b j₀ < a j₀ * b i₀) {t : ℝ} (ht : 0 < t) :
    oddFactorialSeries a t * evenFactorialSeries b t <
      evenFactorialSeries a t * oddFactorialSeries b t := by
  have hO : ∀ c : ℕ → ℝ, oddFactorialSeries c t =
      ∑' j, c j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := fun c => rfl
  have hE : ∀ c : ℕ → ℝ, evenFactorialSeries c t =
      ∑' j, c j * t ^ (2 * j + 0) / ((2 * j + 0).factorial : ℝ) := fun c => by
    unfold evenFactorialSeries; simp only [add_zero]
  rw [hO, hO, hE, hE, tsum_mul_tsum_of_summable_norm (summable_norm_term hR ha t 1)
      (summable_norm_term hR' hb t 0),
    tsum_mul_tsum_of_summable_norm (summable_norm_term hR ha t 0) (summable_norm_term hR' hb t 1)]
  have hc := summable_mul_of_summable_norm (summable_norm_term hR ha t 0)
    (summable_norm_term hR' hb t 1)
  have hc' := summable_mul_of_summable_norm (summable_norm_term hR ha t 1)
    (summable_norm_term hR' hb t 0)
  have hd : Summable (oddDerivCross a b t) := hc.sub hc'
  have hdswap : Summable fun z => oddDerivCross a b t (Prod.swap z) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.2 hd
  have hswap : ∑' z, oddDerivCross a b t (Prod.swap z) = ∑' z, oddDerivCross a b t z :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (oddDerivCross a b t)
  have hfac : ∀ n : ℕ, (0 : ℝ) < (n.factorial : ℝ) := fun n => by exact_mod_cast Nat.factorial_pos n
  have he_eq : ∀ z : ℕ × ℕ, oddDerivCross a b t z + oddDerivCross a b t (Prod.swap z) =
      2 * ((z.1 : ℝ) - z.2) * (a z.1 * b z.2 - a z.2 * b z.1) * t ^ (2 * z.1 + 2 * z.2 + 1) /
        (((2 * z.1 + 1).factorial : ℝ) * ((2 * z.2 + 1).factorial : ℝ)) := by
    intro z
    simp only [oddDerivCross, Prod.fst_swap, Prod.snd_swap, add_zero]
    have f1 : ((2 * z.1 + 1).factorial : ℝ) = (2 * z.1 + 1) * ((2 * z.1).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have f2 : ((2 * z.2 + 1).factorial : ℝ) = (2 * z.2 + 1) * ((2 * z.2).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [f1, f2]
    have h1 := hfac (2 * z.1)
    have h2 := hfac (2 * z.2)
    field_simp
    ring
  have hden : ∀ z : ℕ × ℕ, (0 : ℝ) < ((2 * z.1 + 1).factorial : ℝ) *
      ((2 * z.2 + 1).factorial : ℝ) := fun z => mul_pos (hfac _) (hfac _)
  have he_nn : ∀ z : ℕ × ℕ, 0 ≤ oddDerivCross a b t z + oddDerivCross a b t (Prod.swap z) := by
    intro z
    rw [he_eq]
    refine div_nonneg ?_ (hden z).le
    have htp : 0 ≤ t ^ (2 * z.1 + 2 * z.2 + 1) := pow_nonneg ht.le _
    rcases le_total z.1 z.2 with h | h
    · have h1 := hab _ _ h
      have h2 : ((z.1 : ℝ) - z.2) ≤ 0 := by have : (z.1 : ℝ) ≤ z.2 := by exact_mod_cast h
                                            linarith
      have := mul_nonneg_of_nonpos_of_nonpos h2 (by linarith : a z.1 * b z.2 - a z.2 * b z.1 ≤ 0)
      nlinarith
    · have h1 := hab _ _ h
      have h2 : 0 ≤ ((z.1 : ℝ) - z.2) := by have : (z.2 : ℝ) ≤ z.1 := by exact_mod_cast h
                                            linarith
      have := mul_nonneg h2 (by linarith : 0 ≤ a z.1 * b z.2 - a z.2 * b z.1)
      nlinarith
  have he_pos : 0 < oddDerivCross a b t (j₀, i₀) + oddDerivCross a b t (Prod.swap (j₀, i₀)) := by
    rw [he_eq]
    refine div_pos ?_ (hden _)
    have h2 : (0 : ℝ) < (j₀ : ℝ) - i₀ := by
      have : (i₀ : ℝ) < j₀ := by exact_mod_cast hij₀
      linarith
    have h3 : 0 < a j₀ * b i₀ - a i₀ * b j₀ := by linarith
    have htp : 0 < t ^ (2 * j₀ + 2 * i₀ + 1) := pow_pos ht _
    simp only
    positivity
  have hpos := (hd.add hdswap).tsum_pos he_nn _ he_pos
  rw [hd.tsum_add hdswap, hswap] at hpos
  have hsub : ∑' z, oddDerivCross a b t z =
      (∑' z : ℕ × ℕ, a z.1 * t ^ (2 * z.1 + 0) / ((2 * z.1 + 0).factorial : ℝ) *
        (b z.2 * t ^ (2 * z.2 + 1) / ((2 * z.2 + 1).factorial : ℝ))) -
      ∑' z : ℕ × ℕ, a z.1 * t ^ (2 * z.1 + 1) / ((2 * z.1 + 1).factorial : ℝ) *
        (b z.2 * t ^ (2 * z.2 + 0) / ((2 * z.2 + 0).factorial : ℝ)) := hc.tsum_sub hc'
  linarith

end GaloisForLFunctions.HTGeometry
