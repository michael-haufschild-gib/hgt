import GaloisForLFunctions.RHTower.PrimeLagLandauCriterion
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound

/-!
# The lag sequence on the `k`-th powers: coefficient series and zero-side identity

For `k ≥ 1` and a bound `M`, the Dirichlet series `Σ_m (M − a_{m^k}) m^{−k} m^{−u}` has nonnegative
coefficients when `a_{m^k} ≤ M` for all `m ≥ 1`, converges for `Re u > k(θ − 3/2) + 1` when all zeros
have real part `≤ θ`, and equals

`M ζ(k + u) − Σ_ρ w_ρ ζ(u + 3k/2 − kρ)`

there.  The weights satisfy `Σ_ρ |w_ρ| √(2 + |γ|) < ∞` (local zero count), which makes the zero-side
sum locally uniformly convergent wherever the arguments stay right of `Re = ½` and away from `1`.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Summability of the weights against `√(2 + |γ|)` -/

theorem winLog_le_rpow_quarter {k : ℕ} (hk : 1 ≤ k) : winLog k ≤ 8 * (k : ℝ) ^ (1 / 4 : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hlog : Real.log ((k : ℝ) + 3) ≤ ((k : ℝ) + 3) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have hle : (k : ℝ) + 3 ≤ (3 / 2 : ℝ) ^ (4 : ℕ) * k := by norm_num; linarith
  have hr : ((k : ℝ) + 3) ^ (1 / 4 : ℝ) ≤ 3 / 2 * (k : ℝ) ^ (1 / 4 : ℝ) := by
    calc ((k : ℝ) + 3) ^ (1 / 4 : ℝ) ≤ ((3 / 2 : ℝ) ^ (4 : ℕ) * k) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hle (by norm_num)
      _ = ((3 / 2 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) * (k : ℝ) ^ (1 / 4 : ℝ) :=
          Real.mul_rpow (by positivity) hk0
      _ = 3 / 2 * (k : ℝ) ^ (1 / 4 : ℝ) := by
          congr 1
          rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) ≤ (k : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hk1 (by norm_num)
  unfold winLog
  linarith

/-- On the window `k ≤ |γ| < k + 1` the weight times `√(2 + |γ|)` is at most `2√k/k²`. -/
theorem weight_sqrt_le_window {k : ℕ} (hk : 1 ≤ k) {q : XiZeroCopy}
    (hq : (k : ℝ) ≤ |zeroOrdinate q|) (hq' : |zeroOrdinate q| < k + 1) :
    ‖lagWeight q‖ * Real.sqrt (2 + |zeroOrdinate q|) ≤ 2 * Real.sqrt k / (k : ℝ) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hw : ‖lagWeight q‖ ≤ 1 / (k : ℝ) ^ 2 := by
    refine (norm_lagWeight_le_inv_sq q).trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have : (k : ℝ) ^ 2 ≤ |zeroOrdinate q| ^ 2 := pow_le_pow_left₀ hk0.le hq 2
    rwa [sq_abs] at this
  have hs : Real.sqrt (2 + |zeroOrdinate q|) ≤ 2 * Real.sqrt k := by
    calc Real.sqrt (2 + |zeroOrdinate q|) ≤ Real.sqrt (4 * k) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt k := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  calc ‖lagWeight q‖ * Real.sqrt (2 + |zeroOrdinate q|)
      ≤ 1 / (k : ℝ) ^ 2 * (2 * Real.sqrt k) := by
        gcongr
    _ = 2 * Real.sqrt k / (k : ℝ) ^ 2 := by ring

/-- `k^{1/4} · √k / k² = (k^{5/4})⁻¹`. -/
theorem rpow_quarter_mul_sqrt_div_sq {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt k / (k : ℝ) ^ 2 = ((k : ℝ) ^ (5 / 4 : ℝ))⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk0, ← Real.rpow_natCast, ← Real.rpow_sub hk0,
    ← Real.rpow_neg hk0.le]
  norm_num

/-- The window majorant `16(240 + K₀) k^{−5/4}`. -/
def powMajorant (k : ℕ) : ℝ := 16 * (240 + smallHeightCount) * ((k : ℝ) ^ (5 / 4 : ℝ))⁻¹

theorem powMajorant_nonneg (k : ℕ) : 0 ≤ powMajorant k := by
  unfold powMajorant; positivity

theorem summable_powMajorant : Summable powMajorant :=
  (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4)).mul_left _

/-- **Summability of the weights against `√(2 + |γ|)`.** -/
theorem summable_lagWeight_mul_sqrt :
    Summable fun q : XiZeroCopy => ‖lagWeight q‖ * Real.sqrt (2 + |zeroOrdinate q|) := by
  classical
  set W := ∑' q : XiZeroCopy, ‖lagWeight q‖ with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun q => norm_nonneg _
  set K₀ : ℝ := (smallHeightCount : ℝ) with hK₀
  have hK₀0 : 0 ≤ K₀ := Nat.cast_nonneg _
  set T := ∑' k : ℕ, powMajorant k with hTdef
  refine summable_of_sum_le (c := 2 * W + T)
    (fun q => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) fun F => ?_
  set idx : XiZeroCopy → ℕ := fun q => ⌊|zeroOrdinate q|⌋₊ with hidx
  set f : XiZeroCopy → ℝ := fun q => ‖lagWeight q‖ * Real.sqrt (2 + |zeroOrdinate q|) with hfdef
  set K := F.sup idx + 1 with hKdef
  have hmaps : ∀ q ∈ F, idx q ∈ Finset.range K := fun q hq =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := idx) hq))
  -- the window `0`
  have hwin0 : ∑ q ∈ F with idx q = 0, f q ≤ 2 * W := by
    have h1 : ∀ q ∈ F.filter (fun q => idx q = 0), f q ≤ 2 * ‖lagWeight q‖ := by
      intro q hq
      have hq0 : idx q = 0 := (Finset.mem_filter.mp hq).2
      have hlt : |zeroOrdinate q| < 1 := by
        have := Nat.lt_floor_add_one |zeroOrdinate q|
        rw [show ⌊|zeroOrdinate q|⌋₊ = idx q from rfl, hq0] at this
        simpa using this
      have hs : Real.sqrt (2 + |zeroOrdinate q|) ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        linarith
      simp only [hfdef]
      have := mul_le_mul_of_nonneg_left hs (norm_nonneg (lagWeight q))
      linarith
    calc ∑ q ∈ F with idx q = 0, f q ≤ ∑ q ∈ F with idx q = 0, 2 * ‖lagWeight q‖ :=
          Finset.sum_le_sum h1
      _ = 2 * ∑ q ∈ F with idx q = 0, ‖lagWeight q‖ := by rw [Finset.mul_sum]
      _ ≤ 2 * W := by
          have hle : ∑ q ∈ F with idx q = 0, ‖lagWeight q‖ ≤ W := by
            rw [hWdef]
            exact summable_norm_lagWeight.sum_le_tsum (F.filter fun q => idx q = 0)
              (fun q _ => norm_nonneg (lagWeight q))
          linarith
  -- the windows `k ≥ 1`
  have hwin : ∀ k ∈ Finset.Ico 1 K, ∑ q ∈ F with idx q = k, f q ≤ powMajorant k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hmem : ∀ q ∈ F.filter (fun q => idx q = k),
        (k : ℝ) ≤ |zeroOrdinate q| ∧ |zeroOrdinate q| < k + 1 := by
      intro q hq
      have hqk : idx q = k := (Finset.mem_filter.mp hq).2
      exact (Nat.floor_eq_iff (abs_nonneg _)).mp hqk
    have hcount := card_absWindow_le' k (F.filter (fun q => idx q = k)) hmem
    have hterm : ∀ q ∈ F.filter (fun q => idx q = k), f q ≤ 2 * Real.sqrt k / (k : ℝ) ^ 2 :=
      fun q hq => weight_sqrt_le_window hk1 (hmem q hq).1 (hmem q hq).2
    have hwl := winLog_le_rpow_quarter hk1
    have hL0 : 0 ≤ winLog k := by linarith [winLog_ge_two k]
    have hid := rpow_quarter_mul_sqrt_div_sq hk1
    calc ∑ q ∈ F with idx q = k, f q
        ≤ ((F.filter (fun q => idx q = k)).card : ℝ) * (2 * Real.sqrt k / (k : ℝ) ^ 2) := by
          rw [← nsmul_eq_mul]
          exact Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ (240 + K₀) * winLog k * (2 * Real.sqrt k / (k : ℝ) ^ 2) := by gcongr
      _ ≤ (240 + K₀) * (8 * (k : ℝ) ^ (1 / 4 : ℝ)) * (2 * Real.sqrt k / (k : ℝ) ^ 2) := by
          gcongr
      _ = 16 * (240 + K₀) * ((k : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt k / (k : ℝ) ^ 2) := by ring
      _ = powMajorant k := by rw [hid]; rfl
  have hsplit : ∑ q ∈ F, f q = ∑ k ∈ Finset.range K, ∑ q ∈ F with idx q = k, f q :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hrange : ∑ k ∈ Finset.range K, ∑ q ∈ F with idx q = k, f q
      = ∑ q ∈ F with idx q = 0, f q + ∑ k ∈ Finset.Ico 1 K, ∑ q ∈ F with idx q = k, f q := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ K)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  have htail : ∑ k ∈ Finset.Ico 1 K, powMajorant k ≤ T :=
    summable_powMajorant.sum_le_tsum _ (fun k _ => powMajorant_nonneg k)
  calc ∑ q ∈ F, f q = _ := hsplit
    _ = _ := hrange
    _ ≤ 2 * W + ∑ k ∈ Finset.Ico 1 K, powMajorant k :=
        add_le_add hwin0 (Finset.sum_le_sum hwin)
    _ ≤ 2 * W + T := by linarith

/-! ## The coefficient series on the `k`-th powers -/

/-- The `k`-th power lag coefficient `(M − a_{m^k})/m^k` (zero at `m = 0`). -/
def powLagCoeff (k : ℕ) (M : ℝ) (m : ℕ) : ℝ := (M - integerLag (m ^ k)) / (m : ℝ) ^ k

theorem powLagCoeff_nonneg {k : ℕ} (hk : 1 ≤ k) {M : ℝ}
    (hM : ∀ m : ℕ, 1 ≤ m → integerLag (m ^ k) ≤ M) (m : ℕ) : 0 ≤ powLagCoeff k M m := by
  unfold powLagCoeff
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hk0 : k ≠ 0 := by omega
    simp [hk0]
  · exact div_nonneg (by linarith [hM m hm]) (by positivity)

/-- The abscissa `k(θ − 3/2) + 1` of the coefficient series. -/
def powAbscissa (k : ℕ) (θ : ℝ) : ℝ := k * (θ - 3 / 2) + 1

theorem abs_powLagCoeff_le {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hθ2 : 1 / 2 ≤ θ)
    (k : ℕ) {M : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    |powLagCoeff k M m| ≤ (|M| + lagWeightTotal) * (m : ℝ) ^ (powAbscissa k θ - 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmk : 1 ≤ m ^ k := Nat.one_le_pow _ _ hm
  have hW := lagWeightTotal_nonneg
  have ha := abs_integerLag_le_rpow hθ hmk (n := m ^ k)
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hm0.le] at ha
  have hpow1 : (1 : ℝ) ≤ (m : ℝ) ^ ((k : ℝ) * (θ - 1 / 2)) :=
    Real.one_le_rpow hm1 (mul_nonneg (Nat.cast_nonneg k) (by linarith))
  unfold powLagCoeff
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) ^ k), div_le_iff₀ (by positivity)]
  have hM' : |M| ≤ |M| * (m : ℝ) ^ ((k : ℝ) * (θ - 1 / 2)) := by
    have := abs_nonneg M
    nlinarith
  have hkey : (m : ℝ) ^ (powAbscissa k θ - 1) * (m : ℝ) ^ k = (m : ℝ) ^ ((k : ℝ) * (θ - 1 / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hm0]
    congr 1
    unfold powAbscissa
    ring
  calc |M - integerLag (m ^ k)| ≤ |M| + |integerLag (m ^ k)| := abs_sub _ _
    _ ≤ |M| * (m : ℝ) ^ ((k : ℝ) * (θ - 1 / 2)) + lagWeightTotal * (m : ℝ) ^ ((k : ℝ) * (θ - 1 / 2)) :=
        add_le_add hM' ha
    _ = (|M| + lagWeightTotal) * (m : ℝ) ^ ((k : ℝ) * (θ - 1 / 2)) := by ring
    _ = (|M| + lagWeightTotal) * (m : ℝ) ^ (powAbscissa k θ - 1) * (m : ℝ) ^ k := by
        rw [mul_assoc, hkey]

/-- The coefficient series converges for `Re u > k(θ − 3/2) + 1`. -/
theorem powLagCoeff_LSeriesSummable {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) (k : ℕ) {M : ℝ} {u : ℂ} (hu : powAbscissa k θ < u.re) :
    LSeriesSummable (fun m => (powLagCoeff k M m : ℂ)) u := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := powAbscissa k θ) hu
    ⟨|M| + lagWeightTotal, fun m hm => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_powLagCoeff_le hθ hθ2 k (Nat.pos_of_ne_zero hm)

/-! ## The identity with the zero-side expression -/

/-- The constant sequence `1`. -/
def oneSeq : ℕ → ℂ := fun _ => 1

theorem tsum_term_oneSeq_eq {w : ℂ} (hw : 1 < w.re) :
    ∑' n, LSeries.term oneSeq w n = riemannZeta w := by
  rw [← LSeries_one_eq_riemannZeta hw]
  rfl

theorem summable_term_oneSeq {w : ℂ} (hw : 1 < w.re) : Summable (LSeries.term oneSeq w) :=
  LSeriesSummable_one_iff.mpr hw

theorem norm_term_oneSeq_le {w : ℂ} {ε' : ℝ} (hw : 1 + ε' ≤ w.re) (n : ℕ) :
    ‖LSeries.term oneSeq w n‖ ≤ ‖LSeries.term oneSeq ((1 + ε' : ℝ) : ℂ) n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', norm_div, norm_div,
      Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast_cpow_of_pos hn]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hn1
    simp only [Complex.ofReal_re]
    exact hw

/-- The shifted argument `u + 3k/2 − kρ`. -/
def powShift (k : ℕ) (q : XiZeroCopy) (u : ℂ) : ℂ := u + 3 * k / 2 - k * (q.1 : ℂ)

theorem powShift_re (k : ℕ) (q : XiZeroCopy) (u : ℂ) :
    (powShift k q u).re = u.re + 3 * k / 2 - k * (q.1 : ℂ).re := by
  unfold powShift; simp

theorem powShift_im (k : ℕ) (q : XiZeroCopy) (u : ℂ) :
    (powShift k q u).im = u.im - k * zeroOrdinate q := by
  unfold powShift zeroOrdinate; simp

theorem one_add_le_powShift_re {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (k : ℕ)
    (q : XiZeroCopy) (u : ℂ) : 1 + (u.re - powAbscissa k θ) ≤ (powShift k q u).re := by
  rw [powShift_re]
  unfold powAbscissa
  have := hθ q
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- The `m`-th term of the coefficient series, `m ≠ 0`. -/
theorem powLagCoeff_term_eq (k : ℕ) {M : ℝ} {u : ℂ} {m : ℕ} (hm : m ≠ 0) :
    LSeries.term (fun j => (powLagCoeff k M j : ℂ)) u m
      = (M : ℂ) * LSeries.term oneSeq ((k : ℂ) + u) m
        - ∑' q : XiZeroCopy, lagWeight q * LSeries.term oneSeq (powShift k q u) m := by
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm
  have hmk : 1 ≤ m ^ k := Nat.one_le_pow _ _ hm1
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hlag := integerLag_eq_tsum_cpow hmk
  rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hm,
    tsum_congr (fun q => by rw [LSeries.term_of_ne_zero hm])]
  simp only [oneSeq]
  unfold powLagCoeff
  rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_natCast, hlag]
  -- `((m^k : ℂ))^(ρ − ½) = m^(k(ρ − ½))`
  have hcp : ∀ q : XiZeroCopy, ((m : ℂ) ^ k) ^ ((q.1 : ℂ) - 1 / 2)
      = (m : ℂ) ^ ((k : ℂ) * ((q.1 : ℂ) - 1 / 2)) := fun q =>
    (Complex.natCast_cpow_natCast_mul m k _).symm
  simp only [Nat.cast_pow, hcp]
  have hne : ∀ z : ℂ, (m : ℂ) ^ z ≠ 0 := fun z => by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hmC h.1
  have hpow : ∀ q : XiZeroCopy,
      (m : ℂ) ^ ((k : ℂ) * ((q.1 : ℂ) - 1 / 2)) / ((m : ℂ) ^ k * (m : ℂ) ^ u)
        = 1 / (m : ℂ) ^ powShift k q u := by
    intro q
    unfold powShift
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hmC, div_eq_div_iff (hne _) (hne _),
      one_mul, ← Complex.cpow_add _ _ hmC]
    congr 1
    ring
  have hM : (M : ℂ) / ((m : ℂ) ^ k * (m : ℂ) ^ u) = (M : ℂ) * (1 / (m : ℂ) ^ ((k : ℂ) + u)) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hmC, mul_one_div]
  rw [div_div, sub_div, ← tsum_div_const, hM]
  congr 1
  refine tsum_congr fun q => ?_
  rw [mul_div_assoc, hpow q]

/-- The shifted family is absolutely summable on `ℕ × copies`. -/
theorem summable_powFam {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (k : ℕ) {u : ℂ}
    (hu : powAbscissa k θ < u.re) :
    Summable (fun p : ℕ × XiZeroCopy =>
      lagWeight p.2 * LSeries.term oneSeq (powShift k p.2 u) p.1) := by
  set ε' : ℝ := u.re - powAbscissa k θ with hε'
  have hε'pos : 0 < ε' := by rw [hε']; linarith
  have hreq' : ∀ q : XiZeroCopy, 1 + ε' ≤ (powShift k q u).re := fun q =>
    one_add_le_powShift_re hθ k q u
  have hsum1 : Summable fun n => ‖LSeries.term oneSeq ((1 + ε' : ℝ) : ℂ) n‖ :=
    (summable_term_oneSeq (by simp; linarith)).norm
  have h1 : Summable fun n : ℕ => ‖‖LSeries.term oneSeq ((1 + ε' : ℝ) : ℂ) n‖‖ := by
    simpa using hsum1
  have h2 : Summable fun q : XiZeroCopy => ‖‖lagWeight q‖‖ := by
    simpa using summable_norm_lagWeight
  have hprodmaj := summable_mul_of_summable_norm
    (f := fun n : ℕ => ‖LSeries.term oneSeq ((1 + ε' : ℝ) : ℂ) n‖)
    (g := fun q : XiZeroCopy => ‖lagWeight q‖) h1 h2
  refine Summable.of_norm_bounded hprodmaj fun p => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_term_oneSeq_le (hreq' p.2) p.1) (norm_nonneg _)

/-- **The coefficient series equals the zero-side expression on `Re u > k(θ − 3/2) + 1`.** -/
theorem LSeries_powLagCoeff_eq {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hθ2 : 1 / 2 ≤ θ)
    (k : ℕ) {M : ℝ} {u : ℂ} (hu : powAbscissa k θ < u.re) :
    LSeries (fun m => (powLagCoeff k M m : ℂ)) u
      = (M : ℂ) * riemannZeta ((k : ℂ) + u)
        - ∑' q : XiZeroCopy, lagWeight q * riemannZeta (powShift k q u) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hre1 : 1 < ((k : ℂ) + u).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    unfold powAbscissa at hu
    nlinarith
  have hreq : ∀ q : XiZeroCopy, 1 < (powShift k q u).re := fun q => by
    have := one_add_le_powShift_re hθ k q u
    linarith
  have hprod := summable_powFam hθ k hu
  have hrow : ∀ n, Summable fun q : XiZeroCopy =>
      lagWeight q * LSeries.term oneSeq (powShift k q u) n :=
    fun n => hprod.prod_factor n
  have hcol : ∀ q : XiZeroCopy, Summable fun n =>
      lagWeight q * LSeries.term oneSeq (powShift k q u) n :=
    fun q => (summable_term_oneSeq (hreq q)).mul_left _
  have hfib : Summable fun n => ∑' q : XiZeroCopy,
      lagWeight q * LSeries.term oneSeq (powShift k q u) n :=
    (hprod.hasSum.prod_fiberwise fun n => (hrow n).hasSum).summable
  have hterm : ∀ n, LSeries.term (fun j => (powLagCoeff k M j : ℂ)) u n
      = (M : ℂ) * LSeries.term oneSeq ((k : ℂ) + u) n
        - ∑' q : XiZeroCopy, lagWeight q * LSeries.term oneSeq (powShift k q u) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero]
    · exact powLagCoeff_term_eq k hn.ne'
  have hsumM : Summable fun n => (M : ℂ) * LSeries.term oneSeq ((k : ℂ) + u) n :=
    (summable_term_oneSeq hre1).mul_left _
  have hswap := Summable.tsum_comm'
    (f := fun (n : ℕ) (q : XiZeroCopy) =>
      lagWeight q * LSeries.term oneSeq (powShift k q u) n) hprod hrow hcol
  calc LSeries (fun m => (powLagCoeff k M m : ℂ)) u
      = ∑' n, ((M : ℂ) * LSeries.term oneSeq ((k : ℂ) + u) n
          - ∑' q : XiZeroCopy, lagWeight q * LSeries.term oneSeq (powShift k q u) n) :=
        tsum_congr hterm
    _ = (M : ℂ) * ∑' n, LSeries.term oneSeq ((k : ℂ) + u) n
          - ∑' n, ∑' q : XiZeroCopy, lagWeight q * LSeries.term oneSeq (powShift k q u) n := by
        rw [Summable.tsum_sub hsumM hfib, tsum_mul_left]
    _ = (M : ℂ) * riemannZeta ((k : ℂ) + u)
          - ∑' q : XiZeroCopy, ∑' n, lagWeight q * LSeries.term oneSeq (powShift k q u) n := by
        rw [tsum_term_oneSeq_eq hre1, hswap]
    _ = _ := by
        congr 1
        refine tsum_congr fun q => ?_
        rw [tsum_mul_left, tsum_term_oneSeq_eq (hreq q)]

end

end RHTower
