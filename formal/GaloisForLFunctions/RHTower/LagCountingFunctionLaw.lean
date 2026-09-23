import GaloisForLFunctions.RHTower.PowerLagLandauCriterion

/-!
# The counting-function law for lag subsequences

A nonnegative weight `c : ℕ → ℝ` with generating function `F(w) = Σ c(n) n^{−w}` (abscissa `α`)
decides the Riemann hypothesis one-sidedly as soon as `F` continues analytically a little to the
left of `α` away from the real axis with polynomial growth of exponent `A < 1`, and `‖F(α + t)‖ → ∞`
as `t → 0⁺`: if `a_n ≤ M` for every `n` in the support of `c`, then RH holds.

The mechanism is Landau's theorem for the nonnegative series `Σ c(n)(M − a_n) n^{−s}`, which equals
`M F(s) − Σ_ρ w_ρ F(s − ρ + ½)` for `Re s > α + Θ − ½`; the singularities of the right side are
the non-real points `α + ρ − ½`, so the abscissa moves left of a pole.  The `k`-th powers
(`F(w) = ζ(kw)`) and the prime powers weighted by `Λ` (`F = −ζ'/ζ`) are instances.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-! ## Summability of the weights against `(2 + |γ|)^A`, `A < 1` -/

theorem winLog_le_rpow_of_le {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    winLog k ≤ (2 / ε) * (k : ℝ) ^ ε := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hlog : Real.log ((k : ℝ) + 3) ≤ ((k : ℝ) + 3) ^ ε / ε :=
    Real.log_le_rpow_div (by linarith) hε
  have hle : (k : ℝ) + 3 ≤ 4 * k := by linarith
  have h4 : (4 : ℝ) ^ ε ≤ 3 / 2 := by
    calc (4 : ℝ) ^ ε ≤ (4 : ℝ) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hε4
      _ = ((3 / 2 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) * (4 / (3 / 2 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          congr 1
          field_simp
      _ ≤ 3 / 2 * 1 := by
          gcongr
          · rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
              Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
          · exact Real.rpow_le_one (by positivity) (by norm_num) (by norm_num)
      _ = 3 / 2 := by ring
  have hr : ((k : ℝ) + 3) ^ ε ≤ 3 / 2 * (k : ℝ) ^ ε := by
    calc ((k : ℝ) + 3) ^ ε ≤ (4 * (k : ℝ)) ^ ε := Real.rpow_le_rpow (by linarith) hle hε.le
      _ = (4 : ℝ) ^ ε * (k : ℝ) ^ ε := Real.mul_rpow (by norm_num) hk0
      _ ≤ 3 / 2 * (k : ℝ) ^ ε := by gcongr
  have h1 : (1 : ℝ) ≤ (k : ℝ) ^ ε := Real.one_le_rpow hk1 hε.le
  have hε' : 2 ≤ 1 / (2 * ε) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h2 : (2 : ℝ) ≤ 1 / (2 * ε) * (k : ℝ) ^ ε := by nlinarith
  have h3 : ((k : ℝ) + 3) ^ ε / ε ≤ 3 / (2 * ε) * (k : ℝ) ^ ε := by
    rw [div_le_iff₀ hε]
    calc ((k : ℝ) + 3) ^ ε ≤ 3 / 2 * (k : ℝ) ^ ε := hr
      _ = 3 / (2 * ε) * (k : ℝ) ^ ε * ε := by field_simp
  unfold winLog
  have e : (2 / ε : ℝ) = 3 / (2 * ε) + 1 / (2 * ε) := by field_simp; ring
  rw [e, add_mul]
  linarith

/-- On the window `k ≤ |γ| < k + 1` the weight times `(2 + |γ|)^A` is at most `4 k^A / k²`. -/
theorem weight_rpow_le_window {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    {q : XiZeroCopy} (hq : (k : ℝ) ≤ |zeroOrdinate q|) (hq' : |zeroOrdinate q| < k + 1) :
    ‖lagWeight q‖ * (2 + |zeroOrdinate q|) ^ A ≤ 4 * (k : ℝ) ^ A / (k : ℝ) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hw : ‖lagWeight q‖ ≤ 1 / (k : ℝ) ^ 2 := by
    refine (norm_lagWeight_le_inv_sq q).trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have : (k : ℝ) ^ 2 ≤ |zeroOrdinate q| ^ 2 := pow_le_pow_left₀ hk0.le hq 2
    rwa [sq_abs] at this
  have hs : (2 + |zeroOrdinate q|) ^ A ≤ 4 * (k : ℝ) ^ A := by
    calc (2 + |zeroOrdinate q|) ^ A ≤ (4 * (k : ℝ)) ^ A :=
          Real.rpow_le_rpow (by positivity) (by linarith) hA0
      _ = (4 : ℝ) ^ A * (k : ℝ) ^ A := Real.mul_rpow (by norm_num) hk0.le
      _ ≤ 4 * (k : ℝ) ^ A := by
          gcongr
          calc (4 : ℝ) ^ A ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hA
            _ = 4 := Real.rpow_one 4
  calc ‖lagWeight q‖ * (2 + |zeroOrdinate q|) ^ A
      ≤ 1 / (k : ℝ) ^ 2 * (4 * (k : ℝ) ^ A) := by gcongr
    _ = 4 * (k : ℝ) ^ A / (k : ℝ) ^ 2 := by ring

/-- `k^ε · k^A / k² = (k^{2 − A − ε})⁻¹`. -/
theorem rpow_mul_rpow_div_sq {k : ℕ} (hk : 1 ≤ k) (ε A : ℝ) :
    (k : ℝ) ^ ε * (k : ℝ) ^ A / (k : ℝ) ^ 2 = ((k : ℝ) ^ (2 - A - ε))⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.rpow_add hk0, ← Real.rpow_natCast, ← Real.rpow_sub hk0, ← Real.rpow_neg hk0.le]
  congr 1
  push_cast
  ring

/-- The window majorant for exponent `A`: `C_A k^{−(7 − 3A)/4}`. -/
def lagRpowMajorant (A : ℝ) (k : ℕ) : ℝ :=
  (240 + smallHeightCount) * (2 / ((1 - A) / 4)) * 4 * ((k : ℝ) ^ (2 - A - (1 - A) / 4))⁻¹

theorem lagRpowMajorant_nonneg {A : ℝ} (hA : A < 1) (k : ℕ) : 0 ≤ lagRpowMajorant A k := by
  unfold lagRpowMajorant
  have : 0 < 1 - A := by linarith
  positivity

theorem summable_lagRpowMajorant {A : ℝ} (hA : A < 1) : Summable (lagRpowMajorant A) := by
  unfold lagRpowMajorant
  refine Summable.mul_left _ ?_
  exact Real.summable_nat_rpow_inv.mpr (by linarith)

/-- **Summability of the weights against `(2 + |γ|)^A` for every `A < 1`.** -/
theorem summable_lagWeight_mul_rpow {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    Summable fun q : XiZeroCopy => ‖lagWeight q‖ * (2 + |zeroOrdinate q|) ^ A := by
  classical
  set ε : ℝ := (1 - A) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hε4 : ε ≤ 1 / 4 := by rw [hε]; linarith
  set W := ∑' q : XiZeroCopy, ‖lagWeight q‖ with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun q => norm_nonneg _
  set K₀ : ℝ := (smallHeightCount : ℝ) with hK₀
  have hK₀0 : 0 ≤ K₀ := Nat.cast_nonneg _
  set T := ∑' k : ℕ, lagRpowMajorant A k with hTdef
  refine summable_of_sum_le (c := 4 * W + T)
    (fun q => mul_nonneg (norm_nonneg _) (by positivity)) fun F => ?_
  set idx : XiZeroCopy → ℕ := fun q => ⌊|zeroOrdinate q|⌋₊ with hidx
  set f : XiZeroCopy → ℝ := fun q => ‖lagWeight q‖ * (2 + |zeroOrdinate q|) ^ A with hfdef
  set K := F.sup idx + 1 with hKdef
  have hmaps : ∀ q ∈ F, idx q ∈ Finset.range K := fun q hq =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := idx) hq))
  -- the window `0`
  have hwin0 : ∑ q ∈ F with idx q = 0, f q ≤ 4 * W := by
    have h1 : ∀ q ∈ F.filter (fun q => idx q = 0), f q ≤ 4 * ‖lagWeight q‖ := by
      intro q hq
      have hq0 : idx q = 0 := (Finset.mem_filter.mp hq).2
      have hlt : |zeroOrdinate q| < 1 := by
        have := Nat.lt_floor_add_one |zeroOrdinate q|
        rw [show ⌊|zeroOrdinate q|⌋₊ = idx q from rfl, hq0] at this
        simpa using this
      have hs : (2 + |zeroOrdinate q|) ^ A ≤ 4 := by
        calc (2 + |zeroOrdinate q|) ^ A ≤ (4 : ℝ) ^ A :=
              Real.rpow_le_rpow (by positivity) (by linarith) hA0
          _ ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hA.le
          _ = 4 := Real.rpow_one 4
      simp only [hfdef]
      have := mul_le_mul_of_nonneg_left hs (norm_nonneg (lagWeight q))
      linarith
    calc ∑ q ∈ F with idx q = 0, f q ≤ ∑ q ∈ F with idx q = 0, 4 * ‖lagWeight q‖ :=
          Finset.sum_le_sum h1
      _ = 4 * ∑ q ∈ F with idx q = 0, ‖lagWeight q‖ := by rw [Finset.mul_sum]
      _ ≤ 4 * W := by
          have hle : ∑ q ∈ F with idx q = 0, ‖lagWeight q‖ ≤ W := by
            rw [hWdef]
            exact summable_norm_lagWeight.sum_le_tsum (F.filter fun q => idx q = 0)
              (fun q _ => norm_nonneg (lagWeight q))
          linarith
  -- the windows `k ≥ 1`
  have hwin : ∀ k ∈ Finset.Ico 1 K, ∑ q ∈ F with idx q = k, f q ≤ lagRpowMajorant A k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hmem : ∀ q ∈ F.filter (fun q => idx q = k),
        (k : ℝ) ≤ |zeroOrdinate q| ∧ |zeroOrdinate q| < k + 1 := by
      intro q hq
      have hqk : idx q = k := (Finset.mem_filter.mp hq).2
      exact (Nat.floor_eq_iff (abs_nonneg _)).mp hqk
    have hcount := card_absWindow_le' k (F.filter (fun q => idx q = k)) hmem
    have hterm : ∀ q ∈ F.filter (fun q => idx q = k), f q ≤ 4 * (k : ℝ) ^ A / (k : ℝ) ^ 2 :=
      fun q hq => weight_rpow_le_window hA0 hA.le hk1 (hmem q hq).1 (hmem q hq).2
    have hwl := winLog_le_rpow_of_le hk1 hεpos hε4
    have hL0 : 0 ≤ winLog k := by linarith [winLog_ge_two k]
    have hid := rpow_mul_rpow_div_sq hk1 ε A
    calc ∑ q ∈ F with idx q = k, f q
        ≤ ((F.filter (fun q => idx q = k)).card : ℝ) * (4 * (k : ℝ) ^ A / (k : ℝ) ^ 2) := by
          rw [← nsmul_eq_mul]
          exact Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ (240 + K₀) * winLog k * (4 * (k : ℝ) ^ A / (k : ℝ) ^ 2) := by gcongr
      _ ≤ (240 + K₀) * ((2 / ε) * (k : ℝ) ^ ε) * (4 * (k : ℝ) ^ A / (k : ℝ) ^ 2) := by
          gcongr
      _ = (240 + K₀) * (2 / ε) * 4 * ((k : ℝ) ^ ε * (k : ℝ) ^ A / (k : ℝ) ^ 2) := by ring
      _ = lagRpowMajorant A k := by rw [hid]; rfl
  have hsplit : ∑ q ∈ F, f q = ∑ k ∈ Finset.range K, ∑ q ∈ F with idx q = k, f q :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hrange : ∑ k ∈ Finset.range K, ∑ q ∈ F with idx q = k, f q
      = ∑ q ∈ F with idx q = 0, f q + ∑ k ∈ Finset.Ico 1 K, ∑ q ∈ F with idx q = k, f q := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ K)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  have htail : ∑ k ∈ Finset.Ico 1 K, lagRpowMajorant A k ≤ T :=
    (summable_lagRpowMajorant hA).sum_le_tsum _ (fun k _ => lagRpowMajorant_nonneg hA k)
  calc ∑ q ∈ F, f q = _ := hsplit
    _ = _ := hrange
    _ ≤ 4 * W + ∑ k ∈ Finset.Ico 1 K, lagRpowMajorant A k :=
        add_le_add hwin0 (Finset.sum_le_sum hwin)
    _ ≤ 4 * W + T := by linarith

/-! ## Weight systems -/

/-- A nonnegative weight `c` with generating function `F(w) = Σ c(n) n^{−w}` of abscissa `α`, which
continues analytically to `Re w ≥ α − η₀` away from the real axis with growth exponent `A < 1`, and
which is unbounded along the real ray `α + t`, `t → 0⁺`. -/
structure LagWeightSystem where
  c : ℕ → ℝ
  F : ℂ → ℂ
  α : ℝ
  η₀ : ℝ
  A : ℝ
  c_nonneg : ∀ n, 0 ≤ c n
  η₀_pos : 0 < η₀
  A_nonneg : 0 ≤ A
  A_lt_one : A < 1
  hasSum : ∀ w : ℂ, α < w.re → HasSum (LSeries.term (fun n => (c n : ℂ)) w) (F w)
  differentiableAt_right : ∀ w : ℂ, α < w.re → DifferentiableAt ℂ F w
  far : ∀ g : ℝ, 0 < g → ∃ C : ℝ, ∀ w : ℂ, α - η₀ ≤ w.re → w.re ≤ α + 2 → g ≤ |w.im| →
    DifferentiableAt ℂ F w ∧ ‖F w‖ ≤ C * (1 + |w.im|) ^ A
  blowup : Tendsto (fun t : ℝ => ‖F ((α : ℂ) + t)‖) (𝓝[>] 0) atTop

namespace LagWeightSystem

variable (S : LagWeightSystem)

/-- The complex weight sequence. -/
def cC (n : ℕ) : ℂ := (S.c n : ℂ)

/-- The coefficient `c(n)(M − a_n)`. -/
def coeff (M : ℝ) (n : ℕ) : ℝ := S.c n * (M - integerLag n)

theorem coeff_nonneg {M : ℝ} (hM : ∀ n, S.c n ≠ 0 → integerLag n ≤ M) (n : ℕ) :
    0 ≤ S.coeff M n := by
  unfold coeff
  by_cases h : S.c n = 0
  · rw [h, zero_mul]
  · exact mul_nonneg (S.c_nonneg n) (by linarith [hM n h])

theorem summable_term {w : ℂ} (hw : S.α < w.re) : Summable (LSeries.term S.cC w) :=
  (S.hasSum w hw).summable

theorem tsum_term_eq {w : ℂ} (hw : S.α < w.re) : ∑' n, LSeries.term S.cC w n = S.F w :=
  (S.hasSum w hw).tsum_eq

/-- The terms are dominated by the terms at a real point to the left. -/
theorem norm_term_le {w : ℂ} {x : ℝ} (hw : x ≤ w.re) (n : ℕ) :
    ‖LSeries.term S.cC w n‖ ≤ ‖LSeries.term S.cC (x : ℂ) n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', norm_div, norm_div,
      Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast_cpow_of_pos hn]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hn1
    simp only [Complex.ofReal_re]
    exact hw

/-- The shifted argument `s − ρ + ½`. -/
def shift (q : XiZeroCopy) (s : ℂ) : ℂ := s - (q.1 : ℂ) + 1 / 2

theorem shift_re (q : XiZeroCopy) (s : ℂ) : (shift q s).re = s.re - (q.1 : ℂ).re + 1 / 2 := by
  unfold shift; simp

theorem shift_im (q : XiZeroCopy) (s : ℂ) : (shift q s).im = s.im - zeroOrdinate q := by
  unfold shift zeroOrdinate; simp

theorem le_shift_re {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (q : XiZeroCopy) (s : ℂ) :
    s.re - θ + 1 / 2 ≤ (shift q s).re := by
  rw [shift_re]; linarith [hθ q]

/-- The abscissa `α + θ − ½` of the coefficient series. -/
def absc (θ : ℝ) : ℝ := S.α + θ - 1 / 2

/-- The `n`-th term of the coefficient series, `n ≠ 0`. -/
theorem coeff_term_eq {M : ℝ} {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun j => (S.coeff M j : ℂ)) s n
      = (M : ℂ) * LSeries.term S.cC s n
        - ∑' q : XiZeroCopy, lagWeight q * LSeries.term S.cC (shift q s) n := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hne : ∀ z : ℂ, (n : ℂ) ^ z ≠ 0 := fun z => by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hnC h.1
  have hlag := integerLag_eq_tsum_cpow hn1
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    tsum_congr (fun q => by rw [LSeries.term_of_ne_zero hn])]
  unfold coeff cC
  rw [Complex.ofReal_mul, Complex.ofReal_sub, hlag]
  have hsum : Summable fun q : XiZeroCopy => lagWeight q * (n : ℂ) ^ ((q.1 : ℂ) - 1 / 2) :=
    summable_lagWeight_mul_cpow hn1
  have hpow : ∀ q : XiZeroCopy,
      (S.c n : ℂ) * (n : ℂ) ^ ((q.1 : ℂ) - 1 / 2) / (n : ℂ) ^ s
        = (S.c n : ℂ) / (n : ℂ) ^ shift q s := by
    intro q
    unfold shift
    rw [div_eq_div_iff (hne _) (hne _), mul_assoc, ← Complex.cpow_add _ _ hnC]
    congr 2
    ring
  rw [mul_sub, sub_div, ← tsum_mul_left, ← tsum_div_const]
  congr 1
  · ring
  · refine tsum_congr fun q => ?_
    rw [← hpow q]
    ring

/-- The shifted family is absolutely summable on `ℕ × copies` for `Re s > α + θ − ½`. -/
theorem summable_fam {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) {s : ℂ}
    (hs : S.absc θ < s.re) :
    Summable (fun p : ℕ × XiZeroCopy => lagWeight p.2 * LSeries.term S.cC (shift p.2 s) p.1) := by
  set x : ℝ := s.re - θ + 1 / 2 with hx
  have hxα : S.α < x := by unfold absc at hs; rw [hx]; linarith
  have hsum1 : Summable fun n => ‖LSeries.term S.cC (x : ℂ) n‖ := (S.summable_term (by simpa using hxα)).norm
  have h1 : Summable fun n : ℕ => ‖‖LSeries.term S.cC (x : ℂ) n‖‖ := by simpa using hsum1
  have h2 : Summable fun q : XiZeroCopy => ‖‖lagWeight q‖‖ := by simpa using summable_norm_lagWeight
  have hprodmaj := summable_mul_of_summable_norm
    (f := fun n : ℕ => ‖LSeries.term S.cC (x : ℂ) n‖)
    (g := fun q : XiZeroCopy => ‖lagWeight q‖) h1 h2
  refine Summable.of_norm_bounded hprodmaj fun p => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (S.norm_term_le (le_shift_re hθ p.2 s) p.1) (norm_nonneg _)

/-- **The coefficient series equals `M F(s) − Σ_ρ w_ρ F(s − ρ + ½)` on `Re s > α + θ − ½`.** -/
theorem LSeries_coeff_eq {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hθ2 : 1 / 2 ≤ θ)
    {M : ℝ} {s : ℂ} (hs : S.absc θ < s.re) :
    LSeries (fun n => (S.coeff M n : ℂ)) s
      = (M : ℂ) * S.F s - ∑' q : XiZeroCopy, lagWeight q * S.F (shift q s) := by
  have hsα : S.α < s.re := by unfold absc at hs; linarith
  have hreq : ∀ q : XiZeroCopy, S.α < (shift q s).re := fun q => by
    have := le_shift_re hθ q s
    unfold absc at hs
    linarith
  have hprod := S.summable_fam hθ hs
  have hrow : ∀ n, Summable fun q : XiZeroCopy => lagWeight q * LSeries.term S.cC (shift q s) n :=
    fun n => hprod.prod_factor n
  have hcol : ∀ q : XiZeroCopy, Summable fun n => lagWeight q * LSeries.term S.cC (shift q s) n :=
    fun q => (S.summable_term (hreq q)).mul_left _
  have hfib : Summable fun n => ∑' q : XiZeroCopy, lagWeight q * LSeries.term S.cC (shift q s) n :=
    (hprod.hasSum.prod_fiberwise fun n => (hrow n).hasSum).summable
  have hterm : ∀ n, LSeries.term (fun j => (S.coeff M j : ℂ)) s n
      = (M : ℂ) * LSeries.term S.cC s n
        - ∑' q : XiZeroCopy, lagWeight q * LSeries.term S.cC (shift q s) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero]
    · exact S.coeff_term_eq hn.ne'
  have hsumM : Summable fun n => (M : ℂ) * LSeries.term S.cC s n :=
    (S.summable_term hsα).mul_left _
  have hswap := Summable.tsum_comm'
    (f := fun (n : ℕ) (q : XiZeroCopy) => lagWeight q * LSeries.term S.cC (shift q s) n)
    hprod hrow hcol
  calc LSeries (fun n => (S.coeff M n : ℂ)) s
      = ∑' n, ((M : ℂ) * LSeries.term S.cC s n
          - ∑' q : XiZeroCopy, lagWeight q * LSeries.term S.cC (shift q s) n) :=
        tsum_congr hterm
    _ = (M : ℂ) * ∑' n, LSeries.term S.cC s n
          - ∑' n, ∑' q : XiZeroCopy, lagWeight q * LSeries.term S.cC (shift q s) n := by
        rw [Summable.tsum_sub hsumM hfib, tsum_mul_left]
    _ = (M : ℂ) * S.F s
          - ∑' q : XiZeroCopy, ∑' n, lagWeight q * LSeries.term S.cC (shift q s) n := by
        rw [S.tsum_term_eq hsα, hswap]
    _ = _ := by
        congr 1
        refine tsum_congr fun q => ?_
        rw [tsum_mul_left, S.tsum_term_eq (hreq q)]

/-- The coefficient series converges for `Re s > α + θ − ½`. -/
theorem coeff_LSeriesSummable {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hθ2 : 1 / 2 ≤ θ)
    {M : ℝ} {s : ℂ} (hs : S.absc θ < s.re) : LSeriesSummable (fun n => (S.coeff M n : ℂ)) s := by
  have hsα : S.α < s.re := by unfold absc at hs; linarith
  have hprod := S.summable_fam hθ hs
  have hrow : ∀ n, Summable fun q : XiZeroCopy => lagWeight q * LSeries.term S.cC (shift q s) n :=
    fun n => hprod.prod_factor n
  have hfib : Summable fun n => ∑' q : XiZeroCopy, lagWeight q * LSeries.term S.cC (shift q s) n :=
    (hprod.hasSum.prod_fiberwise fun n => (hrow n).hasSum).summable
  have hsumM : Summable fun n => (M : ℂ) * LSeries.term S.cC s n :=
    (S.summable_term hsα).mul_left _
  refine (hsumM.sub hfib).congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · exact (S.coeff_term_eq hn.ne').symm

end LagWeightSystem

namespace LagWeightSystem

variable (S : LagWeightSystem)

/-! ## The zero-side continuation -/

/-- The term of the copy `q`. -/
def term (q : XiZeroCopy) (s : ℂ) : ℂ := lagWeight q * S.F (shift q s)

/-- The zero-side continuation `M F(s) − Σ_ρ w_ρ F(s − ρ + ½)`. -/
def G (M : ℝ) (s : ℂ) : ℂ := (M : ℂ) * S.F s - ∑' q : XiZeroCopy, S.term q s

theorem LSeries_coeff_eq_G {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hθ2 : 1 / 2 ≤ θ)
    {M : ℝ} {s : ℂ} (hs : S.absc θ < s.re) :
    LSeries (fun n => (S.coeff M n : ℂ)) s = S.G M s :=
  S.LSeries_coeff_eq hθ hθ2 hs

/-- **The far-term bound.** -/
theorem norm_term_le_far {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) {η : ℝ}
    (hη : η ≤ S.η₀) {t₀ g : ℝ} (hg : 0 < g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ w : ℂ, S.α - S.η₀ ≤ w.re → w.re ≤ S.α + 2 → g / 2 ≤ |w.im| →
      DifferentiableAt ℂ S.F w ∧ ‖S.F w‖ ≤ C * (1 + |w.im|) ^ S.A)
    {s : ℂ} (hs1 : S.absc θ - η ≤ s.re) (hs2 : s.re ≤ S.α + 3 / 2) (hs3 : |s.im - t₀| ≤ g / 2)
    {q : XiZeroCopy} (hq : g ≤ |zeroOrdinate q - t₀|) :
    ‖S.term q s‖
      ≤ ‖lagWeight q‖ * (C * (1 + g / 2 + |t₀|) ^ S.A * (2 + |zeroOrdinate q|) ^ S.A) := by
  have hA0 := S.A_nonneg
  set w : ℂ := shift q s with hw
  have hre1 : S.α - S.η₀ ≤ w.re := by
    have := le_shift_re hθ q s
    rw [← hw] at this
    unfold absc at hs1
    linarith
  have hre2 : w.re ≤ S.α + 2 := by
    rw [hw, shift_re]
    have := xiZeroCopy_re_pos q
    linarith
  have him : w.im = s.im - zeroOrdinate q := by rw [hw, shift_im]
  have hsep : g / 2 ≤ |w.im| := by
    rw [him]
    have htri : |zeroOrdinate q - t₀| ≤ |zeroOrdinate q - s.im| + |s.im - t₀| := abs_sub_le _ _ _
    rw [abs_sub_comm (zeroOrdinate q) s.im] at htri
    linarith
  obtain ⟨-, hF⟩ := hC w hre1 hre2 hsep
  have hbase : 1 + |w.im| ≤ (1 + g / 2 + |t₀|) * (2 + |zeroOrdinate q|) := by
    rw [him]
    have h1 : |s.im - zeroOrdinate q| ≤ |s.im - t₀| + |t₀ - zeroOrdinate q| := abs_sub_le _ _ _
    rw [abs_sub_comm t₀] at h1
    have h2 : |zeroOrdinate q - t₀| ≤ |zeroOrdinate q| + |t₀| := abs_sub _ _
    have := abs_nonneg t₀
    have := abs_nonneg (zeroOrdinate q)
    nlinarith
  have hrpow : (1 + |w.im|) ^ S.A
      ≤ (1 + g / 2 + |t₀|) ^ S.A * (2 + |zeroOrdinate q|) ^ S.A := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hbase hA0
  unfold term
  rw [norm_mul, ← hw]
  calc ‖lagWeight q‖ * ‖S.F w‖ ≤ ‖lagWeight q‖ * (C * (1 + |w.im|) ^ S.A) := by gcongr
    _ ≤ ‖lagWeight q‖ * (C * ((1 + g / 2 + |t₀|) ^ S.A * (2 + |zeroOrdinate q|) ^ S.A)) := by
        gcongr
    _ = _ := by ring

/-- The far majorant is summable. -/
theorem summable_far_majorant (D : ℝ) :
    Summable fun q : XiZeroCopy => ‖lagWeight q‖ * (D * (2 + |zeroOrdinate q|) ^ S.A) := by
  have := (summable_lagWeight_mul_rpow S.A_nonneg S.A_lt_one).mul_left D
  refine this.congr fun q => ?_
  ring

theorem differentiableOn_term (q : XiZeroCopy) {U : Set ℂ}
    (hU : ∀ s ∈ U, DifferentiableAt ℂ S.F (shift q s)) : DifferentiableOn ℂ (S.term q) U := by
  intro s hs
  have h1 : DifferentiableAt ℂ (shift q) s := by
    unfold shift
    fun_prop
  exact (((hU s hs).comp s h1).const_mul _).differentiableWithinAt

/-- The far continuation constant delivered by `far` at gap `g/2`, made nonnegative. -/
theorem exists_far_const {g : ℝ} (hg : 0 < g) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ w : ℂ, S.α - S.η₀ ≤ w.re → w.re ≤ S.α + 2 → g / 2 ≤ |w.im| →
      DifferentiableAt ℂ S.F w ∧ ‖S.F w‖ ≤ C * (1 + |w.im|) ^ S.A := by
  obtain ⟨C, hC⟩ := S.far (g / 2) (by positivity)
  refine ⟨max C 0, le_max_right _ _, fun w h1 h2 h3 => ⟨(hC w h1 h2 h3).1, ?_⟩⟩
  refine (hC w h1 h2 h3).2.trans ?_
  gcongr
  exact le_max_left _ _

/-- Summability of the full family where the far terms are dominated. -/
theorem summable_term_family {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) {η : ℝ}
    (hη : η ≤ S.η₀) {t₀ g : ℝ} (hg : 0 < g)
    (hgap : ∀ q : XiZeroCopy, zeroOrdinate q ≠ t₀ → g ≤ |zeroOrdinate q - t₀|) {s : ℂ}
    (hs1 : S.absc θ - η ≤ s.re) (hs2 : s.re ≤ S.α + 3 / 2) (hs3 : |s.im - t₀| ≤ g / 2) :
    Summable fun q : XiZeroCopy => S.term q s := by
  obtain ⟨C, hC0, hC⟩ := S.exists_far_const hg
  have hfar : Summable fun q : ↑(sameOrdinate t₀)ᶜ => S.term q s :=
    Summable.of_norm_bounded ((S.summable_far_majorant (C * (1 + g / 2 + |t₀|) ^ S.A)).subtype _)
      fun q => S.norm_term_le_far hθ hη hg hC0 hC hs1 hs2 hs3 (hgap q.1 q.2)
  have hnear : Summable fun q : sameOrdinate t₀ => S.term q s := by
    haveI : Finite (sameOrdinate t₀) := (finite_sameOrdinate t₀).to_subtype
    exact Summable.of_finite
  exact summable_subtype_and_compl.mp ⟨hnear, hfar⟩

theorem tsum_term_split {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) {η : ℝ}
    (hη : η ≤ S.η₀) {t₀ g : ℝ} (hg : 0 < g)
    (hgap : ∀ q : XiZeroCopy, zeroOrdinate q ≠ t₀ → g ≤ |zeroOrdinate q - t₀|) {s : ℂ}
    (hs1 : S.absc θ - η ≤ s.re) (hs2 : s.re ≤ S.α + 3 / 2) (hs3 : |s.im - t₀| ≤ g / 2) :
    ∑' q, S.term q s
      = ∑ q ∈ (finite_sameOrdinate t₀).toFinset, S.term q s
        + ∑' q : ↑(sameOrdinate t₀)ᶜ, S.term q s := by
  have hsum := S.summable_term_family hθ hη hg hgap hs1 hs2 hs3
  rw [← hsum.tsum_subtype_add_tsum_subtype_compl (sameOrdinate t₀)]
  congr 1
  rw [← tsum_congr_set_coe (fun q => S.term q s) (Set.Finite.coe_toFinset (finite_sameOrdinate t₀))]
  exact Finset.tsum_subtype' _ (fun q => S.term q s)

/-- **The continuation is differentiable on an open set on which the far terms are dominated,
the `M`-term and the same-ordinate terms are differentiable.** -/
theorem differentiableOn_G {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) {η : ℝ}
    (hη : η ≤ S.η₀) {M : ℝ} {t₀ g : ℝ} (hg : 0 < g)
    (hgap : ∀ q : XiZeroCopy, zeroOrdinate q ≠ t₀ → g ≤ |zeroOrdinate q - t₀|) {U : Set ℂ}
    (hUopen : IsOpen U) (hUre : ∀ s ∈ U, S.absc θ - η ≤ s.re)
    (hUre' : ∀ s ∈ U, s.re ≤ S.α + 3 / 2) (hUim : ∀ s ∈ U, |s.im - t₀| ≤ g / 2)
    (hUM : ∀ s ∈ U, DifferentiableAt ℂ S.F s)
    (hS : ∀ q ∈ sameOrdinate t₀, ∀ s ∈ U, DifferentiableAt ℂ S.F (shift q s)) :
    DifferentiableOn ℂ (S.G M) U := by
  obtain ⟨C, hC0, hC⟩ := S.exists_far_const hg
  have hfun : ∀ s ∈ U, S.G M s
      = (M : ℂ) * S.F s
        - (∑ q ∈ (finite_sameOrdinate t₀).toFinset, S.term q s
          + ∑' q : ↑(sameOrdinate t₀)ᶜ, S.term q s) := by
    intro s hs
    unfold G
    rw [S.tsum_term_split hθ hη hg hgap (hUre s hs) (hUre' s hs) (hUim s hs)]
  refine DifferentiableOn.congr ?_ hfun
  have hM : DifferentiableOn ℂ (fun s : ℂ => (M : ℂ) * S.F s) U := fun s hs =>
    ((hUM s hs).const_mul _).differentiableWithinAt
  have hnearD : DifferentiableOn ℂ
      (fun s => ∑ q ∈ (finite_sameOrdinate t₀).toFinset, S.term q s) U := by
    have := DifferentiableOn.sum (𝕜 := ℂ) (s := U) (u := (finite_sameOrdinate t₀).toFinset)
      (A := fun q => S.term q) fun q hq => ?_
    · refine this.congr fun s _ => ?_
      simp [Finset.sum_apply]
    · have hqn : q ∈ sameOrdinate t₀ := (Set.Finite.mem_toFinset _).mp hq
      exact S.differentiableOn_term q fun s hs => hS q hqn s hs
  have hfarD : DifferentiableOn ℂ (fun s => ∑' q : ↑(sameOrdinate t₀)ᶜ, S.term q s) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun q : ↑(sameOrdinate t₀)ᶜ =>
        ‖lagWeight q‖ * (C * (1 + g / 2 + |t₀|) ^ S.A * (2 + |zeroOrdinate q|) ^ S.A))
      ?_ (fun q => ?_) hUopen
      (fun q s hs => S.norm_term_le_far hθ hη hg hC0 hC (hUre s hs) (hUre' s hs) (hUim s hs)
        (hgap q.1 q.2))
    · exact (S.summable_far_majorant (C * (1 + g / 2 + |t₀|) ^ S.A)).subtype _
    · refine S.differentiableOn_term q.1 fun s hs => ?_
      -- the shifted argument satisfies the far hypotheses
      have hre1 : S.α - S.η₀ ≤ (shift q.1 s).re := by
        have := le_shift_re hθ q.1 s
        have := hUre s hs
        unfold absc at *
        linarith
      have hre2 : (shift q.1 s).re ≤ S.α + 2 := by
        rw [shift_re]
        have := xiZeroCopy_re_pos q.1
        have := hUre' s hs
        linarith
      have hsep : g / 2 ≤ |(shift q.1 s).im| := by
        rw [shift_im]
        have hq := hgap q.1 q.2
        have h3 := hUim s hs
        have htri : |zeroOrdinate q.1 - t₀| ≤ |zeroOrdinate q.1 - s.im| + |s.im - t₀| :=
          abs_sub_le _ _ _
        rw [abs_sub_comm (zeroOrdinate q.1) s.im] at htri
        linarith
      exact (hC _ hre1 hre2 hsep).1
  exact hM.sub (hnearD.add hfarD)

end LagWeightSystem

/-! ## The Landau transfer step -/

theorem mul_div_self_of_pos {a b : ℝ} (ha : 0 < a) : a * (b / a) = b := by
  field_simp

/-- A ray parameter below three thresholds. -/
theorem exists_small_ray_parameter' {δ δ₂ : ℝ} (hδ : 0 < δ) (hδ₂ : 0 < δ₂) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < δ ∧ t₀ < δ₂ ∧ t₀ < 1 / 4 := by
  set m : ℝ := min δ (min δ₂ (1 / 4)) with hm
  have hmpos : 0 < m := lt_min hδ (lt_min hδ₂ (by norm_num))
  have h1 : m ≤ δ := min_le_left _ _
  have h2 : m ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : m ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  clear_value m
  exact ⟨m / 2, half_pos hmpos, by linarith, by linarith, by linarith⟩

namespace LagWeightSystem

variable (S : LagWeightSystem)

/-- **Landau transfer.**  Under `¬RH` and bounded lags on the support of `c`, the coefficient series
converges at a real point to the left of `α + Θ − ½`. -/
theorem transfer_step {M : ℝ} (hM : ∀ n, S.c n ≠ 0 → integerLag n ≤ M)
    (hRH : ¬ RiemannHypothesis) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 5 ∧ η ≤ S.η₀ ∧ η < zeroReSup - 1 / 2 ∧
      LSeriesSummable (fun n => (S.coeff M n : ℂ)) ((S.absc zeroReSup - η / 4 : ℝ) : ℂ) := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁ (re_le_zeroReSup q₁)
  have hΘ1 : Θ ≤ 1 := zeroReSup_le fun q => (xiZeroCopy_re_lt_one q).le
  have hη₀ := S.η₀_pos
  obtain ⟨g, hg, hgall⟩ := exists_pos_le_abs_ordinate_all
  set u₀ : ℝ := S.absc Θ with hu₀
  set η : ℝ := min (1 / 5) (min S.η₀ (min ((Θ - 1 / 2) / 2) (g / 6))) with hη
  have hηpos : 0 < η :=
    lt_min (by norm_num) (lt_min hη₀ (lt_min (by linarith) (by positivity)))
  have hη5 : η ≤ 1 / 5 := min_le_left _ _
  have hηη₀ : η ≤ S.η₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hηΘ : η ≤ (Θ - 1 / 2) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηg : η ≤ g / 6 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηΘ' : η < Θ - 1 / 2 := by linarith
  refine ⟨η, hηpos, hη5, hηη₀, hηΘ', ?_⟩
  have hsum : LSeriesSummable (fun n => (S.coeff M n : ℂ)) ((u₀ + η : ℝ) : ℂ) :=
    S.coeff_LSeriesSummable hθ hΘ12.le (by simp; linarith)
  set R : NNReal := ⟨5 * η / 2, by positivity⟩ with hR
  have hRval : (R : ℝ) = 5 * η / 2 := rfl
  set U : Set ℂ := powBox (u₀ - η) (u₀ + 5 * η) 0 (3 * η) with hU
  have hball : closedBall (((u₀ + η) + η : ℝ) : ℂ) (R : ℝ) ⊆ U := by
    intro s hs
    rw [mem_closedBall, Complex.dist_eq] at hs
    have hre := Complex.abs_re_le_norm (s - (((u₀ + η) + η : ℝ) : ℂ))
    have him := Complex.abs_im_le_norm (s - (((u₀ + η) + η : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    rw [hRval] at hs
    have h1 := (abs_le.mp (hre.trans hs)).1
    have h2 := (abs_le.mp (hre.trans hs)).2
    refine ⟨by linarith, by linarith, ?_⟩
    rw [sub_zero]
    linarith [him.trans hs]
  have hGd : DifferentiableOn ℂ (S.G M) (closedBall (((u₀ + η) + η : ℝ) : ℂ) (R : ℝ)) := by
    refine (S.differentiableOn_G (θ := Θ) hθ hηη₀ (M := M) (t₀ := 0) (g := g) hg
      (fun q _ => by rw [sub_zero]; exact hgall q) (U := U) (isOpen_powBox _ _ _ _)
      ?_ ?_ ?_ ?_ ?_).mono hball
    · intro s hs; exact hs.1.le
    · intro s hs
      have := hs.2.1
      rw [hu₀] at this; unfold absc at this
      linarith
    · intro s hs
      have := hs.2.2
      rw [sub_zero] at this ⊢
      linarith
    · intro s hs
      apply S.differentiableAt_right
      have := hs.1
      rw [hu₀] at this; unfold absc at this
      linarith
    · intro q hq
      exfalso
      exact zeroOrdinate_ne_zero' q hq
  have hagree : ∀ s : ℂ, u₀ + η < s.re →
      S.G M s = LSeries (fun n => (S.coeff M n : ℂ)) s := by
    intro s hs
    exact (S.LSeries_coeff_eq_G hθ hΘ12.le (by linarith)).symm
  exact landau_local_summability_transfer (a := S.coeff M) (S.coeff_nonneg hM)
    (σ₁ := u₀ + η) (h := η) hηpos hsum (R := R) (G := S.G M) hGd hagree
    (σ := u₀ - η / 4) (by rw [hRval]; linarith)

/-! ## The pole of the continuation at a maximal zero -/

/-- The singular point `α + ρ₀ − ½`. -/
def pole (q₀ : XiZeroCopy) : ℂ := (S.α : ℂ) + (q₀.1 : ℂ) - 1 / 2

theorem pole_re (q₀ : XiZeroCopy) : (S.pole q₀).re = S.α + (q₀.1 : ℂ).re - 1 / 2 := by
  unfold pole; simp

theorem pole_im (q₀ : XiZeroCopy) : (S.pole q₀).im = zeroOrdinate q₀ := by
  unfold pole zeroOrdinate; simp

theorem shift_pole_add (q q₀ : XiZeroCopy) (t : ℂ) :
    shift q (S.pole q₀ + t) = (S.α : ℂ) + t + ((q₀.1 : ℂ) - (q.1 : ℂ)) := by
  unfold shift pole; ring

/-- **The singularity of the continuation at a maximal zero.**  Along the ray `pole + t`, the
continuation is at least `‖W₀‖ · ‖F(α + t)‖ − C`. -/
theorem G_ray_lower_bound {θ η : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hη : η ≤ S.η₀)
    {M : ℝ} (q₀ : XiZeroCopy) (hβ₀ : θ - (q₀.1 : ℂ).re ≤ η) (hβ₀' : 1 / 2 < (q₀.1 : ℂ).re)
    (hmax : ∀ q : XiZeroCopy, zeroOrdinate q = zeroOrdinate q₀ → (q.1 : ℂ).re ≤ (q₀.1 : ℂ).re) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      ‖powAliasedWeight q₀‖ * ‖S.F ((S.α : ℂ) + t)‖ - C ≤ ‖S.G M (S.pole q₀ + t)‖ := by
  classical
  set ρ₀ : ℂ := (q₀.1 : ℂ) with hρ₀
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  set s₀ : ℂ := S.pole q₀ with hs₀
  have hs₀re : s₀.re = S.α + ρ₀.re - 1 / 2 := S.pole_re q₀
  have hs₀im : s₀.im = γ₀ := S.pole_im q₀
  have hρ₀1 : ρ₀.re < 1 := xiZeroCopy_re_lt_one q₀
  set N := (finite_sameOrdinate γ₀).toFinset with hN
  set N' := N.filter (fun q => ¬ (q.1 : ℂ) = ρ₀) with hN'
  obtain ⟨g, hg, hg1, hgap⟩ := exists_pos_le_ordinate_gap_all γ₀
  obtain ⟨C, hC0, hC⟩ := S.exists_far_const hg
  -- the `M` term on the closed segment
  have hMc : ContinuousOn (fun t : ℝ => (M : ℂ) * S.F (s₀ + t)) (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have hd : DifferentiableAt ℂ S.F (s₀ + t) := by
      apply S.differentiableAt_right
      simp only [Complex.add_re, Complex.ofReal_re, hs₀re]
      linarith [ht.1]
    have hc : ContinuousAt (fun t : ℝ => s₀ + (t : ℂ)) t :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    have hcomp := ContinuousAt.comp (g := S.F) (f := fun t : ℝ => s₀ + (t : ℂ)) hd.continuousAt hc
    exact (continuousAt_const.mul hcomp).continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hMc
  -- the non-aliased same-ordinate terms on the closed segment
  have hN'c : ContinuousOn (fun t : ℝ => ∑ q ∈ N', S.term q (s₀ + t)) (Icc (0 : ℝ) (1 / 4)) := by
    apply continuousOn_finsetSum
    intro q hq t ht
    rw [hN', Finset.mem_filter] at hq
    have hqne : (q.1 : ℂ) ≠ ρ₀ := hq.2
    have hqord : zeroOrdinate q = γ₀ := by
      have := hq.1; rw [hN, Set.Finite.mem_toFinset] at this; exact this
    have hle := hmax q hqord
    have hlt : (q.1 : ℂ).re < ρ₀.re := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        apply hqne
        apply Complex.ext
        · exact h
        · unfold zeroOrdinate at hqord; rw [hqord, hγ₀, hρ₀]; rfl
    have hd : DifferentiableAt ℂ S.F (shift q (s₀ + t)) := by
      apply S.differentiableAt_right
      rw [hs₀, S.shift_pole_add]
      simp
      linarith [ht.1]
    have hc : ContinuousAt (fun t : ℝ => shift q (s₀ + t)) t := by
      unfold shift; fun_prop
    have hcomp := ContinuousAt.comp (g := S.F) (f := fun t : ℝ => shift q (s₀ + t)) hd.continuousAt hc
    exact (continuousAt_const.mul hcomp).continuousWithinAt
  obtain ⟨B₃, hB₃⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hN'c
  -- the far tail
  set D : ℝ := C * (1 + g / 2 + |γ₀|) ^ S.A with hD
  set B₄ : ℝ := ∑' q : XiZeroCopy, ‖lagWeight q‖ * (D * (2 + |zeroOrdinate q|) ^ S.A) with hB₄
  refine ⟨B₂ + B₃ + B₄, fun t ht ht4 => ?_⟩
  -- the ray point satisfies the far-bound hypotheses
  have hs1 : S.absc θ - η ≤ (s₀ + t).re := by
    simp only [Complex.add_re, Complex.ofReal_re, hs₀re]
    unfold absc
    linarith
  have hs2 : (s₀ + t).re ≤ S.α + 3 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, hs₀re]
    linarith
  have hs3 : |(s₀ + t).im - γ₀| ≤ g / 2 := by
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, hs₀im, sub_self, abs_zero]
    positivity
  unfold G
  rw [S.tsum_term_split hθ hη hg hgap hs1 hs2 hs3]
  rw [← Finset.sum_filter_add_sum_filter_not N (fun q => (q.1 : ℂ) = ρ₀)]
  -- the aliased part
  have hal : ∑ q ∈ N.filter (fun q => (q.1 : ℂ) = ρ₀), S.term q (s₀ + t)
      = powAliasedWeight q₀ * S.F ((S.α : ℂ) + t) := by
    unfold powAliasedWeight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_filter] at hq
    unfold term
    rw [hs₀, S.shift_pole_add, hq.2]
    congr 2
    ring
  rw [hal]
  -- the far part
  have hfar : ‖∑' q : ↑(sameOrdinate γ₀)ᶜ, S.term q (s₀ + t)‖ ≤ B₄ := by
    have hmaj := S.summable_far_majorant D
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hmaj0 : ∀ q : XiZeroCopy, 0 ≤ ‖lagWeight q‖ * (D * (2 + |zeroOrdinate q|) ^ S.A) :=
      fun q => by positivity
    have hle : ∀ q : ↑(sameOrdinate γ₀)ᶜ, ‖S.term q (s₀ + t)‖
        ≤ ‖lagWeight q‖ * (D * (2 + |zeroOrdinate q|) ^ S.A) :=
      fun q => S.norm_term_le_far hθ hη hg hC0 hC hs1 hs2 hs3 (hgap q.1 q.2)
    have hsn : Summable fun q : ↑(sameOrdinate γ₀)ᶜ => ‖S.term q (s₀ + t)‖ :=
      Summable.of_nonneg_of_le (fun q => norm_nonneg _) hle (hmaj.subtype _)
    calc ‖∑' q : ↑(sameOrdinate γ₀)ᶜ, S.term q (s₀ + t)‖
        ≤ ∑' q : ↑(sameOrdinate γ₀)ᶜ, ‖S.term q (s₀ + t)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' q : ↑(sameOrdinate γ₀)ᶜ, ‖lagWeight q‖ * (D * (2 + |zeroOrdinate q|) ^ S.A) :=
          hsn.tsum_le_tsum hle (hmaj.subtype _)
      _ ≤ B₄ := Summable.tsum_subtype_le _ _ hmaj0 hmaj
  have hMt := hB₂ t ⟨ht.le, ht4⟩
  have hN't := hB₃ t ⟨ht.le, ht4⟩
  set A := (M : ℂ) * S.F (s₀ + t) with hA
  set Al := powAliasedWeight q₀ * S.F ((S.α : ℂ) + t) with hAl
  set Nt := ∑ q ∈ N.filter (fun q => ¬ (q.1 : ℂ) = ρ₀), S.term q (s₀ + t) with hNt
  set Fa := ∑' q : ↑(sameOrdinate γ₀)ᶜ, S.term q (s₀ + t) with hFa
  have hNt' : ‖Nt‖ ≤ B₃ := hN't
  have hAl' : ‖Al‖ = ‖powAliasedWeight q₀‖ * ‖S.F ((S.α : ℂ) + t)‖ := norm_mul _ _
  have key : ‖Al‖ ≤ ‖A‖ + ‖A - (Al + Nt + Fa)‖ + ‖Nt‖ + ‖Fa‖ := by
    have e : Al = A - (A - (Al + Nt + Fa)) - Nt - Fa := by ring
    calc ‖Al‖ = ‖A - (A - (Al + Nt + Fa)) - Nt - Fa‖ := by rw [← e]
      _ ≤ ‖A - (A - (Al + Nt + Fa))‖ + ‖Nt‖ + ‖Fa‖ := by
          have h1 := norm_sub_le (A - (A - (Al + Nt + Fa)) - Nt) Fa
          have h2 := norm_sub_le (A - (A - (Al + Nt + Fa))) Nt
          linarith
      _ ≤ ‖A‖ + ‖A - (Al + Nt + Fa)‖ + ‖Nt‖ + ‖Fa‖ := by
          linarith [norm_sub_le A (A - (Al + Nt + Fa))]
  linarith

/-! ## The law -/

/-- **The counting-function law.**  If the lag values are bounded above on the support of the
weight, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_lag_le {M : ℝ} (hM : ∀ n, S.c n ≠ 0 → integerLag n ≤ M) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨η, hηpos, hη5, hηη₀, hηΘ, hsumσ⟩ := S.transfer_step hM hRH
  obtain ⟨q₁', hq₁'⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁'⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁' (re_le_zeroReSup q₁')
  have hΘ1 : Θ ≤ 1 := zeroReSup_le fun q => (xiZeroCopy_re_lt_one q).le
  set c : ℕ → ℂ := fun n => (S.coeff M n : ℂ) with hc
  set u₀ : ℝ := S.absc Θ with hu₀
  set σ : ℝ := u₀ - η / 4 with hσ
  have habs : LSeries.abscissaOfAbsConv c ≤ (σ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsumσ.of_re_le_re (by simp; linarith)
  have hFd : ∀ z : ℂ, σ < z.re → DifferentiableAt ℂ (LSeries c) z := fun z hz =>
    (LSeries_analyticOnNhd c z
      (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz))).differentiableAt
  -- a copy near the top
  obtain ⟨q₁, hq₁⟩ := exists_re_gt_of_lt_zeroReSup (b := Θ - η / 8) (by linarith)
  -- a zero of maximal real part on the horizontal segment through `ρ₁`
  set ρ₁ : ℂ := (q₁.1 : ℂ) with hρ₁
  set K : Set ℂ := Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin : (xiZeroSet_weilLagFunctionCriterion ∩ K).Finite := finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
    refine ⟨xi_xiZeroCopy_eq_zero q₁, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, (xiZeroCopy_re_lt_one q₁).le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet_weilLagFunctionCriterion ∩ K, ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ₀mem.1
  have hρ₀K := hρ₀mem.2
  rw [hK, Complex.mem_reProdIm] at hρ₀K
  have hre₀ : Θ - η / 8 < ρ₀.re := lt_of_lt_of_le hq₁ hρ₀K.1.1
  have hre₀' : ρ₀.re < 1 := by have := xiZeroCopy_re_lt_one q₀; rwa [hq₀] at this
  have him₀ : ρ₀.im = ρ₁.im := le_antisymm hρ₀K.2.2 hρ₀K.2.1
  have hmaxq : ∀ q : XiZeroCopy, zeroOrdinate q = zeroOrdinate q₀ →
      (q.1 : ℂ).re ≤ (q₀.1 : ℂ).re := by
    intro q hq
    rw [hq₀]
    by_contra hlt
    push Not at hlt
    have hmemK : (q.1 : ℂ) ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
      refine ⟨xi_xiZeroCopy_eq_zero q, ?_⟩
      rw [hK, Complex.mem_reProdIm]
      refine ⟨⟨by linarith [hρ₀K.1.1], (xiZeroCopy_re_lt_one q).le⟩, ?_⟩
      have : (q.1 : ℂ).im = ρ₁.im := by
        unfold zeroOrdinate at hq; rw [hq, hq₀, him₀]
      rw [this]; exact ⟨le_rfl, le_rfl⟩
    have := hmax _ hmemK hlt.le
    linarith
  have hρ₀half : 1 / 2 < ρ₀.re := by linarith
  have hβ₀' : 1 / 2 < (q₀.1 : ℂ).re := by rw [hq₀]; exact hρ₀half
  have hβ₀ : Θ - (q₀.1 : ℂ).re ≤ η := by rw [hq₀]; linarith
  -- the singularity bound along the ray
  obtain ⟨C, hC⟩ := S.G_ray_lower_bound hθ hηη₀ (M := M) q₀ hβ₀ hβ₀' hmaxq
  -- the ray box, avoiding every same-ordinate singularity
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  have hγ₀im : ρ₀.im = γ₀ := by rw [hγ₀]; unfold zeroOrdinate; rw [hq₀]
  obtain ⟨g, hg, hg1, hgap⟩ := exists_pos_le_ordinate_gap_all γ₀
  set s₀ : ℂ := S.pole q₀ with hs₀
  have hs₀re : s₀.re = S.α + ρ₀.re - 1 / 2 := by rw [hs₀, S.pole_re, hq₀]
  have hs₀im : s₀.im = γ₀ := S.pole_im q₀
  have hs₀u₀ : u₀ - η / 8 < s₀.re := by
    rw [hs₀re, hu₀]; unfold absc; linarith
  have hs₀u₀' : s₀.re ≤ u₀ := by
    rw [hs₀re, hu₀]; unfold absc
    have := hθ q₀; rw [hq₀] at this
    linarith
  set r' : ℝ := g / 2 with hr'
  have hr'pos : 0 < r' := by positivity
  set U₀ : Set ℂ := powBox s₀.re (u₀ + 1) γ₀ r' with hU₀
  have hU₀open : IsOpen U₀ := isOpen_powBox _ _ _ _
  have hGd : DifferentiableOn ℂ (S.G M) U₀ := by
    refine S.differentiableOn_G (θ := Θ) hθ hηη₀ (M := M) (t₀ := γ₀) (g := g) hg hgap
      (U := U₀) hU₀open ?_ ?_ ?_ ?_ ?_
    · intro s hs; linarith [hs.1]
    · intro s hs
      have := hs.2.1
      rw [hu₀] at this; unfold absc at this
      linarith
    · intro s hs; exact hs.2.2.le
    · intro s hs
      apply S.differentiableAt_right
      have := hs.1
      rw [hs₀re] at this
      linarith
    · intro q hq s hs
      apply S.differentiableAt_right
      have hqord : zeroOrdinate q = γ₀ := hq
      have hle := hmaxq q hqord
      rw [hq₀] at hle
      rw [shift_re]
      have := hs.1
      rw [hs₀re] at this
      linarith
  -- the ray
  set ℓ : ℝ → ℂ := fun t => s₀ + t with hℓ
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  have hℓre : ∀ t : ℝ, (ℓ t).re = s₀.re + t := fun t => by rw [hℓ]; simp
  have hℓim : ∀ t : ℝ, (ℓ t).im = γ₀ := fun t => by rw [hℓ]; simp [hs₀im]
  set U : Set ℝ := Ioo (0 : ℝ) (1 / 4) with hU
  have hℓU₀ : ∀ t ∈ U, ℓ t ∈ U₀ := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [hℓre]; linarith [ht.1]
    · rw [hℓre]; linarith [ht.2]
    · rw [hℓim, sub_self, abs_zero]; exact hr'pos
  set V : Set ℂ := {z : ℂ | σ < z.re} with hV
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hFdiff : DifferentiableOn ℂ (LSeries c) V := fun z hz => (hFd z hz).differentiableWithinAt
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    show σ < (ℓ t).re
    rw [hℓre]; linarith [ht.1]
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => LSeries c (ℓ t)) U := fun t ht =>
    ((hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))).restrictScalars).comp (hℓan t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => S.G M (ℓ t)) U := fun t ht =>
    ((hGd.analyticAt (hU₀open.mem_nhds (hℓU₀ t ht))).restrictScalars).comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h18U : (1 / 8 : ℝ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hagree : ∀ s : ℂ, u₀ < s.re → LSeries c s = S.G M s := fun s hs =>
    S.LSeries_coeff_eq_G hθ hΘ12.le hs
  have hfg : (fun t : ℝ => LSeries c (ℓ t)) =ᶠ[𝓝 (1 / 8 : ℝ)] (fun t : ℝ => S.G M (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (by linarith : η / 8 < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1 / 4))
      fun t ht => ?_
    apply hagree
    rw [hℓre]
    linarith [ht.1]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconn h18U hfg
  -- continuity of the series at `s₀`
  have hs₀σ : σ < s₀.re := by rw [hσ]; linarith
  have hFcont : ContinuousAt (LSeries c) s₀ := (hFd s₀ hs₀σ).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 s₀) := by
    have : Tendsto (fun t : ℝ => s₀ + (t : ℂ)) (𝓝 0) (𝓝 (s₀ + ((0 : ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
    rwa [Complex.ofReal_zero, add_zero] at this
  have hcomp : Tendsto (fun t : ℝ => LSeries c (ℓ t)) (𝓝 0) (𝓝 (LSeries c s₀)) :=
    hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = ‖LSeries c s₀‖ + 1 := ⟨_, rfl⟩
  have hw : 0 < ‖powAliasedWeight q₀‖ := norm_powAliasedWeight_pos q₀
  -- the blow-up of `F` at `α`
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = (Bd + C + 1) / ‖powAliasedWeight q₀‖ := ⟨_, rfl⟩
  have hbig : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), Kc ≤ ‖S.F ((S.α : ℂ) + (t : ℂ))‖ :=
    S.blowup.eventually_ge_atTop Kc
  rw [eventually_nhdsWithin_iff] at hbig
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.mp hbig
  obtain ⟨t₀, ht₀pos, ht₀δ, ht₀δ₂, ht₀4⟩ := exists_small_ray_parameter' hδ hδ₂
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, ht₀4⟩
  have hFb : ‖LSeries c (ℓ t₀)‖ ≤ Bd := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖LSeries c (ℓ t₀)‖
        = ‖(LSeries c (ℓ t₀) - LSeries c s₀) + LSeries c s₀‖ := by congr 1; ring
      _ ≤ ‖LSeries c (ℓ t₀) - LSeries c s₀‖ + ‖LSeries c s₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖LSeries c s₀‖ := by linarith
      _ = Bd := by rw [hBd]; ring
  have hGb : Bd < ‖S.G M (ℓ t₀)‖ := by
    have h1 := hC t₀ ht₀pos ht₀4.le
    have hℓt : ℓ t₀ = S.pole q₀ + t₀ := rfl
    rw [hℓt]
    have hd₂ : dist t₀ 0 < δ₂ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ₂
    have hK := hδ₂' hd₂ ht₀pos
    have h2 : ‖powAliasedWeight q₀‖ * Kc ≤ ‖powAliasedWeight q₀‖ * ‖S.F ((S.α : ℂ) + t₀)‖ :=
      mul_le_mul_of_nonneg_left hK hw.le
    have h3 : ‖powAliasedWeight q₀‖ * Kc = Bd + C + 1 := by
      rw [hKc]; exact mul_div_self_of_pos hw
    linarith
  have hEq : LSeries c (ℓ t₀) = S.G M (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith

/-- **RH ⟺ the lag sequence is bounded above on the support of the weight.** -/
theorem riemannHypothesis_iff_lag_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n, S.c n ≠ 0 → integerLag n ≤ M := by
  constructor
  · intro h
    exact ⟨poleSharpConstant, fun n _ =>
      (abs_le.mp (abs_integerLag_le_of_riemannHypothesis h n)).2⟩
  · rintro ⟨M, hM⟩
    exact S.riemannHypothesis_of_lag_le hM

end LagWeightSystem

end

end RHTower
