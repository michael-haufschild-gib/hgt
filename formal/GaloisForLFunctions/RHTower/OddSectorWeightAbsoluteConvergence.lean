import GaloisForLFunctions.RHTower.OddSectorPoleFreeLogDensity
import GaloisForLFunctions.RHTower.WeilPrimitiveSetMeanSquare

/-!
# Odd-positive weights converge absolutely on `Re s > 1`

**Theorem** (`summable_abs_div_rpow_of_weilPositiveOddAt`).  If `lam` is Weil-positive at a pole
weight `β ≥ 0` on the autocorrelations of odd compactly supported `C²` tests, then
`Σ |lam(n)| n^{−σ} < ∞` for every `σ > 1`.

The two signs of `lam` are controlled by different tests.
* *Positive part* (`odd_sum_posPart_sq_Ioc_le`).  The odd Weil–Toeplitz bound holds for every
  nonnegative coefficient vector (`odd_toeplitz_bound_nonneg`).  The star resonator
  `δ₁ + t Σ_{n ∈ S} lam(n) n^{−1/2} δ_n` on a primitive set `S` where `lam ≥ 0` has nonnegative
  coefficients, so `Σ_{n ∈ S} lam(n)²/n ≤ (log N + C₀)²`, and on the dyadic block `(N, 2N]` the
  positive part has `Σ lam⁺(n)² ≤ 2N (log 2N + C₀)²`.
* *Negative part* (`odd_sum_negPart_Ioc_le`).  The odd far bump `φ(· − a) − φ(· + a)` has pole term
  `−2(e^{a/2} − e^{−a/2})² J²`, `J = ∫ φ(x) e^{−x/2} dx`, and meets the atoms only at
  `log n ≈ 2a`, through the smoothed sum `S(a) = Σ_n lam(n) n^{−1/2} k(log n − 2a)`,
  `k = φ ⋆ φ̃ ≥ 0`.  Odd positivity at `β ≥ 0` gives `S(a) ≥ β(e^a − 2)J² − A₀`
  (`farSum_ge`).  Covering a dyadic block by finitely many windows on which `k` is bounded below,
  the negative part is dominated by the positive part plus `O(1)` per window.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.OddSector

open ResonatorProfile EvenSector WeilOneSided WeilMeanSquare WeilSpectral WeilPoleWeight

/-! ## The odd Weil–Toeplitz bound for nonnegative coefficients -/

/-- Odd positivity at any pole weight gives the Toeplitz hypothesis on every odd resonator with
nonnegative coefficients. -/
theorem integral_weilAtomSymbol_oddResonator_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) (N : ℕ) (c : ℕ → ℝ) (hc0 : ∀ m, 0 ≤ c m) :
    0 ≤ ∫ τ : ℝ, ‖paperFT (profileResonator N (fun m => (c m : ℂ))
        (gR' (1 / ((N : ℝ) + 1)))) τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * (Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4))⌋₊
        (τ / (2 * π)) := by
  have hw : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨hp1, hp2⟩ := paperFT_profileResonator_gR'_pole N (fun m => (c m : ℂ)) hw
  have ha : 0 ≤ Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4 := by
    have := Real.log_natCast_nonneg N
    positivity
  have hd : ContDiff ℝ 2 (profileResonator N (fun m => (c m : ℂ)) (gR' (1 / ((N : ℝ) + 1)))) :=
    contDiff_profileResonator N _ (contDiff_gR' _ 2)
  refine integral_weilAtomSymbol_nonneg_of_polar ha hd
    (tsupport_subset_of_vanish fun u hu => sum_translates_eq_zero
      (h := fun v => ((gR' (1 / ((N : ℝ) + 1)) v : ℝ) : ℂ))
      (fun v hv => by
        show ((gR' (1 / ((N : ℝ) + 1)) v : ℝ) : ℂ) = 0
        rw [gR'_eq_zero hw hv, Complex.ofReal_zero]) hu) hp1 hp2 ?_
  have hgc : HasCompactSupport (gR (1 / ((N : ℝ) + 1))) :=
    (hasCompactSupport_comp_left (g := Complex.ofReal) fun {_} => Complex.ofReal_eq_zero).mp
      (hasCompactSupport_gC hw)
  have e : profileResonator N (fun m => (c m : ℂ)) (gR' (1 / ((N : ℝ) + 1))) =
      fun u => ((∑ m ∈ Finset.Icc 1 N, c m *
        deriv (gR (1 / ((N : ℝ) + 1))) (u - resPt N m) : ℝ) : ℂ) := by
    funext u
    unfold profileResonator
    rw [Complex.ofReal_sum, deriv_gR]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.ofReal_mul]
  rw [e]
  exact re_weilFullFunctional_derivTranslateSum_nonneg_of_weilPositiveOddAt h (Finset.Icc 1 N)
    (fun m _ => hc0 m) (resPt N) (contDiff_gR _ 3) hgc (gR_neg _) (paperFT_gC_pole hw).1

/-- The odd Toeplitz constant `C₀' = log 2 + 9/2 + K'/2`. -/
def oddToeplitzConst : ℝ := Real.log 2 + 9 / 2 + oddProfileRatio / 2

/-- **The odd Weil–Toeplitz bound for nonnegative coefficients.** -/
theorem odd_toeplitz_bound_nonneg {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {N : ℕ}
    (hN : 1 ≤ N) (c : ℕ → ℝ) (hc0 : ∀ m, 0 ≤ c m) (hc : ∀ m, N < m → c m = 0) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m ≤
      (Real.log N + oddToeplitzConst) * ∑ m ∈ Finset.Icc 1 N, c m ^ 2 := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hw : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hw1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hN1]; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  have hcC : ∀ m, N < m → (c m : ℂ) = 0 := fun m hm => by rw [hc m hm, Complex.ofReal_zero]
  have hq0 : 0 < ∫ u, gR' (1 / ((N : ℝ) + 1)) u ^ 2 :=
    lt_of_lt_of_le (div_pos integral_d3_sq_pos (by positivity)) (integral_gR'_sq_ge hw)
  have hK : (1 / ((N : ℝ) + 1)) ^ 2 * ∫ u, deriv (gR' (1 / ((N : ℝ) + 1))) u ^ 2 ≤
      oddProfileRatio * ∫ u, gR' (1 / ((N : ℝ) + 1)) u ^ 2 := by
    rw [deriv_gR']; exact sq_mul_integral_gR''_le hw hw1
  have hb := weil_multiplicativeToeplitz_bound_of_profile hN (fun m => (c m : ℂ)) hcC
    (contDiff_gR' _ 3) (fun u hu => gR'_eq_zero hw hu) hq0 hK
    (integral_weilAtomSymbol_oddResonator_nonneg h N c hc0)
  have hl : ∀ n, (∑ m ∈ Finset.Icc 1 N, (c (n * m) : ℂ) * conj (c m : ℂ)).re =
      ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m := fun n => by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hr : ∑ m ∈ Finset.Icc 1 N, ‖(c m : ℂ)‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, c m ^ 2 :=
    Finset.sum_congr rfl fun m _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hl, hr] at hb
  exact hb

/-! ## Mean square of the positive part -/

/-- **Odd positivity bounds the weights in mean square on primitive sets where they are
nonnegative.** -/
theorem odd_sum_sq_div_le_of_primitive {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {N : ℕ}
    (hN : 1 ≤ N) :
    0 ≤ Real.log N + oddToeplitzConst ∧
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S → (∀ n ∈ S, 0 ≤ lam n) →
        ∑ n ∈ S, lam n ^ 2 / n ≤ (Real.log N + oddToeplitzConst) ^ 2 := by
  have key : ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S → (∀ n ∈ S, 0 ≤ lam n) →
      ∀ t : ℝ, 0 ≤ t → 2 * t * ∑ n ∈ S, lam n ^ 2 / n ≤
        (Real.log N + oddToeplitzConst) * (1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n) := by
    intro S hS hprim hpos t ht
    set c : ℕ → ℝ := fun m => if m = 1 then 1 else if m ∈ S then t * lam m / Real.sqrt m else 0
      with hc
    have hc0 : ∀ m, 0 ≤ c m := fun m => by
      simp only [hc]
      split_ifs with h1 h2
      · norm_num
      · exact div_nonneg (mul_nonneg ht (hpos m h2)) (Real.sqrt_nonneg _)
      · exact le_rfl
    have hcN : ∀ m, N < m → c m = 0 := by
      intro m hm
      have h1 : m ≠ 1 := by omega
      have h2 : m ∉ S := fun h' => by have := (Finset.mem_Icc.mp (hS h')).2; omega
      simp [hc, h1, h2]
    have hb := odd_toeplitz_bound_nonneg h hN c hc0 hcN
    have hinner : ∀ n ∈ Finset.Icc 2 N,
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m = if n ∈ S then t * lam n / Real.sqrt n else 0 := by
      intro n hn
      obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hrest : ∑ m ∈ (Finset.Icc 1 N).erase 1, c (n * m) * c m = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        obtain ⟨hm1, hmI⟩ := Finset.mem_erase.mp hm
        by_cases hmS : m ∈ S
        · have hnm1 : n * m ≠ 1 := by
            have := (Finset.mem_Icc.mp hmI).1; nlinarith
          have hnmS : n * m ∉ S := fun h' => hprim _ h' m hmS n hn2 rfl
          simp [hc, hnm1, hnmS]
        · simp [hc, hm1, hmS]
      rw [hrest, add_zero, mul_one]
      have hn1 : n ≠ 1 := by omega
      by_cases hnS : n ∈ S
      · simp [hc, hn1, hnS]
      · simp [hc, hn1, hnS]
    have hmass : ∑ m ∈ Finset.Icc 1 N, c m ^ 2 = 1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hS' : S ⊆ (Finset.Icc 1 N).erase 1 := fun n hn => by
        have := Finset.mem_Icc.mp (hS hn)
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, this.2⟩⟩
      rw [← Finset.sum_subset hS' (fun m hm hmS => by
        have hm1 := (Finset.mem_erase.mp hm).1
        simp [hc, hm1, hmS]), Finset.mul_sum]
      congr 1
      · simp [hc]
      · refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp (hS hn)).1
        have hn1 : n ≠ 1 := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        simp only [hc, hn1, hn, if_false, if_true, div_pow, mul_pow, Real.sq_sqrt hn0.le]
        ring
    have hlhs : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m = t * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [Finset.sum_congr rfl fun n hn => by rw [hinner n hn], Finset.mul_sum]
      rw [← Finset.sum_subset hS (fun n _ hnS => by simp [hnS])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 := (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      rw [if_pos hn, show lam n / Real.sqrt n * (t * lam n / Real.sqrt n) =
        t * (lam n ^ 2 / (Real.sqrt n * Real.sqrt n)) by ring, hsq]
    rw [hlhs, hmass] at hb
    linarith
  have hB : 0 ≤ Real.log N + oddToeplitzConst := by
    have := key ∅ (Finset.empty_subset _) (fun m hm => absurd hm (Finset.notMem_empty m))
      (fun n hn => absurd hn (Finset.notMem_empty n)) 0 le_rfl
    simpa using this
  refine ⟨hB, fun S hS hprim hpos => ?_⟩
  set Q := ∑ n ∈ S, lam n ^ 2 / n with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
  set B := Real.log N + oddToeplitzConst with hBdef
  rcases hQ0.lt_or_eq with hQpos | hQzero
  · have h1 := key S hS hprim hpos (B / Q) (div_nonneg hB hQ0)
    rw [← hQ] at h1
    have e : 2 * (B / Q) * Q = 2 * B := by field_simp
    have e2 : B * (1 + (B / Q) ^ 2 * Q) = B + B ^ 3 / Q := by field_simp
    rw [e, e2] at h1
    have h3 : B ≤ B ^ 3 / Q := by linarith
    rcases hB.lt_or_eq with hBpos | hBzero
    · rw [le_div_iff₀ hQpos] at h3
      nlinarith
    · have h4 := key S hS hprim hpos 1 zero_le_one
      rw [← hQ, ← hBzero] at h4
      nlinarith
  · rw [← hQzero]; positivity

/-- **Dyadic mean square of the positive part.** -/
theorem odd_sum_posPart_sq_Ioc_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {N : ℕ}
    (hN : 1 ≤ N) :
    0 ≤ Real.log (2 * N : ℕ) + oddToeplitzConst ∧
      ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ^ 2 ≤
        (2 * N : ℕ) * (Real.log (2 * N : ℕ) + oddToeplitzConst) ^ 2 := by
  obtain ⟨hB, hS⟩ := odd_sum_sq_div_le_of_primitive h (N := 2 * N) (by omega)
  refine ⟨hB, ?_⟩
  set S := (Finset.Ioc N (2 * N)).filter fun n => 0 ≤ lam n with hSdef
  have hsub : S ⊆ Finset.Icc 2 (2 * N) := fun n hn => by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  have hprim : IsPrimitiveSet S := by
    intro m hm m' hm' k hk heq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm hm'
    have : k * m' ≥ 2 * (N + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hQ := hS S hsub hprim fun n hn => (Finset.mem_filter.mp hn).2
  have h2N : (0 : ℝ) < (2 * N : ℕ) := by exact_mod_cast (show 0 < 2 * N by omega)
  have hsplit : ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ^ 2 = ∑ n ∈ S, lam n ^ 2 := by
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hn
    · rw [max_eq_left hn]
    · push Not at hn; rw [max_eq_right hn.le]; ring
  rw [hsplit]
  calc ∑ n ∈ S, lam n ^ 2
      = (2 * N : ℕ) * ∑ n ∈ S, lam n ^ 2 / (2 * N : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by field_simp
    _ ≤ (2 * N : ℕ) * ∑ n ∈ S, lam n ^ 2 / n := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) h2N.le
        rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hn0 (by exact_mod_cast hn.1.2)
    _ ≤ (2 * N : ℕ) * (Real.log (2 * N : ℕ) + oddToeplitzConst) ^ 2 :=
        mul_le_mul_of_nonneg_left hQ h2N.le

/-- **Dyadic `ℓ¹` bound of the positive part.** -/
theorem odd_sum_posPart_Ioc_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {N : ℕ}
    (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ≤
      3 / 2 * N * (Real.log (2 * N : ℕ) + oddToeplitzConst + 1) := by
  obtain ⟨hB, hsq⟩ := odd_sum_posPart_sq_Ioc_le h hN
  have h1 := sum_abs_Ioc_le_of_sum_sq (lam := fun n => max (lam n) 0) hB hsq
  have e : ∀ n, |max (lam n) 0| = max (lam n) 0 := fun n => abs_of_nonneg (le_max_right _ _)
  simp only [e] at h1
  exact h1


/-! ## Odd far bumps -/

/-- The far-bump profile `φ`, a fixed even bump of radius `≤ 1/12`. -/
def farBump (x : ℝ) : ℝ := nodeBump 2 x

/-- `k = φ ⋆ φ̃`. -/
def farKernel (t : ℝ) : ℝ := crossCorr farBump farBump t

/-- The odd far bump `φ(· − a) − φ(· + a)`. -/
def oddFarBump (a x : ℝ) : ℝ := farBump (x - a) - farBump (x + a)

/-- `J = ∫ φ(x) e^{−x/2} dx`. -/
def farJ : ℝ := ∫ x, farBump x * Real.exp (-x / 2)

/-- `S(a) = Σ_n lam(n) n^{−1/2} k(log n − 2a)`. -/
def farSum (lam : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) * farKernel (Real.log n - 2 * a)

theorem farBump_neg (x : ℝ) : farBump (-x) = farBump x := nodeBump_neg 2 x

theorem farBump_nonneg (x : ℝ) : 0 ≤ farBump x := (nodeBump 2).nonneg

theorem contDiff_farBump (n : ℕ) : ContDiff ℝ n farBump := (nodeBump 2).contDiff

theorem continuous_farBump : Continuous farBump := (contDiff_farBump 0).continuous

theorem farBump_eq_zero {x : ℝ} (hx : (nodeBump 2).rOut ≤ |x|) : farBump x = 0 :=
  nodeBump_eq_zero 2 hx

theorem hasCompactSupport_farBump : HasCompactSupport farBump :=
  (nodeBump 2).hasCompactSupport

theorem farKernel_neg (t : ℝ) : farKernel (-t) = farKernel t := crossCorr_self_neg farBump t

theorem farKernel_eq_zero {t : ℝ} (ht : 2 * (nodeBump 2).rOut ≤ |t|) : farKernel t = 0 := by
  unfold farKernel crossCorr
  have : (fun s => farBump s * farBump (s - t)) = fun _ => 0 := by
    funext s
    rcases le_or_gt (nodeBump 2).rOut |s| with hs | hs
    · rw [farBump_eq_zero hs, zero_mul]
    · have : (nodeBump 2).rOut ≤ |s - t| := by
        have := abs_sub_abs_le_abs_sub t s
        rw [abs_sub_comm] at this; linarith
      rw [farBump_eq_zero this, mul_zero]
  rw [this, integral_zero]

theorem farKernel_nonneg (t : ℝ) : 0 ≤ farKernel t :=
  integral_nonneg fun s => mul_nonneg (farBump_nonneg s) (farBump_nonneg _)

theorem integrable_farBump_mul (t : ℝ) : Integrable fun s => farBump s * farBump (s - t) :=
  (continuous_farBump.mul (continuous_farBump.comp (continuous_id.sub continuous_const))
    ).integrable_of_hasCompactSupport hasCompactSupport_farBump.mul_right

/-- The autocorrelation of the odd far bump. -/
theorem crossCorr_oddFarBump (a y : ℝ) :
    crossCorr (oddFarBump a) (oddFarBump a) y =
      2 * farKernel y - farKernel (y - 2 * a) - farKernel (y + 2 * a) := by
  unfold crossCorr oddFarBump farKernel crossCorr
  have i1 : Integrable fun t => farBump (t - a) * farBump (t - y - a) := by
    have := (integrable_farBump_mul y).comp_sub_right a
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t - a) * farBump (t - a - y) = _
    rw [show t - a - y = t - y - a by ring]
  have i2 : Integrable fun t => farBump (t - a) * farBump (t - y + a) := by
    have := (integrable_farBump_mul (y - 2 * a)).comp_sub_right a
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t - a) * farBump (t - a - (y - 2 * a)) = _
    rw [show t - a - (y - 2 * a) = t - y + a by ring]
  have i3 : Integrable fun t => farBump (t + a) * farBump (t - y - a) := by
    have := (integrable_farBump_mul (y + 2 * a)).comp_add_right a
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t + a) * farBump (t + a - (y + 2 * a)) = _
    rw [show t + a - (y + 2 * a) = t - y - a by ring]
  have i4 : Integrable fun t => farBump (t + a) * farBump (t - y + a) := by
    have := (integrable_farBump_mul y).comp_add_right a
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t + a) * farBump (t + a - y) = _
    rw [show t + a - y = t - y + a by ring]
  have e : (fun t => (farBump (t - a) - farBump (t + a)) *
      (farBump (t - y - a) - farBump (t - y + a))) =
      fun t => farBump (t - a) * farBump (t - y - a) - farBump (t - a) * farBump (t - y + a) -
        farBump (t + a) * farBump (t - y - a) + farBump (t + a) * farBump (t - y + a) := by
    funext t; ring
  rw [e, integral_add (f := fun t => farBump (t - a) * farBump (t - y - a) -
      farBump (t - a) * farBump (t - y + a) - farBump (t + a) * farBump (t - y - a))
      (g := fun t => farBump (t + a) * farBump (t - y + a)) ((i1.sub i2).sub i3) i4,
    integral_sub (f := fun t => farBump (t - a) * farBump (t - y - a) -
      farBump (t - a) * farBump (t - y + a))
      (g := fun t => farBump (t + a) * farBump (t - y - a)) (i1.sub i2) i3,
    integral_sub i1 i2]
  have j1 : ∫ t, farBump (t - a) * farBump (t - y - a) = ∫ s, farBump s * farBump (s - y) := by
    rw [← integral_sub_right_eq_self (fun s => farBump s * farBump (s - y)) a]
    congr 1; funext t; congr 2; ring
  have j2 : ∫ t, farBump (t - a) * farBump (t - y + a) =
      ∫ s, farBump s * farBump (s - (y - 2 * a)) := by
    rw [← integral_sub_right_eq_self (fun s => farBump s * farBump (s - (y - 2 * a))) a]
    congr 1; funext t; congr 2; ring
  have j3 : ∫ t, farBump (t + a) * farBump (t - y - a) =
      ∫ s, farBump s * farBump (s - (y + 2 * a)) := by
    rw [← integral_add_right_eq_self (fun s => farBump s * farBump (s - (y + 2 * a))) a]
    congr 1; funext t; congr 2; ring
  have j4 : ∫ t, farBump (t + a) * farBump (t - y + a) = ∫ s, farBump s * farBump (s - y) := by
    rw [← integral_add_right_eq_self (fun s => farBump s * farBump (s - y)) a]
    congr 1; funext t; congr 2; ring
  rw [j1, j2, j3, j4]
  ring

theorem two_mul_rOut_lt_log_two : 2 * (nodeBump 2).rOut < Real.log 2 := by
  have h1 := nodeBump_rOut_le 2
  have h2 := Real.log_two_gt_d9
  linarith

/-- At the atoms only the cross terms survive: `−2 k(log n − 2a)`. -/
theorem crossCorr_oddFarBump_log_add {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 2 ≤ n) :
    crossCorr (oddFarBump a) (oddFarBump a) (Real.log n) +
      crossCorr (oddFarBump a) (oddFarBump a) (-Real.log n) =
      -2 * farKernel (Real.log n - 2 * a) := by
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hr := two_mul_rOut_lt_log_two
  have hr0 := (nodeBump 2).rOut_pos
  rw [crossCorr_oddFarBump, crossCorr_oddFarBump]
  have z1 : farKernel (Real.log n) = 0 :=
    farKernel_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith)
  have z2 : farKernel (Real.log n + 2 * a) = 0 :=
    farKernel_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith)
  have z3 : farKernel (-Real.log n) = 0 := by rw [farKernel_neg, z1]
  have z4 : farKernel (-Real.log n - 2 * a) = 0 := by
    rw [show -Real.log n - 2 * a = -(Real.log n + 2 * a) by ring, farKernel_neg, z2]
  have e5 : farKernel (-Real.log n + 2 * a) = farKernel (Real.log n - 2 * a) := by
    rw [show -Real.log n + 2 * a = -(Real.log n - 2 * a) by ring, farKernel_neg]
  rw [z1, z2, z3, z4, e5]
  ring

theorem atomPairing_oddFarBump (lam : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    atomPairing lam (crossCorr (oddFarBump a) (oddFarBump a)) = -2 * farSum lam a := by
  unfold atomPairing farSum
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  split_ifs with hn
  · rw [crossCorr_oddFarBump_log_add ha hn]; ring
  · ring

theorem oddFarBump_neg (a x : ℝ) : oddFarBump a (-x) = -oddFarBump a x := by
  unfold oddFarBump
  rw [show -x - a = -(x + a) by ring, show -x + a = -(x - a) by ring, farBump_neg, farBump_neg]
  ring

theorem contDiff_oddFarBump (a : ℝ) : ContDiff ℝ 2 (oddFarBump a) := by
  unfold oddFarBump
  exact ((contDiff_farBump 2).comp (contDiff_id.sub contDiff_const)).sub
    ((contDiff_farBump 2).comp (contDiff_id.add contDiff_const))

theorem hasCompactSupport_oddFarBump (a : ℝ) : HasCompactSupport (oddFarBump a) := by
  unfold oddFarBump
  exact (hasCompactSupport_farBump.comp_homeomorph (Homeomorph.subRight a)).sub
    (hasCompactSupport_farBump.comp_homeomorph (Homeomorph.addRight a))

/-- The exponential moment of the odd far bump: `(e^{−a/2} − e^{a/2}) J`. -/
theorem integral_oddFarBump_mul_exp (a : ℝ) :
    ∫ x, oddFarBump a x * Real.exp (-x / 2) =
      (Real.exp (-a / 2) - Real.exp (a / 2)) * farJ := by
  have hi : ∀ c : ℝ, Integrable fun x => farBump (x - c) * Real.exp (-x / 2) := fun c =>
    ((continuous_farBump.comp (continuous_id.sub continuous_const)).mul (by fun_prop)
      ).integrable_of_hasCompactSupport
      (hasCompactSupport_farBump.comp_homeomorph (Homeomorph.subRight c)).mul_right
  have h1 : ∫ x, farBump (x - a) * Real.exp (-x / 2) = Real.exp (-a / 2) * farJ := by
    have key := integral_sub_right_eq_self (μ := volume)
      (fun x => farBump x * Real.exp (-(x + a) / 2)) a
    simp only [sub_add_cancel] at key
    rw [key]
    unfold farJ
    rw [← integral_const_mul]
    congr 1; funext x
    rw [show -(x + a) / 2 = -a / 2 + -x / 2 by ring, Real.exp_add]
    ring
  have h2 : ∫ x, farBump (x + a) * Real.exp (-x / 2) = Real.exp (a / 2) * farJ := by
    have key := integral_add_right_eq_self (μ := volume)
      (fun x => farBump x * Real.exp (-(x - a) / 2)) a
    simp only [add_sub_cancel_right] at key
    rw [key]
    unfold farJ
    rw [← integral_const_mul]
    congr 1; funext x
    rw [show -(x - a) / 2 = a / 2 + -x / 2 by ring, Real.exp_add]
    ring
  unfold oddFarBump
  have e : (fun x => (farBump (x - a) - farBump (x + a)) * Real.exp (-x / 2)) =
      fun x => farBump (x - a) * Real.exp (-x / 2) - farBump (x + a) * Real.exp (-x / 2) := by
    funext x; ring
  have hi2 : Integrable fun x => farBump (x + a) * Real.exp (-x / 2) := by
    refine (hi (-a)).congr (Eventually.of_forall fun x => ?_)
    simp only [sub_neg_eq_add]
  rw [e, integral_sub (hi a) hi2, h1, h2]
  ring

theorem oddFarBumpC_eq (a : ℝ) :
    (fun u => ((oddFarBump a u : ℝ) : ℂ)) = fun u => ∑ k : Fin 2, (![1, -1] k : ℂ) *
      (fun v => ((farBump v : ℝ) : ℂ)) (u - ![a, -a] k) := by
  funext u
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, oddFarBump]
  push_cast
  rw [sub_neg_eq_add]
  ring

theorem norm_paperFT_oddFarBump_le (a r : ℝ) :
    ‖paperFT (fun u => ((oddFarBump a u : ℝ) : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump 2 u : ℂ)) r‖ := by
  rw [oddFarBumpC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _
    (Complex.continuous_ofReal.comp continuous_farBump)
    (hasCompactSupport_farBump.comp_left Complex.ofReal_zero) r).trans ?_
  have hs : (∑ k : Fin 2, ‖(![1, -1] k : ℂ)‖) = 2 := by simp [Fin.sum_univ_two]; norm_num
  rw [hs]
  have : ‖paperFT (Complex.ofReal ∘ farBump) r‖ = ‖paperFT (fun u => (nodeBump 2 u : ℂ)) r‖ :=
    rfl
  rw [this]
  nlinarith [norm_nonneg (paperFT (fun u => (nodeBump 2 u : ℂ)) r)]

/-- The pole and archimedean parts of a real test. -/
theorem weilArchRe_weilTest_eq {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    weilArchRe (EF.weilTest f f) = (weilPoleTerm (EF.weilTest f f)).re +
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r := by
  have hint : (∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)) =
      ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [paperFT_weilTest_self_eq_normSq hf hfc r]
    push_cast; ring
  unfold weilArchRe weilPoleTerm
  rw [hint, show (1 / (2 * (Real.pi : ℂ)) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re]

/-- The archimedean constant of the far bumps. -/
def farArchConst : ℝ :=
  1 / (4 * Real.pi) * (16 / nodeScale 2 *
    ((gammaLogConst + Real.log (nodeScale 2)) * bumpMassConst + bumpLogConst))

/-- **The far-bump lower bound.**  Odd positivity at a pole weight `β ≥ 0` gives, for `a ≥ 0`,
`S(a) ≥ β (e^a − 2) J² − A₀`. -/
theorem farSum_ge {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) (hβ : 0 ≤ β) {a : ℝ}
    (ha : 0 ≤ a) : β * (Real.exp a - 2) * farJ ^ 2 - farArchConst ≤ farSum lam a := by
  set F := oddFarBump a with hFdef
  set f : ℝ → ℂ := fun u => ((F u : ℝ) : ℂ) with hfdef
  have hf2 : ContDiff ℝ 2 f := contDiff_ofReal_comp (contDiff_oddFarBump a)
  have hfc : HasCompactSupport f := (hasCompactSupport_oddFarBump a).comp_left Complex.ofReal_zero
  have hodd : ∀ x, f (-x) = -f x := fun x => by
    simp only [hfdef, hFdef, oddFarBump_neg]; push_cast; ring
  have hpos := h f hf2 hfc hodd
  rw [re_weilPoleWeightFunctional_eq_add, re_weilFullFunctional_ofReal,
    weilArchRe_weilTest_eq hf2.continuous hfc,
    re_weilPoleTerm_weilTest_of_odd hf2.continuous hfc hodd,
    atomPairing_oddFarBump lam ha] at hpos
  -- the pole value
  have hpole : ‖paperFT f (I / 2)‖ ^ 2 = ((Real.exp (-a / 2) - Real.exp (a / 2)) * farJ) ^ 2 := by
    rw [hfdef, paperFT_ofRealFun_I_div_two, integral_oddFarBump_mul_exp, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  -- the archimedean value
  have harch : |1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r| ≤
      2 * farArchConst := by
    have h1 := integral_normSq_mul_abs_gammaBracket_le 2 (f := f) (norm_paperFT_oddFarBump_le a)
    have h2 : |∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r| ≤
        ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| := by
      refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [abs_mul, abs_of_nonneg (sq_nonneg ‖paperFT f r‖)]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    unfold farArchConst
    have hpi : 0 < Real.pi := Real.pi_pos
    calc 1 / (2 * Real.pi) * |∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r|
        ≤ 1 / (2 * Real.pi) * (16 / nodeScale 2 *
          ((gammaLogConst + Real.log (nodeScale 2)) * bumpMassConst + bumpLogConst)) :=
          mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity)
      _ = 2 * (1 / (4 * Real.pi) * (16 / nodeScale 2 *
          ((gammaLogConst + Real.log (nodeScale 2)) * bumpMassConst + bumpLogConst))) := by
          field_simp; ring
  have hsq : Real.exp a - 2 ≤ (Real.exp (-a / 2) - Real.exp (a / 2)) ^ 2 := by
    have e : (Real.exp (-a / 2) - Real.exp (a / 2)) ^ 2 = Real.exp a - 2 + Real.exp (-a) := by
      have h1 : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have h2 : Real.exp (a / 2) ^ 2 = Real.exp a := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have h3 : Real.exp (-a / 2) * Real.exp (a / 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      nlinarith
    rw [e]; linarith [Real.exp_pos (-a)]
  have hJ2 : β * (Real.exp a - 2) * farJ ^ 2 ≤ β * ‖paperFT f (I / 2)‖ ^ 2 := by
    calc β * (Real.exp a - 2) * farJ ^ 2 = β * ((Real.exp a - 2) * farJ ^ 2) := by ring
      _ ≤ β * ((Real.exp (-a / 2) - Real.exp (a / 2)) ^ 2 * farJ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) hβ
      _ = β * ‖paperFT f (I / 2)‖ ^ 2 := by rw [hpole, mul_pow]
  have hab := abs_le.mp harch
  nlinarith


/-! ## The kernel near the origin and the negative part -/

theorem farBump_eq_one {s : ℝ} (hs : |s| ≤ (nodeBump 2).rIn) : farBump s = 1 :=
  (nodeBump 2).one_of_mem_closedBall
    (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hs)

theorem farBump_le_one (s : ℝ) : farBump s ≤ 1 := (nodeBump 2).le_one

theorem farKernel_ge {t : ℝ} (ht : |t| ≤ (nodeBump 2).rIn / 2) :
    (nodeBump 2).rIn ≤ farKernel t := by
  set r := (nodeBump 2).rIn with hrdef
  have hr : 0 < r := (nodeBump 2).rIn_pos
  have hind : ∀ s, (Icc (-(r / 2)) (r / 2)).indicator (fun _ => (1 : ℝ)) s ≤
      farBump s * farBump (s - t) := by
    intro s
    by_cases hs : s ∈ Icc (-(r / 2)) (r / 2)
    · rw [indicator_of_mem hs]
      have h1 : |s| ≤ r := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
      have h2 : |s - t| ≤ r := by
        rw [abs_le] at ht ⊢; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      rw [farBump_eq_one h1, farBump_eq_one h2]; norm_num
    · rw [indicator_of_notMem hs]; exact mul_nonneg (farBump_nonneg _) (farBump_nonneg _)
  have hii : Integrable ((Icc (-(r / 2)) (r / 2)).indicator fun _ => (1 : ℝ)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hval : ∫ s, (Icc (-(r / 2)) (r / 2)).indicator (fun _ => (1 : ℝ)) s = r := by
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one, Measure.real,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  unfold farKernel crossCorr
  rw [← hval]
  exact integral_mono hii (integrable_farBump_mul t) hind

/-- `∫ φ`, an upper bound for the kernel. -/
def farMass : ℝ := ∫ s, farBump s

theorem farKernel_le (t : ℝ) : farKernel t ≤ farMass := by
  unfold farKernel crossCorr farMass
  refine integral_mono (integrable_farBump_mul t)
    (continuous_farBump.integrable_of_hasCompactSupport hasCompactSupport_farBump) fun s => ?_
  have h1 := farBump_le_one (s - t)
  have h2 := farBump_nonneg s
  have h3 := farBump_nonneg (s - t)
  nlinarith

theorem max_neg_zero_eq (x : ℝ) : max (-x) 0 = max x 0 - x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right (by linarith), max_eq_left h]; ring
  · rw [max_eq_left (by linarith), max_eq_right h]; ring

theorem abs_eq_max_zero_add_max_neg_zero (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring

/-- The far sum is a finite sum over `[2, 4N]` when `2a ≤ log N + log 2 + 1/12`. -/
theorem farSum_eq_sum {lam : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {a : ℝ}
    (ha2 : 2 * a ≤ Real.log N + Real.log 2 + 1 / 12) :
    farSum lam a = ∑ n ∈ Finset.Icc 2 (4 * N), lam n / Real.sqrt n *
      farKernel (Real.log n - 2 * a) := by
  unfold farSum
  have hr := nodeBump_rOut_le 2
  have hlog2 := Real.log_two_gt_d9
  rw [tsum_eq_sum (s := Finset.Icc 2 (4 * N)) (fun n hn => ?_)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_Icc.mp hn).1]
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h1 | h1
    · rw [if_neg (by omega), zero_mul]
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hn4 : (4 * N : ℝ) ≤ n := by exact_mod_cast h1.le
      have hlog : Real.log (4 * N) ≤ Real.log n := Real.log_le_log (by positivity) hn4
      rw [Real.log_mul (by norm_num) hN0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        at hlog
      push_cast at hlog
      rw [farKernel_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith), mul_zero]

/-! ## Windows covering a dyadic block -/

/-- The window step `δ = r/2`, half the inner radius of the far bump. -/
def farStep : ℝ := (nodeBump 2).rIn / 2

/-- The number of windows needed to cover a dyadic block, `⌈log 2 / δ⌉`. -/
def farWindowCount : ℕ := ⌈Real.log 2 / farStep⌉₊

/-- The window centres, `2a_i = log N + iδ`. -/
def farWindow (N i : ℕ) : ℝ := (Real.log N + i * farStep) / 2

theorem farStep_pos : 0 < farStep := by
  unfold farStep; linarith [(nodeBump 2).rIn_pos]

theorem farStep_le : farStep ≤ 1 / 24 := by
  unfold farStep; linarith [(nodeBump 2).rIn_lt_rOut, nodeBump_rOut_le 2]

theorem farWindow_bounds (N : ℕ) {i : ℕ} (hi : i ≤ farWindowCount) :
    Real.log N ≤ 2 * farWindow N i ∧
      2 * farWindow N i ≤ Real.log N + Real.log 2 + 1 / 12 := by
  have hδ := farStep_pos
  have hδ' := farStep_le
  have hlog2 := Real.log_two_gt_d9
  have hJ : (farWindowCount : ℝ) < Real.log 2 / farStep + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by linarith) hδ.le)
  have hi' : (i : ℝ) * farStep ≤ Real.log 2 + farStep := by
    have h1 : (i : ℝ) ≤ farWindowCount := by exact_mod_cast hi
    have h2 : (i : ℝ) * farStep ≤ (Real.log 2 / farStep + 1) * farStep :=
      mul_le_mul_of_nonneg_right (h1.trans hJ.le) hδ.le
    rwa [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at h2
  have hi0 : 0 ≤ (i : ℝ) * farStep := by positivity
  unfold farWindow
  constructor <;> linarith

/-- Every `n ∈ (N, 2N]` lies in the plateau of one of the window kernels. -/
theorem farWindow_cover {N n : ℕ} (hN : 1 ≤ N) (hn1 : N < n) (hn2 : n ≤ 2 * N) :
    (nodeBump 2).rIn ≤ ∑ i ∈ Finset.range (farWindowCount + 1),
      farKernel (Real.log n - 2 * farWindow N i) := by
  have hδ := farStep_pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx0 : 0 ≤ Real.log n - Real.log N := by
    have := Real.log_le_log hN0 (show (N : ℝ) ≤ n by exact_mod_cast hn1.le); linarith
  have hx2 : Real.log n - Real.log N ≤ Real.log 2 := by
    have h := Real.log_le_log hn0 (show (n : ℝ) ≤ 2 * N by exact_mod_cast hn2)
    rw [Real.log_mul (by norm_num) hN0.ne'] at h; linarith
  have hi1 : (⌊(Real.log n - Real.log N) / farStep⌋₊ : ℝ) ≤ (Real.log n - Real.log N) / farStep :=
    Nat.floor_le (div_nonneg hx0 hδ.le)
  have hi2 : (Real.log n - Real.log N) / farStep <
      (⌊(Real.log n - Real.log N) / farStep⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hiJ : ⌊(Real.log n - Real.log N) / farStep⌋₊ ∈ Finset.range (farWindowCount + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have h1 : (Real.log n - Real.log N) / farStep ≤ Real.log 2 / farStep :=
      div_le_div_of_nonneg_right hx2 hδ.le
    have h2 : (⌊(Real.log n - Real.log N) / farStep⌋₊ : ℝ) ≤ farWindowCount :=
      (hi1.trans h1).trans (Nat.le_ceil _)
    exact_mod_cast h2
  have hwin : |Real.log n - 2 * farWindow N ⌊(Real.log n - Real.log N) / farStep⌋₊| ≤
      (nodeBump 2).rIn / 2 := by
    have h1 := (le_div_iff₀ hδ).mp hi1
    have h2 := (div_lt_iff₀ hδ).mp hi2
    unfold farWindow
    rw [show (nodeBump 2).rIn / 2 = farStep from rfl, abs_le]
    constructor <;> nlinarith
  exact (farKernel_ge hwin).trans (Finset.single_le_sum
    (f := fun i => farKernel (Real.log n - 2 * farWindow N i))
    (fun i _ => farKernel_nonneg _) hiJ)

/-! ## The negative part on a dyadic block -/

/-- The positive part seen through one window is controlled by three dyadic blocks. -/
theorem odd_window_posPart_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {M : ℕ}
    (hM : 1 ≤ M) {a : ℝ} (ha : Real.log (2 * M : ℕ) ≤ 2 * a) :
    ∑ n ∈ Finset.Icc 2 (8 * M), max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) ≤
      farMass * (Real.sqrt M)⁻¹ *
        (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) := by
  have hK0 : 0 ≤ farMass := (farKernel_nonneg 0).trans (farKernel_le 0)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog2 := Real.log_two_gt_d9
  have hrO := nodeBump_rOut_le 2
  have hg0 : ∀ n, 0 ≤ max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) := fun n =>
    mul_nonneg (div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) (farKernel_nonneg _)
  have hzero : ∀ n ∈ Finset.Ioc 0 M,
      max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) = 0 := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hl : Real.log n ≤ Real.log M := Real.log_le_log hn0 (by exact_mod_cast hn2)
    have h2M : Real.log (2 * M : ℕ) = Real.log 2 + Real.log M := by
      push_cast; exact Real.log_mul (by norm_num) hM0.ne'
    have hk : farKernel (Real.log n - 2 * a) = 0 :=
      farKernel_eq_zero (by rw [abs_of_nonpos (by linarith)]; linarith)
    rw [hk, mul_zero]
  have hbound : ∀ n ∈ Finset.Ioc M (8 * M),
      max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) ≤
        farMass * (Real.sqrt M)⁻¹ * max (lam n) 0 := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : (Real.sqrt n)⁻¹ ≤ (Real.sqrt M)⁻¹ := by
      rw [inv_le_inv₀ (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hM0)]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn1.le)
    have hlp := le_max_right (lam n) 0
    calc max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a)
        ≤ max (lam n) 0 / Real.sqrt n * farMass :=
          mul_le_mul_of_nonneg_left (farKernel_le _) (div_nonneg hlp (Real.sqrt_nonneg _))
      _ = farMass * (Real.sqrt n)⁻¹ * max (lam n) 0 := by ring
      _ ≤ farMass * (Real.sqrt M)⁻¹ * max (lam n) 0 := by gcongr
  have hblocks : ∑ n ∈ Finset.Ioc M (8 * M), max (lam n) 0 ≤
      21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1) := by
    have hlog : ∀ k : ℕ, 1 ≤ k → k ≤ 4 * M →
        Real.log (2 * k : ℕ) + oddToeplitzConst + 1 ≤
          Real.log (8 * M) + oddToeplitzConst + 1 := by
      intro k hk1 hk
      have h8 : ((2 * k : ℕ) : ℝ) ≤ 8 * M := by
        have : (k : ℝ) ≤ 4 * M := by exact_mod_cast hk
        push_cast; linarith
      have := Real.log_le_log (by exact_mod_cast (show 0 < 2 * k by omega)) h8
      linarith
    have P1 := odd_sum_posPart_Ioc_le h hM
    have P2 := odd_sum_posPart_Ioc_le h (N := 2 * M) (by omega)
    have P3 := odd_sum_posPart_Ioc_le h (N := 2 * (2 * M)) (by omega)
    have Q1 := mul_le_mul_of_nonneg_left (hlog M hM (by omega))
      (show (0 : ℝ) ≤ 3 / 2 * M by positivity)
    have Q2 := mul_le_mul_of_nonneg_left (hlog (2 * M) (by omega) (by omega))
      (show (0 : ℝ) ≤ 3 / 2 * ((2 * M : ℕ) : ℝ) by positivity)
    have Q3 := mul_le_mul_of_nonneg_left (hlog (2 * (2 * M)) (by omega) (by omega))
      (show (0 : ℝ) ≤ 3 / 2 * ((2 * (2 * M) : ℕ) : ℝ) by positivity)
    rw [show 8 * M = 2 * (2 * (2 * M)) by ring,
      ← Finset.sum_Ioc_consecutive _ (show M ≤ 2 * M by omega)
        (show 2 * M ≤ 2 * (2 * (2 * M)) by omega),
      ← Finset.sum_Ioc_consecutive _ (show 2 * M ≤ 2 * (2 * M) by omega)
        (show 2 * (2 * M) ≤ 2 * (2 * (2 * M)) by omega)]
    calc _ ≤ _ := add_le_add (P1.trans Q1) (add_le_add (P2.trans Q2) (P3.trans Q3))
      _ = _ := by push_cast; ring
  calc ∑ n ∈ Finset.Icc 2 (8 * M), max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a)
      ≤ ∑ n ∈ Finset.Ioc 0 (8 * M),
          max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
          rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ioc]; omega) fun n _ _ => hg0 n
    _ = ∑ n ∈ Finset.Ioc M (8 * M),
          max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) := by
        rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) (show M ≤ 8 * M by omega),
          Finset.sum_eq_zero hzero, zero_add]
    _ ≤ ∑ n ∈ Finset.Ioc M (8 * M), farMass * (Real.sqrt M)⁻¹ * max (lam n) 0 :=
        Finset.sum_le_sum hbound
    _ = farMass * (Real.sqrt M)⁻¹ * ∑ n ∈ Finset.Ioc M (8 * M), max (lam n) 0 := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hblocks (by positivity)

/-- The negative part seen through one window. -/
theorem odd_window_negPart_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) (hβ : 0 ≤ β)
    {M : ℕ} (hM : 2 ≤ M) {a : ℝ} (ha1 : Real.log (2 * M : ℕ) ≤ 2 * a)
    (ha2 : 2 * a ≤ Real.log (2 * M : ℕ) + Real.log 2 + 1 / 12) :
    ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 / Real.sqrt n *
        farKernel (Real.log n - 2 * a) ≤
      farMass * (Real.sqrt M)⁻¹ * (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
        |farArchConst| := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog2 := Real.log_two_gt_d9
  have h2M : Real.log (2 * M : ℕ) = Real.log 2 + Real.log M := by
    push_cast; exact Real.log_mul (by norm_num) hM0.ne'
  have hlogM : Real.log 2 ≤ Real.log M :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have ha0 : Real.log 2 ≤ a := by linarith
  have hexp : 2 ≤ Real.exp a := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
      _ ≤ Real.exp a := Real.exp_le_exp.mpr ha0
  have hge := farSum_ge h hβ (a := a) (by linarith)
  rw [farSum_eq_sum (N := 2 * M) (by omega) ha2, show 4 * (2 * M) = 8 * M by ring] at hge
  have hβ' : 0 ≤ β * (Real.exp a - 2) * farJ ^ 2 :=
    mul_nonneg (mul_nonneg hβ (sub_nonneg.mpr hexp)) (sq_nonneg _)
  have hpos := odd_window_posPart_le h (M := M) (by omega) ha1
  have hsub : Finset.Ioc (2 * M) (4 * M) ⊆ Finset.Icc 2 (8 * M) := fun n hn => by
    rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  have hsplit : ∑ n ∈ Finset.Icc 2 (8 * M), max (-lam n) 0 / Real.sqrt n *
      farKernel (Real.log n - 2 * a) =
      ∑ n ∈ Finset.Icc 2 (8 * M), max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) -
      ∑ n ∈ Finset.Icc 2 (8 * M), lam n / Real.sqrt n * farKernel (Real.log n - 2 * a) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [max_neg_zero_eq]; ring
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun n =>
      max (-lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a)) fun n _ _ =>
    mul_nonneg (div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) (farKernel_nonneg _)
  linarith [le_abs_self farArchConst]

/-- **The negative part on a dyadic block.**  At pole weight `β ≥ 0`, with `J` windows of
plateau width `r`, `Σ_{2M < n ≤ 4M} lam⁻(n) ≤ 2 (J+1)/r · (K · 21M/2 · (log 8M + C + 1) + √M |A₀|)`.
-/
theorem odd_sum_negPart_Ioc_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) (hβ : 0 ≤ β)
    {M : ℕ} (hM : 2 ≤ M) :
    ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 ≤
      2 * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn) *
        (farMass * (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
          Real.sqrt M * |farArchConst|) := by
  have hr : 0 < (nodeBump 2).rIn := (nodeBump 2).rIn_pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have hq : 0 ≤ ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn := by positivity
  have hln0 : ∀ n, 0 ≤ max (-lam n) 0 := fun n => le_max_right _ _
  have hcov : (nodeBump 2).rIn * ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 / Real.sqrt n ≤
      ∑ i ∈ Finset.range (farWindowCount + 1), ∑ n ∈ Finset.Ioc (2 * M) (4 * M),
        max (-lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * farWindow (2 * M) i) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    rw [← Finset.mul_sum]
    calc (nodeBump 2).rIn * (max (-lam n) 0 / Real.sqrt n)
        = max (-lam n) 0 / Real.sqrt n * (nodeBump 2).rIn := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (farWindow_cover (N := 2 * M) (by omega) hn1
          (by omega)) (div_nonneg (hln0 n) (Real.sqrt_nonneg _))
  have hwin : ∀ i ∈ Finset.range (farWindowCount + 1), ∑ n ∈ Finset.Ioc (2 * M) (4 * M),
      max (-lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * farWindow (2 * M) i) ≤
        farMass * (Real.sqrt M)⁻¹ * (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
          |farArchConst| := by
    intro i hi
    obtain ⟨h1, h2⟩ := farWindow_bounds (2 * M) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    exact odd_window_negPart_le h hβ hM h1 h2
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have h1 : ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 / Real.sqrt n ≤
      ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn * (farMass * (Real.sqrt M)⁻¹ *
        (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) + |farArchConst|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    have := hcov.trans hsum
    push_cast at this
    linarith
  have h2 : ∀ n ∈ Finset.Ioc (2 * M) (4 * M),
      max (-lam n) 0 ≤ 2 * Real.sqrt M * (max (-lam n) 0 / Real.sqrt n) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsn := Real.sqrt_pos.mpr hn0
    have hle : Real.sqrt n ≤ 2 * Real.sqrt M := by
      have e : Real.sqrt (4 * M) = 2 * Real.sqrt M := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [← e]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn2)
    rw [mul_div_assoc', le_div_iff₀ hsn]
    exact (mul_le_mul_of_nonneg_left hle (hln0 n)).trans_eq (by ring)
  calc ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0
      ≤ ∑ n ∈ Finset.Ioc (2 * M) (4 * M), 2 * Real.sqrt M * (max (-lam n) 0 / Real.sqrt n) :=
        Finset.sum_le_sum h2
    _ = 2 * Real.sqrt M * ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 / Real.sqrt n := by
        rw [Finset.mul_sum]
    _ ≤ 2 * Real.sqrt M * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
        (farMass * (Real.sqrt M)⁻¹ * (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
          |farArchConst|)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn) *
        (farMass * (Real.sqrt M * (Real.sqrt M)⁻¹) *
          (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
          Real.sqrt M * |farArchConst|) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hsM.ne', mul_one]

/-- The negative part on the dyadic blocks `(2^j, 2^{j+1}]` is `O(2^j (j + 1))`. -/
theorem odd_sum_negPart_dyadic_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam)
    (hβ : 0 ≤ β) : ∃ B : ℝ, ∀ j : ℕ, 2 ≤ j →
      ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), max (-lam n) 0 ≤ B * 2 ^ j * ((j : ℝ) + 1) := by
  have hr : 0 < (nodeBump 2).rIn := (nodeBump 2).rIn_pos
  have hq : 0 ≤ ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn := by positivity
  have hK0 : 0 ≤ farMass := (farKernel_nonneg 0).trans (farKernel_le 0)
  refine ⟨((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
    (21 / 2 * farMass * (3 + |oddToeplitzConst|) + |farArchConst|), fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hM : 2 ≤ 2 ^ k :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have e2 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
  rw [e1, e2]
  refine (odd_sum_negPart_Ioc_le h hβ hM).trans ?_
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hcast]
  have hX1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have t1 : Real.log (8 * (2 : ℝ) ^ k) + oddToeplitzConst + 1 ≤
      (3 + |oddToeplitzConst|) * ((k : ℝ) + 2) := by
    have e : Real.log (8 * (2 : ℝ) ^ k) = ((k : ℝ) + 3) * Real.log 2 := by
      rw [show (8 : ℝ) * (2 : ℝ) ^ k = 2 ^ (k + 3) by ring, Real.log_pow]; push_cast; ring
    rw [e]
    have := Real.log_two_lt_d9
    nlinarith [le_abs_self oddToeplitzConst, abs_nonneg oddToeplitzConst]
  have t2 : Real.sqrt ((2 : ℝ) ^ k) ≤ (2 : ℝ) ^ k := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have u1 : farMass * (21 / 2 * (2 : ℝ) ^ k * (Real.log (8 * (2 : ℝ) ^ k) + oddToeplitzConst + 1))
      ≤ farMass * (21 / 2 * (2 : ℝ) ^ k * ((3 + |oddToeplitzConst|) * ((k : ℝ) + 2))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t1 (by positivity)) hK0
  have u2 : Real.sqrt ((2 : ℝ) ^ k) * |farArchConst| ≤
      (2 : ℝ) ^ k * ((k : ℝ) + 2) * |farArchConst| :=
    mul_le_mul_of_nonneg_right (t2.trans (le_mul_of_one_le_right (by positivity)
      (by linarith))) (abs_nonneg _)
  refine (mul_le_mul_of_nonneg_left (add_le_add u1 u2)
    (by positivity : (0 : ℝ) ≤ 2 * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn))).trans_eq ?_
  push_cast
  ring

/-! ## Absolute convergence -/

/-- Dyadic blocks of size `O(2^j (j+1))` give absolute convergence on `Re s > 1`. -/
theorem summable_div_rpow_of_block {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) {B : ℝ} {j₀ : ℕ} {σ : ℝ}
    (hσ : 1 < σ)
    (hb : ∀ j, j₀ ≤ j → ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n ≤ B * 2 ^ j * (j + 1)) :
    Summable fun n : ℕ => f n / (n : ℝ) ^ σ := by
  set r : ℝ := (2 : ℝ) ^ (1 - σ) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set g : ℕ → ℝ := fun n => f n / (n : ℝ) ^ σ with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n =>
    div_nonneg (hf0 n) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  set b : ℕ → ℝ := fun j => ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), g n with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => Finset.sum_nonneg fun n _ => hg0 n
  have hbs : Summable b := by
    have hgeo : Summable fun j : ℕ => |B| * (((j : ℝ) + 1) * r ^ j) := by
      have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
        (show ‖r‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
      have h2 := summable_geometric_of_lt_one hr0 hr1
      refine ((h1.add h2).mul_left |B|).congr fun j => ?_
      simp only [pow_one]; ring
    refine Summable.of_norm_bounded_eventually hgeo ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_lt_nat j₀).subset fun j hj => ?_
    simp only [Set.mem_setOf_eq, not_le] at hj ⊢
    by_contra hjj
    push Not at hjj
    apply (not_lt.mpr ?_) hj
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 j)]
    have hN0 : (0 : ℝ) < 2 ^ j := by positivity
    calc b j ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n / ((2 : ℝ) ^ j) ^ σ := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_Ioc] at hn
          simp only [hg]
          refine div_le_div_of_nonneg_left (hf0 n) (Real.rpow_pos_of_pos hN0 _)
            (Real.rpow_le_rpow hN0.le ?_ (by linarith))
          exact_mod_cast hn.1.le
      _ = (∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n) / ((2 : ℝ) ^ j) ^ σ := by
          rw [Finset.sum_div]
      _ ≤ B * 2 ^ j * (j + 1) / ((2 : ℝ) ^ j) ^ σ := by
          exact div_le_div_of_nonneg_right (hb j hjj) (Real.rpow_nonneg hN0.le _)
      _ ≤ |B| * (((j : ℝ) + 1) * r ^ j) := by
          have hrj : (2 : ℝ) ^ j / ((2 : ℝ) ^ j) ^ σ = r ^ j := by
            rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num), ← Real.rpow_sub (by norm_num)]
            congr 1; ring
          have e : B * 2 ^ j * (j + 1) / ((2 : ℝ) ^ j) ^ σ =
              B * (((j : ℝ) + 1) * ((2 : ℝ) ^ j / ((2 : ℝ) ^ j) ^ σ)) := by ring
          rw [e, hrj]
          have : 0 ≤ ((j : ℝ) + 1) * r ^ j := by positivity
          exact mul_le_mul_of_nonneg_right (le_abs_self B) this
  have hdyad : ∀ J : ℕ, ∑ n ∈ Finset.Ioc 1 (2 ^ J), g n ≤ ∑ j ∈ Finset.range J, b j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← Finset.sum_Ioc_consecutive g (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ J)), Finset.sum_range_succ]
      exact add_le_add ih le_rfl
  refine summable_of_sum_range_le (c := g 0 + g 1 + ∑' j, b j) hg0 fun T => ?_
  have hT : T ≤ 2 ^ T := (Nat.lt_two_pow_self).le
  calc ∑ n ∈ Finset.range T, g n ≤ ∑ n ∈ Finset.range (2 ^ T + 1), g n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun n _ _ => hg0 n)
    _ = g 0 + g 1 + ∑ n ∈ Finset.Ioc 1 (2 ^ T), g n :=
        sum_range_succ_eq_Ioc g (2 ^ T) Nat.one_le_two_pow
    _ ≤ g 0 + g 1 + ∑' j, b j := by
        have := (hdyad T).trans (hbs.sum_le_tsum _ fun j _ => hb0 j)
        linarith

/-- **Odd-positive weights converge absolutely on `Re s > 1`.** -/
theorem summable_abs_div_rpow_of_weilPositiveOddAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) (hβ : 0 ≤ β) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  obtain ⟨B, hB⟩ := odd_sum_negPart_dyadic_le h hβ
  refine summable_div_rpow_of_block (fun n => abs_nonneg (lam n))
    (B := B + 3 / 2 * (2 + |oddToeplitzConst|)) (j₀ := 2) hσ fun j hj => ?_
  have hneg := hB j hj
  have hpos := odd_sum_posPart_Ioc_le h (N := 2 ^ j) Nat.one_le_two_pow
  rw [show 2 * 2 ^ j = 2 ^ (j + 1) by ring] at hpos
  have hsplit : ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), |lam n| =
      ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), max (lam n) 0 +
      ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), max (-lam n) 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => abs_eq_max_zero_add_max_neg_zero (lam n)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    nlinarith
  have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
  rw [hcast] at hpos
  have t : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) + oddToeplitzConst + 1 ≤
      (2 + |oddToeplitzConst|) * ((j : ℝ) + 1) := by
    nlinarith [le_abs_self oddToeplitzConst, abs_nonneg oddToeplitzConst]
  have hpos' := hpos.trans (mul_le_mul_of_nonneg_left t (by positivity))
  rw [hsplit]
  nlinarith

end RHTower.OddSector

end
