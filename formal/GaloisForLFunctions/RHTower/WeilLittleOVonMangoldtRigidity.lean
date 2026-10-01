import GaloisForLFunctions.RHTower.ZetaNotchRampMainTerm
import GaloisForLFunctions.RHTower.WeilLittleODeviationHarmonicConvergence
import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity

/-!
# Weil-cone rigidity for deviations that are `o(Λ)`

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_isLittleO`). Let `lam` be full-cone
Weil-positive and suppose `lam − Λ = o(Λ)`: for every `η > 0`, `|lam(n) − Λ(n)| ≤ η Λ(n)` for all
large `n`. Then `lam(n) = Λ(n)` for every `n ≥ 2`.

In particular, no second point of the Weil cone agrees with `Λ` off the prime powers and satisfies
`lam(p^k) = log p (1 + o(1))`. This covers every bounded deviation `|lam(p) − log p| ≤ C` on primes,
with arbitrary signs, when `lam = Λ` elsewhere.

**Proof.** Put `v(n) = (lam(n) − Λ(n))/√n` and `d(n) = √n v(n)`. Fix `n₀`, the truncation
`P = P_y` and `ε = ±1`, and let `a(n) = v(n) mW(n)` be the fibre weights of the notch.
* **Convergence.** The harmonic series `Σ d(n)/n` converges, by window pinning and the local
  smallness of `d` (`exists_tendsto_sum_coneDeviation_div`). Hence the fibre partial sums
  `S(M) = Σ_{n≤M} a(n)` are bounded, and they are `≥ ε v(n₀) − O(δ)` beyond some `y`.
* **Refined notch.** The notch at scale `L`, truncated at `N = ⌈(1 + L)²⌉`, has per-scale main term
  `e_P u Σ_{n≤u/(4K₀)} a(n) (β₀ log(u/n) + β₁)`. By Abel summation this is
  `≥ e_P u (β₀ Y log u − C)` when `S(k) ≥ Y` eventually. Its per-mode errors carry no `log n`.
* **Errors.** With `d = o(Λ)`:
  - `Σ_{n≤N} |d(n)|/n ≤ A + η log N`, by Mertens' first theorem;
  - `Σ_{n≤x} |d(n)|/√n ≤ A + η C √x`, by the square-root Chebyshev bound;
  - `Σ_{n>N} |d(n)| n^{−3/2} ≤ η C N^{−1/2}`, by the dyadic Chebyshev tail.

  So the shifted-pole pairing, the defect and the refined envelope cost `C_η + η K log L`.
* **Conclusion.** Comparing with the main term `e_P β₀ Y 2e^{−1} log(L − 1)` forces `Y ≤ 0`, so
  `ε v(n₀) ≤ O(δ)` for both signs and every `δ`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable
open RHTower.PrimeSmallDeviation

variable {P : Finset ℕ}

/-! ## The scaled deviation `d(n) = √n v(n)` -/

/-- `d(n) = √n v(n)`. -/
def sqrtScaled (v : ℕ → ℝ) (n : ℕ) : ℝ := Real.sqrt n * v n

theorem abs_sqrtScaled (v : ℕ → ℝ) (n : ℕ) : |sqrtScaled v n| = Real.sqrt n * |v n| := by
  rw [sqrtScaled, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem abs_mul_inv_sqrt_eq (v : ℕ → ℝ) (n : ℕ) :
    |v n| * (Real.sqrt n)⁻¹ = |sqrtScaled v n| / n := by
  rw [abs_sqrtScaled, mul_comm (Real.sqrt n), mul_div_assoc, Real.sqrt_div_self]

theorem abs_eq_sqrtScaled_div {v : ℕ → ℝ} (hv0 : v 0 = 0) (n : ℕ) :
    |v n| = |sqrtScaled v n| / Real.sqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hv0, sqrtScaled]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rw [abs_sqrtScaled]
  field_simp

theorem abs_mul_inv_eq_rpow (v : ℕ → ℝ) (n : ℕ) :
    |v n| * (n : ℝ)⁻¹ = |sqrtScaled v n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sqrtScaled]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_sqrtScaled, Real.sqrt_eq_rpow, mul_comm (_ ^ _) |v n|, mul_assoc,
    ← Real.rpow_add hn0, show (1 / 2 : ℝ) + -(1 + 1 / 2) = -1 by norm_num, Real.rpow_neg_one]

theorem abs_mul_rpow_three_quarters_eq (v : ℕ → ℝ) (n : ℕ) :
    |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)) = |sqrtScaled v n| * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sqrtScaled]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_sqrtScaled, Real.sqrt_eq_rpow, mul_comm (_ ^ _) |v n|, mul_assoc,
    ← Real.rpow_add hn0, show (1 / 2 : ℝ) + -(5 / 4) = -(3 / 4) by norm_num]

/-- `Σ_{n≤N} |v(n)| ≤ A + η C √N` and its cut-off form `Σ_{n≤N, n≤x} |v(n)| ≤ A + η C √x`. -/
theorem sum_abs_indicator_le {v : ℕ → ℝ} (hv0 : v 0 = 0) {A η : ℝ} (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hsq : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.range (N + 1), |sqrtScaled v n| / Real.sqrt n ≤
      A + η * ((2 * Real.log 4 + 16) * Real.sqrt N)) (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.range (N + 1), |v n| * (if (n : ℝ) ≤ x then 1 else 0) ≤
      A + η * (2 * Real.log 4 + 16) * Real.sqrt x := by
  have hC : 0 ≤ 2 * Real.log 4 + 16 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hsub : ∑ n ∈ Finset.range (N + 1), |v n| * (if (n : ℝ) ≤ x then 1 else 0) ≤
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), |v n| := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => abs_nonneg _
    rw [Finset.mem_filter] at hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hn.2))
  refine hsub.trans ?_
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | h1
  · rw [h0]; simp [hv0]; positivity
  · have e : ∑ n ∈ Finset.range (⌊x⌋₊ + 1), |v n| =
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1), |sqrtScaled v n| / Real.sqrt n :=
      Finset.sum_congr rfl fun n _ => abs_eq_sqrtScaled_div hv0 n
    rw [e]
    refine (hsq _ h1).trans ?_
    have : Real.sqrt ⌊x⌋₊ ≤ Real.sqrt x := Real.sqrt_le_sqrt (Nat.floor_le hx)
    have : η * ((2 * Real.log 4 + 16) * Real.sqrt ⌊x⌋₊) ≤
        η * ((2 * Real.log 4 + 16) * Real.sqrt x) := by gcongr
    linarith

/-! ## The pairing tail against `1/n` -/

/-- **The pairing tail**: if `|m(n)| ≤ B₁/n`, the pairing sum is summable and its part beyond `N`
is at least `−B₁ Σ_{n>N} |v(n)|/n`. -/
theorem pairing_tail_inv {v : ℕ → ℝ} (hv0 : v 0 = 0)
    (hs : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹) {B₁ : ℝ} {m : ℕ → ℝ}
    (hm : ∀ n : ℕ, 1 ≤ n → |m n| ≤ B₁ * (n : ℝ)⁻¹) (N : ℕ) :
    Summable (fun n => v n * m n) ∧
      ∑ n ∈ Finset.range (N + 1), v n * m n -
        B₁ * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹ ≤ ∑' n, v n * m n := by
  have hbound : ∀ n : ℕ, |v n * m n| ≤ B₁ * (|v n| * (n : ℝ)⁻¹) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv0]; simp
    rw [abs_mul]
    calc |v n| * |m n| ≤ |v n| * (B₁ * (n : ℝ)⁻¹) := mul_le_mul_of_nonneg_left (hm n hn) (abs_nonneg _)
      _ = B₁ * (|v n| * (n : ℝ)⁻¹) := by ring
  have hf : Summable fun n => v n * m n :=
    Summable.of_norm_bounded (hs.mul_left B₁) fun n => by rw [Real.norm_eq_abs]; exact hbound n
  refine ⟨hf, ?_⟩
  rw [← hf.sum_add_tsum_nat_add (N + 1)]
  have hs' := (summable_nat_add_iff (N + 1)).mpr hs
  have hs2 : Summable fun i : ℕ => |v (i + (N + 1)) * m (i + (N + 1))| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => hbound _) (hs'.mul_left _)
  have habs : |∑' i : ℕ, v (i + (N + 1)) * m (i + (N + 1))| ≤
      B₁ * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹ :=
    calc |∑' i : ℕ, v (i + (N + 1)) * m (i + (N + 1))|
        ≤ ∑' i : ℕ, |v (i + (N + 1)) * m (i + (N + 1))| := abs_tsum_le_tsum_abs hs2
      _ ≤ ∑' i : ℕ, B₁ * (|v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹) :=
          hs2.tsum_le_tsum (fun i => hbound _) (hs'.mul_left _)
      _ = _ := by rw [tsum_mul_left]
  linarith [(abs_le.mp habs).1]

/-- The tail `Σ_{n>N} |v(n)|/n` of a deviation notch-bounded at level `η` is
`≤ η C_T N^{−1/2}` for large `N`. -/
theorem exists_tail_inv_le {v : ℕ → ℝ} {η : ℝ} (hd : NotchBounded (sqrtScaled v) η) :
    ∃ P₀ : ℕ, ∀ N : ℕ, P₀ ≤ N → 1 ≤ N →
      ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹ ≤
        η * (vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹) := by
  obtain ⟨P₀, hP₀⟩ := hd.tail
  refine ⟨P₀, fun N hPN hN => Real.tsum_le_of_sum_range_le (fun i => by positivity) fun m => ?_⟩
  have e : ∑ i ∈ Finset.range m, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹ =
      ∑ n ∈ Finset.Ioc N (N + m), |sqrtScaled v n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) := by
    have hI : Finset.Ioc N (N + m) = Finset.Ico (N + 1) (N + 1 + m) := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range, show N + 1 + m - (N + 1) = m by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show N + 1 + i = i + (N + 1) by omega, abs_mul_inv_eq_rpow]
  rw [e]
  exact hP₀ N hPN hN (N + m)

/-! ## Elementary logarithm bounds -/

theorem log_add_one_le_two_log {L : ℝ} (hL : 32 ≤ L) : Real.log L + 1 ≤ 2 * Real.log (L - 1) := by
  have h1 : Real.log L ≤ Real.log 2 + Real.log (L - 1) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log 2 + 1 ≤ Real.log (L - 1) := by
    have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have h3 : Real.log 2 + 1 = Real.log (2 * Real.exp 1) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    rw [h3]
    exact Real.log_le_log (by positivity) (by linarith)
  linarith

/-! ## The pairing side -/

/-- **The pairing side of the notch.** For a nonnegative weight `q` with a bounded entire extension
`Q`, the shifted-pole pairing, its tail beyond `N`, and the defect give
`Σ_{n≤N} v(n) Re M_Ω(log n) ≤ C_df/(2 + L) Σ_{n≤N} |v(n)| + C_sh (1 + L) Σ_{n>N} |v(n)|/n`. -/
theorem exists_sum_re_mixMoment_le_of_pairing {q : ℝ → ℝ} {Q : ℂ → ℂ}
    (hQd : Differentiable ℂ Q) {CQ : ℝ} (hQb1 : ∀ z : ℂ, |z.im| ≤ 1 → ‖Q z‖ ≤ CQ)
    (hQq : ∀ t : ℝ, Q t = q t) (hq0 : ∀ t, 0 ≤ q t) (hqc : Continuous q)
    (hqb : ∀ t, |q t| ≤ CQ) :
    ∃ Csh Cdf : ℝ, 0 ≤ Csh ∧ 0 ≤ Cdf ∧ ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ {A : ℝ}, 0 ≤ A →
      (∀ n, |v n| ≤ 2 * Real.log n + A) →
      Summable (fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ))) →
      Summable (fun n : ℕ => |v n| * (n : ℝ)⁻¹) →
      PositiveDefiniteOnReal (fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) →
      ∀ {L : ℝ}, 0 ≤ L → ∀ N : ℕ,
      ∑ n ∈ Finset.range (N + 1), v n * (mixMoment L q (Real.log n)).re ≤
        Cdf / (2 + L) * ∑ n ∈ Finset.range (N + 1), |v n| +
          Csh * (1 + L) * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹ := by
  obtain ⟨Csh, hCsh0, hsh⟩ := exists_norm_shiftMoment_le hQd hQb1 hQq
  obtain ⟨Cdf, hCdf0, hdf⟩ := exists_norm_defectMoment_le hqb
  refine ⟨Csh, Cdf, hCsh0, hCdf0, fun {v} hv0 {A} hA ha hs34 hs1 hPD {L} hL0 N => ?_⟩
  have hpair := sum_mul_re_shiftMoment_nonpos hv0 hA ha hs34 hPD L hQd
    (fun z hz => hQb1 z (by linarith)) hQq hq0
  have hm : ∀ n : ℕ, 1 ≤ n → |(shiftMoment L q (Real.log n)).re| ≤
      (Csh * (1 + L)) * (n : ℝ)⁻¹ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    refine (Complex.abs_re_le_norm _).trans ((hsh L hL0 _ (Real.log_natCast_nonneg n)).trans ?_)
    rw [Real.exp_neg, Real.exp_log hn0]
  obtain ⟨-, htail⟩ := pairing_tail_inv hv0 hs1 hm N
  have hdefect : ∑ n ∈ Finset.range (N + 1), v n * (defectMoment L q (Real.log n)).re ≤
      Cdf / (2 + L) * ∑ n ∈ Finset.range (N + 1), |v n| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have h := (Complex.abs_re_le_norm _).trans (hdf L hL0 (Real.log n))
    calc v n * (defectMoment L q (Real.log n)).re ≤ |v n| * |(defectMoment L q (Real.log n)).re| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ |v n| * (Cdf / (2 + L)) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = Cdf / (2 + L) * |v n| := by ring
  have hsplit : ∑ n ∈ Finset.range (N + 1), v n * (mixMoment L q (Real.log n)).re =
      ∑ n ∈ Finset.range (N + 1), v n * (shiftMoment L q (Real.log n)).re +
        ∑ n ∈ Finset.range (N + 1), v n * (defectMoment L q (Real.log n)).re := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [shiftMoment_eq_sub L hqc hqb, Complex.sub_re]
    ring
  linarith

/-! ## The scale bound -/

/-- **The scale bound of the refined notch, abstract form at a fixed level.** Let `q ≥ 0` have a
bounded entire extension, and suppose the per-scale notch moments of `q` dominate
`e u · rampSum(v W) − D E_u(v)`. Then there are `κ₁ > 0` and `K`, depending only on these data,
with the following property. Let `d = √n v` be notch-bounded at level `η`, and suppose the partial
sums `S(k)` of `a(n) = v(n) W(n)` are bounded below, with `S(k) ≥ Y > 0` for `k ≥ T`. Then
`κ₁ Y log(L − 1) ≤ C + η K log(L − 1)` for all large `L`. -/
theorem exists_ramp_scale_bound_bounded_of {q : ℝ → ℝ} {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q)
    {CQ : ℝ} (hQb1 : ∀ z : ℂ, |z.im| ≤ 1 → ‖Q z‖ ≤ CQ) (hQq : ∀ t : ℝ, Q t = q t)
    (hq0 : ∀ t, 0 ≤ q t) (hqc : Continuous q) (hqb : ∀ t, |q t| ≤ CQ)
    {W : ℕ → ℝ} {eP K₀ Dr : ℝ} (heP0 : 0 < eP) (hK₀ : 1 ≤ K₀) (hDr0 : 0 ≤ Dr)
    (hDr : ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ (N : ℕ) {u : ℝ}, 16 ≤ u →
      eP * u * rampSum (fun n => v n * W n) N K₀ notchProfileMass notchProfileLogMass u -
        Dr * refErrSum v (Finset.range (N + 1)) (2 * K₀ ^ 3) 7 u ≤
      ∑ n ∈ Finset.range (N + 1), v n * (ZetaNotch.weightedMoment u q (Real.log n)).re) :
    ∃ κ₁ Kc : ℝ, 0 < κ₁ ∧ 0 ≤ Kc ∧ ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ {A : ℝ}, 0 ≤ A →
      (∀ n, |v n| ≤ 2 * Real.log n + A) →
      PositiveDefiniteOnReal (fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) →
      ∀ {η : ℝ}, 0 < η → NotchBounded (sqrtScaled v) η →
      ∀ {Y B : ℝ} {T : ℕ}, 0 < Y → 1 ≤ T →
      (∀ k, -B ≤ rampPartial (fun n => v n * W n) k) →
      (∀ k, T ≤ k → Y ≤ rampPartial (fun n => v n * W n) k) →
      ∃ Cη L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
        κ₁ * Y * Real.log (L - 1) ≤ Cη + η * Kc * Real.log (L - 1) := by
  classical
  obtain ⟨C₁, C₂, hC₁0, hC₂0, hmix⟩ := exists_sum_re_mixMoment_ge_of_ramp hqc hqb
  obtain ⟨Csh, Cdf, hCsh0, hCdf0, hpair⟩ :=
    exists_sum_re_mixMoment_le_of_pairing hQd hQb1 hQq hq0 hqc hqb
  obtain ⟨CU, hCU0, hCU⟩ := exists_critUniform_le 4 7 (by norm_num)
  have hCc0 : 0 ≤ 2 * Real.log 4 + 16 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hβpos : 0 < notchProfileMass := lt_of_lt_of_le one_pos one_le_notchProfileMass
  refine ⟨eP * notchProfileMass * (2 * Real.exp (-1)),
    Dr * gaussHalf * (4 + 2 * (2 * Real.log 4 + 16) * Real.sqrt (2 * K₀ ^ 3)),
    mul_pos (mul_pos heP0 hβpos) (by positivity),
    mul_nonneg (mul_nonneg hDr0 gaussHalf_nonneg) (by positivity),
    fun {v} hv0 {A} hA ha hPD {η} hη hd {Y B T} hY hT hB hc => ?_⟩
  set a : ℕ → ℝ := fun n => v n * W n with hadef
  have ha0 : a 0 = 0 := by simp [hadef, hv0]
  have hβ₀ : 1 ≤ notchProfileMass := one_le_notchProfileMass
  obtain ⟨CG, hCG⟩ := exists_rampSum_ge a ha0 (β₁ := notchProfileLogMass) hY.le
    (by linarith : (0 : ℝ) ≤ notchProfileMass) notchProfile_log_two_add_nonneg hK₀ hT hB hc
  set G : ℝ := gaussHalf with hGdef
  have hG0 : 0 ≤ G := gaussHalf_nonneg
  set Cc : ℝ := 2 * Real.log 4 + 16 with hCc
  set c' : ℝ := 2 * K₀ ^ 3 with hc'
  have hc'0 : 0 < c' := by positivity
  set k : ℝ := eP * notchProfileMass * Y with hk
  have hk0 : 0 < k := by positivity
  set CG' : ℝ := max CG 0 with hCG'
  set C₀ : ℝ := eP * CG' with hC₀
  have hC₀0 : 0 ≤ C₀ := mul_nonneg heP0.le (le_max_right _ _)
  obtain ⟨A₁, hA₁0, hA₁⟩ := hd.harm
  obtain ⟨A₂, hA₂0, hA₂⟩ := hd.sqrt
  obtain ⟨P₀, hP₀⟩ := exists_tail_inv_le hd
  set CT : ℝ := vonMangoldtThreeHalvesTail with hCT
  have hCT0 : 0 ≤ CT := vonMangoldtThreeHalvesTail_nonneg
  refine ⟨C₀ * G + Dr * G * (A₁ + η * (Real.log 4 + 3) + 2 * A₂ + 133 * CU * (A₂ + 2 * (η * Cc))) +
    (2 * (C₁ + C₂) + Cdf) * (A₂ + 2 * (η * Cc)) + Csh * (η * CT), 32 + T + P₀, fun L hL => ?_⟩
  have hTP : (0 : ℝ) ≤ T + P₀ := by positivity
  have hL32 : 32 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  -- the truncation `N = ⌈(1 + L)²⌉`
  set N : ℕ := ⌈(1 + L) ^ 2⌉₊ with hNdef
  have hN1 : (1 + L) ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNL : L ≤ (N : ℝ) := by nlinarith
  have hNT : T ≤ N := by
    have : (T : ℝ) ≤ N := by have := (Nat.cast_nonneg P₀ : (0 : ℝ) ≤ P₀); linarith
    exact_mod_cast this
  have hNP : P₀ ≤ N := by
    have : (P₀ : ℝ) ≤ N := by have := (Nat.cast_nonneg T : (0 : ℝ) ≤ T); linarith
    exact_mod_cast this
  have hNpos : 1 ≤ N := hT.trans hNT
  have hsqN : Real.sqrt N ≤ 2 * (1 + L) := by
    have hNle : (N : ℝ) ≤ 2 * (1 + L) ^ 2 := by
      have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (1 + L) ^ 2 by positivity)
      nlinarith
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hsqN' : 1 + L ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; exact hN1
  set F := Finset.range (N + 1) with hF
  -- summability and masses
  have hs1 : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹ :=
    (hd.summable (1 + 1 / 2) (by norm_num)).congr fun n =>
      (abs_mul_inv_eq_rpow v n).symm
  have hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)) :=
    (hd.summable (5 / 4) (by norm_num)).congr fun n =>
      (abs_mul_rpow_three_quarters_eq v n).symm
  set TF : ℝ := ∑ n ∈ F, |v n| with hTF
  have hTF0 : 0 ≤ TF := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hTFb : TF ≤ A₂ + η * Cc * Real.sqrt N := by
    have e : TF = ∑ n ∈ Finset.range (N + 1), |sqrtScaled v n| / Real.sqrt n :=
      Finset.sum_congr rfl fun n _ => abs_eq_sqrtScaled_div hv0 n
    rw [e]
    have := hA₂ N hNpos
    linarith
  have hS₁ : ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ ≤
      A₁ + η * (Real.log N + (Real.log 4 + 4)) := by
    have e : ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ =
        ∑ n ∈ Finset.range (N + 1), |sqrtScaled v n| / n :=
      Finset.sum_congr rfl fun n _ => abs_mul_inv_sqrt_eq v n
    rw [e]; exact hA₁ N hNpos
  have hAB : ∀ x : ℝ, 0 ≤ x → ∑ n ∈ F, |v n| * (if (n : ℝ) ≤ x then 1 else 0) ≤
      A₂ + η * Cc * Real.sqrt x := fun x hx =>
    sum_abs_indicator_le hv0 hA₂0 hη.le (fun M hM => hA₂ M hM) N hx
  -- the per-scale inequality
  have hE : ∀ u, 16 ≤ u → u * (k * Real.log u - C₀) - Dr * refErrSum v F c' 7 u ≤
      ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u q (Real.log n)).re := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have h1 := hDr hv0 N hu
    have h2 := hCG N hNT u (by linarith)
    have h3 : notchProfileMass * Y * Real.log u - CG' ≤
        rampSum a N K₀ notchProfileMass notchProfileLogMass u := by
      have := le_max_left CG 0
      linarith
    have h4 : u * (k * Real.log u - C₀) ≤
        eP * u * rampSum a N K₀ notchProfileMass notchProfileLogMass u := by
      calc u * (k * Real.log u - C₀) = eP * u * (notchProfileMass * Y * Real.log u - CG') := by
            rw [hk, hC₀]; ring
        _ ≤ eP * u * rampSum a N K₀ notchProfileMass notchProfileLogMass u :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  -- the error integral
  obtain ⟨hEint, hEb⟩ := setIntegral_refErrSum_le hL32 (v := v) (F := F) hc'0 (K := 7)
    (S₁ := A₁ + η * (Real.log N + (Real.log 4 + 4))) (A := A₂) (B := η * Cc)
    (T := A₂ + η * Cc * Real.sqrt N) hA₂0 (by positivity) hCU0 hS₁ hAB hTFb hCU
  -- the mixture and the pairing
  have hlow := hmix F hL32 hDr0 hk0.le hC₀0 hE hEint
  have hup := hpair hv0 hA ha hs34 hs1 hPD hL0 N
  have htail := hP₀ N hNP hNpos
  -- bookkeeping
  set lg : ℝ := Real.log (L - 1) with hlg
  have hlogN : Real.log N + (Real.log 4 + 4) ≤ 4 * lg + (Real.log 4 + 3) := by
    have := one_add_log_ceil_le hL32; linarith
  have hlogL := log_add_one_le_two_log hL32
  have hlg0 : 0 ≤ lg := Real.log_nonneg (by linarith)
  have hηCc : 0 ≤ η * Cc := by positivity
  have hT3 : (A₂ + η * Cc * Real.sqrt N) / (1 + L) ≤ A₂ + 2 * (η * Cc) :=
    div_one_add_le_split hL0 hA₂0 hηCc (le_of_eq (by ring)) hsqN
  have hTFL : TF / (1 + L) ≤ A₂ + 2 * (η * Cc) :=
    div_one_add_le_split hL0 hA₂0 hηCc (hTFb.trans (le_of_eq (by ring))) hsqN
  obtain ⟨-, hsm2, hsm3⟩ := abs_small_errors_le hL32 hTF0 hCU0 hC₁0 hC₂0 hCdf0
  have htail' : Csh * (1 + L) * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹ ≤
      Csh * (η * CT) := by
    have hq : (1 + L) * (Real.sqrt N)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; exact hsqN'
    have h1 : (1 + L) * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹ ≤ η * CT := by
      calc (1 + L) * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹
          ≤ (1 + L) * (η * (CT * (Real.sqrt N)⁻¹)) :=
            mul_le_mul_of_nonneg_left htail (by linarith)
        _ = η * CT * ((1 + L) * (Real.sqrt N)⁻¹) := by ring
        _ ≤ η * CT * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
        _ = η * CT := mul_one _
    calc Csh * (1 + L) * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹
        = Csh * ((1 + L) * ∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ Csh * (η * CT) := mul_le_mul_of_nonneg_left h1 hCsh0
  have hbr : A₁ + η * (Real.log N + (Real.log 4 + 4)) + 2 * A₂ +
      η * Cc * Real.sqrt c' * (Real.log L + 1) + 133 * CU * ((A₂ + η * Cc * Real.sqrt N) / (1 + L)) ≤
      A₁ + η * (Real.log 4 + 3) + 2 * A₂ + 133 * CU * (A₂ + 2 * (η * Cc)) +
        η * (4 + 2 * Cc * Real.sqrt c') * lg := by
    have h1 := mul_le_mul_of_nonneg_left hlogN hη.le
    have h2 := mul_le_mul_of_nonneg_left hlogL (by positivity : (0 : ℝ) ≤ η * Cc * Real.sqrt c')
    have h3 := mul_le_mul_of_nonneg_left hT3 (by positivity : (0 : ℝ) ≤ 133 * CU)
    linarith
  have hIb : Dr * (∫ u in Ioi 16, scaleWeight L u / u * refErrSum v F c' 7 u) ≤
      Dr * G * (A₁ + η * (Real.log 4 + 3) + 2 * A₂ + 133 * CU * (A₂ + 2 * (η * Cc))) +
        η * (Dr * G * (4 + 2 * Cc * Real.sqrt c')) * lg := by
    have h1 := mul_le_mul_of_nonneg_right hbr hG0
    have h2 := mul_le_mul_of_nonneg_left (hEb.trans h1) hDr0
    linarith
  have hsm2' := mul_le_mul_of_nonneg_left hTFL (by positivity : (0 : ℝ) ≤ 2 * (C₁ + C₂))
  have hsm3' := mul_le_mul_of_nonneg_left hTFL hCdf0
  have hfin : k * (2 * Real.exp (-1) * lg) ≤
      C₀ * G + Dr * G * (A₁ + η * (Real.log 4 + 3) + 2 * A₂ + 133 * CU * (A₂ + 2 * (η * Cc))) +
        (2 * (C₁ + C₂) + Cdf) * (A₂ + 2 * (η * Cc)) + Csh * (η * CT) +
        η * (Dr * G * (4 + 2 * Cc * Real.sqrt c')) * lg := by
    linarith
  have e1 : eP * notchProfileMass * (2 * Real.exp (-1)) * Y * lg =
      k * (2 * Real.exp (-1) * lg) := by rw [hk]; ring
  rw [e1]
  linarith

/-- **The scale bound of the refined notch, abstract form.** Let `q ≥ 0` have a bounded entire
extension, and suppose the per-scale notch moments of `q` dominate `e u · rampSum(v W) − D E_u(v)`.
Suppose the partial sums `S(k)` of `a(n) = v(n) W(n)` are bounded below, and `S(k) ≥ Y > 0` for
`k ≥ T`. Then there are `κ > 0` and `K` such that for every `η > 0` and all large `L`,
`κ log(L − 1) ≤ C_η + η K log(L − 1)`. -/
theorem exists_ramp_scale_bound_of {q : ℝ → ℝ} {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q)
    {CQ : ℝ} (hQb1 : ∀ z : ℂ, |z.im| ≤ 1 → ‖Q z‖ ≤ CQ) (hQq : ∀ t : ℝ, Q t = q t)
    (hq0 : ∀ t, 0 ≤ q t) (hqc : Continuous q) (hqb : ∀ t, |q t| ≤ CQ)
    {W : ℕ → ℝ} {eP K₀ Dr : ℝ} (heP0 : 0 < eP) (hK₀ : 1 ≤ K₀) (hDr0 : 0 ≤ Dr)
    (hDr : ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ (N : ℕ) {u : ℝ}, 16 ≤ u →
      eP * u * rampSum (fun n => v n * W n) N K₀ notchProfileMass notchProfileLogMass u -
        Dr * refErrSum v (Finset.range (N + 1)) (2 * K₀ ^ 3) 7 u ≤
      ∑ n ∈ Finset.range (N + 1), v n * (ZetaNotch.weightedMoment u q (Real.log n)).re)
    {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hd : NotchSmall (sqrtScaled v)) {Y B : ℝ} {T : ℕ} (hY : 0 < Y) (hT : 1 ≤ T)
    (hB : ∀ k, -B ≤ rampPartial (fun n => v n * W n) k)
    (hc : ∀ k, T ≤ k → Y ≤ rampPartial (fun n => v n * W n) k) :
    ∃ κ Kc : ℝ, 0 < κ ∧ 0 ≤ Kc ∧ ∀ η : ℝ, 0 < η → ∃ Cη L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      κ * Real.log (L - 1) ≤ Cη + η * Kc * Real.log (L - 1) := by
  obtain ⟨κ₁, Kc, hκ₁, hKc, h⟩ :=
    exists_ramp_scale_bound_bounded_of hQd hQb1 hQq hq0 hqc hqb heP0 hK₀ hDr0 hDr
  exact ⟨κ₁ * Y, Kc, mul_pos hκ₁ hY, hKc, fun η hη =>
    h hv0 hA ha hPD hη (hd.notchBounded hη) hY hT hB hc⟩

/-- **A bounded scale bound caps the level.** If `κ₁ Y log(L − 1) ≤ C + η K log(L − 1)` for all
large `L`, then `κ₁ Y ≤ η K`. -/
theorem le_of_log_scale_bound {a b C L₀ : ℝ}
    (h : ∀ L : ℝ, L₀ ≤ L → a * Real.log (L - 1) ≤ C + b * Real.log (L - 1)) : a ≤ b := by
  by_contra hab
  push Not at hab
  set δ : ℝ := a - b with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set L : ℝ := max L₀ (Real.exp (2 * |C| / δ + 1) + 1) with hLdef
  have h1 := h L (le_max_left _ _)
  have hL1 : Real.exp (2 * |C| / δ + 1) ≤ L - 1 := by
    linarith [le_max_right L₀ (Real.exp (2 * |C| / δ + 1) + 1)]
  have hlog : 2 * |C| / δ + 1 ≤ Real.log (L - 1) := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hL1)]; exact hL1
  have h3 : δ * (2 * |C| / δ + 1) ≤ δ * Real.log (L - 1) := mul_le_mul_of_nonneg_left hlog hδ0.le
  have h4 : δ * (2 * |C| / δ + 1) = 2 * |C| + δ := by field_simp
  have h5 := le_abs_self C
  have h6 : δ * Real.log (L - 1) = a * Real.log (L - 1) - b * Real.log (L - 1) := by rw [hδ]; ring
  have h7 := abs_nonneg C
  linarith

/-- **The scale bound of the refined notch.** Suppose the fibre partial sums `S(k)` of
`a(n) = v(n) mW(n)` are bounded below, and `S(k) ≥ Y > 0` for `k ≥ T`. Then there are `κ > 0` and
`K` such that for every `η > 0` and all large `L`, `κ log(L − 1) ≤ C_η + η K log(L − 1)`. -/
theorem exists_ramp_scale_bound (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀)
    {ε : ℝ} {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hd : NotchSmall (sqrtScaled v)) {Y B : ℝ} {T : ℕ} (hY : 0 < Y) (hT : 1 ≤ T)
    (hB : ∀ k, -B ≤ rampPartial (fun n => v n * mainWeight P ε n₀ n) k)
    (hc : ∀ k, T ≤ k → Y ≤ rampPartial (fun n => v n * mainWeight P ε n₀ n) k) :
    ∃ κ Kc : ℝ, 0 < κ ∧ 0 ≤ Kc ∧ ∀ η : ℝ, 0 < η → ∃ Cη L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      κ * Real.log (L - 1) ≤ Cη + η * Kc * Real.log (L - 1) := by
  obtain ⟨Dr, hDr0, hDr⟩ := exists_sum_re_weightedMoment_ge_ramp hP (K := 7) (by norm_num) ε hn₀
  obtain ⟨CQ, hCQ0, hQb1, hqb⟩ := exists_notchWeight_bound P ε n₀
  exact exists_ramp_scale_bound_of (differentiable_notchWeightC P ε n₀) hQb1
    (notchWeightC_ofReal P ε n₀) (notchWeight_nonneg P ε n₀) (continuous_notchWeight P ε n₀) hqb
    (eulerProduct_pos hP) (by exact_mod_cast twistBound_pos hP n₀) hDr0 hDr hv0 hA ha hPD hd hY hT
    hB hc

/-- **The scale bound is contradictory.** No `κ > 0` satisfies
`κ log(L − 1) ≤ C_η + η K log(L − 1)` for every `η > 0` and all large `L`. -/
theorem false_of_log_scale_bound {κ Kc : ℝ} (hκ : 0 < κ) (hKc : 0 ≤ Kc)
    (h : ∀ η : ℝ, 0 < η → ∃ Cη L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      κ * Real.log (L - 1) ≤ Cη + η * Kc * Real.log (L - 1)) : False := by
  set η : ℝ := κ / (2 * (Kc + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηK : η * Kc ≤ κ / 2 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨Cη, L₀, hL⟩ := h η hη0
  set L : ℝ := max L₀ (Real.exp (2 * |Cη| / κ + 1) + 1) with hLdef
  have h1 := hL L (le_max_left _ _)
  have hL1 : Real.exp (2 * |Cη| / κ + 1) ≤ L - 1 := by
    linarith [le_max_right L₀ (Real.exp (2 * |Cη| / κ + 1) + 1)]
  have hlog : 2 * |Cη| / κ + 1 ≤ Real.log (L - 1) := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hL1)]; exact hL1
  have hlg0 : 0 ≤ Real.log (L - 1) := le_trans (by positivity) hlog
  have h2 : η * Kc * Real.log (L - 1) ≤ κ / 2 * Real.log (L - 1) :=
    mul_le_mul_of_nonneg_right hηK hlg0
  have h3 : κ * (2 * |Cη| / κ + 1) ≤ κ * Real.log (L - 1) := mul_le_mul_of_nonneg_left hlog hκ.le
  have h4 : κ * (2 * |Cη| / κ + 1) = 2 * |Cη| + κ := by field_simp
  have h5 := le_abs_self Cη
  nlinarith

/-- **The fibre partial sums cannot stay above a positive level.** If the partial sums `S(k)` of
`a(n) = v(n) mW(n)` are bounded below and `S(k) ≥ Y` for `k ≥ T`, then `Y ≤ 0`. -/
theorem nonpos_of_rampPartial_ge (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀)
    {ε : ℝ} {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hd : NotchSmall (sqrtScaled v)) {Y B : ℝ} {T : ℕ} (hT : 1 ≤ T)
    (hB : ∀ k, -B ≤ rampPartial (fun n => v n * mainWeight P ε n₀ n) k)
    (hc : ∀ k, T ≤ k → Y ≤ rampPartial (fun n => v n * mainWeight P ε n₀ n) k) : Y ≤ 0 := by
  by_contra hY
  push Not at hY
  obtain ⟨κ, Kc, hκ, hKc, h⟩ := exists_ramp_scale_bound hP hn₀ hv0 hA ha hPD hd hY hT hB hc
  exact false_of_log_scale_bound hκ hKc h

/-! ## The fibres of the truncated main functional -/

theorem vecOf_eq_zero_of_prime {y n : ℕ} (hn : n.Prime) (hyn : y < n) :
    vecOf (WeilLogSummable.primesUpTo y) n = 0 := by
  funext p
  have hp := WeilLogSummable.mem_primesUpTo.mp p.2
  have hne : (p : ℕ) ≠ n := by omega
  simp [vecOf, hn.factorization, hne.symm]

theorem roughPart_eq_one_of_smooth {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) : roughPart P n₀ = 1 := by
  have h := eq_mul_roughPart (P := P) (n := n₀) (by have := hn₀.1; omega) hn₀ rfl
  have hn0 : 0 < n₀ := by have := hn₀.1; omega
  have : n₀ * roughPart P n₀ = n₀ * 1 := by rw [mul_one]; exact h.symm
  exact Nat.eq_of_mul_eq_mul_left hn0 this

/-- On the fibre `vecOf P n = vecOf P n₀` of a mode `n ≠ n₀`, the rough part exceeds `y`. -/
theorem lt_of_fibre {y n n₀ : ℕ} (hn₀ : IsSmoothOver (WeilLogSummable.primesUpTo y) n₀) (hn : n ≠ 0)
    (h1 : vecOf (WeilLogSummable.primesUpTo y) n = vecOf (WeilLogSummable.primesUpTo y) n₀)
    (hnn : n ≠ n₀) : y < n := by
  have hP : ∀ p ∈ WeilLogSummable.primesUpTo y, p.Prime := prime_of_mem_primesUpTo
  have hnr := eq_mul_roughPart (P := WeilLogSummable.primesUpTo y) hn hn₀ h1
  have hr1 : roughPart (WeilLogSummable.primesUpTo y) n ≠ 1 := fun hr => hnn (by rw [hnr, hr, mul_one])
  have hr0 := roughPart_pos (P := WeilLogSummable.primesUpTo y) hn
  have hy := lt_of_vecOf_eq_zero (y := y) (n := roughPart (WeilLogSummable.primesUpTo y) n)
    (by omega) (vecOf_roughPart hP hn)
  have : roughPart (WeilLogSummable.primesUpTo y) n ≤ n :=
    calc roughPart (WeilLogSummable.primesUpTo y) n ≤ n₀ * roughPart (WeilLogSummable.primesUpTo y) n :=
          Nat.le_mul_of_pos_left _ (by have := hn₀.1; omega)
      _ = n := hnr.symm
  omega

/-- **The low part of the fibre sum**: `Σ_{n≤y} v(n) mW(n) = ε v(n₀)`. -/
theorem sum_range_mainWeight_low {y n₀ : ℕ} (hn₀2 : 2 ≤ n₀) (hy : n₀ ≤ y) {v : ℕ → ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (ε : ℝ) :
    ∑ n ∈ Finset.range (y + 1), v n * mainWeight (WeilLogSummable.primesUpTo y) ε n₀ n =
      ε * v n₀ := by
  set P := WeilLogSummable.primesUpTo y with hPdef
  have hn₀s : IsSmoothOver P n₀ := isSmoothOver_primesUpTo hn₀2 hy
  rw [Finset.sum_eq_single n₀]
  · rw [mainWeight, if_neg (vecOf_ne_zero hn₀s), if_pos rfl, roughPart_eq_one_of_smooth hn₀s]
    simp; ring
  · intro n hn hnn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · rw [hv0, zero_mul]
      · rw [hv1, zero_mul]
    have hny : n ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have h0 : vecOf P n ≠ 0 := fun h0 => absurd (lt_of_vecOf_eq_zero h2 h0) (by omega)
    have h1 : vecOf P n ≠ vecOf P n₀ := fun h1 =>
      absurd (lt_of_fibre hn₀s (by omega) h1 hnn) (by omega)
    rw [mainWeight, if_neg h0, if_neg h1]; ring
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The high part of the fibre sum**, termwise: for `n > y` and `ε² = 1`,
`|v(n) mW(n) − 2 v(n)/√n| ≤ (2 + √n₀) |v(n)|/√n · 1_{n not prime}`. -/
theorem abs_mainWeight_high_sub_le {y n₀ n : ℕ} (hn₀2 : 2 ≤ n₀) (hy : n₀ ≤ y) (hyn : y < n)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (v : ℕ → ℝ) :
    |v n * mainWeight (WeilLogSummable.primesUpTo y) ε n₀ n - 2 * (v n * (Real.sqrt n)⁻¹)| ≤
      (2 + Real.sqrt n₀) * (|v n| * (Real.sqrt n)⁻¹) * (if n.Prime then 0 else 1) := by
  set P := WeilLogSummable.primesUpTo y with hPdef
  have hn₀s : IsSmoothOver P n₀ := isSmoothOver_primesUpTo hn₀2 hy
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hn0 : n ≠ 0 := by omega
  have hsq0 : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  by_cases h0 : vecOf P n = 0
  · have h1 : vecOf P n ≠ vecOf P n₀ := by rw [h0]; exact (vecOf_ne_zero hn₀s).symm
    rw [mainWeight, if_pos h0, if_neg h1, roughPart_eq_self h0, hε2]
    have : v n * (((1 + 1) * 1 + ε * 0) * (Real.sqrt n)⁻¹) - 2 * (v n * (Real.sqrt n)⁻¹) = 0 := by
      ring
    rw [this, abs_zero]
    split_ifs <;> positivity
  · have hnp : ¬ n.Prime := fun hp => h0 (vecOf_eq_zero_of_prime hp hyn)
    rw [if_neg hnp, mul_one]
    have hmW : |mainWeight P ε n₀ n| ≤ Real.sqrt n₀ * (Real.sqrt n)⁻¹ := by
      rw [mainWeight, if_neg h0]
      by_cases h1 : vecOf P n = vecOf P n₀
      · rw [if_pos h1]
        have hnr := eq_mul_roughPart (P := P) hn0 hn₀s h1
        have e : (Real.sqrt (roughPart P n))⁻¹ = Real.sqrt n₀ * (Real.sqrt n)⁻¹ := by
          have e' : (n : ℝ) = n₀ * roughPart P n := by exact_mod_cast hnr
          have hs0 : Real.sqrt n₀ ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))).ne'
          rw [e', Real.sqrt_mul (Nat.cast_nonneg _), mul_inv, ← mul_assoc, mul_inv_cancel₀ hs0,
            one_mul]
        rw [e, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hsq0]
        simp only [mul_zero, zero_add, mul_one]
        rw [hεa, one_mul]
      · rw [if_neg h1]; simp only [mul_zero, zero_add, zero_mul, abs_zero]; positivity
    calc |v n * mainWeight P ε n₀ n - 2 * (v n * (Real.sqrt n)⁻¹)|
        ≤ |v n * mainWeight P ε n₀ n| + |2 * (v n * (Real.sqrt n)⁻¹)| := abs_sub _ _
      _ = |v n| * |mainWeight P ε n₀ n| + 2 * (|v n| * (Real.sqrt n)⁻¹) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hsq0, abs_two]
      _ ≤ |v n| * (Real.sqrt n₀ * (Real.sqrt n)⁻¹) + 2 * (|v n| * (Real.sqrt n)⁻¹) := by
          gcongr
      _ = (2 + Real.sqrt n₀) * (|v n| * (Real.sqrt n)⁻¹) := by ring

/-! ## The theorem -/

/-- `g(n) = Λ(n)/n` on the composite `n`, and `0` on primes. -/
def nonprimeWeight (n : ℕ) : ℝ := if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ) / n

theorem nonprimeWeight_nonneg (n : ℕ) : 0 ≤ nonprimeWeight n := by
  unfold nonprimeWeight
  split_ifs
  · exact le_rfl
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)

/-- The tail `τ(y) = Σ_{n>y} g(n)`. -/
def nonprimeTail (y : ℕ) : ℝ := ∑' i : ℕ, nonprimeWeight (i + (y + 1))

theorem tendsto_nonprimeTail : Tendsto nonprimeTail atTop (𝓝 0) := by
  have h := (tendsto_sum_nat_add nonprimeWeight).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun y => ?_
  simp only [Function.comp_apply, nonprimeTail]

theorem sum_Ico_nonprimeWeight_le (y M : ℕ) :
    ∑ n ∈ Finset.Ico (y + 1) (M + 1), nonprimeWeight n ≤ nonprimeTail y := by
  have hs : Summable fun i : ℕ => nonprimeWeight (i + (y + 1)) :=
    (summable_nat_add_iff (y + 1)).mpr RHTower.WeilPrimeDeficit.summable_nonprime_vonMangoldt_div
  rw [Finset.sum_Ico_eq_sum_range]
  have e : ∑ k ∈ Finset.range (M + 1 - (y + 1)), nonprimeWeight (y + 1 + k) =
      ∑ k ∈ Finset.range (M + 1 - (y + 1)), nonprimeWeight (k + (y + 1)) :=
    Finset.sum_congr rfl fun k _ => by rw [add_comm]
  rw [e]
  exact hs.sum_le_tsum _ fun i _ => nonprimeWeight_nonneg _

/-- **Weil-cone rigidity for `o(Λ)` deviations, deviation form.** Let `v(0) = v(1) = 0`,
`|v(n)| ≤ 2 log n + A`, and let `−ψ_v` be positive definite. Suppose `d(n) = √n v(n)` is `o(Λ)` and
`Σ_n v(n)/√n = Σ_n d(n)/n` converges. Then `v = 0`. -/
theorem eq_zero_of_positiveDefinite_neg_nullPotential_of_isLittleO {v : ℕ → ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hd : IsLittleOVonMangoldt (sqrtScaled v)) {Y : ℝ}
    (hconv : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, v n * (Real.sqrt n)⁻¹) atTop (𝓝 Y)) :
    v = 0 := by
  funext n₀
  rw [Pi.zero_apply]
  rcases Nat.lt_or_ge n₀ 2 with h2 | hn₀2
  · interval_cases n₀
    · exact hv0
    · exact hv1
  obtain ⟨P₀, hP₀⟩ := hd 1 one_pos
  set s : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, v n * (Real.sqrt n)⁻¹ with hs
  have hsq₀ : 0 ≤ Real.sqrt n₀ := Real.sqrt_nonneg _
  have key : ∀ δ : ℝ, 0 < δ → |v n₀| ≤ (4 + Real.sqrt n₀) * δ := by
    intro δ hδ
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hconv (δ / 2) (by positivity)
    obtain ⟨y₁, hy₁⟩ := eventually_atTop.mp (tendsto_nonprimeTail.eventually_le_const hδ)
    set y : ℕ := n₀ + P₀ + N₀ + y₁ with hydef
    have hcau : ∀ M, y ≤ M →
        |∑ n ∈ Finset.Ico (y + 1) (M + 1), v n * (Real.sqrt n)⁻¹| ≤ δ := by
      intro M hM
      rw [Finset.sum_Ico_eq_sub _ (by omega)]
      have h1 := hN₀ (M + 1) (by omega)
      have h2 := hN₀ (y + 1) (by omega)
      rw [Real.dist_eq] at h1 h2
      have := abs_sub_le (s (M + 1)) Y (s (y + 1))
      rw [abs_sub_comm Y] at this
      simp only [hs] at this
      linarith
    have hsign : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ε * v n₀ ≤ (4 + Real.sqrt n₀) * δ := by
      intro ε hε
      set P := WeilLogSummable.primesUpTo y with hPdef
      have hP : ∀ p ∈ P, p.Prime := prime_of_mem_primesUpTo
      have hn₀s : IsSmoothOver P n₀ := isSmoothOver_primesUpTo hn₀2 (by omega)
      set a : ℕ → ℝ := fun n => v n * mainWeight P ε n₀ n with hadef
      have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
      have hfib : ∀ M, y ≤ M → |rampPartial a M - ε * v n₀ -
          2 * ∑ n ∈ Finset.Ico (y + 1) (M + 1), v n * (Real.sqrt n)⁻¹| ≤
          (2 + Real.sqrt n₀) * δ := by
        intro M hM
        have hsplit : rampPartial a M = ε * v n₀ +
            ∑ n ∈ Finset.Ico (y + 1) (M + 1), a n := by
          rw [rampPartial, ← Finset.sum_range_add_sum_Ico _ (by omega : y + 1 ≤ M + 1)]
          congr 1
          exact sum_range_mainWeight_low hn₀2 (by omega) hv0 hv1 ε
        rw [hsplit, add_sub_cancel_left, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ n ∈ Finset.Ico (y + 1) (M + 1), |a n - 2 * (v n * (Real.sqrt n)⁻¹)|
            ≤ ∑ n ∈ Finset.Ico (y + 1) (M + 1), (2 + Real.sqrt n₀) * nonprimeWeight n := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hyn : y < n := by have := (Finset.mem_Ico.mp hn).1; omega
              refine (abs_mainWeight_high_sub_le hn₀2 (by omega) hyn hε v).trans ?_
              rw [mul_assoc]
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              unfold nonprimeWeight
              split_ifs with hp
              · simp
              · rw [mul_one, abs_mul_inv_sqrt_eq]
                have := hP₀ n (by omega)
                rw [one_mul] at this
                exact div_le_div_of_nonneg_right this (Nat.cast_nonneg n)
          _ = (2 + Real.sqrt n₀) * ∑ n ∈ Finset.Ico (y + 1) (M + 1), nonprimeWeight n := by
              rw [Finset.mul_sum]
          _ ≤ (2 + Real.sqrt n₀) * δ := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact (sum_Ico_nonprimeWeight_le y M).trans (hy₁ y (by omega))
      have hc : ∀ M, y ≤ M → ε * v n₀ - (4 + Real.sqrt n₀) * δ ≤ rampPartial a M := by
        intro M hM
        have h1 := abs_le.mp (hfib M hM)
        have h2 := abs_le.mp (hcau M hM)
        linarith
      have hB : ∀ M, |rampPartial a M| ≤ |v n₀| + (4 + Real.sqrt n₀) * δ +
          ∑ k ∈ Finset.range y, |rampPartial a k| := by
        intro M
        have hsum0 : 0 ≤ ∑ k ∈ Finset.range y, |rampPartial a k| :=
          Finset.sum_nonneg fun k _ => abs_nonneg _
        rcases lt_or_ge M y with hMy | hMy
        · have := Finset.single_le_sum (f := fun k => |rampPartial a k|)
            (fun k _ => abs_nonneg _) (Finset.mem_range.mpr hMy)
          have : 0 ≤ (4 + Real.sqrt n₀) * δ := by positivity
          linarith [abs_nonneg (v n₀)]
        · have h1 := abs_le.mp (hfib M hMy)
          have h2 := abs_le.mp (hcau M hMy)
          have h3 : |ε * v n₀| = |v n₀| := by rw [abs_mul, hεa, one_mul]
          have h4 := abs_le.mp (le_of_eq h3)
          rw [abs_le]
          constructor <;> nlinarith [abs_nonneg (v n₀), le_abs_self (ε * v n₀),
            neg_abs_le (ε * v n₀)]
      have := nonpos_of_rampPartial_ge hP hn₀s hv0 hA ha hPD hd.notchSmall (T := y) (by omega)
        (B := |v n₀| + (4 + Real.sqrt n₀) * δ + ∑ k ∈ Finset.range y, |rampPartial a k|)
        (fun M => by have := hB M; have := neg_abs_le (rampPartial a M); linarith) hc
      linarith
    have h1 := hsign 1 (Or.inl rfl)
    have h2 := hsign (-1) (Or.inr rfl)
    rw [abs_le]
    constructor <;> linarith
  by_contra hne
  have hpos : 0 < |v n₀| := abs_pos.mpr hne
  have h := key (|v n₀| / (2 * (4 + Real.sqrt n₀))) (by positivity)
  have e : (4 + Real.sqrt n₀) * (|v n₀| / (2 * (4 + Real.sqrt n₀))) = |v n₀| / 2 := by
    field_simp
  linarith

/-- **Weil-cone rigidity for `o(Λ)` deviations.** A full-cone Weil-positive `lam` with
`lam − Λ = o(Λ)` (for every `η > 0`, `|lam(n) − Λ(n)| ≤ η Λ(n)` for all large `n`) equals `Λ` on
every `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_isLittleO {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam)
    (hd : IsLittleOVonMangoldt fun n => lam n - ArithmeticFunction.vonMangoldt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hv1 : v 1 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsc : ∀ n, sqrtScaled v n = WeilOneSided.coneDeviation lam n := by
    intro n
    simp only [sqrtScaled, hv, RHTower.WeilExcess.weilDeviation, WeilOneSided.coneDeviation]
    split_ifs with h2
    · have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      field_simp
    · simp
  have hcd : IsLittleOVonMangoldt (WeilOneSided.coneDeviation lam) := fun η hη => by
    obtain ⟨P₀, hP₀⟩ := hd η hη
    refine ⟨P₀, fun n hn => ?_⟩
    unfold WeilOneSided.coneDeviation
    split_ifs
    · exact hP₀ n hn
    · rw [abs_zero]; exact mul_nonneg hη.le ArithmeticFunction.vonMangoldt_nonneg
  have hdv : IsLittleOVonMangoldt (sqrtScaled v) := fun η hη => by
    obtain ⟨P₀, hP₀⟩ := hcd η hη
    exact ⟨P₀, fun n hn => by rw [hsc]; exact hP₀ n hn⟩
  obtain ⟨Y, hY⟩ := WeilOneSided.exists_tendsto_sum_coneDeviation_div hW hcd
  have hconv : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, v n * (Real.sqrt n)⁻¹) atTop (𝓝 Y) := by
    refine hY.congr fun N => Finset.sum_congr rfl fun n _ => ?_
    rw [← hsc, sqrtScaled, mul_comm (Real.sqrt n), mul_div_assoc, Real.sqrt_div_self]
  have h0 := eq_zero_of_positiveDefinite_neg_nullPotential_of_isLittleO hv0 hv1 hC0 hC hPD hdv hconv
  intro n hn
  have h := congrFun h0 n
  rw [hv, RHTower.WeilExcess.weilDeviation, if_pos hn, Pi.zero_apply] at h
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hsq.ne'

/-- **No bounded prime deviation.** A full-cone Weil-positive `lam` that agrees with `Λ` off the
primes and has `|lam(p) − log p| ≤ C` on the primes equals `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_bounded_prime_deviation {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam)
    (hoff : ∀ n, 2 ≤ n → ¬ n.Prime → lam n = ArithmeticFunction.vonMangoldt n) {C : ℝ}
    (hC : ∀ p, p.Prime → |lam p - ArithmeticFunction.vonMangoldt p| ≤ C) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine eq_vonMangoldt_of_weilPositiveFull_of_isLittleO hW fun η hη => ?_
  refine ⟨⌈Real.exp (|C| / η)⌉₊ + 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  by_cases hp : n.Prime
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    refine (hC n hp).trans ((le_abs_self C).trans ?_)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hexp : Real.exp (|C| / η) ≤ n := by
      have := Nat.le_ceil (Real.exp (|C| / η))
      have : ((⌈Real.exp (|C| / η)⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega)
      linarith
    have hlog : |C| / η ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn0]; exact hexp
    rw [div_le_iff₀ hη] at hlog
    linarith
  · show |lam n - ArithmeticFunction.vonMangoldt n| ≤ _
    rw [hoff n hn2 hp, sub_self, abs_zero]
    exact mul_nonneg hη.le ArithmeticFunction.vonMangoldt_nonneg

/-- **RH as a Weil-positive system asymptotic to `Λ`.** RH holds iff some full-cone Weil-positive
`lam` has `lam − Λ = o(Λ)`; every such `lam` equals `Λ`. -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_isLittleO :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, RHTower.WeilPositiveFull lam ∧
      IsLittleOVonMangoldt fun n => lam n - ArithmeticFunction.vonMangoldt n := by
  constructor
  · intro hRH
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, fun η hη => ⟨0, ?_⟩⟩
    intro n _
    show |ArithmeticFunction.vonMangoldt n - ArithmeticFunction.vonMangoldt n| ≤ _
    rw [sub_self, abs_zero]
    exact mul_nonneg hη.le ArithmeticFunction.vonMangoldt_nonneg
  · rintro ⟨lam, hW, hd⟩
    have h := eq_vonMangoldt_of_weilPositiveFull_of_isLittleO hW hd
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

end RHTower.WeilAbscissa
