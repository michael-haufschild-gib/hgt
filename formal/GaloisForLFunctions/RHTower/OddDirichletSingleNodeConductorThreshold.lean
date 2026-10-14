import GaloisForLFunctions.RHTower.OddDirichletSingleNodeFakeProducer
import GaloisForLFunctions.RHTower.DigammaVerticalLogGrowth

/-!
# The single-node threshold for odd Dirichlet data lies in `(3, 5]`

For an odd primitive character of conductor `q` the archimedean symbol of the explicit formula is
`S_q(τ) = Re ψ(¾ + iτ/2) − log π + log q`, with deficit `c_q = −S_q(0)`.  A Weil-positive weight
supported on the single node `m ≥ 2` exists exactly when `S_q(τ) + b cos(τ log m) ≥ 0` for every
`τ`, for some real `b` (a weight `λ` at `m` contributes `b = −2λ/√m`).

**Conductor at least `5`** (`oddDirichletSingleNodeSymbol_nonneg_two_of_five_le`).  For every
`q ≥ 5` the weight `−c_q√2/2` at the node `2` (`oddSingleNodeWeight q 2`) is Weil-positive.  This
extends `oddDirichletSingleNodeSymbol_nonneg_two` from `q ≥ 7` to `q ≥ 5`.

**Conductor `3`** (`exists_oddConductorThree_singleNode_neg`,
`not_forall_oddConductorThree_singleNodeSymbol_nonneg`).  For every node `m ≥ 2` and every real
weight, the single-node symbol is negative somewhere.  So the Weil cone of the conductor-`3` odd
data contains no weight supported on one node.

Proofs.
* The Gauss series gives the exact expansion
  `Re ψ(a + iy) − ψ(a) = Σ_{n≥0} y²/((a + n)((a + n)² + y²))`
  (`hasSum_re_digamma_vertical_sub`).  Every term is nonnegative and increasing in `y²`.
* Lower bound: the first three terms.  For `y² ≤ 2` each term is at least `y²` times its value at
  `y² = 2`, which beats `c_q(1 − cos x) ≤ c_q x²/2`.  For `y² ≥ 2` each term is at least its value
  at `y² = 2`, and their sum `≥ 1.34` beats `2c_q`.  The deficit bound `c_q ≤ 0.6575` uses
  `γ < H₁₆ − log 16`, `log π ≤ (3 log 2 + ⅛)/2 + π/3 − 1` and `3 log 5 ≥ 7 log 2 − 3/125`.
* Upper bound: for `n ≥ 3`, `y²/(u(u² + y²)) ≤ y²/u³ ≤ y²(1/(2(u − ½)²) − 1/(2(u + ½)²))` with
  `u = a + n`, which telescopes (`re_digamma_vertical_sub_le`).  At conductor `3`, `b ≥ c₃` forces
  `S₃(π/log m) = G − c₃ − b ≤ G − 2c₃` with `G ≤ 1.951` at `y = π/(2 log m) ≤ π/(2 log 2)` and
  `c₃ ≥ 1.05`; `b < c₃` makes `S₃(0) + b < 0`.
-/

open Complex Real

namespace RHTower

noncomputable section

/-! ### The vertical Gauss expansion -/

/-- The `n`-th Gauss increment on a vertical line. -/
theorem re_gaussDigammaSeriesTerm_vertical_sub {a : ℝ} (ha : 0 < a) (y : ℝ) (n : ℕ) :
    (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * I) n).re -
        (gaussDigammaSeriesTerm (a : ℂ) n).re =
      y ^ 2 / ((a + n) * ((a + n) ^ 2 + y ^ 2)) := by
  have h1 := re_gaussDigammaSeriesTerm_vertical a y n
  have h0 := re_gaussDigammaSeriesTerm_vertical a 0 n
  rw [show ((a : ℂ) + ((0 : ℝ) : ℂ) * I) = (a : ℂ) by simp] at h0
  rw [h1, h0]
  have hp : 0 < a + n := by positivity
  have hq : 0 < (a + n) ^ 2 + y ^ 2 := by positivity
  field_simp
  ring

/-- **The vertical Gauss expansion.**
`Re ψ(a + iy) − ψ(a) = Σ_{n≥0} y²/((a + n)((a + n)² + y²))`. -/
theorem hasSum_re_digamma_vertical_sub {a : ℝ} (ha : 0 < a) (y : ℝ) :
    HasSum (fun n : ℕ => y ^ 2 / ((a + n) * ((a + n) ^ 2 + y ^ 2)))
      ((Complex.digamma ((a : ℂ) + (y : ℂ) * I)).re - (Complex.digamma (a : ℂ)).re) := by
  have hreR : ((a : ℂ)).re = a := Complex.ofReal_re a
  have hreC : ((a : ℂ) + (y : ℂ) * I).re = a := by simp [Complex.add_re, Complex.mul_re]
  have hsR := digamma_eq_neg_euler_add_tsum_gauss (s := (a : ℂ)) (by rw [hreR]; exact ha)
  have hsC := digamma_eq_neg_euler_add_tsum_gauss (s := (a : ℂ) + (y : ℂ) * I)
    (by rw [hreC]; exact ha)
  have hsumR : Summable (fun n : ℕ => gaussDigammaSeriesTerm ((a : ℂ)) n) :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  have hsumC : Summable (fun n : ℕ => gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * I) n) :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  have h := (Complex.hasSum_re hsumC.hasSum).sub (Complex.hasSum_re hsumR.hasSum)
  have hval : (Complex.digamma ((a : ℂ) + (y : ℂ) * I)).re - (Complex.digamma (a : ℂ)).re =
      (∑' n, gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * I) n).re -
        (∑' n, gaussDigammaSeriesTerm (a : ℂ) n).re := by
    rw [hsR, hsC]
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    ring
  have hfun : (fun n : ℕ => y ^ 2 / ((a + n) * ((a + n) ^ 2 + y ^ 2))) =
      fun n => (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * I) n).re -
        (gaussDigammaSeriesTerm (a : ℂ) n).re := by
    funext n
    exact (re_gaussDigammaSeriesTerm_vertical_sub ha y n).symm
  rw [hval, hfun]
  exact h

theorem gaussVerticalTerm_nonneg {a : ℝ} (ha : 0 < a) (y : ℝ) (n : ℕ) :
    0 ≤ y ^ 2 / ((a + n) * ((a + n) ^ 2 + y ^ 2)) := by positivity

/-- **Finite lower bound.** -/
theorem sum_range_le_re_digamma_vertical_sub {a : ℝ} (ha : 0 < a) (y : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, y ^ 2 / ((a + n) * ((a + n) ^ 2 + y ^ 2)) ≤
      (Complex.digamma ((a : ℂ) + (y : ℂ) * I)).re - (Complex.digamma (a : ℂ)).re :=
  sum_le_hasSum _ (fun n _ => gaussVerticalTerm_nonneg ha y n) (hasSum_re_digamma_vertical_sub ha y)

/-- The telescoping majorant: `y²/(u(u² + y²)) ≤ y²(1/(2(u − ½)²) − 1/(2(u + ½)²))` for
`u > ½`. -/
theorem gaussVerticalTerm_le_telescope {u : ℝ} (hu : 1 / 2 < u) (y : ℝ) :
    y ^ 2 / (u * (u ^ 2 + y ^ 2)) ≤
      y ^ 2 * (1 / (2 * (u - 1 / 2) ^ 2) - 1 / (2 * (u + 1 / 2) ^ 2)) := by
  have hu0 : 0 < u := by linarith
  have h1 : 0 < u - 1 / 2 := by linarith
  have h2 : 0 < u + 1 / 2 := by linarith
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have heq : 1 / (2 * (u - 1 / 2) ^ 2) - 1 / (2 * (u + 1 / 2) ^ 2) =
      u / ((u - 1 / 2) ^ 2 * (u + 1 / 2) ^ 2) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity)
      (by positivity)]
    ring
  rw [heq]
  calc y ^ 2 / (u * (u ^ 2 + y ^ 2)) ≤ y ^ 2 / (u * u ^ 2) := by
        apply div_le_div_of_nonneg_left hy (by positivity)
        nlinarith [mul_pos hu0 hu0]
    _ ≤ y ^ 2 * (u / ((u - 1 / 2) ^ 2 * (u + 1 / 2) ^ 2)) := by
        rw [div_eq_mul_one_div (y ^ 2)]
        apply mul_le_mul_of_nonneg_left _ hy
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hp : (u - 1 / 2) ^ 2 * (u + 1 / 2) ^ 2 = (u ^ 2 - 1 / 4) ^ 2 := by ring
        rw [hp]
        have h4 : 0 ≤ u ^ 2 - 1 / 4 := by nlinarith
        have h3 : (u ^ 2 - 1 / 4) ^ 2 ≤ (u ^ 2) ^ 2 := by
          apply pow_le_pow_left₀ h4; linarith
        nlinarith

/-- **Upper bound by three terms and a telescoped tail.** For `a > ½`,
`Re ψ(a + iy) − ψ(a) ≤ Σ_{n<3} y²/((a + n)((a + n)² + y²)) + y²/(2(a + 5/2)²)`. -/
theorem re_digamma_vertical_sub_le {a : ℝ} (ha : 1 / 2 < a) (y : ℝ) :
    (Complex.digamma ((a : ℂ) + (y : ℂ) * I)).re - (Complex.digamma (a : ℂ)).re ≤
      ∑ n ∈ Finset.range 3, y ^ 2 / ((a + n) * ((a + n) ^ 2 + y ^ 2)) +
        y ^ 2 / (2 * (a + 5 / 2) ^ 2) := by
  have ha0 : 0 < a := by linarith
  set d : ℕ → ℝ := fun n => y ^ 2 / ((a + n) * ((a + n) ^ 2 + y ^ 2)) with hd
  set φ : ℕ → ℝ := fun n => y ^ 2 / (2 * (a + n - 1 / 2) ^ 2) with hφ
  have hstep : ∀ n : ℕ, d (n + 3) + φ (n + 4) ≤ φ (n + 3) := by
    intro n
    have hu : 1 / 2 < a + ((n + 3 : ℕ) : ℝ) := by
      push_cast
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have h := gaussVerticalTerm_le_telescope hu y
    simp only [hd, hφ]
    have e1 : a + ((n + 3 : ℕ) : ℝ) + 1 / 2 = a + ((n + 4 : ℕ) : ℝ) - 1 / 2 := by push_cast; ring
    have e2 : a + ((n + 3 : ℕ) : ℝ) - 1 / 2 = a + ((n + 3 : ℕ) : ℝ) - 1 / 2 := rfl
    rw [e1, mul_sub, mul_one_div, mul_one_div] at h
    rw [← e2]
    linarith
  have htel : ∀ k : ℕ, ∑ n ∈ Finset.range (k + 3), d n + φ (k + 3) ≤
      ∑ n ∈ Finset.range 3, d n + φ 3 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show k + 1 + 3 = (k + 3) + 1 by ring, Finset.sum_range_succ]
      have := hstep k
      rw [show k + 3 + 1 = k + 4 by ring]
      linarith
  have hφ0 : ∀ n, 0 ≤ φ n := fun n => by simp only [hφ]; positivity
  have hd0 : ∀ n, 0 ≤ d n := fun n => gaussVerticalTerm_nonneg ha0 y n
  have hφ3 : φ 3 = y ^ 2 / (2 * (a + 5 / 2) ^ 2) := by
    simp only [hφ]; push_cast; ring_nf
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.range N, d n ≤ ∑ n ∈ Finset.range 3, d n + φ 3 := by
    intro N
    rcases le_or_gt N 3 with hN | hN
    · have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
        (fun n _ _ => hd0 n)
      linarith [hφ0 3]
    · obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
      linarith [htel k, hφ0 (k + 3)]
  have h := (hasSum_re_digamma_vertical_sub ha0 y).tsum_eq
  rw [← h, ← hφ3]
  exact Real.tsum_le_of_sum_range_le hd0 hbound

/-! ### Constants -/

theorem eulerMascheroniConstant_lt_harmonic_sixteen :
    Real.eulerMascheroniConstant < 2436559 / 720720 - 4 * Real.log 2 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 16
  have h16 : ((harmonic 16 : ℚ) : ℝ) = 2436559 / 720720 := by
    simp [harmonic, Finset.sum_range_succ]
    norm_num
  have hl : Real.log (16 : ℕ) = 4 * Real.log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  simp only [Real.eulerMascheroniSeq', show (16 : ℕ) ≠ 0 by norm_num, if_false, h16, hl] at h
  exact h

theorem log_five_ge : 7 * Real.log 2 - 3 / 125 ≤ 3 * Real.log 5 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 128 / 125 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), show (128 : ℝ) = 2 ^ 7 by norm_num,
    show (125 : ℝ) = 5 ^ 3 by norm_num, Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

theorem one_sub_three_div_pi_le_log_pi_sub_log_three :
    1 - 3 / π ≤ Real.log π - Real.log 3 := by
  rw [← Real.log_div Real.pi_pos.ne' (by norm_num)]
  have := Real.one_sub_inv_le_log_of_pos (show 0 < π / 3 by positivity)
  rwa [inv_div] at this

/-- `c_q ≤ 0.6575` for `q ≥ 5`. -/
theorem oddDeficit_le_of_five_le {q : ℝ} (hq : 5 ≤ q) : oddDeficit q ≤ 6575 / 10000 := by
  have hlogq : Real.log 5 ≤ Real.log q := Real.log_le_log (by norm_num) hq
  have hγ := eulerMascheroniConstant_lt_harmonic_sixteen
  have hl2 := Real.log_two_gt_d9
  have hπ := Real.pi_gt_d4
  rw [oddDeficit_eq]
  linarith [log_pi_le, log_five_ge]

/-- `c₃ ≥ 1.05`. -/
theorem oddDeficit_three_ge : 105 / 100 ≤ oddDeficit 3 := by
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hl2 := Real.log_two_gt_d9
  have hπ := Real.pi_gt_d4
  have hπ' := Real.pi_lt_d4
  have h3π : 3 / π ≤ 3 / 3.1415 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ.le
  rw [oddDeficit_eq]
  linarith [one_sub_three_div_pi_le_log_pi_sub_log_three]

/-! ### Conductor at least `5` -/

theorem gaussTerm_ge_mul {A z : ℝ} (hA : 0 < A) (hz : 0 ≤ z) (hz2 : z ≤ 2) :
    z * (1 / (A * (A ^ 2 + 2))) ≤ z / (A * (A ^ 2 + z)) := by
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left hz (by positivity) (by nlinarith)

theorem gaussTerm_ge_const {A z : ℝ} (hA : 0 < A) (hz2 : 2 ≤ z) :
    2 / (A * (A ^ 2 + 2)) ≤ z / (A * (A ^ 2 + z)) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hA hA, mul_pos (mul_pos hA hA) hA]

/-- **Node `2` for every odd conductor `q ≥ 5`.** -/
theorem oddDirichletSingleNodeSymbol_nonneg_two_of_five_le {q : ℝ} (hq : 5 ≤ q) (τ : ℝ) :
    0 ≤ weilAtomSymbol (oddSingleNodeWeight q 2) 2 (τ / (2 * π)) + Real.log q +
      π / Real.cosh (π * τ) := by
  rw [weilAtomSymbol_oddSingleNodeWeight (le_refl 2) τ]
  set c := oddDeficit q with hc_def
  have hc : c ≤ 6575 / 10000 := oddDeficit_le_of_five_le hq
  have hS0 : (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re - Real.log π + Real.log q = -c := by
    rw [hc_def, oddDeficit]; ring
  have hgrow := sum_range_le_re_digamma_vertical_sub (a := 3 / 4) (by norm_num) (τ / 2) 3
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, add_zero, zero_add] at hgrow
  set z := (τ / 2) ^ 2 with hz_def
  have hz : 0 ≤ z := sq_nonneg _
  set S := z / (3 / 4 * ((3 / 4) ^ 2 + z)) + z / ((3 / 4 + 1) * ((3 / 4 + 1) ^ 2 + z)) +
    z / ((3 / 4 + 2) * ((3 / 4 + 2) ^ 2 + z)) with hS_def
  set x := τ * Real.log 2 with hx
  have hcos1 : Real.cos x ≤ 1 := Real.cos_le_one x
  have hcosm : -1 ≤ Real.cos x := Real.neg_one_le_cos x
  have hS0' : 0 ≤ S := by positivity
  have hgoal : c * (1 - Real.cos x) ≤ S := by
    rcases le_or_gt c 0 with hc0 | hc0
    · nlinarith
    rcases le_or_gt z 2 with hz2 | hz2
    · have t0 := gaussTerm_ge_mul (A := 3 / 4) (by norm_num) hz hz2
      have t1 := gaussTerm_ge_mul (A := 3 / 4 + 1) (by norm_num) hz hz2
      have t2 := gaussTerm_ge_mul (A := 3 / 4 + 2) (by norm_num) hz hz2
      have hK : z * (64 / 123 + 64 / 567 + 64 / 1683) ≤ S := by
        have e0 : (1 : ℝ) / (3 / 4 * ((3 / 4) ^ 2 + 2)) = 64 / 123 := by norm_num
        have e1 : (1 : ℝ) / ((3 / 4 + 1) * ((3 / 4 + 1) ^ 2 + 2)) = 64 / 567 := by norm_num
        have e2 : (1 : ℝ) / ((3 / 4 + 2) * ((3 / 4 + 2) ^ 2 + 2)) = 64 / 1683 := by norm_num
        rw [e0] at t0; rw [e1] at t1; rw [e2] at t2
        rw [hS_def]; linarith
      have hcos2 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
      have hx2 : x ^ 2 = 4 * z * Real.log 2 ^ 2 := by rw [hx, hz_def]; ring
      have hl2 := Real.log_two_lt_d9
      have hl2' := Real.log_two_gt_d9
      have hL2 : Real.log 2 ^ 2 ≤ 0.6931471808 ^ 2 := by
        apply pow_le_pow_left₀ (by linarith) hl2.le
      have h1 : c * (1 - Real.cos x) ≤ c * (2 * z * Real.log 2 ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hc0.le
        nlinarith
      have h2 : c * (2 * z * Real.log 2 ^ 2) ≤ z * (64 / 123 + 64 / 567 + 64 / 1683) := by
        have hzL : 0 ≤ z * Real.log 2 ^ 2 := by positivity
        have : c * (2 * z * Real.log 2 ^ 2) ≤ 6575 / 10000 * (2 * z * 0.6931471808 ^ 2) := by
          have hzz : 2 * z * Real.log 2 ^ 2 ≤ 2 * z * 0.6931471808 ^ 2 := by nlinarith
          have := mul_le_mul hc hzz (by positivity) (by norm_num)
          linarith
        nlinarith
      linarith
    · have t0 := gaussTerm_ge_const (A := 3 / 4) (by norm_num) hz2.le
      have t1 := gaussTerm_ge_const (A := 3 / 4 + 1) (by norm_num) hz2.le
      have t2 := gaussTerm_ge_const (A := 3 / 4 + 2) (by norm_num) hz2.le
      have hK : 2 * (64 / 123 + 64 / 567 + 64 / 1683) ≤ S := by
        have e0 : (2 : ℝ) / (3 / 4 * ((3 / 4) ^ 2 + 2)) = 2 * (64 / 123) := by norm_num
        have e1 : (2 : ℝ) / ((3 / 4 + 1) * ((3 / 4 + 1) ^ 2 + 2)) = 2 * (64 / 567) := by norm_num
        have e2 : (2 : ℝ) / ((3 / 4 + 2) * ((3 / 4 + 2) ^ 2 + 2)) = 2 * (64 / 1683) := by norm_num
        rw [e0] at t0; rw [e1] at t1; rw [e2] at t2
        rw [hS_def]; linarith
      have h1 : c * (1 - Real.cos x) ≤ 2 * c := by nlinarith
      linarith
  have hre : (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re -
      (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re ≥ S := by
    rw [hS_def, hz_def]; linarith
  linarith

/-- **The conductor-`q ≥ 5` single-node Weil forms are nonnegative on every test.** -/
theorem integral_oddDirichletSingleNode_nonneg_of_five_le {q : ℝ} (hq : 5 ≤ q) (f : ℝ → ℂ) :
    0 ≤ ∫ τ : ℝ, ‖Zeta23.paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (oddSingleNodeWeight q 2) 2 (τ / (2 * π)) + Real.log q +
        π / Real.cosh (π * τ)) :=
  MeasureTheory.integral_nonneg fun τ =>
    mul_nonneg (by positivity) (oddDirichletSingleNodeSymbol_nonneg_two_of_five_le hq τ)

/-! ### Conductor `3` -/

/-- **No single node at conductor `3`.**  For every node `m ≥ 2` and every real `b`, the symbol
`S₃(τ) + b cos(τ log m)` is negative at some `τ`. -/
theorem exists_oddConductorThree_singleNode_neg {m : ℕ} (hm : 2 ≤ m) (b : ℝ) :
    ∃ τ : ℝ, (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re - Real.log π +
      Real.log 3 + b * Real.cos (τ * Real.log m) < 0 := by
  set c := oddDeficit 3 with hc_def
  have hc : 105 / 100 ≤ c := oddDeficit_three_ge
  have hS0 : (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re - Real.log π + Real.log 3 = -c := by
    rw [hc_def, oddDeficit]; ring
  rcases lt_or_ge b c with hb | hb
  · refine ⟨0, ?_⟩
    have e : ((3 / 4 : ℝ) : ℂ) + (((0 : ℝ) / 2 : ℝ) : ℂ) * I = ((3 / 4 : ℝ) : ℂ) := by simp
    rw [e, zero_mul, Real.cos_zero, mul_one]
    linarith
  · have hlogm : Real.log 2 ≤ Real.log m :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm)
    have hl2 := Real.log_two_gt_d9
    have hlpos : 0 < Real.log m := by linarith
    refine ⟨π / Real.log m, ?_⟩
    rw [div_mul_cancel₀ _ hlpos.ne', Real.cos_pi]
    set y := π / Real.log m / 2 with hy
    have hy2 : y ^ 2 ≤ 514 / 100 := by
      have hπ' := Real.pi_lt_d4
      have h0 : 0 ≤ y := by rw [hy]; positivity
      have h1 : y ≤ 3.1416 / (2 * 0.6931471803) := by
        rw [hy, div_div]
        apply div_le_div₀ (by norm_num) hπ'.le (by norm_num)
        linarith
      have h2 : (3.1416 / (2 * 0.6931471803) : ℝ) ^ 2 ≤ 514 / 100 := by norm_num
      nlinarith
    have hup := re_digamma_vertical_sub_le (a := 3 / 4) (by norm_num) y
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      Nat.cast_one, Nat.cast_ofNat, add_zero, zero_add] at hup
    have hz : 0 ≤ y ^ 2 := sq_nonneg y
    have mono : ∀ A : ℝ, 0 < A → y ^ 2 / (A * (A ^ 2 + y ^ 2)) ≤
        (514 / 100) / (A * (A ^ 2 + 514 / 100)) := by
      intro A hA
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hA hA, mul_pos (mul_pos hA hA) hA]
    have m0 := mono (3 / 4) (by norm_num)
    have m1 := mono (3 / 4 + 1) (by norm_num)
    have m2 := mono (3 / 4 + 2) (by norm_num)
    have mt : y ^ 2 / (2 * (3 / 4 + 5 / 2) ^ 2) ≤ (514 / 100) / (2 * (3 / 4 + 5 / 2) ^ 2) :=
      div_le_div_of_nonneg_right hy2 (by positivity)
    have hG : (514 / 100 : ℝ) / (3 / 4 * ((3 / 4) ^ 2 + 514 / 100)) +
        (514 / 100) / ((3 / 4 + 1) * ((3 / 4 + 1) ^ 2 + 514 / 100)) +
        (514 / 100) / ((3 / 4 + 2) * ((3 / 4 + 2) ^ 2 + 514 / 100)) +
        (514 / 100) / (2 * (3 / 4 + 5 / 2) ^ 2) ≤ 1951 / 1000 := by norm_num
    linarith

/-- A single weight `lam` at the node `m`. -/
def singleNodeWeight (lam : ℝ) (m : ℕ) (n : ℕ) : ℝ := if n = m then lam else 0

theorem weilAtomSymbol_singleNodeWeight {m : ℕ} (hm : 2 ≤ m) (lam τ : ℝ) :
    weilAtomSymbol (singleNodeWeight lam m) m (τ / (2 * π)) + Real.log 3 +
        π / Real.cosh (π * τ) =
      (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re - Real.log π +
        Real.log 3 + (-(2 * lam / Real.sqrt m)) * Real.cos (τ * Real.log m) := by
  have hsum : ∑ n ∈ Finset.Icc 2 m, singleNodeWeight lam m n * (1 / Real.sqrt n) *
      (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))) =
      2 * lam / Real.sqrt m * Real.cos (τ * Real.log m) := by
    rw [Finset.sum_eq_single m]
    · simp only [singleNodeWeight, if_true]
      rw [show 2 * π * Real.log m * (τ / (2 * π)) = τ * Real.log m by field_simp]
      ring
    · intro n _ hn
      simp [singleNodeWeight, hn]
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩) h
  rw [weilAtomSymbol, hsum, ← archimedeanWeilSymbol_add_sech τ]
  ring

/-- **The conductor-`3` odd Weil cone contains no single-node weight.** -/
theorem not_forall_oddConductorThree_singleNodeSymbol_nonneg {m : ℕ} (hm : 2 ≤ m) (lam : ℝ) :
    ¬ ∀ τ : ℝ, 0 ≤ weilAtomSymbol (singleNodeWeight lam m) m (τ / (2 * π)) + Real.log 3 +
      π / Real.cosh (π * τ) := by
  intro h
  obtain ⟨τ, hτ⟩ := exists_oddConductorThree_singleNode_neg hm (-(2 * lam / Real.sqrt m))
  have := h τ
  rw [weilAtomSymbol_singleNodeWeight hm lam τ] at this
  linarith

end

end RHTower
