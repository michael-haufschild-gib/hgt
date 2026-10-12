import GaloisForLFunctions.HTGeometry.SincBackgroundDetectionWindow

/-!
# Height window of an off-line pair against a dense critical background

Let `L > 0`, `δ ≥ 0`, `u ∈ ℝ`, and let

  `f(z) = ((z − u)² + δ²) · sin(Lz/2)/(Lz/2)`:

real zeros at `2πk/L` (`k ≠ 0`, density `L/2π`) and the non-real pair `u ± iδ`.  Its slice at the
height `0`, which lies at distance `|u|` from the ordinate of the pair, is (`sincOffsetPairSlice_eq`)

  `f(ix) f(−ix) = ((u² + δ² − x²)² + 4u²x²) (sinh(Lx/2)/(Lx/2))² = Σ_m c_m x^{2m}`

(`hasSum_sincOffsetSliceCoeff`), with `c_m = (u² + δ²)² b_m − 2(δ² − u²) b_{m−1} + b_{m−2}` and
`b_m = 2L^{2m}/(2m+2)!`.  Write `D = (δL)²`, `U = (uL)²`, `P = (2m+1)(2m+2)`.

**Sign law** (`sincOffsetSliceCoeff_neg_iff`).  For `m ≥ 2`,

  `c_m < 0  ⟺  (D + U − P)² + 4UP < P(8m + 2)`.

At `u = 0` this is the ordinate law `sincSliceCoeff_neg_iff`.  The offset adds the positive term `4UP`,
which competes with the window width `P(8m + 2)`.

**Height window** (`sq_mul_lt_of_sincOffsetSliceCoeff_neg`, `exists_sincOffsetSliceCoeff_neg`).

* If some `c_m` is negative, then `(uL)² < 2δL + 6`.
* If `δL ≥ 8` and `(uL)² ≤ δL − 9`, then some `c_m` is negative.

So the slice criterion sees the pair exactly at heights `|u| ≍ √(δ/L)` from its ordinate, and the
failure set is a single interval centred at the ordinate: every coefficient is increasing in
`(uL)²` (`sincOffsetSliceCoeff_neg_of_sq_le`, `exists_sincOffsetSliceCoeff_neg_of_abs_le`).  The
visibility cone of the pair (the heights where it is exposed, `|u| < δ`) is wider by the factor
`√(δL)` once `δL` is large: a pair far from the critical line, against a dense background, makes
the slice fail only on a window of width comparable to the geometric mean of its displacement
`δ` and the mean spacing `2π/L`.  For `δL = O(1)` the window and the cone have the same size.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The slice coefficients, in `y = x²`, at height `0` of `((z − u)² + δ²) sin(Lz/2)/(Lz/2)`. -/
def sincOffsetSliceCoeff (L δ u : ℝ) : ℕ → ℝ
  | 0 => (u ^ 2 + δ ^ 2) ^ 2 * sincSqCoeff L 0
  | 1 => (u ^ 2 + δ ^ 2) ^ 2 * sincSqCoeff L 1 - 2 * (δ ^ 2 - u ^ 2) * sincSqCoeff L 0
  | m + 2 => (u ^ 2 + δ ^ 2) ^ 2 * sincSqCoeff L (m + 2) -
      2 * (δ ^ 2 - u ^ 2) * sincSqCoeff L (m + 1) + sincSqCoeff L m

theorem hasSum_sincOffsetSliceCoeff (L δ u x : ℝ) (hx : L * x ≠ 0) :
    HasSum (fun m => sincOffsetSliceCoeff L δ u m * (x ^ 2) ^ m)
      (((u ^ 2 + δ ^ 2 - x ^ 2) ^ 2 + 4 * u ^ 2 * x ^ 2) *
        (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2) := by
  have h0 := hasSum_sincSqCoeff L x hx
  have h1 := (hasSum_nat_add_iff' 1).mpr h0
  have h2 := (hasSum_nat_add_iff' 2).mpr h0
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h1 h2
  rw [← hasSum_nat_add_iff' 2]
  have hsum := ((h2.mul_left ((u ^ 2 + δ ^ 2) ^ 2)).add
    (h1.mul_left (-2 * (δ ^ 2 - u ^ 2) * x ^ 2))).add (h0.mul_left ((x ^ 2) ^ 2))
  have efun : (fun n => sincOffsetSliceCoeff L δ u (n + 2) * (x ^ 2) ^ (n + 2)) =
      fun n => (u ^ 2 + δ ^ 2) ^ 2 * (sincSqCoeff L (n + 2) * (x ^ 2) ^ (n + 2)) +
        -2 * (δ ^ 2 - u ^ 2) * x ^ 2 * (sincSqCoeff L (n + 1) * (x ^ 2) ^ (n + 1)) +
          (x ^ 2) ^ 2 * (sincSqCoeff L n * (x ^ 2) ^ n) := by
    funext n
    simp only [sincOffsetSliceCoeff]
    ring
  have hval : ((u ^ 2 + δ ^ 2 - x ^ 2) ^ 2 + 4 * u ^ 2 * x ^ 2) *
        (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 -
      ∑ i ∈ Finset.range 2, sincOffsetSliceCoeff L δ u i * (x ^ 2) ^ i =
      (u ^ 2 + δ ^ 2) ^ 2 * ((Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 -
          (sincSqCoeff L 0 * (x ^ 2) ^ 0 + sincSqCoeff L 1 * (x ^ 2) ^ 1)) +
        -2 * (δ ^ 2 - u ^ 2) * x ^ 2 * ((Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 -
          sincSqCoeff L 0 * (x ^ 2) ^ 0) +
        (x ^ 2) ^ 2 * (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      sincOffsetSliceCoeff]
    ring
  rw [efun, hval]
  exact hsum

/-- **Slice identity.**  For `f(z) = ((z − u)² + δ²) sin(Lz/2)/(Lz/2)` and `Lx ≠ 0`,
`f(ix) f(−ix) = ((u² + δ² − x²)² + 4u²x²) (sinh(Lx/2)/(Lx/2))²`. -/
theorem sincOffsetPairSlice_eq (L δ u x : ℝ) (hx : L * x ≠ 0) :
    (((((x : ℂ) * Complex.I) - u) ^ 2 + (δ : ℂ) ^ 2) *
        (Complex.sin ((L : ℂ) * ((x : ℂ) * Complex.I) / 2) /
          ((L : ℂ) * ((x : ℂ) * Complex.I) / 2))) *
      (((-((x : ℂ) * Complex.I) - u) ^ 2 + (δ : ℂ) ^ 2) *
        (Complex.sin ((L : ℂ) * (-((x : ℂ) * Complex.I)) / 2) /
          ((L : ℂ) * (-((x : ℂ) * Complex.I)) / 2))) =
      ((((u ^ 2 + δ ^ 2 - x ^ 2) ^ 2 + 4 * u ^ 2 * x ^ 2) *
        (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 : ℝ) : ℂ) := by
  have hpair : ((((x : ℂ) * Complex.I) - u) ^ 2 + (δ : ℂ) ^ 2) *
      (((-((x : ℂ) * Complex.I)) - u) ^ 2 + (δ : ℂ) ^ 2) =
      (((u ^ 2 + δ ^ 2 - x ^ 2) ^ 2 + 4 * u ^ 2 * x ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (2 * ((u : ℂ) ^ 2 + (δ : ℂ) ^ 2 - (x : ℂ) ^ 2) * (x : ℂ) ^ 2 +
      (x : ℂ) ^ 4 * (Complex.I ^ 2 + 1) - 4 * (u : ℂ) ^ 2 * (x : ℂ) ^ 2) * Complex.I_sq
  have hsinc := sincPairSlice_eq L 0 x hx
  have hq : ∀ v : ℂ, (v ^ 2 + ((0 : ℝ) : ℂ) ^ 2) = v ^ 2 := fun v => by push_cast; ring
  rw [hq, hq] at hsinc
  have hx2 : (((x : ℂ) * Complex.I) ^ 2) * ((-((x : ℂ) * Complex.I)) ^ 2) = (x : ℂ) ^ 4 := by
    linear_combination ((x : ℂ) ^ 4 * Complex.I ^ 2 - (x : ℂ) ^ 4) * Complex.I_sq
  set s₁ := Complex.sin ((L : ℂ) * ((x : ℂ) * Complex.I) / 2) /
    ((L : ℂ) * ((x : ℂ) * Complex.I) / 2)
  set s₂ := Complex.sin ((L : ℂ) * (-((x : ℂ) * Complex.I)) / 2) /
    ((L : ℂ) * (-((x : ℂ) * Complex.I)) / 2)
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hx
  have hs : s₁ * s₂ = (((Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 : ℝ) : ℂ) := by
    have h4 : (x : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 hx0
    have e : ((x : ℂ) * Complex.I) ^ 2 * s₁ * ((-((x : ℂ) * Complex.I)) ^ 2 * s₂) =
        (x : ℂ) ^ 4 * (s₁ * s₂) := by rw [← hx2]; ring
    rw [e] at hsinc
    have : (((0 : ℝ) ^ 2 - x ^ 2) ^ 2 * (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 : ℝ) =
        x ^ 4 * (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 := by ring
    rw [this] at hsinc
    push_cast at hsinc ⊢
    exact mul_left_cancel₀ h4 hsinc
  calc _ = ((((x : ℂ) * Complex.I) - u) ^ 2 + (δ : ℂ) ^ 2) *
        (((-((x : ℂ) * Complex.I)) - u) ^ 2 + (δ : ℂ) ^ 2) * (s₁ * s₂) := by ring
    _ = _ := by rw [hpair, hs]; push_cast; ring

/-- The closed form `c_{m+2} = 2L^{2m}/(2m+6)! · ((D + U − P)² + 4UP − P(8m + 18))`, with
`D = (δL)²`, `U = (uL)²`, `P = (2m+5)(2m+6)`. -/
theorem sincOffsetSliceCoeff_add_two_eq (L δ u : ℝ) (m : ℕ) :
    sincOffsetSliceCoeff L δ u (m + 2) = 2 * L ^ (2 * m) / ((2 * m + 6).factorial : ℝ) *
      (((δ * L) ^ 2 + (u * L) ^ 2 - (2 * (m : ℝ) + 5) * (2 * m + 6)) ^ 2 +
        4 * (u * L) ^ 2 * ((2 * (m : ℝ) + 5) * (2 * m + 6)) -
        (2 * (m : ℝ) + 5) * (2 * m + 6) * (8 * m + 18)) := by
  simp only [sincOffsetSliceCoeff, sincSqCoeff]
  rw [show 2 * (m + 2) + 2 = (2 * m + 5) + 1 by ring, show 2 * (m + 1) + 2 = (2 * m + 3) + 1 by ring,
    show 2 * m + 6 = (2 * m + 5) + 1 by ring, show 2 * (m + 2) = 2 * m + 4 by ring,
    show 2 * (m + 1) = 2 * m + 2 by ring]
  rw [Nat.factorial_succ (2 * m + 5), show 2 * m + 5 = (2 * m + 4) + 1 by ring,
    Nat.factorial_succ (2 * m + 4), show 2 * m + 4 = (2 * m + 3) + 1 by ring,
    Nat.factorial_succ (2 * m + 3), show 2 * m + 3 = (2 * m + 2) + 1 by ring,
    Nat.factorial_succ (2 * m + 2)]
  have hf : ((2 * m + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  field_simp
  ring

/-- **Sign law.**  For `m ≥ 2` and `P = (2m+1)(2m+2)`:
`c_m < 0 ⟺ ((δL)² + (uL)² − P)² + 4(uL)²P < P(8m + 2)`. -/
theorem sincOffsetSliceCoeff_neg_iff (L δ u : ℝ) (hL : L ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    sincOffsetSliceCoeff L δ u m < 0 ↔
      ((δ * L) ^ 2 + (u * L) ^ 2 - (2 * (m : ℝ) + 1) * (2 * m + 2)) ^ 2 +
          4 * (u * L) ^ 2 * ((2 * (m : ℝ) + 1) * (2 * m + 2)) <
        (2 * (m : ℝ) + 1) * (2 * m + 2) * (8 * m + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [sincOffsetSliceCoeff_add_two_eq]
  have hpos : 0 < 2 * L ^ (2 * k) / ((2 * k + 6).factorial : ℝ) := by
    have : 0 < L ^ (2 * k) := by
      rw [pow_mul]
      exact pow_pos (by positivity) k
    positivity
  have e5 : (2 * ((k + 2 : ℕ) : ℝ) + 1) = 2 * (k : ℝ) + 5 := by push_cast; ring
  have e6 : (2 * ((k + 2 : ℕ) : ℝ) + 2) = 2 * (k : ℝ) + 6 := by push_cast; ring
  have e8 : (8 * ((k + 2 : ℕ) : ℝ) + 2) = 8 * (k : ℝ) + 18 := by push_cast; ring
  rw [e5, e6, e8]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := mul_nonneg hpos.le (sub_nonneg.mpr hc)
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hpos (sub_neg.mpr h)

theorem sincOffsetSliceCoeff_zero_nonneg (L δ u : ℝ) : 0 ≤ sincOffsetSliceCoeff L δ u 0 := by
  simp only [sincOffsetSliceCoeff, sincSqCoeff, mul_zero, pow_zero]
  positivity

/-- The order-one coefficient: `c_1 < 0 ⟺ ((δL)² + (uL)²)² < 24((δL)² − (uL)²)`. -/
theorem sincOffsetSliceCoeff_one_neg_iff (L δ u : ℝ) (hL : L ≠ 0) :
    sincOffsetSliceCoeff L δ u 1 < 0 ↔
      ((δ * L) ^ 2 + (u * L) ^ 2) ^ 2 < 24 * ((δ * L) ^ 2 - (u * L) ^ 2) := by
  have hL2 : 0 < L ^ 2 := by positivity
  have e : sincOffsetSliceCoeff L δ u 1 =
      (((δ * L) ^ 2 + (u * L) ^ 2) ^ 2 - 24 * ((δ * L) ^ 2 - (u * L) ^ 2)) / (12 * L ^ 2) := by
    simp only [sincOffsetSliceCoeff, sincSqCoeff]
    norm_num [Nat.factorial]
    field_simp
    ring
  rw [e, div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_lt.mpr (by positivity))
    · linarith
  · intro h
    right
    exact ⟨by linarith, mul_pos (by norm_num) hL2⟩

/-- **The window is at most `√(2δL + 6)/L` wide.**  If some slice coefficient is negative, then
`(uL)² < 2δL + 6`. -/
theorem sq_mul_lt_of_sincOffsetSliceCoeff_neg (L δ u : ℝ) (hL : 0 < L) (hδ : 0 ≤ δ) {m : ℕ}
    (hneg : sincOffsetSliceCoeff L δ u m < 0) : (u * L) ^ 2 < 2 * (δ * L) + 6 := by
  set D := δ * L with hD
  set U := (u * L) ^ 2 with hU
  have hD0 : 0 ≤ D := mul_nonneg hδ hL.le
  have hU0 : 0 ≤ U := sq_nonneg _
  rcases m with _ | _ | m
  · exact absurd hneg (not_lt.mpr (sincOffsetSliceCoeff_zero_nonneg L δ u))
  · rw [sincOffsetSliceCoeff_one_neg_iff L δ u hL.ne'] at hneg
    nlinarith
  · rw [sincOffsetSliceCoeff_neg_iff L δ u hL.ne' (by omega)] at hneg
    set k : ℝ := ((m + 2 : ℕ) : ℝ) with hk
    have hk2 : (2 : ℝ) ≤ k := by rw [hk]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    set P := (2 * k + 1) * (2 * k + 2) with hP
    have hP0 : 0 < P := by rw [hP]; nlinarith
    have hUk : U < 2 * k + 1 / 2 := by
      by_contra hc
      push Not at hc
      nlinarith [sq_nonneg (D ^ 2 + U - P)]
    by_contra hcon
    push Not at hcon
    -- then `D < k − 7/4`, so `P − D² − U` is large
    have hDk : D < k - 7 / 4 := by linarith
    have hD2 : D ^ 2 < (k - 7 / 4) ^ 2 := by nlinarith
    have hX : 3 * k ^ 2 + 15 / 2 * k - 25 / 16 < P - D ^ 2 - U := by
      rw [hP]; nlinarith
    have hX0 : 0 < 3 * k ^ 2 + 15 / 2 * k - 25 / 16 := by nlinarith
    have hXsq : (3 * k ^ 2 + 15 / 2 * k - 25 / 16) ^ 2 < (D ^ 2 + U - P) ^ 2 := by
      nlinarith
    have hpoly : P * (8 * k + 2) ≤ (3 * k ^ 2 + 15 / 2 * k - 25 / 16) ^ 2 := by
      rw [hP]
      nlinarith [mul_nonneg (sub_nonneg.mpr hk2) (sub_nonneg.mpr hk2),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hk2) (sub_nonneg.mpr hk2)) (sub_nonneg.mpr hk2),
        mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hk2) (sub_nonneg.mpr hk2))
          (sub_nonneg.mpr hk2)) (sub_nonneg.mpr hk2)]
    nlinarith [mul_nonneg hU0 hP0.le]

/-- **The window is at least `√(δL − 9)/L` wide.**  If `δL ≥ 8` and `(uL)² ≤ δL − 9`, some slice
coefficient is negative. -/
theorem exists_sincOffsetSliceCoeff_neg (L δ u : ℝ) (hL : 0 < L) (hδL : 8 ≤ δ * L)
    (hu : (u * L) ^ 2 ≤ δ * L - 9) : ∃ m, sincOffsetSliceCoeff L δ u m < 0 := by
  set D := δ * L with hD
  set U := (u * L) ^ 2 with hU
  have hU0 : 0 ≤ U := sq_nonneg _
  -- the bracket `P_m ≤ D² + U < P_{m+1}`
  have hex : ∃ n : ℕ, D ^ 2 + U < (2 * ((n + 1 : ℕ) : ℝ) + 1) * (2 * ((n + 1 : ℕ) : ℝ) + 2) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (D ^ 2 + U)
    refine ⟨n, lt_of_lt_of_le hn ?_⟩
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  classical
  set m := Nat.find hex with hm
  have hmspec := Nat.find_spec hex
  rw [← hm] at hmspec
  have hD64 : 64 ≤ D ^ 2 := by nlinarith
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    have hle : ((m + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : m + 1 ≤ 3)
    have h0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hlo : (2 * (m : ℝ) + 1) * (2 * m + 2) ≤ D ^ 2 + U := by
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    push Not at hmin
    rw [hj]
    push_cast at hmin ⊢
    linarith
  refine ⟨m, ?_⟩
  rw [sincOffsetSliceCoeff_neg_iff L δ u hL.ne' (by omega)]
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hhi : D ^ 2 + U < (2 * (m : ℝ) + 3) * (2 * m + 4) := by
    have := hmspec
    push_cast at this
    linarith
  have hDm : D < 2 * (m : ℝ) + 4 := by nlinarith
  have hUm : U ≤ 2 * (m : ℝ) - 5 := by linarith
  set P := (2 * (m : ℝ) + 1) * (2 * m + 2) with hP
  have h0 : 0 ≤ D ^ 2 + U - P := by linarith
  have h1 : D ^ 2 + U - P < 8 * m + 10 := by rw [hP]; nlinarith
  have h2 : (8 * (m : ℝ) + 10) ^ 2 ≤ 22 * P := by
    rw [hP]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm') (sub_nonneg.mpr hm')]
  have hP0 : 0 < P := by rw [hP]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hUm (by linarith : (0 : ℝ) ≤ 4 * P)]

/-- **Each order fails on a centred interval.**  If `c_m < 0` at the offset `u`, then `c_m < 0` at
every offset `u'` with `u'² ≤ u²`: every coefficient is increasing in `U = (uL)²`. -/
theorem sincOffsetSliceCoeff_neg_of_sq_le (L δ : ℝ) (hL : L ≠ 0) {u u' : ℝ} (hu : u' ^ 2 ≤ u ^ 2)
    {m : ℕ} (h : sincOffsetSliceCoeff L δ u m < 0) : sincOffsetSliceCoeff L δ u' m < 0 := by
  have hUU : (u' * L) ^ 2 ≤ (u * L) ^ 2 := by
    rw [mul_pow, mul_pow]; exact mul_le_mul_of_nonneg_right hu (sq_nonneg L)
  have hU' : 0 ≤ (u' * L) ^ 2 := sq_nonneg _
  have hD : 0 ≤ (δ * L) ^ 2 := sq_nonneg _
  rcases m with _ | _ | m
  · exact absurd h (not_lt.mpr (sincOffsetSliceCoeff_zero_nonneg L δ u))
  · rw [sincOffsetSliceCoeff_one_neg_iff L δ u hL] at h
    rw [sincOffsetSliceCoeff_one_neg_iff L δ u' hL]
    nlinarith
  · rw [sincOffsetSliceCoeff_neg_iff L δ u hL (by omega)] at h
    rw [sincOffsetSliceCoeff_neg_iff L δ u' hL (by omega)]
    have hP : 0 < (2 * ((m + 2 : ℕ) : ℝ) + 1) * (2 * ((m + 2 : ℕ) : ℝ) + 2) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hUU)
      (by positivity : (0 : ℝ) ≤ 2 * (δ * L) ^ 2 + (u * L) ^ 2 + (u' * L) ^ 2 +
        2 * ((2 * ((m + 2 : ℕ) : ℝ) + 1) * (2 * ((m + 2 : ℕ) : ℝ) + 2)))]

/-- **The failure set is one interval around the ordinate.**  If some slice coefficient is negative
at the offset `u`, then some slice coefficient is negative at every offset `u'` with `|u'| ≤ |u|`.
So the set of heights where the slice criterion fails is a single interval centred at the ordinate
of the pair, of half-width between `√(δL − 9)/L` and `√(2δL + 6)/L`. -/
theorem exists_sincOffsetSliceCoeff_neg_of_abs_le (L δ : ℝ) (hL : L ≠ 0) {u u' : ℝ}
    (hu : |u'| ≤ |u|) (h : ∃ m, sincOffsetSliceCoeff L δ u m < 0) :
    ∃ m, sincOffsetSliceCoeff L δ u' m < 0 := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, sincOffsetSliceCoeff_neg_of_sq_le L δ hL (sq_le_sq.mpr hu) hm⟩

end

end GaloisForLFunctions.HTGeometry
