import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnANarrowWindowThePotentialIsPositiveAndThereAreNoBoundStates
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFirstBlockMatricesOfRatioFourAndSevenHaveAMargin

/-!
# A packet and its dilate by two are bound on the window of ratio three

The window `(2r, 6r]` has the lower end `A = (2r, 3r]`, the middle `(3r, 4r]` and the upper end
`C = (4r, 6r]`; the floor map of `2` sends the blocks `2a`, `2a + 1` of `C` to the block `a` of
`A`. For step packets `σ, τ` on the blocks of `A` let `z = (σ, 0, U₂τ)`: `σ` on `A`, zero on the
middle, and on `C` the refinement `U₂τ`, with the value `τ_a/√2` on the two children of `a`.
`N` is the neutral part of the block matrix and `N_A` its restriction to `A`.

* **The two ends** (`sum_neutralBlock_twoEnds`).
  `N(z) = N_A(σ) + N_A(τ) − √2 (log 2 · Σ σ_j τ_j + Σ σ_j τ_l K(j, l))`, where `K(j, l)` is the
  sum of the jets between the block `2r + j` and the two children of `2r + l`. The upper end
  carries `N_A(τ)` by the invariance of the neutral part under refinement; a block of `A` and a
  block of `C` are coupled by their jet and by the contact `(log 2)/2` of the floor map of `2`.
* **The odd sector** (`sum_neutralBlock_twoEnds_ge`). For `τ = −σ`:
  `N(z) ≥ (1/30) Σ σ_j²`, at every block size `r ≥ 1` and for every `Q ≥ 2`.
* **A packet and its dilate are bound.** For `x = (σ, 0, 0)` and `y = (0, 0, U₂σ)`:
  `N(y, y) = N(x, x)` and `N(x, y) ≤ N(x, x) − (1/60) Σ σ_j²`
  (`bilin_neutralWindow_lowerEnd_upperEnd_le`), so `N(x, x) N(y, y) ≤ N(x, y)²` when
  `N(x, x) < 0`: in the count of the bound states of a window by two wells that stay apart, a
  packet on `A` and its dilate on `C` are never such a pair (`not_unbound_lowerEnd_upperEnd`).

Proof of the odd sector. With the block matrix `W_A` of `A`, the degrees `d` and the kernel
`k(j, l) = √2 (d_j + d_l) − K(j, l)`,

  `N(z) = 2 W_A(σ) + √2 log 2 · Σ σ_j² − √2 Σ σ_j σ_l k(j, l)`:

the charges of `N_A` cancel against the degrees in `k`. `W_A ≥ (1/5000) Σ σ_j²` since `A` has
ratio `3/2`. The kernel is nonnegative (`endKernel_nonneg`): the jets are at most
`2/(γ + α) + 2/(γ − α)` with `α = 2a_j + 1`, `γ = 4a_l`, the degrees at least
`2/α + 4/(γ + 2)`, and the difference is a cubic in `α` that is nonnegative for
`0 < α ≤ (3γ − 4)/4`. By the Schur test `Σ σ_j σ_l k(j, l) ≤ κ Σ σ_j²` as soon as
`Σ_l (k(j, l) + k(l, j)) ≤ 2κ` for every `j`. The row and column sums of `K` are six runs of
consecutive jets; they telescope to steps of `n log n`, which the midpoint enclosure turns into
logarithms of ratios, bounded below by `log(u/v) ≥ 2(u − v)/(u + v)`, by
`log(u/v) ≤ (u² − v²)/(2uv)` and by tangents of `1/y`. This gives `κ = log 2 − 1/40`
(`sum_endKernel_add_le`) and `N(z) ≥ (1/2500 + √2/40) Σ σ_j²`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Logarithms of ratios and rational functions -/

/-- `2(u − v)/(u + v) ≤ log u − log v` for `0 < v ≤ u`. -/
theorem two_mul_sub_div_add_le_log_sub {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    2 * (u - v) / (u + v) ≤ Real.log u - Real.log v := by
  rcases hvu.eq_or_lt with rfl | hlt
  · simp
  · have hu : 0 < u := hv.trans hlt
    have hx : 0 < (u - v) / v := div_pos (sub_pos.mpr hlt) hv
    have h := (Real.lt_log_one_add_of_pos hx).le
    have e1 : 1 + (u - v) / v = u / v := by
      rw [one_add_div hv.ne']
      congr 1
      ring
    have e2 : 2 * ((u - v) / v) / ((u - v) / v + 2) = 2 * (u - v) / (u + v) := by
      field_simp
      ring
    rw [e1, e2, Real.log_div hu.ne' hv.ne'] at h
    exact h

/-- `log u − log v ≤ (u² − v²)/(2uv)` for `0 < v ≤ u`: `t ≤ sinh t` at `t = log(u/v)`. -/
theorem log_sub_log_le_div {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    Real.log u - Real.log v ≤ (u ^ 2 - v ^ 2) / (2 * u * v) := by
  have hu : 0 < u := hv.trans_le hvu
  have h0 : 0 ≤ Real.log (u / v) := Real.log_nonneg ((one_le_div hv).mpr hvu)
  have h := Real.self_le_sinh_iff.mpr h0
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log (div_pos hu hv), Real.log_div hu.ne' hv.ne'] at h
  refine h.trans (le_of_eq ?_)
  field_simp

/-- The tangent of `1/y` at `y₀` lies below it. -/
theorem tangent_le_one_div {y y₀ : ℝ} (hy : 0 < y) (hy₀ : 0 < y₀) :
    (2 * y₀ - y) / y₀ ^ 2 ≤ 1 / y := by
  rw [div_le_div_iff₀ (by positivity) hy]
  nlinarith [sq_nonneg (y - y₀)]

/-- On `[p, q]` the chord of `1/y` lies above it. -/
theorem one_div_le_chord {y p q : ℝ} (hp : 0 < p) (hpy : p ≤ y) (hyq : y ≤ q) :
    1 / y ≤ (p + q - y) / (p * q) := by
  have hy : 0 < y := hp.trans_le hpy
  have hq : 0 < q := hy.trans_le hyq
  rw [div_le_div_iff₀ hy (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpy) (sub_nonneg.mpr hyq)]

/-- The cubic `g(α) = s(γ + 2 + 2α)(γ² − α²) − 2γα(γ + 2)` is nonnegative for
`0 < α ≤ α₁ = (3γ − 4)/4` and `7/5 ≤ s ≤ 3/2`: `g(0) > 0`, `g(α₁) ≥ 0`, and `g` lies above its
chord on `[0, α₁]`. -/
theorem endCoupling_cubic {α γ s : ℝ} (hα : 0 < α) (hαγ : 4 * α ≤ 3 * γ - 4)
    (hs : 7 / 5 ≤ s) (hs' : s ≤ 3 / 2) :
    2 * γ * α * (γ + 2) ≤ s * (γ + 2 + 2 * α) * (γ ^ 2 - α ^ 2) := by
  have hγ : 0 < γ := by linarith
  have hu : 0 ≤ (3 * γ - 4) / 4 - α := by linarith
  have hα₁ : 0 < (3 * γ - 4) / 4 := by linarith
  have g0 : 0 ≤ s * γ ^ 2 * (γ + 2) := by
    have hs0 : 0 ≤ s := by linarith
    positivity
  have g1 : 0 ≤ γ / 32 * ((35 * s - 48) * γ ^ 2 + (120 * s - 32) * γ + (128 - 80 * s)) := by
    have h1 : 0 ≤ (35 * s - 48) * γ ^ 2 := mul_nonneg (by linarith) (sq_nonneg γ)
    have h2 : 0 ≤ (120 * s - 32) * γ := mul_nonneg (by linarith) hγ.le
    exact mul_nonneg (by positivity) (by linarith)
  have g2 : 0 ≤ (3 * γ - 4) / 4 * α * ((3 * γ - 4) / 4 - α) *
      (s * (γ + 2 + 2 * (α + (3 * γ - 4) / 4))) := by
    have hs0 : 0 ≤ s := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hα₁.le hα.le) hu)
      (mul_nonneg hs0 (by linarith))
  have key : (3 * γ - 4) / 4 *
      (s * (γ + 2 + 2 * α) * (γ ^ 2 - α ^ 2) - 2 * γ * α * (γ + 2)) =
      ((3 * γ - 4) / 4 - α) * (s * γ ^ 2 * (γ + 2)) +
        α * (γ / 32 * ((35 * s - 48) * γ ^ 2 + (120 * s - 32) * γ + (128 - 80 * s))) +
        (3 * γ - 4) / 4 * α * ((3 * γ - 4) / 4 - α) *
          (s * (γ + 2 + 2 * (α + (3 * γ - 4) / 4))) := by
    ring
  have hpos : 0 ≤ (3 * γ - 4) / 4 *
      (s * (γ + 2 + 2 * α) * (γ ^ 2 - α ^ 2) - 2 * γ * α * (γ + 2)) := by
    rw [key]
    exact add_nonneg (add_nonneg (mul_nonneg hu g0) (mul_nonneg hα.le g1)) g2
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hpos hα₁)

/-- `2/(γ + α) + 2/(γ − α) ≤ s (2/α + 4/(γ + 2))` for `0 < α ≤ (3γ − 4)/4`, `7/5 ≤ s ≤ 3/2`. -/
theorem end_kernel_real {α γ s : ℝ} (hα : 0 < α) (hαγ : 4 * α ≤ 3 * γ - 4)
    (hs : 7 / 5 ≤ s) (hs' : s ≤ 3 / 2) :
    2 / (γ + α) + 2 / (γ - α) ≤ s * (2 / α + 4 / (γ + 2)) := by
  have hγα : 0 < γ - α := by linarith
  have hγ : 0 < γ := by linarith
  have h := endCoupling_cubic hα hαγ hs hs'
  have e : s * (2 / α + 4 / (γ + 2)) - (2 / (γ + α) + 2 / (γ - α)) =
      2 * (s * (γ + 2 + 2 * α) * (γ ^ 2 - α ^ 2) - 2 * γ * α * (γ + 2)) /
        (α * (γ + 2) * (γ + α) * (γ - α)) := by
    have h1 : γ - α ≠ 0 := hγα.ne'
    field_simp
    ring
  rw [← sub_nonneg, e]
  exact div_nonneg (by linarith)
    (mul_pos (mul_pos (mul_pos hα (by linarith)) (by linarith)) hγα).le

/-- `log((2ρ + w/2)/(ρ + w/2)) ≥ log 2 − 3/4 + 2ρ/(4ρ + w) + (ρ/2)/(2ρ + w)`: `log 2` is split
off and the remaining logarithm of a ratio is bounded from above. -/
theorem log_two_end_ge {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 < w) :
    Real.log 2 - 3 / 4 + 2 * (ρ / (4 * ρ + w)) + 1 / 2 * (ρ / (2 * ρ + w)) ≤
      Real.log (2 * ρ + w / 2) - Real.log (ρ + w / 2) := by
  have h := log_sub_log_le_div (u := 2 * ρ + w) (v := 2 * ρ + w / 2) (by positivity)
    (by linarith)
  have e1 : Real.log (ρ + w / 2) = Real.log (2 * ρ + w) - Real.log 2 := by
    rw [← Real.log_div (by positivity) two_ne_zero]
    congr 1
    ring
  have e2 : ((2 * ρ + w) ^ 2 - (2 * ρ + w / 2) ^ 2) / (2 * (2 * ρ + w) * (2 * ρ + w / 2)) =
      3 / 4 - 2 * (ρ / (4 * ρ + w)) - 1 / 2 * (ρ / (2 * ρ + w)) := by
    field_simp
    ring
  rw [e2] at h
  rw [e1]
  linarith

/-- `7/5 ≤ √2 ≤ 1.41422`. -/
theorem sqrt_two_mem : (7 / 5 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.41422 := by
  have h0 := Real.sqrt_nonneg 2
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  constructor <;> nlinarith

/-- The trapezoid value of the degree of a block `a ∈ [2ρ, 3ρ − 1]`, times `ρ`, is at most
`(10 − (2a + 1)/ρ)/12`: the chord of `1/y` on `[2ρ, 3ρ]`. -/
theorem degree_chord {ρ a : ℝ} (hρ : 0 < ρ) (ha : 2 * ρ ≤ a) (ha' : a + 1 ≤ 3 * ρ) :
    ρ * ((1 / a + 1 / (a + 1)) / 2) ≤ (10 - (2 * a + 1) / ρ) / 12 := by
  have h1 := one_div_le_chord (y := a) (p := 2 * ρ) (q := 3 * ρ) (by positivity) ha (by linarith)
  have h2 := one_div_le_chord (y := a + 1) (p := 2 * ρ) (q := 3 * ρ) (by positivity)
    (by linarith) ha'
  have h3 : ρ * ((1 / a + 1 / (a + 1)) / 2) ≤
      ρ * (((2 * ρ + 3 * ρ - a) / (2 * ρ * (3 * ρ)) +
        (2 * ρ + 3 * ρ - (a + 1)) / (2 * ρ * (3 * ρ))) / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hρ.le
  refine h3.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The six runs of jets against the degrees.** For `ρ = r` and `m = 2j + 1` the six
logarithms bound the row and column sums of the jets of the two ends from below. Each is bounded
by a rational function and each `1/y` by its tangent at `m = ρ/2`; what remains is linear in
`m/ρ`. -/
theorem endSums_real {ρ m s : ℝ} (hρ : 1 ≤ ρ) (hm : 1 ≤ m) (hm' : m ≤ 2 * ρ - 1)
    (hs : s ≤ 1.41422) :
    4 * (s * ((6 - m / ρ) / 12 + (Real.log 3 - Real.log 2))) - 4 * Real.log 2 + 1 / 10 +
        6 / 99 ≤
      (Real.log (8 * ρ + m / 2) - Real.log (6 * ρ + m / 2)) +
      (Real.log (4 * ρ - m / 2) - Real.log (2 * ρ - m / 2)) +
      (Real.log (7 * ρ + m - 1 / 2) - Real.log (6 * ρ + m - 1 / 2)) +
      (Real.log (7 * ρ + m + 1 / 2) - Real.log (6 * ρ + m + 1 / 2)) +
      (Real.log (2 * ρ + m - 1 / 2) - Real.log (ρ + m - 1 / 2)) +
      (Real.log (2 * ρ + m + 1 / 2) - Real.log (ρ + m + 1 / 2)) := by
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  obtain ⟨hl3a, hl3⟩ := log_three_mem
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = m / ρ := ⟨_, rfl⟩
  obtain ⟨ι, hι⟩ : ∃ ι : ℝ, ι = 1 / ρ := ⟨_, rfl⟩
  rw [← hν]
  have hν0 : 0 ≤ ν := by rw [hν]; exact div_nonneg (by linarith) hρ0.le
  have hν2 : ν ≤ 2 := by rw [hν, div_le_iff₀ hρ0]; linarith
  -- the tangent of `ρ/y` in the variable `y/ρ`
  have tan : ∀ (y k : ℝ), 0 < y → 0 < k → (2 * k - y / ρ) / k ^ 2 ≤ ρ / y := fun y k hy hk => by
    have h := tangent_le_one_div (y := y / ρ) (y₀ := k) (div_pos hy hρ0) hk
    rwa [one_div_div] at h
  have t1 : 4 * ((2 * (29 / 2) - (14 + ν)) / (29 / 2) ^ 2) ≤
      Real.log (8 * ρ + m / 2) - Real.log (6 * ρ + m / 2) := by
    have hp := two_mul_sub_div_add_le_log_sub (u := 8 * ρ + m / 2) (v := 6 * ρ + m / 2)
      (by linarith) (by linarith)
    have e : 2 * (8 * ρ + m / 2 - (6 * ρ + m / 2)) / (8 * ρ + m / 2 + (6 * ρ + m / 2)) =
        4 * (ρ / (14 * ρ + m)) := by
      rw [show 8 * ρ + m / 2 - (6 * ρ + m / 2) = 2 * ρ by ring,
        show 8 * ρ + m / 2 + (6 * ρ + m / 2) = 14 * ρ + m by ring]
      ring
    have ht := tan (14 * ρ + m) (29 / 2) (by linarith) (by norm_num)
    rw [show (14 * ρ + m) / ρ = 14 + ν by rw [hν]; field_simp] at ht
    rw [e] at hp
    linarith
  have t2 : Real.log 2 - 2 / 3 + 32 / 3 * ((2 * (29 / 2) - (16 - 3 * ν)) / (29 / 2) ^ 2) ≤
      Real.log (4 * ρ - m / 2) - Real.log (2 * ρ - m / 2) := by
    have hp := two_mul_sub_div_add_le_log_sub (u := 4 * ρ - m / 2) (v := 4 * ρ - m)
      (by linarith) (by linarith)
    have hlog : Real.log (2 * ρ - m / 2) = Real.log (4 * ρ - m) - Real.log 2 := by
      rw [← Real.log_div (by linarith) two_ne_zero]
      congr 1
      ring
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 16 * ρ - 3 * m := ⟨_, rfl⟩
    have hD0 : 0 < D := by rw [hD]; linarith
    have e : 2 * (4 * ρ - m / 2 - (4 * ρ - m)) / (4 * ρ - m / 2 + (4 * ρ - m)) =
        -(2 / 3) + 32 / 3 * (ρ / (16 * ρ - 3 * m)) := by
      rw [show 4 * ρ - m / 2 - (4 * ρ - m) = m / 2 by ring,
        show 4 * ρ - m / 2 + (4 * ρ - m) = (16 * ρ - 3 * m) / 2 by ring, ← hD]
      field_simp
      rw [hD]
      ring
    have ht := tan (16 * ρ - 3 * m) (29 / 2) (by linarith) (by norm_num)
    rw [show (16 * ρ - 3 * m) / ρ = 16 - 3 * ν by rw [hν]; field_simp] at ht
    rw [e] at hp
    rw [hlog]
    linarith
  have t3 : 2 * ((2 * 14 - (13 + 2 * ν - ι)) / 14 ^ 2) ≤
      Real.log (7 * ρ + m - 1 / 2) - Real.log (6 * ρ + m - 1 / 2) := by
    have hp := two_mul_sub_div_add_le_log_sub (u := 7 * ρ + m - 1 / 2) (v := 6 * ρ + m - 1 / 2)
      (by linarith) (by linarith)
    have e : 2 * (7 * ρ + m - 1 / 2 - (6 * ρ + m - 1 / 2)) /
        (7 * ρ + m - 1 / 2 + (6 * ρ + m - 1 / 2)) = 2 * (ρ / (13 * ρ + 2 * m - 1)) := by
      rw [show 7 * ρ + m - 1 / 2 - (6 * ρ + m - 1 / 2) = ρ by ring,
        show 7 * ρ + m - 1 / 2 + (6 * ρ + m - 1 / 2) = 13 * ρ + 2 * m - 1 by ring]
      ring
    have ht := tan (13 * ρ + 2 * m - 1) 14 (by linarith) (by norm_num)
    rw [show (13 * ρ + 2 * m - 1) / ρ = 13 + 2 * ν - ι by rw [hν, hι]; field_simp] at ht
    rw [e] at hp
    linarith
  have t5 : 2 * ((2 * 14 - (13 + 2 * ν + ι)) / 14 ^ 2) ≤
      Real.log (7 * ρ + m + 1 / 2) - Real.log (6 * ρ + m + 1 / 2) := by
    have hp := two_mul_sub_div_add_le_log_sub (u := 7 * ρ + m + 1 / 2) (v := 6 * ρ + m + 1 / 2)
      (by linarith) (by linarith)
    have e : 2 * (7 * ρ + m + 1 / 2 - (6 * ρ + m + 1 / 2)) /
        (7 * ρ + m + 1 / 2 + (6 * ρ + m + 1 / 2)) = 2 * (ρ / (13 * ρ + 2 * m + 1)) := by
      rw [show 7 * ρ + m + 1 / 2 - (6 * ρ + m + 1 / 2) = ρ by ring,
        show 7 * ρ + m + 1 / 2 + (6 * ρ + m + 1 / 2) = 13 * ρ + 2 * m + 1 by ring]
      ring
    have ht := tan (13 * ρ + 2 * m + 1) 14 (by linarith) (by norm_num)
    rw [show (13 * ρ + 2 * m + 1) / ρ = 13 + 2 * ν + ι by rw [hν, hι]; field_simp] at ht
    rw [e] at hp
    linarith
  have t4 : Real.log 2 - 3 / 4 + 2 * ((2 * 5 - (4 + 2 * ν - ι)) / 5 ^ 2) +
      1 / 2 * ((2 * 3 - (2 + 2 * ν - ι)) / 3 ^ 2) ≤
      Real.log (2 * ρ + m - 1 / 2) - Real.log (ρ + m - 1 / 2) := by
    have hp := log_two_end_ge (ρ := ρ) (w := 2 * m - 1) hρ0 (by linarith)
    rw [show 2 * ρ + (2 * m - 1) / 2 = 2 * ρ + m - 1 / 2 by ring,
      show ρ + (2 * m - 1) / 2 = ρ + m - 1 / 2 by ring] at hp
    have ht1 := tan (4 * ρ + (2 * m - 1)) 5 (by linarith) (by norm_num)
    have ht2 := tan (2 * ρ + (2 * m - 1)) 3 (by linarith) (by norm_num)
    rw [show (4 * ρ + (2 * m - 1)) / ρ = 4 + 2 * ν - ι by rw [hν, hι]; field_simp; ring] at ht1
    rw [show (2 * ρ + (2 * m - 1)) / ρ = 2 + 2 * ν - ι by rw [hν, hι]; field_simp; ring] at ht2
    linarith
  have t6 : Real.log 2 - 3 / 4 + 2 * ((2 * 5 - (4 + 2 * ν + ι)) / 5 ^ 2) +
      1 / 2 * ((2 * 3 - (2 + 2 * ν + ι)) / 3 ^ 2) ≤
      Real.log (2 * ρ + m + 1 / 2) - Real.log (ρ + m + 1 / 2) := by
    have hp := log_two_end_ge (ρ := ρ) (w := 2 * m + 1) hρ0 (by linarith)
    rw [show 2 * ρ + (2 * m + 1) / 2 = 2 * ρ + m + 1 / 2 by ring,
      show ρ + (2 * m + 1) / 2 = ρ + m + 1 / 2 by ring] at hp
    have ht1 := tan (4 * ρ + (2 * m + 1)) 5 (by linarith) (by norm_num)
    have ht2 := tan (2 * ρ + (2 * m + 1)) 3 (by linarith) (by norm_num)
    rw [show (4 * ρ + (2 * m + 1)) / ρ = 4 + 2 * ν + ι by rw [hν, hι]; field_simp; ring] at ht1
    rw [show (2 * ρ + (2 * m + 1)) / ρ = 2 + 2 * ν + ι by rw [hν, hι]; field_simp; ring] at ht2
    linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (6 - ν) / 12 + (Real.log 3 - Real.log 2) := ⟨_, rfl⟩
  rw [← hXdef]
  have hX : 0 ≤ X := by rw [hXdef]; linarith
  have hsX : s * X ≤ 1.41422 * X := mul_le_mul_of_nonneg_right hs hX
  norm_num at t1 t2 t3 t5 t4 t6 hsX ⊢
  linarith

/-! ### Quadratic forms on blocks -/

/-- A symmetric quadratic form on `n + m` blocks: the two diagonal parts and twice the cross
part. -/
theorem sum_sum_range_add_symm (n m : ℕ) (x : ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (hB : ∀ i l, B i l = B l i) :
    ∑ i ∈ range (n + m), ∑ l ∈ range (n + m), x i * x l * B i l =
      ∑ i ∈ range n, ∑ l ∈ range n, x i * x l * B i l +
        2 * ∑ i ∈ range n, ∑ l ∈ range m, x i * x (n + l) * B i (n + l) +
          ∑ i ∈ range m, ∑ l ∈ range m, x (n + i) * x (n + l) * B (n + i) (n + l) := by
  have h2 : ∑ i ∈ range m, ∑ l ∈ range n, x (n + i) * x l * B (n + i) l =
      ∑ i ∈ range n, ∑ l ∈ range m, x i * x (n + l) * B i (n + l) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by
      rw [hB (n + l) i]
      ring
  simp only [Finset.sum_range_add, Finset.sum_add_distrib]
  rw [h2]
  ring

/-- **Schur test** for a kernel `k ≥ 0`: the form is at most `κ Σ σ_j²` when every row sum plus
column sum is at most `2κ`. -/
theorem sum_sum_mul_le_of_nonneg {J : ℕ} (σ : ℕ → ℝ) (k : ℕ → ℕ → ℝ) {κ : ℝ}
    (hk : ∀ j < J, ∀ l < J, 0 ≤ k j l)
    (hrow : ∀ j < J, ∑ l ∈ range J, (k j l + k l j) ≤ 2 * κ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * k j l ≤ κ * ∑ j ∈ range J, σ j ^ 2 := by
  have h1 : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * k j l ≤
      ∑ j ∈ range J, ∑ l ∈ range J, (σ j ^ 2 * k j l / 2 + σ l ^ 2 * k j l / 2) :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l hl => by
      nlinarith [mul_nonneg (hk j (Finset.mem_range.mp hj) l (Finset.mem_range.mp hl))
        (sq_nonneg (σ j - σ l))]
  have hswap : ∑ j ∈ range J, ∑ l ∈ range J, σ l ^ 2 * k j l / 2 =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j ^ 2 * k l j / 2 := Finset.sum_comm
  have h2 : ∑ j ∈ range J, ∑ l ∈ range J, (σ j ^ 2 * k j l / 2 + σ l ^ 2 * k j l / 2) =
      ∑ j ∈ range J, σ j ^ 2 / 2 * ∑ l ∈ range J, (k j l + k l j) := by
    calc ∑ j ∈ range J, ∑ l ∈ range J, (σ j ^ 2 * k j l / 2 + σ l ^ 2 * k j l / 2)
        = ∑ j ∈ range J, ∑ l ∈ range J, σ j ^ 2 * k j l / 2 +
            ∑ j ∈ range J, ∑ l ∈ range J, σ l ^ 2 * k j l / 2 := by
          simp only [Finset.sum_add_distrib]
      _ = ∑ j ∈ range J, ∑ l ∈ range J, σ j ^ 2 * k j l / 2 +
            ∑ j ∈ range J, ∑ l ∈ range J, σ j ^ 2 * k l j / 2 := by rw [hswap]
      _ = ∑ j ∈ range J, σ j ^ 2 / 2 * ∑ l ∈ range J, (k j l + k l j) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun l _ => by ring
  rw [h2] at h1
  refine h1.trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj => by
    nlinarith [mul_le_mul_of_nonneg_left (hrow j (Finset.mem_range.mp hj))
      (show 0 ≤ σ j ^ 2 / 2 by positivity)]

theorem sum_range_two_eq (f : ℕ → ℝ) : ∑ e ∈ range 2, f e = f 0 + f 1 := by
  simp [Finset.sum_range_succ]

/-- `Σ σ_j σ_l (d_j + d_l) = 2 (Σ σ_j)(Σ σ_j d_j)`. -/
theorem sum_sum_mul_add (J : ℕ) (σ d : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * (d j + d l) =
      (2 * ∑ j ∈ range J, σ j) * ∑ j ∈ range J, σ j * d j := by
  have h1 : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * d j =
      (∑ j ∈ range J, σ j * d j) * ∑ l ∈ range J, σ l := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have h2 : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * d l =
      (∑ j ∈ range J, σ j) * ∑ l ∈ range J, σ l * d l := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  calc ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * (d j + d l)
      = ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * d j +
          ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * d l := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = (2 * ∑ j ∈ range J, σ j) * ∑ j ∈ range J, σ j * d j := by
        rw [h1, h2]
        ring

/-- The margin of the odd sector from its four inputs: the block matrix `W` of the lower end,
the charges `P`, the jets `E` written through the kernel `K`, and the Schur bound of `K`. -/
theorem two_ends_margin {S P W NA K E s L : ℝ} (hs : s * s = 2) (hs1 : 7 / 5 ≤ s) (hS : 0 ≤ S)
    (hW : 1 / 5000 * S ≤ W) (hN : W = P + NA) (hE : E = s * P - K)
    (hK : K ≤ (L - 1 / 40) * S) :
    1 / 30 * S ≤ 2 * NA + s * (L * S + E) := by
  have hs0 : 0 ≤ s := by linarith
  have hKs := mul_le_mul_of_nonneg_left hK hs0
  have hsS := mul_le_mul_of_nonneg_right hs1 hS
  have e : 2 * NA + s * (L * S + E) = 2 * NA + s * s * P + L * (s * S) - s * K := by
    rw [hE]
    ring
  have e2 : s * ((L - 1 / 40) * S) = L * (s * S) - 1 / 40 * (s * S) := by ring
  rw [e, hs]
  rw [e2] at hKs
  linarith

/-- `a² ≤ c²` when `c ≤ a − S/60`, `a < 0 ≤ S`. -/
theorem mul_self_le_sq_of_le_sub {a c S : ℝ} (ha : a < 0) (hS : 0 ≤ S)
    (hc : c ≤ a - 1 / 60 * S) : a * a ≤ c ^ 2 := by
  nlinarith [mul_nonneg (show 0 ≤ a - c by linarith) (show 0 ≤ -a - c by linarith)]

/-! ### Degrees, jets and steps -/

/-- `2/y ≤ d(a)` for `y ≥ 2a + 1`. -/
theorem two_div_le_blockDegree {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 2 * (a : ℝ) + 1 ≤ y) :
    2 / y ≤ blockDegree a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h := two_mul_sub_div_add_le_log_sub (u := (a : ℝ) + 1) (v := a) ha' (by linarith)
  rw [show 2 * ((a : ℝ) + 1 - a) / ((a : ℝ) + 1 + a) = 2 / (2 * (a : ℝ) + 1) by
    rw [show (a : ℝ) + 1 - a = 1 by ring, show (a : ℝ) + 1 + a = 2 * a + 1 by ring,
      mul_one]] at h
  rw [blockDegree, Nat.cast_add, Nat.cast_one]
  exact (div_le_div_of_nonneg_left (by norm_num) (by linarith) hy).trans h

/-- The degree of a block is at most its trapezoid value. -/
theorem blockDegree_le_trapezoid {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : (a : ℝ) = y) :
    blockDegree a ≤ (1 / y + 1 / (y + 1)) / 2 := by
  subst hy
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h := log_sub_log_le_div (u := (a : ℝ) + 1) (v := a) ha' (by linarith)
  rw [blockDegree, Nat.cast_add, Nat.cast_one]
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- `D(n) ≤ 2/y` for `0 < y ≤ 2n − 1`, `D` the second difference of `n log n`. -/
theorem xLogXDiff_le_two_div_of_le {n : ℕ} (hn : 2 ≤ n) {y : ℝ} (hy : 0 < y)
    (hyn : y ≤ 2 * (n : ℝ) - 1) : xLogXDiff n ≤ 2 / y :=
  (xLogXDiff_le_two_div hn).trans (div_le_div_of_nonneg_left (by norm_num) hy hyn)

/-- The jets at `c + r, …, c + 1`, summed downwards. -/
theorem sum_range_xLogXDiff_sub (c r : ℕ) :
    ∑ l ∈ range r, xLogXDiff (c + r - l) = xLogXStep (c + r) - xLogXStep c := by
  refine Eq.trans ?_ (sum_range_xLogXDiff_add c r)
  refine Eq.trans ?_ (Finset.sum_range_reflect (fun l => xLogXDiff (c + l + 1)) r)
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  show xLogXDiff (c + r - l) = xLogXDiff (c + (r - 1 - l) + 1)
  congr 1
  omega

/-- **A run of consecutive jets** is at least the logarithm of the ratio of the midpoints of
its ends, up to `1/99`: the midpoint enclosure of the step of `n log n`. -/
theorem log_sub_log_le_xLogXStep_sub {p q : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hu : (p : ℝ) + 1 / 2 = u) (hv : (q : ℝ) + 1 / 2 = v) :
    Real.log u - Real.log v - 1 / 99 ≤ xLogXStep p - xLogXStep q := by
  subst hu hv
  have h1 := log_add_half_sub_le_xLogXStep (n := p) (by omega)
  have h2 := xLogXStep_le_log_add_half q
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h3 : 1 / ((4 * (p : ℝ) + 1) * (4 * (p : ℝ) + 3)) ≤ 1 / 99 :=
    one_div_le_one_div_of_le (by norm_num)
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hp')])
  linarith

/-! ### The two ends of the window -/

/-- The step packet `(σ, 0, U₂τ)` of the window `(2r, 6r]`: `σ` on the blocks of `(2r, 3r]`,
zero on `(3r, 4r]`, and the refinement of `τ` on `(4r, 6r]`. -/
def twoEnds (r : ℕ) (σ τ : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < r then σ i else if i < 2 * r then 0 else refineStep 2 τ (i - 2 * r)

theorem twoEnds_of_lt {r i : ℕ} (σ τ : ℕ → ℝ) (hi : i < r) : twoEnds r σ τ i = σ i := by
  rw [twoEnds, if_pos hi]

theorem twoEnds_add_of_lt {r i : ℕ} (σ τ : ℕ → ℝ) (hi : i < r) :
    twoEnds r σ τ (r + i) = 0 := by
  rw [twoEnds, if_neg (by omega), if_pos (by omega)]

theorem twoEnds_two_mul_add (r : ℕ) (σ τ : ℕ → ℝ) (i : ℕ) :
    twoEnds r σ τ (2 * r + i) = refineStep 2 τ i := by
  rw [twoEnds, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

/-- A sum against the two ends over the lower half `(2r, 4r]` sees `σ` only. -/
theorem sum_twoEnds_mul (r : ℕ) (σ τ : ℕ → ℝ) (g : ℕ → ℝ) :
    ∑ i ∈ range (2 * r), twoEnds r σ τ i * g i = ∑ j ∈ range r, σ j * g j := by
  have h0 : ∑ i ∈ range r, twoEnds r σ τ (r + i) * g (r + i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [twoEnds_add_of_lt σ τ (Finset.mem_range.mp hi), zero_mul]
  rw [two_mul, Finset.sum_range_add, h0, add_zero]
  exact Finset.sum_congr rfl fun j hj => by rw [twoEnds_of_lt σ τ (Finset.mem_range.mp hj)]

/-- The jets between the block `2r + j` of the lower end and the two children `2(2r + l)`,
`2(2r + l) + 1` of the block `2r + l`. -/
def endJet (r j l : ℕ) : ℝ :=
  blockJet (2 * r + j) (2 * (2 * r) + 2 * l) + blockJet (2 * r + j) (2 * (2 * r) + (2 * l + 1))

/-- **A block of the lower end and the two children of a block**: minus their jets, and minus
`log 2` if the children are its own. -/
theorem neutralBlock_add_children {r Q j l : ℕ} (hQ : 2 ≤ Q) (hj : j < r) (hl : l < r) :
    neutralBlock Q (2 * r + j) (2 * (2 * r) + (2 * l + 0)) +
        neutralBlock Q (2 * r + j) (2 * (2 * r) + (2 * l + 1)) =
      -(endJet r j l + if l = j then Real.log 2 else 0) := by
  rw [Nat.add_zero]
  have e₀ := blockWeight_eq_of_lt_three_mul (Q := Q) (a := 2 * r + j)
    (b := 2 * (2 * r) + 2 * l) hQ (by omega) (by omega)
  have e₁ := blockWeight_eq_of_lt_three_mul (Q := Q) (a := 2 * r + j)
    (b := 2 * (2 * r) + (2 * l + 1)) hQ (by omega) (by omega)
  have c₀ : (2 * (2 * r) + 2 * l) / 2 = 2 * r + j ↔ l = j := by omega
  have c₁ : (2 * (2 * r) + (2 * l + 1)) / 2 = 2 * r + j ↔ l = j := by omega
  rw [if_congr c₀ rfl rfl, blockWeight] at e₀
  rw [if_congr c₁ rfl rfl, blockWeight] at e₁
  rw [endJet]
  by_cases hlj : l = j
  · rw [if_pos hlj] at e₀ e₁ ⊢
    linarith
  · rw [if_neg hlj] at e₀ e₁ ⊢
    linarith

/-- The coupling of a block of the lower end with a refined packet on the upper end. -/
theorem sum_refineStep_mul_neutralBlock {r Q j : ℕ} (hQ : 2 ≤ Q) (hj : j < r) (τ : ℕ → ℝ) :
    ∑ l ∈ range (2 * r), refineStep 2 τ l * neutralBlock Q (2 * r + j) (2 * (2 * r) + l) =
      -(1 / Real.sqrt 2) * (Real.log 2 * τ j + ∑ l ∈ range r, τ l * endJet r j l) := by
  have h2 : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
  have hl : ∀ l ∈ range r, ∑ e ∈ range 2, refineStep 2 τ (2 * l + e) *
      neutralBlock Q (2 * r + j) (2 * (2 * r) + (2 * l + e)) =
      -(1 / Real.sqrt 2) * ((if l = j then Real.log 2 * τ l else 0) + τ l * endJet r j l) :=
    fun l hl => by
      have hc := neutralBlock_add_children hQ hj (Finset.mem_range.mp hl)
      rw [sum_range_two_eq, refineStep_mul_add (by norm_num) τ l (by norm_num : 0 < 2),
        refineStep_mul_add (by norm_num) τ l (by norm_num : 1 < 2), h2, ← mul_add, hc]
      by_cases hlj : l = j
      · rw [if_pos hlj, if_pos hlj]
        ring
      · rw [if_neg hlj, if_neg hlj]
        ring
  rw [sum_range_mul_eq 2 r
      (fun l => refineStep 2 τ l * neutralBlock Q (2 * r + j) (2 * (2 * r) + l)),
    Finset.sum_congr rfl hl, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr hj)]

/-- **The two ends.** `N(σ, 0, U₂τ) = N_A(σ) + N_A(τ) − √2 (log 2 · Σ σ_j τ_j + Σ σ_j τ_l K(j, l))`:
the upper end carries `N_A(τ)` by the invariance under refinement, and the two ends are coupled
through the jets `K` and the contact of the floor map of `2`. -/
theorem sum_neutralBlock_twoEnds {r Q : ℕ} (hr : 1 ≤ r) (hQ : 2 ≤ Q) (σ τ : ℕ → ℝ) :
    ∑ i ∈ range (2 * (2 * r)), ∑ l ∈ range (2 * (2 * r)),
        twoEnds r σ τ i * twoEnds r σ τ l * neutralBlock Q (2 * r + i) (2 * r + l) =
      ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * neutralBlock Q (2 * r + j) (2 * r + l) +
          ∑ j ∈ range r, ∑ l ∈ range r, τ j * τ l * neutralBlock Q (2 * r + j) (2 * r + l) -
        Real.sqrt 2 * (Real.log 2 * ∑ j ∈ range r, σ j * τ j +
          ∑ j ∈ range r, ∑ l ∈ range r, σ j * τ l * endJet r j l) := by
  -- the lower end
  have hA : ∑ i ∈ range (2 * r), ∑ l ∈ range (2 * r),
      twoEnds r σ τ i * twoEnds r σ τ l * neutralBlock Q (2 * r + i) (2 * r + l) =
      ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * neutralBlock Q (2 * r + j) (2 * r + l) := by
    have h1 : ∀ i, ∑ l ∈ range (2 * r),
        twoEnds r σ τ i * twoEnds r σ τ l * neutralBlock Q (2 * r + i) (2 * r + l) =
        twoEnds r σ τ i * ∑ l ∈ range r, σ l * neutralBlock Q (2 * r + i) (2 * r + l) :=
      fun i => by
        rw [← sum_twoEnds_mul r σ τ (fun l => neutralBlock Q (2 * r + i) (2 * r + l)),
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    refine (Finset.sum_congr rfl fun i _ => h1 i).trans ?_
    rw [sum_twoEnds_mul r σ τ
      (fun i => ∑ l ∈ range r, σ l * neutralBlock Q (2 * r + i) (2 * r + l))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  -- the upper end: the refinement of `τ`
  have hC : ∑ i ∈ range (2 * r), ∑ l ∈ range (2 * r),
      twoEnds r σ τ (2 * r + i) * twoEnds r σ τ (2 * r + l) *
        neutralBlock Q (2 * r + (2 * r + i)) (2 * r + (2 * r + l)) =
      ∑ j ∈ range r, ∑ l ∈ range r, τ j * τ l * neutralBlock Q (2 * r + j) (2 * r + l) := by
    refine Eq.trans ?_
      (sum_neutralBlock_refine (R := 2 * r) (by omega) (m := 2) (by norm_num) Q r τ)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [twoEnds_two_mul_add, twoEnds_two_mul_add, ← add_assoc, ← add_assoc, ← two_mul]
  -- the coupling of the two ends
  have hB : ∑ i ∈ range (2 * r), ∑ l ∈ range (2 * r),
      twoEnds r σ τ i * twoEnds r σ τ (2 * r + l) *
        neutralBlock Q (2 * r + i) (2 * r + (2 * r + l)) =
      -(1 / Real.sqrt 2) * (Real.log 2 * ∑ j ∈ range r, σ j * τ j +
        ∑ j ∈ range r, ∑ l ∈ range r, σ j * τ l * endJet r j l) := by
    have h1 : ∀ i, ∑ l ∈ range (2 * r), twoEnds r σ τ i * twoEnds r σ τ (2 * r + l) *
        neutralBlock Q (2 * r + i) (2 * r + (2 * r + l)) =
        twoEnds r σ τ i * ∑ l ∈ range (2 * r),
          refineStep 2 τ l * neutralBlock Q (2 * r + i) (2 * (2 * r) + l) := fun i => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [twoEnds_two_mul_add, ← add_assoc, ← two_mul, mul_assoc]
    have h2 : ∀ j ∈ range r, σ j * ∑ l ∈ range (2 * r),
        refineStep 2 τ l * neutralBlock Q (2 * r + j) (2 * (2 * r) + l) =
        -(1 / Real.sqrt 2) * (Real.log 2 * (σ j * τ j) +
          ∑ l ∈ range r, σ j * τ l * endJet r j l) := fun j hj => by
      have e : ∑ l ∈ range r, σ j * τ l * endJet r j l =
          σ j * ∑ l ∈ range r, τ l * endJet r j l := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _
      rw [sum_refineStep_mul_neutralBlock hQ (Finset.mem_range.mp hj) τ, e]
      ring
    refine (Finset.sum_congr rfl fun i _ => h1 i).trans ?_
    rw [sum_twoEnds_mul r σ τ (fun i => ∑ l ∈ range (2 * r),
        refineStep 2 τ l * neutralBlock Q (2 * r + i) (2 * (2 * r) + l)),
      Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff h0 two_ne_zero]
    linarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [show 2 * (2 * r) = 2 * r + 2 * r from two_mul _,
    sum_sum_range_add_symm (2 * r) (2 * r) (twoEnds r σ τ)
      (fun i l => neutralBlock Q (2 * r + i) (2 * r + l)) (fun i l => neutralBlock_comm Q _ _),
    hA, hB, hC, hinv]
  ring

/-- **The odd sector of the two ends**: for `τ = −σ` the charges of the two ends add up. -/
theorem sum_neutralBlock_twoEnds_odd {r Q : ℕ} (hr : 1 ≤ r) (hQ : 2 ≤ Q) (σ τ : ℕ → ℝ)
    (hτ : ∀ j, τ j = -σ j) :
    ∑ i ∈ range (2 * (2 * r)), ∑ l ∈ range (2 * (2 * r)),
        twoEnds r σ τ i * twoEnds r σ τ l * neutralBlock Q (2 * r + i) (2 * r + l) =
      2 * ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * neutralBlock Q (2 * r + j) (2 * r + l) +
        Real.sqrt 2 * (Real.log 2 * ∑ j ∈ range r, σ j ^ 2 +
          ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * endJet r j l) := by
  have e1 : ∑ j ∈ range r, ∑ l ∈ range r, -σ j * -σ l * neutralBlock Q (2 * r + j) (2 * r + l) =
      ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * neutralBlock Q (2 * r + j) (2 * r + l) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have e2 : ∑ j ∈ range r, σ j * -σ j = -∑ j ∈ range r, σ j ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j ∈ range r, ∑ l ∈ range r, σ j * -σ l * endJet r j l =
      -∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * endJet r j l := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [sum_neutralBlock_twoEnds hr hQ σ τ]
  simp only [hτ]
  rw [e1, e2, e3]
  ring

/-! ### The kernel of the odd sector -/

/-- The kernel of the odd sector: `√2 (d_j + d_l)` minus the jets of the two ends. -/
def endKernel (r j l : ℕ) : ℝ :=
  Real.sqrt 2 * (blockDegree (2 * r + j) + blockDegree (2 * r + l)) - endJet r j l

/-- The jets of the two ends are at most `2/(γ + α) + 2/(γ − α)`, `γ = 4(2r + l)`,
`α = 2(2r + j) + 1`. -/
theorem endJet_le {r j l : ℕ} (hj : j < r) (hl : l < r) :
    endJet r j l ≤ 2 / (8 * (r : ℝ) + 4 * l + (4 * (r : ℝ) + 2 * j + 1)) +
      2 / (8 * (r : ℝ) + 4 * l - (4 * (r : ℝ) + 2 * j + 1)) := by
  have hjr : (j : ℝ) + 1 ≤ r := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have h1 : xLogXDiff (2 * r + j + (2 * (2 * r) + 2 * l) + 1) ≤
      2 / (8 * (r : ℝ) + 4 * l + (4 * (r : ℝ) + 2 * j + 1)) :=
    xLogXDiff_le_two_div_of_le (by omega) (by linarith) (by push_cast; linarith)
  have h2 : xLogXDiff (2 * (2 * r) + 2 * l - (2 * r + j)) ≤
      2 / (8 * (r : ℝ) + 4 * l - (4 * (r : ℝ) + 2 * j + 1)) :=
    xLogXDiff_le_two_div_of_le (by omega) (by linarith) (by
      rw [Nat.cast_sub (show 2 * r + j ≤ 2 * (2 * r) + 2 * l by omega)]
      push_cast
      linarith)
  have h3 : xLogXDiff (2 * r + j + (2 * (2 * r) + (2 * l + 1)) + 1) ≤
      2 / (8 * (r : ℝ) + 4 * l + (4 * (r : ℝ) + 2 * j + 1)) :=
    xLogXDiff_le_two_div_of_le (by omega) (by linarith) (by push_cast; linarith)
  have h4 : xLogXDiff (2 * (2 * r) + (2 * l + 1) - (2 * r + j)) ≤
      2 / (8 * (r : ℝ) + 4 * l - (4 * (r : ℝ) + 2 * j + 1)) :=
    xLogXDiff_le_two_div_of_le (by omega) (by linarith) (by
      rw [Nat.cast_sub (show 2 * r + j ≤ 2 * (2 * r) + (2 * l + 1) by omega)]
      push_cast
      linarith)
  unfold endJet blockJet
  linarith

/-- **The kernel of the odd sector is nonnegative**: the degrees of two blocks, times `√2`,
exceed the jets between one of them and the children of the other. -/
theorem endKernel_nonneg {r j l : ℕ} (hj : j < r) (hl : l < r) : 0 ≤ endKernel r j l := by
  have hjr : (j : ℝ) + 1 ≤ r := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hJ := endJet_le hj hl
  have hdj := two_div_le_blockDegree (a := 2 * r + j) (by omega)
    (y := 4 * (r : ℝ) + 2 * j + 1) (by push_cast; linarith)
  have hdl := two_div_le_blockDegree (a := 2 * r + l) (by omega)
    (y := 4 * (r : ℝ) + 2 * l + 1) (by push_cast; linarith)
  have hR := end_kernel_real (α := 4 * (r : ℝ) + 2 * j + 1) (γ := 8 * (r : ℝ) + 4 * l)
    (s := Real.sqrt 2) (by linarith) (by linarith) sqrt_two_mem.1
    (by linarith [sqrt_two_mem.2])
  have e4 : (4 : ℝ) / (8 * (r : ℝ) + 4 * l + 2) = 2 / (4 * (r : ℝ) + 2 * l + 1) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  have hsum : 2 / (4 * (r : ℝ) + 2 * j + 1) + 4 / (8 * (r : ℝ) + 4 * l + 2) ≤
      blockDegree (2 * r + j) + blockDegree (2 * r + l) := by
    rw [e4]
    exact add_le_add hdj hdl
  have hmul := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg 2)
  rw [endKernel]
  linarith

/-- The row sum of the jets of the two ends: two runs of consecutive jets. -/
theorem sum_endJet_row {r j : ℕ} (hj : j < r) :
    ∑ l ∈ range r, endJet r j l =
      ((xLogXStep (6 * r + j + 2 * r) - xLogXStep (6 * r + j)) +
        (xLogXStep (2 * r - j - 1 + 2 * r) - xLogXStep (2 * r - j - 1))) / 2 := by
  rw [← sum_range_xLogXDiff_add (6 * r + j) (2 * r),
    ← sum_range_xLogXDiff_add (2 * r - j - 1) (2 * r),
    sum_range_mul_eq 2 r (fun i => xLogXDiff (6 * r + j + i + 1)),
    sum_range_mul_eq 2 r (fun i => xLogXDiff (2 * r - j - 1 + i + 1)),
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  have i1 : 2 * r + j + (2 * (2 * r) + 2 * l) + 1 = 6 * r + j + (2 * l + 0) + 1 := by omega
  have i2 : 2 * (2 * r) + 2 * l - (2 * r + j) = 2 * r - j - 1 + (2 * l + 0) + 1 := by omega
  have i3 : 2 * r + j + (2 * (2 * r) + (2 * l + 1)) + 1 = 6 * r + j + (2 * l + 1) + 1 := by
    omega
  have i4 : 2 * (2 * r) + (2 * l + 1) - (2 * r + j) = 2 * r - j - 1 + (2 * l + 1) + 1 := by
    omega
  rw [sum_range_two_eq, sum_range_two_eq]
  unfold endJet blockJet
  rw [i1, i2, i3, i4]
  ring

/-- The column sum of the jets of the two ends: four runs of consecutive jets. -/
theorem sum_endJet_col (r j : ℕ) :
    ∑ l ∈ range r, endJet r l j =
      ((xLogXStep (6 * r + 2 * j + r) - xLogXStep (6 * r + 2 * j)) +
        (xLogXStep (r + 2 * j + r) - xLogXStep (r + 2 * j)) +
        (xLogXStep (6 * r + 2 * j + 1 + r) - xLogXStep (6 * r + 2 * j + 1)) +
        (xLogXStep (r + 2 * j + 1 + r) - xLogXStep (r + 2 * j + 1))) / 2 := by
  rw [← sum_range_xLogXDiff_add (6 * r + 2 * j) r, ← sum_range_xLogXDiff_sub (r + 2 * j) r,
    ← sum_range_xLogXDiff_add (6 * r + 2 * j + 1) r,
    ← sum_range_xLogXDiff_sub (r + 2 * j + 1) r, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  have i1 : 2 * r + l + (2 * (2 * r) + 2 * j) + 1 = 6 * r + 2 * j + l + 1 := by omega
  have i2 : 2 * (2 * r) + 2 * j - (2 * r + l) = r + 2 * j + r - l := by omega
  have i3 : 2 * r + l + (2 * (2 * r) + (2 * j + 1)) + 1 = 6 * r + 2 * j + 1 + l + 1 := by omega
  have i4 : 2 * (2 * r) + (2 * j + 1) - (2 * r + l) = r + 2 * j + 1 + r - l := by omega
  unfold endJet blockJet
  rw [i1, i2, i3, i4]
  ring

/-- The row sum plus the column sum of the kernel: the degrees of the lower end against the
six runs of jets. -/
theorem sum_endKernel_add {r : ℕ} (hr : 1 ≤ r) (j : ℕ) :
    ∑ l ∈ range r, (endKernel r j l + endKernel r l j) =
      2 * Real.sqrt 2 * (r * blockDegree (2 * r + j) + (Real.log 3 - Real.log 2)) -
        ∑ l ∈ range r, (endJet r j l + endJet r l j) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd : ∑ l ∈ range r, blockDegree (2 * r + l) = Real.log 3 - Real.log 2 := by
    rw [sum_blockDegree_range, show ((2 * r + r : ℕ) : ℝ) = 3 * (r : ℝ) by push_cast; ring,
      show ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) by push_cast; ring,
      Real.log_mul (by norm_num) hr'.ne', Real.log_mul (by norm_num) hr'.ne']
    ring
  have h : ∀ l ∈ range r, endKernel r j l + endKernel r l j =
      2 * Real.sqrt 2 * blockDegree (2 * r + j) + 2 * Real.sqrt 2 * blockDegree (2 * r + l) -
        (endJet r j l + endJet r l j) := fun l _ => by
    unfold endKernel
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, hd]
  ring

/-- **The row and column sums of the kernel**: `Σ_l (k(j, l) + k(l, j)) ≤ 2 (log 2 − 1/40)` at
every block size. -/
theorem sum_endKernel_add_le {r j : ℕ} (hr : 1 ≤ r) (hj : j < r) :
    ∑ l ∈ range r, (endKernel r j l + endKernel r l j) ≤ 2 * (Real.log 2 - 1 / 40) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hjr : (j : ℝ) + 1 ≤ r := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hq : ((2 * r - j - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - j - 1 := by
    rw [Nat.cast_sub (show 1 ≤ 2 * r - j by omega), Nat.cast_sub (show j ≤ 2 * r by omega)]
    push_cast
    ring
  -- the six runs of jets
  have s1 : Real.log (8 * (r : ℝ) + (2 * (j : ℝ) + 1) / 2) -
      Real.log (6 * (r : ℝ) + (2 * (j : ℝ) + 1) / 2) - 1 / 99 ≤
      xLogXStep (6 * r + j + 2 * r) - xLogXStep (6 * r + j) :=
    log_sub_log_le_xLogXStep_sub (by omega) (by push_cast; ring) (by push_cast; ring)
  have s2 : Real.log (4 * (r : ℝ) - (2 * (j : ℝ) + 1) / 2) -
      Real.log (2 * (r : ℝ) - (2 * (j : ℝ) + 1) / 2) - 1 / 99 ≤
      xLogXStep (2 * r - j - 1 + 2 * r) - xLogXStep (2 * r - j - 1) :=
    log_sub_log_le_xLogXStep_sub (by omega)
      (by rw [Nat.cast_add, hq]; push_cast; ring) (by rw [hq]; ring)
  have s3 : Real.log (7 * (r : ℝ) + (2 * (j : ℝ) + 1) - 1 / 2) -
      Real.log (6 * (r : ℝ) + (2 * (j : ℝ) + 1) - 1 / 2) - 1 / 99 ≤
      xLogXStep (6 * r + 2 * j + r) - xLogXStep (6 * r + 2 * j) :=
    log_sub_log_le_xLogXStep_sub (by omega) (by push_cast; ring) (by push_cast; ring)
  have s4 : Real.log (2 * (r : ℝ) + (2 * (j : ℝ) + 1) - 1 / 2) -
      Real.log ((r : ℝ) + (2 * (j : ℝ) + 1) - 1 / 2) - 1 / 99 ≤
      xLogXStep (r + 2 * j + r) - xLogXStep (r + 2 * j) :=
    log_sub_log_le_xLogXStep_sub (by omega) (by push_cast; ring) (by push_cast; ring)
  have s5 : Real.log (7 * (r : ℝ) + (2 * (j : ℝ) + 1) + 1 / 2) -
      Real.log (6 * (r : ℝ) + (2 * (j : ℝ) + 1) + 1 / 2) - 1 / 99 ≤
      xLogXStep (6 * r + 2 * j + 1 + r) - xLogXStep (6 * r + 2 * j + 1) :=
    log_sub_log_le_xLogXStep_sub (by omega) (by push_cast; ring) (by push_cast; ring)
  have s6 : Real.log (2 * (r : ℝ) + (2 * (j : ℝ) + 1) + 1 / 2) -
      Real.log ((r : ℝ) + (2 * (j : ℝ) + 1) + 1 / 2) - 1 / 99 ≤
      xLogXStep (r + 2 * j + 1 + r) - xLogXStep (r + 2 * j + 1) :=
    log_sub_log_le_xLogXStep_sub (by omega) (by push_cast; ring) (by push_cast; ring)
  have hE := endSums_real (ρ := (r : ℝ)) (m := 2 * (j : ℝ) + 1) (s := Real.sqrt 2) hr'
    (by linarith) (by linarith) sqrt_two_mem.2
  -- the degrees of the lower end: trapezoid and chord
  have hdiv : (2 * (2 * (r : ℝ) + j) + 1) / r = 4 + (2 * (j : ℝ) + 1) / r := by
    rw [show 2 * (2 * (r : ℝ) + j) + 1 = 4 * r + (2 * j + 1) by ring, add_div,
      mul_div_assoc, div_self hr0.ne', mul_one]
  have hd : (r : ℝ) * blockDegree (2 * r + j) ≤ (6 - (2 * (j : ℝ) + 1) / r) / 12 := by
    have h1 := blockDegree_le_trapezoid (a := 2 * r + j) (by omega)
      (y := 2 * (r : ℝ) + j) (by norm_num)
    have h2 := degree_chord (ρ := (r : ℝ)) (a := 2 * (r : ℝ) + j) hr0 (by linarith)
      (by linarith)
    rw [hdiv] at h2
    exact ((mul_le_mul_of_nonneg_left h1 hr0.le).trans h2).trans (le_of_eq (by ring))
  have hprod : Real.sqrt 2 * ((r : ℝ) * blockDegree (2 * r + j) +
      (Real.log 3 - Real.log 2)) ≤
      Real.sqrt 2 * ((6 - (2 * (j : ℝ) + 1) / r) / 12 + (Real.log 3 - Real.log 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
  rw [sum_endKernel_add hr j, Finset.sum_add_distrib, sum_endJet_row hj, sum_endJet_col r j,
    show 2 * Real.sqrt 2 * ((r : ℝ) * blockDegree (2 * r + j) + (Real.log 3 - Real.log 2)) =
      2 * (Real.sqrt 2 * ((r : ℝ) * blockDegree (2 * r + j) + (Real.log 3 - Real.log 2)))
      by ring]
  linarith

/-- **The Schur bound of the kernel**: `Σ σ_j σ_l k(j, l) ≤ (log 2 − 1/40) Σ σ_j²`. -/
theorem sum_sum_mul_endKernel_le {r : ℕ} (hr : 1 ≤ r) (σ : ℕ → ℝ) :
    ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * endKernel r j l ≤
      (Real.log 2 - 1 / 40) * ∑ j ∈ range r, σ j ^ 2 :=
  sum_sum_mul_le_of_nonneg σ (endKernel r) (fun _ hj _ hl => endKernel_nonneg hj hl)
    fun _ hj => sum_endKernel_add_le hr hj

/-! ### The odd sector -/

/-- **The neutral part of the window `(2r, 6r]` on a packet minus its dilate by two** is at
least `(1/30) Σ σ_j²`, at every block size `r ≥ 1` and for every `Q ≥ 2`. -/
theorem sum_neutralBlock_twoEnds_ge {r Q : ℕ} (hr : 1 ≤ r) (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    1 / 30 * ∑ j ∈ range r, σ j ^ 2 ≤
      ∑ i ∈ range (2 * (2 * r)), ∑ l ∈ range (2 * (2 * r)),
        twoEnds r σ (fun j => -σ j) i * twoEnds r σ (fun j => -σ j) l *
          neutralBlock Q (2 * r + i) (2 * r + l) := by
  rw [sum_neutralBlock_twoEnds_odd hr hQ σ (fun j => -σ j) fun _ => rfl]
  -- the lower end is a short window
  have hW := sum_blockMatrix_ge_of_short (R := 2 * r) (J := r) (Q := Q) (by omega) (by omega)
    hQ σ
  have hN := sum_blockMatrix_eq_charges_add_neutral Q (2 * r) r σ
  -- the jets through the kernel: the degrees give the product of the charges
  have hJ : ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * endJet r j l =
      Real.sqrt 2 * ((2 * ∑ j ∈ range r, σ j) *
        ∑ j ∈ range r, σ j * blockDegree (2 * r + j)) -
        ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * endKernel r j l := by
    have h : ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * endJet r j l =
        ∑ j ∈ range r, (Real.sqrt 2 * ∑ l ∈ range r,
          σ j * σ l * (blockDegree (2 * r + j) + blockDegree (2 * r + l)) -
          ∑ l ∈ range r, σ j * σ l * endKernel r j l) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold endKernel
      ring
    rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_sum_mul_add r σ (fun j => blockDegree (2 * r + j))]
  exact two_ends_margin (Real.mul_self_sqrt (by norm_num)) sqrt_two_mem.1
    (Finset.sum_nonneg fun j _ => sq_nonneg (σ j)) hW hN hJ (sum_sum_mul_endKernel_le hr σ)

/-! ### A packet and its dilate as two wells -/

/-- The packet `σ` on the lower end `(2r, 3r]` of the window `(2r, 6r]`. -/
def lowerEnd (r : ℕ) (σ : ℕ → ℝ) (i : Fin (2 * (2 * r))) : ℝ := twoEnds r σ (fun _ => 0) i

/-- The dilate by two of the packet `σ`: its refinement on the upper end `(4r, 6r]`. -/
def upperEnd (r : ℕ) (σ : ℕ → ℝ) (i : Fin (2 * (2 * r))) : ℝ := twoEnds r (fun _ => 0) σ i

theorem lowerEnd_nonneg {r : ℕ} {σ : ℕ → ℝ} (hσ : ∀ j, 0 ≤ σ j) (i : Fin (2 * (2 * r))) :
    0 ≤ lowerEnd r σ i := by
  simp only [lowerEnd, twoEnds, refineStep]
  split_ifs
  · exact hσ _
  · exact le_rfl
  · exact div_nonneg le_rfl (Real.sqrt_nonneg _)

theorem upperEnd_nonneg {r : ℕ} {σ : ℕ → ℝ} (hσ : ∀ j, 0 ≤ σ j) (i : Fin (2 * (2 * r))) :
    0 ≤ upperEnd r σ i := by
  simp only [upperEnd, twoEnds, refineStep]
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact div_nonneg (hσ _) (Real.sqrt_nonneg _)

/-- A packet and its dilate have no common block. -/
theorem lowerEnd_mul_upperEnd (r : ℕ) (σ : ℕ → ℝ) (i : Fin (2 * (2 * r))) :
    lowerEnd r σ i * upperEnd r σ i = 0 := by
  simp only [lowerEnd, upperEnd, twoEnds, refineStep]
  split_ifs
  · exact mul_zero _
  · exact mul_zero _
  · rw [zero_div, zero_mul]

/-- The neutral part of the window `(2r, 6r]` on a step packet, as a sum over the blocks. -/
theorem bilin_neutralWindow_coe (Q r : ℕ) (z : ℕ → ℝ) :
    bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (fun i => z i) (fun i => z i) =
      ∑ i ∈ range (2 * (2 * r)), ∑ l ∈ range (2 * (2 * r)),
        z i * z l * neutralBlock Q (2 * r + i) (2 * r + l) :=
  sum_fin_windowMatrix_coe (neutralBlock Q) (2 * r) (2 * (2 * r)) z

/-- The neutral part on the packet of the lower end. -/
theorem bilin_neutralWindow_lowerEnd {r Q : ℕ} (hr : 1 ≤ r) (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (lowerEnd r σ) (lowerEnd r σ) =
      ∑ j ∈ range r, ∑ l ∈ range r, σ j * σ l * neutralBlock Q (2 * r + j) (2 * r + l) := by
  refine (bilin_neutralWindow_coe Q r (twoEnds r σ fun _ => 0)).trans ?_
  rw [sum_neutralBlock_twoEnds hr hQ σ fun _ => 0]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, sub_zero]

/-- **The dilate has the depth of the packet.** -/
theorem bilin_neutralWindow_upperEnd {r Q : ℕ} (hr : 1 ≤ r) (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (upperEnd r σ) (upperEnd r σ) =
      bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (lowerEnd r σ) (lowerEnd r σ) := by
  rw [bilin_neutralWindow_lowerEnd hr hQ σ]
  refine (bilin_neutralWindow_coe Q r (twoEnds r (fun _ => 0) σ)).trans ?_
  rw [sum_neutralBlock_twoEnds hr hQ (fun _ => 0) σ]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero]

/-- The packet minus its dilate is the odd packet of the two ends. -/
theorem twoEnds_neg (r : ℕ) (σ : ℕ → ℝ) (i : ℕ) :
    twoEnds r σ (fun j => -σ j) i =
      1 * twoEnds r σ (fun _ => 0) i + -1 * twoEnds r (fun _ => 0) σ i := by
  simp only [twoEnds, refineStep]
  split_ifs <;> ring

/-- **The coupling of a packet and its dilate exceeds their depth**:
`N(x, y) ≤ N(x, x) − (1/60) Σ σ_j²` for `x = (σ, 0, 0)`, `y = (0, 0, U₂σ)`. -/
theorem bilin_neutralWindow_lowerEnd_upperEnd_le {r Q : ℕ} (hr : 1 ≤ r) (hQ : 2 ≤ Q)
    (σ : ℕ → ℝ) :
    bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (lowerEnd r σ) (upperEnd r σ) ≤
      bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (lowerEnd r σ) (lowerEnd r σ) -
        1 / 60 * ∑ j ∈ range r, σ j ^ 2 := by
  have hodd : 1 / 30 * ∑ j ∈ range r, σ j ^ 2 ≤
      bilin (neutralWindow Q (2 * r) (2 * (2 * r)))
        (fun i => 1 * lowerEnd r σ i + -1 * upperEnd r σ i)
        (fun i => 1 * lowerEnd r σ i + -1 * upperEnd r σ i) := by
    have hz : (fun i : Fin (2 * (2 * r)) => 1 * lowerEnd r σ i + -1 * upperEnd r σ i) =
        fun i : Fin (2 * (2 * r)) => twoEnds r σ (fun j => -σ j) i :=
      funext fun i => (twoEnds_neg r σ i).symm
    rw [hz]
    exact (sum_neutralBlock_twoEnds_ge hr hQ σ).trans_eq
      (bilin_neutralWindow_coe Q r (twoEnds r σ fun j => -σ j)).symm
  rw [bilin_comb, bilin_swap (neutralWindow_symm Q (2 * r) (2 * (2 * r))) (upperEnd r σ)
    (lowerEnd r σ), bilin_neutralWindow_upperEnd hr hQ σ] at hodd
  linarith

/-- **A packet and its dilate by two are bound.** In the count of the bound states of a window
by two wells that stay apart, the packet `σ` on `(2r, 3r]` and its dilate on `(4r, 6r]` are
never such a pair: `N(x, x) N(y, y) ≤ N(x, y)²` whenever `N(x, x) < 0`. -/
theorem not_unbound_lowerEnd_upperEnd {r Q : ℕ} (hr : 1 ≤ r) (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    ¬(bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (lowerEnd r σ) (lowerEnd r σ) < 0 ∧
      bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (lowerEnd r σ) (upperEnd r σ) ^ 2 <
        bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (lowerEnd r σ) (lowerEnd r σ) *
          bilin (neutralWindow Q (2 * r) (2 * (2 * r))) (upperEnd r σ) (upperEnd r σ)) := by
  rintro ⟨hx, hlt⟩
  rw [bilin_neutralWindow_upperEnd hr hQ σ] at hlt
  exact absurd (mul_self_le_sq_of_le_sub hx (Finset.sum_nonneg fun j _ => sq_nonneg (σ j))
    (bilin_neutralWindow_lowerEnd_upperEnd_le hr hQ σ)) (not_le.mpr hlt)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
