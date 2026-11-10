import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGluingIndexCountsTheZeros
import GaloisForLFunctions.SquareRootThreshold.ZetaZeroCountRemainderIsUnbounded

/-!
# The square misses the zeros by an unbounded remainder

The graph `Γ_{n+1}` carries `log(n + 1)` gluing conditions and owns the window of heights
`(T_n, T_{n+1}]`, `T_n = 2π(n + ½)`. Spread evenly over its window, the conditions give a count at
every real height: at `T = 2π(n + ½ + θ)`, `0 ≤ θ < 1`,

  `G(T) = log n! + θ·log(n + 1)`.

* **The count at every height** (`tendsto_gluingCount_sub_xiZeroCount_add_rvmRemainder`):
  `G(T) − N(T) + S(T) → ½ log 2π − 7/8` as `T → ∞`, with `N` the number of zeros below the height
  `T` and `S` the remainder of the zero count. The smooth count `x log x − x` is convex, so its
  increment over a part `θ` of a window lies between `θ log(n + ½)` and `θ log(n + 3/2)`
  (`mul_log_le_entropy_sub`), within `1/(n + ½)` of the share `θ log(n + 1)` of the conditions.
* **The miss is unbounded** (`exists_lt_abs_gluingCount_sub_xiZeroCount`): `S` is unbounded, so
  `G(T) − N(T)` leaves every bounded neighbourhood of its constant at arbitrarily large heights.
  The gluing conditions count the zeros in the mean and not at a height.
-/

open Filter Topology Real

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The index `n` of the window `[2π(n + ½), 2π(n + 3/2))` that contains the height `T`. -/
noncomputable def windowIndex (T : ℝ) : ℕ := ⌊T / (2 * π) - 1 / 2⌋₊

/-- The position `θ` of the height `T` in its window. -/
noncomputable def windowPhase (T : ℝ) : ℝ := T / (2 * π) - 1 / 2 - windowIndex T

/-- The gluing conditions below the height `T`: those of the first `n` graphs and the share `θ`
of the `log(n + 1)` conditions of `Γ_{n+1}`. -/
noncomputable def gluingCount (T : ℝ) : ℝ :=
  Real.log ((windowIndex T).factorial : ℝ) + windowPhase T * Real.log ((windowIndex T : ℝ) + 1)

theorem windowPhase_nonneg {T : ℝ} (hT : π ≤ T) : 0 ≤ windowPhase T := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hx : 0 ≤ T / (2 * π) - 1 / 2 := by
    rw [sub_nonneg, le_div_iff₀ h2π]
    linarith
  unfold windowPhase windowIndex
  linarith [Nat.floor_le hx]

theorem windowPhase_lt_one (T : ℝ) : windowPhase T < 1 := by
  unfold windowPhase windowIndex
  linarith [Nat.lt_floor_add_one (T / (2 * π) - 1 / 2)]

theorem tendsto_windowIndex : Tendsto windowIndex atTop atTop := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have h1 : Tendsto (fun T : ℝ => T / (2 * π) + -(1 / 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_div_const h2π)
  refine (tendsto_nat_floor_atTop.comp h1).congr fun T => ?_
  simp only [Function.comp_apply, windowIndex, sub_eq_add_neg]

/-- The increments of `y log y − y` lie between those of its tangents at the two ends. -/
theorem mul_log_le_entropy_sub {y θ : ℝ} (hy : 0 < y) (hθ : 0 ≤ θ) :
    θ * Real.log y ≤ ((y + θ) * Real.log (y + θ) - (y + θ)) - (y * Real.log y - y) ∧
      ((y + θ) * Real.log (y + θ) - (y + θ)) - (y * Real.log y - y) ≤ θ * Real.log (y + θ) := by
  have hyθ : 0 < y + θ := by linarith
  have hq : 0 < (y + θ) / y := div_pos hyθ hy
  have hlog : Real.log ((y + θ) / y) = Real.log (y + θ) - Real.log y :=
    Real.log_div hyθ.ne' hy.ne'
  have h1 := Real.one_sub_inv_le_log_of_pos hq
  have h2 := Real.log_le_sub_one_of_pos hq
  rw [hlog] at h1 h2
  have e1 : (y + θ) * (1 - ((y + θ) / y)⁻¹) = θ := by
    rw [inv_div]
    field_simp
    ring
  have e2 : y * ((y + θ) / y - 1) = θ := by
    field_simp
    ring
  have h1' := mul_le_mul_of_nonneg_left h1 hyθ.le
  have h2' := mul_le_mul_of_nonneg_left h2 hy.le
  rw [e1] at h1'
  rw [e2] at h2'
  constructor <;> linarith

/-- The share `θ log(n + 1)` of the conditions of `Γ_{n+1}` against the increment of the smooth
count over the part `θ` of its window. -/
theorem abs_share_sub_entropy_le (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    |θ * Real.log ((n : ℝ) + 1) -
        ((((n : ℝ) + 1 / 2 + θ) * Real.log ((n : ℝ) + 1 / 2 + θ) - ((n : ℝ) + 1 / 2 + θ)) -
          (((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1 / 2) - ((n : ℝ) + 1 / 2)))| ≤
      1 / ((n : ℝ) + 1 / 2) := by
  have hy : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hy3 : (0 : ℝ) < (n : ℝ) + 3 / 2 := by positivity
  obtain ⟨hlo, hhi⟩ := mul_log_le_entropy_sub hy hθ0
  have hl1 : Real.log ((n : ℝ) + 1 / 2) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hy (by linarith)
  have hl2 : Real.log ((n : ℝ) + 1 / 2 + θ) ≤ Real.log ((n : ℝ) + 3 / 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl3 : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 3 / 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl4 : Real.log ((n : ℝ) + 3 / 2) - Real.log ((n : ℝ) + 1 / 2) ≤ 1 / ((n : ℝ) + 1 / 2) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy3 hy)
    rw [Real.log_div hy3.ne' hy.ne'] at h
    have e : ((n : ℝ) + 3 / 2) / ((n : ℝ) + 1 / 2) - 1 = 1 / ((n : ℝ) + 1 / 2) := by
      field_simp
      ring
    linarith
  have m1 := mul_le_mul_of_nonneg_left hl1 hθ0
  have m2 := mul_le_mul_of_nonneg_left hl2 hθ0
  have m3 := mul_le_mul_of_nonneg_left hl3 hθ0
  have hD : θ * (Real.log ((n : ℝ) + 3 / 2) - Real.log ((n : ℝ) + 1 / 2)) ≤
      Real.log ((n : ℝ) + 3 / 2) - Real.log ((n : ℝ) + 1 / 2) :=
    mul_le_of_le_one_left (by linarith) hθ1
  rw [abs_le]
  constructor <;> linarith

/-- The smooth Riemann–von Mangoldt count at a positive height. -/
theorem routeKSmoothRVMCount_eq {T : ℝ} (hT : 0 < T) :
    RHTower.routeKSmoothRVMCount T =
      T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8 := by
  have h := routeKSmoothRVMCount_two_pi_mul (x := T / (2 * π)) (by positivity)
  have e : 2 * π * (T / (2 * π)) = T := by
    field_simp
  rwa [e] at h

/-- The count of the conditions minus the smooth count: the defect at the start of the window
plus the share against the increment. -/
theorem gluingCount_sub_smoothCount {T : ℝ} (hT : 0 < T) :
    gluingCount T - RHTower.routeKSmoothRVMCount T =
      (Real.log ((windowIndex T).factorial : ℝ) -
          RHTower.routeKSmoothRVMCount (2 * π * ((windowIndex T : ℝ) + 1 / 2))) +
        (windowPhase T * Real.log ((windowIndex T : ℝ) + 1) -
          ((((windowIndex T : ℝ) + 1 / 2 + windowPhase T) *
                Real.log ((windowIndex T : ℝ) + 1 / 2 + windowPhase T) -
              ((windowIndex T : ℝ) + 1 / 2 + windowPhase T)) -
            (((windowIndex T : ℝ) + 1 / 2) * Real.log ((windowIndex T : ℝ) + 1 / 2) -
              ((windowIndex T : ℝ) + 1 / 2)))) := by
  have hx : T / (2 * π) = (windowIndex T : ℝ) + 1 / 2 + windowPhase T := by
    unfold windowPhase
    ring
  rw [routeKSmoothRVMCount_eq hT, routeKSmoothRVMCount_two_pi_mul (by positivity), hx,
    gluingCount]
  ring

theorem tendsto_gluingCount_sub_smoothCount :
    Tendsto (fun T : ℝ => gluingCount T - RHTower.routeKSmoothRVMCount T) atTop
      (𝓝 (Real.log (2 * π) / 2 - 7 / 8)) := by
  have h1 := tendsto_log_factorial_sub_smoothCount.comp tendsto_windowIndex
  have hε : Tendsto (fun T : ℝ => 1 / ((windowIndex T : ℝ) + 1 / 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_windowIndex))
  have h2 : Tendsto (fun T : ℝ => windowPhase T * Real.log ((windowIndex T : ℝ) + 1) -
      ((((windowIndex T : ℝ) + 1 / 2 + windowPhase T) *
            Real.log ((windowIndex T : ℝ) + 1 / 2 + windowPhase T) -
          ((windowIndex T : ℝ) + 1 / 2 + windowPhase T)) -
        (((windowIndex T : ℝ) + 1 / 2) * Real.log ((windowIndex T : ℝ) + 1 / 2) -
          ((windowIndex T : ℝ) + 1 / 2)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hε
    filter_upwards [eventually_ge_atTop π] with T hT
    rw [Real.norm_eq_abs]
    exact abs_share_sub_entropy_le _ (windowPhase_nonneg hT) (windowPhase_lt_one T).le
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop π] with T hT
  simp only [Function.comp_apply]
  rw [gluingCount_sub_smoothCount (lt_of_lt_of_le Real.pi_pos hT)]

/-- **The gluing conditions count the zeros at every height up to the remainder.** With `S` the
remainder of the zero count, `G(T) − N(T) + S(T) → ½ log 2π − 7/8` as `T → ∞`. -/
theorem tendsto_gluingCount_sub_xiZeroCount_add_rvmRemainder :
    Tendsto (fun T : ℝ => gluingCount T - (RHTower.xiZeroCount T : ℝ) + RHTower.rvmRemainder T)
      atTop (𝓝 (Real.log (2 * π) / 2 - 7 / 8)) := by
  refine tendsto_gluingCount_sub_smoothCount.congr fun T => ?_
  unfold RHTower.rvmRemainder RHTower.zeroCountReal
  ring

/-- **The miss is unbounded.** At arbitrarily large heights the gluing conditions and the zeros
differ from their constant by more than any given bound. -/
theorem exists_lt_abs_gluingCount_sub_xiZeroCount (B T₀ : ℝ) :
    ∃ T, T₀ ≤ T ∧
      B < |gluingCount T - (RHTower.xiZeroCount T : ℝ) - (Real.log (2 * π) / 2 - 7 / 8)| := by
  have hev := tendsto_gluingCount_sub_xiZeroCount_add_rvmRemainder.eventually
    (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  obtain ⟨T, hT, hS⟩ := SquareRootThreshold.rvmRemainder_unbounded (B + 1) (max T₀ T₁)
  refine ⟨T, (le_max_left _ _).trans hT, ?_⟩
  have hb := hT₁ T ((le_max_right _ _).trans hT)
  rw [Real.dist_eq, abs_lt] at hb
  rcases lt_abs.mp hS with h | h
  · exact lt_abs.mpr (Or.inr (by linarith [hb.2]))
  · exact lt_abs.mpr (Or.inl (by linarith [hb.1]))

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
