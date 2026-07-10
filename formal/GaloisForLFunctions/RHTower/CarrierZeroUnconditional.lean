/-
# Unconditional simple zeros of every finite completed carrier

The center-value supply needed by the phase-crossing theorem does not require a small-ball or
caustic argument.  A finite Dirichlet polynomial with nonzero diagonal second moment must exceed
every smaller fixed floor at cofinally many heights: otherwise its exact second-moment lower bound
contradicts the pointwise upper bound.  The global line derivative budget spreads such a center
floor to a short interval.  At sufficiently large height the archimedean winding crosses a
half-turn on that interval, producing a simple carrier zero and its local analytic peel.
-/
import GaloisForLFunctions.RHTower.CarrierPhaseCrossing

namespace RHTower

open Complex Real Metric MeasureTheory

noncomputable section

/-- A finite Dirichlet polynomial whose diagonal second moment exceeds `t₀²` crosses the floor
`t₀` in every interval of one fixed positive length, uniformly in the base height. -/
theorem dpoly_floor_syndetic_of_diagonal (a : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) {t₀ : ℝ} (ht₀0 : 0 ≤ t₀)
    (hdiag : t₀ ^ 2 < ∑ n ∈ s, (a n) ^ 2) :
    ∃ U > 0, ∀ T : ℝ, ∃ τ ∈ Set.Icc T (T + U), t₀ < ‖dpoly a s τ‖ := by
  let S : ℝ := ∑ n ∈ s, (a n) ^ 2
  let B : ℝ := ∑ m ∈ s, ∑ n ∈ s.erase m,
    2 * |a m * a n| / |Real.log n - Real.log m|
  let g : ℝ := S - t₀ ^ 2
  have hg0 : 0 < g := by simpa [g, S] using hdiag
  let U : ℝ := (|B| + 1) / g
  have hU0 : 0 < U := div_pos (by positivity) hg0
  refine ⟨U, hU0, fun T => ?_⟩
  by_contra hnot
  push Not at hnot
  have hpoint : ∀ τ ∈ Set.Icc T (T + U), ‖dpoly a s τ‖ ^ 2 ≤ t₀ ^ 2 := by
    intro τ hτ
    have hle : ‖dpoly a s τ‖ ≤ t₀ := hnot τ hτ
    nlinarith [norm_nonneg (dpoly a s τ)]
  have hcont : Continuous (fun τ : ℝ => ‖dpoly a s τ‖ ^ 2) :=
    (dpoly_continuous a s).norm.pow 2
  have hupper : (∫ τ in T..(T + U), ‖dpoly a s τ‖ ^ 2) ≤ U * t₀ ^ 2 := by
    calc
      (∫ τ in T..(T + U), ‖dpoly a s τ‖ ^ 2) ≤
          ∫ _ in T..(T + U), t₀ ^ 2 :=
        intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable T (T + U))
          intervalIntegrable_const hpoint
      _ = U * t₀ ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
  have hlower := secondMoment_lower_bound a s T U hs
  have hstrict : U * t₀ ^ 2 < U * S - B := by
    have hid : U * g = |B| + 1 := by
      dsimp [U]
      field_simp
    have hBabs : B ≤ |B| := le_abs_self B
    dsimp [g] at hid
    nlinarith
  dsimp [S, B] at hlower hstrict
  linarith

/-- A finite Dirichlet polynomial whose diagonal second moment exceeds `t₀²` takes values larger
than `t₀` at cofinally many heights. -/
theorem dpoly_floor_cofinal_of_diagonal (a : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) {t₀ : ℝ} (ht₀0 : 0 ≤ t₀)
    (hdiag : t₀ ^ 2 < ∑ n ∈ s, (a n) ^ 2) :
    ∀ M : ℝ, ∃ τ, M < τ ∧ t₀ < ‖dpoly a s τ‖ := by
  obtain ⟨U, hU0, hU⟩ := dpoly_floor_syndetic_of_diagonal a s hs ht₀0 hdiag
  intro M
  obtain ⟨τ, hτ, hfloor⟩ := hU (M + 1)
  exact ⟨τ, lt_of_lt_of_le (by linarith) hτ.1, hfloor⟩

/-- Every nonempty critical-line Dirichlet carrier crosses the fixed floor `1/2` in every
interval of one fixed length. -/
theorem dirichletPoly_half_floor_syndetic (N : ℕ) (hN : 1 ≤ N) :
    ∃ U > 0, ∀ T : ℝ, ∃ τ ∈ Set.Icc T (T + U),
      (1 / 2 : ℝ) < ‖dirichletPoly N (linePt τ)‖ := by
  let a : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))
  let s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1mem : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hsum : (1 : ℝ) ≤ ∑ n ∈ s, (a n) ^ 2 := by
    calc
      (1 : ℝ) = (a 1) ^ 2 := by simp [a]
      _ ≤ ∑ n ∈ s, (a n) ^ 2 :=
        Finset.single_le_sum (fun n _ => sq_nonneg (a n)) h1mem
  have hdiag : (1 / 2 : ℝ) ^ 2 < ∑ n ∈ s, (a n) ^ 2 := by nlinarith
  obtain ⟨U, hU0, hU⟩ :=
    dpoly_floor_syndetic_of_diagonal a s hs (t₀ := (1 / 2 : ℝ)) (by norm_num) hdiag
  refine ⟨U, hU0, fun T => ?_⟩
  obtain ⟨τ, hτ, hfloor⟩ := hU T
  refine ⟨τ, hτ, ?_⟩
  have heq := dirichletPoly_line_eq N τ
  change dirichletPoly N (linePt τ) =
    dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) τ at heq
  rw [heq]
  simpa [a, s] using hfloor

/-- Every nonempty critical-line Dirichlet carrier has the fixed floor `1/2` at cofinally many
heights. -/
theorem dirichletPoly_half_floor_cofinal (N : ℕ) (hN : 1 ≤ N) :
    ∀ M : ℝ, ∃ τ, M < τ ∧ (1 / 2 : ℝ) < ‖dirichletPoly N (linePt τ)‖ := by
  obtain ⟨U, hU0, hU⟩ := dirichletPoly_half_floor_syndetic N hN
  intro M
  obtain ⟨τ, hτ, hfloor⟩ := hU (M + 1)
  exact ⟨τ, lt_of_lt_of_le (by linarith) hτ.1, hfloor⟩

/-- **Unconditional bounded-gap finite-carrier centers.** At every finite depth `N ≥ 1`, there
is one fixed length `L` such that every sufficiently high interval of length `L` contains a simple
critical-line zero of `completedGN N`, together with its local zero-free analytic peel. -/
theorem completedGN_factorized_simple_zero_syndetic (N : ℕ) (hN : 1 ≤ N) :
    ∃ A > 0, ∃ L > 0, ∀ T : ℝ, A ≤ T → ∃ τ ∈ Set.Icc T (T + L), ∃ R h,
      0 < R ∧ completedGN N (linePt τ) = 0 ∧
      deriv (completedGN N) (linePt τ) ≠ 0 ∧
      AnalyticOnNhd ℂ h (ball (linePt τ) R) ∧
      (∀ z ∈ ball (linePt τ) R, h z ≠ 0) ∧
      ∀ z ∈ ball (linePt τ) R, completedGN N z = (z - linePt τ) * h z := by
  let B : ℝ := dirichletLineDerivativeBudget N
  have hB0 : 0 ≤ B := dirichletLineDerivativeBudget_nonneg N
  let r : ℝ := 1 / (8 * (B + 1))
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hBr : B * r < 1 / 4 := by
    dsimp [r]
    rw [show B * (1 / (8 * (B + 1))) = B / (8 * (B + 1)) by ring]
    rw [div_lt_iff₀ (show 0 < 8 * (B + 1) by positivity)]
    nlinarith
  obtain ⟨A, hA0, hA⟩ := exists_height_carrierNetPhaseRate_ge N
    (d := (1 / 4 : ℝ)) (q := Real.pi / (2 * r))
  obtain ⟨U, hU0, hU⟩ := dirichletPoly_half_floor_syndetic N hN
  refine ⟨A, hA0, U + 2 * r, by positivity, fun T hAT => ?_⟩
  obtain ⟨τc, hτc, hcenter⟩ := hU (T + r)
  have hTleft : T ≤ τc - r := by linarith [hτc.1]
  have hright : τc + r ≤ T + (U + 2 * r) := by linarith [hτc.2]
  have hAleft : A ≤ τc - r := le_trans hAT hTleft
  have hleft0 : 0 < τc - r := lt_of_lt_of_le hA0 hAleft
  have hinterval : ∀ τ ∈ Set.Icc (τc - r) (τc + r),
      (1 / 4 : ℝ) ≤ ‖dirichletPoly N (linePt τ)‖ := by
    intro τ hτ
    have hdist : |τc - τ| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [hτ.1, hτ.2]
    have hlip := norm_dirichletPoly_line_sub_le_budget N τc τ
    have hvar :
        ‖dirichletPoly N (linePt τc) - dirichletPoly N (linePt τ)‖ < 1 / 4 :=
      lt_of_le_of_lt hlip (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdist hB0) hBr)
    have hrev : ‖dirichletPoly N (linePt τc)‖ - ‖dirichletPoly N (linePt τ)‖ ≤
        ‖dirichletPoly N (linePt τc) - dirichletPoly N (linePt τ)‖ :=
      norm_sub_norm_le _ _
    linarith
  have hrate : Real.pi / (2 * r) ≤ carrierNetPhaseRate N (1 / 4) (τc - r) :=
    hA (τc - r) hAleft
  have htarget0 : 0 < Real.pi / (2 * r) := div_pos Real.pi_pos (by positivity)
  have hnet0 : 0 < carrierNetPhaseRate N (1 / 4) (τc - r) :=
    lt_of_lt_of_le htarget0 hrate
  have hadvance : Real.pi ≤
      ((τc + r) - (τc - r)) * carrierNetPhaseRate N (1 / 4) (τc - r) := by
    have hm := mul_le_mul_of_nonneg_left hrate (show 0 ≤ 2 * r by positivity)
    have hid : (2 * r) * (Real.pi / (2 * r)) = Real.pi := by field_simp
    nlinarith
  obtain ⟨τ, hτ, hzero, hsimple⟩ :=
    exists_simple_completedGN_zero_of_interval_floor N hleft0 (by linarith) (by norm_num)
      hinterval hnet0 hadvance
  obtain ⟨R, hR0, h, hhan, hh0, hfact⟩ :=
    completedGN_simple_zero_peel_ball N τ hzero hsimple
  exact ⟨τ, ⟨le_trans hTleft hτ.1, le_trans hτ.2 hright⟩,
    R, h, hR0, hzero, hsimple, hhan, hh0, hfact⟩

/-- **Unconditional finite-carrier center theorem.** At every finite depth `N ≥ 1`, the
completed carrier has cofinally many simple zeros on the critical line.  Every such zero carries
the exact local one-zero analytic factorization consumed by the pinned-window gates. -/
theorem completedGN_factorized_simple_zero_cofinal (N : ℕ) (hN : 1 ≤ N) :
    ∀ M : ℝ, ∃ τ R h,
      M < τ ∧ 0 < R ∧ completedGN N (linePt τ) = 0 ∧
      deriv (completedGN N) (linePt τ) ≠ 0 ∧
      AnalyticOnNhd ℂ h (ball (linePt τ) R) ∧
      (∀ z ∈ ball (linePt τ) R, h z ≠ 0) ∧
      ∀ z ∈ ball (linePt τ) R, completedGN N z = (z - linePt τ) * h z := by
  obtain ⟨A, hA0, L, hL0, hsyn⟩ := completedGN_factorized_simple_zero_syndetic N hN
  intro M
  let T : ℝ := max A (M + 1)
  have hAT : A ≤ T := le_max_left _ _
  obtain ⟨τ, hτ, R, h, hR0, hzero, hsimple, hhan, hh0, hfact⟩ := hsyn T hAT
  have hMτ : M < τ := lt_of_lt_of_le
    (lt_of_lt_of_le (by linarith) (le_max_right A (M + 1))) hτ.1
  exact ⟨τ, R, h, hMτ, hR0, hzero, hsimple, hhan, hh0, hfact⟩

end

end RHTower
