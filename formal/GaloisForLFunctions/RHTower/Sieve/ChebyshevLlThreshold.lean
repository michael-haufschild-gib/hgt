import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlWidth

/-!
# The eventual thresholds when the depth grows with the height

Every condition the assembly needs holds for all large `N`: the smoothing width is between one and
`N`, the balanced quantity at the cutoff `Z = N + H + 1` is at least `256` and at least twice
`log Z`, and the height clears any prescribed `L₀`.

The condition that carries the whole construction is `2 ≤ c·log log Z`, which is what makes the
depth `c·log log T` exceed the fixed depth used by de la Vallée Poussin's rectangle.  It is a
threshold on `log N`, not on `N`: `log N ≥ exp(2/c)`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **Every threshold holds eventually.** -/
theorem eventually_cheb_ll_conditions (c L₀ : ℝ) (hc0 : 0 < c) (hc : c ≤ 1) :
    ∀ᶠ N : ℝ in atTop,
      0 < N ∧ 1 ≤ Real.log N ∧ 1 ≤ chebWidthLl c N ∧ chebWidthLl c N ≤ N
        ∧ 0 < Real.log (N + chebWidthLl c N + 1)
        ∧ 256 ≤ chebQuadLl c (N + chebWidthLl c N + 1)
        ∧ 2 * Real.log (N + chebWidthLl c N + 1) ≤ chebQuadLl c (N + chebWidthLl c N + 1)
        ∧ 2 ≤ c * Real.log (Real.log (N + chebWidthLl c N + 1))
        ∧ L₀ ≤ Real.log (chebHeightLl c (N + chebWidthLl c N + 1)) := by
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop
      (max (max 128 (Real.exp (2 / c))) (L₀ ^ (2 : ℕ) / 2))] with N hN3 hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  have h128 : (128 : ℝ) ≤ Real.log N :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hlogN)
  have hexp : Real.exp (2 / c) ≤ Real.log N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hlogN)
  have hL₀ : L₀ ^ (2 : ℕ) / 2 ≤ Real.log N := le_trans (le_max_right _ _) hlogN
  have hN1 : (1 : ℝ) ≤ Real.log N := by linarith
  have hH1 : (1 : ℝ) ≤ chebWidthLl c N := one_le_chebWidthLl hc hN0 hN1
  have hHN : chebWidthLl c N ≤ N := chebWidthLl_le hN0.le
  set Z : ℝ := N + chebWidthLl c N + 1 with hZdef
  have hZ0 : (0 : ℝ) < Z := by rw [hZdef]; linarith
  have hNZ : N ≤ Z := by rw [hZdef]; linarith
  have hlogZ : Real.log N ≤ Real.log Z := Real.log_le_log hN0 hNZ
  have hlogZ0 : (0 : ℝ) < Real.log Z := by linarith
  -- the depth condition
  have hLLZ : 2 / c ≤ Real.log (Real.log Z) := by
    have h1 : Real.log (Real.exp (2 / c)) ≤ Real.log (Real.log Z) :=
      Real.log_le_log (Real.exp_pos _) (le_trans hexp hlogZ)
    rwa [Real.log_exp] at h1
  have hdepth : 2 ≤ c * Real.log (Real.log Z) := by
    rw [div_le_iff₀ hc0] at hLLZ
    linarith
  -- the balanced quantity
  have hQ2 : 2 * Real.log Z ≤ chebQuadLl c Z := by
    rw [chebQuadLl]
    nlinarith [hdepth, hlogZ0]
  have hQ256 : (256 : ℝ) ≤ chebQuadLl c Z := by linarith
  refine ⟨hN0, hN1, hH1, hHN, hlogZ0, hQ256, hQ2, hdepth, ?_⟩
  rw [chebHeightLl, Real.log_exp]
  have hsq : L₀ ^ (2 : ℕ) ≤ chebQuadLl c Z := by linarith
  have hroot : Real.sqrt (L₀ ^ (2 : ℕ)) ≤ Real.sqrt (chebQuadLl c Z) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at hroot
  linarith [le_abs_self L₀, hroot]

end RHTower.Sieve
