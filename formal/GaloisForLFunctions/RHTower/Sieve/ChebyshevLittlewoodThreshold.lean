import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodWidth

/-!
# The eventual thresholds at depth `A`

Every condition the depth-`A` assembly needs holds for all large `N`: the smoothing width is at
least one and at most `N`, the cutoff `Z = N + H + 1` satisfies `16 ≤ A log Z` and `A ≤ log Z`, and
the height `chebHeightLw A Z` clears any prescribed `L₀`.

The only difference from the exponent-one thresholds is that the conditions are on `A log N` rather
than on `log N`, so the threshold grows with `A` — which is what makes a depth that itself grows
with `N` a genuine constraint rather than a free parameter.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **Every depth-`A` threshold holds eventually.** -/
theorem eventually_cheb_littlewood_conditions (A L₀ : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℝ in atTop,
      0 < N ∧ 1 ≤ chebWidthLw A N ∧ chebWidthLw A N ≤ N
        ∧ 16 ≤ A * Real.log (N + chebWidthLw A N + 1)
        ∧ 16 * A ≤ Real.log (N + chebWidthLw A N + 1)
        ∧ L₀ ≤ Real.log (chebHeightLw A (N + chebWidthLw A N + 1)) := by
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop
      (max (max 16 (16 * A)) (max (16 / A) ((L₀ / 2) ^ 2 / A)))] with N hN3 hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  have h16 : (16 : ℝ) ≤ Real.log N :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hlogN)
  have hAlog16 : 16 * A ≤ Real.log N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hlogN)
  have hAlog : A ≤ Real.log N := by nlinarith [hAlog16, hA]
  have h16A : 16 / A ≤ Real.log N :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hlogN)
  have hLsq : (L₀ / 2) ^ 2 / A ≤ Real.log N :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hlogN)
  have hlog1 : (1 : ℝ) ≤ Real.log N := by linarith
  have hH1 : (1 : ℝ) ≤ chebWidthLw A N := one_le_chebWidthLw hAlog hN0 hlog1
  have hHN : chebWidthLw A N ≤ N := chebWidthLw_le hN0.le
  have hlogZ : Real.log N ≤ Real.log (N + chebWidthLw A N + 1) :=
    Real.log_le_log hN0 (by linarith)
  have h16Z : (16 : ℝ) ≤ A * Real.log (N + chebWidthLw A N + 1) := by
    rw [div_le_iff₀ hA] at h16A
    nlinarith [h16A, hlogZ, hA]
  have hAZ : 16 * A ≤ Real.log (N + chebWidthLw A N + 1) := by linarith
  refine ⟨hN0, hH1, hHN, h16Z, hAZ, ?_⟩
  rw [log_chebHeightLw]
  have hsq : (L₀ / 2) ^ 2 ≤ A * Real.log (N + chebWidthLw A N + 1) := by
    rw [div_le_iff₀ hA] at hLsq
    nlinarith [hLsq, hlogZ, hA]
  have hroot : Real.sqrt ((L₀ / 2) ^ 2)
      ≤ Real.sqrt (A * Real.log (N + chebWidthLw A N + 1)) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at hroot
  have habs : L₀ / 2 ≤ |L₀ / 2| := le_abs_self _
  linarith [hroot, habs]

/-- **The depth condition of the coefficient lemma, at the balanced height.**  `8A ≤ log T` is
`16A ≤ log Z`, since `log T = 2√(A log Z)`. -/
theorem eight_mul_le_log_chebHeightLw {A Z : ℝ} (hA : 0 < A) (h16 : 16 * A ≤ Real.log Z) :
    8 * A ≤ Real.log (chebHeightLw A Z) := by
  rw [log_chebHeightLw]
  have hAZ : (0 : ℝ) ≤ A * Real.log Z := by nlinarith
  have hs : Real.sqrt (A * Real.log Z) * Real.sqrt (A * Real.log Z) = A * Real.log Z :=
    Real.mul_self_sqrt hAZ
  have hnn : (0 : ℝ) ≤ Real.sqrt (A * Real.log Z) := Real.sqrt_nonneg _
  nlinarith [hs, hnn, hA, h16]

end RHTower.Sieve
