import GaloisForLFunctions.RHTower.NearDiagonalPhaseCurvature
import GaloisForLFunctions.RHTower.Sieve.KthDerivativeTest
import GaloisForLFunctions.RHTower.Sieve.LogPhaseBlock

/-!
# Third derivative of the near-diagonal phase

This supplies the phase-specific input for the third-derivative test.  For

`F(u) = (T / (2π)) log (1 + r/u)`,

the third derivative of `-F` is positive and, on `M ≤ u ≤ 2M` with `r ≤ M`, is pinned to
`T r / M⁴` within an absolute ratio.
-/

namespace RHTower

noncomputable section

/-- The positive third derivative of the negated near-diagonal phase. -/
def nearDiagonalPhaseD3Abs (T r u : ℝ) : ℝ :=
  T * r * (3 * u ^ 2 + 3 * u * r + r ^ 2) /
    (Real.pi * u ^ 3 * (u + r) ^ 3)

theorem hasDerivAt_nearDiagonalPhaseD2 (T : ℝ) {r u : ℝ} (hr : 0 ≤ r) (hu : 0 < u) :
    HasDerivAt (nearDiagonalPhaseD2 T r) (-nearDiagonalPhaseD3Abs T r u) u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hune : u ≠ 0 := ne_of_gt hu
  have hurne : u + r ≠ 0 := by positivity
  have hlin : HasDerivAt (fun x : ℝ => 2 * x + r) 2 u := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id u).const_mul 2).add_const r
  have hnum := hlin.const_mul r
  have hq : HasDerivAt (fun x : ℝ => x * (x + r)) (1 * (u + r) + u * 1) u :=
    (hasDerivAt_id u).mul ((hasDerivAt_id u).add_const r)
  have hden := hq.mul hq
  have hqne : u * (u + r) ≠ 0 := mul_ne_zero hune hurne
  have hquot := hnum.div hden (mul_ne_zero hqne hqne)
  have hscaled := hquot.const_mul (T / (2 * Real.pi))
  refine (hscaled.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [] with x
    rw [nearDiagonalPhaseD2]
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [pow_two, pow_two]
    ring
  · rw [nearDiagonalPhaseD3Abs]
    simp only [Pi.mul_apply]
    field_simp
    ring

theorem nearDiagonalPhaseD3Abs_pos {T r u : ℝ} (hT : 0 < T) (hr : 0 < r) (hu : 0 < u) :
    0 < nearDiagonalPhaseD3Abs T r u := by
  rw [nearDiagonalPhaseD3Abs]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

/-- Dyadic third-derivative scale `T r / (72 π M⁴)`. -/
def nearDiagonalLambda3 (T r M : ℝ) : ℝ := T * r / (72 * Real.pi * M ^ 4)

theorem nearDiagonalLambda3_pos {T r M : ℝ} (hT : 0 < T) (hr : 0 < r) (hM : 0 < M) :
    0 < nearDiagonalLambda3 T r M := by
  rw [nearDiagonalLambda3]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

theorem nearDiagonalLambda3_le_D3Abs {T r M u : ℝ}
    (hT : 0 < T) (hr : 0 < r) (hM : 0 < M) (hrM : r ≤ M)
    (hu1 : M ≤ u) (hu2 : u ≤ 2 * M) :
    nearDiagonalLambda3 T r M ≤ nearDiagonalPhaseD3Abs T r u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hM hu1
  have hur0 : (0 : ℝ) < u + r := by linarith
  have hnum : 3 * M ^ 2 ≤ 3 * u ^ 2 + 3 * u * r + r ^ 2 := by nlinarith
  have hden : u ^ 3 * (u + r) ^ 3 ≤ 216 * M ^ 6 := by
    have hu3 : u ^ 3 ≤ (2 * M) ^ 3 := pow_le_pow_left₀ hu0.le hu2 3
    have hur3 : (u + r) ^ 3 ≤ (3 * M) ^ 3 :=
      pow_le_pow_left₀ hur0.le (by linarith) 3
    have := mul_le_mul hu3 hur3 (by positivity) (by positivity)
    calc
      u ^ 3 * (u + r) ^ 3 ≤ (2 * M) ^ 3 * (3 * M) ^ 3 := this
      _ = 216 * M ^ 6 := by ring
  have hcore : u ^ 3 * (u + r) ^ 3 ≤
      72 * M ^ 4 * (3 * u ^ 2 + 3 * u * r + r ^ 2) := by
    calc
      u ^ 3 * (u + r) ^ 3 ≤ 216 * M ^ 6 := hden
      _ = 72 * M ^ 4 * (3 * M ^ 2) := by ring
      _ ≤ 72 * M ^ 4 * (3 * u ^ 2 + 3 * u * r + r ^ 2) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
  rw [nearDiagonalLambda3, nearDiagonalPhaseD3Abs]
  rw [div_le_div_iff₀ (by positivity : 0 < 72 * Real.pi * M ^ 4)
    (by positivity : 0 < Real.pi * u ^ 3 * (u + r) ^ 3)]
  have hTr : 0 < T * r := mul_pos hT hr
  have hpihcore : Real.pi * u ^ 3 * (u + r) ^ 3 ≤
      Real.pi * (72 * M ^ 4 * (3 * u ^ 2 + 3 * u * r + r ^ 2)) := by
    calc
      Real.pi * u ^ 3 * (u + r) ^ 3 = Real.pi * (u ^ 3 * (u + r) ^ 3) := by ring
      _ ≤ Real.pi * (72 * M ^ 4 * (3 * u ^ 2 + 3 * u * r + r ^ 2)) :=
        mul_le_mul_of_nonneg_left hcore hpi.le
  calc
    T * r * (Real.pi * u ^ 3 * (u + r) ^ 3)
        ≤ T * r * (Real.pi * (72 * M ^ 4 *
            (3 * u ^ 2 + 3 * u * r + r ^ 2))) :=
      mul_le_mul_of_nonneg_left hpihcore hTr.le
    _ = T * r * (3 * u ^ 2 + 3 * u * r + r ^ 2) *
          (72 * Real.pi * M ^ 4) := by ring

theorem D3Abs_le_nearDiagonalLambda3 {T r M u : ℝ}
    (hT : 0 < T) (hr : 0 < r) (hM : 0 < M) (hrM : r ≤ M)
    (hu1 : M ≤ u) (hu2 : u ≤ 2 * M) :
    nearDiagonalPhaseD3Abs T r u ≤ 1368 * nearDiagonalLambda3 T r M := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hM hu1
  have hur0 : (0 : ℝ) < u + r := by linarith
  have hnum : 3 * u ^ 2 + 3 * u * r + r ^ 2 ≤ 19 * M ^ 2 := by nlinarith
  have hden : M ^ 6 ≤ u ^ 3 * (u + r) ^ 3 := by
    have hu3 : M ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hM.le hu1 3
    have hur3 : M ^ 3 ≤ (u + r) ^ 3 :=
      pow_le_pow_left₀ hM.le (by linarith) 3
    have := mul_le_mul hu3 hur3 (by positivity) (by positivity)
    calc
      M ^ 6 = M ^ 3 * M ^ 3 := by ring
      _ ≤ u ^ 3 * (u + r) ^ 3 := this
  have hcore : (3 * u ^ 2 + 3 * u * r + r ^ 2) * M ^ 4
      ≤ 19 * (u ^ 3 * (u + r) ^ 3) := by
    calc
      (3 * u ^ 2 + 3 * u * r + r ^ 2) * M ^ 4 ≤ 19 * M ^ 2 * M ^ 4 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = 19 * M ^ 6 := by ring
      _ ≤ 19 * (u ^ 3 * (u + r) ^ 3) := mul_le_mul_of_nonneg_left hden (by norm_num)
  rw [nearDiagonalPhaseD3Abs, nearDiagonalLambda3]
  have hrhs : 1368 * (T * r / (72 * Real.pi * M ^ 4)) =
      T * r * 19 / (Real.pi * M ^ 4) := by
    field_simp
    ring
  rw [hrhs]
  rw [div_le_div_iff₀ (by positivity : 0 < Real.pi * u ^ 3 * (u + r) ^ 3)
    (by positivity : 0 < Real.pi * M ^ 4)]
  have hTr : 0 < T * r := mul_pos hT hr
  calc
    T * r * (3 * u ^ 2 + 3 * u * r + r ^ 2) * (Real.pi * M ^ 4)
        = T * r * Real.pi * ((3 * u ^ 2 + 3 * u * r + r ^ 2) * M ^ 4) := by ring
    _ ≤ T * r * Real.pi * (19 * (u ^ 3 * (u + r) ^ 3)) :=
      mul_le_mul_of_nonneg_left hcore (mul_pos hTr hpi).le
    _ = T * r * 19 * (Real.pi * u ^ 3 * (u + r) ^ 3) := by ring

/-- Derivative chain for the negated near-diagonal phase through order three. -/
def nearDiagonalNegDerivativeChain (T r : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun u => -nearDiagonalPhase T r u
  | 1 => fun u => -nearDiagonalPhaseD1 T r u
  | 2 => fun u => -nearDiagonalPhaseD2 T r u
  | 3 => nearDiagonalPhaseD3Abs T r
  | _ => fun _ => 0

theorem nearDiagonalNegDerivativeChain_zero (T r : ℝ) :
    nearDiagonalNegDerivativeChain T r 0 = fun u => -nearDiagonalPhase T r u := rfl

theorem nearDiagonalNegDerivativeChain_hasDerivAt (T : ℝ) {r u : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (i : ℕ) (hi : i < 3) :
    HasDerivAt (nearDiagonalNegDerivativeChain T r i)
      (nearDiagonalNegDerivativeChain T r (i + 1) u) u := by
  interval_cases i
  · exact (hasDerivAt_nearDiagonalPhase T hr hu).neg
  · exact (hasDerivAt_nearDiagonalPhaseD1 T hr hu).neg
  · change HasDerivAt (-nearDiagonalPhaseD2 T r) (nearDiagonalPhaseD3Abs T r u) u
    simpa only [neg_neg] using (hasDerivAt_nearDiagonalPhaseD2 T hr hu).neg

/-- Third-derivative estimate for a unit-spaced dyadic block of the near-diagonal phase. -/
theorem norm_nearDiagonalBlock_third_le {T r M : ℝ}
    (hT : 0 < T) (hr : 0 < r) (hM : 0 < M) (hrM : r ≤ M)
    {N : ℕ} (hN : 1 ≤ N) (hspan : ((N : ℕ) - 1 : ℕ) ≤ M)
    (hlam1 : nearDiagonalLambda3 T r M ≤ 1) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * nearDiagonalPhase T r (M + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ 256 * ((N : ℝ) * (1368 ^ 2 * nearDiagonalLambda3 T r M) ^ (1 / 6 : ℝ)
          + (N : ℝ) ^ (1 / 2 : ℝ) * nearDiagonalLambda3 T r M ^ (-(1 / 4 : ℝ))) := by
  have hlam0 : 0 < nearDiagonalLambda3 T r M := nearDiagonalLambda3_pos hT hr hM
  have hmemsub : ∀ x ∈ Set.Icc M (M + (((N : ℕ) - 1 : ℕ) : ℝ)),
      M ≤ x ∧ x ≤ 2 * M := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have htest := RHTower.Sieve.kth_derivative_test 3 (by omega)
    (nearDiagonalNegDerivativeChain T r) M N hN hlam0 hlam1 (by norm_num : (1 : ℝ) ≤ 1368)
    (by
      intro i hi x hx
      exact nearDiagonalNegDerivativeChain_hasDerivAt T hr.le
        (lt_of_lt_of_le hM (hmemsub x hx).1) i hi)
    (by
      intro x hx
      simpa only [nearDiagonalNegDerivativeChain] using
        nearDiagonalLambda3_le_D3Abs hT hr hM hrM (hmemsub x hx).1 (hmemsub x hx).2)
    (by
      intro x hx
      simpa only [nearDiagonalNegDerivativeChain] using
        D3Abs_le_nearDiagonalLambda3 hT hr hM hrM (hmemsub x hx).1 (hmemsub x hx).2)
  rw [← RHTower.Sieve.norm_phase_sum_neg (nearDiagonalPhase T r) M N]
  simp only [nearDiagonalNegDerivativeChain] at htest
  convert htest using 1
  all_goals norm_num

end


end RHTower
