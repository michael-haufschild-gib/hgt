import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheTateTwistIsTheShiftedPair
import GaloisForLFunctions.ArithmeticIncidencePositivity.ShiftedPairOddWindowSelectivity

/-!
# Short windows stay positive in small Tate dimension

On a window of length `A ≤ 3/5` Weil's form is coercive, `Q(H) ≥ ‖H‖²/5000` (LST), and the symmetric
Tate twist `Q^{(k)}` is negative on some test in every large dimension
(`exists_window_tateTwistedForm_neg`). This module shows that positivity survives a definite distance
into positive dimension.

* **The short-window comparison** (AIP `shiftedPairZeroForm_eq`): for tests supported in `[−r, r]`,
  `2r < log 2`, `Q^{(k)}(F) = Q(F) + 2∫_0^∞(cosh(kt) − 1)(2cosh(t/2) − ω(t))c_F(t) dt`.
* **The kernel is quadratically small** (`abs_kernel_le`): for `0 < t ≤ 1`, `0 ≤ k ≤ 1`,
  `|(cosh(kt) − 1)(2cosh(t/2) − ω(t))| ≤ 5k²`, from `ω(t) ≤ e^{3t/2}/(2t)` (`archLevyDensity_le`) and
  `cosh x − 1 ≤ (x²/2)e^{x²/2}` (`cosh_sub_one_le`).
* **Stability** (`tateTwistedForm_ge_of_window`): on a window of length `A ≤ 3/5`,
  `Q^{(k)}(H) ≥ (1/5000 − 10Ak²)‖H‖²` for `|k| ≤ 1`.
* **The critical Tate dimension of a short window is positive and finite**
  (`shortWindow_criticalTateDimension`): every window of length `0 < A ≤ 3/5` is positive in every
  symmetric dimension `|k| ≤ 1/200` and negative on some test in every large dimension.

Read through the shifted pair, a short window does not see zeros moved off the line by less than
`1/200` but sees every sufficiently deep shift: the depth a window tolerates is a definite invariant
between the two bounds. Dimension zero is an interior point of an interval of positive dimensions on
short windows; on long windows the interval shrinks with the doubly exponential window margins.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis
open ArithmeticCriticalityTheory _root_.RHTower

/-- `ω(t) ≤ e^{3t/2}/(2t)` for `t > 0`. -/
theorem archLevyDensity_le {t : ℝ} (ht : 0 < t) :
    archLevyDensity t ≤ Real.exp (3 * t / 2) / (2 * t) := by
  unfold archLevyDensity
  have he : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by rw [← Real.exp_add]; simp
  have h1 : (2 * t + 1) * Real.exp (-2 * t) ≤ 1 := by
    have := Real.add_one_le_exp (2 * t)
    nlinarith [Real.exp_pos (-2 * t)]
  have hpos : 0 < 2 * t * Real.exp (-2 * t) := by positivity
  have hden : 2 * t * Real.exp (-2 * t) ≤ 1 - Real.exp (-2 * t) := by nlinarith
  calc Real.exp (-t / 2) / (1 - Real.exp (-2 * t))
      ≤ Real.exp (-t / 2) / (2 * t * Real.exp (-2 * t)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hden
    _ = Real.exp (3 * t / 2) / (2 * t) := by
        rw [show 3 * t / 2 = -t / 2 - -2 * t by ring, Real.exp_sub]
        field_simp

/-- `cosh x − 1 ≤ (x²/2)e^{x²/2}`. -/
theorem cosh_sub_one_le (x : ℝ) : Real.cosh x - 1 ≤ x ^ 2 / 2 * Real.exp (x ^ 2 / 2) := by
  have h1 := Real.cosh_le_exp_half_sq x
  have he : Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) = 1 := by rw [← Real.exp_add]; simp
  have h2 := Real.add_one_le_exp (-(x ^ 2 / 2))
  have h3 := mul_nonneg (sub_nonneg.mpr h2) (Real.exp_pos (x ^ 2 / 2)).le
  nlinarith

/-- **The comparison kernel is quadratically small**: for `0 < t ≤ 1` and `0 ≤ k ≤ 1`,
`|(cosh(kt) − 1)(2cosh(t/2) − ω(t))| ≤ 5k²`. -/
theorem abs_kernel_le {k t : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |(Real.cosh (k * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t)| ≤ 5 * k ^ 2 := by
  have hX0 : 0 ≤ Real.cosh (k * t) - 1 := by linarith [Real.one_le_cosh (k * t)]
  have hkt : (k * t) ^ 2 ≤ 1 := by
    have h1 : k * t ≤ 1 := by nlinarith
    have h2 : 0 ≤ k * t := mul_nonneg hk0 ht0.le
    nlinarith
  have hX : Real.cosh (k * t) - 1 ≤ k ^ 2 * t ^ 2 / 2 * Real.exp (1 / 2) := by
    have hexp : Real.exp ((k * t) ^ 2 / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
    calc Real.cosh (k * t) - 1 ≤ (k * t) ^ 2 / 2 * Real.exp ((k * t) ^ 2 / 2) := cosh_sub_one_le _
      _ ≤ (k * t) ^ 2 / 2 * Real.exp (1 / 2) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hω0 : 0 ≤ archLevyDensity t := (archLevyDensity_pos ht0).le
  have hω := archLevyDensity_le ht0
  have hc0 : 0 ≤ Real.cosh (t / 2) := (Real.cosh_pos _).le
  have hc : Real.cosh (t / 2) ≤ Real.exp (1 / 2) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-(t / 2)) ≤ Real.exp (t / 2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (t / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hh : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hh' : Real.exp (1 / 2) * Real.exp (3 / 2) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he32 : Real.exp (3 * t / 2) ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr (by linarith)
  -- the archimedean part
  have hA : (Real.cosh (k * t) - 1) * archLevyDensity t ≤ k ^ 2 * (Real.exp 1 * Real.exp 1) / 4 := by
    calc (Real.cosh (k * t) - 1) * archLevyDensity t
        ≤ k ^ 2 * t ^ 2 / 2 * Real.exp (1 / 2) * (Real.exp (3 * t / 2) / (2 * t)) :=
          mul_le_mul hX hω hω0 (by positivity)
      _ = k ^ 2 * t * (Real.exp (1 / 2) * Real.exp (3 * t / 2)) / 4 := by field_simp; ring
      _ ≤ k ^ 2 * 1 * (Real.exp (1 / 2) * Real.exp (3 / 2)) / 4 := by gcongr
      _ = k ^ 2 * (Real.exp 1 * Real.exp 1) / 4 := by rw [hh']; ring
  -- the pole part
  have hP : (Real.cosh (k * t) - 1) * (2 * Real.cosh (t / 2)) ≤ k ^ 2 * Real.exp 1 := by
    calc (Real.cosh (k * t) - 1) * (2 * Real.cosh (t / 2))
        ≤ k ^ 2 * t ^ 2 / 2 * Real.exp (1 / 2) * (2 * Real.exp (1 / 2)) :=
          mul_le_mul hX (by linarith) (by positivity) (by positivity)
      _ = k ^ 2 * t ^ 2 * Real.exp 1 := by rw [← hh]; ring
      _ ≤ k ^ 2 * 1 * Real.exp 1 := by gcongr; nlinarith
      _ = _ := by ring
  have habs : |2 * Real.cosh (t / 2) - archLevyDensity t| ≤ 2 * Real.cosh (t / 2) + archLevyDensity t :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  rw [abs_mul, abs_of_nonneg hX0]
  calc (Real.cosh (k * t) - 1) * |2 * Real.cosh (t / 2) - archLevyDensity t|
      ≤ (Real.cosh (k * t) - 1) * (2 * Real.cosh (t / 2) + archLevyDensity t) :=
        mul_le_mul_of_nonneg_left habs hX0
    _ ≤ k ^ 2 * Real.exp 1 + k ^ 2 * (Real.exp 1 * Real.exp 1) / 4 := by nlinarith
    _ = k ^ 2 * (Real.exp 1 + Real.exp 1 * Real.exp 1 / 4) := by ring
    _ ≤ k ^ 2 * 5 := by
        have he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 :=
          mul_lt_mul'' he he he0.le he0.le
        exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg k)
    _ = 5 * k ^ 2 := by ring

/-- An autocorrelation is bounded by the energy: `|c_F(t)| ≤ ‖F‖²`. -/
theorem abs_autoCorr_le {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    |autoCorr F t| ≤ ∫ u, F u ^ 2 := by
  have h1 := WeilMarkovPole.integrable_sq hF hFc
  have h2 : Integrable fun u => F (u + t) ^ 2 := h1.comp_add_right t
  have h := abs_integral_mul_le h1 h2 (WeilMarkovPole.integrable_mul_shift hF hFc t)
  rwa [integral_add_right_eq_self (fun u => F u ^ 2) t,
    Real.mul_self_sqrt (integral_nonneg fun u => sq_nonneg _)] at h

/-- The autocorrelation of a test supported in `[−r, r]` vanishes beyond `2r`. -/
theorem autoCorr_eq_zero_of_lt {F : ℝ → ℝ} {r t : ℝ} (hsupp : ∀ x, r < |x| → F x = 0)
    (ht : 2 * r < t) : autoCorr F t = 0 := by
  rw [autoCorr]
  have hz : (fun x => F x * F (x + t)) = fun _ => (0 : ℝ) := by
    funext x
    by_cases hx : r < |x|
    · rw [hsupp x hx, zero_mul]
    · rw [hsupp (x + t) (by
        rw [not_lt] at hx
        have := neg_abs_le x
        have := abs_nonneg x
        rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  rw [hz, integral_zero]

/-- **Stability on symmetric supports**: for tests supported in `[−r, r]`, `r ≤ 3/10`, and
`0 ≤ k ≤ 1`, `Q^{(k)}(F) ≥ (1/5000 − 20rk²)‖F‖²`. -/
theorem tateTwistedForm_ge_of_support {F : ℝ → ℝ} {r k : ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, r < |x| → F x = 0) (hr0 : 0 ≤ r) (hr : r ≤ 3 / 10)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    (1 / 5000 - 20 * r * k ^ 2) * (∫ x, F x ^ 2) ≤ tateTwistedForm k F := by
  have hrlog : 2 * r < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨hint, heq⟩ := ArithmeticIncidencePositivity.shiftedPairZeroForm_eq hF hFc hsupp hr0 hrlog k
  have hmem : F ∈ realTests := ⟨hF, hFc⟩
  rw [tateTwistedForm_eq_half_shiftedPairZeroForm hmem, heq]
  have hts : tsupport F ⊆ Icc (-(3 / 10)) (3 / 10) := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    by_contra h
    exact hx (hsupp x (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith))
  have hcoer := LatticeSectionTheory.WindowJumpCounts.weilPair_ge_of_le_threeTenths hmem hts le_rfl
  rw [LatticeSectionTheory.WindowJumpCounts.weilPair_eq_fullZeroForm hmem] at hcoer
  set f : ℝ → ℝ := fun t => (Real.cosh (k * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
    autoCorr F t with hf
  have hzero : ∫ t in Ioi (2 * r), f t = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
      simp only [hf, autoCorr_eq_zero_of_lt hsupp ht, mul_zero]
  have hsplit : ∫ t in Ioi (0 : ℝ), f t = ∫ t in Ioc 0 (2 * r), f t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ 2 * r),
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi (by linarith))),
      hzero, add_zero]
  have hbound : |∫ t in Ioi (0 : ℝ), f t| ≤ 5 * k ^ 2 * (∫ x, F x ^ 2) * (2 * r) := by
    rw [hsplit]
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 (2 * r)) (f := f)
      (C := 5 * k ^ 2 * (∫ x, F x ^ 2)) measure_Ioc_lt_top fun t ht => by
        rw [Real.norm_eq_abs, hf]
        dsimp only
        rw [abs_mul]
        exact mul_le_mul (abs_kernel_le hk0 hk1 ht.1 (by linarith [ht.2]))
          (abs_autoCorr_le hF.continuous hFc t) (abs_nonneg _) (by positivity)
    rw [Real.norm_eq_abs] at h
    have hvol : volume.real (Ioc (0 : ℝ) (2 * r)) = 2 * r := by
      rw [Real.volume_real_Ioc, sub_zero, max_eq_left (by linarith)]
    rwa [hvol] at h
  have hlow := (abs_le.mp hbound).1
  have hF2 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  nlinarith

/-- **Stability on windows**: on a window of length `A ≤ 3/5`, `Q^{(k)}(H) ≥ (1/5000 − 10Ak²)‖H‖²`
for `0 ≤ k ≤ 1`. -/
theorem tateTwistedForm_ge_of_window {A k : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 3 / 5) (hk0 : 0 ≤ k)
    (hk1 : k ≤ 1) {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    (1 / 5000 - 10 * A * k ^ 2) * (∫ u, H u ^ 2) ≤ tateTwistedForm k H := by
  set F : ℝ → ℝ := fun u => H (u - A / 2) with hFdef
  have hFd : ContDiff ℝ 2 F := hH.contDiff.comp (contDiff_id.sub contDiff_const)
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) fun u hu =>
      hH.vanish _ fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  have hsupp : ∀ x, A / 2 < |x| → F x = 0 := fun x hx =>
    hH.vanish _ fun h => by
      rcases lt_abs.mp hx with h' | h'
      · linarith [h.2]
      · linarith [h.1]
  have h := tateTwistedForm_ge_of_support hFd hFc hsupp (by linarith) (by linarith) hk0 hk1
  have hn : (∫ x, F x ^ 2) = ∫ u, H u ^ 2 := integral_sub_right_eq_self (fun u => H u ^ 2) (A / 2)
  rw [hn, show tateTwistedForm k F = tateTwistedForm k H from tateTwistedForm_comp_sub k (A / 2)]
    at h
  linarith

/-- **The critical Tate dimension of a short window is positive and finite.** Every window of length
`0 < A ≤ 3/5` is positive in every symmetric Tate dimension `|k| ≤ 1/200`, and negative on some test in
every large dimension. -/
theorem shortWindow_criticalTateDimension {A : ℝ} (hA0 : 0 < A) (hA : A ≤ 3 / 5) :
    (∀ k : ℝ, |k| ≤ 1 / 200 → ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateTwistedForm k H) ∧
      ∃ k₀ : ℝ, ∀ k, k₀ ≤ k → ∃ H : ℝ → ℝ, IsWindowTest A H ∧ tateTwistedForm k H < 0 := by
  refine ⟨fun k hk H hH => ?_, exists_window_tateTwistedForm_neg hA0⟩
  have habs : |k| ≤ 1 := by linarith
  have h := tateTwistedForm_ge_of_window hA0.le hA (abs_nonneg k) habs hH
  have hsq : |k| ^ 2 ≤ (1 / 200) ^ 2 := pow_le_pow_left₀ (abs_nonneg k) hk 2
  have hcoef : 0 ≤ 1 / 5000 - 10 * A * |k| ^ 2 := by nlinarith
  have hH2 : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hk' : tateTwistedForm |k| H = tateTwistedForm k H := by
    rcases abs_choice k with h' | h'
    · rw [h']
    · rw [h', tateTwistedForm_neg]
  rw [hk'] at h
  nlinarith [mul_nonneg hcoef hH2]

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
