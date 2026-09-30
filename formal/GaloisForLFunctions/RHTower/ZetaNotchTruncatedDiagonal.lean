import GaloisForLFunctions.RHTower.ZetaNotchTwistedDiagonal

/-!
# The truncated diagonal law of the windowed twisted moment

The diagonal of the windowed twisted moment is
`𝒟_L(N) = ω̂(0) Σ_j j^{−1} V(Nj²/L) + ∫ ω(t) Σ_j j^{−1} W_t(Nj²L) dt`
(`diagMain`). Each harmonic sum is `½ log(X/N) + O(1)` when `N ≤ X`, and `O(X/N)` when `N > X`.
Hence, with `½ log⁺ x = max(½ log x, 0)` (`halfLogPos`),

`‖𝒟_L(N) − T_L(N)‖ ≤ 2L C`,   `T_L(N) = ω̂(0) ½ log⁺(L/N) + ∫ ω(t) ½ log⁺(t²/(LN)) dt`,

uniformly in `N > 0` (`exists_norm_diagMain_sub_truncMain_le`). The logarithm of `N` is part of
the main term `T_L`, not of the error:
- `T_L(N) = ∫ ω log t − ω̂(0) log N` for `N ≤ L/4` (`truncMain_eq_of_le`);
- `‖T_L(N)‖ ≤ 4L · ½ log⁺(25L/(4N))` for every `N > 0` (`norm_truncMain_le`).
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-- `½ log⁺ x = max(½ log x, 0)`. -/
def halfLogPos (x : ℝ) : ℝ := max (Real.log x / 2) 0

theorem halfLogPos_nonneg (x : ℝ) : 0 ≤ halfLogPos x := le_max_right _ _

theorem halfLogPos_of_one_le {x : ℝ} (hx : 1 ≤ x) : halfLogPos x = Real.log x / 2 :=
  max_eq_left (by have := Real.log_nonneg hx; linarith)

theorem halfLogPos_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : halfLogPos x = 0 :=
  max_eq_right (by have := Real.log_nonpos hx0 hx; linarith)

theorem halfLogPos_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : halfLogPos x ≤ halfLogPos y :=
  max_le_max (by have := Real.log_le_log hx hxy; linarith) le_rfl

theorem continuousOn_halfLogPos_window {L N : ℝ} (hL : 0 < L) (hN : 0 < N) :
    ContinuousOn (fun t : ℝ => (halfLogPos (t ^ 2 / L / N) : ℂ)) (Icc (L / 2) (5 * L / 2)) := by
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  unfold halfLogPos
  refine (continuous_id.max continuous_const).comp_continuousOn (g := fun x : ℝ => max x 0) ?_
  refine ContinuousOn.div_const ?_ 2
  refine Real.continuousOn_log.comp (by fun_prop) fun t ht => ?_
  simp only [mem_compl_iff, mem_singleton_iff]
  have ht0 : 0 < t := by linarith [ht.1]
  positivity

/-- A harmonic sum against its truncated main term, in both regimes. -/
theorem norm_sub_halfLogPos_le {x : ℂ} {X N C₁ C₂ : ℝ} (hX : 0 ≤ X) (hN : 0 < N) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (h1 : N ≤ X → ‖x - ((Real.log (X / N) / 2 : ℝ) : ℂ)‖ ≤ C₁)
    (h2 : ‖x‖ ≤ C₂ * (X / N)) :
    ‖x - (halfLogPos (X / N) : ℂ)‖ ≤ C₁ + C₂ := by
  rcases le_or_gt N X with hNX | hNX
  · have hX1 : 1 ≤ X / N := (one_le_div hN).mpr hNX
    rw [halfLogPos_of_one_le hX1]
    linarith [h1 hNX]
  · have hXN : X / N < 1 := (div_lt_one hN).mpr hNX
    rw [halfLogPos_of_le_one (div_nonneg hX hN.le) hXN.le, Complex.ofReal_zero, sub_zero]
    calc ‖x‖ ≤ C₂ * (X / N) := h2
      _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left hXN.le hC₂
      _ ≤ C₁ + C₂ := by linarith

/-- The truncated diagonal main term `T_L(N)`. -/
def truncMain (L N : ℝ) : ℂ :=
  windowHat L 0 * (halfLogPos (L / N) : ℂ) +
    ∫ t, notchWindow L t * (halfLogPos (t ^ 2 / L / N) : ℂ)

/-- **The truncated diagonal law**: `‖𝒟_L(N) − T_L(N)‖ ≤ 2L C` for every `N > 0`. -/
theorem exists_norm_diagMain_sub_truncMain_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L N : ℝ}, 16 ≤ L → 0 < N →
      ‖diagMain L N - truncMain L N‖ ≤ 2 * L * C := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_directDiag_sub_le
  obtain ⟨C₂, hC₂, h₂⟩ := direct_diagSum_le
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_dualDiag_sub_le
  obtain ⟨C₄, hC₄, h₄⟩ := dual_diagSum_le
  refine ⟨(C₁ + C₂) + (C₃ + C₄), by positivity, fun {L N} hL hN => ?_⟩
  have hL0 : 0 < L := by linarith
  set D : ℂ := diagSum smoothAFECutoff N L with hD
  have hDb : ‖D - (halfLogPos (L / N) : ℂ)‖ ≤ C₁ + C₂ :=
    norm_sub_halfLogPos_le hL0.le hN hC₁ hC₂ (fun hNL => h₁ hN hNL) (h₂ hN hL0)
  have hDs : ∀ t ∈ Icc (L / 2) (5 * L / 2),
      ‖dualDiagAt L N t - (halfLogPos (t ^ 2 / L / N) : ℂ)‖ ≤ C₃ + C₄ := by
    intro t ht
    have ht1 : 1 ≤ t := by linarith [ht.1]
    rw [dualDiagAt_eq_diagSum hL0 (by linarith)]
    exact norm_sub_halfLogPos_le (by positivity) hN hC₃ hC₄ (fun hNX => h₃ ht1 hL0 hN hNX)
      (h₄ ht1 hL0 hN)
  have i1 : Integrable (fun t => notchWindow L t * dualDiagAt L N t) :=
    integrable_notchWindow_mul_of_continuousOn hL0 (continuousOn_dualDiagAt (by linarith) hN)
  have i2 : Integrable (fun t => notchWindow L t * (halfLogPos (t ^ 2 / L / N) : ℂ)) :=
    integrable_notchWindow_mul_of_continuousOn hL0 (continuousOn_halfLogPos_window hL0 hN)
  have hsplit : diagMain L N - truncMain L N =
      windowHat L 0 * (D - (halfLogPos (L / N) : ℂ)) +
        ∫ t, notchWindow L t * (dualDiagAt L N t - (halfLogPos (t ^ 2 / L / N) : ℂ)) := by
    unfold diagMain truncMain
    rw [← hD]
    have e : (fun t => notchWindow L t * (dualDiagAt L N t - (halfLogPos (t ^ 2 / L / N) : ℂ))) =
        fun t => notchWindow L t * dualDiagAt L N t -
          notchWindow L t * (halfLogPos (t ^ 2 / L / N) : ℂ) := by
      funext t; ring
    rw [e, integral_sub i1 i2]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hw := norm_windowHat_le hL0 0
  have hA : ‖windowHat L 0 * (D - (halfLogPos (L / N) : ℂ))‖ ≤ 2 * L * (C₁ + C₂) := by
    rw [norm_mul]
    exact mul_le_mul hw hDb (norm_nonneg _) (by positivity)
  have hB : ‖∫ t, notchWindow L t * (dualDiagAt L N t - (halfLogPos (t ^ 2 / L / N) : ℂ))‖ ≤
      2 * L * (C₃ + C₄) :=
    (norm_integral_le_integral_norm _).trans (integral_norm_notchWindow_mul_le hL0 hDs)
  linarith

/-- For `N ≤ L/4` the truncated main term is `∫ ω log t − ω̂(0) log N`. -/
theorem truncMain_eq_of_le {L N : ℝ} (hL : 0 < L) (hN : 0 < N) (hNL : N ≤ L / 4) :
    truncMain L N = logWindow L - windowHat L 0 * (Real.log N : ℂ) := by
  have h1 : halfLogPos (L / N) = (Real.log L - Real.log N) / 2 := by
    rw [halfLogPos_of_one_le ((one_le_div hN).mpr (by linarith)),
      Real.log_div hL.ne' hN.ne']
  have hpt : ∀ t, notchWindow L t * (halfLogPos (t ^ 2 / L / N) : ℂ) =
      notchWindow L t * ((Real.log t : ℂ) - ((Real.log L + Real.log N) / 2 : ℝ)) := by
    intro t
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · have ht0 : 0 < t := by linarith [ht.1]
      have hX : 1 ≤ t ^ 2 / L / N := by
        rw [le_div_iff₀ hN, le_div_iff₀ hL]
        nlinarith [ht.1]
      rw [halfLogPos_of_one_le hX, Real.log_div (by positivity) hN.ne',
        Real.log_div (by positivity) hL.ne', Real.log_pow]
      push_cast
      ring
    · rw [notchWindow_eq_zero hL ht, zero_mul, zero_mul]
  have i3 : Integrable (fun t => notchWindow L t * (Real.log t : ℂ)) :=
    integrable_notchWindow_mul_of_continuousOn hL
      ((Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        linarith [ht.1])))
  have i4 : Integrable (fun t => notchWindow L t * (((Real.log L + Real.log N) / 2 : ℝ) : ℂ)) :=
    integrable_notchWindow_mul_continuous hL continuous_const
  unfold truncMain
  rw [funext hpt]
  have e : (fun t => notchWindow L t * ((Real.log t : ℂ) - ((Real.log L + Real.log N) / 2 : ℝ))) =
      fun t => notchWindow L t * (Real.log t : ℂ) -
        notchWindow L t * (((Real.log L + Real.log N) / 2 : ℝ) : ℂ) := by
    funext t; ring
  rw [e, integral_sub i3 i4, integral_mul_const, ← windowHat_zero, h1]
  unfold logWindow
  push_cast
  ring

/-- `‖T_L(N)‖ ≤ 4L · ½ log⁺(25L/(4N))` for every `N > 0`. -/
theorem norm_truncMain_le {L N : ℝ} (hL : 0 < L) (hN : 0 < N) :
    ‖truncMain L N‖ ≤ 4 * L * halfLogPos (25 * L / (4 * N)) := by
  have hB := halfLogPos_nonneg (25 * L / (4 * N))
  have h1 : halfLogPos (L / N) ≤ halfLogPos (25 * L / (4 * N)) :=
    halfLogPos_mono (by positivity) (by
      rw [div_le_div_iff₀ hN (by positivity)]; nlinarith)
  have h2 : ∀ t ∈ Icc (L / 2) (5 * L / 2),
      ‖(halfLogPos (t ^ 2 / L / N) : ℂ)‖ ≤ halfLogPos (25 * L / (4 * N)) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (halfLogPos_nonneg _)]
    refine halfLogPos_mono (by positivity) ?_
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : t ^ 2 ≤ (5 * L / 2) ^ 2 := by nlinarith [ht.2]
    nlinarith
  unfold truncMain
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (halfLogPos_nonneg _)]
  have hA := mul_le_mul (norm_windowHat_le hL 0) h1 (halfLogPos_nonneg _) (by positivity)
  have hC := (norm_integral_le_integral_norm _).trans (integral_norm_notchWindow_mul_le hL h2)
  linarith

end RHTower.ZetaNotch
