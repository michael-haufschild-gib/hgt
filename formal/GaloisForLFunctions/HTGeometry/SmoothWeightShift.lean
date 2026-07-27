import GaloisForLFunctions.HTGeometry.SmoothWeightInversion
import GaloisForLFunctions.HTGeometry.VerticalContourShift
import GaloisForLFunctions.HTGeometry.PolynomialDecayIntegrable

/-!
# Shifting the Perron contour

The vertical integral of `F(s) W(s)`, with `W` the Mellin transform of the smooth cutoff, is the
same on every line inside a strip on which `F` is holomorphic and polynomially bounded.

The cutoff's transform decays faster than any power of `|Im s|`, so it absorbs the polynomial
growth of `F` twice over: on the vertical edges the product is integrable, and on the horizontal
edges it tends to zero.  No hypothesis on `F` beyond holomorphy and a polynomial bound is needed —
in particular the growth exponent may be arbitrarily large.
-/

open MeasureTheory Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The Mellin transform of the cutoff is holomorphic on any strip inside `Re s > 0`. -/
theorem differentiableOn_mellin_smoothWeight_strip {N H : ℝ} (hH : 0 < H) {c d : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)))
      (verticalStrip c d) := fun _s hs =>
  (differentiableAt_mellin_smoothWeight hH (lt_of_lt_of_le hc hs.1)).differentiableWithinAt

/-- A line inside the strip stays inside the strip. -/
theorem line_mem_verticalStrip {c d σ : ℝ} (h1 : c ≤ σ) (h2 : σ ≤ d) (y : ℝ) :
    ((σ : ℂ) + (y : ℝ) * I) ∈ verticalStrip c d := by
  constructor <;> simpa using by assumption

/-- **Integrability on a vertical edge.**  A polynomially bounded holomorphic factor times the
cutoff's transform is integrable on every line of the strip. -/
theorem integrable_mul_mellin_smoothWeight_line {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {F : ℂ → ℂ}
    {c d : ℝ} (hc : 0 < c) (hFcont : ContinuousOn F (verticalStrip c d)) {K A : ℝ} (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hFbd : ∀ s ∈ verticalStrip c d, ‖F s‖ ≤ K * (2 + |s.im|) ^ A) {σ : ℝ}
    (h1 : c ≤ σ) (h2 : σ ≤ d) :
    Integrable fun y : ℝ => F ((σ : ℂ) + (y : ℝ) * I) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) := by
  have hσ : 0 < σ := lt_of_lt_of_le hc h1
  obtain ⟨m, hm⟩ : ∃ m : ℕ, A + 1 < 2 * (m : ℝ) := by
    refine ⟨⌈A⌉₊ + 1, ?_⟩
    have h := Nat.le_ceil A
    push_cast
    linarith
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight_line_pow hN hH hσ m
  have hmem : ∀ y : ℝ, ((σ : ℂ) + (y : ℝ) * I) ∈ verticalStrip c d :=
    line_mem_verticalStrip h1 h2
  have hFline : Continuous fun y : ℝ => F ((σ : ℂ) + (y : ℝ) * I) :=
    hFcont.comp_continuous (by fun_prop) hmem
  have hcont : Continuous fun y : ℝ => F ((σ : ℂ) + (y : ℝ) * I) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) :=
    hFline.mul (continuous_mellin_smoothWeight_line hH hσ)
  refine Integrable.mono' ((integrable_rpow_mul_inv_pow hA hm).const_mul (K * C))
    hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have hFy : ‖F ((σ : ℂ) + (y : ℝ) * I)‖ ≤ K * (2 + |y|) ^ A := by
    have h := hFbd _ (hmem y)
    simpa using h
  rw [norm_mul]
  calc ‖F ((σ : ℂ) + (y : ℝ) * I)‖ *
        ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I)‖
      ≤ (K * (2 + |y|) ^ A) * (C * ((1 + y ^ 2) ^ m)⁻¹) :=
        mul_le_mul hFy (hbd y) (norm_nonneg _) (by positivity)
    _ = K * C * ((2 + |y|) ^ A * ((1 + y ^ 2) ^ m)⁻¹) := by ring

/-- **Vanishing of the horizontal edges.**  The cutoff's transform decays faster than any power of
the height, so the segment integrals of `F W` tend to zero. -/
theorem tendsto_horizontal_mul_mellin_smoothWeight {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {F : ℂ → ℂ}
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hFbd : ∀ s ∈ verticalStrip c d, ‖F s‖ ≤ K * (2 + |s.im|) ^ A) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u in c..d, F ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  set j : ℕ := ⌈A⌉₊ with hj
  have hjA : A < (j : ℝ) + 1 := by
    rw [hj]
    have := Nat.le_ceil A
    linarith
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight_horizontal hN hH j d
  have h0 : (0 : ℝ) < ((j : ℝ) + 1) - A := by linarith
  have hMtend : Tendsto (fun T : ℝ => K * 2 ^ A * C * T ^ (A - ((j : ℝ) + 1))) atTop (𝓝 0) := by
    have hlim := (tendsto_rpow_neg_atTop h0).const_mul (K * 2 ^ A * C)
    rw [mul_zero] at hlim
    have hexp : -(((j : ℝ) + 1) - A) = A - ((j : ℝ) + 1) := by ring
    rw [hexp] at hlim
    exact hlim
  refine tendsto_intervalIntegral_of_tendsto_bound
    (G := fun s : ℂ => F s * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s)
    (M := fun T : ℝ => K * 2 ^ A * C * T ^ (A - ((j : ℝ) + 1))) (hgt := fun T : ℝ => ε * T)
    ?_ hMtend
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT u hu
  have hT0 : (0 : ℝ) < T := by linarith
  rw [uIoc_of_le hcd] at hu
  have hu0 : 0 < u := lt_trans hc hu.1
  have hre : ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I).re = u := by simp
  have him : ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I).im = ε * T := by simp
  have habs : |ε * T| = T := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos hT0]
  have hmem : ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I) ∈ verticalStrip c d :=
    ⟨by rw [hre]; exact le_of_lt hu.1, by rw [hre]; exact hu.2⟩
  have hFy : ‖F ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ ≤ K * (2 + T) ^ A := by
    have h := hFbd _ hmem
    rwa [him, habs] at h
  have hWy : ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
      ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ ≤ C * (T ^ ((j : ℝ) + 1))⁻¹ := by
    have h := hbd _ (by rw [hre]; exact hu0) (by rw [hre]; exact hu.2)
    rw [him, habs] at h
    have hpow : (T : ℝ) ^ (j + 1) = T ^ ((j : ℝ) + 1) := by
      rw [← Real.rpow_natCast T (j + 1)]
      push_cast
      ring_nf
    rw [hpow] at h
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith [h]
  have hgrow : (2 + T) ^ A ≤ 2 ^ A * T ^ A := by
    have hle : 2 + T ≤ 2 * T := by linarith
    calc (2 + T) ^ A ≤ (2 * T) ^ A := Real.rpow_le_rpow (by positivity) hle hA
      _ = 2 ^ A * T ^ A := Real.mul_rpow (by norm_num) hT0.le
  have hcombine : T ^ A * (T ^ ((j : ℝ) + 1))⁻¹ = T ^ (A - ((j : ℝ) + 1)) := by
    rw [← Real.rpow_neg hT0.le, ← Real.rpow_add hT0]
    ring_nf
  rw [norm_mul]
  calc ‖F ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ *
        ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (K * (2 + T) ^ A) * (C * (T ^ ((j : ℝ) + 1))⁻¹) :=
        mul_le_mul hFy hWy (norm_nonneg _) (by positivity)
    _ ≤ (K * (2 ^ A * T ^ A)) * (C * (T ^ ((j : ℝ) + 1))⁻¹) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrow hK) (by positivity)
    _ = K * 2 ^ A * C * (T ^ A * (T ^ ((j : ℝ) + 1))⁻¹) := by ring
    _ = K * 2 ^ A * C * T ^ (A - ((j : ℝ) + 1)) := by rw [hcombine]

/-- **The Perron contour shift.**  If `F` is holomorphic and polynomially bounded on the strip
`c ≤ Re s ≤ d` with `c > 0`, then the vertical integral of `F W` is the same on both edges. -/
theorem integral_mul_mellin_smoothWeight_shift {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {F : ℂ → ℂ}
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hFdiff : DifferentiableOn ℂ F (verticalStrip c d))
    {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hFbd : ∀ s ∈ verticalStrip c d, ‖F s‖ ≤ K * (2 + |s.im|) ^ A) :
    (∫ y : ℝ, F ((d : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * I))
      = ∫ y : ℝ, F ((c : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * I) := by
  refine integral_vertical_line_eq_of_horizontal_tendsto hcd
    (hFdiff.mul (differentiableOn_mellin_smoothWeight_strip hH hc))
    (integrable_mul_mellin_smoothWeight_line hN hH hc hFdiff.continuousOn hK hA hFbd le_rfl hcd)
    (integrable_mul_mellin_smoothWeight_line hN hH hc hFdiff.continuousOn hK hA hFbd hcd le_rfl)
    ?_ ?_
  · have h := tendsto_horizontal_mul_mellin_smoothWeight hN hH hc hcd hK hA hFbd (-1) (Or.inr rfl)
    simpa only [neg_one_mul] using h
  · have h := tendsto_horizontal_mul_mellin_smoothWeight hN hH hc hcd hK hA hFbd 1 (Or.inl rfl)
    simpa only [one_mul] using h

end GaloisForLFunctions.HTGeometry
