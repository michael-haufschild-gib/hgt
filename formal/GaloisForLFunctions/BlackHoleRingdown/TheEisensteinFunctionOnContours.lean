import GaloisForLFunctions.BlackHoleRingdown.ThePolynomialGrowthOfTheEisensteinFunction
import GaloisForLFunctions.BlackHoleRingdown.ThePulseAmplitude

/-!
# The Eisenstein function on the contours

The jets of `E(u; x, Y)` grow at most polynomially in `Im u` on the three kinds of contour that the shift
arguments use: horizontal segments at the good heights, vertical lines `Re u = c ≥ ½`, and vertical lines
`Re u = -A ≤ -1`. A rapid amplitude beats any such growth, uniformly on vertical strips.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-- A continuous function with an inverse-square tail is integrable. -/
theorem integrable_of_continuous_of_inv_sq_tail {f : ℝ → ℂ} (hf : Continuous f) {R C : ℝ}
    (h : ∀ x : ℝ, R ≤ |x| → ‖f x‖ ≤ C * ((1 + |x|) ^ 2)⁻¹) : Integrable f := by
  set R' := max R 0 with hR'
  have hR0 : 0 ≤ R' := le_max_right _ _
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R') (b := R')).exists_bound_of_continuousOn hf.continuousOn
  have hg := integrable_inv_one_add_abs_sq.const_mul (max M 0 * (1 + R') ^ 2 + max C 0)
  refine hg.mono' hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hp : 0 < (1 + |x|) ^ 2 := by positivity
  have hinv : 0 < ((1 + |x|) ^ 2)⁻¹ := inv_pos.mpr hp
  have hM0 := le_max_right M 0
  have hC0 := le_max_right C 0
  rcases le_or_gt |x| R' with hx | hx
  · have h1 : ‖f x‖ ≤ max M 0 := (hM x (abs_le.mp hx)).trans (le_max_left _ _)
    have h2 : (1 + |x|) ^ 2 ≤ (1 + R') ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : 1 ≤ (1 + R') ^ 2 * ((1 + |x|) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hp]
      exact h2
    calc ‖f x‖ ≤ max M 0 * 1 := by rw [mul_one]; exact h1
      _ ≤ max M 0 * ((1 + R') ^ 2 * ((1 + |x|) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h3 hM0
      _ ≤ (max M 0 * (1 + R') ^ 2 + max C 0) * ((1 + |x|) ^ 2)⁻¹ := by
          have : 0 ≤ max C 0 * ((1 + |x|) ^ 2)⁻¹ := by positivity
          nlinarith
  · have hx' : R ≤ |x| := (le_max_left R 0).trans hx.le
    refine (h x hx').trans ?_
    have h1 : C * ((1 + |x|) ^ 2)⁻¹ ≤ max C 0 * ((1 + |x|) ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hinv.le
    have : 0 ≤ max M 0 * (1 + R') ^ 2 * ((1 + |x|) ^ 2)⁻¹ := by positivity
    nlinarith

/-- The rotated amplitude on vertical strips. -/
theorem RapidAmplitude.exists_rotated_le {a : ℂ → ℂ} (ha : RapidAmplitude a) (B : ℝ) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, |u.re| ≤ B →
      ‖a (-I * u)‖ * (1 + |u.im|) ^ M ≤ C * ((1 + |u.im|) ^ 2)⁻¹ := by
  obtain ⟨C, hC, h⟩ := ha.exists_mul_poly_le B M
  refine ⟨C, hC, fun u hu => ?_⟩
  have hre : (-I * u).re = u.im := by simp
  have him : (-I * u).im = -u.re := by simp
  have := h (-I * u) (by rw [him, abs_neg]; exact hu)
  rwa [hre] at this

/-! ### Polynomial bounds on the contours -/

/-- The jets as a package. -/
def EisensteinJetsLE (K : ℝ) (u : ℂ) (x Y : ℝ) : Prop :=
  ‖normalizedEisenstein u x Y‖ ≤ K ∧ ‖eisensteinX u x Y‖ ≤ K ∧ ‖eisensteinXX u x Y‖ ≤ K ∧
    ‖eisensteinY u x Y‖ ≤ K ∧ ‖eisensteinYY u x Y‖ ≤ K

theorem EisensteinJetsLE.mono {K K' : ℝ} {u : ℂ} {x Y : ℝ} (h : EisensteinJetsLE K u x Y)
    (hK : K ≤ K') : EisensteinJetsLE K' u x Y := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨a.trans hK, b.trans hK, c.trans hK, d.trans hK, e.trans hK⟩

/-- The strip bound with a polynomial bound for `1/ζ(1+2u)` on a set of parameters. -/
theorem exists_jets_le_of_zeta {Y₀ A c : ℝ} (hY₀ : 0 < Y₀) (hA : 0 ≤ A) (hc : 0 ≤ c) {K : ℝ}
    {N : ℕ} (hK : 0 ≤ K) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ (u : ℂ) (x Y : ℝ), -A ≤ u.re → u.re ≤ c → 1 ≤ |u.im| →
      Y ∈ Icc (Y₀ / 2) (2 * Y₀) → ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ K * (1 + |u.im|) ^ N →
      EisensteinJetsLE (C * (1 + |u.im|) ^ M) u x Y := by
  obtain ⟨C₁, M₁, hC₁, hS⟩ := exists_eisenstein_strip_le hY₀ hA hc
  obtain ⟨C₂, N₂, hC₂, hX⟩ := exists_exp_mul_norm_inv_xi_le (1 + 2 * -A) (1 + 2 * c)
  refine ⟨C₁ * (1 + C₂ * K), M₁ + (N₂ + N), by positivity, fun u x Y h1 h2 h3 hY hz => ?_⟩
  have hsre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  have hxb := hX u (by rw [hsre]; linarith) (by rw [hsre]; linarith) h3
  have hweight : Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖ ≤
      C₂ * K * (1 + |u.im|) ^ (N₂ + N) := by
    refine hxb.trans ?_
    calc C₂ * (1 + |u.im|) ^ N₂ * ‖(riemannZeta (1 + 2 * u))⁻¹‖
        ≤ C₂ * (1 + |u.im|) ^ N₂ * (K * (1 + |u.im|) ^ N) :=
          mul_le_mul_of_nonneg_left hz (by positivity)
      _ = _ := by
          rw [pow_add]
          ring
  have hsw := stripWeight_le_of (M := M₁) hC₁ (by positivity) hweight
  obtain ⟨s0, s1, s2, s3, s4⟩ := hS u x Y h1 h2 h3 hY
  exact ⟨s0.trans hsw, s1.trans hsw, s2.trans hsw, s3.trans hsw, s4.trans hsw⟩

/-- **Good heights.** -/
theorem exists_jets_goodHeight {Y₀ A c : ℝ} (hY₀ : 0 < Y₀) (hA : 0 ≤ A) (hc : 0 ≤ c) :
    ∃ (C : ℝ) (M : ℕ) (k₀ : ℕ), 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ k → ∀ (u : ℂ) (x Y : ℝ), -A ≤ u.re → u.re ≤ c →
      |u.im| = goodHeight k / 2 → 1 ≤ |u.im| → Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      EisensteinJetsLE (C * (1 + |u.im|) ^ M) u x Y := by
  obtain ⟨C₃, N₃, k₀, hC₃, hz⟩ := exists_norm_inv_zeta_goodHeight (2 + 2 * A + 2 * c) (by linarith)
  obtain ⟨C, M, hC, h⟩ := exists_jets_le_of_zeta (K := C₃ * 2 ^ N₃) (N := N₃) hY₀ hA hc (by positivity)
  refine ⟨C, M, k₀, hC, fun k hk u x Y h1 h2 him h3 hY => h u x Y h1 h2 h3 hY ?_⟩
  have hsre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  have hsim : |(1 + 2 * u).im| = 2 * |u.im| := by
    have : (1 + 2 * u).im = 2 * u.im := by simp
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := hz k hk (1 + 2 * u) (by rw [hsre]; linarith) (by rw [hsre]; linarith)
    (by rw [hsim, him]; ring)
  rw [hsim] at hb
  refine hb.trans ?_
  have hT := abs_nonneg u.im
  have h1T : (1 + 2 * |u.im|) ^ N₃ ≤ 2 ^ N₃ * (1 + |u.im|) ^ N₃ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N₃
  calc C₃ * (1 + 2 * |u.im|) ^ N₃ ≤ C₃ * (2 ^ N₃ * (1 + |u.im|) ^ N₃) :=
        mul_le_mul_of_nonneg_left h1T hC₃
    _ = _ := by ring

/-- **Right lines.**  On `Re u = c ≥ ½`, where `1/ζ(1+2u)` is bounded. -/
theorem exists_jets_right_line {Y₀ c : ℝ} (hY₀ : 0 < Y₀) (hc : 1 / 2 ≤ c) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ (y x Y : ℝ), 1 ≤ |y| → Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      EisensteinJetsLE (C * (1 + |y|) ^ M) ((c : ℂ) + (y : ℂ) * I) x Y := by
  obtain ⟨C, M, hC, h⟩ := exists_jets_le_of_zeta (A := 0) (c := c) (K := 4) (N := 0) hY₀ le_rfl
    (by linarith) (by norm_num)
  refine ⟨C, M, hC, fun y x Y hy hY => ?_⟩
  have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
  have him : ((c : ℂ) + (y : ℂ) * I).im = y := by simp
  have hs : (1 + 2 * ((c : ℂ) + (y : ℂ) * I)).re = 1 + 2 * c := by simp
  have := h ((c : ℂ) + (y : ℂ) * I) x Y (by rw [hre]; linarith) (by rw [hre]) (by rw [him]; exact hy)
    hY (by
      rw [pow_zero, mul_one]
      exact norm_zeta_inv_le_of_two_le_re (by rw [hs]; linarith))
  rwa [him] at this

/-- **Left lines.**  On `Re u = -A ≤ -1`, where the functional equation bounds `1/ζ(1+2u)`. -/
theorem exists_jets_left_line {Y₀ A : ℝ} (hY₀ : 0 < Y₀) (hA : 1 ≤ A) :
    ∃ (C T₀ : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ (y x Y : ℝ), T₀ ≤ |y| → Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      EisensteinJetsLE (C * (1 + |y|) ^ M) (((-A : ℝ) : ℂ) + (y : ℂ) * I) x Y := by
  obtain ⟨C₃, T₃, N₃, hC₃, hz⟩ := exists_norm_zeta_inv_left_bound (2 * A)
  obtain ⟨C, M, hC, h⟩ := exists_jets_le_of_zeta (A := A) (c := 0) (K := C₃ * 2 ^ N₃) (N := N₃) hY₀
    (by linarith) le_rfl (by positivity)
  refine ⟨C, max 1 (T₃ / 2), M, hC, fun y x Y hy hY => ?_⟩
  have hy1 : 1 ≤ |y| := (le_max_left _ _).trans hy
  have hyT : T₃ ≤ 2 * |y| := by
    have := (le_max_right 1 (T₃ / 2)).trans hy
    linarith
  have hre : (((-A : ℝ) : ℂ) + (y : ℂ) * I).re = -A := by simp
  have him : (((-A : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
  have hline : (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)) =
      ((1 - 2 * A : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I := by
    push_cast
    ring
  have habs : |2 * y| = 2 * |y| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := hz (1 - 2 * A) (2 * y) (by linarith) (by linarith) (by rw [habs]; exact hyT)
  rw [← hline, habs] at hb
  have := h (((-A : ℝ) : ℂ) + (y : ℂ) * I) x Y (by rw [hre]) (by rw [hre]; linarith)
    (by rw [him]; exact hy1) hY (by
      rw [him]
      refine hb.trans ?_
      have hT := abs_nonneg y
      have h1T : (1 + 2 * |y|) ^ N₃ ≤ 2 ^ N₃ * (1 + |y|) ^ N₃ := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) N₃
      calc C₃ * (1 + 2 * |y|) ^ N₃ ≤ C₃ * (2 ^ N₃ * (1 + |y|) ^ N₃) :=
            mul_le_mul_of_nonneg_left h1T hC₃.le
        _ = _ := by ring)
  rwa [him] at this

end GaloisForLFunctions.BlackHoleRingdown

end
