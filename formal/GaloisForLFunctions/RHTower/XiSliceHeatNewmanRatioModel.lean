import GaloisForLFunctions.RHTower.XiSliceHeatCoshSharpThreshold
import GaloisForLFunctions.RHTower.XiSliceHeatNewmanCosModelFlow

/-!
# The WD heat threshold is half the de Bruijn–Newman time in the dense model

The slice at height `0` of the dense single-defect model `F(z) = (z² + δ²) cos(Lz/2)` is

  `F(ix) F(−ix) = (δ² − x²)² (1 + cosh Lx)/2`        (`cosDefect_slice`, `cosSlice`).

Heat `λ` turns it into `cosSliceHeat`, with Taylor coefficients `cosSliceHeatCoeff` at `0`.

**Theorem** (`newmanRatio_cosDefect`).  For `0 < 2ε < δ` and all large `L`:
* at heat `(δ/2 + ε)/L` every Taylor coefficient of the heated slice is `≥ 0`;
* at heat `(δ/2 − ε)/L` some Taylor coefficient is negative;
* at de Bruijn–Newman time `δ/L` every zero of the flow `H_λ = e^{−λD²}F` is real;
* at time `(δ − ε)/L` the flow has a zero on the positive imaginary axis.

So at the defect ordinate the WD heat threshold is `∼ δ/(2L)` and the de Bruijn–Newman constant of the
model is `∼ δ/L`: their ratio tends to `½`.  For the isolated quadratic model `z² + a²` the ratio is `⅔`
(`quadModel_heatCoeff_nonneg_iff`, `quadModel_flow_realRooted_iff`): heat `λ` makes the slice
coefficients nonnegative iff `3λ ≥ a²`, while the flow `z² + a² − 2λ` is real-rooted iff `2λ ≥ a²`.

Proof.  The slice is half the cosh model plus the quartic `(δ² − x²)²/2`, which only touches the
orders `0, 2, 4`.  Detection uses the negative cosh coefficient of order `≥ 6`
(`exists_coshModelHeatCoeff_neg`).  For positivity the order `2` needs the cosh coefficient to beat
`2δ²`.  It is `e^{κL/2} c₂` with `2 c₂ L⁴ = L² R(κL, δL, 2) ≥ L²` (`one_le_coshModelScaledSign`), so
it is `≥ κ³L/96`.  The flow side is `cosDefectFlow_collision`.
-/

open MeasureTheory Filter Topology Complex

namespace RHTower.DeBruijn

noncomputable section

/-- The slice of the dense model at height `0`. -/
def cosSlice (δ L x : ℝ) : ℝ := (δ ^ 2 - x ^ 2) ^ 2 * (1 + Real.cosh (L * x)) / 2

/-- **The slice identity.**  `F(ix) F(−ix) = (δ² − x²)² (1 + cosh Lx)/2`. -/
theorem cosDefect_slice (δ L x : ℝ) :
    cosDefect δ L (I * x) * cosDefect δ L (-(I * x)) = ((cosSlice δ L x : ℝ) : ℂ) := by
  have hc : Complex.cos ((L : ℂ) * (I * x) / 2) = ((Real.cosh (L * x / 2) : ℝ) : ℂ) := by
    rw [show (L : ℂ) * (I * x) / 2 = ((L * x / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.cos_mul_I,
      Complex.ofReal_cosh]
  have hc' : Complex.cos ((L : ℂ) * -(I * x) / 2) = ((Real.cosh (L * x / 2) : ℝ) : ℂ) := by
    rw [show (L : ℂ) * -(I * x) / 2 = -((L : ℂ) * (I * x) / 2) by ring, Complex.cos_neg, hc]
  have hsq : Real.cosh (L * x / 2) ^ 2 = (1 + Real.cosh (L * x)) / 2 := by
    have h2 : Real.cosh (L * x) = Real.cosh (2 * (L * x / 2)) := by ring_nf
    rw [h2, Real.cosh_two_mul, Real.cosh_sq]
    ring
  unfold cosDefect cosSlice
  rw [hc, hc']
  have e1 : (I * (x : ℂ)) ^ 2 + (δ : ℂ) ^ 2 = ((δ ^ 2 - x ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have e2 : (-(I * (x : ℂ))) ^ 2 + (δ : ℂ) ^ 2 = ((δ ^ 2 - x ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [e1, e2]
  have : (δ ^ 2 - x ^ 2) * Real.cosh (L * x / 2) * ((δ ^ 2 - x ^ 2) * Real.cosh (L * x / 2))
      = (δ ^ 2 - x ^ 2) ^ 2 * (1 + Real.cosh (L * x)) / 2 := by
    rw [show (δ ^ 2 - x ^ 2) ^ 2 * (1 + Real.cosh (L * x)) / 2
      = (δ ^ 2 - x ^ 2) ^ 2 * ((1 + Real.cosh (L * x)) / 2) by ring, ← hsq]
    ring
  rw [← this]
  push_cast
  ring

/-- The heated slice: the Gaussian average with variance `λ`. -/
def cosSliceHeat (δ L lam x : ℝ) : ℝ := ∫ u : ℝ, gaussDensity (lam / 2) u * cosSlice δ L (x + u)

theorem integrable_gaussDensity_mul_coshModel {lam : ℝ} (hlam : 0 < lam) (δ L x : ℝ) :
    Integrable (fun u : ℝ => gaussDensity (lam / 2) u * coshModel δ L (x + u)) := by
  obtain ⟨h1, -⟩ := integrable_and_integral_gaussDensity_tilt_quartic hlam δ L x
  obtain ⟨h2, -⟩ := integrable_and_integral_gaussDensity_tilt_quartic hlam δ (-L) x
  refine ((h1.const_mul (Real.exp (L * x) / 2)).add (h2.const_mul (Real.exp (-(L * x)) / 2))).congr
    (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]
  unfold coshModel
  rw [Real.cosh_eq, show L * (x + u) = L * x + L * u by ring, Real.exp_add,
    show -(L * x + L * u) = -(L * x) + -L * u by ring, Real.exp_add]
  ring

/-- **The heated slice is half the heated quartic plus half the heated cosh model.** -/
theorem cosSliceHeat_eq {lam : ℝ} (hlam : 0 < lam) (δ L x : ℝ) :
    cosSliceHeat δ L lam x = coshModelQuartic δ lam x / 2 + coshModelHeat δ L lam x / 2 := by
  obtain ⟨hq, vq⟩ := integrable_and_integral_gaussDensity_quartic hlam δ x
  have hc := integrable_gaussDensity_mul_coshModel hlam δ L x
  have hpt : ∀ u : ℝ, gaussDensity (lam / 2) u * cosSlice δ L (x + u)
      = (gaussDensity (lam / 2) u * (δ ^ 2 - (x + u) ^ 2) ^ 2) / 2
        + (gaussDensity (lam / 2) u * coshModel δ L (x + u)) / 2 := by
    intro u; unfold cosSlice coshModel; ring
  unfold cosSliceHeat
  rw [show (fun u : ℝ => gaussDensity (lam / 2) u * cosSlice δ L (x + u)) = _ from funext hpt,
    integral_add (hq.div_const 2) (hc.div_const 2), integral_div, integral_div, vq]
  rfl

/-- The Taylor coefficients of the heated quartic `x⁴ + (6λ − 2δ²)x² + δ⁴ − 2λδ² + 3λ²`. -/
def cosQuarticCoeff (δ lam : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then δ ^ 4 - 2 * lam * δ ^ 2 + 3 * lam ^ 2
  else if n = 2 then 6 * lam - 2 * δ ^ 2 else if n = 4 then 1 else 0

theorem hasSum_cosQuarticCoeff (δ lam x : ℝ) :
    HasSum (fun n : ℕ => cosQuarticCoeff δ lam n * x ^ n) (coshModelQuartic δ lam x) := by
  have h : HasSum (fun n : ℕ => cosQuarticCoeff δ lam n * x ^ n)
      (∑ n ∈ Finset.range 5, cosQuarticCoeff δ lam n * x ^ n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      have h0 : n ≠ 0 := by omega
      have h2 : n ≠ 2 := by omega
      have h4 : n ≠ 4 := by omega
      simp [cosQuarticCoeff, h0, h2, h4])
  convert h using 1
  simp [Finset.sum_range_succ, cosQuarticCoeff, coshModelQuartic]
  ring

/-- The Taylor coefficients of the heated slice at `0`. -/
def cosSliceHeatCoeff (δ L lam : ℝ) (n : ℕ) : ℝ :=
  cosQuarticCoeff δ lam n / 2 + coshModelHeatCoeff δ L lam n / 2

theorem hasSum_cosSliceHeatCoeff {lam : ℝ} (hlam : 0 < lam) (δ L x : ℝ) :
    HasSum (fun n : ℕ => cosSliceHeatCoeff δ L lam n * x ^ n) (cosSliceHeat δ L lam x) := by
  rw [cosSliceHeat_eq hlam]
  refine ((hasSum_cosQuarticCoeff δ lam x).div_const 2 |>.add
    ((hasSum_coshModelHeatCoeff (δ := δ) (L := L) hlam x).div_const 2)).congr_fun fun n => ?_
  unfold cosSliceHeatCoeff
  ring

/-- **Detection below half the offset** for the dense model. -/
theorem exists_cosSliceHeatCoeff_neg {δ κ : ℝ} (hκ : 0 < κ) (hδκ : 2 * κ < δ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, ∃ n : ℕ, cosSliceHeatCoeff δ L (κ / L) n < 0 := by
  obtain ⟨L₀, hL₀, h⟩ := exists_coshModelHeatCoeff_neg hκ hδκ
  refine ⟨L₀, hL₀, fun L hL => ?_⟩
  obtain ⟨n, hn6, hn⟩ := h L hL
  refine ⟨n, ?_⟩
  have hq : cosQuarticCoeff δ (κ / L) n = 0 := by
    have h0 : n ≠ 0 := by omega
    have h2 : n ≠ 2 := by omega
    have h4 : n ≠ 4 := by omega
    simp [cosQuarticCoeff, h0, h2, h4]
  unfold cosSliceHeatCoeff
  rw [hq]
  linarith

/-- **Positivity above half the offset** for the dense model. -/
theorem exists_cosSliceHeatCoeff_nonneg {δ κ : ℝ} (hδ : 0 < δ) (hδκ : δ < 2 * κ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, 0 ≤ cosSliceHeatCoeff δ L (κ / L) n := by
  have hκ : 0 < κ := by linarith
  obtain ⟨L₁, hL₁, hcosh⟩ := exists_coshModelHeatCoeff_nonneg hδ hδκ
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = 1 - (δ / (2 * κ)) ^ 2 := ⟨_, rfl⟩
  have hρ : δ / (2 * κ) < 1 := by rw [div_lt_one (by positivity)]; exact hδκ
  have hρ0 : 0 < δ / (2 * κ) := by positivity
  have hθ0 : 0 < θ := by
    rw [hθ]
    have : (δ / (2 * κ)) ^ 2 < 1 := by nlinarith
    linarith
  refine ⟨max (max L₁ (max (1 / κ) (5 / δ))) (max (7 / (2 * κ * θ ^ 2)) (192 * δ ^ 2 / κ ^ 3)),
    lt_max_of_lt_left (lt_max_of_lt_left hL₁), fun L hL n => ?_⟩
  have hLL₁ : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL1 : 1 / κ ≤ L :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hL
  have hL3 : 5 / δ ≤ L :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hL
  have hL7 : 7 / (2 * κ * θ ^ 2) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL192 : 192 * δ ^ 2 / κ ^ 3 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL1
  have hc := hcosh L hLL₁ n
  have hlam0 : 0 ≤ κ / L := by positivity
  -- the order-2 cosh coefficient beats `2δ²`
  have hc2 : 2 * δ ^ 2 ≤ coshModelHeatCoeff δ L (κ / L) 2 := by
    have ha1 : 1 ≤ κ * L := by rw [div_le_iff₀ hκ] at hL1; linarith
    have hb5 : 5 ≤ δ * L := by rw [div_le_iff₀ hδ] at hL3; linarith
    have hθa : 7 ≤ θ ^ 2 * (2 * (κ * L)) := by
      rw [div_le_iff₀ (by positivity)] at hL7; linarith
    have hbθ : (δ * L) ^ 2 = (1 - θ) * (2 * (κ * L)) ^ 2 := by
      rw [hθ]; field_simp; ring
    have hR := one_le_coshModelScaledSign ha1 hb5 hθ0 hbθ hθa (show (0:ℝ) ≤ ((2 : ℕ) : ℝ) by norm_num)
    have hS := coshModelSeriesCoeff_scaled (κ := κ) (δ := δ) hL0 2
    have hκL : κ / L * L = κ := by field_simp
    have heven := coshModelHeatCoeff_even δ L (κ / L) 1
    rw [show 2 * 1 = 2 by norm_num, hκL] at heven
    rw [heven]
    have hc2' : 1 / (2 * L ^ 2) ≤ coshModelSeriesCoeff δ L (κ / L) κ 2 := by
      have hpos : 0 < ((2 : ℕ).factorial : ℝ) * L ^ 4 := by positivity
      have h1 : L ^ 2 ≤ L ^ 2 * coshModelScaledSign (κ * L) (δ * L) ((2 : ℕ) : ℝ) :=
        calc L ^ 2 = L ^ 2 * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)
      rw [← hS] at h1
      rw [div_le_iff₀ (by positivity)]
      have hf : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
      rw [hf, show coshModelSeriesCoeff δ L (κ / L) κ 2 * (2 * L ^ 4)
        = L ^ 2 * (coshModelSeriesCoeff δ L (κ / L) κ 2 * (2 * L ^ 2)) by ring] at h1
      have hL2 : 0 < L ^ 2 := by positivity
      have h1' : L ^ 2 * 1 ≤ L ^ 2 * (coshModelSeriesCoeff δ L (κ / L) κ 2 * (2 * L ^ 2)) := by
        rw [mul_one]; exact h1
      exact (mul_le_mul_iff_right₀ hL2).mp h1'
    have hexp : (κ * L / 2) ^ 3 / 6 ≤ Real.exp (κ / L * L ^ 2 / 2) := by
      have h := Real.pow_div_factorial_le_exp (κ * L / 2) (by positivity) 3
      rw [show κ / L * L ^ 2 / 2 = κ * L / 2 by field_simp]
      simpa [Nat.factorial] using h
    have hbig : 2 * δ ^ 2 ≤ (κ * L / 2) ^ 3 / 6 * (1 / (2 * L ^ 2)) := by
      rw [div_le_iff₀ (by positivity)] at hL192
      have : (κ * L / 2) ^ 3 / 6 * (1 / (2 * L ^ 2)) = κ ^ 3 * L / 96 := by field_simp; ring
      rw [this]
      nlinarith
    calc 2 * δ ^ 2 ≤ (κ * L / 2) ^ 3 / 6 * (1 / (2 * L ^ 2)) := hbig
      _ ≤ Real.exp (κ / L * L ^ 2 / 2) * coshModelSeriesCoeff δ L (κ / L) κ 2 :=
        mul_le_mul hexp hc2' (by positivity) (Real.exp_pos _).le
  unfold cosSliceHeatCoeff cosQuarticCoeff
  split_ifs with h0 h2 h4
  · have : 0 ≤ δ ^ 4 - 2 * (κ / L) * δ ^ 2 + 3 * (κ / L) ^ 2 := by
      nlinarith [sq_nonneg (δ ^ 2 - κ / L), sq_nonneg (κ / L)]
    linarith
  · subst h2
    have : 0 ≤ 6 * (κ / L) := by positivity
    linarith
  · linarith
  · linarith

/-- **WD heat versus de Bruijn–Newman time in the dense model.**  For `0 < 2ε < δ` and all large `L`:
WD positivity at heat `(δ/2 + ε)/L`, WD failure at heat `(δ/2 − ε)/L`, real zeros of the flow at time
`δ/L`, and a non-real zero of the flow at time `(δ − ε)/L`.  So the ratio of the two thresholds tends
to `½`. -/
theorem newmanRatio_cosDefect {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεδ : 2 * ε < δ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀,
      (∀ n : ℕ, 0 ≤ cosSliceHeatCoeff δ L ((δ / 2 + ε) / L) n) ∧
      (∃ n : ℕ, cosSliceHeatCoeff δ L ((δ / 2 - ε) / L) n < 0) ∧
      (∀ z : ℂ, cosDefectFlow δ L (δ / L) z = 0 → z.im = 0) ∧
      (∃ Y : ℝ, 0 < Y ∧ cosDefectFlow δ L ((δ - ε) / L) (I * Y) = 0) := by
  obtain ⟨L₁, hL₁, hpos⟩ := exists_cosSliceHeatCoeff_nonneg (κ := δ / 2 + ε) hδ (by linarith)
  obtain ⟨L₂, hL₂, hneg⟩ := exists_cosSliceHeatCoeff_neg (δ := δ) (κ := δ / 2 - ε) (by linarith)
    (by linarith)
  have hd : 0 < δ ^ 2 - (δ - ε) ^ 2 := by nlinarith
  refine ⟨max (max L₁ L₂) (2 * (δ - ε) / (δ ^ 2 - (δ - ε) ^ 2) + 1),
    lt_max_of_lt_left (lt_max_of_lt_left hL₁), fun L hL => ?_⟩
  have hLL₁ : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLL₂ : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL3 : 2 * (δ - ε) / (δ ^ 2 - (δ - ε) ^ 2) < L :=
    lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hL)
  have hL0 : 0 < L := lt_of_lt_of_le hL₁ hLL₁
  have hcol := cosDefectFlow_collision (μ := δ) hδ hL0
  have hcol' := cosDefectFlow_collision (μ := δ - ε) hδ hL0
  exact ⟨hpos L hLL₁, hneg L hLL₂, hcol.1 le_rfl, hcol'.2 (by linarith) (by linarith) hL3⟩

/-! ## The isolated quadratic model -/

/-- **Quadratic model, WD side.**  The heated slice of `z² + a²` at height `0` is the quartic
`x⁴ + (6λ − 2a²)x² + a⁴ − 2λa² + 3λ²`; its coefficients are all `≥ 0` iff `3λ ≥ a²`. -/
theorem quadModel_heatCoeff_nonneg_iff {a lam : ℝ} :
    (∀ n : ℕ, 0 ≤ cosQuarticCoeff a lam n) ↔ a ^ 2 ≤ 3 * lam := by
  constructor
  · intro h
    have := h 2
    simp [cosQuarticCoeff] at this
    linarith
  · intro h n
    unfold cosQuarticCoeff
    split_ifs
    · nlinarith [sq_nonneg (a ^ 2 - lam), sq_nonneg lam]
    · linarith
    · norm_num
    · exact le_rfl

/-- **Quadratic model, de Bruijn–Newman side.**  The flow `e^{−λD²}(z² + a²) = z² + a² − 2λ` has only
real zeros iff `2λ ≥ a²`. -/
theorem quadModel_flow_realRooted_iff (a lam : ℝ) :
    (∀ z : ℂ, z ^ 2 + (a : ℂ) ^ 2 - 2 * lam = 0 → z.im = 0) ↔ a ^ 2 ≤ 2 * lam := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hpos : 0 < a ^ 2 - 2 * lam := by linarith
    obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (a ^ 2 - 2 * lam) := ⟨_, rfl⟩
    have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hpos
    have hrr : r ^ 2 = a ^ 2 - 2 * lam := by rw [hr]; exact Real.sq_sqrt hpos.le
    have hz := h (I * r) (by
      have : (I * (r : ℂ)) ^ 2 = -((r ^ 2 : ℝ) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
      rw [this, hrr]; push_cast; ring)
    simp at hz
    exact hr0.ne' hz
  · intro h z hz
    have hz2 : z ^ 2 = ((2 * lam - a ^ 2 : ℝ) : ℂ) := by
      push_cast; linear_combination hz
    have him := congrArg Complex.im hz2
    have hre := congrArg Complex.re hz2
    simp only [sq, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re] at him hre
    by_contra hy
    have hx : z.re = 0 := by
      have : 2 * (z.re * z.im) = 0 := by linarith
      rcases mul_eq_zero.mp (by linarith : z.re * z.im = 0) with h1 | h1
      · exact h1
      · exact absurd h1 hy
    rw [hx] at hre
    have : 0 < z.im * z.im := mul_self_pos.mpr hy
    nlinarith

end

end RHTower.DeBruijn
