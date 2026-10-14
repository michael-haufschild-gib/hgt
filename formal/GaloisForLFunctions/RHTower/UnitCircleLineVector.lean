import GaloisForLFunctions.RHTower.UnitCirclePoissonPair

/-!
# Superpositions of unit-circle Poisson pairs

Let `κ` be a finite measure on a measurable space `X`, and `c, y : X → ℝ` measurable with
`c² + y² = 1` and `y > 0` for `κ`-almost every point, and `∫ y^{−2} dκ < ∞`.  Put

`H(x) = ∫ P_{z(p)}(x) dκ(p)`,  `P_z(x) = ((x − c)² + y²)^{−1/2} + ((x + c)² + y²)^{−1/2}`

(`circleLine`).  Then:

* `circleLine_neg`, `circleLine_inv`: `H` is even and `H(1/x) = |x| H(x)`;
* `hasDerivAt_circleLine`: `H' = ∫ P_z' dκ` (`circleLineDeriv`), by dominated differentiation with
  `|P_z'| ≤ 2 max(1, y^{−2})`;
* `integrable_circleLineDeriv` and `integral_circleLineDeriv_mul_sin`:
  `∫ H'(x) sin(ax) dx = −4a ∫ K₀(a y) cos(a c) dκ` for `a > 0` (Fubini against two Cauchy profiles);
* `exp_half_mul_circleLine`: `e^{v/2} H(e^v) = 2^{−1/2} ∫ 𝒦_c(v) dκ`;
* `integral_cos_mul_circleProfile`: its cosine transform is `2^{−1/2} ∫ Ŝ_c(τ) dκ`, with
  `Ŝ_c(τ) = ∫ cos(τv) 𝒦_c(v) dv`; Fubini uses `𝒦_c ≤ (2√2/y)(cosh v)^{−1/2}`.

The hypotheses allow points with `y = 0` on a null set; this covers measures on the side arcs whose
parameter interval contains the cusp.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- The standing hypotheses on a superposition of unit-circle Poisson pairs. -/
structure CircleData (κ : Measure X) (c y : X → ℝ) : Prop where
  meas_c : Measurable c
  meas_y : Measurable y
  circle : ∀ᵐ p ∂κ, c p ^ 2 + y p ^ 2 = 1
  pos : ∀ᵐ p ∂κ, 0 < y p
  inv_sq : Integrable (fun p => 1 / y p ^ 2) κ

/-- `H(x) = ∫ P_{z(p)}(x) dκ(p)`. -/
def circleLine (κ : Measure X) (c y : X → ℝ) (x : ℝ) : ℝ := ∫ p, circlePair (c p) (y p) x ∂κ

/-- `H'(x) = ∫ P_{z(p)}'(x) dκ(p)`. -/
def circleLineDeriv (κ : Measure X) (c y : X → ℝ) (x : ℝ) : ℝ :=
  ∫ p, circlePairDeriv (c p) (y p) x ∂κ

variable {κ : Measure X} {c y : X → ℝ}

theorem CircleData.integrable_one_add (h : CircleData κ c y) [IsFiniteMeasure κ] :
    Integrable (fun p => 1 + 1 / y p ^ 2) κ :=
  (integrable_const 1).add h.inv_sq

theorem max_one_le_one_add {y : ℝ} : max 1 (1 / y ^ 2) ≤ 1 + 1 / y ^ 2 := by
  have : 0 ≤ 1 / y ^ 2 := by positivity
  exact max_le (by linarith) (by linarith)

theorem inv_le_one_add_inv_sq {y : ℝ} (hy : 0 < y) : 1 / y ≤ 1 + 1 / y ^ 2 := by
  rcases le_or_gt 1 y with h | h
  · have : 1 / y ≤ 1 := by rw [div_le_one hy]; exact h
    have : 0 ≤ 1 / y ^ 2 := by positivity
    linarith
  · have h1 : 1 / y ≤ 1 / y ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith

theorem circlePair_le {c y x : ℝ} (hy : 0 < y) : circlePair c y x ≤ 2 / y := by
  unfold circlePair
  have key : ∀ u : ℝ, ((x - u) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ) ≤ 1 / y := by
    intro u
    have hle : y ^ 2 ≤ (x - u) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - u)]
    calc ((x - u) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ) ≤ (y ^ 2) ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
      _ = 1 / y := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
          norm_num
          rw [Real.rpow_neg_one]
  have h2 := key (-c)
  rw [sub_neg_eq_add] at h2
  calc ((x - c) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ) + ((x + c) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ)
      ≤ 1 / y + 1 / y := add_le_add (key c) h2
    _ = 2 / y := by ring

theorem measurable_circlePair_comp (h : CircleData κ c y) (x : ℝ) :
    Measurable fun p => circlePair (c p) (y p) x := by
  unfold circlePair
  have hc := h.meas_c
  have hy := h.meas_y
  fun_prop

theorem measurable_circlePairDeriv_comp (h : CircleData κ c y) (x : ℝ) :
    Measurable fun p => circlePairDeriv (c p) (y p) x := by
  unfold circlePairDeriv
  have hc := h.meas_c
  have hy := h.meas_y
  fun_prop

/-- **Evenness.** -/
theorem circleLine_neg (x : ℝ) : circleLine κ c y (-x) = circleLine κ c y x := by
  unfold circleLine
  simp only [circlePair_neg]

/-- **Inversion.**  `H(1/x) = |x| H(x)`. -/
theorem circleLine_inv (h : CircleData κ c y) {x : ℝ} (hx : x ≠ 0) :
    circleLine κ c y (1 / x) = |x| * circleLine κ c y x := by
  unfold circleLine
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [h.circle, h.pos] with p hp hpos
  exact circlePair_inv hp hpos hx

/-- **The derivative.** -/
theorem hasDerivAt_circleLine [IsFiniteMeasure κ] (h : CircleData κ c y) (x : ℝ) :
    HasDerivAt (circleLine κ c y) (circleLineDeriv κ c y x) x := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := κ)
    (F := fun (x : ℝ) (p : X) => circlePair (c p) (y p) x)
    (F' := fun x p => circlePairDeriv (c p) (y p) x) (x₀ := x)
    (bound := fun p => 2 * (1 + 1 / y p ^ 2)) (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x' => (measurable_circlePair_comp h x').aestronglyMeasurable)
    ((h.integrable_one_add.const_mul 2).mono' (measurable_circlePair_comp h x).aestronglyMeasurable
      (by
        filter_upwards [h.pos] with p hp
        rw [Real.norm_eq_abs, abs_of_nonneg (circlePair_nonneg _ _ _)]
        calc circlePair (c p) (y p) x ≤ 2 / y p := circlePair_le hp
          _ = 2 * (1 / y p) := by ring
          _ ≤ 2 * (1 + 1 / y p ^ 2) := by
              gcongr; exact inv_le_one_add_inv_sq hp))
    (measurable_circlePairDeriv_comp h x).aestronglyMeasurable
    (by
      filter_upwards [h.pos] with p hp x' _
      rw [Real.norm_eq_abs]
      calc |circlePairDeriv (c p) (y p) x'| ≤ 2 * max 1 (1 / y p ^ 2) :=
            abs_circlePairDeriv_le_const hp x'
        _ ≤ 2 * (1 + 1 / y p ^ 2) := by gcongr; exact max_one_le_one_add)
    (h.integrable_one_add.const_mul 2)
    (by
      filter_upwards [h.pos] with p hp x' _
      exact hasDerivAt_circlePair hp x')
  exact key.2

/-- The Cauchy majorant `(1 + (x − c)²)^{−1} + (1 + (x + c)²)^{−1}`. -/
def cauchyPairMajorant (c x : ℝ) : ℝ := (1 + (x - c) ^ 2)⁻¹ + (1 + (x + c) ^ 2)⁻¹

theorem integral_cauchyPairMajorant (c : ℝ) :
    ∫ x, cauchyPairMajorant c x = 2 * ∫ x : ℝ, (1 + x ^ 2)⁻¹ := by
  unfold cauchyPairMajorant
  have h1 : Integrable fun x : ℝ => (1 + (x - c) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_sub_right c
  have h2 : Integrable fun x : ℝ => (1 + (x + c) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_add_right c
  rw [integral_add h1 h2,
    integral_sub_right_eq_self (fun x : ℝ => (1 + x ^ 2)⁻¹) c,
    integral_add_right_eq_self (fun x : ℝ => (1 + x ^ 2)⁻¹) c]
  ring

theorem integrable_cauchyPairMajorant (c : ℝ) : Integrable (cauchyPairMajorant c) :=
  (integrable_inv_one_add_sq.comp_sub_right c).add (integrable_inv_one_add_sq.comp_add_right c)

theorem cauchyPairMajorant_nonneg (c x : ℝ) : 0 ≤ cauchyPairMajorant c x := by
  unfold cauchyPairMajorant; positivity

theorem measurable_circlePairDeriv_comp_prod (h : CircleData κ c y) :
    Measurable fun q : ℝ × X => circlePairDeriv (c q.2) (y q.2) q.1 := by
  unfold circlePairDeriv
  have hc : Measurable fun q : ℝ × X => c q.2 := h.meas_c.comp measurable_snd
  have hy : Measurable fun q : ℝ × X => y q.2 := h.meas_y.comp measurable_snd
  have hx : Measurable fun q : ℝ × X => q.1 := measurable_fst
  have A : Measurable fun q : ℝ × X => q.1 - c q.2 := hx.sub hc
  have B : Measurable fun q : ℝ × X => q.1 + c q.2 := hx.add hc
  have Y2 : Measurable fun q : ℝ × X => y q.2 ^ 2 := hy.pow_const 2
  have PA : Measurable fun q : ℝ × X => ((q.1 - c q.2) ^ 2 + y q.2 ^ 2) ^ (-(3 / 2) : ℝ) :=
    ((A.pow_const 2).add Y2).pow_const _
  have PB : Measurable fun q : ℝ × X => ((q.1 + c q.2) ^ 2 + y q.2 ^ 2) ^ (-(3 / 2) : ℝ) :=
    ((B.pow_const 2).add Y2).pow_const _
  exact ((A.mul PA).add (B.mul PB)).neg

/-- Product integrability of the derivative kernel against a bounded continuous factor. -/
theorem integrable_circlePairDeriv_prod [IsFiniteMeasure κ] (h : CircleData κ c y) {g : ℝ → ℝ}
    (hg : Continuous g) (hg1 : ∀ x, |g x| ≤ 1) :
    Integrable (fun q : ℝ × X => circlePairDeriv (c q.2) (y q.2) q.1 * g q.1)
      (volume.prod κ) := by
  set M : ℝ × X → ℝ := fun q => (1 + 1 / y q.2 ^ 2) * cauchyPairMajorant (c q.2) q.1 with hM
  have hMmeas : Measurable M := by
    simp only [hM, cauchyPairMajorant]
    have hc : Measurable fun q : ℝ × X => c q.2 := h.meas_c.comp measurable_snd
    have hy : Measurable fun q : ℝ × X => y q.2 := h.meas_y.comp measurable_snd
    have hx : Measurable fun q : ℝ × X => q.1 := measurable_fst
    have A : Measurable fun q : ℝ × X => q.1 - c q.2 := hx.sub hc
    have B : Measurable fun q : ℝ × X => q.1 + c q.2 := hx.add hc
    exact (measurable_const.add (measurable_const.div (hy.pow_const 2))).mul
      ((measurable_const.add (A.pow_const 2)).inv.add (measurable_const.add (B.pow_const 2)).inv)
  have hMint : Integrable M (volume.prod κ) := by
    rw [integrable_prod_iff' hMmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
    · simp only [hM]
      exact (integrable_cauchyPairMajorant (c p)).const_mul _
    refine (h.integrable_one_add.mul_const (2 * ∫ x : ℝ, (1 + x ^ 2)⁻¹)).congr ?_
    refine Eventually.of_forall fun p => ?_
    simp only [hM]
    have hnn : ∀ x, ‖(1 + 1 / y p ^ 2) * cauchyPairMajorant (c p) x‖ =
        (1 + 1 / y p ^ 2) * cauchyPairMajorant (c p) x := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
        (cauchyPairMajorant_nonneg _ _))]
    simp_rw [hnn]
    rw [integral_const_mul, integral_cauchyPairMajorant]
  refine hMint.mono' ?_ ?_
  · exact ((measurable_circlePairDeriv_comp_prod h).mul (hg.measurable.comp measurable_fst))
      |>.aestronglyMeasurable
  · have hpos := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := κ)).ae h.pos
    filter_upwards [hpos] with q hq
    simp only [hM, Real.norm_eq_abs, abs_mul]
    calc |circlePairDeriv (c q.2) (y q.2) q.1| * |g q.1|
        ≤ (max 1 (1 / y q.2 ^ 2) * cauchyPairMajorant (c q.2) q.1) * 1 :=
          mul_le_mul (abs_circlePairDeriv_le hq q.1) (hg1 _) (abs_nonneg _)
            (mul_nonneg (le_max_of_le_left zero_le_one) (cauchyPairMajorant_nonneg _ _))
      _ ≤ (1 + 1 / y q.2 ^ 2) * cauchyPairMajorant (c q.2) q.1 := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right max_one_le_one_add (cauchyPairMajorant_nonneg _ _)

theorem integrable_circleLineDeriv [IsFiniteMeasure κ] (h : CircleData κ c y) :
    Integrable (circleLineDeriv κ c y) := by
  have hint := integrable_circlePairDeriv_prod h (g := fun _ => (1 : ℝ)) continuous_const
    fun _ => by norm_num
  refine hint.integral_prod_left.congr (Eventually.of_forall fun x => ?_)
  simp only [mul_one, circleLineDeriv]

theorem integrable_circleLineDeriv_mul [IsFiniteMeasure κ] (h : CircleData κ c y) {g : ℝ → ℝ}
    (hg : Continuous g) (hg1 : ∀ x, |g x| ≤ 1) :
    Integrable fun x => circleLineDeriv κ c y x * g x := by
  refine (integrable_circlePairDeriv_prod h hg hg1).integral_prod_left.congr
    (Eventually.of_forall fun x => ?_)
  simp only [circleLineDeriv]
  rw [integral_mul_const]

/-- **Sine coefficients of `H'`.**  `∫ H'(x) sin(ax) dx = −4a ∫ K₀(a y) cos(a c) dκ`. -/
theorem integral_circleLineDeriv_mul_sin [IsFiniteMeasure κ] (h : CircleData κ c y) {a : ℝ}
    (ha : 0 < a) :
    ∫ x, circleLineDeriv κ c y x * Real.sin (a * x) =
      -(4 * a * ∫ p, kMoment 0 (a * y p) * Real.cos (a * c p) ∂κ) := by
  have hint := integrable_circlePairDeriv_prod h (g := fun x => Real.sin (a * x)) (by fun_prop)
    fun x => Real.abs_sin_le_one _
  have hswap := integral_integral_swap (f := fun x p => circlePairDeriv (c p) (y p) x *
    Real.sin (a * x)) hint
  have hl : ∫ x, circleLineDeriv κ c y x * Real.sin (a * x) =
      ∫ x, ∫ p, circlePairDeriv (c p) (y p) x * Real.sin (a * x) ∂κ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [circleLineDeriv]
    rw [integral_mul_const]
  rw [hl, hswap, ← integral_const_mul, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [h.pos] with p hp
  rw [integral_circlePairDeriv_mul_sin hp ha]
  ring

theorem circlePairDeriv_neg (c y x : ℝ) : circlePairDeriv c y (-x) = -circlePairDeriv c y x := by
  unfold circlePairDeriv
  rw [show (-x - c) ^ 2 = (x + c) ^ 2 by ring, show (-x + c) ^ 2 = (x - c) ^ 2 by ring]
  ring

theorem circleLineDeriv_neg (x : ℝ) : circleLineDeriv κ c y (-x) = -circleLineDeriv κ c y x := by
  unfold circleLineDeriv
  simp only [circlePairDeriv_neg, integral_neg]

/-- **Cosine coefficients of `H'` vanish**, since `H'` is odd. -/
theorem integral_circleLineDeriv_mul_cos (a : ℝ) :
    ∫ x, circleLineDeriv κ c y x * Real.cos (a * x) = 0 := by
  have hn := integral_neg_eq_self (fun x : ℝ => circleLineDeriv κ c y x * Real.cos (a * x)) volume
  have e : (fun x : ℝ => circleLineDeriv κ c y (-x) * Real.cos (a * -x)) =
      fun x => -(circleLineDeriv κ c y x * Real.cos (a * x)) := by
    funext x; rw [circleLineDeriv_neg, mul_neg, Real.cos_neg]; ring
  rw [e, integral_neg] at hn
  linarith

/-- **The log-scale profile.**  `e^{v/2} H(e^v) = 2^{−1/2} ∫ 𝒦_c(v) dκ`. -/
theorem exp_half_mul_circleLine (h : CircleData κ c y) (v : ℝ) :
    Real.exp (v / 2) * circleLine κ c y (Real.exp v) =
      (Real.sqrt 2)⁻¹ * ∫ p, symCoshKernel (c p) v ∂κ := by
  unfold circleLine
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [h.circle, h.pos] with p hcp hp
  exact exp_half_mul_circlePair hcp hp v

/-- Product integrability of `cos(τv) 𝒦_{c(p)}(v)`. -/
theorem integrable_cos_mul_symCoshKernel_prod [IsFiniteMeasure κ] (h : CircleData κ c y)
    (τ : ℝ) :
    Integrable (fun q : ℝ × X => Real.cos (τ * q.1) * symCoshKernel (c q.2) q.1)
      (volume.prod κ) := by
  have hI := _root_.HTGeometry.integrable_cosh_rpow_neg (s := 1 / 2) (by norm_num)
  have hFmeas : Measurable fun q : ℝ × X => Real.cos (τ * q.1) * symCoshKernel (c q.2) q.1 := by
    simp only [symCoshKernel]
    have hc : Measurable fun q : ℝ × X => c q.2 := h.meas_c.comp measurable_snd
    have hv : Measurable fun q : ℝ × X => q.1 := measurable_fst
    have hch : Measurable fun q : ℝ × X => Real.cosh q.1 := Real.measurable_cosh.comp hv
    exact ((Real.measurable_cos.comp (measurable_const.mul hv))).mul
      (((hch.add hc).pow_const _).add ((hch.sub hc).pow_const _))
  have hb : Integrable (fun q : ℝ × X =>
      Real.cosh q.1 ^ (-(1 / 2) : ℝ) * (2 * Real.sqrt 2 * (1 + 1 / y q.2 ^ 2)))
      (volume.prod κ) :=
    hI.mul_prod (h.integrable_one_add.const_mul (2 * Real.sqrt 2))
  refine hb.mono' hFmeas.aestronglyMeasurable ?_
  have hae := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := κ)).ae
    (h.circle.and h.pos)
  filter_upwards [hae] with q hq
  obtain ⟨hcq, hyq⟩ := hq
  simp only [Real.norm_eq_abs, abs_mul]
  have hc1 : |c q.2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  have hk := symCoshKernel_le_of_circle hcq hyq q.1
  have hk0 := symCoshKernel_nonneg hc1 q.1
  rw [abs_of_nonneg hk0]
  calc |Real.cos (τ * q.1)| * symCoshKernel (c q.2) q.1
      ≤ 1 * (2 * Real.sqrt 2 / y q.2 * Real.cosh q.1 ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul (Real.abs_cos_le_one _) hk hk0 zero_le_one
    _ = Real.cosh q.1 ^ (-(1 / 2) : ℝ) * (2 * Real.sqrt 2 * (1 / y q.2)) := by ring
    _ ≤ Real.cosh q.1 ^ (-(1 / 2) : ℝ) * (2 * Real.sqrt 2 * (1 + 1 / y q.2 ^ 2)) := by
        gcongr; exact inv_le_one_add_inv_sq hyq

/-- The spectrum `p ↦ Ŝ_{c(p)}(τ)` is integrable. -/
theorem integrable_circleSpectrum [IsFiniteMeasure κ] (h : CircleData κ c y) (τ : ℝ) :
    Integrable (fun p => ∫ v, Real.cos (τ * v) * symCoshKernel (c p) v) κ :=
  (integrable_cos_mul_symCoshKernel_prod h τ).integral_prod_right

/-- **The spectrum of the profile.**  Its cosine transform is `2^{−1/2} ∫ Ŝ_c(τ) dκ`. -/
theorem integral_cos_mul_circleProfile [IsFiniteMeasure κ] (h : CircleData κ c y) (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * circleLine κ c y (Real.exp v)) =
      (Real.sqrt 2)⁻¹ * ∫ p, (∫ v, Real.cos (τ * v) * symCoshKernel (c p) v) ∂κ := by
  have hFint := integrable_cos_mul_symCoshKernel_prod h τ
  have hswap := integral_integral_swap (f := fun v p => Real.cos (τ * v) * symCoshKernel (c p) v)
    hFint
  have hl : ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * circleLine κ c y (Real.exp v)) =
      (Real.sqrt 2)⁻¹ * ∫ v, ∫ p, Real.cos (τ * v) * symCoshKernel (c p) v ∂κ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [exp_half_mul_circleLine h v, integral_const_mul]
    ring
  rw [hl, hswap]

/-- The cosine-weighted profile is integrable. -/
theorem integrable_cos_mul_circleProfile [IsFiniteMeasure κ] (h : CircleData κ c y) (τ : ℝ) :
    Integrable fun v => Real.cos (τ * v) * (Real.exp (v / 2) * circleLine κ c y (Real.exp v)) := by
  have hint := ((integrable_cos_mul_symCoshKernel_prod h τ).integral_prod_left).const_mul
    (Real.sqrt 2)⁻¹
  refine hint.congr (Eventually.of_forall fun v => ?_)
  simp only
  rw [exp_half_mul_circleLine h v, integral_const_mul]
  ring

end

end RHTower
