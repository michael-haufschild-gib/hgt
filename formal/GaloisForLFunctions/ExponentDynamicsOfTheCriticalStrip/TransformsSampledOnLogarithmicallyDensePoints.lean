import GaloisForLFunctions.SquareRootThreshold.IntervalSourceTransformsSampledOnLocallyBoundedPoints

/-!
# Transforms of interval sources sampled on logarithmically dense points

Let `f` be continuous, vanishing off `[−a, a]`, with transform `Φ(z) = ∫ f(u) e^{izu} du`. The sampling
inequality of `SquareRootThreshold` bounds `Σ_q |Φ(z_q)|²` by the mass `∫|f|²` when the heights
`Re z_q` are boundedly many on unit windows. The zeros of an `L`-function are not: a unit window at
height `T` carries up to `C log T` of them, and the mass alone cannot pay for the logarithm.

The logarithmic energy `E(f) = ∫₀¹ ‖f(· + t) − f‖² dt/t` does. For weights `m_q ≥ 0` with unit-window
sums at most `W` and depths `|Im z_q| ≤ σ`,

`Σ_q m_q log(|Re z_q| + 5) |Φ(z_q)|² ≤ W · 4 (2a + 2 + 2π) e^{2π} e^{σ(2a+3)} (E(f) + ∫|f|²)`
(`sum_weight_mul_log_mul_norm_sq_testTransform_le`),

so a family with `C log T` points per unit window (take `m_q = 1/log(|Re z_q| + 5)`) is sampled at
the rate `e^{2σa}` with no loss in the exponent.

**Proof.** (i) The sampling inequality holds with weights: the grid expansion
`|Φ(z)|² ≤ e^{(h+σ)a} Σ_j (h+σ)^j/(j! a^j) |Φ_j(g)|²` at the grid point `g` left of `Re z` is pointwise, and a
cell of the grid carries weight at most `W` (`sum_weight_mul_norm_sq_testTransform_le`).
(ii) The translate difference `f(· + t) − f` has transform `(e^{−izt} − 1) Φ(z)`, and
`|e^{−izt} − 1|² ≥ 2 e^{−σ} (1 − cos(t Re z))` for `0 ≤ t ≤ 1`. Sampling the differences and integrating
against `dt/t` gives `Σ_q m_q K(Re z_q) |Φ(z_q)|² ≤ W C E(f)` with the kernel
`K(ξ) = ∫₀¹ (1 − cos ξt) dt/t`. (iii) `K(Y) ≥ K(Y/2) + ¼` for `Y ≥ 8`, hence `log(|ξ| + 5) ≤ 4K(ξ) + 4`.

Lipschitz sources have finite logarithmic energy, at most `K²(2a + 2)`
(`logEnergy_le_of_lipschitz`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open GaloisForLFunctions.HTGeometry _root_.RHTower _root_.RHTower.CCMParityQuartet
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-! ### 1. The grid expansion at one point -/

/-- The squared `j`-th moment transform at the grid point `−k h`. -/
def gridMoment (a : ℝ) (f : ℝ → ℂ) (j : ℕ) (k : ℤ) : ℝ :=
  ‖testTransform (momentSource f j) ((-(k * gridStep a) : ℝ) : ℂ)‖ ^ 2

theorem gridMoment_nonneg (a : ℝ) (f : ℝ → ℂ) (j : ℕ) (k : ℤ) : 0 ≤ gridMoment a f j k :=
  sq_nonneg _

/-- The weight `ρ^j/(j! a^j)` of the `j`-th moment in the grid expansion. -/
def gridWeight (ρ a : ℝ) (j : ℕ) : ℝ := ρ ^ j / (j.factorial * a ^ j)

theorem gridWeight_nonneg {ρ a : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (j : ℕ) : 0 ≤ gridWeight ρ a j := by
  unfold gridWeight; positivity

/-- Grid Parseval for the moments: `Σ_k |Φ_j(kh)|² ≤ L a^{2j} ∫|f|²` on every finite set of cells. -/
theorem sum_gridMoment_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : IntervalSource a f) (j : ℕ)
    (t : Finset ℤ) :
    ∑ k ∈ t, gridMoment a f j k ≤ windowLength a * ((a ^ j) ^ 2 * ∫ u, ‖f u‖ ^ 2) :=
  sum_norm_sq_testTransform_grid_le ha hf j t

theorem gridWeight_mul_gridMoment_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : IntervalSource a f)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (j : ℕ) (k : ℤ) :
    gridWeight ρ a j * gridMoment a f j k ≤ (ρ * a) ^ j / j.factorial * (∫ u, ‖f u‖) ^ 2 := by
  have hB := norm_testTransform_momentSource_le hf j (-(k * gridStep a))
  calc gridWeight ρ a j * gridMoment a f j k
      ≤ gridWeight ρ a j * (a ^ j * ∫ u, ‖f u‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hB 2)
          (gridWeight_nonneg hρ ha.le j)
    _ = (ρ * a) ^ j / j.factorial * (∫ u, ‖f u‖) ^ 2 := by
        rw [mul_pow (a ^ j)]
        exact momentWeight_mul_sq ρ a _ j ha.ne'

theorem summable_gridWeight_mul_gridMoment {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℤ) :
    Summable fun j => gridWeight ρ a j * gridMoment a f j k :=
  Summable.of_nonneg_of_le
    (fun j => mul_nonneg (gridWeight_nonneg hρ ha.le j) (gridMoment_nonneg a f j k))
    (fun j => gridWeight_mul_gridMoment_le ha hf hρ j k)
    ((Real.summable_pow_div_factorial (ρ * a)).mul_right _)

/-- **The grid expansion.** With `h` the grid step, `g` the grid point left of `x` and `|y| ≤ σ`:
`|Φ(x + iy)|² ≤ e^{(h+σ)a} Σ_j (h+σ)^j/(j! a^j) |Φ_j(g)|²`. -/
theorem norm_sq_testTransform_le_tsum_gridMoment {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {σ : ℝ} (hσ : 0 ≤ σ) (x : ℝ) {y : ℝ} (hy : |y| ≤ σ) :
    ‖testTransform f ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
      Real.exp ((gridStep a + σ) * a) *
        ∑' j, gridWeight (gridStep a + σ) a j * gridMoment a f j (gridIndex a x) := by
  have hh0 : 0 < gridStep a := gridStep_pos ha
  set ρ₀ := gridStep a + σ with hρ₀
  have hρ₀0 : 0 < ρ₀ := by linarith
  set g : ℝ := -((gridIndex a x : ℝ) * gridStep a) with hg
  set B : ℕ → ℝ := fun j => ‖testTransform (momentSource f j) ((g : ℝ) : ℂ)‖ with hB
  have hw : ‖((x : ℂ) + (y : ℂ) * I) - (g : ℂ)‖ ≤ ρ₀ := by
    have e : ((x : ℂ) + (y : ℂ) * I) - (g : ℂ) = ((x - g : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have := abs_sub_gridPoint_le ha x
    linarith
  have hz : ((x : ℂ) + (y : ℂ) * I) = (g : ℂ) + (((x : ℂ) + (y : ℂ) * I) - (g : ℂ)) := by ring
  have h1 := norm_testTransform_le_tsum_momentSource hf g hw
  rw [← hz] at h1
  have hp : ∀ j : ℕ, 0 < (ρ₀ * a) ^ j / j.factorial := fun j => by positivity
  have hps : Summable fun j : ℕ => (ρ₀ * a) ^ j / j.factorial :=
    Real.summable_pow_div_factorial _
  have hconv : ∀ j : ℕ, (ρ₀ ^ j / j.factorial * B j) ^ 2 / ((ρ₀ * a) ^ j / j.factorial) =
      gridWeight ρ₀ a j * gridMoment a f j (gridIndex a x) := fun j =>
    sq_div_momentWeight ρ₀ a (B j) j ha.ne' hρ₀0.ne'
  have hcs : Summable fun j : ℕ =>
      (ρ₀ ^ j / j.factorial * B j) ^ 2 / ((ρ₀ * a) ^ j / j.factorial) := by
    simp only [hconv]
    exact summable_gridWeight_mul_gridMoment ha hf hρ₀0.le _
  have hCS := sq_tsum_le_tsum_mul_tsum_div hp (fun j => by positivity) hps hcs
  have hE : ∑' j : ℕ, (ρ₀ * a) ^ j / j.factorial = Real.exp (ρ₀ * a) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc ‖testTransform f ((x : ℂ) + (y : ℂ) * I)‖ ^ 2
      ≤ (∑' j : ℕ, ρ₀ ^ j / j.factorial * B j) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := hCS
    _ = Real.exp (ρ₀ * a) * ∑' j, gridWeight ρ₀ a j * gridMoment a f j (gridIndex a x) := by
        rw [hE]
        congr 1
        exact tsum_congr hconv

/-! ### 2. Weighted cells and the weighted sampling inequality -/

/-- **Weighted cell sums against a grid function.** If every unit window of `s` carries weight at
most `W`, then `Σ_{q ∈ s} m_q G(k_q) ≤ W Σ_k G(k)` for nonnegative `G` with partial sums at most
`Gs`. -/
theorem sum_weight_mul_grid_le {ι : Type*} {x m : ι → ℝ} {a : ℝ} (ha : 0 < a) (s : Finset ι)
    {W : ℝ}
    (hW : ∀ T : ℝ, ∀ t : Finset ι, t ⊆ s → (∀ q ∈ t, |x q - T| ≤ 1) → ∑ q ∈ t, m q ≤ W)
    (G : ℤ → ℝ) (hG0 : ∀ k, 0 ≤ G k) {Gs : ℝ} (hGs : ∀ t : Finset ℤ, ∑ k ∈ t, G k ≤ Gs) :
    ∑ q ∈ s, m q * G (gridIndex a (x q)) ≤ W * Gs := by
  classical
  have hW0 : 0 ≤ W := by simpa using hW 0 ∅ (Finset.empty_subset _) (by simp)
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun q => gridIndex a (x q))
    (t := s.image fun q => gridIndex a (x q)) (fun q hq => Finset.mem_image_of_mem _ hq)]
  have hcell : ∀ k ∈ s.image (fun q => gridIndex a (x q)),
      ∑ q ∈ s with gridIndex a (x q) = k, m q * G (gridIndex a (x q)) ≤ W * G k := by
    intro k _
    have hsum : ∑ q ∈ s with gridIndex a (x q) = k, m q * G (gridIndex a (x q)) =
        (∑ q ∈ s with gridIndex a (x q) = k, m q) * G k := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [(Finset.mem_filter.mp hq).2]
    rw [hsum]
    refine mul_le_mul_of_nonneg_right ?_ (hG0 k)
    refine hW (-((k : ℝ) * gridStep a)) _ (Finset.filter_subset _ _) fun q hq => ?_
    have hqk := (Finset.mem_filter.mp hq).2
    rw [← hqk]
    exact (abs_sub_gridPoint_le ha (x q)).trans (gridStep_le_one ha)
  calc ∑ k ∈ s.image (fun q => gridIndex a (x q)),
        ∑ q ∈ s with gridIndex a (x q) = k, m q * G (gridIndex a (x q))
      ≤ ∑ k ∈ s.image (fun q => gridIndex a (x q)), W * G k := Finset.sum_le_sum hcell
    _ = W * ∑ k ∈ s.image (fun q => gridIndex a (x q)), G k := by rw [Finset.mul_sum]
    _ ≤ W * Gs := mul_le_mul_of_nonneg_left (hGs _) hW0

/-- **The sampling inequality with weights.** If the weights `m_q ≥ 0` of the points with height in
any unit window sum to at most `W` and all depths satisfy `|y_q| ≤ σ`, then
`Σ_{q ∈ s} m_q |Φ(x_q + i y_q)|² ≤ e^{2(h+σ)a} W L ∫|f|²` with `L = 2a + 2π`, `h = 2π/L`. -/
theorem sum_weight_mul_norm_sq_testTransform_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {ι : Type*} (x y m : ι → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hy : ∀ q, |y q| ≤ σ) (hm : ∀ q, 0 ≤ m q) {W : ℝ} (s : Finset ι)
    (hW : ∀ T : ℝ, ∀ t : Finset ι, t ⊆ s → (∀ q ∈ t, |x q - T| ≤ 1) → ∑ q ∈ t, m q ≤ W) :
    ∑ q ∈ s, m q * ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      Real.exp (2 * (gridStep a + σ) * a) * (W * (windowLength a * ∫ u, ‖f u‖ ^ 2)) := by
  have hh0 : 0 < gridStep a := gridStep_pos ha
  set ρ₀ := gridStep a + σ with hρ₀
  have hρ₀0 : 0 < ρ₀ := by linarith
  set N := ∫ u, ‖f u‖ ^ 2 with hN
  set L := windowLength a with hL
  set D : ℕ → ℝ := gridWeight ρ₀ a with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => gridWeight_nonneg hρ₀0.le ha.le j
  have hsummD : ∀ q, Summable fun j => D j * gridMoment a f j (gridIndex a (x q)) := fun q =>
    summable_gridWeight_mul_gridMoment ha hf hρ₀0.le _
  have hpt : ∀ q, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      Real.exp (ρ₀ * a) * ∑' j, D j * gridMoment a f j (gridIndex a (x q)) := fun q =>
    norm_sq_testTransform_le_tsum_gridMoment ha hf hσ (x q) (hy q)
  -- a cell of the grid carries weight at most `W`; grid Parseval for the moments
  have hcell : ∀ j, ∑ q ∈ s, m q * gridMoment a f j (gridIndex a (x q)) ≤
      W * (L * ((a ^ j) ^ 2 * N)) := fun j =>
    sum_weight_mul_grid_le ha s hW (gridMoment a f j) (gridMoment_nonneg a f j)
      (sum_gridMoment_le ha hf j)
  have hterm : ∀ j : ℕ, D j * (W * (L * ((a ^ j) ^ 2 * N))) =
      (ρ₀ * a) ^ j / j.factorial * (W * (L * N)) := by
    intro j
    rw [show W * (L * ((a ^ j) ^ 2 * N)) = (a ^ j) ^ 2 * (W * (L * N)) by ring]
    exact momentWeight_mul_sq ρ₀ a (W * (L * N)) j ha.ne'
  have hE : ∑' j : ℕ, (ρ₀ * a) ^ j / j.factorial = Real.exp (ρ₀ * a) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsummR : Summable fun j : ℕ => (ρ₀ * a) ^ j / j.factorial * (W * (L * N)) :=
    (Real.summable_pow_div_factorial (ρ₀ * a)).mul_right _
  have hsummS : Summable fun j => D j * ∑ q ∈ s, m q * gridMoment a f j (gridIndex a (x q)) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsummR
    · exact mul_nonneg (hD0 j) (Finset.sum_nonneg fun q _ =>
        mul_nonneg (hm q) (gridMoment_nonneg a f j _))
    · exact (mul_le_mul_of_nonneg_left (hcell j) (hD0 j)).trans (hterm j).le
  have hswap : ∀ q, m q * (Real.exp (ρ₀ * a) * ∑' j, D j * gridMoment a f j (gridIndex a (x q))) =
      Real.exp (ρ₀ * a) * ∑' j, m q * (D j * gridMoment a f j (gridIndex a (x q))) := fun q => by
    rw [(hsummD q).tsum_mul_left (m q)]
    ring
  calc ∑ q ∈ s, m q * ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2
      ≤ ∑ q ∈ s, m q *
          (Real.exp (ρ₀ * a) * ∑' j, D j * gridMoment a f j (gridIndex a (x q))) :=
        Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hpt q) (hm q)
    _ = Real.exp (ρ₀ * a) *
          ∑' j, D j * ∑ q ∈ s, m q * gridMoment a f j (gridIndex a (x q)) := by
        rw [Finset.sum_congr rfl fun q _ => hswap q, ← Finset.mul_sum,
          ← Summable.tsum_finsetSum (fun q _ => (hsummD q).mul_left (m q))]
        congr 1
        refine tsum_congr fun j => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ Real.exp (ρ₀ * a) * ∑' j, D j * (W * (L * ((a ^ j) ^ 2 * N))) := by
        refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun j => ?_) hsummS ?_)
          (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left (hcell j) (hD0 j)
        · exact hsummR.congr fun j => (hterm j).symm
    _ = Real.exp (ρ₀ * a) * (Real.exp (ρ₀ * a) * (W * (L * N))) := by
        congr 1
        rw [tsum_congr hterm, tsum_mul_right, hE]
    _ = Real.exp (2 * ρ₀ * a) * (W * (L * N)) := by
        rw [← mul_assoc, ← Real.exp_add, show ρ₀ * a + ρ₀ * a = 2 * ρ₀ * a by ring]

/-- The constant `(2a + 2π) e^{2π} e^{2σa}` of the sampling inequality. -/
def samplingConst (a σ : ℝ) : ℝ := (2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)

/-- **The weighted sampling inequality with the explicit constant.** -/
theorem sum_weight_mul_norm_sq_testTransform_le' {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {ι : Type*} (x y m : ι → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hy : ∀ q, |y q| ≤ σ) (hm : ∀ q, 0 ≤ m q) {W : ℝ} (s : Finset ι)
    (hW : ∀ T : ℝ, ∀ t : Finset ι, t ⊆ s → (∀ q ∈ t, |x q - T| ≤ 1) → ∑ q ∈ t, m q ≤ W) :
    ∑ q ∈ s, m q * ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      W * (samplingConst a σ * ∫ u, ‖f u‖ ^ 2) := by
  refine (sum_weight_mul_norm_sq_testTransform_le ha hf x y m hσ hy hm s hW).trans ?_
  have hW0 : 0 ≤ W := by simpa using hW 0 ∅ (Finset.empty_subset _) (by simp)
  have hN0 : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hexp : Real.exp (2 * (gridStep a + σ) * a) ≤ Real.exp (2 * π) * Real.exp (2 * σ * a) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := gridStep_mul_le_pi ha
    have h2 : 2 * (gridStep a + σ) * a = 2 * (gridStep a * a) + 2 * σ * a := by ring
    linarith
  unfold windowLength samplingConst
  calc Real.exp (2 * (gridStep a + σ) * a) * (W * ((2 * a + 2 * π) * ∫ u, ‖f u‖ ^ 2))
      ≤ Real.exp (2 * π) * Real.exp (2 * σ * a) * (W * ((2 * a + 2 * π) * ∫ u, ‖f u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = _ := by ring

/-! ### 3. The logarithmic kernel -/

/-- The logarithmic kernel `K(ξ) = ∫₀¹ (1 − cos ξt) dt/t`. -/
def logKernel (ξ : ℝ) : ℝ := ∫ t in (0:ℝ)..1, (1 - Real.cos (ξ * t)) / t

theorem one_sub_cos_div_nonneg (ξ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (1 - Real.cos (ξ * t)) / t :=
  div_nonneg (by linarith [Real.cos_le_one (ξ * t)]) ht

theorem one_sub_cos_div_le (ξ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (1 - Real.cos (ξ * t)) / t ≤ ξ ^ 2 * t / 2 := by
  rcases ht.eq_or_lt with rfl | ht0
  · simp
  · rw [div_le_iff₀ ht0]
    have := Real.one_sub_sq_div_two_le_cos (x := ξ * t)
    nlinarith

theorem intervalIntegrable_one_sub_cos_div (ξ : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (1 - Real.cos (ξ * t)) / t) volume a b := by
  have hmeas : Measurable fun t : ℝ => (1 - Real.cos (ξ * t)) / t :=
    (measurable_const.sub (Real.measurable_cos.comp (measurable_const.mul measurable_id))).div
      measurable_id
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := ξ ^ 2 * b / 2) measure_Ioc_lt_top.ne
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 ≤ t := ha.trans ht.1.le
  rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_div_nonneg ξ ht0)]
  refine (one_sub_cos_div_le ξ ht0).trans ?_
  have : ξ ^ 2 * t ≤ ξ ^ 2 * b := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg ξ)
  linarith

theorem logKernel_nonneg (ξ : ℝ) : 0 ≤ logKernel ξ :=
  intervalIntegral.integral_nonneg zero_le_one fun _ ht => one_sub_cos_div_nonneg ξ ht.1

theorem logKernel_neg (ξ : ℝ) : logKernel (-ξ) = logKernel ξ := by
  simp only [logKernel, neg_mul, Real.cos_neg]

theorem logKernel_abs (ξ : ℝ) : logKernel |ξ| = logKernel ξ := by
  rcases abs_choice ξ with h | h <;> rw [h]
  exact logKernel_neg ξ

/-- `K(Y/2) = ∫₀^{1/2} (1 − cos Yt) dt/t`. -/
theorem logKernel_half (Y : ℝ) :
    logKernel (Y / 2) = ∫ t in (0:ℝ)..(1 / 2), (1 - Real.cos (Y * t)) / t := by
  have h := intervalIntegral.integral_comp_div (a := 0) (b := 1)
    (fun t : ℝ => (1 - Real.cos (Y * t)) / t) (two_ne_zero (α := ℝ))
  have hfun : (fun t : ℝ => (1 - Real.cos (Y * (t / 2))) / (t / 2)) =
      fun t => 2 * ((1 - Real.cos (Y / 2 * t)) / t) := by
    funext t
    rw [show Y * (t / 2) = Y / 2 * t by ring]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
  beta_reduce at h
  rw [hfun, intervalIntegral.integral_const_mul, zero_div, smul_eq_mul] at h
  unfold logKernel
  linarith

/-- **The kernel gains a quarter on each octave**: `K(Y) ≥ K(Y/2) + ¼` for `Y ≥ 8`, since
`∫_{1/2}^1 (1 − cos Yt) dt/t ≥ ½ − 2/Y`. -/
theorem logKernel_half_add_quarter_le {Y : ℝ} (hY : 8 ≤ Y) :
    logKernel (Y / 2) + 1 / 4 ≤ logKernel Y := by
  have hY0 : 0 < Y := by linarith
  have hsplit : logKernel Y = (∫ t in (0:ℝ)..(1 / 2), (1 - Real.cos (Y * t)) / t) +
      ∫ t in (1 / 2 : ℝ)..1, (1 - Real.cos (Y * t)) / t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_one_sub_cos_div Y le_rfl (by norm_num))
      (intervalIntegrable_one_sub_cos_div Y (by norm_num) (by norm_num))).symm
  have hcont : Continuous fun t : ℝ => 1 - Real.cos (Y * t) := by fun_prop
  have hmono : ∫ t in (1 / 2 : ℝ)..1, (1 - Real.cos (Y * t)) ≤
      ∫ t in (1 / 2 : ℝ)..1, (1 - Real.cos (Y * t)) / t := by
    refine intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
      (intervalIntegrable_one_sub_cos_div Y (by norm_num) (by norm_num)) fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    rw [le_div_iff₀ ht0]
    nlinarith [mul_nonneg (by linarith [Real.cos_le_one (Y * t)] :
      (0 : ℝ) ≤ 1 - Real.cos (Y * t)) (sub_nonneg.mpr ht.2)]
  have hcos : ∫ t in (1 / 2 : ℝ)..1, Real.cos (Y * t) = (Real.sin Y - Real.sin (Y / 2)) / Y := by
    rw [intervalIntegral.integral_comp_mul_left Real.cos hY0.ne', integral_cos, smul_eq_mul,
      mul_one, show Y * (1 / 2 : ℝ) = Y / 2 by ring]
    ring
  have hval : ∫ t in (1 / 2 : ℝ)..1, (1 - Real.cos (Y * t)) =
      1 / 2 - (Real.sin Y - Real.sin (Y / 2)) / Y := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (Y * t)).intervalIntegrable _ _), hcos,
      intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  have hsin : (Real.sin Y - Real.sin (Y / 2)) / Y ≤ 1 / 4 := by
    rw [div_le_iff₀ hY0]
    linarith [Real.sin_le_one Y, Real.neg_one_le_sin (Y / 2)]
  rw [hsplit, logKernel_half]
  linarith

theorem div_four_le_logKernel (n : ℕ) : ∀ Y : ℝ, 4 * 2 ^ n ≤ Y → (n : ℝ) / 4 ≤ logKernel Y := by
  induction n with
  | zero => intro Y _; simpa using logKernel_nonneg Y
  | succ n ih =>
    intro Y hY
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ] at hY
    have h3 := logKernel_half_add_quarter_le (Y := Y) (by linarith)
    have h4 := ih (Y / 2) (by linarith)
    push_cast
    linarith

/-- **The kernel dominates the logarithm**: `log(|ξ| + 5) ≤ 4 K(ξ) + 4`. -/
theorem log_abs_add_five_le (ξ : ℝ) : Real.log (|ξ| + 5) ≤ 4 * logKernel ξ + 4 := by
  rw [← logKernel_abs ξ]
  have hY0 : 0 ≤ |ξ| := abs_nonneg ξ
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hK := logKernel_nonneg |ξ|
  by_cases hY4 : |ξ| < 4
  · have h1 : Real.log (|ξ| + 5) ≤ Real.log (2 ^ 4) :=
      Real.log_le_log (by linarith) (by norm_num; linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  · have hY4' : 4 ≤ |ξ| := not_lt.mp hY4
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ |ξ| / 4)
      (by norm_num : (1 : ℝ) < 2)
    have hKn := div_four_le_logKernel n |ξ| (by linarith)
    have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h1 : Real.log (|ξ| + 5) ≤ Real.log (2 ^ (n + 4)) := by
      refine Real.log_le_log (by linarith) ?_
      rw [show (2 : ℝ) ^ (n + 4) = 16 * 2 ^ n by ring]
      rw [show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n by ring] at hn2
      linarith
    rw [Real.log_pow] at h1
    push_cast at h1
    have h5 : ((n : ℝ) + 4) * Real.log 2 ≤ (n : ℝ) + 4 :=
      mul_le_of_le_one_right (by positivity) hlog2
    linarith

/-! ### 4. Translate differences -/

/-- The difference `u ↦ f(u + t) − f(u)` of a translate and the source. -/
def shiftDiff (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ := fun u => f (u + t) - f u

theorem intervalSource_shiftDiff {a : ℝ} {f : ℝ → ℂ} (hf : IntervalSource a f) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IntervalSource (a + 1) (shiftDiff f t) := by
  have hvan : ∀ u, u ∉ Icc (-(a + 1)) (a + 1) → shiftDiff f t u = 0 := fun u hu => by
    have h1 : u + t ∉ Icc (-a) a := fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
    have h2 : u ∉ Icc (-a) a := fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
    simp [shiftDiff, hf.vanish _ h1, hf.vanish _ h2]
  exact
    { continuous := (hf.continuous.comp (continuous_add_const t)).sub hf.continuous
      hasCompactSupport := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        fun u hu => by_contra fun h => hu (hvan u h)
      vanish := hvan }

/-- The transform of a translate difference: `(e^{−izt} − 1) Φ(z)`. -/
theorem testTransform_shiftDiff {a : ℝ} {f : ℝ → ℂ} (hf : IntervalSource a f) (t : ℝ) (z : ℂ) :
    testTransform (shiftDiff f t) z = (cexp (-(I * z * (t : ℂ))) - 1) * testTransform f z := by
  have hc : Continuous fun u : ℝ => f (u + t) := hf.continuous.comp (continuous_add_const t)
  have hcs : HasCompactSupport fun u : ℝ => f (u + t) :=
    hf.hasCompactSupport.comp_homeomorph (Homeomorph.addRight t)
  have hint := integrable_testTransform_integrand hf.continuous hf.hasCompactSupport z
  have hint' := integrable_testTransform_integrand hc hcs z
  have hshift : ∫ u : ℝ, f (u + t) * cexp (I * z * (u : ℂ)) =
      cexp (-(I * z * (t : ℂ))) * ∫ u : ℝ, f u * cexp (I * z * (u : ℂ)) := by
    rw [← integral_const_mul, ← integral_add_right_eq_self
      (fun u : ℝ => cexp (-(I * z * (t : ℂ))) * (f u * cexp (I * z * (u : ℂ)))) t]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show f (u + t) * cexp (I * z * (u : ℂ)) =
      cexp (-(I * z * (t : ℂ))) * (f (u + t) * cexp (I * z * ((u + t : ℝ) : ℂ)))
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have e : (fun u : ℝ => shiftDiff f t u * cexp (I * z * (u : ℂ))) =
      fun u => f (u + t) * cexp (I * z * (u : ℂ)) - f u * cexp (I * z * (u : ℂ)) := by
    funext u
    simp only [shiftDiff, sub_mul]
  unfold testTransform
  rw [e, integral_sub hint' hint, hshift]
  ring

/-- `|e^{−izt} − 1|² ≥ 2 e^{−σ} (1 − cos(t Re z))` for `|Im z| ≤ σ` and `0 ≤ t ≤ 1`. -/
theorem two_mul_exp_neg_mul_one_sub_cos_le {σ ξ η t : ℝ} (hη : |η| ≤ σ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    2 * Real.exp (-σ) * (1 - Real.cos (ξ * t)) ≤
      ‖cexp (-(I * ((ξ : ℂ) + (η : ℂ) * I) * (t : ℂ))) - 1‖ ^ 2 := by
  have hw : -(I * ((ξ : ℂ) + (η : ℂ) * I) * (t : ℂ)) =
      ((η * t : ℝ) : ℂ) + ((-(ξ * t) : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (-(η : ℂ) * (t : ℂ)) * Complex.I_sq
  set w : ℂ := ((η * t : ℝ) : ℂ) + ((-(ξ * t) : ℝ) : ℂ) * I with hwdef
  have hre : w.re = η * t := by simp [hwdef]
  have him : w.im = -(ξ * t) := by simp [hwdef]
  have hnorm : ‖cexp w - 1‖ ^ 2 = (Real.exp (η * t) * Real.cos (ξ * t) - 1) ^ 2 +
      (Real.exp (η * t) * Real.sin (ξ * t)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.exp_re,
      Complex.exp_im, hre, him, Complex.one_re, Complex.one_im, Real.cos_neg, Real.sin_neg]
    ring
  rw [hw, hnorm]
  have hσ0 : 0 ≤ σ := (abs_nonneg η).trans hη
  have hE : Real.exp (-σ) ≤ Real.exp (η * t) := Real.exp_le_exp.mpr (by
    nlinarith [mul_nonneg ht0 (by linarith [(abs_le.mp hη).1] : (0 : ℝ) ≤ η + σ),
      mul_nonneg (sub_nonneg.mpr ht1) hσ0])
  have hc : 0 ≤ 1 - Real.cos (ξ * t) := by linarith [Real.cos_le_one (ξ * t)]
  have h1 := mul_le_mul_of_nonneg_right hE hc
  have hsc : Real.exp (η * t) ^ 2 * Real.sin (ξ * t) ^ 2 +
      Real.exp (η * t) ^ 2 * Real.cos (ξ * t) ^ 2 = Real.exp (η * t) ^ 2 := by
    rw [← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  nlinarith [sq_nonneg (Real.exp (η * t) - 1)]

/-! ### 5. The logarithmic energy -/

/-- The logarithmic energy `E(f) = ∫₀¹ ‖f(· + t) − f‖² dt/t`. -/
def logEnergy (f : ℝ → ℂ) : ℝ := ∫ t in (0:ℝ)..1, (∫ u, ‖f (u + t) - f u‖ ^ 2) / t

theorem logEnergy_nonneg (f : ℝ → ℂ) : 0 ≤ logEnergy f :=
  intervalIntegral.integral_nonneg zero_le_one fun _ ht =>
    div_nonneg (integral_nonneg fun _ => sq_nonneg _) ht.1

/-- The `L²` modulus of a `K`-Lipschitz source: `‖f(· + t) − f‖² ≤ (Kt)² (2a + 2)`. -/
theorem integral_norm_sq_shiftDiff_le_of_lipschitz {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {K : NNReal} (hK : LipschitzWith K f) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ∫ u, ‖f (u + t) - f u‖ ^ 2 ≤ ((K : ℝ) * t) ^ 2 * (2 * a + 2) := by
  have hS := intervalSource_shiftDiff hf ht0 ht1
  have hpt : ∀ u, ‖f (u + t) - f u‖ ^ 2 ≤
      (Icc (-(a + 1)) (a + 1)).indicator (fun _ => ((K : ℝ) * t) ^ 2) u := by
    intro u
    by_cases hu : u ∈ Icc (-(a + 1)) (a + 1)
    · rw [indicator_of_mem hu]
      have h := hK.dist_le_mul (u + t) u
      rw [dist_eq_norm, Real.dist_eq, add_sub_cancel_left, abs_of_nonneg ht0] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    · rw [indicator_of_notMem hu]
      have h0 : f (u + t) - f u = 0 := hS.vanish u hu
      rw [h0]
      simp
  calc ∫ u, ‖f (u + t) - f u‖ ^ 2
      ≤ ∫ u, (Icc (-(a + 1)) (a + 1)).indicator (fun _ => ((K : ℝ) * t) ^ 2) u :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
          (Eventually.of_forall hpt)
    _ = ((K : ℝ) * t) ^ 2 * (2 * a + 2) := by
        rw [integral_indicator_const _ measurableSet_Icc,
          Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

/-- Lipschitz sources have integrable logarithmic energy density. -/
theorem intervalIntegrable_logEnergy_of_lipschitz {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {K : NNReal} (hK : LipschitzWith K f) :
    IntervalIntegrable (fun t => (∫ u, ‖f (u + t) - f u‖ ^ 2) / t) volume 0 1 := by
  have hcont : Continuous (Function.uncurry fun (t u : ℝ) => ‖f (u + t) - f u‖ ^ 2) := by
    have h1 : Continuous fun p : ℝ × ℝ => f (p.2 + p.1) :=
      hf.continuous.comp (continuous_snd.add continuous_fst)
    have h2 : Continuous fun p : ℝ × ℝ => f p.2 := hf.continuous.comp continuous_snd
    exact ((h1.sub h2).norm).pow 2
  have hsm : StronglyMeasurable fun t : ℝ => ∫ u, ‖f (u + t) - f u‖ ^ 2 :=
    hcont.stronglyMeasurable.integral_prod_right'
  have hmeas : Measurable fun t : ℝ => (∫ u, ‖f (u + t) - f u‖ ^ 2) / t :=
    hsm.measurable.div measurable_id
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2 * (2 * a + 2)) measure_Ioc_lt_top.ne
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
  have hI := integral_norm_sq_shiftDiff_le_of_lipschitz ha hf hK ht.1.le ht.2
  have hI0 : 0 ≤ ∫ u, ‖f (u + t) - f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hK2 : 0 ≤ (K : ℝ) ^ 2 * (2 * a + 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hI0 ht.1.le), div_le_iff₀ ht.1]
  nlinarith [mul_nonneg hK2 (mul_nonneg ht.1.le (sub_nonneg.mpr ht.2))]

/-- **Lipschitz sources have logarithmic energy at most `K² (2a + 2)`.** -/
theorem logEnergy_le_of_lipschitz {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : IntervalSource a f)
    {K : NNReal} (hK : LipschitzWith K f) : logEnergy f ≤ (K : ℝ) ^ 2 * (2 * a + 2) := by
  have hK2 : 0 ≤ (K : ℝ) ^ 2 * (2 * a + 2) := by positivity
  have h := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_logEnergy_of_lipschitz ha hf hK)
    (intervalIntegrable_const (c := (K : ℝ) ^ 2 * (2 * a + 2)) (μ := volume) (a := 0) (b := 1))
    (fun t ht => by
      rcases ht.1.eq_or_lt with rfl | ht0
      · simpa using hK2
      · have hI := integral_norm_sq_shiftDiff_le_of_lipschitz ha hf hK ht.1 ht.2
        rw [div_le_iff₀ ht0]
        nlinarith [mul_nonneg hK2 (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))])
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  unfold logEnergy
  linarith

/-! ### 6. The sampling inequality with the logarithmic weight -/

/-- The constant `4 (2a + 2 + 2π) e^{2π} e^{σ(2a+3)}` of the logarithmic sampling inequality. -/
def logSamplingConst (a σ : ℝ) : ℝ :=
  4 * (2 * a + 2 + 2 * π) * Real.exp (2 * π) * Real.exp (σ * (2 * a + 3))

theorem logSamplingConst_nonneg {a σ : ℝ} (ha : 0 ≤ a) : 0 ≤ logSamplingConst a σ := by
  unfold logSamplingConst; positivity

theorem four_mul_samplingConst_le {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 ≤ σ) :
    4 * samplingConst a σ ≤ logSamplingConst a σ := by
  unfold samplingConst logSamplingConst
  have hexp : Real.exp (2 * σ * a) ≤ Real.exp (σ * (2 * a + 3)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hπ := Real.pi_pos
  have h1 : (2 * a + 2 * π) * Real.exp (2 * σ * a) ≤
      (2 * a + 2 + 2 * π) * Real.exp (σ * (2 * a + 3)) :=
    mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (2 * π)).le
  nlinarith [h2]

theorem four_mul_exp_mul_samplingConst_le {a σ : ℝ} (ha : 0 ≤ a) :
    4 * (Real.exp σ / 2 * samplingConst (a + 1) σ) ≤ logSamplingConst a σ := by
  unfold samplingConst logSamplingConst
  have hexp : Real.exp σ * Real.exp (2 * σ * (a + 1)) = Real.exp (σ * (2 * a + 3)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h0 : 0 ≤ (2 * a + 2 + 2 * π) * Real.exp (2 * π) * Real.exp (σ * (2 * a + 3)) := by
    positivity
  calc 4 * (Real.exp σ / 2 *
        ((2 * (a + 1) + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * (a + 1))))
      = 2 * ((2 * a + 2 + 2 * π) * Real.exp (2 * π) *
          (Real.exp σ * Real.exp (2 * σ * (a + 1)))) := by ring
    _ = 2 * ((2 * a + 2 + 2 * π) * Real.exp (2 * π) * Real.exp (σ * (2 * a + 3))) := by
        rw [hexp]
    _ ≤ 4 * (2 * a + 2 + 2 * π) * Real.exp (2 * π) * Real.exp (σ * (2 * a + 3)) := by linarith

/-- **Sampling on logarithmically dense points.** Let the weights `m_q ≥ 0` of the points with
height in any unit window sum to at most `W`, let `|y_q| ≤ σ`, and let `f` have integrable
logarithmic energy density. Then
`Σ_{q ∈ s} m_q log(|x_q| + 5) |Φ(x_q + i y_q)|² ≤ W · 4 (2a + 2 + 2π) e^{2π} e^{σ(2a+3)} (E(f) + ∫|f|²)`. -/
theorem sum_weight_mul_log_mul_norm_sq_testTransform_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntervalSource a f) {ι : Type*} (x y m : ι → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hy : ∀ q, |y q| ≤ σ) (hm : ∀ q, 0 ≤ m q) {W : ℝ} (s : Finset ι)
    (hW : ∀ T : ℝ, ∀ t : Finset ι, t ⊆ s → (∀ q ∈ t, |x q - T| ≤ 1) → ∑ q ∈ t, m q ≤ W)
    (hG : IntervalIntegrable (fun t => (∫ u, ‖f (u + t) - f u‖ ^ 2) / t) volume 0 1) :
    ∑ q ∈ s, m q *
        (Real.log (|x q| + 5) * ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2) ≤
      W * (logSamplingConst a σ * (logEnergy f + ∫ u, ‖f u‖ ^ 2)) := by
  have hW0 : 0 ≤ W := by simpa using hW 0 ∅ (Finset.empty_subset _) (by simp)
  have hN0 : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hE0 := logEnergy_nonneg f
  set P : ι → ℝ := fun q => ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 with hP
  have hP0 : ∀ q, 0 ≤ P q := fun q => sq_nonneg _
  -- the unweighted part: the sampling inequality for `f`
  have hplain : ∑ q ∈ s, m q * P q ≤ W * (samplingConst a σ * ∫ u, ‖f u‖ ^ 2) :=
    sum_weight_mul_norm_sq_testTransform_le' ha hf x y m hσ hy hm s hW
  -- the kernel part: the sampling inequality for the translate differences, integrated `dt/t`
  have hker : ∑ q ∈ s, m q * (logKernel (x q) * P q) ≤
      W * (Real.exp σ / 2 * samplingConst (a + 1) σ * logEnergy f) := by
    have hInt : ∀ q ∈ s, IntervalIntegrable
        (fun t : ℝ => m q * ((1 - Real.cos (x q * t)) / t * P q)) volume 0 1 := fun q _ =>
      ((intervalIntegrable_one_sub_cos_div (x q) le_rfl zero_le_one).mul_const (P q)).const_mul
        (m q)
    have hLHS : ∑ q ∈ s, m q * (logKernel (x q) * P q) =
        ∫ t in (0:ℝ)..1, ∑ q ∈ s, m q * ((1 - Real.cos (x q * t)) / t * P q) := by
      rw [intervalIntegral.integral_finsetSum hInt]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
      rfl
    have hRHS : W * (Real.exp σ / 2 * samplingConst (a + 1) σ * logEnergy f) =
        ∫ t in (0:ℝ)..1, W * (Real.exp σ / 2 * samplingConst (a + 1) σ) *
          ((∫ u, ‖f (u + t) - f u‖ ^ 2) / t) := by
      rw [intervalIntegral.integral_const_mul]
      unfold logEnergy
      ring
    rw [hLHS, hRHS]
    refine intervalIntegral.integral_mono_on zero_le_one ?_ (hG.const_mul _) fun t ht => ?_
    · exact ⟨integrable_finsetSum _ fun q hq => (hInt q hq).1,
        integrable_finsetSum _ fun q hq => (hInt q hq).2⟩
    · rcases ht.1.eq_or_lt with rfl | ht0
      · simp
      · have hS := intervalSource_shiftDiff hf ht.1 ht.2
        have hsamp := sum_weight_mul_norm_sq_testTransform_le' (by linarith : 0 < a + 1) hS
          x y m hσ hy hm s hW
        have hee : Real.exp σ * Real.exp (-σ) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        have hterm : ∀ q ∈ s, m q * ((1 - Real.cos (x q * t)) / t * P q) ≤
            Real.exp σ / 2 / t *
              (m q * ‖testTransform (shiftDiff f t) ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2) := by
          intro q _
          have h1 := two_mul_exp_neg_mul_one_sub_cos_le (ξ := x q) (hy q) ht.1 ht.2
          have h2 : ‖testTransform (shiftDiff f t) ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 =
              ‖cexp (-(I * ((x q : ℂ) + (y q : ℂ) * I) * (t : ℂ))) - 1‖ ^ 2 * P q := by
            rw [testTransform_shiftDiff hf, norm_mul, mul_pow]
          have h3 : 2 * Real.exp (-σ) * (1 - Real.cos (x q * t)) * P q ≤
              ‖testTransform (shiftDiff f t) ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 := by
            rw [h2]
            exact mul_le_mul_of_nonneg_right h1 (hP0 q)
          have h4 : (1 - Real.cos (x q * t)) * P q ≤ Real.exp σ / 2 *
              ‖testTransform (shiftDiff f t) ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 := by
            have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ Real.exp σ / 2)
            have h6 : Real.exp σ / 2 * (2 * Real.exp (-σ) * (1 - Real.cos (x q * t)) * P q) =
                Real.exp σ * Real.exp (-σ) * ((1 - Real.cos (x q * t)) * P q) := by ring
            rw [h6, hee, one_mul] at h5
            exact h5
          calc m q * ((1 - Real.cos (x q * t)) / t * P q)
              = m q * ((1 - Real.cos (x q * t)) * P q) / t := by ring
            _ ≤ m q * (Real.exp σ / 2 *
                  ‖testTransform (shiftDiff f t) ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2) / t :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (hm q)) ht0.le
            _ = _ := by ring
        calc ∑ q ∈ s, m q * ((1 - Real.cos (x q * t)) / t * P q)
            ≤ ∑ q ∈ s, Real.exp σ / 2 / t *
                (m q * ‖testTransform (shiftDiff f t) ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2) :=
              Finset.sum_le_sum hterm
          _ = Real.exp σ / 2 / t *
                ∑ q ∈ s, m q * ‖testTransform (shiftDiff f t) ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 := by
              rw [Finset.mul_sum]
          _ ≤ Real.exp σ / 2 / t *
                (W * (samplingConst (a + 1) σ * ∫ u, ‖shiftDiff f t u‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hsamp (by positivity)
          _ = W * (Real.exp σ / 2 * samplingConst (a + 1) σ) *
                ((∫ u, ‖f (u + t) - f u‖ ^ 2) / t) := by
              simp only [shiftDiff]
              ring
  -- the logarithm is at most `4K + 4`
  have hstep : ∀ q ∈ s, m q * (Real.log (|x q| + 5) * P q) ≤
      4 * (m q * (logKernel (x q) * P q)) + 4 * (m q * P q) := by
    intro q _
    have h2 : Real.log (|x q| + 5) * P q ≤ (4 * logKernel (x q) + 4) * P q :=
      mul_le_mul_of_nonneg_right (log_abs_add_five_le (x q)) (hP0 q)
    have h3 := mul_le_mul_of_nonneg_left h2 (hm q)
    linarith
  have hc1 := four_mul_exp_mul_samplingConst_le (σ := σ) ha.le
  have hc2 := four_mul_samplingConst_le ha.le hσ
  calc ∑ q ∈ s, m q * (Real.log (|x q| + 5) * P q)
      ≤ ∑ q ∈ s, (4 * (m q * (logKernel (x q) * P q)) + 4 * (m q * P q)) :=
        Finset.sum_le_sum hstep
    _ = 4 * ∑ q ∈ s, m q * (logKernel (x q) * P q) + 4 * ∑ q ∈ s, m q * P q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ W * (4 * (Real.exp σ / 2 * samplingConst (a + 1) σ) * logEnergy f +
          4 * samplingConst a σ * ∫ u, ‖f u‖ ^ 2) := by linarith
    _ ≤ W * (logSamplingConst a σ * (logEnergy f + ∫ u, ‖f u‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hW0
        have h7 := mul_le_mul_of_nonneg_right hc1 hE0
        have h8 := mul_le_mul_of_nonneg_right hc2 hN0
        linarith

#print axioms sum_weight_mul_log_mul_norm_sq_testTransform_le
#print axioms logEnergy_le_of_lipschitz

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
