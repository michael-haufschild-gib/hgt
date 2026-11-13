import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveMeasureHamburgerRigidity
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockTailLowerBoundCompleteness
import GaloisForLFunctions.EulerFETransportTheory.MobiusInvertedOverRegularPrimes

/-!
# Point-mass discretizations of a Laplace density

Let `π ≥ 0` be a measurable density on `ℝ` with `π(y) ≤ 1_{[u₀,∞)}(y) e^y` (`u₀ ≥ 20`).  Cut
`[u₀, ∞)` into the unit blocks `J_m = (u₀ + m, u₀ + m + 1]` and each block into `M_m` cells
`I_{m,j}` of length `1/M_m` (`node`, `Cell`).  Put a point `u_{m,j}` in each cell with the cell
mass `w_{m,j} = ∫_{I_{m,j}} π` (`cellWeight`), and form the prime measure
`P = Σ_{i, r ≥ 1} (w_i / r) δ_{e^{r u_i}}` (`eulerPrimeMeasure`) of the real-weighted Euler product
`Π_i (1 - e^{-s u_i})^{-w_i}`.

* For `Re s > 1`:
  `∫ u^{-s} dP = Σ_{r ≥ 1} r⁻¹ ∫ e^{-r s y} π(y) dy + E(s)` (`measureDirichlet_eulerPrimeMeasure`),
  where `E = Σ_m E_m` and `E_m(s) = Σ_j Σ_r r⁻¹ ∫_{I_{m,j}} (e^{-rsu_{m,j}} - e^{-rsy}) π(y) dy`
  (`discretizationError`, `blockError`).
* Each `E_m` is holomorphic on `Re s > 0`; with `‖·‖` on `Re s ≥ σ₀` (`σ₀ u₀ ≥ 1`) bounded by
  `4 κ_m` and by `2 ‖s‖ κ_m / M_m`, `κ_m = e^{-σ₀(u₀+m)} ∫_{J_m} π` (`norm_blockError_le`,
  `norm_blockError_le_fine`).  Hence `E` is holomorphic on `Re s > 1/3` once `M_m ≥ e^{2(u₀+m)}`
  (`differentiableOn_discretizationError`).
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory.Discretization

/-! ## The prime measure of a real-weighted Euler product -/

/-- The prime-power measure `Σ_{i, r ≥ 1} (w_i / r) δ_{e^{r u_i}}` of `Π_i (1 - e^{-s u_i})^{-w_i}`. -/
def eulerPrimeMeasure {ι : Type*} (u w : ι → ℝ) : Measure ℝ :=
  Measure.sum fun p : ι × ℕ =>
    ENNReal.ofReal (w p.1 / ((p.2 : ℝ) + 1)) • Measure.dirac (Real.exp (((p.2 : ℝ) + 1) * u p.1))

instance sfinite_eulerPrimeMeasure {ι : Type*} [Countable ι] (u w : ι → ℝ) :
    SFinite (eulerPrimeMeasure u w) := by
  unfold eulerPrimeMeasure; infer_instance

theorem eulerPrimeMeasure_Iic_one {ι : Type*} {u w : ι → ℝ} (hu : ∀ i, 0 < u i) :
    eulerPrimeMeasure u w (Iic 1) = 0 := by
  rw [eulerPrimeMeasure, Measure.sum_apply _ measurableSet_Iic]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic, indicator_of_notMem, smul_zero]
  simp only [mem_Iic, not_le]
  exact Real.one_lt_exp_iff.mpr (mul_pos (by positivity) (hu p.1))

theorem ofReal_exp_cpow_neg (x : ℝ) (s : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ (-s) = cexp (-(s * x)) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  ring_nf

/-- **Integration against the prime measure.** -/
theorem integrable_eulerPrimeMeasure {ι : Type*} [Countable ι] {u w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hsum : Summable fun p : ι × ℕ => w p.1 / ((p.2 : ℝ) + 1) *
      ‖f (Real.exp (((p.2 : ℝ) + 1) * u p.1))‖) :
    Integrable f (eulerPrimeMeasure u w) := by
  rw [eulerPrimeMeasure]
  refine integrable_sum_measure_iff.2
    ⟨fun p => (integrable_dirac (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top, ?_⟩
  refine hsum.congr fun p => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by
    have := hw p.1; positivity), smul_eq_mul]

theorem integral_eulerPrimeMeasure {ι : Type*} [Countable ι] {u w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) {f : ℝ → ℂ} (hint : Integrable f (eulerPrimeMeasure u w)) :
    ∫ y, f y ∂(eulerPrimeMeasure u w) = ∑' p : ι × ℕ,
      ((w p.1 / ((p.2 : ℝ) + 1) : ℝ) : ℂ) * f (Real.exp (((p.2 : ℝ) + 1) * u p.1)) := by
  rw [eulerPrimeMeasure] at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun p => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by
    have := hw p.1; positivity), Complex.real_smul]

/-! ## Cells -/

/-- The nodes `u₀ + m + j/M_m`. -/
def node (u₀ : ℝ) (M : ℕ → ℕ) (m j : ℕ) : ℝ := u₀ + m + j / M m

/-- The cells `(m, j)`, `j < M_m`. -/
abbrev Cell (M : ℕ → ℕ) := Σ m : ℕ, Fin (M m)

/-- The mass `∫_{I_{m,j}} π` of a cell. -/
def cellWeight (u₀ : ℝ) (M : ℕ → ℕ) (π : ℝ → ℝ) (i : Cell M) : ℝ :=
  ∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1), π y

section Cells

variable {u₀ : ℝ} {M : ℕ → ℕ} {π : ℝ → ℝ}

theorem node_zero (u₀ : ℝ) (M : ℕ → ℕ) (m : ℕ) : node u₀ M m 0 = u₀ + m := by
  simp [node]

theorem node_top {M : ℕ → ℕ} (hM : ∀ m, 1 ≤ M m) (u₀ : ℝ) (m : ℕ) :
    node u₀ M m (M m) = u₀ + m + 1 := by
  have : (M m : ℝ) ≠ 0 := by have := hM m; positivity
  simp [node, div_self this]

theorem node_succ_sub {M : ℕ → ℕ} (u₀ : ℝ) (m j : ℕ) :
    node u₀ M m (j + 1) - node u₀ M m j = 1 / M m := by
  simp only [node]; push_cast; ring

theorem node_le_succ {M : ℕ → ℕ} (u₀ : ℝ) (m j : ℕ) : node u₀ M m j ≤ node u₀ M m (j + 1) := by
  have := node_succ_sub (M := M) u₀ m j
  have : (0 : ℝ) ≤ 1 / M m := by positivity
  linarith

theorem le_node {M : ℕ → ℕ} (u₀ : ℝ) (m j : ℕ) : u₀ + m ≤ node u₀ M m j := by
  simp only [node]
  have : (0 : ℝ) ≤ j / M m := by positivity
  linarith

theorem node_le {M : ℕ → ℕ} (hM : ∀ m, 1 ≤ M m) (u₀ : ℝ) (m : ℕ) {j : ℕ} (hj : j ≤ M m) :
    node u₀ M m j ≤ u₀ + m + 1 := by
  simp only [node]
  have hM0 : (0 : ℝ) < M m := by have := hM m; positivity
  have : (j : ℝ) / M m ≤ 1 := by rw [div_le_one hM0]; exact_mod_cast hj
  linarith

variable (hπm : Measurable π) (hπ0 : ∀ y, 0 ≤ π y)
  (hπle : ∀ y, π y ≤ (Ici u₀).indicator Real.exp y)
include hπm hπ0 hπle

theorem integrableOn_density (a b : ℝ) : IntegrableOn π (Icc a b) := by
  refine (Real.continuous_exp.integrableOn_Icc (a := a) (b := b)).mono'
    hπm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun y _ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hπ0 y)]
  refine (hπle y).trans ?_
  by_cases hy : y ∈ Ici u₀
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy]; exact (Real.exp_pos y).le

theorem intervalIntegrable_density (a b : ℝ) : IntervalIntegrable π volume a b :=
  (integrableOn_density hπm hπ0 hπle (min a b) (max a b)).intervalIntegrable

omit hπm hπle in
theorem cellWeight_nonneg (i : Cell M) : 0 ≤ cellWeight u₀ M π i :=
  intervalIntegral.integral_nonneg (node_le_succ u₀ i.1 i.2) fun y _ => hπ0 y

/-- A block is the sum of its cells: `Σ_j w_{m,j} = ∫_{J_m} π`. -/
theorem sum_cellWeight (hM : ∀ m, 1 ≤ M m) (m : ℕ) :
    ∑ j : Fin (M m), cellWeight u₀ M π ⟨m, j⟩ = ∫ y in (u₀ + m)..(u₀ + m + 1), π y := by
  have key := intervalIntegral.sum_integral_adjacent_intervals (f := π) (μ := volume)
    (a := node u₀ M m) (n := M m) fun k _ => intervalIntegrable_density hπm hπ0 hπle _ _
  rw [node_zero, node_top hM] at key
  rw [← key, ← Fin.sum_univ_eq_sum_range (fun j => ∫ y in node u₀ M m j..node u₀ M m (j + 1), π y)]
  rfl

theorem integral_block_le (m : ℕ) :
    ∫ y in (u₀ + m)..(u₀ + m + 1), π y ≤ Real.exp (u₀ + m + 1) := by
  calc ∫ y in (u₀ + m)..(u₀ + m + 1), π y ≤ ∫ _y in (u₀ + m)..(u₀ + m + 1), Real.exp (u₀ + m + 1) := by
        refine intervalIntegral.integral_mono_on (by linarith)
          (intervalIntegrable_density hπm hπ0 hπle _ _) intervalIntegrable_const fun y hy => ?_
        refine (hπle y).trans ?_
        by_cases h : y ∈ Ici u₀
        · rw [indicator_of_mem h]; exact Real.exp_le_exp.mpr hy.2
        · rw [indicator_of_notMem h]; exact (Real.exp_pos _).le
    _ = Real.exp (u₀ + m + 1) := by simp

omit hπm hπle in
theorem integral_block_nonneg (m : ℕ) : 0 ≤ ∫ y in (u₀ + m)..(u₀ + m + 1), π y :=
  intervalIntegral.integral_nonneg (by linarith) fun y _ => hπ0 y

/-- `Σ_{cells} w_i e^{-c(u₀ + m_i)}` converges for `c > 1`. -/
theorem summable_cellWeight_mul_exp (hM : ∀ m, 1 ≤ M m) {c : ℝ} (hc : 1 < c) :
    Summable fun i : Cell M => cellWeight u₀ M π i * Real.exp (-c * (u₀ + i.1)) := by
  refine (summable_sigma_of_nonneg fun i => mul_nonneg (cellWeight_nonneg hπ0 i)
    (Real.exp_pos _).le).2 ⟨fun m => (hasSum_fintype _).summable, ?_⟩
  have hq : Real.exp (-(c - 1)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun m => tsum_nonneg fun j => mul_nonneg
    (cellWeight_nonneg hπ0 _) (Real.exp_pos _).le) (fun m => ?_)
    ((summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left
      (Real.exp (-(c - 1) * u₀ + 1)))
  rw [tsum_fintype]
  dsimp only
  rw [← Finset.sum_mul, sum_cellWeight hπm hπ0 hπle hM]
  calc (∫ y in (u₀ + m)..(u₀ + m + 1), π y) * Real.exp (-c * (u₀ + m))
      ≤ Real.exp (u₀ + m + 1) * Real.exp (-c * (u₀ + m)) :=
        mul_le_mul_of_nonneg_right (integral_block_le hπm hπ0 hπle m) (Real.exp_pos _).le
    _ = Real.exp (-(c - 1) * u₀ + 1) * Real.exp (-(c - 1)) ^ m := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; ring_nf

end Cells

/-! ## Laplace transforms over the blocks -/

/-- The blocks `J_m` exhaust `(u₀, ∞)`: `Σ_m ∫_{J_m} f = ∫_{u₀}^∞ f` with norm-summable blocks. -/
theorem hasSum_integral_blocks {u₀ : ℝ} {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi u₀)) :
    HasSum (fun m : ℕ => ∫ y in (u₀ + m)..(u₀ + m + 1), f y) (∫ y in Ioi u₀, f y) ∧
      Summable fun m : ℕ => ∫ y in (u₀ + m)..(u₀ + m + 1), ‖f y‖ := by
  have hii : ∀ a b : ℝ, u₀ ≤ a → a ≤ b → IntervalIntegrable f volume a b := fun a b ha hab =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (hf.mono_set fun y hy => lt_of_le_of_lt ha hy.1)
  have hii' : ∀ a b : ℝ, u₀ ≤ a → a ≤ b → IntervalIntegrable (fun y => ‖f y‖) volume a b :=
    fun a b ha hab => (hii a b ha hab).norm
  have hadj : ∀ N : ℕ, ∑ m ∈ Finset.range N, ∫ y in (u₀ + m)..(u₀ + m + 1), f y =
      ∫ y in u₀..(u₀ + N), f y := by
    intro N
    have := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
      (a := fun k : ℕ => u₀ + k) (n := N) fun k _ => hii _ _ (by linarith [k.cast_nonneg' (α := ℝ)])
        (by push_cast; linarith)
    simpa [add_assoc] using this
  have hadj' : ∀ N : ℕ, ∑ m ∈ Finset.range N, ∫ y in (u₀ + m)..(u₀ + m + 1), ‖f y‖ =
      ∫ y in u₀..(u₀ + N), ‖f y‖ := by
    intro N
    have := intervalIntegral.sum_integral_adjacent_intervals (f := fun y => ‖f y‖) (μ := volume)
      (a := fun k : ℕ => u₀ + k) (n := N)
      fun k _ => hii' _ _ (by linarith [k.cast_nonneg' (α := ℝ)]) (by push_cast; linarith)
    simpa [add_assoc] using this
  have hnn : ∀ m : ℕ, 0 ≤ ∫ y in (u₀ + m)..(u₀ + m + 1), ‖f y‖ :=
    fun m => intervalIntegral.integral_nonneg (by linarith) fun y _ => norm_nonneg _
  have hsn : Summable fun m : ℕ => ∫ y in (u₀ + m)..(u₀ + m + 1), ‖f y‖ := by
    refine summable_of_sum_range_le (c := ∫ y in Ioi u₀, ‖f y‖) hnn fun N => ?_
    rw [hadj', intervalIntegral.integral_of_le (by linarith [N.cast_nonneg' (α := ℝ)])]
    exact setIntegral_mono_set hf.norm (Eventually.of_forall fun y => norm_nonneg _)
      (Eventually.of_forall Ioc_subset_Ioi_self)
  have hs : Summable fun m : ℕ => ∫ y in (u₀ + m)..(u₀ + m + 1), f y :=
    Summable.of_norm_bounded hsn fun m =>
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
  refine ⟨?_, hsn⟩
  have hlim : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, ∫ y in (u₀ + m)..(u₀ + m + 1), f y)
      atTop (𝓝 (∫ y in Ioi u₀, f y)) := by
    simp_rw [hadj]
    exact intervalIntegral_tendsto_integral_Ioi u₀ hf
      (tendsto_atTop_add_const_left _ u₀ tendsto_natCast_atTop_atTop)
  have := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim
  rw [← this]
  exact hs.hasSum

/-! ## Exponentials on a cell -/

theorem norm_cexp_neg_mul_ofReal (z : ℂ) (y : ℝ) : ‖cexp (-z * y)‖ = Real.exp (-(z.re * y)) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- Mean value bound: `‖e^{-zξ} - e^{-zy}‖ ≤ ‖z‖ e^{-a Re z} (b - a)` on `[a, b]`, `Re z ≥ 0`. -/
theorem norm_cexp_sub_le_fine {z : ℂ} (hz : 0 ≤ z.re) {a b ξ y : ℝ} (hξ : ξ ∈ Icc a b)
    (hy : y ∈ Icc a b) :
    ‖cexp (-z * ξ) - cexp (-z * y)‖ ≤ ‖z‖ * Real.exp (-(z.re * a)) * (b - a) := by
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t : ℝ => cexp (-z * t))
      (cexp (-z * t) * (-z * ((1 : ℝ) : ℂ))) (Icc a b) t := fun t _ =>
    (((hasDerivAt_id t).ofReal_comp.const_mul (-z)).cexp).hasDerivWithinAt
  have hb : ∀ t ∈ Icc a b, ‖cexp (-z * t) * (-z * ((1 : ℝ) : ℂ))‖ ≤
      ‖z‖ * Real.exp (-(z.re * a)) := fun t ht => by
    rw [norm_mul, norm_cexp_neg_mul_ofReal, Complex.ofReal_one, mul_one, norm_neg, mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [ht.1])) (norm_nonneg _)
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hξ
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hξ.1, hξ.2, hy.1, hy.2]

theorem norm_cexp_sub_le_crude {z : ℂ} (hz : 0 ≤ z.re) {a b ξ y : ℝ} (hξ : ξ ∈ Icc a b)
    (hy : y ∈ Icc a b) : ‖cexp (-z * ξ) - cexp (-z * y)‖ ≤ 2 * Real.exp (-(z.re * a)) := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_cexp_neg_mul_ofReal, norm_cexp_neg_mul_ofReal]
  have h1 : Real.exp (-(z.re * ξ)) ≤ Real.exp (-(z.re * a)) :=
    Real.exp_le_exp.mpr (by nlinarith [hξ.1])
  have h2 : Real.exp (-(z.re * y)) ≤ Real.exp (-(z.re * a)) :=
    Real.exp_le_exp.mpr (by nlinarith [hy.1])
  linarith

/-- A geometric tail: `‖Σ_n f_n‖ ≤ 2K e^{-c}` when `‖f_n‖ ≤ K e^{-(n+1)c}`, `c ≥ 1`. -/
theorem norm_tsum_le_of_le_exp {f : ℕ → ℂ} {K c : ℝ} (hK : 0 ≤ K) (hc : 1 ≤ c)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ K * Real.exp (-((n + 1) * c))) :
    Summable f ∧ ‖∑' n, f n‖ ≤ 2 * K * Real.exp (-c) := by
  set q := Real.exp (-c) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq2 : q ≤ 1 / 2 := by
    have h1 : Real.exp (-c) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    rw [hq]
    calc Real.exp (-c) ≤ (Real.exp 1)⁻¹ := h3 ▸ h1
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2
  have hexp : ∀ n : ℕ, K * Real.exp (-((n + 1) * c)) = K * q * q ^ n := fun n => by
    rw [hq, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; ring_nf
  have hs : HasSum (fun n : ℕ => K * Real.exp (-((n + 1) * c))) (K * q * (1 - q)⁻¹) := by
    simp_rw [hexp]
    exact (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left (K * q)
  refine ⟨Summable.of_norm_bounded hs.summable hf, (tsum_of_norm_bounded hs hf).trans ?_⟩
  have : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc K * q * (1 - q)⁻¹ ≤ K * q * 2 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * K * q := by ring

/-! ## The discretization error -/

/-- The cell error `r⁻¹ (w_i e^{-rsu_i} - ∫_{I_i} e^{-rsy} π(y) dy)`, `r = n + 1`. -/
def cellTerm (u₀ : ℝ) (M : ℕ → ℕ) (π : ℝ → ℝ) (u : Cell M → ℝ) (i : Cell M) (n : ℕ)
    (s : ℂ) : ℂ :=
  1 / ((n : ℂ) + 1) * ((cellWeight u₀ M π i : ℂ) * cexp (-(((n : ℂ) + 1) * s) * u i) -
    ∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1),
      cexp (-(((n : ℂ) + 1) * s) * y) * (π y : ℂ))

/-- The block error `E_m(s) = Σ_j Σ_r` (cell errors). -/
def blockError (u₀ : ℝ) (M : ℕ → ℕ) (π : ℝ → ℝ) (u : Cell M → ℝ) (m : ℕ) (s : ℂ) : ℂ :=
  ∑ j : Fin (M m), ∑' n : ℕ, cellTerm u₀ M π u ⟨m, j⟩ n s

/-- The discretization error `E(s) = Σ_m E_m(s)`. -/
def discretizationError (u₀ : ℝ) (M : ℕ → ℕ) (π : ℝ → ℝ) (u : Cell M → ℝ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, blockError u₀ M π u m s

section Errors

variable {u₀ : ℝ} {M : ℕ → ℕ} {π : ℝ → ℝ} {u : Cell M → ℝ}
  (hπm : Measurable π) (hπ0 : ∀ y, 0 ≤ π y) (hπle : ∀ y, π y ≤ (Ici u₀).indicator Real.exp y)
  (hM : ∀ m, 1 ≤ M m) (hu : ∀ i : Cell M, u i ∈ Icc (node u₀ M i.1 i.2) (node u₀ M i.1 (i.2 + 1)))
  (hu₀ : 0 ≤ u₀)
include hπm hπ0 hπle

theorem intervalIntegrable_density_complex (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => (π y : ℂ)) volume a b := by
  have h : IntegrableOn π (uIcc a b) := integrableOn_density hπm hπ0 hπle (min a b) (max a b)
  exact IntegrableOn.intervalIntegrable (Integrable.ofReal h)

theorem intervalIntegrable_cexp_mul_density (z : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => cexp (-z * y) * (π y : ℂ)) volume a b :=
  (intervalIntegrable_density_complex hπm hπ0 hπle a b).continuousOn_mul (by fun_prop)

/-- `r⁻¹ ∫_{I_i} (e^{-rsu_i} - e^{-rsy}) π(y) dy`. -/
theorem cellTerm_eq (i : Cell M) (n : ℕ) (s : ℂ) :
    cellTerm u₀ M π u i n s = 1 / ((n : ℂ) + 1) *
      ∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1),
        (cexp (-(((n : ℂ) + 1) * s) * u i) - cexp (-(((n : ℂ) + 1) * s) * y)) * (π y : ℂ) := by
  rw [cellTerm]
  congr 1
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_density_complex hπm hπ0 hπle _ _).const_mul _)
    (intervalIntegrable_cexp_mul_density hπm hπ0 hπle _ _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, cellWeight, mul_comm]

/-- Integrating a bounded factor against `π` over a cell. -/
theorem norm_integral_cell_le {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℂ} {K : ℝ}
    (hg : ∀ y ∈ Icc a b, ‖g y‖ ≤ K) :
    ‖∫ y in a..b, g y * (π y : ℂ)‖ ≤ K * ∫ y in a..b, π y := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall fun y hy => ?_)
    ((intervalIntegrable_density hπm hπ0 hπle a b).const_mul K)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hπ0 y)]
  exact mul_le_mul_of_nonneg_right (hg y ⟨hy.1.le, hy.2⟩) (hπ0 y)

omit hπm hπ0 hπle in
theorem exp_cell_le (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) (i : Cell M)
    (n : ℕ) :
    Real.exp (-((((n : ℂ) + 1) * s).re * node u₀ M i.1 i.2)) ≤
      Real.exp (-((n + 1) * (σ₀ * (u₀ + i.1)))) := by
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  have hre : (((n : ℂ) + 1) * s).re = ((n : ℝ) + 1) * s.re := by simp
  rw [hre, mul_assoc]
  have ha := le_node (M := M) u₀ i.1 i.2
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hn
  have hm : (0 : ℝ) ≤ u₀ + i.1 := add_nonneg hu₀ (Nat.cast_nonneg _)
  exact mul_le_mul hs ha hm (hσ₀.trans hs)

include hu in
/-- Crude cell bound `‖cell error‖ ≤ 2 w_i e^{-r σ₀ (u₀ + m)}` on `Re s ≥ σ₀`. -/
theorem norm_cellTerm_le (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {s : ℂ} (hs : σ₀ ≤ s.re)
    (i : Cell M) (n : ℕ) :
    ‖cellTerm u₀ M π u i n s‖ ≤
      2 * cellWeight u₀ M π i * Real.exp (-((n + 1) * (σ₀ * (u₀ + i.1)))) := by
  have hz0 : 0 ≤ (((n : ℂ) + 1) * s).re := by
    have : (((n : ℂ) + 1) * s).re = ((n : ℝ) + 1) * s.re := by simp
    rw [this]; exact mul_nonneg (by positivity) (hσ₀.trans hs)
  have hab := node_le_succ (M := M) u₀ i.1 i.2
  have hn1 : ‖1 / ((n : ℂ) + 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, show ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 by
      exact_mod_cast Complex.norm_natCast (n + 1)]
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h2 := norm_integral_cell_le hπm hπ0 hπle hab (g := fun y : ℝ =>
    cexp (-(((n : ℂ) + 1) * s) * u i) - cexp (-(((n : ℂ) + 1) * s) * y))
    fun y hy => norm_cexp_sub_le_crude hz0 (hu i) hy
  have h3 := exp_cell_le hu₀ hσ₀ hs i n
  have hw := cellWeight_nonneg hπ0 (u₀ := u₀) i
  rw [cellTerm_eq hπm hπ0 hπle, norm_mul]
  calc ‖1 / ((n : ℂ) + 1)‖ * ‖∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1),
        (cexp (-(((n : ℂ) + 1) * s) * u i) - cexp (-(((n : ℂ) + 1) * s) * y)) * (π y : ℂ)‖
      ≤ 1 * (2 * Real.exp (-((((n : ℂ) + 1) * s).re * node u₀ M i.1 i.2)) *
          cellWeight u₀ M π i) := mul_le_mul hn1 h2 (norm_nonneg _) zero_le_one
    _ ≤ 2 * cellWeight u₀ M π i * Real.exp (-((n + 1) * (σ₀ * (u₀ + i.1)))) := by
        rw [one_mul, mul_right_comm]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)

include hu in
/-- Fine cell bound `‖cell error‖ ≤ (‖s‖/M_m) w_i e^{-r σ₀ (u₀ + m)}` on `Re s ≥ σ₀`. -/
theorem norm_cellTerm_le_fine (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {s : ℂ} (hs : σ₀ ≤ s.re)
    (i : Cell M) (n : ℕ) :
    ‖cellTerm u₀ M π u i n s‖ ≤
      ‖s‖ / M i.1 * cellWeight u₀ M π i * Real.exp (-((n + 1) * (σ₀ * (u₀ + i.1)))) := by
  have hz0 : 0 ≤ (((n : ℂ) + 1) * s).re := by
    have : (((n : ℂ) + 1) * s).re = ((n : ℝ) + 1) * s.re := by simp
    rw [this]; exact mul_nonneg (by positivity) (hσ₀.trans hs)
  have hab := node_le_succ (M := M) u₀ i.1 i.2
  have hlen := node_succ_sub (M := M) u₀ i.1 i.2
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
  have h2 := norm_integral_cell_le hπm hπ0 hπle hab (g := fun y : ℝ =>
    cexp (-(((n : ℂ) + 1) * s) * u i) - cexp (-(((n : ℂ) + 1) * s) * y))
    fun y hy => norm_cexp_sub_le_fine hz0 (hu i) hy
  have h3 := exp_cell_le hu₀ hσ₀ hs i n
  have hw := cellWeight_nonneg hπ0 (u₀ := u₀) i
  rw [hlen, norm_mul, hnorm] at h2
  rw [cellTerm_eq hπm hπ0 hπle, norm_mul, norm_div, norm_one, hnorm]
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hM0 : (0 : ℝ) ≤ 1 / (M i.1 : ℝ) := by positivity
  calc 1 / ((n : ℝ) + 1) * ‖∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1),
        (cexp (-(((n : ℂ) + 1) * s) * u i) - cexp (-(((n : ℂ) + 1) * s) * y)) * (π y : ℂ)‖
      ≤ 1 / ((n : ℝ) + 1) * (((n : ℝ) + 1) * ‖s‖ *
          Real.exp (-((((n : ℂ) + 1) * s).re * node u₀ M i.1 i.2)) * (1 / M i.1) *
            cellWeight u₀ M π i) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ‖s‖ / M i.1 * cellWeight u₀ M π i *
          Real.exp (-((((n : ℂ) + 1) * s).re * node u₀ M i.1 i.2)) := by
        field_simp
    _ ≤ ‖s‖ / M i.1 * cellWeight u₀ M π i * Real.exp (-((n + 1) * (σ₀ * (u₀ + i.1)))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

include hu in
theorem norm_tsum_cellTerm_le (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσu : 1 ≤ σ₀ * u₀)
    {s : ℂ} (hs : σ₀ ≤ s.re) (i : Cell M) :
    ‖∑' n, cellTerm u₀ M π u i n s‖ ≤
      4 * cellWeight u₀ M π i * Real.exp (-(σ₀ * (u₀ + i.1))) := by
  have hc : 1 ≤ σ₀ * (u₀ + i.1) := by
    have : 0 ≤ σ₀ * (i.1 : ℝ) := mul_nonneg hσ₀ (Nat.cast_nonneg _)
    nlinarith
  have hw := cellWeight_nonneg hπ0 (u₀ := u₀) i
  have h := (norm_tsum_le_of_le_exp (K := 2 * cellWeight u₀ M π i) (by positivity) hc
    fun n => norm_cellTerm_le hπm hπ0 hπle hu hu₀ hσ₀ hs i n).2
  linarith

include hu in
theorem norm_tsum_cellTerm_le_fine (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσu : 1 ≤ σ₀ * u₀)
    {s : ℂ} (hs : σ₀ ≤ s.re) (i : Cell M) :
    ‖∑' n, cellTerm u₀ M π u i n s‖ ≤
      2 * (‖s‖ / M i.1) * cellWeight u₀ M π i * Real.exp (-(σ₀ * (u₀ + i.1))) := by
  have hc : 1 ≤ σ₀ * (u₀ + i.1) := by
    have : 0 ≤ σ₀ * (i.1 : ℝ) := mul_nonneg hσ₀ (Nat.cast_nonneg _)
    nlinarith
  have hw := cellWeight_nonneg hπ0 (u₀ := u₀) i
  have h := (norm_tsum_le_of_le_exp (K := ‖s‖ / M i.1 * cellWeight u₀ M π i) (by positivity) hc
    fun n => norm_cellTerm_le_fine hπm hπ0 hπle hu hu₀ hσ₀ hs i n).2
  linarith

include hu hM in
/-- **Crude block bound** `‖E_m(s)‖ ≤ 4 e^{-σ₀(u₀+m)} ∫_{J_m} π` on `Re s ≥ σ₀`. -/
theorem norm_blockError_le (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσu : 1 ≤ σ₀ * u₀)
    {s : ℂ} (hs : σ₀ ≤ s.re) (m : ℕ) :
    ‖blockError u₀ M π u m s‖ ≤
      4 * Real.exp (-(σ₀ * (u₀ + m))) * ∫ y in (u₀ + m)..(u₀ + m + 1), π y := by
  rw [blockError, ← sum_cellWeight hπm hπ0 hπle hM, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_tsum_cellTerm_le hπm hπ0 hπle hu hu₀ hσ₀ hσu hs ⟨m, j⟩).trans (le_of_eq ?_)
  ring

include hu hM in
/-- **Fine block bound** `‖E_m(s)‖ ≤ 2 (‖s‖/M_m) e^{-σ₀(u₀+m)} ∫_{J_m} π` on `Re s ≥ σ₀`. -/
theorem norm_blockError_le_fine (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσu : 1 ≤ σ₀ * u₀)
    {s : ℂ} (hs : σ₀ ≤ s.re) (m : ℕ) :
    ‖blockError u₀ M π u m s‖ ≤
      2 * (‖s‖ / M m) * Real.exp (-(σ₀ * (u₀ + m))) * ∫ y in (u₀ + m)..(u₀ + m + 1), π y := by
  rw [blockError, ← sum_cellWeight hπm hπ0 hπle hM, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_tsum_cellTerm_le_fine hπm hπ0 hπle hu hu₀ hσ₀ hσu hs ⟨m, j⟩).trans (le_of_eq ?_)
  ring

/-! ## Holomorphy -/

theorem differentiable_cellTerm (hu₀ : 0 ≤ u₀) (i : Cell M) (n : ℕ) :
    Differentiable ℂ (cellTerm u₀ M π u i n) := by
  have hab := node_le_succ (M := M) u₀ i.1 i.2
  have ha : 0 ≤ node u₀ M i.1 i.2 :=
    le_trans (add_nonneg hu₀ (Nat.cast_nonneg _)) (le_node u₀ i.1 i.2)
  have hf : IntegrableOn (fun y : ℝ => (π y : ℂ))
      (Ioc (node u₀ M i.1 i.2) (node u₀ M i.1 (i.2 + 1))) :=
    (Integrable.ofReal ((integrableOn_density hπm hπ0 hπle _ _).mono_set Ioc_subset_Icc_self))
  have hD := (RHTower.differentiable_compactLaplaceIntegral ha hab hf).comp
    (by fun_prop : Differentiable ℂ fun s : ℂ => ((n : ℂ) + 1) * s)
  have he : cellTerm u₀ M π u i n = fun s => 1 / ((n : ℂ) + 1) *
      ((cellWeight u₀ M π i : ℂ) * cexp (-(((n : ℂ) + 1) * s) * u i) -
        ((fun z : ℂ => ∫ L in Ioc (node u₀ M i.1 i.2) (node u₀ M i.1 (i.2 + 1)),
          cexp (-z * L) * (π L : ℂ)) ∘ fun s : ℂ => ((n : ℂ) + 1) * s) s) := by
    funext s
    rw [cellTerm, intervalIntegral.integral_of_le hab]
    rfl
  rw [he]
  exact (differentiable_const _).mul ((by fun_prop : Differentiable ℂ fun s : ℂ =>
    (cellWeight u₀ M π i : ℂ) * cexp (-(((n : ℂ) + 1) * s) * u i)).sub hD)

omit hπm hπ0 hπle in
theorem summable_mul_exp_succ {K c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => K * Real.exp (-((n + 1) * c)) := by
  have hq : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine ((summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left
    (K * Real.exp (-c))).congr fun n => ?_
  rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; ring_nf

include hu in
theorem differentiableOn_tsum_cellTerm (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀)
    (hσu : 1 ≤ σ₀ * u₀) (i : Cell M) :
    DifferentiableOn ℂ (fun s => ∑' n, cellTerm u₀ M π u i n s) {s : ℂ | σ₀ < s.re} := by
  have hc : 0 < σ₀ * (u₀ + i.1) := by
    have : 0 ≤ σ₀ * (i.1 : ℝ) := mul_nonneg hσ₀ (Nat.cast_nonneg _)
    nlinarith
  exact differentiableOn_tsum_of_summable_norm (summable_mul_exp_succ hc)
    (fun n => (differentiable_cellTerm hπm hπ0 hπle hu₀ i n).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
    fun n s hs => norm_cellTerm_le hπm hπ0 hπle hu hu₀ hσ₀ (le_of_lt hs) i n

include hu in
theorem differentiableOn_blockError (hu₀ : 0 ≤ u₀) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀)
    (hσu : 1 ≤ σ₀ * u₀) (m : ℕ) :
    DifferentiableOn ℂ (blockError u₀ M π u m) {s : ℂ | σ₀ < s.re} := by
  have h := DifferentiableOn.fun_sum (u := Finset.univ) (A := fun (j : Fin (M m)) s =>
    ∑' n, cellTerm u₀ M π u ⟨m, j⟩ n s)
    fun j _ => differentiableOn_tsum_cellTerm hπm hπ0 hπle hu hu₀ hσ₀ hσu ⟨m, j⟩
  exact h

include hu hM in
/-- **The discretization error is holomorphic on `Re s > 1/3`** once `M_m ≥ e^{u₀+m}`. -/
theorem differentiableOn_discretizationError (hu₀ : 3 ≤ u₀)
    (hMbig : ∀ m : ℕ, Real.exp (u₀ + m) ≤ M m) :
    DifferentiableOn ℂ (discretizationError u₀ M π u) {s : ℂ | 1 / 3 < s.re} := by
  have hu0 : 0 ≤ u₀ := by linarith
  have hσu : 1 ≤ 1 / 3 * u₀ := by linarith
  intro s₀ hs₀
  set R := ‖s₀‖ + 1 with hR
  set U : Set ℂ := {s : ℂ | 1 / 3 < s.re} ∩ {s : ℂ | ‖s‖ < R} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hq : Real.exp (-(1 / 3 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hbound : ∀ m : ℕ, ∀ s ∈ U, ‖blockError u₀ M π u m s‖ ≤
      2 * R * Real.exp 1 * Real.exp (-(1 / 3 : ℝ)) ^ m := by
    intro m s hs
    have hfine := norm_blockError_le_fine hπm hπ0 hπle hM hu hu0 (σ₀ := 1 / 3) (by norm_num) hσu
      (le_of_lt hs.1) m
    have hI := integral_block_le hπm hπ0 hπle (u₀ := u₀) m
    have hI0 := integral_block_nonneg hπ0 (u₀ := u₀) m
    have hM0 : (0 : ℝ) < M m := lt_of_lt_of_le (Real.exp_pos _) (hMbig m)
    have hsR : ‖s‖ ≤ R := hs.2.le
    refine hfine.trans ?_
    have h1 : ‖s‖ / M m ≤ R * Real.exp (-(u₀ + m)) := by
      rw [Real.exp_neg, div_le_iff₀ hM0]
      calc ‖s‖ ≤ R := hsR
        _ = R * (Real.exp (u₀ + m))⁻¹ * Real.exp (u₀ + m) := by
            field_simp
        _ ≤ R * (Real.exp (u₀ + m))⁻¹ * M m :=
            mul_le_mul_of_nonneg_left (hMbig m) (by positivity)
    have hR0 : 0 ≤ 2 * R * Real.exp 1 := mul_nonneg (mul_nonneg (by norm_num)
      (by rw [hR]; positivity)) (Real.exp_pos 1).le
    calc 2 * (‖s‖ / M m) * Real.exp (-(1 / 3 * (u₀ + m))) * ∫ y in (u₀ + m)..(u₀ + m + 1), π y
        ≤ 2 * (R * Real.exp (-(u₀ + m))) * Real.exp (-(1 / 3 * (u₀ + m))) *
            Real.exp (u₀ + m + 1) := by
          gcongr
      _ = 2 * R * Real.exp 1 * Real.exp (-(1 / 3 * (u₀ + m))) := by
          have e : Real.exp (-(u₀ + m)) * Real.exp (u₀ + m + 1) = Real.exp 1 := by
            rw [← Real.exp_add]; ring_nf
          calc 2 * (R * Real.exp (-(u₀ + m))) * Real.exp (-(1 / 3 * (u₀ + m))) *
                Real.exp (u₀ + m + 1)
              = 2 * R * (Real.exp (-(u₀ + m)) * Real.exp (u₀ + m + 1)) *
                  Real.exp (-(1 / 3 * (u₀ + m))) := by ring
            _ = 2 * R * Real.exp 1 * Real.exp (-(1 / 3 * (u₀ + m))) := by rw [e]
      _ ≤ 2 * R * Real.exp 1 * Real.exp (-(1 / 3 : ℝ)) ^ m := by
          rw [← Real.exp_nat_mul]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hR0
          nlinarith
  have hdiffU : DifferentiableOn ℂ (discretizationError u₀ M π u) U :=
    differentiableOn_tsum_of_summable_norm
      ((summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left (2 * R * Real.exp 1))
      (fun m => (differentiableOn_blockError hπm hπ0 hπle hu hu0 (σ₀ := 1 / 3) (by norm_num)
        hσu m).mono fun s hs => hs.1)
      hUo hbound
  have hs₀U : s₀ ∈ U := ⟨hs₀, by show ‖s₀‖ < R; rw [hR]; linarith⟩
  exact (hdiffU.differentiableAt (hUo.mem_nhds hs₀U)).differentiableWithinAt

/-! ## The Dirichlet transform of the prime measure -/

omit hπm hπ0 hπle in
theorem exp_succ_le_geom {σ : ℝ} (hσ : 0 ≤ σ) (m n : ℕ) :
    Real.exp (-((n + 1) * (σ * (u₀ + m)))) ≤
      Real.exp (-σ * (u₀ + m)) * Real.exp (-(σ * u₀)) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have : 0 ≤ σ * (n : ℝ) * m := by positivity
  nlinarith

omit hπm in
theorem density_eq_zero {y : ℝ} (hy : y ∉ Ici u₀) : π y = 0 := by
  have h := hπle y
  rw [indicator_of_notMem hy] at h
  exact le_antisymm h (hπ0 y)

theorem integrable_cexp_mul_density {z : ℂ} (hz : 1 < z.re) :
    Integrable fun y : ℝ => cexp (-(z * y)) * (π y : ℂ) := by
  refine (MobiusInverted.integrable_indicator_exp_neg (u₀ := u₀) (by linarith : 0 < z.re - 1)).mono'
    ((by fun_prop : Continuous fun y : ℝ => cexp (-(z * y))).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp hπm).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [MobiusInverted.norm_cexp_mul_ofReal, abs_of_nonneg (hπ0 y)]
  by_cases hy : y ∈ Ici u₀
  · have h := hπle y
    rw [indicator_of_mem hy] at h ⊢
    calc Real.exp (-z.re * y) * π y ≤ Real.exp (-z.re * y) * Real.exp y :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = Real.exp (-(z.re - 1) * y) := by rw [← Real.exp_add]; ring_nf
  · rw [density_eq_zero hπ0 hπle hy, mul_zero, indicator_of_notMem hy]

include hM in
/-- The whole-line Laplace transform splits over the cells. -/
theorem hasSum_integral_cells {z : ℂ} (hz : 1 < z.re) :
    Summable (fun i : Cell M => ∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1),
      cexp (-z * y) * (π y : ℂ)) ∧
    ∑' i : Cell M, (∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1), cexp (-z * y) * (π y : ℂ)) =
      ∫ y : ℝ, cexp (-(z * y)) * (π y : ℂ) := by
  have hint := integrable_cexp_mul_density hπm hπ0 hπle (u₀ := u₀) hz
  set f : ℝ → ℂ := fun y => cexp (-z * y) * (π y : ℂ) with hf
  have hfe : (fun y : ℝ => cexp (-(z * y)) * (π y : ℂ)) = f := by
    funext y; simp only [hf, neg_mul]
  rw [hfe] at hint ⊢
  have hzre : 0 ≤ z.re := by linarith
  -- the cells are norm-summable
  have hcell : ∀ i : Cell M, ‖∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1), f y‖ ≤
      cellWeight u₀ M π i * Real.exp (-z.re * (u₀ + i.1)) := by
    intro i
    have hab := node_le_succ (M := M) u₀ i.1 i.2
    have h := norm_integral_cell_le hπm hπ0 hπle hab (g := fun y : ℝ => cexp (-z * y))
      (K := Real.exp (-z.re * (u₀ + i.1))) fun y hy => by
        rw [norm_cexp_neg_mul_ofReal]
        refine Real.exp_le_exp.mpr ?_
        have := le_node (M := M) u₀ i.1 i.2
        nlinarith [hy.1]
    rw [mul_comm] at h
    exact h
  have hsum : Summable fun i : Cell M =>
      ∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1), f y :=
    Summable.of_norm_bounded (summable_cellWeight_mul_exp hπm hπ0 hπle hM hz) hcell
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_sigma, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici u₀)
    (fun y hy => by
      show cexp (-z * y) * (π y : ℂ) = 0
      rw [density_eq_zero hπ0 hπle hy]; simp),
    integral_Ici_eq_integral_Ioi, ← (hasSum_integral_blocks hint.integrableOn).1.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [tsum_fintype]
  have key := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := node u₀ M m) (n := M m) fun k _ =>
      intervalIntegrable_cexp_mul_density hπm hπ0 hπle z _ _
  rw [node_zero, node_top hM] at key
  rw [← key, ← Fin.sum_univ_eq_sum_range (fun j => ∫ y in node u₀ M m j..node u₀ M m (j + 1), f y)]

include hu hM in
/-- **The Dirichlet transform of the discretized prime measure** on `Re s > 1`: the log-Euler series
`Σ_{i,r} (w_i/r) e^{-rsu_i}` converges absolutely to `∫ u^{-s} dP`, which is the prime-power Laplace
sum of `π` plus the discretization error. -/
theorem measureDirichlet_eulerPrimeMeasure (hu₀ : 3 ≤ u₀) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Cell M × ℕ => ((cellWeight u₀ M π p.1 / ((p.2 : ℝ) + 1) : ℝ) : ℂ) *
        cexp (-(s * ((((p.2 : ℝ) + 1) * u p.1 : ℝ) : ℂ))))
      (measureDirichlet (eulerPrimeMeasure u (cellWeight u₀ M π)) s) ∧
    measureDirichlet (eulerPrimeMeasure u (cellWeight u₀ M π)) s =
      (∑' n : ℕ, 1 / ((n : ℂ) + 1) * ∫ y : ℝ, cexp (-(((n : ℂ) + 1) * s * y)) * (π y : ℂ)) +
        discretizationError u₀ M π u s := by
  have hu0 : 0 ≤ u₀ := by linarith
  set σ := s.re with hσ
  have hσ0 : 0 ≤ σ := by linarith
  set q := Real.exp (-(σ * u₀)) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hw := cellWeight_nonneg hπ0 (u₀ := u₀) (M := M)
  -- the dominating family `β(i, n) = w_i e^{-σ(u₀+m)} q^n`
  set β : Cell M × ℕ → ℝ := fun p =>
    cellWeight u₀ M π p.1 * Real.exp (-σ * (u₀ + p.1.1)) * q ^ p.2 with hβdef
  have hβ : Summable β :=
    (summable_cellWeight_mul_exp hπm hπ0 hπle hM hs).mul_of_nonneg
      (summable_geometric_of_lt_one (Real.exp_pos _).le hq1)
      (fun i => mul_nonneg (hw i) (Real.exp_pos _).le) (fun n => pow_nonneg (Real.exp_pos _).le n)
  have hgeo : ∀ p : Cell M × ℕ, cellWeight u₀ M π p.1 *
      Real.exp (-((p.2 + 1) * (σ * (u₀ + p.1.1)))) ≤ β p := fun p => by
    simp only [hβdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left (exp_succ_le_geom hσ0 p.1.1 p.2) (hw p.1)
  -- the atoms `T` and the cell integrals `S`
  set T : Cell M × ℕ → ℂ := fun p => ((cellWeight u₀ M π p.1 / ((p.2 : ℝ) + 1) : ℝ) : ℂ) *
    cexp (-(s * ((((p.2 : ℝ) + 1) * u p.1 : ℝ) : ℂ))) with hTdef
  set S : Cell M × ℕ → ℂ := fun p => 1 / ((p.2 : ℂ) + 1) *
    ∫ y in node u₀ M p.1.1 p.1.2..node u₀ M p.1.1 (p.1.2 + 1),
      cexp (-(((p.2 : ℂ) + 1) * s) * y) * (π y : ℂ) with hSdef
  have hn1 : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1)‖ ≤ 1 := fun n => by
    rw [norm_div, norm_one, show ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 by
      exact_mod_cast Complex.norm_natCast (n + 1)]
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hTn : ∀ p : Cell M × ℕ, ‖T p‖ = cellWeight u₀ M π p.1 / ((p.2 : ℝ) + 1) *
      Real.exp (-(σ * (((p.2 : ℝ) + 1) * u p.1))) := fun p => by
    simp only [hTdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
      have := hw p.1; positivity), Complex.norm_exp]
    congr 2
    simp [hσ]
  have hTb : ∀ p, ‖T p‖ ≤ β p := fun p => by
    rw [hTn]
    refine le_trans ?_ (hgeo p)
    have hn : (1 : ℝ) ≤ (p.2 : ℝ) + 1 := by linarith [(p.2.cast_nonneg : (0 : ℝ) ≤ p.2)]
    have hui := (hu p.1).1
    have hle := le_node (M := M) u₀ p.1.1 p.1.2
    calc cellWeight u₀ M π p.1 / ((p.2 : ℝ) + 1) * Real.exp (-(σ * (((p.2 : ℝ) + 1) * u p.1)))
        ≤ cellWeight u₀ M π p.1 * Real.exp (-(σ * (((p.2 : ℝ) + 1) * u p.1))) :=
          mul_le_mul_of_nonneg_right (div_le_self (hw p.1) hn) (Real.exp_pos _).le
      _ ≤ cellWeight u₀ M π p.1 * Real.exp (-((p.2 + 1) * (σ * (u₀ + p.1.1)))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hw p.1)
          have h1 : u₀ + p.1.1 ≤ u p.1 := hle.trans hui
          have h2 : (0 : ℝ) ≤ (p.2 : ℝ) + 1 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hσ0 h2)]
  have hSb : ∀ p, ‖S p‖ ≤ β p := fun p => by
    refine le_trans ?_ (hgeo p)
    have hab := node_le_succ (M := M) u₀ p.1.1 p.1.2
    have hz0 : 0 ≤ (((p.2 : ℂ) + 1) * s).re := by
      have : (((p.2 : ℂ) + 1) * s).re = ((p.2 : ℝ) + 1) * s.re := by simp
      rw [this]; positivity
    have hI := norm_integral_cell_le hπm hπ0 hπle hab (g := fun y : ℝ =>
      cexp (-(((p.2 : ℂ) + 1) * s) * y))
      (K := Real.exp (-((((p.2 : ℂ) + 1) * s).re * node u₀ M p.1.1 p.1.2))) fun y hy => by
        rw [norm_cexp_neg_mul_ofReal]
        exact Real.exp_le_exp.mpr (by nlinarith [hy.1])
    have h3 := exp_cell_le hu0 hσ0 (le_refl σ) p.1 p.2
    simp only [hSdef]
    rw [norm_mul]
    calc ‖1 / ((p.2 : ℂ) + 1)‖ * ‖∫ y in node u₀ M p.1.1 p.1.2..node u₀ M p.1.1 (p.1.2 + 1),
          cexp (-(((p.2 : ℂ) + 1) * s) * y) * (π y : ℂ)‖
        ≤ 1 * (Real.exp (-((((p.2 : ℂ) + 1) * s).re * node u₀ M p.1.1 p.1.2)) *
            cellWeight u₀ M π p.1) := mul_le_mul (hn1 p.2) hI (norm_nonneg _) zero_le_one
      _ ≤ cellWeight u₀ M π p.1 * Real.exp (-((p.2 + 1) * (σ * (u₀ + p.1.1)))) := by
          rw [one_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left h3 (hw p.1)
  have hT : Summable T := Summable.of_norm_bounded hβ hTb
  have hS : Summable S := Summable.of_norm_bounded hβ hSb
  -- the Dirichlet transform is the atom series
  have hP : measureDirichlet (eulerPrimeMeasure u (cellWeight u₀ M π)) s = ∑' p, T p := by
    have hint : Integrable (fun x : ℝ => (x : ℂ) ^ (-s)) (eulerPrimeMeasure u (cellWeight u₀ M π)) :=
      integrable_eulerPrimeMeasure hw (hT.norm.congr fun p => by
        rw [hTn, ofReal_exp_cpow_neg, Complex.norm_exp]
        congr 2
        simp [hσ])
    rw [measureDirichlet, integral_eulerPrimeMeasure hw hint]
    refine tsum_congr fun p => ?_
    rw [ofReal_exp_cpow_neg]
  refine ⟨hP ▸ hT.hasSum, ?_⟩
  -- the Laplace sum is the cell sum
  have hF : ∀ n : ℕ, 1 / ((n : ℂ) + 1) * ∫ y : ℝ, cexp (-(((n : ℂ) + 1) * s * y)) * (π y : ℂ) =
      ∑' i : Cell M, S (i, n) := by
    intro n
    have hre : 1 < (((n : ℂ) + 1) * s).re := by
      have : (((n : ℂ) + 1) * s).re = ((n : ℝ) + 1) * s.re := by simp
      rw [this]; nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    rw [← (hasSum_integral_cells hπm hπ0 hπle hM hre).2, ← tsum_mul_left]
  have hRHS : (∑' n : ℕ, 1 / ((n : ℂ) + 1) * ∫ y : ℝ, cexp (-(((n : ℂ) + 1) * s * y)) * (π y : ℂ)) =
      ∑' p, S p := by
    rw [tsum_congr hF, hS.tsum_prod]
    exact (Summable.tsum_comm (f := fun i n => S (i, n)) hS)
  -- the error is the difference
  have hC : ∀ p : Cell M × ℕ, T p - S p = cellTerm u₀ M π u p.1 p.2 s := fun p => by
    simp only [hTdef, hSdef, cellTerm]
    rw [show -(s * ((((p.2 : ℝ) + 1) * u p.1 : ℝ) : ℂ)) = -(((p.2 : ℂ) + 1) * s) * (u p.1 : ℂ) by
      push_cast; ring]
    push_cast
    ring
  have hTS := hT.sub hS
  have hσsum : ∑' i : Cell M, ∑' n : ℕ, (T (i, n) - S (i, n)) =
      ∑' m : ℕ, ∑' j : Fin (M m), ∑' n : ℕ, (T (⟨m, j⟩, n) - S (⟨m, j⟩, n)) :=
    Summable.tsum_sigma' (f := fun i : Cell M => ∑' n : ℕ, (T (i, n) - S (i, n)))
      (fun m => (hasSum_fintype _).summable) hTS.prod
  have hE : discretizationError u₀ M π u s = ∑' p, (T p - S p) := by
    rw [hTS.tsum_prod, hσsum]
    unfold discretizationError blockError
    refine tsum_congr fun m => ?_
    rw [tsum_fintype]
    exact Finset.sum_congr rfl fun j _ => tsum_congr fun n => (hC (⟨m, j⟩, n)).symm
  rw [hP, hRHS, hE, hT.tsum_sub hS]
  ring

include hM in
theorem cellWeight_pos (hπpos : ∀ y, u₀ ≤ y → 0 < π y) (i : Cell M) :
    0 < cellWeight u₀ M π i := by
  have hlen := node_succ_sub (M := M) u₀ i.1 i.2
  have hM0 : (0 : ℝ) < M i.1 := by have := hM i.1; positivity
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_density hπm hπ0 hπle _ _) (fun y hy => hπpos y ?_) (by
      have : (0 : ℝ) < 1 / M i.1 := by positivity
      linarith)
  exact (le_trans (by linarith [(i.1.cast_nonneg : (0 : ℝ) ≤ i.1)]) (le_node u₀ i.1 i.2)).trans
    hy.1.le

include hu hM in
/-- The atom series `Σ_{i,r} (w_i/r) e^{-σ r u_i}` converges for `σ > 1`. -/
theorem summable_atoms (hu₀ : 3 ≤ u₀) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Cell M × ℕ => cellWeight u₀ M π p.1 / ((p.2 : ℝ) + 1) *
      Real.exp (-(σ * (((p.2 : ℝ) + 1) * u p.1))) := by
  have h := (measureDirichlet_eulerPrimeMeasure hπm hπ0 hπle hM hu hu₀ (s := (σ : ℂ))
    (by simpa using hσ)).1.summable.norm
  refine h.congr fun p => ?_
  have hw := cellWeight_nonneg hπ0 (u₀ := u₀) (M := M) p.1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Complex.norm_exp]
  congr 2
  simp

include hu hM in
theorem integrable_rpow_neg_eulerPrimeMeasure (hu₀ : 3 ≤ u₀) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun x : ℝ => x ^ (-σ)) (eulerPrimeMeasure u (cellWeight u₀ M π)) := by
  refine integrable_eulerPrimeMeasure (cellWeight_nonneg hπ0)
    ((summable_atoms hπm hπ0 hπle hM hu hu₀ hσ).congr fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _), ← Real.exp_mul]
  ring_nf

omit hπm hπ0 hπle in
/-- At `s = 1` the cell errors are real. -/
theorem cellTerm_one (i : Cell M) (n : ℕ) :
    cellTerm u₀ M π u i n 1 = ((1 / ((n : ℝ) + 1) * (cellWeight u₀ M π i *
      Real.exp (-(((n : ℝ) + 1) * u i)) - ∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1),
        Real.exp (-(((n : ℝ) + 1) * y)) * π y) : ℝ) : ℂ) := by
  have hI : ∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1),
      cexp (-(((n : ℂ) + 1) * 1) * y) * (π y : ℂ) =
      ((∫ y in node u₀ M i.1 i.2..node u₀ M i.1 (i.2 + 1),
        Real.exp (-(((n : ℝ) + 1) * y)) * π y : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun y _ => ?_
    push_cast
    ring_nf
  rw [cellTerm, hI]
  push_cast
  ring_nf

omit hπm hπ0 hπle in
theorem exists_discretizationError_one_eq :
    ∃ e : ℝ, discretizationError u₀ M π u 1 = e := by
  refine ⟨∑' m : ℕ, ∑ j : Fin (M m), ∑' n : ℕ, (1 / ((n : ℝ) + 1) *
    (cellWeight u₀ M π ⟨m, j⟩ * Real.exp (-(((n : ℝ) + 1) * u ⟨m, j⟩)) -
      ∫ y in node u₀ M m j..node u₀ M m (j + 1), Real.exp (-(((n : ℝ) + 1) * y)) * π y)), ?_⟩
  unfold discretizationError blockError
  simp only [cellTerm_one, Complex.ofReal_tsum, Complex.ofReal_sum]

end Errors

/-! ## Rationally independent points -/

/-- In countably many intervals `(a_i, b_i) ⊆ (0, ∞)` there are points linearly independent over
`ℚ`: nonzero rational multiples of distinct vectors of a Hamel basis of `ℝ`. -/
theorem exists_linearIndependent_mem_Ioo {ι : Type} [Countable ι] {a b : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) :
    ∃ u : ι → ℝ, (∀ i, u i ∈ Ioo (a i) (b i)) ∧ LinearIndependent ℚ u := by
  set B := Module.Basis.ofVectorSpace ℚ ℝ with hB
  have hκ : ¬ Countable (Module.Basis.ofVectorSpaceIndex ℚ ℝ) := by
    intro h
    have : Countable ℝ := B.repr.toEquiv.countable_iff.mpr inferInstance
    exact Cardinal.not_countable_real Set.countable_univ
  obtain ⟨e⟩ : Nonempty (ι ↪ Module.Basis.ofVectorSpaceIndex ℚ ℝ) := by
    rw [← Cardinal.le_def]
    exact (Cardinal.mk_le_aleph0_iff.mpr inferInstance).trans
      (le_of_lt (not_le.mp fun h => hκ (Cardinal.mk_le_aleph0_iff.mp h)))
  have hq : ∀ i, ∃ q : ℚ, (q : ℝ) * B (e i) ∈ Ioo (a i) (b i) := by
    intro i
    rcases lt_or_gt_of_ne (B.ne_zero (e i)) with hneg | hpos
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((div_lt_div_right_of_neg hneg).mpr (hab i))
      exact ⟨q, (lt_div_iff_of_neg hneg).mp hq2, (div_lt_iff_of_neg hneg).mp hq1⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (div_lt_div_of_pos_right (hab i) hpos)
      exact ⟨q, (div_lt_iff₀ hpos).mp hq1, (lt_div_iff₀ hpos).mp hq2⟩
  choose q hq using hq
  have hq0 : ∀ i, q i ≠ 0 := fun i h => by
    have := (hq i).1
    rw [h, Rat.cast_zero, zero_mul] at this
    linarith [ha i]
  refine ⟨fun i => (q i : ℝ) * B (e i), hq, ?_⟩
  have hli := (B.linearIndependent.comp e e.injective).units_smul
    (fun i => Units.mk0 (q i) (hq0 i))
  have hfun : ((fun i => Units.mk0 (q i) (hq0 i)) • (B ∘ e) : ι → ℝ) =
      fun i => (q i : ℝ) * B (e i) := by
    funext i
    simp [Rat.smul_def]
  rw [hfun] at hli
  exact hli






end GaloisForLFunctions.EulerFETransportTheory.Discretization
