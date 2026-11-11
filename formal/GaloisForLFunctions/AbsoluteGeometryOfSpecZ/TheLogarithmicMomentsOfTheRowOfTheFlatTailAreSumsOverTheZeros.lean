import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRowOfTheFlatTailHasTheMellinTransformOfTheZeros
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass

/-!
# The logarithmic moments of the row of the flat tail are sums over the zeros

For the row `ϱ(t) = 1/t − ψ(1/t) − ½ log(1 − t²) − log 2π` of the flat tail and every `j`,

`μ_j = ∫_0^1 log^j(1/t) ϱ(t) dt = j! Σ_ρ 1/(ρ (1 − ρ)^{j+1})`   (`rowMoment_eq_tsum`).

The Mellin transform `∫_0^1 t^ε ϱ = Σ_ρ 1/(ρ(1 + ε − ρ))` holds for `ε > 0` only; the moments are
its expansion at `ε = 0`, a point on the boundary. Both sides are expanded with exact remainders.

* **The exponential** (`abs_expRem_le`). `R_j(y) = e^{−y} − Σ_{i<j} (−y)^i/i!` satisfies
  `|R_j(y)| ≤ y^j/j!` for `y ≥ 0`; `t^ε = e^{−ε log(1/t)}`.
* **The zeros** (`tailZeroSum_sub`). `Z_j(ε) = Σ_ρ 1/(ρ (1−ρ)^j (1+ε−ρ))` satisfies
  `Z_j(ε) = Z_j(0) − ε Z_{j+1}(ε)`, and `|Z_j(ε)| ≤ Σ 1/γ²` uniformly.
* **The induction** (`remIntegral_eq_and_rowMoment`). If
  `∫ R_j(ε log(1/t)) ϱ = (−ε)^j Z_j(ε)` for all `ε > 0`, divide by `ε^j` and let `ε ↓ 0`:
  dominated convergence gives `μ_j/j! = Z_j(0)`, and subtracting the term of degree `j` gives the
  identity for `j + 1`.

The domination needs `log^j(1/t) |ϱ(t)|` integrable: the prime number theorem with powers of
the logarithm to spare.
-/

open Finset Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower (XiZeroCopy xi)

/-! ### The remainder of the exponential series -/

/-- The remainder of the exponential series at `−y` after `j` terms. -/
def expRem (j : ℕ) (y : ℝ) : ℝ := Real.exp (-y) - ∑ i ∈ range j, (-y) ^ i / i.factorial

theorem expRem_zero (y : ℝ) : expRem 0 y = Real.exp (-y) := by
  simp [expRem]

theorem expRem_succ (j : ℕ) (y : ℝ) :
    expRem (j + 1) y = expRem j y - (-y) ^ j / j.factorial := by
  rw [expRem, expRem, Finset.sum_range_succ]
  ring

theorem expRem_succ_zero (j : ℕ) : expRem (j + 1) 0 = 0 := by
  induction j with
  | zero => simp [expRem]
  | succ j ih =>
    rw [expRem_succ, ih]
    simp

theorem continuous_expRem (j : ℕ) : Continuous (expRem j) := by
  unfold expRem
  exact (Real.continuous_exp.comp continuous_neg).sub
    (continuous_finsetSum _ fun i _ => (continuous_neg.pow i).div_const _)

theorem hasDerivAt_expRem_succ (j : ℕ) (y : ℝ) :
    HasDerivAt (expRem (j + 1)) (-expRem j y) y := by
  induction j with
  | zero =>
    have h : expRem 1 = fun y => Real.exp (-y) - 1 := by
      funext y
      simp [expRem]
    rw [h, expRem_zero]
    have h1 := ((hasDerivAt_neg' y).exp).sub_const 1
    refine h1.congr_deriv ?_
    ring
  | succ j ih =>
    have h : expRem (j + 1 + 1) =
        fun y => expRem (j + 1) y - (-y) ^ (j + 1) / ((j + 1).factorial : ℝ) :=
      funext fun y => expRem_succ (j + 1) y
    have hfac : ((j.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hp : HasDerivAt (fun y : ℝ => (-y) ^ (j + 1) / ((j + 1).factorial : ℝ))
        (-((-y) ^ j / (j.factorial : ℝ))) y := by
      have h1 := ((hasDerivAt_neg' y).pow (j + 1)).div_const ((j + 1).factorial : ℝ)
      refine h1.congr_deriv ?_
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    rw [h]
    refine (ih.sub hp).congr_deriv ?_
    rw [expRem_succ]
    ring

/-- The remainder alternates and is at most its first omitted term. -/
theorem expRem_bounds (j : ℕ) : ∀ y : ℝ, 0 ≤ y →
    0 ≤ (-1) ^ j * expRem j y ∧ (-1) ^ j * expRem j y ≤ y ^ j / j.factorial := by
  induction j with
  | zero =>
    intro y hy
    rw [expRem_zero]
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  | succ j ih =>
    intro y hy
    have hfac : ((j.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hφ : ∀ x : ℝ, HasDerivAt (fun y => (-1 : ℝ) ^ (j + 1) * expRem (j + 1) y)
        ((-1) ^ j * expRem j x) x := fun x => by
      refine ((hasDerivAt_expRem_succ j x).const_mul ((-1 : ℝ) ^ (j + 1))).congr_deriv ?_
      rw [pow_succ]
      ring
    have hmono : MonotoneOn (fun y => (-1 : ℝ) ^ (j + 1) * expRem (j + 1) y) (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (continuous_const.mul (continuous_expRem (j + 1))).continuousOn
        (fun x _ => (hφ x).differentiableAt.differentiableWithinAt) fun x hx => ?_
      rw [interior_Ici] at hx
      rw [(hφ x).deriv]
      exact (ih x hx.le).1
    have h0 : (-1 : ℝ) ^ (j + 1) * expRem (j + 1) 0 = 0 := by
      rw [expRem_succ_zero, mul_zero]
    have hlow : 0 ≤ (-1 : ℝ) ^ (j + 1) * expRem (j + 1) y := by
      have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
      simp only [h0] at h
      exact h
    have hχ : ∀ x : ℝ, HasDerivAt
        (fun y => y ^ (j + 1) / ((j + 1).factorial : ℝ) - (-1 : ℝ) ^ (j + 1) * expRem (j + 1) y)
        (x ^ j / (j.factorial : ℝ) - (-1) ^ j * expRem j x) x := fun x => by
      have hp : HasDerivAt (fun y : ℝ => y ^ (j + 1) / ((j + 1).factorial : ℝ))
          (x ^ j / (j.factorial : ℝ)) x := by
        refine ((hasDerivAt_pow (j + 1) x).div_const ((j + 1).factorial : ℝ)).congr_deriv ?_
        rw [Nat.add_sub_cancel, Nat.factorial_succ]
        push_cast
        field_simp
      exact hp.sub (hφ x)
    have hmono2 : MonotoneOn
        (fun y => y ^ (j + 1) / ((j + 1).factorial : ℝ) - (-1 : ℝ) ^ (j + 1) * expRem (j + 1) y)
        (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (((continuous_pow (j + 1)).div_const _).sub
          (continuous_const.mul (continuous_expRem (j + 1)))).continuousOn
        (fun x _ => (hχ x).differentiableAt.differentiableWithinAt) fun x hx => ?_
      rw [interior_Ici] at hx
      rw [(hχ x).deriv]
      linarith [(ih x hx.le).2]
    have hup : 0 ≤ y ^ (j + 1) / ((j + 1).factorial : ℝ) -
        (-1 : ℝ) ^ (j + 1) * expRem (j + 1) y := by
      have h := hmono2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
      simp only [h0, zero_pow (Nat.succ_ne_zero j), zero_div, sub_zero] at h
      exact h
    exact ⟨hlow, by linarith⟩

/-- **The remainder of the exponential series**: `|R_j(y)| ≤ y^j/j!` for `y ≥ 0`. -/
theorem abs_expRem_le (j : ℕ) {y : ℝ} (hy : 0 ≤ y) : |expRem j y| ≤ y ^ j / j.factorial := by
  obtain ⟨h1, h2⟩ := expRem_bounds j y hy
  have h : |expRem j y| = (-1) ^ j * expRem j y := by
    rw [← abs_of_nonneg h1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [h]
  exact h2

/-! ### The sums over the zeros -/

/-- The term `1/(ρ (1 − ρ)^j (1 + ε − ρ))` of a zero. -/
def zeroTerm (j : ℕ) (ε : ℝ) (q : XiZeroCopy) : ℂ :=
  1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)) ^ j * (1 + (ε : ℂ) - (q.1 : ℂ)))

/-- `Z_j(ε) = Σ_ρ 1/(ρ (1 − ρ)^j (1 + ε − ρ))`. -/
def tailZeroSum (j : ℕ) (ε : ℝ) : ℂ := ∑' q : XiZeroCopy, zeroTerm j ε q

theorem norm_zeroTerm_le (j : ℕ) {ε : ℝ} (q : XiZeroCopy) :
    ‖zeroTerm j ε q‖ ≤ 1 / RHTower.xiCopyOrdinate q ^ 2 := by
  have hγ := RHTower.four_lt_abs_xiCopyOrdinate q
  have hγ0 : 0 < |RHTower.xiCopyOrdinate q| := by linarith
  have him : ((q.1 : ℂ)).im = RHTower.xiCopyOrdinate q := rfl
  have h1 : |RHTower.xiCopyOrdinate q| ≤ ‖(q.1 : ℂ)‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  have h2 : |RHTower.xiCopyOrdinate q| ≤ ‖1 - (q.1 : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (1 - (q.1 : ℂ))
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, him] at h
    exact h
  have h3 : |RHTower.xiCopyOrdinate q| ≤ ‖1 + (ε : ℂ) - (q.1 : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (1 + (ε : ℂ) - (q.1 : ℂ))
    rw [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero, zero_sub,
      abs_neg, him] at h
    exact h
  have h2' : 1 ≤ ‖1 - (q.1 : ℂ)‖ ^ j := one_le_pow₀ (by linarith)
  have hpos : 0 < ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ ^ j * ‖1 + (ε : ℂ) - (q.1 : ℂ)‖ :=
    mul_pos (mul_pos (lt_of_lt_of_le hγ0 h1) (pow_pos (lt_of_lt_of_le hγ0 h2) j))
      (lt_of_lt_of_le hγ0 h3)
  have hsq : 0 < RHTower.xiCopyOrdinate q ^ 2 := by
    rw [← sq_abs]
    exact pow_pos hγ0 2
  rw [zeroTerm, norm_div, norm_one, norm_mul, norm_mul, norm_pow,
    div_le_div_iff₀ hpos hsq, one_mul, one_mul]
  calc RHTower.xiCopyOrdinate q ^ 2
      = |RHTower.xiCopyOrdinate q| * 1 * |RHTower.xiCopyOrdinate q| := by
        rw [mul_one, ← sq, sq_abs]
    _ ≤ ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ ^ j * ‖1 + (ε : ℂ) - (q.1 : ℂ)‖ :=
        mul_le_mul (mul_le_mul h1 h2' zero_le_one (norm_nonneg _)) h3 hγ0.le
          (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) j))

theorem summable_zeroTerm (j : ℕ) (ε : ℝ) : Summable (zeroTerm j ε) :=
  Summable.of_norm_bounded RHTower.summable_inv_sq_xiCopyOrdinate (norm_zeroTerm_le j)

theorem norm_tailZeroSum_le (j : ℕ) (ε : ℝ) :
    ‖tailZeroSum j ε‖ ≤ ∑' q : XiZeroCopy, 1 / RHTower.xiCopyOrdinate q ^ 2 :=
  tsum_of_norm_bounded RHTower.summable_inv_sq_xiCopyOrdinate.hasSum (norm_zeroTerm_le j)

/-- **The exact expansion at the zeros**: `Z_j(ε) = Z_j(0) − ε Z_{j+1}(ε)`. -/
theorem tailZeroSum_sub (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    tailZeroSum j ε = tailZeroSum j 0 - (ε : ℂ) * tailZeroSum (j + 1) ε := by
  rw [tailZeroSum, tailZeroSum, tailZeroSum, ← tsum_mul_left,
    ← (summable_zeroTerm j 0).tsum_sub ((summable_zeroTerm (j + 1) ε).mul_left _)]
  refine tsum_congr fun q => ?_
  have hρ : (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_ne_zero q
  have h1 : (1 : ℂ) - (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_one_sub_ne_zero q
  have h2 : (1 : ℂ) + (ε : ℂ) - (q.1 : ℂ) ≠ 0 := fun h => by
    have h' := congrArg Complex.re h
    simp at h'
    linarith [RHTower.xiZeroCopy_re_lt_one q]
  rw [zeroTerm, zeroTerm, zeroTerm]
  simp only [Complex.ofReal_zero, add_zero]
  field_simp
  ring

theorem tendsto_tailZeroSum (j : ℕ) :
    Tendsto (fun ε : ℝ => tailZeroSum j ε) (𝓝[>] 0) (𝓝 (tailZeroSum j 0)) := by
  have hS : ∀ ε : ℝ, 0 ≤ ε → ‖tailZeroSum j ε - tailZeroSum j 0‖ ≤
      ε * ∑' q : XiZeroCopy, 1 / RHTower.xiCopyOrdinate q ^ 2 := by
    intro ε hε
    rw [tailZeroSum_sub j hε, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (norm_tailZeroSum_le (j + 1) ε) hε
  have hlim : Tendsto (fun ε : ℝ => ε * ∑' q : XiZeroCopy, 1 / RHTower.xiCopyOrdinate q ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ =>
        ε * ∑' q : XiZeroCopy, 1 / RHTower.xiCopyOrdinate q ^ 2 :=
      continuous_id.mul continuous_const
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hS ε (le_of_lt hε)

/-! ### The row against the remainder of the exponential -/

/-- `∫_0^1 R_j(ε log(1/t)) ϱ(t) dt`. -/
def remIntegral (j : ℕ) (ε : ℝ) : ℝ :=
  ∫ t in Set.Ioc 0 1, expRem j (ε * Real.log (1 / t)) * rowProfile t

theorem measurable_expRem_comp (j : ℕ) (ε : ℝ) :
    Measurable fun t : ℝ => expRem j (ε * Real.log (1 / t)) :=
  (continuous_expRem j).measurable.comp
    (measurable_const.mul (Real.measurable_log.comp (measurable_const.div measurable_id)))

theorem abs_expRem_comp_le (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    |expRem j (ε * Real.log (1 / t))| ≤ ε ^ j / j.factorial * logPow j t := by
  have hL := log_one_div_nonneg ht
  refine (abs_expRem_le j (mul_nonneg hε hL)).trans (le_of_eq ?_)
  rw [logPow, mul_pow]
  ring

theorem integrableOn_expRem_mul_rowProfile (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    IntegrableOn (fun t => expRem j (ε * Real.log (1 / t)) * rowProfile t) (Set.Ioc 0 1) :=
  integrableOn_mul_rowProfile (measurable_expRem_comp j ε) j
    fun _ ht => abs_expRem_comp_le j hε ht

theorem integrableOn_logPow_mul_rowProfile (j : ℕ) :
    IntegrableOn (fun t => logPow j t * rowProfile t) (Set.Ioc 0 1) :=
  integrableOn_mul_rowProfile (measurable_logPow j) j (c := 1) fun t ht => by
    rw [abs_of_nonneg (logPow_nonneg j ht), one_mul]

/-- At `j = 0` the weight is `t^ε`. -/
theorem remIntegral_zero {ε : ℝ} :
    remIntegral 0 ε = ∫ t in Set.Ioc (0 : ℝ) 1, t ^ ε * rowProfile t := by
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  show expRem 0 (ε * Real.log (1 / t)) * rowProfile t = t ^ ε * rowProfile t
  rw [expRem_zero, Real.rpow_def_of_pos ht.1, Real.log_div one_ne_zero ht.1.ne', Real.log_one]
  congr 2
  ring

/-- Removing the term of degree `j`. -/
theorem remIntegral_succ (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    remIntegral (j + 1) ε = remIntegral j ε - (-ε) ^ j / j.factorial * rowMoment j := by
  rw [remIntegral, remIntegral, rowMoment, ← integral_const_mul,
    ← integral_sub (integrableOn_expRem_mul_rowProfile j hε)
      ((integrableOn_logPow_mul_rowProfile j).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show expRem (j + 1) (ε * Real.log (1 / t)) * rowProfile t =
    expRem j (ε * Real.log (1 / t)) * rowProfile t -
      (-ε) ^ j / j.factorial * (logPow j t * rowProfile t)
  rw [expRem_succ, logPow]
  ring

/-- **Dominated convergence at the boundary**: `∫ R_j(ε log(1/t)) ϱ / ε^j → (−1)^j μ_j/j!`. -/
theorem tendsto_remIntegral_div (j : ℕ) :
    Tendsto (fun ε : ℝ => remIntegral j ε / ε ^ j) (𝓝[>] 0)
      (𝓝 ((-1) ^ j / j.factorial * rowMoment j)) := by
  have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hF : ∀ ε : ℝ, remIntegral j ε / ε ^ j =
      ∫ t in Set.Ioc (0 : ℝ) 1, expRem j (ε * Real.log (1 / t)) / ε ^ j * rowProfile t := by
    intro ε
    rw [remIntegral, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show expRem j (ε * Real.log (1 / t)) * rowProfile t / ε ^ j =
      expRem j (ε * Real.log (1 / t)) / ε ^ j * rowProfile t
    ring
  have hlimval : (-1 : ℝ) ^ j / j.factorial * rowMoment j =
      ∫ t in Set.Ioc (0 : ℝ) 1, (-1) ^ j / j.factorial * (logPow j t * rowProfile t) := by
    rw [integral_const_mul, rowMoment]
  simp only [hF]
  rw [hlimval]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => |logPow j t * rowProfile t| / j.factorial)
    (Eventually.of_forall fun ε =>
      (((measurable_expRem_comp j ε).div_const _).mul measurable_rowProfile).aestronglyMeasurable)
    ?_ ((integrableOn_logPow_mul_rowProfile j).abs.div_const _) ?_
  · -- the bound
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    have hb := abs_expRem_comp_le j hε0.le ht
    have hL := logPow_nonneg j ht
    have hεj : 0 < ε ^ j := pow_pos hε0 j
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hεj, abs_mul, abs_of_nonneg hL]
    calc |expRem j (ε * Real.log (1 / t))| / ε ^ j * |rowProfile t|
        ≤ (ε ^ j / j.factorial * logPow j t) / ε ^ j * |rowProfile t| :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hεj.le) (abs_nonneg _)
      _ = logPow j t * |rowProfile t| / j.factorial := by
          field_simp
  · -- the pointwise limit
    refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    have hL := log_one_div_nonneg ht
    have hsmall : Tendsto (fun ε : ℝ => expRem (j + 1) (ε * Real.log (1 / t)) / ε ^ j)
        (𝓝[>] 0) (𝓝 0) := by
      have hb : Tendsto (fun ε : ℝ => ε * (Real.log (1 / t) ^ (j + 1) / (j + 1).factorial))
          (𝓝[>] 0) (𝓝 0) := by
        have hc : Continuous fun ε : ℝ =>
            ε * (Real.log (1 / t) ^ (j + 1) / (j + 1).factorial) :=
          continuous_id.mul continuous_const
        have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa using h
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0 : ℝ) < ε := hε
      have hεj : 0 < ε ^ j := pow_pos hε0 j
      have h1 := abs_expRem_le (j + 1) (mul_nonneg hε0.le hL)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hεj, div_le_iff₀ hεj]
      refine h1.trans (le_of_eq ?_)
      ring
    have hmain : Tendsto (fun ε : ℝ => expRem j (ε * Real.log (1 / t)) / ε ^ j) (𝓝[>] 0)
        (𝓝 ((-Real.log (1 / t)) ^ j / j.factorial)) := by
      have h := (tendsto_const_nhds (x := (-Real.log (1 / t)) ^ j / (j.factorial : ℝ))
        (f := 𝓝[>] (0 : ℝ))).add hsmall
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0 : ℝ) < ε := hε
      have hεj : ε ^ j ≠ 0 := (pow_pos hε0 j).ne'
      have hexp : expRem j (ε * Real.log (1 / t)) = expRem (j + 1) (ε * Real.log (1 / t)) +
          (-(ε * Real.log (1 / t))) ^ j / j.factorial := by
        rw [expRem_succ]
        ring
      have hpow : (-(ε * Real.log (1 / t))) ^ j = ε ^ j * (-Real.log (1 / t)) ^ j := by
        rw [← mul_neg, mul_pow]
      rw [hexp, hpow]
      field_simp
      ring
    have h := hmain.mul_const (rowProfile t)
    have e : (-Real.log (1 / t)) ^ j / (j.factorial : ℝ) * rowProfile t =
        (-1) ^ j / (j.factorial : ℝ) * (logPow j t * rowProfile t) := by
      rw [logPow, neg_pow]
      ring
    rw [← e]
    exact h

/-! ### The moments -/

/-- If the identity of degree `j` holds for every `ε > 0`, the moment of degree `j` is the sum
over the zeros: divide by `ε^j` and let `ε ↓ 0`. -/
theorem rowMoment_of_remIntegral (j : ℕ)
    (hP : ∀ ε : ℝ, 0 < ε → ((remIntegral j ε : ℝ) : ℂ) = (-(ε : ℂ)) ^ j * tailZeroSum j ε) :
    ((rowMoment j : ℝ) : ℂ) = j.factorial * tailZeroSum j 0 := by
  have hfac : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h1 : Tendsto (fun ε : ℝ => ((remIntegral j ε / ε ^ j : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (((-1) ^ j / j.factorial * rowMoment j : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_remIntegral_div j)
  have h2 : Tendsto (fun ε : ℝ => (-1 : ℂ) ^ j * tailZeroSum j ε) (𝓝[>] 0)
      (𝓝 ((-1 : ℂ) ^ j * tailZeroSum j 0)) := (tendsto_tailZeroSum j).const_mul _
  have heq : (fun ε : ℝ => ((remIntegral j ε / ε ^ j : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => (-1 : ℂ) ^ j * tailZeroSum j ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    have hεc : ((ε : ℂ)) ^ j ≠ 0 := pow_ne_zero j (Complex.ofReal_ne_zero.mpr hε0.ne')
    rw [Complex.ofReal_div, Complex.ofReal_pow, hP ε hε0, neg_pow]
    field_simp
  have h3 := tendsto_nhds_unique (h1.congr' heq) h2
  have hsign : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero j (by norm_num)
  push_cast at h3
  have h4 : ((rowMoment j : ℝ) : ℂ) / j.factorial = tailZeroSum j 0 := by
    apply mul_left_cancel₀ hsign
    rw [← h3]
    ring
  rw [← h4]
  field_simp

/-- **The induction**: the identity of the remainders at every degree, and the moments. -/
theorem remIntegral_eq_and_rowMoment (j : ℕ) :
    (∀ ε : ℝ, 0 < ε → ((remIntegral j ε : ℝ) : ℂ) = (-(ε : ℂ)) ^ j * tailZeroSum j ε) ∧
      ((rowMoment j : ℝ) : ℂ) = j.factorial * tailZeroSum j 0 := by
  induction j with
  | zero =>
    have hP : ∀ ε : ℝ, 0 < ε →
        ((remIntegral 0 ε : ℝ) : ℂ) = (-(ε : ℂ)) ^ 0 * tailZeroSum 0 ε := by
      intro ε hε
      rw [pow_zero, one_mul, remIntegral_zero, mellin_rowProfile hε, tailZeroSum]
      refine tsum_congr fun q => ?_
      rw [zeroTerm, pow_zero, mul_one]
    exact ⟨hP, rowMoment_of_remIntegral 0 hP⟩
  | succ j ih =>
    obtain ⟨hP, hM⟩ := ih
    have hfac : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    have hP' : ∀ ε : ℝ, 0 < ε →
        ((remIntegral (j + 1) ε : ℝ) : ℂ) = (-(ε : ℂ)) ^ (j + 1) * tailZeroSum (j + 1) ε := by
      intro ε hε
      rw [remIntegral_succ j hε.le, Complex.ofReal_sub, hP ε hε, Complex.ofReal_mul, hM,
        tailZeroSum_sub j hε.le]
      push_cast
      field_simp
      ring
    exact ⟨hP', rowMoment_of_remIntegral (j + 1) hP'⟩

/-- **The logarithmic moments of the row of the flat tail are sums over the zeros**:
`∫_0^1 log^j(1/t) ϱ(t) dt = j! Σ_ρ 1/(ρ (1 − ρ)^{j+1})`. -/
theorem rowMoment_eq_tsum (j : ℕ) :
    ((rowMoment j : ℝ) : ℂ) =
      j.factorial * ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)) ^ (j + 1)) := by
  rw [(remIntegral_eq_and_rowMoment j).2, tailZeroSum]
  congr 1
  refine tsum_congr fun q => ?_
  rw [zeroTerm, Complex.ofReal_zero, add_zero, pow_succ, mul_assoc]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
