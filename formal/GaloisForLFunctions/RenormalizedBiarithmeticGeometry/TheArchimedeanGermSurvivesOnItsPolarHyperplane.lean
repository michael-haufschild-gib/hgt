import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheRenormalizationSurvivalLaw
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries
import GaloisForLFunctions.RHTower.CCM.CCMDiagonalFockLift

/-!
# The archimedean germ survives on its polar hyperplane

The **lattice germ** `G_r(z) = Σ_{k ≥ 0} r^k/(k + z)` (`0 ≤ r < 1`, `z > 0`) is the Abel-regularized
self-energy of the shifted integer lattice `z + ℕ`. Its Hankel forms are positive:
`Σ_{i,j} c_i c_j G_r(x_i + x_j) ≥ 0`, since every `1/(k + x_i + x_j)` is a Cauchy kernel
(`latticeGerm_hankel_nonneg`).

As `r → 1⁻` the germ diverges like the torsion germ, by the universal self-energy `−log(1 − r)`, and
the renormalized limit is the digamma function of the archimedean local factor
(`tendsto_latticeGerm_add_log`, `latticeGermLimit_eq`):
`G_r(z) + log(1 − r) → −ψ(z) − γ`.

The divergence does not depend on `z`: the counterterm of the Hankel family is the rank-one matrix
`𝟙𝟙ᵀ`. By the survival law, positivity survives on its null cone, the polar-neutral hyperplane
`Σ c_i = 0`, and there it reads (`neg_digamma_hankel_nonneg`)

`Σ_{i,j} c_i c_j (−ψ(x_i + x_j)) ≥ 0`.

Off the hyperplane nothing survives: `G_r(2) + log(1 − r) → −1 < 0`
(`latticeGermLimit_two`, `not_nonneg_latticeGermLimit`).
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

/-- The Abel-regularized self-energy of the shifted lattice `z + ℕ`. -/
def latticeGerm (r z : ℝ) : ℝ := ∑' k : ℕ, r ^ k / ((k : ℝ) + z)

/-- The renormalized lattice germ `Σ_k (1/(k + z) − 1/(k + 1))`. -/
def latticeGermLimit (z : ℝ) : ℝ := ∑' k : ℕ, (1 / ((k : ℝ) + z) - 1 / ((k : ℝ) + 1))

theorem hasSum_latticeGerm {r z : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hz : 0 < z) :
    HasSum (fun k : ℕ => r ^ k / ((k : ℝ) + z)) (latticeGerm r z) := by
  refine (Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).div_const z)).hasSum
  exact div_le_div_of_nonneg_left (pow_nonneg hr0 k) hz (by linarith [k.cast_nonneg (α := ℝ)])

/-- The real Gauss terms are minus the corpus's complex Gauss digamma terms. -/
theorem gaussDigammaSeriesTerm_ofReal (z : ℝ) (k : ℕ) :
    _root_.RHTower.gaussDigammaSeriesTerm (z : ℂ) k =
      ((-(1 / ((k : ℝ) + z) - 1 / ((k : ℝ) + 1)) : ℝ) : ℂ) := by
  simp only [_root_.RHTower.gaussDigammaSeriesTerm]
  push_cast
  ring

theorem summable_abs_latticeGermLimit {z : ℝ} (hz : 0 < z) :
    Summable fun k : ℕ => |1 / ((k : ℝ) + z) - 1 / ((k : ℝ) + 1)| := by
  have h := _root_.RHTower.summable_norm_gaussDigammaSeriesTerm (s := (z : ℂ)) (by simpa using hz)
  refine h.congr fun k => ?_
  rw [gaussDigammaSeriesTerm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_neg]

/-- **The renormalized lattice germ is the digamma function**: `Σ_k (1/(k + z) − 1/(k + 1)) =
−ψ(z) − γ`. -/
theorem latticeGermLimit_eq {z : ℝ} (hz : 0 < z) :
    latticeGermLimit z = -((Complex.digamma z).re + Real.eulerMascheroniConstant) := by
  have hzre : 0 < (z : ℂ).re := by simpa using hz
  rw [_root_.RHTower.digamma_eq_neg_euler_add_tsum_gauss hzre, Complex.add_re,
    Complex.re_tsum (_root_.RHTower.summable_gaussDigammaSeriesTerm hzre)]
  simp only [gaussDigammaSeriesTerm_ofReal, Complex.ofReal_re, Complex.neg_re]
  rw [tsum_neg, latticeGermLimit]
  ring

/-- `ψ(2) = 1 − γ` makes the renormalized germ at `z = 2` equal to `−1`. -/
theorem latticeGermLimit_two : latticeGermLimit 2 = -1 := by
  rw [latticeGermLimit_eq two_pos]
  have h2 : ((2 : ℝ) : ℂ) = 1 + 1 := by norm_num
  rw [h2, Complex.digamma_apply_add_one 1 (fun m h => by
      have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]),
    Complex.digamma_one]
  simp

/-! ### Positivity of the regularized germ -/

/-- Each Abel level is a Cauchy form: `Σ_{i,j} c_i c_j/(k + x_i + x_j) ≥ 0`. -/
theorem cauchy_level_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (c : Fin n → ℝ)
    (k : ℕ) : 0 ≤ ∑ i, ∑ j, c i * c j * (1 / ((k : ℝ) + (x i + x j))) := by
  have hy : ∀ i, 0 < (k : ℝ) / 2 + x i := fun i => add_pos_of_nonneg_of_pos (by positivity) (hx i)
  have h := GaloisForLFunctions.RHTower.cauchy_quadratic_form hy c
  have heq : ∑ i, ∑ j, c i * c j * (1 / ((k : ℝ) + (x i + x j))) =
      ∑ i, ∑ j, c i * c j *
        GaloisForLFunctions.RHTower.cauchyKernel ((k : ℝ) / 2 + x i) ((k : ℝ) / 2 + x j) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [GaloisForLFunctions.RHTower.cauchyKernel]
    congr 2
    ring
  rw [heq, h]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _

/-- **Hankel positivity of the lattice germ** at every regulator `0 ≤ r < 1`. -/
theorem latticeGerm_hankel_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * latticeGerm r (x i + x j) := by
  have h := hasSum_sum fun i (_ : i ∈ univ) => hasSum_sum fun j (_ : j ∈ univ) =>
    (hasSum_latticeGerm hr0 hr1 (add_pos (hx i) (hx j))).mul_left (c i * c j)
  refine h.nonneg fun k => ?_
  have hlev : ∑ i, ∑ j, c i * c j * (r ^ k / ((k : ℝ) + (x i + x j))) =
      r ^ k * ∑ i, ∑ j, c i * c j * (1 / ((k : ℝ) + (x i + x j))) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [hlev]
  exact mul_nonneg (pow_nonneg hr0 k) (cauchy_level_nonneg hx c k)

/-! ### The renormalized limit -/

/-- `Σ_k r^k/(k + 1) = −log(1 − r)/r`. -/
theorem hasSum_pow_div_succ {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => r ^ k / ((k : ℝ) + 1)) (-Real.log (1 - r) / r) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one (x := r)
    (by rw [abs_of_pos hr0]; exact hr1)).div_const r
  refine h.congr_fun fun k => ?_
  rw [pow_succ]
  field_simp

/-- **The lattice germ renormalizes to the digamma function**:
`G_r(z) + log(1 − r) → Σ_k (1/(k + z) − 1/(k + 1)) = −ψ(z) − γ` as `r → 1⁻`. -/
theorem tendsto_latticeGerm_add_log {z : ℝ} (hz : 0 < z) :
    Tendsto (fun r => latticeGerm r z + Real.log (1 - r)) (𝓝[<] 1)
      (𝓝 (latticeGermLimit z)) := by
  set d : ℕ → ℝ := fun k => 1 / ((k : ℝ) + z) - 1 / ((k : ℝ) + 1)
  have hd := summable_abs_latticeGermLimit hz
  -- The Abel means of the absolutely summable differences converge (Tannery).
  have hAbel : Tendsto (fun r : ℝ => ∑' k, r ^ k * d k) (𝓝[<] 1) (𝓝 (∑' k, d k)) := by
    refine tendsto_tsum_of_dominated_convergence hd (fun k => ?_) ?_
    · have : Tendsto (fun r : ℝ => r ^ k * d k) (𝓝 1) (𝓝 (1 ^ k * d k)) :=
        ((continuous_pow k).tendsto 1).mul_const _
      rw [one_pow, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr k
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr.1.le k)]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hr.1.le hr.2.le)
  -- `(1 − r) log(1 − r) → 0`.
  have hml : Tendsto (fun r : ℝ => (1 - r) * Real.log (1 - r)) (𝓝[<] 1) (𝓝 0) := by
    have h := (Real.continuous_mul_log.comp (continuous_sub_left (1 : ℝ))).tendsto 1
    simp only [Function.comp_def, sub_self, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun r : ℝ => r⁻¹) (𝓝[<] 1) (𝓝 1) := by
    have h := (continuousAt_inv₀ (one_ne_zero (α := ℝ))).tendsto
    rw [inv_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim := hAbel.sub (hml.mul hinv)
  rw [zero_mul, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  -- Split `G_r(z)` into the Abel mean of `d` and the logarithmic series.
  have hsplit : latticeGerm r z = ∑' k, r ^ k * d k + -Real.log (1 - r) / r := by
    have h1 := (hasSum_latticeGerm hr.1.le hr.2 hz)
    have h2 : HasSum (fun k : ℕ => r ^ k * d k + r ^ k / ((k : ℝ) + 1))
        (∑' k, r ^ k * d k + -Real.log (1 - r) / r) := by
      refine HasSum.add (Summable.hasSum ?_) (hasSum_pow_div_succ hr.1 hr.2)
      refine Summable.of_norm_bounded hd fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr.1.le k)]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hr.1.le hr.2.le)
    refine h1.unique (h2.congr_fun fun k => ?_)
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkz : (0 : ℝ) < (k : ℝ) + z := by positivity
    simp only [d]
    field_simp
    ring
  rw [hsplit]
  have hr0 : r ≠ 0 := hr.1.ne'
  field_simp
  ring

/-! ### Survival on the polar hyperplane -/

/-- The regularized Hankel matrix of the lattice germ. -/
def latticeHankel {n : ℕ} (x : Fin n → ℝ) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => latticeGerm r (x i + x j)

/-- The counterterm of the lattice germ: the rank-one matrix `𝟙𝟙ᵀ`. -/
def latticeCounterterm (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

/-- The renormalized limit of the lattice Hankel family. -/
def latticeHankelLimit {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => latticeGermLimit (x i + x j)

/-- **The lattice germ is a regularized family with rank-one counterterm**: its Hankel forms are
positive, and `G_r + log(1 − r) 𝟙𝟙ᵀ → G_1^{ren}` entrywise. -/
theorem latticeHankel_regularized {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    (∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ c, 0 ≤ quad (latticeHankel x r) c) ∧
      ∀ i j, Tendsto (fun r => latticeHankel x r i j -
        (-Real.log (1 - r)) * latticeCounterterm n i j) (𝓝[<] 1)
          (𝓝 (latticeHankelLimit x i j)) := by
  refine ⟨?_, fun i j => ?_⟩
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr c
    have h := latticeGerm_hankel_nonneg hx hr.1.le hr.2 c
    refine h.trans_eq ?_
    simp only [quad, latticeHankel, Matrix.of_apply]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  · refine (tendsto_latticeGerm_add_log (add_pos (hx i) (hx j))).congr fun r => ?_
    simp only [latticeHankel, latticeCounterterm, Matrix.of_apply, Matrix.vecMulVec_apply]
    ring

/-- **Survival of the archimedean germ.** On the polar-neutral hyperplane `Σ c_i = 0` the
renormalized lattice germ is a positive Hankel form: `Σ_{i,j} c_i c_j (−ψ(x_i + x_j)) ≥ 0`. -/
theorem neg_digamma_hankel_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    {c : Fin n → ℝ} (hc : ∑ i, c i = 0) :
    0 ≤ ∑ i, ∑ j, c i * c j * (-(Complex.digamma ((x i + x j : ℝ) : ℂ)).re) := by
  obtain ⟨hQ, hlim⟩ := latticeHankel_regularized hx
  have hcone : c ∈ survivalCone (latticeCounterterm n) := by
    rw [latticeCounterterm, mem_survivalCone_vecMulVec_iff]
    simpa using hc
  have h := quad_nonneg_of_regularized hQ hlim hcone
  have heq : quad (latticeHankelLimit x) c =
      ∑ i, ∑ j, c i * c j * (-(Complex.digamma ((x i + x j : ℝ) : ℂ)).re) -
        Real.eulerMascheroniConstant * ((∑ i, c i) * ∑ j, c j) := by
    rw [sum_mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [latticeHankelLimit, Matrix.of_apply, latticeGermLimit_eq (add_pos (hx i) (hx j))]
    ring
  rw [heq, hc, zero_mul, mul_zero, sub_zero] at h
  exact h

/-- **Nothing survives off the hyperplane**: the one-node renormalized limit at `x = 1` is `−1`. -/
theorem not_nonneg_latticeGermLimit :
    ¬ ∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 < x i) → ∀ c, 0 ≤ quad (latticeHankelLimit x) c := by
  intro h
  have h1 := h 1 (fun _ => 1) (fun _ => one_pos) (fun _ => 1)
  simp only [quad, latticeHankelLimit, Matrix.of_apply, Fin.sum_univ_one, mul_one, one_mul] at h1
  norm_num [latticeGermLimit_two] at h1

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
