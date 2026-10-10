import GaloisForLFunctions.RHTower.XiGaussianHeatHankelIndex

/-!
# The negative index law for the vertical heat Gram form

Finite differences carry the polynomial heat Hankel form into the vertical heat Gram form.  The weight
`D_h = (ih)^{-1}(δ_0 − δ_h) ∈ ℂ[ℝ]` has amplitude `E_h(w) = (1 − e^{-ihw})/(ih)`, with
`|E_h(w) − w| ≤ h|w|² e^{h|w|}`.  Hence `P(D_h)` has amplitude `P(E_h(w))`, and
`Q_a(P(D_h), R(D_h)) → H_a(P, R)` as `h → 0` by dominated convergence.  Strict negativity on a
finite-dimensional family is an open condition, so a negative definite family for `H_a` yields one
for `Q_a`.

**Theorem** (`heatGram_negative_subspace_of_infinite`).  If there are infinitely many off-line zero
quadruples, the vertical heat Gram form `Q_a` has negative definite subspaces of every dimension.

**Theorem** (`heatGram_negativeIndex_law`).  For every `a > 0`, the negative index of `Q_a` is the
number of off-line zero quadruples: exactly `#U` when this set is finite, and infinite otherwise.
-/

open Complex Filter Topology Set Polynomial

namespace RHTower

noncomputable section

/-! ## Difference weights -/

/-- The difference weight `D_h = (ih)^{-1}(δ_0 − δ_h)`. -/
def heatDiffWeight (h : ℝ) : HeatWeights :=
  ((I * (h : ℂ))⁻¹) • (AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single h 1)

/-- The amplitude `E_h(w) = (1 − e^{-ihw})/(ih)` of `D_h`. -/
def heatDiffAmp (h : ℝ) (w : ℂ) : ℂ := (I * (h : ℂ))⁻¹ * (1 - Complex.exp (-(I * (h : ℂ)) * w))

theorem heatAmp_heatDiffWeight (h : ℝ) (w : ℂ) :
    heatAmp w (heatDiffWeight h) = heatDiffAmp h w := by
  rw [heatDiffWeight, heatAmp_smul, map_sub, heatAmp_single, heatAmp_single, heatDiffAmp]
  simp

/-- The weight `P(D_h)`. -/
def heatLiftWeight (h : ℝ) (P : ℂ[X]) : HeatWeights := Polynomial.aeval (heatDiffWeight h) P

theorem heatAmp_heatLiftWeight (h : ℝ) (P : ℂ[X]) (w : ℂ) :
    heatAmp w (heatLiftWeight h P) = P.eval (heatDiffAmp h w) := by
  rw [heatLiftWeight, ← Polynomial.aeval_algHom_apply, heatAmp_heatDiffWeight,
    Polynomial.coe_aeval_eq_eval]

theorem norm_I_mul_ofReal_of_pos {h : ℝ} (hh : 0 < h) : ‖I * (h : ℂ)‖ = h := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hh.le]

theorem norm_heatDiffAmp_le {h : ℝ} (hh : 0 < h) (w : ℂ) :
    ‖heatDiffAmp h w‖ ≤ ‖w‖ * Real.exp (h * ‖w‖) := by
  have hz := Complex.norm_exp_sub_sum_le_norm_mul_exp (-(I * (h : ℂ)) * w) 1
  have hn : ‖-(I * (h : ℂ)) * w‖ = h * ‖w‖ := by rw [norm_mul, norm_neg, norm_I_mul_ofReal_of_pos hh]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one, hn] at hz
  rw [heatDiffAmp, norm_mul, norm_inv, norm_I_mul_ofReal_of_pos hh, norm_sub_rev, inv_mul_le_iff₀ hh]
  calc ‖Complex.exp (-(I * (h : ℂ)) * w) - 1‖ ≤ h * ‖w‖ * Real.exp (h * ‖w‖) := hz
    _ = h * (‖w‖ * Real.exp (h * ‖w‖)) := by ring

theorem norm_heatDiffAmp_sub_le {h : ℝ} (hh : 0 < h) (w : ℂ) :
    ‖heatDiffAmp h w - w‖ ≤ h * ‖w‖ ^ 2 * Real.exp (h * ‖w‖) := by
  have hz := Complex.norm_exp_sub_sum_le_norm_mul_exp (-(I * (h : ℂ)) * w) 2
  have hn : ‖-(I * (h : ℂ)) * w‖ = h * ‖w‖ := by rw [norm_mul, norm_neg, norm_I_mul_ofReal_of_pos hh]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one, zero_add, hn] at hz
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hI : (I * (h : ℂ)) ≠ 0 := mul_ne_zero I_ne_zero hh'
  have heq : heatDiffAmp h w - w = -((I * (h : ℂ))⁻¹ *
      (Complex.exp (-(I * (h : ℂ)) * w) - (1 + -(I * (h : ℂ)) * w))) := by
    rw [heatDiffAmp]
    field_simp
    ring
  rw [heq, norm_neg, norm_mul, norm_inv, norm_I_mul_ofReal_of_pos hh, inv_mul_le_iff₀ hh]
  calc ‖Complex.exp (-(I * (h : ℂ)) * w) - (1 + -(I * (h : ℂ)) * w)‖
      ≤ (h * ‖w‖) ^ 2 * Real.exp (h * ‖w‖) := hz
    _ = h * (h * ‖w‖ ^ 2 * Real.exp (h * ‖w‖)) := by ring

/-- The difference step `h_n = 1/(n+1)`. -/
def heatStep (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem heatStep_pos (n : ℕ) : 0 < heatStep n := by unfold heatStep; positivity

theorem heatStep_le_one (n : ℕ) : heatStep n ≤ 1 := by
  unfold heatStep
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_heatStep : Tendsto heatStep atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_heatDiffAmp (w : ℂ) :
    Tendsto (fun n => heatDiffAmp (heatStep n) w) atTop (𝓝 w) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (norm_heatDiffAmp_sub_le (heatStep_pos n) w).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (heatStep_le_one n)
      (norm_nonneg w))) (by have := (heatStep_pos n).le; positivity))) ?_
  have h := (tendsto_heatStep.mul_const (‖w‖ ^ 2)).mul_const (Real.exp (1 * ‖w‖))
  simpa using h

/-! ## Sesquilinear expansions -/

theorem heatHankelTermAt_sum_sum {ι : Type*} [Fintype ι] (a : ℝ) (P : ι → ℂ[X]) (x : ι → ℂ)
    (w : ℂ) : heatHankelTermAt a (∑ i, x i • P i) (∑ i, x i • P i) w =
      ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatHankelTermAt a (P i) (P j) w := by
  rw [heatHankelTermAt, eval_sum_smul, eval_sum_smul, map_sum, mul_assoc, Finset.sum_mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [heatHankelTermAt, map_mul]
  ring

theorem heatGramTermAt_sum_sum {ι : Type*} [Fintype ι] (a : ℝ) (c : ι → HeatWeights) (x : ι → ℂ)
    (w : ℂ) : heatGramTermAt a (∑ i, x i • c i) (∑ i, x i • c i) w =
      ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatGramTermAt a (c i) (c j) w := by
  rw [heatGramTermAt, heatAmp_sum_smul, heatAmp_sum_smul, map_sum, mul_assoc, Finset.sum_mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [heatGramTermAt, map_mul]
  ring

theorem tsum_sum_sum_mul_conj {ι : Type*} [Fintype ι] (g : ι → ι → XiZeroCopy → ℂ)
    (hg : ∀ i j, Summable (g i j)) (x : ι → ℂ) :
    ∑' q, ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * g i j q =
      ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * ∑' q, g i j q := by
  rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => (hg i j).mul_left _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum fun j _ => (hg i j).mul_left _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]

theorem heatHankel_sum_sum {a : ℝ} (ha : 0 < a) {ι : Type*} [Fintype ι] (P : ι → ℂ[X])
    (x : ι → ℂ) : heatHankel a (∑ i, x i • P i) (∑ i, x i • P i) =
      ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatHankel a (P i) (P j) := by
  rw [heatHankel]
  simp only [heatHankelTermAt_sum_sum]
  exact tsum_sum_sum_mul_conj _ (fun i j => summable_heatHankelTermAt ha (P i) (P j)) x

theorem heatGram_sum_sum {a : ℝ} (ha : 0 < a) {ι : Type*} [Fintype ι] (c : ι → HeatWeights)
    (x : ι → ℂ) : heatGram a (∑ i, x i • c i) (∑ i, x i • c i) =
      ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatGram a (c i) (c j) := by
  rw [heatGram_eq_tsum ha]
  simp only [heatGramTermAt_sum_sum]
  rw [tsum_sum_sum_mul_conj _ (fun i j => summable_heatGramTermAt ha (c i) (c j)) x]
  simp only [heatGram_eq_tsum ha]

/-! ## Convergence of the lifted Gram form -/

theorem norm_eval_heatDiffAmp_le {h h₀ : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀) (P : ℂ[X]) (w : ℂ) :
    ‖P.eval (heatDiffAmp h w)‖ ≤
      polyMass P * ((1 + ‖w‖) ^ P.natDegree * Real.exp (P.natDegree * (h₀ * ‖w‖))) := by
  refine (norm_eval_le_polyMass P _).trans (mul_le_mul_of_nonneg_left ?_ (polyMass_nonneg P))
  have hw0 := norm_nonneg w
  have h1 : 1 + ‖heatDiffAmp h w‖ ≤ (1 + ‖w‖) * Real.exp (h₀ * ‖w‖) := by
    have e1 := norm_heatDiffAmp_le hh w
    have e2 : Real.exp (h * ‖w‖) ≤ Real.exp (h₀ * ‖w‖) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hh₀ hw0)
    have e3 : 1 ≤ Real.exp (h₀ * ‖w‖) :=
      Real.one_le_exp (mul_nonneg (hh.le.trans hh₀) hw0)
    have e4 : ‖w‖ * Real.exp (h * ‖w‖) ≤ ‖w‖ * Real.exp (h₀ * ‖w‖) :=
      mul_le_mul_of_nonneg_left e2 hw0
    calc 1 + ‖heatDiffAmp h w‖ ≤ 1 + ‖w‖ * Real.exp (h₀ * ‖w‖) := by linarith
      _ ≤ Real.exp (h₀ * ‖w‖) + ‖w‖ * Real.exp (h₀ * ‖w‖) := by linarith
      _ = (1 + ‖w‖) * Real.exp (h₀ * ‖w‖) := by ring
  calc (1 + ‖heatDiffAmp h w‖) ^ P.natDegree
      ≤ ((1 + ‖w‖) * Real.exp (h₀ * ‖w‖)) ^ P.natDegree := pow_le_pow_left₀ (by positivity) h1 _
    _ = (1 + ‖w‖) ^ P.natDegree * Real.exp (P.natDegree * (h₀ * ‖w‖)) := by
        rw [mul_pow, ← Real.exp_nat_mul]

/-- **Finite differences converge to the Hankel form.** -/
theorem tendsto_heatGram_heatLiftWeight {a : ℝ} (ha : 0 < a) (P R : ℂ[X]) :
    Tendsto (fun n => heatGram a (heatLiftWeight (heatStep n) P) (heatLiftWeight (heatStep n) R))
      atTop (𝓝 (heatHankel a P R)) := by
  set d := P.natDegree + R.natDegree with hd
  set h₀ : ℝ := a / (4 * (d + 1)) with hh₀
  have hh₀0 : 0 < h₀ := by positivity
  have hdh₀ : (d : ℝ) * h₀ ≤ a / 4 := by
    rw [hh₀, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb : 0 < 3 * a / 4 := by positivity
  have hsum := (summable_one_add_norm_pow_mul_exp hb d).mul_left
    (polyMass P * polyMass R * Real.exp (a / 8))
  simp only [heatGram_eq_tsum ha, heatHankel]
  refine tendsto_tsum_of_dominated_convergence hsum (fun q => ?_) ?_
  · simp only [heatGramTermAt, heatAmp_heatLiftWeight, heatHankelTermAt]
    exact (tendsto_const_nhds.mul ((P.continuous.tendsto _).comp (tendsto_heatDiffAmp _))).mul
      ((Complex.continuous_conj.tendsto _).comp ((R.continuous.tendsto _).comp
        (tendsto_heatDiffAmp _)))
  · filter_upwards [tendsto_heatStep.eventually (Iic_mem_nhds hh₀0)] with n hn q
    have hpos := heatStep_pos n
    set w := xiHeatFrequency q with hw
    rw [heatGramTermAt, heatAmp_heatLiftWeight, heatAmp_heatLiftWeight, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_exp]
    have hre : (-(a : ℂ) * w).re = -(a * w.re) := by simp
    rw [hre]
    have h1 := norm_eval_heatDiffAmp_le hpos hn P w
    have h2 := norm_eval_heatDiffAmp_le hpos hn R ((starRingEnd ℂ) w)
    rw [Complex.norm_conj] at h2
    have hwre := norm_xiHeatFrequency_le_re q
    rw [← hw] at hwre
    have hexp : Real.exp (P.natDegree * (h₀ * ‖w‖)) * Real.exp (R.natDegree * (h₀ * ‖w‖)) ≤
        Real.exp (a / 8) * Real.exp (a / 4 * w.re) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hdd : (P.natDegree : ℝ) + R.natDegree = d := by rw [hd]; push_cast; ring
      have hw0 := norm_nonneg w
      have : ((P.natDegree : ℝ) + R.natDegree) * h₀ * ‖w‖ ≤ a / 4 * ‖w‖ := by
        rw [hdd]; exact mul_le_mul_of_nonneg_right hdh₀ hw0
      nlinarith
    have hpre : 0 ≤ polyMass P * polyMass R * (1 + ‖w‖) ^ d * Real.exp (-(a * w.re)) := by
      have := polyMass_nonneg P
      have := polyMass_nonneg R
      positivity
    calc Real.exp (-(a * w.re)) * ‖P.eval (heatDiffAmp (heatStep n) w)‖ *
          ‖R.eval (heatDiffAmp (heatStep n) ((starRingEnd ℂ) w))‖
        ≤ Real.exp (-(a * w.re)) *
            (polyMass P * ((1 + ‖w‖) ^ P.natDegree * Real.exp (P.natDegree * (h₀ * ‖w‖)))) *
            (polyMass R * ((1 + ‖w‖) ^ R.natDegree * Real.exp (R.natDegree * (h₀ * ‖w‖)))) := by
          have hm1 := polyMass_nonneg P
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) h2 (norm_nonneg _)
            (mul_nonneg (Real.exp_pos _).le (mul_nonneg hm1 (by positivity)))
      _ = polyMass P * polyMass R * (1 + ‖w‖) ^ d * Real.exp (-(a * w.re)) *
            (Real.exp (P.natDegree * (h₀ * ‖w‖)) * Real.exp (R.natDegree * (h₀ * ‖w‖))) := by
          rw [hd, pow_add]; ring
      _ ≤ polyMass P * polyMass R * (1 + ‖w‖) ^ d * Real.exp (-(a * w.re)) *
            (Real.exp (a / 8) * Real.exp (a / 4 * w.re)) := mul_le_mul_of_nonneg_left hexp hpre
      _ = polyMass P * polyMass R * Real.exp (a / 8) *
            ((1 + ‖w‖) ^ d * Real.exp (-(3 * a / 4 * w.re))) := by
          have : Real.exp (-(a * w.re)) * Real.exp (a / 4 * w.re) = Real.exp (-(3 * a / 4 * w.re)) := by
            rw [← Real.exp_add]; congr 1; ring
          calc _ = polyMass P * polyMass R * Real.exp (a / 8) * (1 + ‖w‖) ^ d *
                (Real.exp (-(a * w.re)) * Real.exp (a / 4 * w.re)) := by ring
            _ = _ := by rw [this]; ring

/-! ## Strict negativity is open -/

theorem exists_neg_quadratic_bound {ι : Type*} [Fintype ι] (M : ι → ι → ℂ)
    (hM : ∀ x : ι → ℂ, x ≠ 0 → (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * M i j).re < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ι → ℂ,
      (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * M i j).re ≤ -(δ * ‖x‖ ^ 2) := by
  classical
  set f : (ι → ℂ) → ℝ := fun x => (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * M i j).re with hf
  have hcont : Continuous f := by
    rw [hf]
    fun_prop
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun x => ?_⟩
    have : x = 0 := funext fun i => (IsEmpty.false i).elim
    simp [this]
  have hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty := ⟨fun _ => 1, by simp [pi_norm_const]⟩
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_sphere (0 : ι → ℂ) 1).exists_isMaxOn hne hcont.continuousOn
  have hx₀n : ‖x₀‖ = 1 := by simpa using hx₀
  have hx₀0 : x₀ ≠ 0 := fun h => by rw [h, norm_zero] at hx₀n; exact zero_ne_one hx₀n
  have hfx₀ : f x₀ < 0 := hM x₀ hx₀0
  refine ⟨-f x₀, by linarith, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  · set r := ‖x‖ with hr
    have hr0 : 0 < r := norm_pos_iff.2 hx
    set y : ι → ℂ := ((r⁻¹ : ℝ) : ℂ) • x with hy
    have hyn : ‖y‖ = 1 := by
      rw [hy, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← hr,
        inv_mul_cancel₀ hr0.ne']
    have hxy : x = ((r : ℝ) : ℂ) • y := by
      rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr0.ne', Complex.ofReal_one, one_smul]
    have hfxy : f x = r ^ 2 * f y := by
      rw [hxy]
      simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
      rw [show (∑ i, ∑ j, (r : ℂ) * y i * ((r : ℂ) * (starRingEnd ℂ) (y j)) * M i j) =
          ((r ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, y i * (starRingEnd ℂ) (y j) * M i j by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        ring]
      rw [re_ofReal_mul]
    have hfy : f y ≤ f x₀ := hmax (by simpa using hyn)
    show f x ≤ -(-f x₀ * r ^ 2)
    rw [hfxy]
    nlinarith [sq_nonneg r]

theorem re_sum_sum_mul_conj_le_add {ι : Type*} [Fintype ι] (A B : ι → ι → ℂ) (x : ι → ℂ) :
    (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * A i j).re ≤
      (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * B i j).re +
        ‖x‖ ^ 2 * ∑ i, ∑ j, ‖A i j - B i j‖ := by
  have h : (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * A i j) =
      (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * B i j) +
        ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * (A i j - B i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h, add_re]
  refine add_le_add le_rfl ((Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hi := norm_le_pi_norm x i
  have hj := norm_le_pi_norm x j
  have : ‖x i‖ * ‖x j‖ ≤ ‖x‖ ^ 2 := by
    rw [sq]
    exact mul_le_mul hi hj (norm_nonneg _) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

/-! ## Transfer and the index law -/

/-- **Transfer.**  A negative definite family for the heat Hankel form lifts, through finite
differences, to a negative definite family for the vertical heat Gram form. -/
theorem exists_heatGram_negative_family_of_heatHankel {a : ℝ} (ha : 0 < a) {ι : Type*}
    [Fintype ι] (P : ι → ℂ[X])
    (hP : ∀ x : ι → ℂ, x ≠ 0 → (heatHankel a (∑ i, x i • P i) (∑ i, x i • P i)).re < 0) :
    ∃ c : ι → HeatWeights, ∀ x : ι → ℂ, x ≠ 0 →
      (heatGram a (∑ i, x i • c i) (∑ i, x i • c i)).re < 0 := by
  classical
  have hMneg : ∀ x : ι → ℂ, x ≠ 0 →
      (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * heatHankel a (P i) (P j)).re < 0 := by
    intro x hx
    have := hP x hx
    rwa [heatHankel_sum_sum ha] at this
  obtain ⟨δ, hδ, hbound⟩ := exists_neg_quadratic_bound _ hMneg
  have hconv : Tendsto (fun n => ∑ i, ∑ j, ‖heatGram a (heatLiftWeight (heatStep n) (P i))
      (heatLiftWeight (heatStep n) (P j)) - heatHankel a (P i) (P j)‖) atTop (𝓝 0) := by
    have : Tendsto (fun n => ∑ i, ∑ j, ‖heatGram a (heatLiftWeight (heatStep n) (P i))
        (heatLiftWeight (heatStep n) (P j)) - heatHankel a (P i) (P j)‖) atTop
        (𝓝 (∑ i : ι, ∑ j : ι, ‖heatHankel a (P i) (P j) - heatHankel a (P i) (P j)‖)) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        ((tendsto_heatGram_heatLiftWeight ha (P i) (P j)).sub tendsto_const_nhds).norm
    simpa using this
  obtain ⟨N, hN⟩ := (hconv.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 2))).exists
  refine ⟨fun i => heatLiftWeight (heatStep N) (P i), fun x hx => ?_⟩
  rw [heatGram_sum_sum ha]
  have h1 := re_sum_sum_mul_conj_le_add
    (fun i j => heatGram a (heatLiftWeight (heatStep N) (P i)) (heatLiftWeight (heatStep N) (P j)))
    (fun i j => heatHankel a (P i) (P j)) x
  have h2 := hbound x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h3 := mul_lt_mul_of_pos_left hN (by positivity : (0 : ℝ) < ‖x‖ ^ 2)
  have h4 : 0 < δ * ‖x‖ ^ 2 := by positivity
  linarith

/-- **Infinite index.**  If there are infinitely many off-line zero quadruples, the vertical heat
Gram form has negative definite subspaces of every dimension. -/
theorem heatGram_negative_subspace_of_infinite {a : ℝ} (ha : 0 < a)
    (hU : xiUpperFrequencies.Infinite) (n : ℕ) :
    ∃ W : Submodule ℂ HeatWeights, Module.finrank ℂ W = n ∧
      ∀ c ∈ W, c ≠ 0 → (heatGram a c c).re < 0 := by
  classical
  obtain ⟨G, hGU, hGcard⟩ := hU.exists_subset_card_eq n
  rcases G.eq_empty_or_nonempty with hGe | hGne
  · refine ⟨⊥, by rw [finrank_bot, ← hGcard, hGe, Finset.card_empty],
      fun c hc hc0 => absurd ((Submodule.mem_bot ℂ).1 hc) hc0⟩
  obtain ⟨P, hP⟩ := exists_heatHankel_negative_family ha G hGne fun u hu => hGU hu
  obtain ⟨c, hc⟩ := exists_heatGram_negative_family_of_heatHankel ha P hP
  set Φ : (G → ℂ) →ₗ[ℂ] HeatWeights := Fintype.linearCombination ℂ c with hΦ
  have hΦapp : ∀ x, Φ x = ∑ u, x u • c u := fun x => Fintype.linearCombination_apply ℂ c x
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have := hc x hne
    rw [← hΦapp, hx, heatGram_zero_left, zero_re] at this
    exact lt_irrefl 0 this
  refine ⟨LinearMap.range Φ, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      hGcard]
  · rintro d ⟨x, rfl⟩ hd
    have hx : x ≠ 0 := by
      rintro rfl
      exact hd (map_zero Φ)
    rw [hΦapp]
    exact hc x hx

/-- **The negative index law.**  For every `a > 0`, the negative index of the vertical heat Gram
form `Q_a` is the number of off-line zero quadruples: exactly `#U` when finite, infinite otherwise. -/
theorem heatGram_negativeIndex_law {a : ℝ} (ha : 0 < a) :
    (∀ hU : xiUpperFrequencies.Finite,
      (∀ V : Submodule ℂ HeatWeights, (∀ c ∈ V, c ≠ 0 → (heatGram a c c).re < 0) →
        Module.finrank ℂ V ≤ hU.toFinset.card) ∧
      ∃ V : Submodule ℂ HeatWeights, Module.finrank ℂ V = hU.toFinset.card ∧
        ∀ c ∈ V, c ≠ 0 → (heatGram a c c).re < 0) ∧
    (xiUpperFrequencies.Infinite → ∀ n : ℕ, ∃ V : Submodule ℂ HeatWeights,
      Module.finrank ℂ V = n ∧ ∀ c ∈ V, c ≠ 0 → (heatGram a c c).re < 0) :=
  ⟨fun hU => heatGram_negativeIndex_eq_card ha hU, heatGram_negative_subspace_of_infinite ha⟩

end

end RHTower
