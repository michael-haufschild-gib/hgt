import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheCurveChainOfTheInnerFactor

/-!
# Castelnuovo constructs the mollifier of a curve

What plays the role of Castelnuovo? Over a curve there is an explicit near-extremal family, and Castelnuovo is exactly what makes it work.

Let `a_k = Σ_i β_i^k` be the normalized traces of Frobenius, the prime-power data of the curve. The **Abel mollifier** is the damped and truncated Euler logarithm

`Q_{ρ,N}(v) = Σ_{k≤N} ρ^k a_k v^k / k` (`abelPoly`).

* **Each mollifier converges** (`tendsto_abelBudget`). As `N → ∞`, `e^{Q_{ρ,N}} → 1/P(ρv)`, so the budget tends to the mean of the dilation quotient `|P(v)/P(ρv)|²`.
* **Castelnuovo is a uniform bound on the quotient** (`norm_one_sub_le_two_mul`). If `|β| ≤ 1` and `|v| = 1`, then `|1 − βv| ≤ 2|1 − ρβv|`, uniformly in `ρ < 1`. So the quotient is dominated, it tends to `1` almost everywhere, and the budgets tend to `1` (`tendsto_circleAverage_abelRatio`).
* **The equivalence** (`hodgeIndex_iff_abelMollifiers`). Castelnuovo's inequality on the Frobenius span holds iff the Abel mollifiers reach budget `1`. On a fake it fails with a floor: the golden curve has budget at least `φ²` for all `ρ` and `N` (`sq_goldenRatio_le_abelBudget`).

So the mollifier is not what is hard to find: its coefficients are the prime data, damped. What Castelnuovo supplies is the a priori bound on the dilation quotient of `P`. Over `ℤ` the same family is the damped Euler logarithm, and the missing input is the same bound on `E(s)/E(s_ρ)`.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open ArithmeticCastelnuovoSeveri

noncomputable section

/-! ### Means on the circle under domination -/

/-- Dominated convergence for circle averages. -/
theorem tendsto_circleAverage_of_bounded {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {F : α → ℂ → ℝ} {f : ℂ → ℝ} {C : ℝ} (hm : ∀ᶠ a in l, Measurable (F a))
    (hb : ∀ᶠ a in l, ∀ v : ℂ, ‖v‖ = 1 → |F a v| ≤ C)
    (hl : ∀ᵐ θ : ℝ, Tendsto (fun a => F a (circleMap 0 1 θ)) l (𝓝 (f (circleMap 0 1 θ)))) :
    Tendsto (fun a => Real.circleAverage (F a) 0 1) l (𝓝 (Real.circleAverage f 0 1)) := by
  simp only [Real.circleAverage_def]
  refine Tendsto.const_smul ?_ _
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
    intervalIntegrable_const ?_
  · exact hm.mono fun a ha => (ha.comp (continuous_circleMap 0 1).measurable).aestronglyMeasurable
  · exact hb.mono fun a ha => Eventually.of_forall fun θ _ => by
      rw [Real.norm_eq_abs]
      exact ha _ (by simp [norm_circleMap_zero])
  · filter_upwards [hl] with θ hθ _ using hθ

/-- **Dilation is dominated on the closed disc.** -/
theorem norm_one_sub_le_two_mul {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - z‖ ≤ 2 * ‖1 - (ρ : ℂ) * z‖ := by
  have e : 1 - z = (1 - (ρ : ℂ) * z) - ((1 - ρ : ℝ) : ℂ) * z := by
    push_cast
    ring
  have h1 : ‖((1 - ρ : ℝ) : ℂ) * z‖ ≤ 1 - ρ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    nlinarith
  have h2 : 1 - ρ ≤ ‖1 - (ρ : ℂ) * z‖ := by
    have h3 := norm_sub_norm_le (1 : ℂ) ((ρ : ℂ) * z)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] at h3
    nlinarith
  calc ‖1 - z‖ = ‖(1 - (ρ : ℂ) * z) - ((1 - ρ : ℝ) : ℂ) * z‖ := by rw [← e]
    _ ≤ ‖1 - (ρ : ℂ) * z‖ + ‖((1 - ρ : ℝ) : ℂ) * z‖ := norm_sub_le _ _
    _ ≤ 2 * ‖1 - (ρ : ℂ) * z‖ := by linarith

/-- The exponential of a partial sum of the logarithm tends to `1/(1 − z)`. -/
theorem tendsto_exp_partial {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => Complex.exp (∑ k ∈ Finset.range (N + 1), z ^ k / k)) atTop (𝓝 (1 - z)⁻¹) := by
  have h := (Complex.hasSum_taylorSeries_neg_log hz).tendsto_sum_nat
  have h2 := (tendsto_add_atTop_iff_nat 1).mpr h
  have hne : 1 - z ≠ 0 := fun h0 => by
    have : z = 1 := (sub_eq_zero.mp h0).symm
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  have e : Complex.exp (-Complex.log (1 - z)) = (1 - z)⁻¹ := by
    rw [Complex.exp_neg, Complex.exp_log hne]
  rw [← e]
  exact Complex.continuous_exp.continuousAt.tendsto.comp h2

/-! ### The Abel mollifier -/

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The normalized trace of Frobenius `a_k = Σ_i β_i^k`. -/
def frobTrace (k : ℕ) : ℂ := ∑ i, D.β i ^ k

/-- The Abel mollifier: the Euler logarithm of the curve, damped by `ρ^k` and truncated at `N`. -/
def abelPoly (ρ : ℝ) (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C ((ρ : ℂ) ^ k * frobTrace D k / k) * Polynomial.X ^ k

theorem abelPoly_coeff_zero (ρ : ℝ) (N : ℕ) : (abelPoly D ρ N).coeff 0 = 0 := by
  rw [abelPoly, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · subst h
    simp
  · rfl

/-- The mollifier in terms of the eigenvalues. -/
theorem eval_abelPoly (ρ : ℝ) (N : ℕ) (v : ℂ) :
    (abelPoly D ρ N).eval v = ∑ i, ∑ k ∈ Finset.range (N + 1), ((ρ : ℂ) * D.β i * v) ^ k / k := by
  simp only [abelPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, frobTrace]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, mul_pow]
  ring

/-- The budget of the Abel mollifier. -/
def abelBudget (ρ : ℝ) (N : ℕ) : ℝ :=
  Real.circleAverage (fun v => ‖lPoly D v‖ ^ 2 * ‖Complex.exp ((abelPoly D ρ N).eval v)‖ ^ 2) 0 1

/-- The dilation quotient `|P(v)/P(ρv)|²`. -/
def abelRatio (ρ : ℝ) (v : ℂ) : ℝ := ∏ i, (‖1 - D.β i * v‖ / ‖1 - (ρ : ℂ) * D.β i * v‖) ^ 2

theorem abelRatio_eq (ρ : ℝ) (v : ℂ) :
    abelRatio D ρ v = ‖lPoly D v‖ ^ 2 * ‖∏ i, (1 - (ρ : ℂ) * D.β i * v)⁻¹‖ ^ 2 := by
  rw [abelRatio, lPoly, norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_inv, div_eq_mul_inv, mul_pow]

variable {D}

theorem norm_mul_le_of_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hD : ∀ i, ‖D.β i‖ ≤ 1) {v : ℂ} (hv : ‖v‖ = 1) (i : ι) :
    ‖(ρ : ℂ) * D.β i * v‖ ≤ ρ := by
  rw [norm_mul, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
  exact mul_le_of_le_one_right hρ0 (hD i)

/-- The Abel integrand converges at each point of the circle. -/
theorem tendsto_abel_integrand {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hD : ∀ i, ‖D.β i‖ ≤ 1) {v : ℂ}
    (hv : ‖v‖ = 1) :
    Tendsto (fun N => ‖lPoly D v‖ ^ 2 * ‖Complex.exp ((abelPoly D ρ N).eval v)‖ ^ 2) atTop
      (𝓝 (abelRatio D ρ v)) := by
  have hz : ∀ i, ‖(ρ : ℂ) * D.β i * v‖ < 1 := fun i => (norm_mul_le_of_le hρ0 hD hv i).trans_lt hρ1
  have h1 : Tendsto (fun N => Complex.exp ((abelPoly D ρ N).eval v)) atTop
      (𝓝 (∏ i, (1 - (ρ : ℂ) * D.β i * v)⁻¹)) := by
    have h := tendsto_finset_prod Finset.univ (fun i _ => tendsto_exp_partial (hz i))
    refine h.congr fun N => ?_
    rw [eval_abelPoly, Complex.exp_sum]
  rw [abelRatio_eq]
  exact (h1.norm.pow 2).const_mul _

/-- A uniform bound for the mollifier at fixed `ρ`. -/
theorem norm_eval_abelPoly_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hD : ∀ i, ‖D.β i‖ ≤ 1) {v : ℂ}
    (hv : ‖v‖ = 1) (N : ℕ) :
    ‖(abelPoly D ρ N).eval v‖ ≤ Fintype.card ι * (1 - ρ)⁻¹ := by
  rw [eval_abelPoly]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
  refine (norm_sum_le _ _).trans ?_
  have hz := norm_mul_le_of_le hρ0 hD hv i
  calc ∑ k ∈ Finset.range (N + 1), ‖((ρ : ℂ) * D.β i * v) ^ k / k‖
      ≤ ∑ k ∈ Finset.range (N + 1), ρ ^ k := Finset.sum_le_sum fun k _ => by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp
        · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          rw [norm_div, norm_pow, Complex.norm_natCast]
          exact (div_le_self (pow_nonneg (norm_nonneg _) k) h1).trans
            (pow_le_pow_left₀ (norm_nonneg _) hz k)
    _ ≤ (1 - ρ)⁻¹ := by
        rw [← tsum_geometric_of_lt_one hρ0 hρ1]
        exact (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum _ fun k _ => pow_nonneg hρ0 k

theorem sq_norm_lPoly_le (hD : ∀ i, ‖D.β i‖ ≤ 1) {v : ℂ} (hv : ‖v‖ = 1) :
    ‖lPoly D v‖ ^ 2 ≤ (4 : ℝ) ^ Fintype.card ι := by
  rw [lPoly, norm_prod, ← Finset.prod_pow, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
  have h1 : ‖1 - D.β i * v‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, hv, mul_one]
    linarith [hD i]
  nlinarith [norm_nonneg (1 - D.β i * v)]

/-- **Each Abel mollifier tends to the dilation quotient.** -/
theorem tendsto_abelBudget {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hD : ∀ i, ‖D.β i‖ ≤ 1) :
    Tendsto (abelBudget D ρ) atTop (𝓝 (Real.circleAverage (abelRatio D ρ) 0 1)) := by
  have hexp : (fun N => abelBudget D ρ N) = fun N => Real.circleAverage
      (fun v => ‖lPoly D v‖ ^ 2 * ‖Complex.exp ((abelPoly D ρ N).eval v)‖ ^ 2) 0 1 := rfl
  rw [show abelBudget D ρ = _ from hexp]
  refine tendsto_circleAverage_of_bounded
    (C := (4 : ℝ) ^ Fintype.card ι * Real.exp (Fintype.card ι * (1 - ρ)⁻¹) ^ 2)
    (Eventually.of_forall fun N => ?_) (Eventually.of_forall fun N v hv => ?_)
    (Eventually.of_forall fun θ => tendsto_abel_integrand hρ0 hρ1 hD (by simp [norm_circleMap_zero]))
  · have h1 := continuous_lPoly D
    have h2 : Continuous fun v => Complex.exp ((abelPoly D ρ N).eval v) :=
      Complex.continuous_exp.comp (abelPoly D ρ N).continuous
    exact ((h1.norm.pow 2).mul (h2.norm.pow 2)).measurable
  · rw [abs_of_nonneg (by positivity)]
    have h1 := sq_norm_lPoly_le hD hv
    have h2 : ‖Complex.exp ((abelPoly D ρ N).eval v)‖ ≤ Real.exp (Fintype.card ι * (1 - ρ)⁻¹) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (norm_eval_abelPoly_le hρ0 hρ1 hD hv N))
    exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity) (by positivity)

theorem measurable_abelRatio (ρ : ℝ) : Measurable (abelRatio D ρ) := by
  have e : abelRatio D ρ = fun v => ∏ i, (‖1 - D.β i * v‖ / ‖1 - (ρ : ℂ) * D.β i * v‖) ^ 2 := rfl
  rw [e]
  refine Finset.measurable_fun_prod _ fun i _ => ?_
  have h1 : Continuous fun v : ℂ => ‖1 - D.β i * v‖ := by fun_prop
  have h2 : Continuous fun v : ℂ => ‖1 - (ρ : ℂ) * D.β i * v‖ := by fun_prop
  exact (h1.measurable.div h2.measurable).pow_const 2

/-- One factor of the quotient is at most `2`: Castelnuovo gives the domination. -/
theorem factor_le_two {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hD : ∀ i, ‖D.β i‖ ≤ 1) {v : ℂ} (hv : ‖v‖ = 1)
    (i : ι) : ‖1 - D.β i * v‖ / ‖1 - (ρ : ℂ) * D.β i * v‖ ≤ 2 := by
  have hz : ‖D.β i * v‖ ≤ 1 := by
    rw [norm_mul, hv, mul_one]
    exact hD i
  have hle := norm_one_sub_le_two_mul h0 h1.le hz
  have e : (ρ : ℂ) * (D.β i * v) = (ρ : ℂ) * D.β i * v := by ring
  rw [e] at hle
  have hne : 0 < ‖1 - (ρ : ℂ) * D.β i * v‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have h3 : (ρ : ℂ) * D.β i * v = 1 := (sub_eq_zero.mp h).symm
    have h4 := norm_mul_le_of_le h0 hD hv i
    rw [h3, norm_one] at h4
    exact absurd h1 (not_lt.mpr h4)
  exact (div_le_iff₀ hne).mpr hle

theorem abs_abelRatio_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hD : ∀ i, ‖D.β i‖ ≤ 1) {v : ℂ} (hv : ‖v‖ = 1) :
    |abelRatio D ρ v| ≤ (4 : ℝ) ^ Fintype.card ι := by
  have hnn : 0 ≤ abelRatio D ρ v := Finset.prod_nonneg fun _ _ => by positivity
  rw [abs_of_nonneg hnn, abelRatio, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
  have hq := pow_le_pow_left₀ (by positivity) (factor_le_two h0 h1 hD hv i) 2
  norm_num at hq
  exact hq

/-- At a point where `P` does not vanish, the quotient tends to `1`. -/
theorem tendsto_abelRatio {v : ℂ} (hv : lPoly D v ≠ 0) :
    Tendsto (fun ρ : ℝ => abelRatio D ρ v) (𝓝[<] 1) (𝓝 1) := by
  have hne : ∀ i, ‖1 - D.β i * v‖ ≠ 0 := fun i => norm_ne_zero_iff.mpr fun h0 => hv <| by
    rw [lPoly]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  have hi : ∀ i, Tendsto (fun ρ : ℝ => (‖1 - D.β i * v‖ / ‖1 - (ρ : ℂ) * D.β i * v‖) ^ 2)
      (𝓝[<] 1) (𝓝 1) := fun i => by
    have hcn : Continuous fun ρ : ℝ => ‖1 - (ρ : ℂ) * D.β i * v‖ := by fun_prop
    have h1 : Tendsto (fun ρ : ℝ => ‖1 - (ρ : ℂ) * D.β i * v‖) (𝓝[<] 1) (𝓝 ‖1 - D.β i * v‖) := by
      have h2 := hcn.tendsto 1
      simp only [Complex.ofReal_one, one_mul] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have h3 := ((tendsto_const_nhds (x := ‖1 - D.β i * v‖)).div h1 (hne i)).pow 2
    rw [div_self (hne i), one_pow] at h3
    exact h3
  have h := tendsto_finset_prod Finset.univ fun i _ => hi i
  rw [Finset.prod_const_one] at h
  exact h

/-- **The dilation quotient has mean tending to `1`.** This is where Castelnuovo enters: the quotient is dominated by `4^{|ι|}`. -/
theorem tendsto_circleAverage_abelRatio (hD : ∀ i, ‖D.β i‖ ≤ 1) :
    Tendsto (fun ρ : ℝ => Real.circleAverage (abelRatio D ρ) 0 1) (𝓝[<] 1) (𝓝 1) := by
  have hpos : ∀ᶠ ρ : ℝ in 𝓝[<] 1, 0 < ρ :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
  have hlt : ∀ᶠ ρ : ℝ in 𝓝[<] 1, ρ < 1 := self_mem_nhdsWithin
  have hb : ∀ᶠ ρ : ℝ in 𝓝[<] 1, ∀ v : ℂ, ‖v‖ = 1 → |abelRatio D ρ v| ≤ (4 : ℝ) ^ Fintype.card ι := by
    filter_upwards [hpos, hlt] with ρ h0 h1 v hv
    exact abs_abelRatio_le h0.le h1 hD hv
  have hcount : (circleMap 0 1 ⁻¹' {v : ℂ | lPoly D v = 0}).Countable :=
    (countable_lPoly_zeros D).preimage_circleMap 0 one_ne_zero
  have hl : ∀ᵐ θ : ℝ, Tendsto (fun ρ : ℝ => abelRatio D ρ (circleMap 0 1 θ)) (𝓝[<] 1) (𝓝 1) := by
    filter_upwards [hcount.ae_notMem volume] with θ hθ
    have hne : lPoly D (circleMap 0 1 θ) ≠ 0 := hθ
    exact tendsto_abelRatio hne
  have hm : ∀ᶠ ρ : ℝ in 𝓝[<] 1, Measurable (abelRatio D ρ) :=
    Eventually.of_forall fun ρ => measurable_abelRatio ρ
  have hmain := tendsto_circleAverage_of_bounded (l := 𝓝[<] (1 : ℝ)) (F := fun ρ => abelRatio D ρ)
    (f := fun _ : ℂ => (1 : ℝ)) hm hb hl
  have hc : Real.circleAverage (fun _ : ℂ => (1 : ℝ)) 0 1 = 1 := Real.circleAverage_const 1 0 1
  rw [hc] at hmain
  exact hmain

/-- **Castelnuovo gives explicit near-extremal mollifiers.** -/
theorem exists_abelBudget_lt (hD : ∀ i, ‖D.β i‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ N : ℕ, abelBudget D ρ N < 1 + ε := by
  have h1 := (tendsto_circleAverage_abelRatio hD).eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + ε))
  have hpos : ∀ᶠ ρ : ℝ in 𝓝[<] 1, 0 < ρ :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
  have hlt : ∀ᶠ ρ : ℝ in 𝓝[<] 1, ρ < 1 := self_mem_nhdsWithin
  obtain ⟨ρ, hρ, h0, hρ1⟩ := (h1.and (hpos.and hlt)).exists
  obtain ⟨N, hN⟩ := ((tendsto_abelBudget h0.le hρ1 hD).eventually (gt_mem_nhds hρ)).exists
  exact ⟨ρ, h0.le, hρ1, N, hN⟩

variable (D)

/-- Every Abel budget is at least the Szegő floor. -/
theorem exp_two_mul_innerMass_le_abelBudget (ρ : ℝ) (N : ℕ) :
    Real.exp (2 * innerMass D) ≤ abelBudget D ρ N :=
  (isGLB_curve_budget D).1 ⟨abelPoly D ρ N, abelPoly_coeff_zero D ρ N, rfl⟩

/-- **Castelnuovo is the Abel family.** The Hodge index on the Frobenius span holds iff the Abel mollifiers reach budget `1`. -/
theorem hodgeIndex_iff_abelMollifiers :
    (∀ S d, 0 ≤ D.spanDefect S d) ↔
      ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ N : ℕ, abelBudget D ρ N < 1 + ε := by
  refine D.hodgeIndexOnSpan_iff_unitary.trans ⟨fun hU ε hε => exists_abelBudget_lt (fun i => (hU i).le) hε,
    fun h => (innerMass_eq_zero_iff D).mp ?_⟩
  have hnn : 0 ≤ innerMass D := Finset.sum_nonneg fun _ _ => Real.posLog_nonneg
  have hle : Real.exp (2 * innerMass D) ≤ 1 := le_of_forall_pos_lt_add fun ε hε => by
    obtain ⟨ρ, -, -, N, hN⟩ := h ε hε
    exact (exp_two_mul_innerMass_le_abelBudget D ρ N).trans_lt hN
  have h0 : 2 * innerMass D ≤ 0 := Real.exp_le_one_iff.mp hle
  linarith

/-- **The golden curve has a floor.** No Abel mollifier gets below `φ²`. -/
theorem sq_goldenRatio_le_abelBudget (ρ : ℝ) (N : ℕ) :
    Real.goldenRatio ^ 2 ≤ abelBudget goldenDatum ρ N := by
  have h := exp_two_mul_innerMass_le_abelBudget goldenDatum ρ N
  rwa [innerMass_goldenDatum, two_mul, Real.exp_add, Real.exp_log Real.goldenRatio_pos, ← sq] at h

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
