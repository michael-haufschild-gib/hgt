import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheCriticalExponent

/-!
# The second-order synthesis

The overlap law (`TheCriticalExponent`) synthesizes a fixed test `F` from atoms of width `1/k` at
the log-lattice of level `n₀`; its cell weights `∫_{cell} F` put each cell's mass on the left
endpoint, an error of first order `k/n₀`, so positivity is RH only once the overlap ratio `n₀/k`
beats `√(log k)`. The trapezoid weights `F(a_j)(a_{j+1} − a_{j−1})/2` make the error second order
`(k/n₀)²`, and the window narrows to the fourth root.

* **The trapezoid on a cell** (`abs_integral_sub_trap_le_one`, `abs_integral_sub_trap_le_two`):
  `|∫_p^q G − (q − p)(G(p) + G(q))/2|` is `≤ (q − p) ∫_p^q |G′|` and `≤ (5/4)(q − p)² ∫_p^q |G″|`;
  the Taylor expansions at the two endpoints (`abs_cell_integral_sub_le`) cancel to first order.
  On nodes with gaps `≤ H` the rule `trapRule` errs by `H ∫|G′|` and by `(5/4) H² ∫|G″|`.
* **The trapezoid synthesis** `trapSum F ψ a J r = T(t ↦ F(t) ψ(r − t))`
  (`abs_trapSum_sub_integral_le`): it is within `(5/4) H² (M₂‖ψ‖₁ + 2L‖ψ′‖₁ + M‖ψ″‖₁)` of
  `F ∗ ψ`, and its derivative is `≤ M‖ψ′‖₁ + H(L‖ψ′‖₁ + M‖ψ″‖₁)` (`abs_trapSum_deriv_le`).
  It is an atomic test (`atomicTest_trapWeights`).
* **The synthesis bound** (`exists_atomicTest_weilQuad_le_two`): with `ψ = φ_k` and `H = 1/n₀`,
  the supremum error is `synthErrTwo = (5/4)(1/n₀)²(M₂‖φ‖₁ + 2Lk‖φ′‖₁ + Mk²‖φ″‖₁) + L‖φ‖₁/k`
  while the Lipschitz constant stays `O(k)`; the Lévy energy of the error is
  `O(((k/n₀)² + 1/k)² log k)`.
* **The overlap law at the fourth root** (`riemannHypothesis_iff_atomicFamilies_nonneg_of_growthTwo`):
  for every `C²` profile and every dilation sequence with `(κ_N/N)⁴ log κ_N → 0`
  (`OverlapGrowthTwo`, implied by `OverlapGrowth`), RH holds iff Weil's form is eventually
  nonnegative on the atomic families of width `1/κ_N`. For widths `(log N)^α/N`
  (`riemannHypothesis_iff_atomicFamilies_nonneg_log_quarter`) this holds for every `α > 1/4`.
-/
noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

variable {G G' G'' : ℝ → ℝ}

/-- On `[p, q]`, `|∫_x^y |f|| ≤ ∫_p^q |f|` for `x, y ∈ [p, q]`. -/
theorem abs_integral_abs_le_of_mem {f : ℝ → ℝ} (hf : Continuous f) {p q x y : ℝ}
    (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) : abs (∫ s in x..y, |f s|) ≤ ∫ s in p..q, |f s| := by
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (integral_nonneg hxy fun s _ => abs_nonneg _)]
    exact integral_mono_interval hx.1 hxy hy.2 (Eventually.of_forall fun s => abs_nonneg _)
      (hf.abs.intervalIntegrable p q)
  · rw [integral_symm, abs_neg, abs_of_nonneg (integral_nonneg hxy fun s _ => abs_nonneg _)]
    exact integral_mono_interval hy.1 hxy hx.2 (Eventually.of_forall fun s => abs_nonneg _)
      (hf.abs.intervalIntegrable p q)

/-- **Taylor on a cell**: `|G(t) − G(a) − G′(a)(t − a)| ≤ |t − a| ∫_p^q |G″|` for `a, t ∈ [p, q]`. -/
theorem abs_taylor_le (hG : ∀ s, HasDerivAt G (G' s) s) (hG' : ∀ s, HasDerivAt G' (G'' s) s)
    (hG'' : Continuous G'') {p q a t : ℝ} (ha : a ∈ Icc p q) (ht : t ∈ Icc p q) :
    |G t - G a - G' a * (t - a)| ≤ |t - a| * ∫ s in p..q, |G'' s| := by
  have hc1 : Continuous G' := continuous_iff_continuousAt.mpr fun s => (hG' s).continuousAt
  have h1 : G t - G a = ∫ s in a..t, G' s :=
    (integral_eq_sub_of_hasDerivAt (fun s _ => hG s) (hc1.intervalIntegrable a t)).symm
  have h2 : G t - G a - G' a * (t - a) = ∫ s in a..t, (G' s - G' a) := by
    rw [intervalIntegral.integral_sub (hc1.intervalIntegrable a t) intervalIntegrable_const,
      intervalIntegral.integral_const, h1, smul_eq_mul]
    ring
  rw [h2]
  have hbound : ∀ s ∈ uIoc a t, ‖G' s - G' a‖ ≤ ∫ s in p..q, |G'' s| := by
    intro s hs
    have hsI : s ∈ Icc p q := by
      have := uIoc_subset_uIcc hs
      rcases mem_uIcc.mp this with h | h
      · exact ⟨le_trans ha.1 h.1, le_trans h.2 ht.2⟩
      · exact ⟨le_trans ht.1 h.1, le_trans h.2 ha.2⟩
    have hftc : G' s - G' a = ∫ u in a..s, G'' u :=
      (integral_eq_sub_of_hasDerivAt (fun u _ => hG' u) (hG''.intervalIntegrable a s)).symm
    have hn := intervalIntegral.norm_integral_le_abs_integral_norm (f := G'') (a := a) (b := s)
      (μ := volume)
    simp only [Real.norm_eq_abs] at hn
    rw [Real.norm_eq_abs, hftc]
    exact hn.trans (abs_integral_abs_le_of_mem hG'' ha hsI)
  have := norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at this
  calc |∫ s in a..t, (G' s - G' a)| ≤ (∫ s in p..q, |G'' s|) * |t - a| := this
    _ = |t - a| * ∫ s in p..q, |G'' s| := mul_comm _ _

/-- **The cell estimate**: on `[p, q] ∋ a` with `q − p ≤ H`, `a − p ≤ H`, `q − a ≤ H`,
`|∫_p^q G − G(a)(q − p) − G′(a)((q − a)² − (p − a)²)/2| ≤ (q − p) H ∫_p^q |G″|`. -/
theorem abs_cell_integral_sub_le (hG : ∀ s, HasDerivAt G (G' s) s)
    (hG' : ∀ s, HasDerivAt G' (G'' s) s) (hG'' : Continuous G'') {p q a H : ℝ} (hpa : p ≤ a)
    (haq : a ≤ q) (hap : a - p ≤ H) (hqa : q - a ≤ H) :
    |(∫ t in p..q, G t) - G a * (q - p) - G' a * (((q - a) ^ 2 - (p - a) ^ 2) / 2)| ≤
      (q - p) * H * ∫ s in p..q, |G'' s| := by
  have hpq : p ≤ q := hpa.trans haq
  have hc0 : Continuous G := continuous_iff_continuousAt.mpr fun s => (hG s).continuousAt
  have hlin : ∫ t in p..q, (t - a) = ((q - a) ^ 2 - (p - a) ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_id intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hrest : (∫ t in p..q, G t) - G a * (q - p) - G' a * (((q - a) ^ 2 - (p - a) ^ 2) / 2) =
      ∫ t in p..q, (G t - G a - G' a * (t - a)) := by
    have i1 : IntervalIntegrable (fun t => G t - G a) volume p q :=
      (hc0.sub continuous_const).intervalIntegrable p q
    have i2 : IntervalIntegrable (fun t => G' a * (t - a)) volume p q :=
      (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable p q
    rw [intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_sub (hc0.intervalIntegrable p q) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul, hlin]
    ring
  rw [hrest]
  have hI : 0 ≤ ∫ s in p..q, |G'' s| := integral_nonneg hpq fun s _ => abs_nonneg _
  have hbound : ∀ t ∈ uIoc p q, ‖G t - G a - G' a * (t - a)‖ ≤ H * ∫ s in p..q, |G'' s| := by
    intro t ht
    rw [uIoc_of_le hpq] at ht
    rw [Real.norm_eq_abs]
    refine (abs_taylor_le hG hG' hG'' ⟨hpa, haq⟩ ⟨ht.1.le, ht.2⟩).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hI
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have := norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpq)] at this
  linarith

/-- `|G(y) − G(x)| ≤ ∫_p^q |G′|` for `x, y ∈ [p, q]`. -/
theorem abs_sub_le_integral_abs_deriv (hG : ∀ s, HasDerivAt G (G' s) s) (hG'c : Continuous G')
    {p q x y : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) :
    |G y - G x| ≤ ∫ s in p..q, |G' s| := by
  have h : G y - G x = ∫ s in x..y, G' s :=
    (integral_eq_sub_of_hasDerivAt (fun s _ => hG s) (hG'c.intervalIntegrable x y)).symm
  have hn := intervalIntegral.norm_integral_le_abs_integral_norm (f := G') (a := x) (b := y)
    (μ := volume)
  simp only [Real.norm_eq_abs] at hn
  rw [h]
  exact hn.trans (abs_integral_abs_le_of_mem hG'c hx hy)

/-- **The trapezoid on a cell, first order**: `|∫_p^q G − (q − p)(G(p) + G(q))/2| ≤
(q − p) ∫_p^q |G′|`. -/
theorem abs_integral_sub_trap_le_one (hG : ∀ s, HasDerivAt G (G' s) s) (hG'c : Continuous G')
    {p q : ℝ} (hpq : p ≤ q) :
    |(∫ t in p..q, G t) - (q - p) * ((G p + G q) / 2)| ≤ (q - p) * ∫ s in p..q, |G' s| := by
  have hc0 : Continuous G := continuous_iff_continuousAt.mpr fun s => (hG s).continuousAt
  have hI : 0 ≤ ∫ s in p..q, |G' s| := integral_nonneg hpq fun s _ => abs_nonneg _
  have hp : p ∈ Icc p q := ⟨le_rfl, hpq⟩
  have hq : q ∈ Icc p q := ⟨hpq, le_rfl⟩
  have hbound : ∀ t ∈ uIoc p q, ‖G t - (G p + G q) / 2‖ ≤ ∫ s in p..q, |G' s| := by
    intro t ht
    rw [uIoc_of_le hpq] at ht
    have htI : t ∈ Icc p q := ⟨ht.1.le, ht.2⟩
    have h1 := abs_sub_le_integral_abs_deriv hG hG'c hp htI
    have h2 := abs_sub_le_integral_abs_deriv hG hG'c hq htI
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(abs_le.mp h1).1, (abs_le.mp h1).2, (abs_le.mp h2).1,
      (abs_le.mp h2).2]
  have e : (∫ t in p..q, G t) - (q - p) * ((G p + G q) / 2) =
      ∫ t in p..q, (G t - (G p + G q) / 2) := by
    rw [intervalIntegral.integral_sub (hc0.intervalIntegrable p q) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [e]
  have := norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpq)] at this
  linarith

/-- **The trapezoid on a cell, second order**: `|∫_p^q G − (q − p)(G(p) + G(q))/2| ≤
(5/4)(q − p)² ∫_p^q |G″|`. The Taylor expansions at the two endpoints cancel to first order up to
`G′(q) − G′(p) = ∫_p^q G″`. -/
theorem abs_integral_sub_trap_le_two (hG : ∀ s, HasDerivAt G (G' s) s)
    (hG' : ∀ s, HasDerivAt G' (G'' s) s) (hG'' : Continuous G'') {p q : ℝ} (hpq : p ≤ q) :
    |(∫ t in p..q, G t) - (q - p) * ((G p + G q) / 2)| ≤
      5 / 4 * (q - p) ^ 2 * ∫ s in p..q, |G'' s| := by
  set I := ∫ s in p..q, |G'' s|
  have hI : 0 ≤ I := integral_nonneg hpq fun s _ => abs_nonneg _
  have hp := abs_cell_integral_sub_le hG hG' hG'' (H := q - p) le_rfl hpq (by linarith) le_rfl
  have hq := abs_cell_integral_sub_le hG hG' hG'' (H := q - p) hpq le_rfl le_rfl (by linarith)
  have hd : |G' q - G' p| ≤ I := by
    have h := abs_sub_le_integral_abs_deriv hG' hG'' (p := p) (q := q) ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩
    exact h
  rw [show (p - p) ^ 2 = 0 by ring, show (q - q) ^ 2 = 0 by ring,
    show (p - q) ^ 2 = (q - p) ^ 2 by ring] at *
  set D := (q - p) ^ 2
  have hD : 0 ≤ D := sq_nonneg _
  have hpD : (q - p) * (q - p) * I = D * I := by simp only [D]; ring
  rw [hpD] at hp hq
  have h1 := abs_le.mp hp
  have h2 := abs_le.mp hq
  have h3 := abs_le.mp hd
  have h4 : (G' q - G' p) * D ≤ I * D := mul_le_mul_of_nonneg_right h3.2 hD
  have h5 : -I * D ≤ (G' q - G' p) * D := mul_le_mul_of_nonneg_right h3.1 hD
  rw [abs_le]
  constructor <;> nlinarith

/-- The trapezoid rule on the nodes `a₀ ≤ … ≤ a_J`. -/
def trapRule (G : ℝ → ℝ) (a : ℕ → ℝ) (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range J, (a (i + 1) - a i) * ((G (a i) + G (a (i + 1))) / 2)

section TrapRule

variable {a : ℕ → ℝ} {J : ℕ} {H : ℝ}

/-- The trapezoid error is the sum of the cell errors. -/
theorem trapRule_sub_integral (hGc : Continuous G) :
    trapRule G a J - ∫ t in a 0..a J, G t = ∑ i ∈ Finset.range J,
      ((a (i + 1) - a i) * ((G (a i) + G (a (i + 1))) / 2) - ∫ t in a i..a (i + 1), G t) := by
  rw [← sum_integral_adjacent_intervals fun i _ => hGc.intervalIntegrable _ _, trapRule,
    ← Finset.sum_sub_distrib]

/-- `Σ_{i<J} ∫_{a_i}^{a_{i+1}} |f| = ∫_{a_0}^{a_J} |f|`. -/
theorem sum_integral_abs_cells {f : ℝ → ℝ} (hf : Continuous f) :
    ∑ i ∈ Finset.range J, ∫ s in a i..a (i + 1), |f s| = ∫ s in a 0..a J, |f s| :=
  sum_integral_adjacent_intervals fun _ _ => hf.abs.intervalIntegrable _ _

/-- **The trapezoid rule, first order**: gaps `≤ H` give `|T(G) − ∫ G| ≤ H ∫ |G′|`. -/
theorem abs_trapRule_sub_le_one (ha : Monotone a) (hgap : ∀ i < J, a (i + 1) - a i ≤ H)
    (hG : ∀ s, HasDerivAt G (G' s) s) (hG'c : Continuous G') :
    |trapRule G a J - ∫ t in a 0..a J, G t| ≤ H * ∫ s in a 0..a J, |G' s| := by
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun s => (hG s).continuousAt
  rw [trapRule_sub_integral hGc, ← sum_integral_abs_cells hG'c, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hai : a i ≤ a (i + 1) := ha (Nat.le_succ i)
  rw [abs_sub_comm]
  exact (abs_integral_sub_trap_le_one hG hG'c hai).trans (mul_le_mul_of_nonneg_right
    (hgap i (Finset.mem_range.mp hi)) (integral_nonneg hai fun s _ => abs_nonneg _))

/-- **The trapezoid rule, second order**: gaps `≤ H` give `|T(G) − ∫ G| ≤ (5/4) H² ∫ |G″|`. -/
theorem abs_trapRule_sub_le_two (ha : Monotone a) (hgap : ∀ i < J, a (i + 1) - a i ≤ H)
    (hG : ∀ s, HasDerivAt G (G' s) s) (hG' : ∀ s, HasDerivAt G' (G'' s) s)
    (hG'' : Continuous G'') :
    |trapRule G a J - ∫ t in a 0..a J, G t| ≤ 5 / 4 * H ^ 2 * ∫ s in a 0..a J, |G'' s| := by
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun s => (hG s).continuousAt
  rw [trapRule_sub_integral hGc, ← sum_integral_abs_cells hG'', Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hai : a i ≤ a (i + 1) := ha (Nat.le_succ i)
  have hsq : (a (i + 1) - a i) ^ 2 ≤ H ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hai) (hgap i (Finset.mem_range.mp hi)) 2
  rw [abs_sub_comm]
  refine (abs_integral_sub_trap_le_two hG hG' hG'' hai).trans ?_
  have hI : 0 ≤ ∫ s in a i..a (i + 1), |G'' s| := integral_nonneg hai fun s _ => abs_nonneg _
  exact mul_le_mul_of_nonneg_right (by linarith) hI

end TrapRule

/-! ### The trapezoid synthesis -/

section TrapSynthesis

variable {F F1 F2 ψ ψ1 ψ2 : ℝ → ℝ} {a : ℕ → ℝ} {J : ℕ} {H M L M2 : ℝ}

/-- The trapezoid synthesis `S(r) = T(t ↦ F(t) ψ(r − t))`: the atom `a_j` carries
`F(a_j)(a_{j+1} − a_{j−1})/2`. -/
def trapSum (F ψ : ℝ → ℝ) (a : ℕ → ℝ) (J : ℕ) (r : ℝ) : ℝ :=
  trapRule (fun t => F t * ψ (r - t)) a J

theorem hasDerivAt_mul_comp_sub {f f' g g' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hg : ∀ s, HasDerivAt g (g' s) s) (r t : ℝ) :
    HasDerivAt (fun t => f t * g (r - t)) (f' t * g (r - t) - f t * g' (r - t)) t := by
  have h := (hf t).mul ((hg (r - t)).comp t ((hasDerivAt_id t).const_sub r))
  exact h.congr_deriv (by simp only [Function.comp_apply, mul_neg, mul_one]; ring)

theorem hasDerivAt_trapSum (hψ : ∀ s, HasDerivAt ψ (ψ1 s) s) (r : ℝ) :
    HasDerivAt (trapSum F ψ a J) (trapSum F ψ1 a J r) r := by
  unfold trapSum trapRule
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.const_mul _ (HasDerivAt.div_const ?_ 2)
  have h1 := ((hψ (r - a i)).comp r ((hasDerivAt_id r).sub_const (a i))).const_mul (F (a i))
  have h2 := ((hψ (r - a (i + 1))).comp r ((hasDerivAt_id r).sub_const (a (i + 1)))).const_mul
    (F (a (i + 1)))
  simp only [id, mul_one] at h1 h2
  exact h1.add h2

/-- `∫_p^q |f(t) g(r − t)| ≤ B ‖g‖₁` for `|f| ≤ B`. -/
theorem integral_abs_mul_comp_sub_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hgi : Integrable g) {B : ℝ} (hfB : ∀ t, |f t| ≤ B) {p q : ℝ} (hpq : p ≤ q) (r : ℝ) :
    ∫ t in p..q, |f t * g (r - t)| ≤ B * ∫ s, |g s| := by
  have hgr : Continuous fun t => g (r - t) := hg.comp (continuous_const.sub continuous_id)
  have hint : Integrable fun t => B * |g (r - t)| := ((hgi.comp_sub_left r).abs).const_mul B
  calc ∫ t in p..q, |f t * g (r - t)| ≤ ∫ t in p..q, B * |g (r - t)| := by
        refine integral_mono_on hpq ((hf.mul hgr).abs.intervalIntegrable _ _)
          ((continuous_const.mul hgr.abs).intervalIntegrable _ _) fun t _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hfB t) (abs_nonneg _)
    _ ≤ ∫ t, B * |g (r - t)| := by
        rw [intervalIntegral.integral_of_le hpq]
        refine setIntegral_le_integral hint (Eventually.of_forall fun t => ?_)
        exact mul_nonneg ((abs_nonneg _).trans (hfB 0)) (abs_nonneg _)
    _ = B * ∫ s, |g s| := by
        rw [MeasureTheory.integral_const_mul, integral_sub_left_eq_self (fun s => |g s|) volume r]

/-- A function vanishing off `[a₀, a_J]` integrates over `[a₀, a_J]`. -/
theorem integral_eq_intervalIntegral_of_supp {G : ℝ → ℝ} (ha : Monotone a)
    (hG : ∀ t, t ∉ Icc (a 0) (a J) → G t = 0) : ∫ t, G t = ∫ t in a 0..a J, G t := by
  rw [intervalIntegral.integral_of_le (ha (Nat.zero_le J)), ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hG t ht).symm

/-- **The trapezoid synthesis is second-order accurate**:
`|S(r) − ∫ F(t) ψ(r − t) dt| ≤ (5/4) H² (M₂ ‖ψ‖₁ + 2L ‖ψ′‖₁ + M ‖ψ″‖₁)`. -/
theorem abs_trapSum_sub_integral_le (ha : Monotone a) (hgap : ∀ i < J, a (i + 1) - a i ≤ H)
    (hF : ∀ t, HasDerivAt F (F1 t) t) (hF1 : ∀ t, HasDerivAt F1 (F2 t) t) (hF2c : Continuous F2)
    (hFM : ∀ t, |F t| ≤ M) (hF1M : ∀ t, |F1 t| ≤ L) (hF2M : ∀ t, |F2 t| ≤ M2)
    (hFsupp : ∀ t, t ∉ Icc (a 0) (a J) → F t = 0)
    (hψ : ∀ s, HasDerivAt ψ (ψ1 s) s) (hψ1 : ∀ s, HasDerivAt ψ1 (ψ2 s) s) (hψ2c : Continuous ψ2)
    (hψi : Integrable ψ) (hψ1i : Integrable ψ1) (hψ2i : Integrable ψ2) (r : ℝ) :
    |trapSum F ψ a J r - ∫ t, F t * ψ (r - t)| ≤
      5 / 4 * H ^ 2 * (M2 * (∫ s, |ψ s|) + 2 * L * (∫ s, |ψ1 s|) + M * ∫ s, |ψ2 s|) := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun s => (hF s).continuousAt
  have hF1c : Continuous F1 := continuous_iff_continuousAt.mpr fun s => (hF1 s).continuousAt
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun s => (hψ s).continuousAt
  have hψ1c : Continuous ψ1 := continuous_iff_continuousAt.mpr fun s => (hψ1 s).continuousAt
  have hsub : Continuous fun t : ℝ => r - t := continuous_const.sub continuous_id
  set G'' : ℝ → ℝ := fun t => F2 t * ψ (r - t) - 2 * (F1 t * ψ1 (r - t)) + F t * ψ2 (r - t)
  have hG : ∀ t, HasDerivAt (fun t => F t * ψ (r - t))
      (F1 t * ψ (r - t) - F t * ψ1 (r - t)) t := hasDerivAt_mul_comp_sub hF hψ r
  have hG' : ∀ t, HasDerivAt (fun t => F1 t * ψ (r - t) - F t * ψ1 (r - t)) (G'' t) t :=
    fun t => ((hasDerivAt_mul_comp_sub hF1 hψ r t).sub (hasDerivAt_mul_comp_sub hF hψ1 r t)).congr_deriv
      (by simp only [G'']; ring)
  have hG''c : Continuous G'' :=
    ((hF2c.mul (hψc.comp hsub)).sub (continuous_const.mul (hF1c.mul (hψ1c.comp hsub)))).add
      (hFc.mul (hψ2c.comp hsub))
  have hsupp : ∫ t, F t * ψ (r - t) = ∫ t in a 0..a J, F t * ψ (r - t) :=
    integral_eq_intervalIntegral_of_supp ha fun t ht => by simp only [hFsupp t ht, zero_mul]
  have hJ : a 0 ≤ a J := ha (Nat.zero_le J)
  have hT := abs_trapRule_sub_le_two ha hgap hG hG' hG''c
  rw [hsupp]
  refine hT.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- the second derivative in `L¹`
  have i1 : IntervalIntegrable (fun t => |F2 t * ψ (r - t)|) volume (a 0) (a J) :=
    (hF2c.mul (hψc.comp hsub)).abs.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => 2 * |F1 t * ψ1 (r - t)|) volume (a 0) (a J) :=
    (continuous_const.mul (hF1c.mul (hψ1c.comp hsub)).abs).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => |F t * ψ2 (r - t)|) volume (a 0) (a J) :=
    (hFc.mul (hψ2c.comp hsub)).abs.intervalIntegrable _ _
  calc ∫ t in a 0..a J, |G'' t| ≤ ∫ t in a 0..a J,
        (|F2 t * ψ (r - t)| + 2 * |F1 t * ψ1 (r - t)| + |F t * ψ2 (r - t)|) := by
        refine integral_mono_on hJ (hG''c.abs.intervalIntegrable _ _) ((i1.add i2).add i3)
          fun t _ => ?_
        simp only [G'']
        have := abs_add_le (F2 t * ψ (r - t) - 2 * (F1 t * ψ1 (r - t))) (F t * ψ2 (r - t))
        have := abs_sub (F2 t * ψ (r - t)) (2 * (F1 t * ψ1 (r - t)))
        rw [abs_mul (2 : ℝ), abs_two] at this
        linarith
    _ = (∫ t in a 0..a J, |F2 t * ψ (r - t)|) + 2 * (∫ t in a 0..a J, |F1 t * ψ1 (r - t)|) +
          ∫ t in a 0..a J, |F t * ψ2 (r - t)| := by
        rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
          intervalIntegral.integral_const_mul]
    _ ≤ M2 * (∫ s, |ψ s|) + 2 * (L * ∫ s, |ψ1 s|) + M * ∫ s, |ψ2 s| := by
        gcongr
        · exact integral_abs_mul_comp_sub_le hF2c hψc hψi hF2M hJ r
        · exact integral_abs_mul_comp_sub_le hF1c hψ1c hψ1i hF1M hJ r
        · exact integral_abs_mul_comp_sub_le hFc hψ2c hψ2i hFM hJ r
    _ = _ := by ring

/-- **The derivative of the trapezoid synthesis**: `|S′(r)| ≤ M ‖ψ′‖₁ + H (L ‖ψ′‖₁ + M ‖ψ″‖₁)`. -/
theorem abs_trapSum_deriv_le (ha : Monotone a) (hH : 0 ≤ H)
    (hgap : ∀ i < J, a (i + 1) - a i ≤ H) (hF : ∀ t, HasDerivAt F (F1 t) t) (hF1c : Continuous F1)
    (hFM : ∀ t, |F t| ≤ M) (hF1M : ∀ t, |F1 t| ≤ L)
    (hFsupp : ∀ t, t ∉ Icc (a 0) (a J) → F t = 0)
    (hψ1 : ∀ s, HasDerivAt ψ1 (ψ2 s) s) (hψ2c : Continuous ψ2)
    (hψ1i : Integrable ψ1) (hψ2i : Integrable ψ2) (r : ℝ) :
    |trapSum F ψ1 a J r| ≤ M * (∫ s, |ψ1 s|) + H * (L * (∫ s, |ψ1 s|) + M * ∫ s, |ψ2 s|) := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun s => (hF s).continuousAt
  have hψ1c : Continuous ψ1 := continuous_iff_continuousAt.mpr fun s => (hψ1 s).continuousAt
  have hsub : Continuous fun t : ℝ => r - t := continuous_const.sub continuous_id
  have hG : ∀ t, HasDerivAt (fun t => F t * ψ1 (r - t))
      (F1 t * ψ1 (r - t) - F t * ψ2 (r - t)) t := hasDerivAt_mul_comp_sub hF hψ1 r
  have hG'c : Continuous fun t => F1 t * ψ1 (r - t) - F t * ψ2 (r - t) :=
    (hF1c.mul (hψ1c.comp hsub)).sub (hFc.mul (hψ2c.comp hsub))
  have hsupp : ∫ t, F t * ψ1 (r - t) = ∫ t in a 0..a J, F t * ψ1 (r - t) :=
    integral_eq_intervalIntegral_of_supp ha fun t ht => by simp only [hFsupp t ht, zero_mul]
  have hJ : a 0 ≤ a J := ha (Nat.zero_le J)
  have hT := abs_trapRule_sub_le_one ha hgap hG hG'c
  have hI := abs_integral_mul_le_sup_mul hFM hψ1i r
  rw [hsupp] at hI
  have i1 : IntervalIntegrable (fun t => |F1 t * ψ1 (r - t)|) volume (a 0) (a J) :=
    (hF1c.mul (hψ1c.comp hsub)).abs.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => |F t * ψ2 (r - t)|) volume (a 0) (a J) :=
    (hFc.mul (hψ2c.comp hsub)).abs.intervalIntegrable _ _
  have hG' : ∫ t in a 0..a J, |F1 t * ψ1 (r - t) - F t * ψ2 (r - t)| ≤
      L * (∫ s, |ψ1 s|) + M * ∫ s, |ψ2 s| := by
    calc ∫ t in a 0..a J, |F1 t * ψ1 (r - t) - F t * ψ2 (r - t)| ≤
          ∫ t in a 0..a J, (|F1 t * ψ1 (r - t)| + |F t * ψ2 (r - t)|) :=
          integral_mono_on hJ (hG'c.abs.intervalIntegrable _ _) (i1.add i2) fun t _ => abs_sub _ _
      _ = (∫ t in a 0..a J, |F1 t * ψ1 (r - t)|) + ∫ t in a 0..a J, |F t * ψ2 (r - t)| :=
          intervalIntegral.integral_add i1 i2
      _ ≤ _ := add_le_add (integral_abs_mul_comp_sub_le hF1c hψ1c hψ1i hF1M hJ r)
          (integral_abs_mul_comp_sub_le hFc hψ2c hψ2i hFM hJ r)
  have h3 := mul_le_mul_of_nonneg_left hG' hH
  unfold trapSum
  calc |trapRule (fun t => F t * ψ1 (r - t)) a J|
      = |(trapRule (fun t => F t * ψ1 (r - t)) a J - ∫ t in a 0..a J, F t * ψ1 (r - t)) +
          ∫ t in a 0..a J, F t * ψ1 (r - t)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

end TrapSynthesis

/-! ### The trapezoid synthesis on the log-lattice -/

section LogLattice

open ArithmeticElectrostatics

variable {φ F : ℝ → ℝ} {R M L M2 k : ℝ} {n₀ : ℕ}

/-- The second-order supremum error
`(5/4)(1/n₀)² (M₂ ‖φ‖₁ + 2L k ‖φ′‖₁ + M k² ‖φ″‖₁) + L ‖φ‖₁/k`. -/
def synthErrTwo (A0 A1 A2 M L M2 k : ℝ) (n₀ : ℕ) : ℝ :=
  5 / 4 * (1 / n₀) ^ 2 * (M2 * A0 + 2 * L * (k * A1) + M * (k * (k * A2))) + L * (1 / k) * A0

/-- The Lipschitz constant `M k ‖φ′‖₁ + (1/n₀)(L k ‖φ′‖₁ + M k² ‖φ″‖₁) + L` of the error. -/
def synthLipTwo (A1 A2 M L k : ℝ) (n₀ : ℕ) : ℝ :=
  M * (k * A1) + 1 / n₀ * (L * (k * A1) + M * (k * (k * A2))) + L

theorem cellCount_add_le_block : n₀ + cellCount n₀ R ≤ n₀ * blockSize R := by
  have hJ : (cellCount n₀ R : ℝ) < n₀ * Real.exp (2 * R) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hB : 1 + Real.exp (2 * R) ≤ blockSize R := Nat.le_ceil _
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have : ((n₀ + cellCount n₀ R : ℕ) : ℝ) < ((n₀ * blockSize R + 1 : ℕ) : ℝ) := by
    push_cast; nlinarith
  have := (Nat.cast_lt (α := ℝ)).mp this
  omega

/-- The trapezoid weights: the atom `n₀ + j` carries the right half of its left cell and the left
half of its right cell, `F(a_j)(a_{j+1} − a_{j−1})/2`. -/
def trapWeights (F : ℝ → ℝ) (a : ℕ → ℝ) (n₀ J : ℕ) (n : ℕ) : ℝ :=
  (if n₀ ≤ n ∧ n < n₀ + J then (a (n - n₀ + 1) - a (n - n₀)) * F (a (n - n₀)) / 2 else 0) +
    (if n₀ + 1 ≤ n ∧ n < n₀ + 1 + J then
      (a (n - (n₀ + 1) + 1) - a (n - (n₀ + 1))) * F (a (n - (n₀ + 1) + 1)) / 2 else 0)

/-- An atomic test with weights on the window `m ≤ n < m + J` is a sum over the window. -/
theorem atomicTest_window {ψ : ℝ → ℝ} {m J N : ℕ} (hm : 1 ≤ m) (hJN : m + J ≤ N + 1)
    (w : ℕ → ℝ) (u : ℝ) :
    atomicTest N (fun n => if m ≤ n ∧ n < m + J then w (n - m) else 0) ψ u =
      ∑ j ∈ Finset.range J, w j * ψ (u - Real.log ((m + j : ℕ) : ℝ)) := by
  unfold atomicTest
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (if m ≤ n ∧ n < m + J then w (n - m) else 0) * ψ (u - Real.log n) =
        if n ∈ Finset.Ico m (m + J) then w (n - m) * ψ (u - Real.log n) else 0 := by
    intro n _
    by_cases h : m ≤ n ∧ n < m + J
    · rw [if_pos h, if_pos (Finset.mem_Ico.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (Finset.mem_Ico.mp h')), zero_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter,
    show (Finset.Icc 1 N).filter (· ∈ Finset.Ico m (m + J)) = Finset.Ico m (m + J) by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_sub_cancel_left]

/-- The atomic test with the trapezoid weights is the trapezoid synthesis, translated. -/
theorem atomicTest_trapWeights {ψ : ℝ → ℝ} {J N : ℕ} (hn₀ : 1 ≤ n₀) (hJN : n₀ + J ≤ N)
    (c u : ℝ) :
    atomicTest N (trapWeights F (logNode n₀ c) n₀ J) ψ u =
      trapSum F ψ (logNode n₀ c) J (u - c) := by
  set a := logNode n₀ c
  have h1 := atomicTest_window (ψ := ψ) (m := n₀) (J := J) (N := N) hn₀ (by omega)
    (fun j => (a (j + 1) - a j) * F (a j) / 2) u
  have h2 := atomicTest_window (ψ := ψ) (m := n₀ + 1) (J := J) (N := N) (by omega) (by omega)
    (fun j => (a (j + 1) - a j) * F (a (j + 1)) / 2) u
  beta_reduce at h1 h2
  have hsplit : atomicTest N (trapWeights F a n₀ J) ψ u =
      atomicTest N (fun n => if n₀ ≤ n ∧ n < n₀ + J then
        (a (n - n₀ + 1) - a (n - n₀)) * F (a (n - n₀)) / 2 else 0) ψ u +
      atomicTest N (fun n => if n₀ + 1 ≤ n ∧ n < n₀ + 1 + J then
        (a (n - (n₀ + 1) + 1) - a (n - (n₀ + 1))) * F (a (n - (n₀ + 1) + 1)) / 2 else 0) ψ u := by
    unfold atomicTest trapWeights
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => add_mul _ _ _
  rw [hsplit, h1, h2, ← Finset.sum_add_distrib]
  unfold trapSum trapRule
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : u - Real.log ((n₀ + j : ℕ) : ℝ) = u - c - a j := by simp only [a, logNode]; ring
  have e2 : u - Real.log ((n₀ + 1 + j : ℕ) : ℝ) = u - c - a (j + 1) := by
    simp only [a, logNode]; rw [show n₀ + 1 + j = n₀ + (j + 1) by omega]; ring
  rw [e1, e2]
  ring

/-- **Error bounds of the second-order synthesis** `S = Σ_j F(a_j)(a_{j+1} − a_{j−1})/2 · φ_k(· − a_j)`
of `F`: the supremum error, the Lipschitz constant of `S`, the support, the smoothness. -/
theorem synthesis_error_bounds_two (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ 2 F) (hR : 0 ≤ R) (hFR : SupportedIn R F)
    (hFM : ∀ t, |F t| ≤ M) (hF1M : ∀ t, |deriv F t| ≤ L) (hF2M : ∀ t, |deriv (deriv F) t| ≤ M2)
    (hn₀ : 1 ≤ n₀) (hk : 1 ≤ k) :
    (∀ r, |trapSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R) r - F r| ≤
        synthErrTwo (∫ s, |φ s|) (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L M2 k n₀) ∧
      (∀ u v, |trapSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R) u -
          trapSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R) v| ≤
        (M * (k * ∫ s, |deriv φ s|) + 1 / n₀ * (L * (k * ∫ s, |deriv φ s|) +
          M * (k * (k * ∫ s, |deriv (deriv φ) s|)))) * |u - v|) ∧
      SupportedIn (R + 3) (trapSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R)) ∧
      ContDiff ℝ 2 (trapSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R)) := by
  obtain ⟨-, -, hc1, hc2⟩ := profile_derivs hφ
  obtain ⟨hF1, hF2, -, hF2c⟩ := profile_derivs hF
  have hk0 : 0 < k := by linarith
  have hv1 := vanishesOff_deriv hφ1
  have hv2 := vanishesOff_deriv hv1
  have hψv : ∀ s, 1 / k < |s| → dilate k φ s = 0 := fun s hs => dilate_vanishes hφ1 hk0 hs
  have hψc : HasCompactSupport (dilate k φ) := hasCompactSupport_of_vanishes hψv
  have hψ : Continuous (dilate k φ) := continuous_dilate_of hφ.continuous
  have hψi : Integrable (dilate k φ) := hψ.integrable_of_hasCompactSupport hψc
  have hc1' : Continuous fun s => k * deriv φ s := continuous_const.mul hc1
  have hc2' : Continuous fun s => k * (k * deriv (deriv φ) s) :=
    continuous_const.mul (continuous_const.mul hc2)
  have hψ2c : Continuous (dilate k fun s => k * (k * deriv (deriv φ) s)) := continuous_dilate_of hc2'
  have hψ1i : Integrable (dilate k fun s => k * deriv φ s) :=
    integrable_dilate_of hc1' (vanishesOff_const_mul hv1 k) hk0
  have hψ2i : Integrable (dilate k fun s => k * (k * deriv (deriv φ) s)) :=
    integrable_dilate_of hc2' (vanishesOff_const_mul (vanishesOff_const_mul hv2 k) k) hk0
  have hψint : ∫ s, dilate k φ s = 1 := by rw [integral_dilate hk0, hφint]
  have hψabs : ∫ s, |dilate k φ s| = ∫ s, |φ s| := integral_abs_dilate hk0 φ
  have hψ1abs := integral_abs_dilate_mul hk0 (deriv φ)
  have hψ2abs := integral_abs_dilate_mul_mul hk0 (deriv (deriv φ))
  have ha := logNode_monotone hn₀ (Real.log n₀ + R)
  have hgap : ∀ j < cellCount n₀ R, logNode n₀ (Real.log n₀ + R) (j + 1) -
      logNode n₀ (Real.log n₀ + R) j ≤ 1 / n₀ := fun j _ => logNode_gap_le hn₀ _ j
  have hh : (0 : ℝ) ≤ 1 / n₀ := by positivity
  have ha0 := logNode_log_add_zero n₀ R
  have haJ := le_logNode_cellCount (R := R) hn₀
  have halb : ∀ j, -R ≤ logNode n₀ (Real.log n₀ + R) j := fun j => ha0 ▸ ha (Nat.zero_le j)
  have hFsupp : ∀ t, t ∉ Icc (logNode n₀ (Real.log n₀ + R) 0)
      (logNode n₀ (Real.log n₀ + R) (cellCount n₀ R)) → F t = 0 := by
    intro t ht
    refine hFR t ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [ha0] at ht
      exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le (lt_of_le_of_lt haJ ht) (le_abs_self t)
  have hL : ∀ u v, |F u - F v| ≤ L * |u - v| := abs_sub_le_of_hasDerivAt hF1 hF1M
  refine ⟨fun r => ?_, fun u v => ?_, fun r hr => ?_, ?_⟩
  · have h1 := abs_trapSum_sub_integral_le ha hgap hF1 hF2 hF2c hFM hF1M hF2M hFsupp
      (hasDerivAt_dilate_profile hφ) (hasDerivAt_dilate_profile' hφ) hψ2c hψi hψ1i hψ2i r
    have h2 := abs_integral_mul_sub_le hF.continuous hψ hψc hψint hψv hL r
    rw [hψabs, hψ1abs, hψ2abs] at h1
    rw [hψabs] at h2
    calc _ = |(trapSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R) r -
          ∫ t, F t * dilate k φ (r - t)) + ((∫ t, F t * dilate k φ (r - t)) - F r)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by unfold synthErrTwo; linarith)
  · refine abs_sub_le_of_hasDerivAt (hasDerivAt_trapSum (hasDerivAt_dilate_profile hφ))
      (fun r => ?_) u v
    have := abs_trapSum_deriv_le ha hh hgap hF1 (profile_derivs hF).2.2.1 hFM hF1M hFsupp
      (hasDerivAt_dilate_profile' hφ) hψ2c hψ1i hψ2i r
    rw [hψ1abs, hψ2abs] at this
    exact this
  · have hk1 : 1 / k ≤ 1 := by rw [div_le_one hk0]; exact hk
    have hvan : ∀ j ≤ cellCount n₀ R, dilate k φ (r - logNode n₀ (Real.log n₀ + R) j) = 0 := by
      intro j hj
      have hab : |logNode n₀ (Real.log n₀ + R) j| ≤ R + 2 :=
        abs_le.mpr ⟨by linarith [halb j], logNode_le hn₀ hR hj⟩
      exact hψv _ (by
        have := abs_sub_abs_le_abs_sub r (logNode n₀ (Real.log n₀ + R) j)
        linarith)
    unfold trapSum trapRule
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjJ := Finset.mem_range.mp hj
    beta_reduce
    rw [hvan j hjJ.le, hvan (j + 1) hjJ]
    ring
  · unfold trapSum trapRule
    have hd : ∀ c, ContDiff ℝ 2 fun r => dilate k φ (r - c) := fun c =>
      (contDiff_dilate hφ k).comp (contDiff_id.sub contDiff_const)
    exact ContDiff.sum fun j _ => contDiff_const.mul
      (((contDiff_const.mul (hd _)).add (contDiff_const.mul (hd _))).div_const 2)

/-- **The second-order synthesis as a perturbation**: the atomic test of level `n₀ B` with the
trapezoid weights is the translate of `F + D` by `log n₀ + R`, where the error `D` is a `C²` test
supported in `[−(R+3), R+3]` with supremum `≤ e₂ = synthErrTwo` and Lipschitz constant
`synthLipTwo`; its `L²`, `L¹` and Lévy norms follow. -/
theorem exists_synthesis_two (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ 2 F) (hR : 0 ≤ R) (hFR : SupportedIn R F)
    (hFM : ∀ t, |F t| ≤ M) (hF1M : ∀ t, |deriv F t| ≤ L) (hF2M : ∀ t, |deriv (deriv F) t| ≤ M2)
    (hn₀ : 1 ≤ n₀) (hk : 1 ≤ k) :
    ∃ (x : ℕ → ℝ) (D : ℝ → ℝ),
      atomicTest (n₀ * blockSize R) x (dilate k φ) =
        (fun u => F (u - (Real.log n₀ + R)) + D (u - (Real.log n₀ + R))) ∧
      ContDiff ℝ 2 D ∧ HasCompactSupport D ∧ SupportedIn (R + 3) D ∧
      Real.sqrt (∫ u, D u ^ 2) ≤ Real.sqrt (2 * (R + 3)) *
        synthErrTwo (∫ s, |φ s|) (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L M2 k n₀ ∧
      ∫ u, D u ^ 2 ≤ 2 * (R + 3) *
        synthErrTwo (∫ s, |φ s|) (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L M2 k n₀ ^ 2 ∧
      levyEnergy D ≤ synthLevy (R + 3)
          (synthErrTwo (∫ s, |φ s|) (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L M2 k n₀)
          (synthLipTwo (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L k n₀) k ∧
      ∫ u, |D u| ≤ 2 * (R + 3) *
        synthErrTwo (∫ s, |φ s|) (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L M2 k n₀ := by
  obtain ⟨hsup, hlip, hSsupp, hS2⟩ :=
    synthesis_error_bounds_two hφ hφ1 hφint hF hR hFR hFM hF1M hF2M hn₀ hk
  set S := trapSum F (dilate k φ) (logNode n₀ (Real.log n₀ + R)) (cellCount n₀ R)
  set e0 := synthErrTwo (∫ s, |φ s|) (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L M2 k n₀
  set LD := synthLipTwo (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L k n₀
  have hk0 : 0 < k := by linarith
  set D : ℝ → ℝ := fun u => S u - F u
  have hD2 : ContDiff ℝ 2 D := hS2.sub hF
  have hFR3 : SupportedIn (R + 3) F := fun u hu => hFR u (by linarith)
  have hDsupp : SupportedIn (R + 3) D := fun u hu => by
    simp only [D, hSsupp u hu, hFR3 u hu, sub_zero]
  have hDc : HasCompactSupport D := hasCompactSupport_of_vanishes hDsupp
  have he0 : ∀ r, |D r| ≤ e0 := hsup
  have he00 : 0 ≤ e0 := (abs_nonneg _).trans (he0 0)
  have hL := abs_sub_le_of_hasDerivAt (profile_derivs hF).1 hF1M
  have hLD : ∀ u v, |D u - D v| ≤ LD * |u - v| := fun u v => by
    have h1 := hlip u v
    have h2 := hL u v
    have e : D u - D v = (S u - S v) - (F u - F v) := by simp only [D]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have : LD * |u - v| = (M * (k * ∫ s, |deriv φ s|) + 1 / n₀ * (L * (k * ∫ s, |deriv φ s|) +
        M * (k * (k * ∫ s, |deriv (deriv φ) s|)))) * |u - v| + L * |u - v| := by
      simp only [LD, synthLipTwo]; ring
    rw [this]
    exact add_le_add h1 h2
  have hR3 : 0 ≤ R + 3 := by linarith
  have hN1 := integral_abs_le_of_bound hD2.continuous hDc he0 hDsupp hR3
  have hN2 : ∫ u, D u ^ 2 ≤ 2 * (R + 3) * e0 ^ 2 := by
    have := integral_sq_le_of_bound hD2.continuous hDc he0
    nlinarith
  have hLD0 : 0 ≤ LD := by
    have := hLD 1 0
    simp only [sub_zero, abs_one, mul_one] at this
    linarith [abs_nonneg (D 1 - D 0)]
  have hLev : levyEnergy D ≤ synthLevy (R + 3) e0 LD k := by
    have h := levyEnergy_le_lipschitz hD2 hDc hLD (δ := 1 / k) (one_div_pos.mpr hk0)
      (by rw [div_le_one hk0]; exact hk)
    rw [one_div_one_div] at h
    have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
    have hC1 : 0 ≤ levyLipConstant := by
      have h2 : 0 < 1 - Real.exp (-2) := by
        have := Real.exp_lt_one_iff.mpr (show (-2 : ℝ) < 0 by norm_num); linarith
      unfold levyLipConstant
      have := div_pos (mul_pos (by norm_num : (0 : ℝ) < 8) (Real.exp_pos (-(1 / 2)))) h2
      linarith [Real.exp_pos (1 / 2)]
    have hb1 : Real.exp (1 / 2) * LD * (1 / k) * (∫ u, |D u|) ≤
        Real.exp (1 / 2) * LD * (1 / k) * (2 * (R + 3) * e0) :=
      mul_le_mul_of_nonneg_left hN1
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hLD0) (one_div_pos.mpr hk0).le)
    have hb2 : (2 * Real.log k + levyLipConstant) * (∫ u, D u ^ 2) ≤
        (2 * Real.log k + levyLipConstant) * (2 * (R + 3) * e0 ^ 2) :=
      mul_le_mul_of_nonneg_left hN2 (by linarith)
    unfold synthLevy
    linarith
  have hsqD : Real.sqrt (∫ u, D u ^ 2) ≤ Real.sqrt (2 * (R + 3)) * e0 := by
    rw [← Real.sqrt_sq he00, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  refine ⟨trapWeights F (logNode n₀ (Real.log n₀ + R)) n₀ (cellCount n₀ R), D,
    ?_, hD2, hDc, hDsupp, hsqD, hN2, hLev, hN1⟩
  funext u
  rw [atomicTest_trapWeights hn₀ cellCount_add_le_block]
  simp only [D]
  ring

/-- **The second-order synthesis bound**: the atoms of level `n₀ B` synthesize a fixed test `F`
supported in `[−R, R]` up to a motion of Weil's form controlled by `e₂ = synthErrTwo`. -/
theorem exists_atomicTest_weilQuad_le_two (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hR : 0 ≤ R)
    (hFR : SupportedIn R F) (hFM : ∀ t, |F t| ≤ M) (hF1M : ∀ t, |deriv F t| ≤ L)
    (hF2M : ∀ t, |deriv (deriv F) t| ≤ M2) (hn₀ : 1 ≤ n₀) (hk : 1 ≤ k) :
    ∃ x : ℕ → ℝ, weilQuad (atomicTest (n₀ * blockSize R) x (dilate k φ)) ≤ weilQuad F +
      weilErr F (R + 3)
        (synthErrTwo (∫ s, |φ s|) (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L M2 k n₀)
        (synthLevy (R + 3)
          (synthErrTwo (∫ s, |φ s|) (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L M2 k n₀)
          (synthLipTwo (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) M L k n₀) k) := by
  obtain ⟨x, D, hx, hD2, hDc, hDsupp, hsqD, hN2, hLev, hN1⟩ :=
    exists_synthesis_two hφ hφ1 hφint hF hR hFR hFM hF1M hF2M hn₀ hk
  refine ⟨x, ?_⟩
  have hFR3 : SupportedIn (R + 3) F := fun u hu => hFR u (by linarith)
  rw [hx, weilQuad_comp_sub (fun u => F u + D u)]
  exact (weilQuad_add_le hF hFc hD2 hDc hFR3 hDsupp).trans (add_le_add le_rfl
    (weilErr_mono (F := F) hsqD hN2 hLev (integral_nonneg fun u => abs_nonneg _) hN1))

end LogLattice

/-! ### Asymptotics at the fourth root -/

section Asymptotics

/-- **Second-order overlap growth**: dilations `κ_N → ∞` whose overlap ratio `N/κ_N` beats
`(log κ_N)^{1/4}`, i.e. `(κ_N/N)⁴ log κ_N → 0`. -/
def OverlapGrowthTwo (κ : ℕ → ℝ) : Prop :=
  Tendsto κ atTop atTop ∧ Tendsto (fun N : ℕ => (κ N / N) ^ 4 * Real.log (κ N)) atTop (𝓝 0)

/-- First-order overlap growth is second-order overlap growth. -/
theorem OverlapGrowth.two {κ : ℕ → ℝ} (hκ : OverlapGrowth κ) : OverlapGrowthTwo κ := by
  obtain ⟨hk, hkl⟩ := hκ
  refine ⟨hk, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (κ N)) atTop atTop := Real.tendsto_log_atTop.comp hk
  have hr2 : Tendsto (fun N : ℕ => (κ N / N) ^ 2) atTop (𝓝 0) := by
    refine (hkl.div_atTop hlog).congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with N hN
    field_simp
  have := hr2.mul hkl
  rw [zero_mul] at this
  exact this.congr' (Eventually.of_forall fun N => by ring)

/-- The second-order error is `≤ (5/4) x² (M₂‖φ‖₁ + 2L‖φ′‖₁ + M‖φ″‖₁) + L‖φ‖₁/k` when the mesh
`h = 1/n₀` and the ratio `x = h k` satisfy `h ≤ x`. -/
theorem synthErrTwo_le {A0 A1 A2 M L M2 K h x : ℝ} {n : ℕ} (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hL : 0 ≤ L) (hM2 : 0 ≤ M2) (hh0 : 0 ≤ h) (hhx : h ≤ x)
    (hK : h * K = x) (hn : 1 / (n : ℝ) = h) :
    synthErrTwo A0 A1 A2 M L M2 K n ≤
      5 / 4 * x ^ 2 * (M2 * A0 + 2 * L * A1 + M * A2) + L * (1 / K) * A0 := by
  unfold synthErrTwo
  rw [hn, show 5 / 4 * h ^ 2 * (M2 * A0 + 2 * L * (K * A1) + M * (K * (K * A2))) =
    5 / 4 * (M2 * A0 * h ^ 2 + 2 * L * A1 * (h * K) * h + M * A2 * (h * K) ^ 2) by ring, hK]
  have h2 : M2 * A0 * h ^ 2 ≤ M2 * A0 * x ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh0 hhx 2) (mul_nonneg hM2 hA0)
  have h3 : 2 * L * A1 * x * h ≤ 2 * L * A1 * x * x :=
    mul_le_mul_of_nonneg_left hhx (by have := hh0.trans hhx; positivity)
  nlinarith

theorem synthErrTwo_nonneg {A0 A1 A2 M L M2 K : ℝ} {n : ℕ} (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) (hM : 0 ≤ M) (hL : 0 ≤ L) (hM2 : 0 ≤ M2) (hK : 0 ≤ K) :
    0 ≤ synthErrTwo A0 A1 A2 M L M2 K n := by
  unfold synthErrTwo; positivity

theorem levyLipConstant_nonneg : 0 ≤ levyLipConstant := by
  have h2 : 0 < 1 - Real.exp (-2) := by
    have := Real.exp_lt_one_iff.mpr (show (-2 : ℝ) < 0 by norm_num); linarith
  unfold levyLipConstant
  have := div_pos (mul_pos (by norm_num : (0 : ℝ) < 8) (Real.exp_pos (-(1 / 2)))) h2
  linarith [Real.exp_pos (1 / 2)]

/-- `synthLevy` is monotone: `0 ≤ e ≤ E`, `0 ≤ LD/k ≤ G`, `k ≥ 1` give
`synthLevy R' e LD k ≤ e^{1/2} 2R' G E + (2 log k + C)(2R') E²`. -/
theorem synthLevy_le {R' e E LD G k : ℝ} (hR' : 0 ≤ R') (he0 : 0 ≤ e) (heE : e ≤ E)
    (hLD0 : 0 ≤ LD * (1 / k)) (hLDG : LD * (1 / k) ≤ G) (hk : 1 ≤ k) :
    0 ≤ synthLevy R' e LD k ∧ synthLevy R' e LD k ≤
      Real.exp (1 / 2) * (2 * R') * (G * E) +
        (2 * Real.log k + levyLipConstant) * (2 * R') * E ^ 2 := by
  have hl : 0 ≤ 2 * Real.log k + levyLipConstant := by
    have := Real.log_nonneg hk; have := levyLipConstant_nonneg; linarith
  have e1 : synthLevy R' e LD k = Real.exp (1 / 2) * (2 * R') * ((LD * (1 / k)) * e) +
      (2 * Real.log k + levyLipConstant) * (2 * R') * e ^ 2 := by unfold synthLevy; ring
  have t1 : (LD * (1 / k)) * e ≤ G * E := mul_le_mul hLDG heE he0 (hLD0.trans hLDG)
  have t2 : e ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ he0 heE 2
  have c1 : 0 ≤ Real.exp (1 / 2) * (2 * R') := by positivity
  have c2 : 0 ≤ (2 * Real.log k + levyLipConstant) * (2 * R') := mul_nonneg hl (by linarith)
  rw [e1]
  exact ⟨add_nonneg (mul_nonneg c1 (mul_nonneg hLD0 he0)) (mul_nonneg c2 (sq_nonneg _)),
    add_le_add (mul_le_mul_of_nonneg_left t1 c1) (mul_le_mul_of_nonneg_left t2 c2)⟩

/-- **The second-order synthesis errors vanish** under second-order overlap growth: along the
levels `n₀ B`, with `k = κ_{n₀B}`, the supremum error and the Lévy bound tend to `0`. -/
theorem tendsto_synth_two {κ : ℕ → ℝ} (hκ : OverlapGrowthTwo κ) {B : ℕ} (hB : 1 ≤ B)
    {A0 A1 A2 M L M2 R' : ℝ} (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (hM2 : 0 ≤ M2) (hR' : 0 ≤ R') :
    Tendsto (fun n : ℕ => synthErrTwo A0 A1 A2 M L M2 (κ (n * B)) n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => synthLevy R' (synthErrTwo A0 A1 A2 M L M2 (κ (n * B)) n)
        (synthLipTwo A1 A2 M L (κ (n * B)) n) (κ (n * B))) atTop (𝓝 0) := by
  obtain ⟨hk, hkl⟩ := hκ
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  set K : ℕ → ℝ := fun n => κ (n * B)
  set r : ℕ → ℝ := fun n => κ (n * B) / ((n * B : ℕ) : ℝ)
  have hK : Tendsto K atTop atTop := hk.comp hNB
  have hrl : Tendsto (fun n => r n ^ 4 * Real.log (K n)) atTop (𝓝 0) := hkl.comp hNB
  have hlogK : Tendsto (fun n => Real.log (K n)) atTop atTop := Real.tendsto_log_atTop.comp hK
  have hinv : Tendsto (fun n => 1 / K n) atTop (𝓝 0) := by
    simp only [one_div]
    exact hK.inv_tendsto_atTop
  have hlinv : Tendsto (fun n => (1 / K n) ^ 2 * Real.log (K n)) atTop (𝓝 0) := by
    refine ((tendsto_log_mul_rpow_neg two_pos).comp hK).congr' ?_
    filter_upwards [hK.eventually_gt_atTop 0] with n hn
    simp only [Function.comp]
    rw [Real.rpow_neg hn.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ K n ∧ 1 ≤ n := (hK.eventually_ge_atTop 1).and
    (eventually_ge_atTop 1)
  have hr0 : ∀ᶠ n : ℕ in atTop, 0 ≤ r n := by
    filter_upwards [hev] with n ⟨h1, _⟩
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  -- `r → 0`, from `r⁴ log K → 0` and `log K → ∞`
  have hr4 : Tendsto (fun n => r n ^ 4) atTop (𝓝 0) := by
    refine (hrl.div_atTop hlogK).congr' ?_
    filter_upwards [hlogK.eventually_gt_atTop 0] with n hn
    field_simp
  have hr2 : Tendsto (fun n => r n ^ 2) atTop (𝓝 0) := by
    have := hr4.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr' (Eventually.of_forall fun n => ?_)
    rw [show r n ^ 4 = (r n ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg _)]
  have hr : Tendsto r atTop (𝓝 0) := by
    have := hr2.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr' ?_
    filter_upwards [hr0] with n hn
    exact Real.sqrt_sq hn
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  -- the dominating sequences
  set C : ℝ := 5 / 4 * (B : ℝ) ^ 2 * (M2 * A0 + 2 * L * A1 + M * A2)
  set E : ℕ → ℝ := fun n => C * r n ^ 2 + L * A0 * (1 / K n)
  set G : ℕ → ℝ := fun n => M * A1 + (L * A1 + M * A2) * (B * r n) + L * (1 / K n)
  have hE : Tendsto E atTop (𝓝 0) := by
    have := (hr2.const_mul C).add (hinv.const_mul (L * A0))
    simpa [E] using this
  have hG : Tendsto G atTop (𝓝 (M * A1 + (L * A1 + M * A2) * (B * 0) + L * 0)) :=
    (tendsto_const_nhds.add ((hr.const_mul (B : ℝ)).const_mul (L * A1 + M * A2))).add
      (hinv.const_mul L)
  have hLE : Tendsto (fun n => Real.log (K n) * E n ^ 2) atTop (𝓝 0) := by
    have hup := (hrl.const_mul (2 * C ^ 2)).add (hlinv.const_mul (2 * (L * A0) ^ 2))
    simp only [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with n ⟨h1, _⟩
      exact mul_nonneg (Real.log_nonneg h1) (sq_nonneg _)
    · filter_upwards [hev] with n ⟨h1, _⟩
      have hl := Real.log_nonneg h1
      have : E n ^ 2 ≤ 2 * C ^ 2 * r n ^ 4 + 2 * (L * A0) ^ 2 * (1 / K n) ^ 2 := by
        simp only [E]
        nlinarith [sq_nonneg (C * r n ^ 2 - L * A0 * (1 / K n))]
      nlinarith
  set V : ℕ → ℝ := fun n => Real.exp (1 / 2) * (2 * R') * (G n * E n) +
    (2 * (Real.log (K n) * E n ^ 2) + levyLipConstant * E n ^ 2) * (2 * R')
  have hV : Tendsto V atTop (𝓝 0) := by
    have h1 := (hG.mul hE).const_mul (Real.exp (1 / 2) * (2 * R'))
    have h2 := ((hLE.const_mul 2).add ((hE.pow 2).const_mul levyLipConstant)).mul_const (2 * R')
    have := h1.add h2
    simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    exact this
  -- the pointwise bounds
  have hpt : ∀ᶠ n : ℕ in atTop,
      0 ≤ synthErrTwo A0 A1 A2 M L M2 (K n) n ∧ synthErrTwo A0 A1 A2 M L M2 (K n) n ≤ E n ∧
      0 ≤ synthLevy R' (synthErrTwo A0 A1 A2 M L M2 (K n) n) (synthLipTwo A1 A2 M L (K n) n) (K n) ∧
      synthLevy R' (synthErrTwo A0 A1 A2 M L M2 (K n) n) (synthLipTwo A1 A2 M L (K n) n) (K n) ≤
        V n := by
    filter_upwards [hev, hr0] with n ⟨h1, hn⟩ hrn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hK0 : 0 < K n := by linarith
    set h : ℝ := 1 / (n : ℝ)
    have hh0 : 0 ≤ h := by positivity
    have hhK : h * K n = B * r n := by
      simp only [h, r, K]; push_cast; field_simp
    have hhx : h ≤ B * r n := by
      rw [← hhK]; exact le_mul_of_one_le_right hh0 h1
    have he := synthErrTwo_le (A2 := A2) (M := M) hA0 hA1 hL hM2 hh0 hhx hhK (n := n) rfl
    have he0 := synthErrTwo_nonneg (n := n) hA0 hA1 hA2 hM hL hM2 hK0.le
    have heE : synthErrTwo A0 A1 A2 M L M2 (K n) n ≤ E n := by
      refine he.trans (le_of_eq ?_)
      simp only [E, C]; ring
    have hLDe : synthLipTwo A1 A2 M L (K n) n * (1 / K n) =
        M * A1 + L * A1 * h + M * A2 * (h * K n) + L * (1 / K n) := by
      unfold synthLipTwo; simp only [h]; field_simp; ring
    have hLD0 : 0 ≤ synthLipTwo A1 A2 M L (K n) n * (1 / K n) := by
      rw [hLDe]; positivity
    have hLDG : synthLipTwo A1 A2 M L (K n) n * (1 / K n) ≤ G n := by
      rw [hLDe, hhK]
      have : L * A1 * h ≤ L * A1 * (B * r n) := mul_le_mul_of_nonneg_left hhx (by positivity)
      simp only [G]; nlinarith
    obtain ⟨hl0, hl1⟩ := synthLevy_le hR' he0 heE hLD0 hLDG h1
    refine ⟨he0, heE, hl0, hl1.trans (le_of_eq ?_)⟩
    simp only [V]; ring
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
      (hpt.mono fun n h => h.1) (hpt.mono fun n h => h.2.1),
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hV
      (hpt.mono fun n h => h.2.2.1) (hpt.mono fun n h => h.2.2.2)⟩

/-- Widths `(log N)^α/N`, `α > 1/4` — overlap ratio `(log N)^α` — have second-order overlap
growth. -/
theorem overlapGrowthTwo_log {α : ℝ} (hα : 1 / 4 < α) :
    OverlapGrowthTwo fun N : ℕ => (N : ℝ) / Real.log N ^ α := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hα0 : 0 < α := by linarith
  have hκ : Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ α) atTop atTop := by
    have ho := (isLittleO_log_rpow_rpow_atTop α one_pos).tendsto_div_nhds_zero
    have hpos : ∀ᶠ y : ℝ in atTop, 0 < Real.log y ^ α / y ^ (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop 1] with y hy
      exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hy) α) (by positivity)
    have hinv := (tendsto_nhdsWithin_iff.mpr ⟨ho, hpos⟩).inv_tendsto_nhdsGT_zero
    refine (hinv.comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp, Real.rpow_one, Pi.inv_apply, inv_div]
  refine ⟨hκ, ?_⟩
  have hup : Tendsto (fun N : ℕ => Real.log N ^ (-(4 * α - 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hκ.eventually_ge_atTop 1] with N h1
    exact mul_nonneg (by positivity) (Real.log_nonneg h1)
  · filter_upwards [hκ.eventually_ge_atTop 1, hlog.eventually_ge_atTop 1,
      eventually_ge_atTop 1] with N h1 hl hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hl0 : 0 < Real.log N := by linarith
    have hpow : 1 ≤ Real.log N ^ α := Real.one_le_rpow hl hα0.le
    have hκN : (N : ℝ) / Real.log N ^ α ≤ N := div_le_self hN0.le hpow
    have hlk : Real.log ((N : ℝ) / Real.log N ^ α) ≤ Real.log N :=
      Real.log_le_log (by linarith) hκN
    have hsq : ((N : ℝ) / Real.log N ^ α / N) ^ 4 = Real.log N ^ (-(4 * α)) := by
      rw [div_div_cancel_left' hN0.ne', Real.rpow_neg hl0.le, inv_pow,
        ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
      push_cast
      rw [mul_comm α 4]
    rw [hsq, show -(4 * α - 1) = -(4 * α) + 1 by ring, Real.rpow_add hl0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hlk (Real.rpow_nonneg hl0.le _)

end Asymptotics

/-! ### The overlap law at the fourth root -/

section FourthRoot

open ArithmeticElectrostatics

variable {φ : ℝ → ℝ}

/-- **The overlap law at the fourth root**: for every `C²` profile `φ` supported in `[−1, 1]` with
`∫ φ = 1` and every dilation sequence `κ` whose overlap ratio `N/κ_N` beats `(log κ_N)^{1/4}`, RH
holds iff for all large `N` Weil's form is nonnegative on every atomic test
`Σ_{n ≤ N} x_n φ_κ(· − log n)` of width `1/κ_N`. -/
theorem riemannHypothesis_iff_atomicFamilies_nonneg_of_growthTwo {κ : ℕ → ℝ}
    (hκ : OverlapGrowthTwo κ) (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate (κ N) φ)) := by
  constructor
  · intro hRH
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ hφ1 hk N x
    exact RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hc
  · intro H
    by_contra hRH
    rw [RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive] at hRH
    push Not at hRH
    obtain ⟨g, hg, hgc, hneg⟩ := hRH
    change weilQuad g < 0 at hneg
    -- a radius and bounds on `g, g′, g″`
    obtain ⟨R0, hR0⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    set R := max R0 0
    have hR : 0 ≤ R := le_max_right _ _
    have hgR : SupportedIn R g := fun u hu => by
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hR0 hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_max_left R0 0]
    obtain ⟨-, -, hg1c, hg2c⟩ := profile_derivs hg
    obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
    obtain ⟨L, hL⟩ := hgc.deriv.exists_bound_of_continuous hg1c
    obtain ⟨M2, hM2⟩ := hgc.deriv.deriv.exists_bound_of_continuous hg2c
    have hM' : ∀ t, |g t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
    have hL' : ∀ t, |deriv g t| ≤ L := fun t => by simpa [Real.norm_eq_abs] using hL t
    have hM2' : ∀ t, |deriv (deriv g) t| ≤ M2 := fun t => by simpa [Real.norm_eq_abs] using hM2 t
    -- the synthesis errors vanish
    set B := blockSize R
    have hB : 1 ≤ B := by
      have h := Nat.le_ceil (1 + Real.exp (2 * R))
      have : (1 : ℝ) ≤ B := by
        have := Real.exp_pos (2 * R)
        simp only [B, blockSize] at h ⊢
        linarith
      exact_mod_cast this
    obtain ⟨he, hV⟩ := tendsto_synth_two hκ hB (integral_nonneg fun s => abs_nonneg (φ s))
      (integral_nonneg fun s => abs_nonneg (deriv φ s))
      (integral_nonneg fun s => abs_nonneg (deriv (deriv φ) s)) ((abs_nonneg _).trans (hM' 0))
      ((abs_nonneg _).trans (hL' 0)) ((abs_nonneg _).trans (hM2' 0)) (by linarith : (0 : ℝ) ≤ R + 3)
    have hErr := tendsto_weilErr g (R + 3) he hV
    have h1 := hErr.eventually (gt_mem_nhds (show (0 : ℝ) < -weilQuad g by linarith))
    have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
    have h2 := hNB.eventually H
    have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
    obtain ⟨n, hn1, hn2, hk, hn3⟩ := (h1.and (h2.and (h3.and (eventually_ge_atTop 1)))).exists
    obtain ⟨x, hx⟩ :=
      exists_atomicTest_weilQuad_le_two hφ hφ1 hφint hg hgc hR hgR hM' hL' hM2' hn3 hk
    have := hn2 x
    linarith

/-- **The logarithmic overlap law at the fourth root**: for every `α > 1/4`, RH holds iff for all
large `N` Weil's form is nonnegative on the atomic families of width `(log N)^α/N`, overlap ratio
`(log N)^α`. -/
theorem riemannHypothesis_iff_atomicFamilies_nonneg_log_quarter {α : ℝ} (hα : 1 / 4 < α)
    (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / Real.log N ^ α) φ)) :=
  riemannHypothesis_iff_atomicFamilies_nonneg_of_growthTwo (overlapGrowthTwo_log hα) hφ hφ1 hφint

end FourthRoot

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
