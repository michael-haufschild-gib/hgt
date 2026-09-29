import GaloisForLFunctions.RHTower.ThetaEndpointHarmonicCompleteness
import GaloisForLFunctions.RHTower.ThetaTailCapacitySharpness
import GaloisForLFunctions.RHTower.ThetaSourceTailRatioCalculus

/-!
# Unconditional infinite defect of the real-zero jets in `L^p_even(μ)`, `1 < p < ∞`

For `μ = k dx` the derivative ratios `f_j = k^{(j)}/k` satisfy `f_j(x) ~ (−2π)^j e^{2jx}` as
`x → ∞` (first-atom asymptotics), hence `|f_j| ≤ A e^{2j|x|}` and `f_j ∈ L^q(μ)` for every finite
`q`.  The transform of `k^{(4m)}` is `z^{4m} F`, so `∫ f_{4m} φ_{γ,j} dμ = (z^{4m}F)^{(j)}(γ)`: the
witnesses `f_{4m}`, `m ≥ 1`, annihilate `1` and every real-zero jet, and pairing with `cos(t·)`
gives `t^{4m} F(t)`, which makes them linearly independent.  By Hölder duality they are bounded
functionals on `L^p(μ)` for `1 < p < ∞`, and the closure of `span({1} ∪ V)` has infinite
codimension in `L^p_even(μ)` whatever the location of the zeros of `F`.
-/
open MeasureTheory Set Filter Topology Complex Polynomial
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Sharp growth of the derivative ratios `k^{(j)}/k` -/

/-- The first-atom ratio `P_j(e^x)/P_0(e^x)` is asymptotic to `(−2π)^j e^{2jx}`. -/
theorem tendsto_thetaAtomRatio_div_exp (j : ℕ) :
    Tendsto (fun x => thetaAtomRatio j x / Real.exp (2 * j * x)) atTop
      (𝓝 ((-(2 * Real.pi)) ^ j)) := by
  set Q := thetaCuspLogDerivativePolynomial j
  set P : ℝ[X] := X ^ (2 * j) * thetaCuspSeedPolynomial
  have hs := thetaCuspLogDerivativePolynomial_degree_leading 0
  have hQ := thetaCuspLogDerivativePolynomial_degree_leading j
  have hseed : thetaCuspSeedPolynomial ≠ 0 := by
    intro h
    have := hs.2
    rw [show thetaCuspLogDerivativePolynomial 0 = thetaCuspSeedPolynomial from rfl, h,
      leadingCoeff_zero] at this
    have hπ := Real.pi_pos
    simp only [pow_zero, mul_one] at this
    nlinarith
  have hPdeg : P.natDegree = 4 + 2 * j := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hseed, natDegree_X_pow,
      show thetaCuspSeedPolynomial = thetaCuspLogDerivativePolynomial 0 from rfl,
      natDegree_thetaCuspLogDerivativePolynomial]
    ring
  have hPlc : P.leadingCoeff = 4 * Real.pi ^ 2 := by
    rw [leadingCoeff_mul, leadingCoeff_X_pow, one_mul,
      show thetaCuspSeedPolynomial = thetaCuspLogDerivativePolynomial 0 from rfl, hs.2, pow_zero,
      mul_one]
  have hPpos : 0 < P.degree := by
    rw [degree_eq_natDegree (by rw [← leadingCoeff_ne_zero, hPlc]; positivity), hPdeg]
    exact_mod_cast (by omega : 0 < 4 + 2 * j)
  have h := (tendsto_eval_div_eval_of_natDegree_le P Q hPpos
    (by rw [hPdeg, natDegree_thetaCuspLogDerivativePolynomial])).comp Real.tendsto_exp_atTop
  have hval : Q.coeff P.natDegree / P.leadingCoeff = (-(2 * Real.pi)) ^ j := by
    rw [hPdeg, ← natDegree_thetaCuspLogDerivativePolynomial, coeff_natDegree, hQ.2, hPlc]
    have : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hval] at h
  refine h.congr fun x => ?_
  simp only [Function.comp, P, eval_mul, eval_pow, eval_X, thetaAtomRatio, Q, div_div]
  rw [← Real.exp_nat_mul, mul_comm (eval _ _)]
  push_cast
  ring_nf

/-- **Sharp derivative growth.**  `k^{(j)}(x)/k(x) ~ (−2π)^j e^{2jx}` as `x → ∞`. -/
theorem tendsto_thetaSourceRatio_div_exp (j : ℕ) :
    Tendsto (fun x => thetaSourceRatio j x / Real.exp (2 * j * x)) atTop
      (𝓝 ((-(2 * Real.pi)) ^ j)) := by
  have hd : Tendsto (fun x => (thetaSourceRatio j x - thetaAtomRatio j x) *
      (Real.exp (2 * j * x))⁻¹) atTop (𝓝 0) := by
    refine (ThetaTailNegligible.tendsto (thetaSourceRatio_close j)).zero_mul_isBoundedUnder_le
      (isBoundedUnder_of_eventually_le (a := 1) ?_)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp, norm_inv, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact inv_le_one_of_one_le₀ (Real.one_le_exp (by positivity))
  have h := (tendsto_thetaAtomRatio_div_exp j).add hd
  rw [add_zero] at h
  refine h.congr fun x => ?_
  have := (Real.exp_pos (2 * j * x)).ne'
  field_simp
  ring

theorem continuous_thetaSourceRatio (j : ℕ) : Continuous (thetaSourceRatio j) :=
  (contDiff_thetaCuspFullSource.continuous_iteratedDeriv j (by exact_mod_cast le_top)).div
    contDiff_thetaCuspFullSource.continuous fun x => (thetaCuspFullSource_pos x).ne'

theorem abs_thetaSourceRatio_neg (j : ℕ) (x : ℝ) :
    |thetaSourceRatio j (-x)| = |thetaSourceRatio j x| := by
  simp only [thetaSourceRatio, abs_div, abs_iteratedDeriv_thetaCuspFullSource_neg,
    thetaCuspFullSource_neg]

/-- A global bound `|k^{(j)}/k| ≤ A e^{2j|x|}`. -/
theorem exists_abs_thetaSourceRatio_le (j : ℕ) :
    ∃ A : ℝ, ∀ x, |thetaSourceRatio j x| ≤ A * Real.exp (2 * j * |x|) := by
  set L := ‖(-(2 * Real.pi)) ^ j‖
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((tendsto_thetaSourceRatio_div_exp j).norm.eventually
    (gt_mem_nhds (lt_add_one L)))
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -|X|) (b := |X|)).exists_bound_of_continuousOn
    (continuous_thetaSourceRatio j).continuousOn
  have hpos : ∀ y, X ≤ y → |thetaSourceRatio j y| ≤ (L + 1) * Real.exp (2 * j * y) := by
    intro y hy
    have h := hX y hy
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le,
      div_lt_iff₀ (Real.exp_pos _)] at h
    exact h.le
  refine ⟨max B (L + 1), fun x => ?_⟩
  have hL : 0 ≤ L := norm_nonneg _
  have he : 1 ≤ Real.exp (2 * j * |x|) := Real.one_le_exp (by positivity)
  by_cases hx : |x| ≤ |X|
  · have h := hB x ⟨by linarith [neg_abs_le x], (le_abs_self x).trans hx⟩
    rw [Real.norm_eq_abs] at h
    calc |thetaSourceRatio j x| ≤ max B (L + 1) := h.trans (le_max_left _ _)
      _ ≤ max B (L + 1) * Real.exp (2 * j * |x|) :=
          le_mul_of_one_le_right ((by linarith : (0 : ℝ) ≤ L + 1).trans (le_max_right _ _)) he
  · replace hx := not_le.1 hx
    have hX' : X ≤ |x| := (le_abs_self X).trans hx.le
    have h1 : |thetaSourceRatio j x| = |thetaSourceRatio j (|x|)| := by
      rcases le_or_gt 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, abs_thetaSourceRatio_neg]
    rw [h1]
    exact (hpos _ hX').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-- Functions of exponential growth belong to every finite `L^p(μ)`. -/
theorem memLp_of_abs_le_exp {g : ℝ → ℝ} (hg : Continuous g) {A a : ℝ}
    (hb : ∀ x, |g x| ≤ A * Real.exp (a * |x|)) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp g p thetaSourceMeasure := by
  have hm : AEStronglyMeasurable g thetaSourceMeasure := hg.aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hm
  have hA : 0 ≤ A :=
    (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((abs_nonneg _).trans (hb 0))
  rw [← integrable_norm_rpow_iff hm hp0 hp]
  set r := p.toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  refine ((integrable_exp_mul_abs_thetaSourceMeasure (r * a)).const_mul (A ^ r)).mono'
    (hg.norm.rpow_const fun _ => Or.inr hr).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  calc |g x| ^ r ≤ (A * Real.exp (a * |x|)) ^ r := Real.rpow_le_rpow (abs_nonneg _) (hb x) hr
    _ = A ^ r * Real.exp (r * a * |x|) := by
        rw [Real.mul_rpow hA (Real.exp_pos _).le, ← Real.exp_mul]
        ring_nf

/-- **The derivative witnesses lie in every finite `L^q(μ)`.** -/
theorem memLp_thetaSourceRatio (j : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞) :
    MemLp (thetaSourceRatio j) q thetaSourceMeasure := by
  obtain ⟨A, hA⟩ := exists_abs_thetaSourceRatio_le j
  exact memLp_of_abs_le_exp (continuous_thetaSourceRatio j) hA hq

theorem thetaSourceRatio_four_mul_neg (m : ℕ) (x : ℝ) :
    thetaSourceRatio (4 * m) (-x) = thetaSourceRatio (4 * m) x := by
  have hpow : (-1 : ℝ) ^ (4 * m) = 1 := by rw [pow_mul]; norm_num
  simp only [thetaSourceRatio, iteratedDeriv_thetaCuspFullSource_neg, hpow, one_mul,
    thetaCuspFullSource_neg]

/-! ## Fourier pairings of the derivative witnesses -/

theorem sourceTransform_thetaDerivSourceC_four_mul (m : ℕ) (z : ℂ) :
    sourceTransform (thetaDerivSourceC (4 * m)) z = z ^ (4 * m) * XiC z := by
  rw [sourceTransform_thetaDerivSourceC, mul_pow, pow_mul I 4 m, Complex.I_pow_four, one_pow,
    one_mul]

/-- `∫ φ_{γ,j} k^{(4m)} = (z^{4m} F)^{(j)}(γ)`. -/
theorem integral_thetaCosJet_mul_iteratedDeriv_four_mul (m : ℕ) (γ : ℝ) (j : ℕ) :
    ((∫ x, thetaCosJet γ j x * iteratedDeriv (4 * m) thetaCuspFullSource x : ℝ) : ℂ) =
      iteratedDeriv j (fun z => z ^ (4 * m) * XiC z) γ := by
  have he := expMomentSource_thetaDerivSourceC (4 * m)
  have hpow : (-1 : ℝ) ^ (4 * m) = 1 := by rw [pow_mul]; norm_num
  rw [← iteratedDeriv_sourceTransform_ofReal_of_moment
    (v := iteratedDeriv (4 * m) thetaCuspFullSource)
    ⟨he.continuous.aestronglyMeasurable, he.moment⟩
    (fun x => by rw [iteratedDeriv_thetaCuspFullSource_neg, hpow, one_mul]) γ j]
  exact congrArg (fun H => iteratedDeriv j H (γ : ℂ))
    (funext (sourceTransform_thetaDerivSourceC_four_mul m))

/-- Integration against `k^{(n)}/k` for the theta measure is integration against `k^{(n)}`. -/
theorem integral_thetaSourceRatio_mul (n : ℕ) (g : ℝ → ℝ) :
    ∫ x, thetaSourceRatio n x * g x ∂thetaSourceMeasure =
      ∫ x, g x * iteratedDeriv n thetaCuspFullSource x := by
  rw [integral_thetaSourceMeasure]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have := (thetaCuspFullSource_pos x).ne'
  simp only [thetaSourceRatio]
  field_simp

/-- **The witnesses annihilate every real-zero jet.** -/
theorem integral_thetaSourceRatio_mul_thetaCosJet_eq_zero (m : ℕ) {γ : ℝ} {j : ℕ}
    (hj : (j : ℕ∞) < analyticOrderAt XiC γ) :
    ∫ x, thetaSourceRatio (4 * m) x * thetaCosJet γ j x ∂thetaSourceMeasure = 0 := by
  rw [integral_thetaSourceRatio_mul]
  have hA : AnalyticAt ℂ (fun z : ℂ => z ^ (4 * m) * XiC z) γ :=
    ((differentiable_pow _).mul XiC_differentiable).analyticAt _
  have hle : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z : ℂ => z ^ (4 * m) * XiC z) γ := by
    have h := analyticOrderAt_mul (f := fun z : ℂ => z ^ (4 * m)) (g := XiC)
      ((differentiable_pow _).analyticAt (γ : ℂ)) (XiC_differentiable.analyticAt _)
    refine (Order.add_one_le_of_lt hj).trans ?_
    rw [show (fun z : ℂ => z ^ (4 * m) * XiC z) = (fun z : ℂ => z ^ (4 * m)) * XiC from rfl, h]
    exact le_add_self
  have h0 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).1 hle j (by omega)
  have h := integral_thetaCosJet_mul_iteratedDeriv_four_mul m γ j
  rw [h0] at h
  exact_mod_cast h

theorem thetaCosJet_zero_zero (x : ℝ) : thetaCosJet 0 0 x = 1 := by
  simp [thetaCosJet]

/-- **The witnesses have zero mass** for `m ≥ 1`. -/
theorem integral_thetaSourceRatio_eq_zero {m : ℕ} (hm : 0 < m) :
    ∫ x, thetaSourceRatio (4 * m) x ∂thetaSourceMeasure = 0 := by
  have h := integral_thetaCosJet_mul_iteratedDeriv_four_mul m 0 0
  simp only [iteratedDeriv_zero, Complex.ofReal_zero, zero_pow (by omega : 4 * m ≠ 0),
    zero_mul] at h
  have h' : ∫ x, thetaCosJet 0 0 x * iteratedDeriv (4 * m) thetaCuspFullSource x = 0 := by
    exact_mod_cast h
  rw [← integral_thetaSourceRatio_mul] at h'
  simpa [thetaCosJet_zero_zero] using h'

/-- The pairing of `k^{(4m)}/k` with `cos(t·)` is `t^{4m} F(t)`. -/
theorem integral_thetaSourceRatio_mul_cos (m : ℕ) (t : ℝ) :
    ((∫ x, thetaSourceRatio (4 * m) x * thetaCosJet t 0 x ∂thetaSourceMeasure : ℝ) : ℂ) =
      (t : ℂ) ^ (4 * m) * XiC t := by
  rw [integral_thetaSourceRatio_mul, integral_thetaCosJet_mul_iteratedDeriv_four_mul,
    iteratedDeriv_zero]

theorem eq_zero_of_sum_mul_pow_eq_zero_on_Icc {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (e : ι → ℕ) (he : Set.InjOn e s) (h : ∀ t ∈ Icc (0 : ℝ) 1, ∑ i ∈ s, g i * t ^ e i = 0) :
    ∀ i ∈ s, g i = 0 := by
  set P : ℝ[X] := ∑ i ∈ s, C (g i) * X ^ e i
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ((Icc_infinite zero_lt_one).mono fun t ht => ?_)
    simp only [mem_setOf_eq, IsRoot, P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact h t ht
  intro i hi
  have hc := congrArg (fun q : ℝ[X] => q.coeff (e i)) hP
  simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rwa [Finset.sum_eq_single (f := fun k => if e i = e k then g k else 0) i
    (fun k hk hki => if_neg fun h => hki (he hk hi h.symm)) (fun h => absurd hi h),
    if_pos rfl] at hc

/-- **Fourier independence.**  If `Σ g_m ∫ (k^{(4m)}/k) cos(t·) dμ = 0` for every real `t`, then every
`g_m` vanishes. -/
theorem eq_zero_of_forall_sum_integral_thetaSourceRatio_mul_cos {ι : Type*} (s : Finset ι)
    (g : ι → ℝ) (e : ι → ℕ) (he : Set.InjOn e s)
    (h : ∀ t : ℝ, ∑ i ∈ s, g i * ∫ x, thetaSourceRatio (4 * e i) x * thetaCosJet t 0 x
      ∂thetaSourceMeasure = 0) : ∀ i ∈ s, g i = 0 := by
  refine eq_zero_of_sum_mul_pow_eq_zero_on_Icc s g (fun i => 4 * e i)
    (fun i hi k hk hik => he hi hk (by simpa using hik)) fun t ht => ?_
  have hF : XiC t ≠ 0 := XiC_ne_zero_of_norm_le_one (by
    rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2)
  have hc := congrArg (fun r : ℝ => (r : ℂ)) (h t)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, integral_thetaSourceRatio_mul_cos,
    Complex.ofReal_zero, ← mul_assoc, ← Finset.sum_mul] at hc
  have := (mul_eq_zero.1 hc).resolve_right hF
  exact_mod_cast this

theorem integrable_thetaSourceRatio_mul_cos (n : ℕ) (t : ℝ) :
    Integrable (fun x => thetaSourceRatio n x * thetaCosJet t 0 x) thetaSourceMeasure := by
  refine (memLp_one_iff_integrable.1 (memLp_thetaSourceRatio n ENNReal.one_ne_top)).norm.mono'
    ((continuous_thetaSourceRatio n).mul (continuous_thetaCosJet t 0)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  have := abs_thetaCosJet_le t 0 x
  rw [pow_zero, ← Real.norm_eq_abs] at this
  exact mul_le_of_le_one_right (norm_nonneg _) this

/-- **The witnesses are linearly independent**, together with the constant `k/k = 1`. -/
theorem linearIndependent_thetaSourceRatio :
    LinearIndependent ℝ fun m : ℕ => thetaSourceRatio (4 * m) := by
  rw [linearIndependent_iff']
  intro s g hg
  refine eq_zero_of_forall_sum_integral_thetaSourceRatio_mul_cos s g id (Set.injOn_id _) fun t => ?_
  have h := congrArg (fun F : ℝ → ℝ => ∫ x, F x * thetaCosJet t 0 x ∂thetaSourceMeasure) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Pi.zero_apply,
    zero_mul, integral_zero] at h
  rw [integral_finsetSum _ fun i _ => (integrable_thetaSourceRatio_mul_cos (4 * i) t).const_mul
    (g i) |>.congr (Eventually.of_forall fun x => by simp only [mul_assoc])] at h
  simpa only [id, mul_assoc, integral_const_mul] using h

/-! ## The reflexive scale: infinite codimension in `L^p_even(μ)`, `1 < p < ∞` -/

section Lp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- `L^p(μ)` for the theta measure. -/
abbrev ThetaLp := Lp ℝ p thetaSourceMeasure

/-- The reflection `f ↦ f(-·)` on `L^p(μ)`. -/
def thetaReflectLp : ThetaLp p →L[ℝ] ThetaLp p :=
  (Lp.compMeasurePreservingₗᵢ ℝ Neg.neg
    (Measure.measurePreserving_neg thetaSourceMeasure)).toContinuousLinearMap

/-- The even subspace `L^p_even(μ)`. -/
def thetaEvenLp : Submodule ℝ (ThetaLp p) :=
  LinearMap.ker ((thetaReflectLp p - ContinuousLinearMap.id ℝ (ThetaLp p) :
    ThetaLp p →L[ℝ] ThetaLp p) : ThetaLp p →ₗ[ℝ] ThetaLp p)

theorem toLp_mem_thetaEvenLp {g : ℝ → ℝ} (hg : MemLp g p thetaSourceMeasure)
    (heven : ∀ x, g (-x) = g x) : hg.toLp g ∈ thetaEvenLp p := by
  simp only [thetaEvenLp, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  refine Lp.ext ?_
  have h0 : (thetaReflectLp p (hg.toLp g) : ℝ → ℝ) =ᵐ[thetaSourceMeasure]
      fun x => (hg.toLp g) (-x) := Lp.coeFn_compMeasurePreserving _ _
  have h1 := MemLp.coeFn_toLp hg
  have h2 : (fun x => (hg.toLp g : ℝ → ℝ) (-x)) =ᵐ[thetaSourceMeasure] fun x => g (-x) :=
    (Measure.measurePreserving_neg thetaSourceMeasure).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h0, h1, h2] with x hx0 hx1 hx2
  rw [hx0, hx2, heven, hx1]

/-- The jet `φ_{γ,j}` in `L^p(μ)`, `p < ∞`. -/
def thetaJetLp (hp : p ≠ ∞) (γ : ℝ) (j : ℕ) : ThetaLp p := (memLp_thetaCosJet γ j hp).toLp _

/-- The constant `1` in `L^p(μ)`. -/
def thetaOneLp : ThetaLp p := (memLp_const (1 : ℝ)).toLp fun _ => (1 : ℝ)

/-- The real-zero jets in `L^p(μ)`. -/
def thetaJetSetLp (hp : p ≠ ∞) : Set (ThetaLp p) :=
  {f | ∃ γ : ℝ, 0 < γ ∧ XiC γ = 0 ∧ ∃ j : ℕ, (j : ℕ∞) < analyticOrderAt XiC γ ∧
    f = thetaJetLp p hp γ j}

/-- `span({1} ∪ V)` in `L^p(μ)`. -/
def thetaJetOneSpanLp (hp : p ≠ ∞) : Submodule ℝ (ThetaLp p) :=
  Submodule.span ℝ (insert (thetaOneLp p) (thetaJetSetLp p hp))

/-- **Hölder pairing.**  For `1 < p < ∞`, integration against `k^{(n)}/k` is a bounded functional on
`L^p(μ)`. -/
theorem exists_thetaSourceRatioPairing (hp1 : 1 < p) (n : ℕ) :
    ∃ Λ : ThetaLp p →L[ℝ] ℝ, ∀ h : ThetaLp p,
      Λ h = ∫ x, thetaSourceRatio n x * h x ∂thetaSourceMeasure := by
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  haveI hpq : ENNReal.HolderConjugate q p := by
    rw [ENNReal.holderConjugate_iff, inv_inv]
    exact tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hp1.le)
  have hq : q ≠ ∞ := fun h => hp1.ne' ((ENNReal.HolderConjugate.eq_top_iff_eq_one q p).1 h)
  haveI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hm := memLp_thetaSourceRatio n hq
  refine ⟨(ContinuousLinearMap.mul ℝ ℝ).lpPairing thetaSourceMeasure q p (hm.toLp _),
    fun h => ?_⟩
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp] with x hx
  simp only [ContinuousLinearMap.mul_apply', hx]

omit [Fact (1 ≤ p)] in
theorem integral_mul_toLp_eq (n : ℕ) {g : ℝ → ℝ} (hg : MemLp g p thetaSourceMeasure) :
    ∫ x, thetaSourceRatio n x * (hg.toLp g) x ∂thetaSourceMeasure =
      ∫ x, thetaSourceRatio n x * g x ∂thetaSourceMeasure :=
  integral_congr_ae (hg.coeFn_toLp.mono fun x hx => by simp only [hx])

/-- **Sharp `L^p` failure.**  For every finite `p > 1`, the closure of `span({1} ∪ V)` has infinite
codimension in `L^p_even(μ)`, whatever the location of the zeros of `F`: the functionals
`h ↦ ∫ (k^{(4m)}/k) h dμ`, `m ≥ 1`, are bounded, vanish on `1` and on every real-zero jet, and are
linearly independent on `L^p_even(μ)`. -/
theorem not_finiteDimensional_thetaLpDefect (hp1 : 1 < p) (hp : p ≠ ∞) :
    ¬ FiniteDimensional ℝ (thetaEvenLp p ⧸
      (thetaJetOneSpanLp p hp).topologicalClosure.comap (thetaEvenLp p).subtype) := by
  intro hfd
  choose Λ hΛ using exists_thetaSourceRatioPairing p hp1
  set S := (thetaJetOneSpanLp p hp).topologicalClosure.comap (thetaEvenLp p).subtype
  have hker : ∀ m : ℕ, (thetaJetOneSpanLp p hp).topologicalClosure ≤
      LinearMap.ker (Λ (4 * (m + 1)) : ThetaLp p →ₗ[ℝ] ℝ) := by
    intro m
    refine Submodule.topologicalClosure_minimal _ ?_ (Λ _).isClosed_ker
    rw [thetaJetOneSpanLp, Submodule.span_le]
    rintro f (rfl | ⟨γ, -, -, j, hj, rfl⟩)
    · show Λ _ (thetaOneLp p) = 0
      rw [hΛ, thetaOneLp, integral_mul_toLp_eq]
      simpa using integral_thetaSourceRatio_eq_zero (Nat.succ_pos m)
    · show Λ _ (thetaJetLp p hp γ j) = 0
      rw [hΛ, thetaJetLp, integral_mul_toLp_eq]
      exact integral_thetaSourceRatio_mul_thetaCosJet_eq_zero _ hj
  let lam : ℕ → Module.Dual ℝ (thetaEvenLp p ⧸ S) := fun m =>
    S.liftQ ((Λ (4 * (m + 1)) : ThetaLp p →ₗ[ℝ] ℝ).comp (thetaEvenLp p).subtype)
      fun h hh => LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (hker m hh))
  set d := Module.finrank ℝ (thetaEvenLp p ⧸ S)
  have hli : LinearIndependent ℝ fun i : Fin (d + 1) => lam i := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key := eq_zero_of_forall_sum_integral_thetaSourceRatio_mul_cos Finset.univ g
      (fun i : Fin (d + 1) => (i : ℕ) + 1) (fun i _ k _ h => Fin.ext (by simpa using h))
      fun t => by
        have hcos : thetaJetLp p hp t 0 ∈ thetaEvenLp p :=
          toLp_mem_thetaEvenLp p _ (thetaCosJet_neg t 0)
        have h := congrArg (fun φ : Module.Dual ℝ (thetaEvenLp p ⧸ S) =>
          φ (S.mkQ ⟨thetaJetLp p hp t 0, hcos⟩)) hg
        simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
          LinearMap.zero_apply, lam, Submodule.mkQ_apply, Submodule.liftQ_apply,
          LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe, hΛ,
          thetaJetLp, integral_mul_toLp_eq] at h
        exact h
    exact fun i => key i (Finset.mem_univ i)
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Subspace.dual_finrank_eq] at this
  omega

end Lp

end

end RHTower
