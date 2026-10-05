import GaloisForLFunctions.HTGeometry.HalfLineLaplaceTomography
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Convolution is diagonal on the character response; origin-atom properness

For a finite measure `ν` on `[0, ∞)` convolution acts diagonally on the integer character
responses, `b_n(J ∗ ν) = L_ν(n) b_n(J)` `(CTL.19)`, by Fubini and `e^{-n(x+y)} = e^{-nx}e^{-ny}`.
Dominated convergence gives `∫ e^{-nx} dμ → μ({0})`, so `b_n(J) → J({0})` `(CTL.20)`, and the
multipliers `a_n = L_ν(n) ∈ (0, 1]` decrease to the origin atom `α = ν({0})` `(CTL.24)`.

On `c_0` (here `C₀(ℕ, ℝ)`, the response `b_{k+1}` in coordinate `k`) the diagonal `M_ν` satisfies:
`M_ν` is bounded below iff its range is closed iff `α > 0` `(CTL.22)`.  If `α > 0` then
`α ‖b‖ ≤ ‖M_ν b‖ ≤ ‖b‖` `(CTL.23)`.  If `α = 0`, `M_ν` is injective and compact (a norm limit of
the finite-rank truncations, `‖M_ν - M_ν^{(N)}‖ ≤ sup_{k ≥ N} a_{k+1}`), its range contains every
finitely supported sequence and is dense, but it is not closed and the inverse on the range is
unbounded (`‖M_ν e_k‖ = a_{k+1} → 0`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal ZeroAtInfty

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LaplaceTomography

/-! ### Convolution is diagonal `(CTL.19)` -/

/-- The integer Laplace transform `L_μ(n) = ∫ e^{-nx} dμ`. -/
def laplaceInt (μ : Measure ℝ≥0) (n : ℕ) : ℝ := ∫ x, Real.exp (-(n * (x : ℝ))) ∂μ

theorem laplaceInt_conv (μ ν : Measure ℝ≥0) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ) :
    laplaceInt (μ ∗ ν) n = laplaceInt μ n * laplaceInt ν n := by
  rw [laplaceInt, integral_conv (integrable_exp_neg_mul _ n), laplaceInt, laplaceInt,
    ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  simp only [NNReal.coe_add]
  rw [← Real.exp_add]
  ring_nf

/-- The convolution `J ∗ ν` of a signed current with a finite measure. -/
def convSigned (J : SignedMeasure ℝ≥0) (ν : Measure ℝ≥0) [IsFiniteMeasure ν] :
    SignedMeasure ℝ≥0 :=
  (J.toJordanDecomposition.posPart ∗ ν).toSignedMeasure -
    (J.toJordanDecomposition.negPart ∗ ν).toSignedMeasure

/-- **`(CTL.19)`**: `b_n(J ∗ ν) = L_ν(n) b_n(J)`. -/
theorem charResponse_convSigned (J : SignedMeasure ℝ≥0) (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (n : ℕ) : charResponse (convSigned J ν) n = laplaceInt ν n * charResponse J n := by
  have hb : ∀ (μ : Measure ℝ≥0) [IsFiniteMeasure μ],
      VectorMeasure.Integrable μ.toSignedMeasure fun x : ℝ≥0 => Real.exp (-(n * (x : ℝ))) :=
    fun μ _ => by
      show Integrable _ (VectorMeasure.variation _)
      rw [Measure.variation_toSignedMeasure]
      exact integrable_exp_neg_mul _ n
  rw [charResponse, convSigned, VectorMeasure.integral_sub_vectorMeasure (hb _) (hb _),
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure, charResponse_eq]
  have h1 := laplaceInt_conv J.toJordanDecomposition.posPart ν n
  have h2 := laplaceInt_conv J.toJordanDecomposition.negPart ν n
  simp only [laplaceInt] at h1 h2
  rw [h1, h2, laplaceInt]
  ring

/-! ### The origin atom `(CTL.20)`, `(CTL.24)` -/

/-- `L_μ(n) → μ({0})`. -/
theorem tendsto_laplaceInt (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    Tendsto (laplaceInt μ) atTop (𝓝 (μ.real {0})) := by
  rw [← integral_indicator_one (measurableSet_singleton 0)]
  refine tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun n => (integrable_exp_neg_mul μ n).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (Nat.cast_nonneg n) x.2
  · by_cases hx : x = 0
    · subst hx
      simp
    · have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.2 (fun h => hx (NNReal.coe_injective h.symm))
      rw [indicator_of_notMem (by simpa using hx)]
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hxpos))

theorem charResponse_tendsto (J : SignedMeasure ℝ≥0) :
    Tendsto (charResponse J) atTop (𝓝 (J {0})) := by
  have hJ : J {0} = J.toJordanDecomposition.posPart.real {0} -
      J.toJordanDecomposition.negPart.real {0} := by
    conv_lhs => rw [← J.toSignedMeasure_toJordanDecomposition]
    rw [JordanDecomposition.toSignedMeasure, sub_apply,
      Measure.toSignedMeasure_apply_measurable (measurableSet_singleton 0),
      Measure.toSignedMeasure_apply_measurable (measurableSet_singleton 0)]
  rw [hJ]
  have h := (tendsto_laplaceInt J.toJordanDecomposition.posPart).sub
    (tendsto_laplaceInt J.toJordanDecomposition.negPart)
  refine h.congr fun n => ?_
  rw [charResponse_eq]
  rfl

/-- **`(CTL.20)`**: without an origin atom the responses tend to zero. -/
theorem charResponse_tendsto_zero (J : SignedMeasure ℝ≥0) (hJ : J {0} = 0) :
    Tendsto (charResponse J) atTop (𝓝 0) := by
  simpa [hJ] using charResponse_tendsto J

/-! ### `c_0` -/

/-- A sequence tending to zero as an element of `c_0 = C₀(ℕ, ℝ)`. -/
def ofTendsto (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) : C₀(ℕ, ℝ) :=
  ⟨⟨f, continuous_of_discreteTopology⟩, by rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]⟩

@[simp] theorem ofTendsto_apply (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) (k : ℕ) :
    ofTendsto f hf k = f k := rfl

theorem tendsto_c0 (b : C₀(ℕ, ℝ)) : Tendsto (fun k => b k) atTop (𝓝 0) := by
  have := b.zero_at_infty'
  rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at this

theorem abs_apply_le_norm (b : C₀(ℕ, ℝ)) (k : ℕ) : |b k| ≤ ‖b‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ← Real.norm_eq_abs]
  exact b.toBCF.norm_coe_le_norm k

theorem norm_le_of_forall {b : C₀(ℕ, ℝ)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ k, |b k| ≤ C) : ‖b‖ ≤ C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).2 fun k => by rw [Real.norm_eq_abs]; exact h k

/-- The unit vector `e_k ∈ c_0`. -/
def unitC0 (k : ℕ) : C₀(ℕ, ℝ) :=
  ofTendsto (Pi.single k 1) (tendsto_const_nhds.congr' (by
    filter_upwards [eventually_gt_atTop k] with j hj
    simp [hj.ne']))

theorem norm_unitC0 (k : ℕ) : ‖unitC0 k‖ = 1 := by
  refine le_antisymm (norm_le_of_forall zero_le_one fun j => ?_) ?_
  · simp only [unitC0, ofTendsto_apply, Pi.single_apply]
    split_ifs <;> simp
  · have := abs_apply_le_norm (unitC0 k) k
    simpa [unitC0] using this

/-- The response of a current without origin atom, in `c_0` (coordinate `k` is `b_{k+1}`). -/
def responseC0 (J : SignedMeasure ℝ≥0) (hJ : J {0} = 0) : C₀(ℕ, ℝ) :=
  ofTendsto (fun k => charResponse J (k + 1))
    ((charResponse_tendsto_zero J hJ).comp (tendsto_add_atTop_nat 1))

/-! ### The convolution multiplier on `c_0` `(CTL.21)` -/

variable (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]

/-- The multipliers `a_{k+1} = L_ν(k+1)`. -/
def mult (k : ℕ) : ℝ := laplaceInt ν (k + 1)

theorem mult_pos (k : ℕ) : 0 < mult ν k := by
  rw [mult, laplaceInt, integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (integrable_exp_neg_mul ν _)]
  have : Function.support (fun x : ℝ≥0 => Real.exp (-(((k + 1 : ℕ) : ℝ) * (x : ℝ)))) = univ :=
    eq_univ_of_forall fun x => (Real.exp_pos _).ne'
  rw [this, measure_univ]
  exact one_pos

theorem mult_le_one (k : ℕ) : mult ν k ≤ 1 := by
  calc mult ν k ≤ ∫ _x, (1 : ℝ) ∂ν := integral_mono (integrable_exp_neg_mul ν _)
        (integrable_const 1) fun x => by
          show Real.exp (-(((k + 1 : ℕ) : ℝ) * (x : ℝ))) ≤ 1
          rw [Real.exp_le_one_iff, neg_nonpos]
          exact mul_nonneg (Nat.cast_nonneg _) x.2
    _ = 1 := by simp

/-- `a_{k+1} ≥ ν({0})`. -/
theorem atom_le_mult (k : ℕ) : ν.real {0} ≤ mult ν k := by
  rw [← integral_indicator_one (measurableSet_singleton 0), mult, laplaceInt]
  refine integral_mono ((integrable_const 1).indicator (measurableSet_singleton 0))
    (integrable_exp_neg_mul ν _) fun x => ?_
  by_cases hx : x = 0
  · subst hx; simp
  · rw [indicator_of_notMem (by simpa using hx)]
    exact (Real.exp_pos _).le

/-- **`(CTL.24)`**: `a_n → ν({0})`. -/
theorem tendsto_mult : Tendsto (mult ν) atTop (𝓝 (ν.real {0})) :=
  (tendsto_laplaceInt ν).comp (tendsto_add_atTop_nat 1)

/-- The diagonal operator `M_ν b = (a_{k+1} b_k)_k` on `c_0` `(CTL.21)`. -/
def diagMul : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun b => ofTendsto (fun k => mult ν k * b k) (by
        refine squeeze_zero_norm (fun k => ?_) (tendsto_norm_zero.comp (tendsto_c0 b))
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mult_pos ν k)]
        exact mul_le_of_le_one_left (abs_nonneg _) (mult_le_one ν k))
      map_add' := fun b c => ZeroAtInftyContinuousMap.ext fun k => by simp [mul_add]
      map_smul' := fun a b => ZeroAtInftyContinuousMap.ext fun k => by
        simp only [ofTendsto_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
    1 fun b => by
      rw [one_mul]
      refine norm_le_of_forall (norm_nonneg _) fun k => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ofTendsto_apply, abs_mul,
        abs_of_pos (mult_pos ν k)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (mult_le_one ν k)).trans (abs_apply_le_norm b k)

@[simp] theorem diagMul_apply (b : C₀(ℕ, ℝ)) (k : ℕ) : diagMul ν b k = mult ν k * b k := rfl

/-- **`(CTL.19)`, `(CTL.21)`**: `M_ν` sends the response of `J` to the response of `J ∗ ν`. -/
theorem diagMul_responseC0 (J : SignedMeasure ℝ≥0) (hJ : J {0} = 0) (k : ℕ) :
    diagMul ν (responseC0 J hJ) k = charResponse (convSigned J ν) (k + 1) := by
  rw [diagMul_apply, charResponse_convSigned]
  rfl

theorem norm_diagMul_le (b : C₀(ℕ, ℝ)) : ‖diagMul ν b‖ ≤ ‖b‖ :=
  norm_le_of_forall (norm_nonneg _) fun k => by
    rw [diagMul_apply, abs_mul, abs_of_pos (mult_pos ν k)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (mult_le_one ν k)).trans (abs_apply_le_norm b k)

theorem diagMul_injective : Function.Injective (diagMul ν) := fun b c h =>
  ZeroAtInftyContinuousMap.ext fun k => by
    have := congrArg (fun d : C₀(ℕ, ℝ) => d k) h
    simp only [diagMul_apply] at this
    exact mul_left_cancel₀ (mult_pos ν k).ne' this

theorem norm_diagMul_unitC0 (k : ℕ) : ‖diagMul ν (unitC0 k)‖ = mult ν k := by
  refine le_antisymm (norm_le_of_forall (mult_pos ν k).le fun j => ?_) ?_
  · simp only [diagMul_apply, unitC0, ofTendsto_apply, Pi.single_apply]
    split_ifs with h
    · subst h; simp [abs_of_pos (mult_pos ν j)]
    · simp [(mult_pos ν k).le]
  · have := abs_apply_le_norm (diagMul ν (unitC0 k)) k
    simpa [unitC0, abs_of_pos (mult_pos ν k)] using this

/-- **`(CTL.23)`**: with an origin atom, `α ‖b‖ ≤ ‖M_ν b‖ ≤ ‖b‖`. -/
theorem diagMul_bounds (b : C₀(ℕ, ℝ)) :
    ν.real {0} * ‖b‖ ≤ ‖diagMul ν b‖ ∧ ‖diagMul ν b‖ ≤ ‖b‖ := by
  refine ⟨?_, norm_diagMul_le ν b⟩
  rcases (measureReal_nonneg (μ := ν) (s := {0})).lt_or_eq with hα | hα
  · rw [← le_div_iff₀' hα]
    refine norm_le_of_forall (by positivity) fun k => ?_
    rw [le_div_iff₀' hα]
    calc ν.real {0} * |b k| ≤ mult ν k * |b k| :=
          mul_le_mul_of_nonneg_right (atom_le_mult ν k) (abs_nonneg _)
      _ = |diagMul ν b k| := by rw [diagMul_apply, abs_mul, abs_of_pos (mult_pos ν k)]
      _ ≤ ‖diagMul ν b‖ := abs_apply_le_norm _ k
  · rw [← hα, zero_mul]
    exact norm_nonneg _

/-- Bounded below forces a positive origin atom. -/
theorem atom_pos_of_boundedBelow {c : ℝ} (hc : 0 < c) (h : ∀ b, c * ‖b‖ ≤ ‖diagMul ν b‖) :
    0 < ν.real {0} := by
  have hle : ∀ k, c ≤ mult ν k := fun k => by
    have := h (unitC0 k)
    rwa [norm_unitC0, mul_one, norm_diagMul_unitC0] at this
  exact hc.trans_le (ge_of_tendsto' (tendsto_mult ν) hle)

/-- **Theorem 5.1, `(CTL.22)`**: `M_ν` is bounded below iff its range is closed iff `ν({0}) > 0`. -/
theorem originAtom_classification :
    ((∃ c > 0, ∀ b, c * ‖b‖ ≤ ‖diagMul ν b‖) ↔ IsClosed (range (diagMul ν))) ∧
      (IsClosed (range (diagMul ν)) ↔ 0 < ν.real {0}) := by
  have h1 : (∃ c > 0, ∀ b, c * ‖b‖ ≤ ‖diagMul ν b‖) → IsClosed (range (diagMul ν)) := by
    rintro ⟨c, hc, hb⟩
    refine ((diagMul ν).antilipschitz_of_bound (K := ⟨c⁻¹, (inv_pos.2 hc).le⟩)
      fun b => ?_).isClosed_range (diagMul ν).uniformContinuous
    show ‖b‖ ≤ c⁻¹ * ‖diagMul ν b‖
    rw [← div_eq_inv_mul, le_div_iff₀' hc]
    exact hb b
  have h2 : IsClosed (range (diagMul ν)) → ∃ c > 0, ∀ b, c * ‖b‖ ≤ ‖diagMul ν b‖ := by
    intro hcl
    obtain ⟨K, hK⟩ := (diagMul ν).antilipschitz_of_injective_of_isClosed_range
      (diagMul_injective ν) hcl
    refine ⟨((K : ℝ) + 1)⁻¹, by positivity, fun b => ?_⟩
    have := hK.le_mul_dist b 0
    rw [dist_zero_right, map_zero, dist_zero_right] at this
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (diagMul ν b), NNReal.coe_nonneg K]
  refine ⟨⟨h1, h2⟩, ⟨fun hcl => ?_, fun hα => h1 ⟨_, hα, fun b => (diagMul_bounds ν b).1⟩⟩⟩
  obtain ⟨c, hc, hb⟩ := h2 hcl
  exact atom_pos_of_boundedBelow ν hc hb

/-- Truncation after `N` coordinates. -/
def truncC0 (N : ℕ) (b : C₀(ℕ, ℝ)) : C₀(ℕ, ℝ) :=
  ofTendsto (fun k => if k < N then b k else 0) (tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop N] with k hk
    simp [not_lt.2 hk]))

theorem tendsto_truncC0 (b : C₀(ℕ, ℝ)) : Tendsto (fun N => truncC0 N b) atTop (𝓝 b) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb := tendsto_c0 b
  rw [Metric.tendsto_atTop] at hb ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hb (ε / 2) (by positivity)
  refine ⟨N, fun M hM => ?_⟩
  rw [dist_zero_right, norm_norm]
  refine lt_of_le_of_lt (norm_le_of_forall (by positivity) fun k => ?_) (half_lt_self hε)
  simp only [truncC0, ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, ofTendsto_apply]
  split_ifs with hk
  · simp only [sub_self, abs_zero]; positivity
  · have := hN k (by omega)
    rw [dist_zero_right, Real.norm_eq_abs] at this
    rw [zero_sub, abs_neg]
    exact this.le

/-- The coordinates `b ↦ (b_k)_{k < N}`. -/
def headC0 (N : ℕ) : C₀(ℕ, ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i => LinearMap.mkContinuous
    { toFun := fun b : C₀(ℕ, ℝ) => b i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 fun b => by
      rw [one_mul, Real.norm_eq_abs]
      exact abs_apply_le_norm b i

/-- The weighted re-embedding `c ↦ (a_{k+1} c_k)_{k < N}`. -/
def weightEmbed (N : ℕ) : (Fin N → ℝ) →L[ℝ] C₀(ℕ, ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ofTendsto (fun k => if h : k < N then mult ν k * c ⟨k, h⟩ else 0)
        (tendsto_const_nhds.congr' (by
          filter_upwards [eventually_ge_atTop N] with k hk
          simp [not_lt.2 hk]))
      map_add' := fun c d => ZeroAtInftyContinuousMap.ext fun k => by
        simp only [ofTendsto_apply, Pi.add_apply, ZeroAtInftyContinuousMap.coe_add]
        split_ifs <;> ring
      map_smul' := fun a c => ZeroAtInftyContinuousMap.ext fun k => by
        simp only [ofTendsto_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          ZeroAtInftyContinuousMap.coe_smul]
        split_ifs <;> ring }

/-- The rank-`N` truncation `M_ν^{(N)}` of `M_ν`. -/
def diagMulTrunc (N : ℕ) : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) := (weightEmbed ν N).comp (headC0 N)

omit [IsProbabilityMeasure ν] in
theorem diagMulTrunc_apply (N : ℕ) (b : C₀(ℕ, ℝ)) (k : ℕ) :
    diagMulTrunc ν N b k = if k < N then mult ν k * b k else 0 := by
  simp only [diagMulTrunc, ContinuousLinearMap.comp_apply, weightEmbed,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, ofTendsto_apply]
  split_ifs <;> rfl

omit [IsProbabilityMeasure ν] in
theorem isCompactOperator_diagMulTrunc (N : ℕ) : IsCompactOperator (diagMulTrunc ν N) :=
  (isCompactOperator_of_locallyCompactSpace_rng (weightEmbed ν N)).comp_clm (headC0 N)

/-- Without an origin atom the truncations converge to `M_ν` in operator norm. -/
theorem tendsto_diagMulTrunc (hα : ν {0} = 0) :
    Tendsto (diagMulTrunc ν) atTop (𝓝 (diagMul ν)) := by
  have hmult : Tendsto (mult ν) atTop (𝓝 0) := by
    have := tendsto_mult ν
    rwa [measureReal_def, hα, ENNReal.toReal_zero] at this
  refine (NormedAddCommGroup.tendsto_atTop (β := C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ))).2 fun ε hε => ?_
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hmult (ε / 2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_)
    (half_lt_self hε)
  refine norm_le_of_forall (by positivity) fun k => ?_
  simp only [sub_apply, ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply,
    diagMul_apply, diagMulTrunc_apply]
  split_ifs with hk
  · simp only [sub_self, abs_zero]; positivity
  · rw [zero_sub, abs_neg, abs_mul, abs_of_pos (mult_pos ν k)]
    have h1 := hN₀ k (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_pos (mult_pos ν k)] at h1
    exact mul_le_mul h1.le (abs_apply_le_norm b k) (abs_nonneg _) (by positivity)

/-- **Theorem 5.1, the atomless face.**  If `ν({0}) = 0`, `M_ν` is injective and compact, its range
contains every finitely supported sequence and is dense, but is not closed, and the inverse on the
range is unbounded. -/
theorem originAtom_zero (hα : ν {0} = 0) :
    Function.Injective (diagMul ν) ∧ IsCompactOperator (diagMul ν) ∧
      (∀ b : C₀(ℕ, ℝ), (∃ N, ∀ k, N ≤ k → b k = 0) → b ∈ range (diagMul ν)) ∧
      Dense (range (diagMul ν)) ∧ ¬ IsClosed (range (diagMul ν)) ∧
      ¬ ∃ C, ∀ b, ‖b‖ ≤ C * ‖diagMul ν b‖ := by
  have hα' : ν.real {0} = 0 := by rw [measureReal_def, hα, ENNReal.toReal_zero]
  have hfin : ∀ b : C₀(ℕ, ℝ), (∃ N, ∀ k, N ≤ k → b k = 0) → b ∈ range (diagMul ν) := by
    rintro b ⟨N, hN⟩
    refine ⟨ofTendsto (fun k => b k / mult ν k) (tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop N] with k hk
      rw [hN k hk, zero_div])), ZeroAtInftyContinuousMap.ext fun k => ?_⟩
    rw [diagMul_apply, ofTendsto_apply, mul_div_cancel₀ _ (mult_pos ν k).ne']
  have hncl : ¬ IsClosed (range (diagMul ν)) := fun hcl => by
    have := ((originAtom_classification ν).2.1 hcl)
    rw [hα'] at this
    exact lt_irrefl 0 this
  refine ⟨diagMul_injective ν, isCompactOperator_of_tendsto (tendsto_diagMulTrunc ν hα)
    (Eventually.of_forall (isCompactOperator_diagMulTrunc ν)), hfin, fun b => ?_, hncl, ?_⟩
  · refine mem_closure_of_tendsto (tendsto_truncC0 b) (Eventually.of_forall fun N => hfin _ ⟨N,
      fun k hk => ?_⟩)
    simp [truncC0, not_lt.2 hk]
  · rintro ⟨C, hC⟩
    have hC0 : 0 < C := by
      have := hC (unitC0 0)
      rw [norm_unitC0, norm_diagMul_unitC0] at this
      by_contra h
      push Not at h
      nlinarith [mult_pos ν 0]
    exact hncl ((originAtom_classification ν).1.1 ⟨C⁻¹, inv_pos.2 hC0, fun b => by
      rw [← div_eq_inv_mul, div_le_iff₀ hC0, mul_comm]
      exact hC b⟩)

end GaloisForLFunctions.HTGeometry.LaplaceTomography
