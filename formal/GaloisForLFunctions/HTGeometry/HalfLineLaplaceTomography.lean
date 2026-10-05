import GaloisForLFunctions.HTGeometry.CompactMomentDeterminacy
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Integer Laplace tomography of signed currents on the half-line

For a finite signed measure `J` on `Ω = [0, ∞)` its integer character responses are
`b_n(J) = ∫ e^{-nx} dJ(x)` `(CTL.8)`.  The responses for `n ≥ 1` determine `J` `(CTL.9)`.

Write `J = J⁺ - J⁻` (Jordan decomposition).  Pushing finite measures forward by
`q(x) = e^{-x} : [0,∞) → [0,1]`, a continuous injection of a Polish space and hence a measurable
embedding, turns the `n`-th response into the `n`-th moment; finite measures on `[0,1]` are
determined by their moments, so the responses for `n ≥ 0` determine a finite measure on `[0,∞)`.
The `n = 0` response (the mass) is not needed: the responses of `J⁺` and `J⁻` agree for `n ≥ 1`
exactly when those of `e^{-x} J⁺` and `e^{-x} J⁻` agree for `n ≥ 0`, and `e^{-x} > 0` can be divided
out again.  So the countable reporter `J ↦ (b_n(J))_{n ≥ 1}` is injective on all finite signed
currents, with or without zero mass.

More generally the responses at any set `S` of exponents determine `J` as soon as the monomials
`y^s`, `s ∈ S`, span a uniformly dense subspace of `C([0,1])`.  Density of the generated algebra is
not enough: `{0, 1}` generates all polynomials, but `δ_0 - 3δ_{log 2} + 2δ_{log 4} ≠ 0` has
`b_0 = b_1 = 0`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LaplaceTomography

/-- The integer character response `b_n(J) = ∫ e^{-nx} dJ(x)` `(CTL.8)`. -/
def charResponse (J : SignedMeasure ℝ≥0) (n : ℕ) : ℝ :=
  ∫ᵛ x, Real.exp (-(n * (x : ℝ))) ∂<•J

/-- The compactification `q(x) = e^{-x} : [0, ∞) → [0, 1]`. -/
def compactify (x : ℝ≥0) : Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-(x : ℝ)), (Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 x.2)⟩

theorem continuous_compactify : Continuous compactify :=
  (Real.continuous_exp.comp (NNReal.continuous_coe.neg)).subtype_mk _

theorem compactify_injective : Function.Injective compactify := fun x y h => by
  have h1 : Real.exp (-(x : ℝ)) = Real.exp (-(y : ℝ)) := congrArg Subtype.val h
  rw [Real.exp_eq_exp, neg_inj] at h1
  exact NNReal.coe_injective h1

theorem measurableEmbedding_compactify : MeasurableEmbedding compactify :=
  continuous_compactify.measurableEmbedding compactify_injective

theorem integrable_exp_neg_mul (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (fun x : ℝ≥0 => Real.exp (-(n * (x : ℝ)))) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (Nat.cast_nonneg n) x.2

/-- **Moments of the compactified measure**: `∫ y^n d(q_* μ) = ∫ e^{-nx} dμ`. -/
theorem integral_pow_map_compactify (μ : Measure ℝ≥0) (n : ℕ) :
    ∫ y, (y : ℝ) ^ n ∂(μ.map compactify) = ∫ x, Real.exp (-(n * (x : ℝ))) ∂μ := by
  rw [measurableEmbedding_compactify.integral_map]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [compactify]
  rw [← Real.exp_nat_mul, mul_neg]

/-- **Laplace determinacy**: finite measures on `[0, ∞)` with equal integer Laplace transforms
`n ≥ 0` are equal. -/
theorem measure_eq_of_laplace_eq {μ ν : Measure ℝ≥0} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, ∫ x, Real.exp (-(n * (x : ℝ))) ∂μ = ∫ x, Real.exp (-(n * (x : ℝ))) ∂ν) :
    μ = ν := by
  have hmap : μ.map compactify = ν.map compactify :=
    ext_of_forall_integral_pow_eq fun n => by
      rw [integral_pow_map_compactify, integral_pow_map_compactify, h]
  rw [← measurableEmbedding_compactify.comap_map μ, hmap, measurableEmbedding_compactify.comap_map]

/-- The damping density `e^{-x}`. -/
def damping (x : ℝ≥0) : ℝ≥0 := Real.toNNReal (Real.exp (-(x : ℝ)))

theorem measurable_damping : Measurable damping := by
  unfold damping
  fun_prop

theorem coe_damping (x : ℝ≥0) : (damping x : ℝ) = Real.exp (-(x : ℝ)) :=
  Real.coe_toNNReal _ (Real.exp_pos _).le

/-- **Laplace determinacy without the mass**: finite measures on `[0, ∞)` whose integer Laplace
transforms agree for `n ≥ 1` are equal. -/
theorem measure_eq_of_laplace_eq_succ {μ ν : Measure ℝ≥0} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, 1 ≤ n →
      ∫ x, Real.exp (-(n * (x : ℝ))) ∂μ = ∫ x, Real.exp (-(n * (x : ℝ))) ∂ν) : μ = ν := by
  set w : ℝ≥0 → ℝ≥0∞ := fun x => (damping x : ℝ≥0∞)
  have hw1 : ∀ x, w x ≤ 1 := fun x => by
    simp only [w, damping, ENNReal.coe_le_one_iff]
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (Real.exp_pos _).le, NNReal.coe_one,
      Real.exp_le_one_iff, neg_nonpos]
    exact x.2
  have hfin : ∀ ρ : Measure ℝ≥0, IsFiniteMeasure ρ → IsFiniteMeasure (ρ.withDensity w) :=
    fun ρ _ => isFiniteMeasure_withDensity (ne_top_of_le_ne_top (measure_ne_top ρ univ)
      ((lintegral_mono hw1).trans_eq (by rw [lintegral_one])))
  have hint : ∀ ρ : Measure ℝ≥0, ∀ n : ℕ, ∫ x, Real.exp (-(n * (x : ℝ))) ∂(ρ.withDensity w) =
      ∫ x, Real.exp (-((n + 1 : ℕ) * (x : ℝ))) ∂ρ := fun ρ n => by
    rw [integral_withDensity_eq_integral_smul measurable_damping]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [NNReal.smul_def, smul_eq_mul, coe_damping, ← Real.exp_add]
    push_cast
    ring_nf
  haveI := hfin μ inferInstance
  haveI := hfin ν inferInstance
  have hw : μ.withDensity w = ν.withDensity w :=
    measure_eq_of_laplace_eq fun n => by rw [hint, hint, h (n + 1) (Nat.le_add_left 1 n)]
  have hm : Measurable w := measurable_damping.coe_nnreal_ennreal
  have hne0 : ∀ x, w x ≠ 0 := fun x => by
    simp only [w, ne_eq, ENNReal.coe_eq_zero, damping, Real.toNNReal_eq_zero, not_le]
    exact Real.exp_pos _
  have hneT : ∀ x, w x ≠ ∞ := fun x => ENNReal.coe_ne_top
  rw [← withDensity_inv_same hm (ae_of_all _ hne0) (ae_of_all _ hneT) (μ := μ), hw,
    withDensity_inv_same hm (ae_of_all _ hne0) (ae_of_all _ hneT)]

theorem toSignedMeasure_sub_eq_zero {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ = ν) :
    μ.toSignedMeasure - ν.toSignedMeasure = 0 := by
  subst h
  exact sub_self _

/-- The response of a signed current through its Jordan parts. -/
theorem charResponse_eq (J : SignedMeasure ℝ≥0) (n : ℕ) :
    charResponse J n = ∫ x, Real.exp (-(n * (x : ℝ))) ∂J.toJordanDecomposition.posPart -
      ∫ x, Real.exp (-(n * (x : ℝ))) ∂J.toJordanDecomposition.negPart := by
  conv_lhs => rw [charResponse, ← J.toSignedMeasure_toJordanDecomposition,
    JordanDecomposition.toSignedMeasure]
  rw [VectorMeasure.integral_sub_vectorMeasure, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  · show Integrable _ (VectorMeasure.variation _)
    rw [Measure.variation_toSignedMeasure]
    exact integrable_exp_neg_mul _ n
  · show Integrable _ (VectorMeasure.variation _)
    rw [Measure.variation_toSignedMeasure]
    exact integrable_exp_neg_mul _ n

/-- **Theorem 3.1, sharpened**: the responses `b_n(J)`, `n ≥ 1`, determine every finite signed
current on `[0, ∞)`; no mass condition is needed. -/
theorem eq_zero_of_charResponse_eq_zero (J : SignedMeasure ℝ≥0)
    (h : ∀ n : ℕ, 1 ≤ n → charResponse J n = 0) : J = 0 := by
  have hPN := measure_eq_of_laplace_eq_succ (μ := J.toJordanDecomposition.posPart)
    (ν := J.toJordanDecomposition.negPart) fun n hn => by
      have := h n hn
      rw [charResponse_eq, sub_eq_zero] at this
      exact this
  rw [← J.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  exact toSignedMeasure_sub_eq_zero hPN

/-- **Theorem 3.1, `(CTL.9)`**: a finite zero-mass signed current on `[0, ∞)` all of whose integer
responses vanish is zero. -/
theorem eq_zero_of_mass_zero_of_charResponse (J : SignedMeasure ℝ≥0) (_hmass : J univ = 0)
    (h : ∀ n : ℕ, 1 ≤ n → charResponse J n = 0) : J = 0 :=
  eq_zero_of_charResponse_eq_zero J h

/-- **`(CTL.10)`**: the reporter `J ↦ (b_n(J))_{n ≥ 1}` is injective on finite signed currents. -/
theorem charResponse_injective :
    Function.Injective fun J : SignedMeasure ℝ≥0 => fun n : ℕ => charResponse J (n + 1) := by
  intro J K hJK
  set P := J.toJordanDecomposition.posPart
  set N := J.toJordanDecomposition.negPart
  set P' := K.toJordanDecomposition.posPart
  set N' := K.toJordanDecomposition.negPart
  have heq : P + N' = P' + N := measure_eq_of_laplace_eq_succ fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h : charResponse J (m + 1) = charResponse K (m + 1) := congrFun hJK m
    rw [charResponse_eq, charResponse_eq] at h
    rw [integral_add_measure (integrable_exp_neg_mul _ _) (integrable_exp_neg_mul _ _),
      integral_add_measure (integrable_exp_neg_mul _ _) (integrable_exp_neg_mul _ _)]
    linarith
  rw [← J.toSignedMeasure_toJordanDecomposition, ← K.toSignedMeasure_toJordanDecomposition,
    JordanDecomposition.toSignedMeasure, JordanDecomposition.toSignedMeasure]
  change P.toSignedMeasure - N.toSignedMeasure = P'.toSignedMeasure - N'.toSignedMeasure
  refine VectorMeasure.ext fun s hs => ?_
  rw [sub_apply, sub_apply, Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable hs, Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable hs]
  have h2 : (P + N').real s = (P' + N).real s := by rw [heq]
  rw [measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _),
    measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  linarith

/-! ### Exponent families with dense span -/

/-- The monomial `y ↦ y^s` on `[0, 1]`. -/
def monomialFn (s : ℕ) : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun y => (y : ℝ) ^ s, by fun_prop⟩

theorem bcInt (f : C(Icc (0 : ℝ) 1, ℝ)) (ρ : Measure (Icc (0 : ℝ) 1)) [IsFiniteMeasure ρ] :
    Integrable f ρ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)

/-- Finite measures on `[0, 1]` agreeing on a set of continuous functions with dense span are
equal. -/
theorem measure_eq_of_dense_span {μ ν : Measure (Icc (0 : ℝ) 1)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {D : Set C(Icc (0 : ℝ) 1, ℝ)}
    (hD : (Submodule.span ℝ D).topologicalClosure = ⊤)
    (h : ∀ f ∈ D, ∫ y, f y ∂μ = ∫ y, f y ∂ν) : μ = ν := by
  -- the difference of integrals as a continuous linear functional
  set L : C(Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ y, f y ∂μ - ∫ y, f y ∂ν
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply]
        rw [integral_add (bcInt f μ) (bcInt g μ), integral_add (bcInt f ν) (bcInt g ν)]
        ring
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [integral_const_mul, integral_const_mul]
        ring }
  have hLc : Continuous L := by
    refine AddMonoidHomClass.continuous_of_bound L ((μ univ).toReal + (ν univ).toReal)
      fun f => ?_
    have hb : ∀ ρ : Measure (Icc (0 : ℝ) 1), IsFiniteMeasure ρ →
        ‖∫ y, f y ∂ρ‖ ≤ ‖f‖ * (ρ univ).toReal := fun ρ _ => by
      have := norm_integral_le_of_norm_le_const (μ := ρ) (C := ‖f‖)
        (ae_of_all _ fun y => f.norm_coe_le_norm y)
      rwa [measureReal_def] at this
    show ‖∫ y, f y ∂μ - ∫ y, f y ∂ν‖ ≤ _
    calc ‖∫ y, f y ∂μ - ∫ y, f y ∂ν‖ ≤ ‖∫ y, f y ∂μ‖ + ‖∫ y, f y ∂ν‖ := norm_sub_le _ _
      _ ≤ ‖f‖ * (μ univ).toReal + ‖f‖ * (ν univ).toReal := add_le_add (hb μ ‹_›) (hb ν ‹_›)
      _ = _ := by ring
  have hker : Submodule.span ℝ D ≤ LinearMap.ker L :=
    (Submodule.span_le).2 fun f hf => by
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      show ∫ y, f y ∂μ - ∫ y, f y ∂ν = 0
      rw [h f hf, sub_self]
  have hclosed : IsClosed (LinearMap.ker L : Set C(Icc (0 : ℝ) 1, ℝ)) :=
    isClosed_eq hLc continuous_const
  have hall : ∀ f : C(Icc (0 : ℝ) 1, ℝ), L f = 0 := fun f => by
    have hmem : f ∈ (Submodule.span ℝ D).topologicalClosure := by rw [hD]; trivial
    exact LinearMap.mem_ker.1
      (Submodule.topologicalClosure_minimal _ hker hclosed hmem)
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have := hall f.toContinuousMap
  exact sub_eq_zero.1 this

/-- **Sharp boundary (3)**: the responses at any exponent set whose monomials have dense span in
`C([0,1])` determine every finite signed current on `[0, ∞)`. -/
theorem eq_zero_of_charResponse_dense (J : SignedMeasure ℝ≥0) {S : Set ℕ}
    (hS : (Submodule.span ℝ (monomialFn '' S)).topologicalClosure = ⊤)
    (h : ∀ s ∈ S, charResponse J s = 0) : J = 0 := by
  set P := J.toJordanDecomposition.posPart
  set N := J.toJordanDecomposition.negPart
  have hmap : P.map compactify = N.map compactify := by
    refine measure_eq_of_dense_span hS ?_
    rintro _ ⟨s, hs, rfl⟩
    have := h s hs
    rw [charResponse_eq, sub_eq_zero] at this
    show ∫ y, (y : ℝ) ^ s ∂(P.map compactify) = ∫ y, (y : ℝ) ^ s ∂(N.map compactify)
    rw [integral_pow_map_compactify, integral_pow_map_compactify]
    exact this
  have hPN : P = N := by
    rw [← measurableEmbedding_compactify.comap_map P, hmap,
      measurableEmbedding_compactify.comap_map]
  rw [← J.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  exact toSignedMeasure_sub_eq_zero hPN

/-- The algebra generated by `y^0, y^1` is uniformly dense in `C([0,1])` (Weierstrass). -/
theorem adjoin_monomialFn_one_dense :
    (Algebra.adjoin ℝ {monomialFn 1}).topologicalClosure = ⊤ := by
  have h : monomialFn 1 = Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) Polynomial.X := by
    ext y
    simp [monomialFn]
  rw [h, ← polynomialFunctions.eq_adjoin_X]
  exact polynomialFunctions_closure_eq_top 0 1

/-- `log 2` and `log 4` as points of `[0, ∞)`. -/
def logTwo : ℝ≥0 := ⟨Real.log 2, Real.log_nonneg one_le_two⟩

def logFour : ℝ≥0 := ⟨Real.log 4, Real.log_nonneg (by norm_num)⟩

theorem exp_neg_nat_mul_log {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.exp (-(n * Real.log a)) = (1 / a) ^ n := by
  rw [show -(n * Real.log a) = Real.log ((a ^ n)⁻¹) by rw [Real.log_inv, Real.log_pow],
    Real.exp_log (by positivity), one_div, inv_pow]

theorem coe_logTwo : (logTwo : ℝ) = Real.log 2 := rfl

theorem coe_logFour : (logFour : ℝ) = Real.log 4 := rfl

/-- The current `δ_0 - 3 δ_{log 2} + 2 δ_{log 4}`. -/
def twoMomentCurrent : SignedMeasure ℝ≥0 :=
  (Measure.dirac 0 + (2 : ℝ≥0) • Measure.dirac logFour).toSignedMeasure -
    ((3 : ℝ≥0) • Measure.dirac logTwo).toSignedMeasure

theorem charResponse_twoMomentCurrent (n : ℕ) :
    charResponse twoMomentCurrent n = 1 + 2 * (1 / 4) ^ n - 3 * (1 / 2) ^ n := by
  have hb : ∀ (μ : Measure ℝ≥0) [IsFiniteMeasure μ],
      VectorMeasure.Integrable μ.toSignedMeasure fun x : ℝ≥0 => Real.exp (-(n * (x : ℝ))) :=
    fun μ _ => by
      show Integrable _ (VectorMeasure.variation _)
      rw [Measure.variation_toSignedMeasure]
      exact integrable_exp_neg_mul _ n
  rw [charResponse, twoMomentCurrent, VectorMeasure.integral_sub_vectorMeasure (hb _) (hb _),
    VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure, integral_add_measure (integrable_exp_neg_mul _ n)
    (integrable_exp_neg_mul _ n), integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_dirac, integral_dirac, integral_dirac]
  rw [NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]
  simp only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero]
  rw [coe_logFour, coe_logTwo, exp_neg_nat_mul_log (by norm_num : (0 : ℝ) < 4),
    exp_neg_nat_mul_log two_pos]
  push_cast
  ring

theorem twoMomentCurrent_ne_zero : twoMomentCurrent ≠ 0 := by
  intro h
  have h1 : twoMomentCurrent {0} = 0 := by rw [h]; rfl
  rw [twoMomentCurrent, sub_apply,
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton 0),
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton 0)] at h1
  have hl4 : logFour ≠ 0 := fun h0 => by
    have := congrArg NNReal.toReal h0
    simp only [logFour, NNReal.coe_zero] at this
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne' this
  have hl2 : logTwo ≠ 0 := fun h0 => by
    have := congrArg NNReal.toReal h0
    simp only [logTwo, NNReal.coe_zero] at this
    exact (Real.log_pos one_lt_two).ne' this
  simp [measureReal_def, Measure.dirac_apply' _
    (measurableSet_singleton _), Set.indicator, hl4, hl2, eq_comm] at h1

/-- **Sharp boundary (3) needs the span, not the algebra**: the algebra generated by `y^0, y^1` is
dense in `C([0,1])`, yet `δ_0 - 3δ_{log 2} + 2δ_{log 4} ≠ 0` has `b_0 = b_1 = 0`. -/
theorem algebra_density_not_sufficient :
    (Algebra.adjoin ℝ {monomialFn 0, monomialFn 1}).topologicalClosure = ⊤ ∧
      twoMomentCurrent ≠ 0 ∧ charResponse twoMomentCurrent 0 = 0 ∧
      charResponse twoMomentCurrent 1 = 0 := by
  refine ⟨eq_top_iff.2 ?_, twoMomentCurrent_ne_zero, ?_, ?_⟩
  · rw [← adjoin_monomialFn_one_dense]
    exact Subalgebra.topologicalClosure_mono
      (Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ rfl)))
  · rw [charResponse_twoMomentCurrent]; norm_num
  · rw [charResponse_twoMomentCurrent]; norm_num

end GaloisForLFunctions.HTGeometry.LaplaceTomography
