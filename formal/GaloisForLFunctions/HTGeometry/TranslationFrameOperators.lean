import GaloisForLFunctions.HTGeometry.TranslationFrameHaarDiscrepancy
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten

/-!
# Frame operators of translate systems and their Haar tangent

For a Bessel family `u : ι → H` the analysis operator `C f = (⟨uᵢ, f⟩)ᵢ : H → ℓ²(ι)` is bounded, its
adjoint is the synthesis operator `S`, with `S eᵢ = uᵢ`, and `A = S S* = C* C` is the positive frame
operator with quadratic form `⟨A f, f⟩ = ∑ |⟨uᵢ, f⟩|²`.

For a `W^{1,1} ∩ L²` window `h` and a translate system `uᵢ = cᵢ T_{tᵢ} h` with clocks `tᵢ ≥ 0`, the
quadratic form is `∫ |⟨f, T_y h⟩|² dμ(y)` against the weight measure `μ = ∑ |cᵢ|² δ_{tᵢ}`.  The
continuous Haar frame operator `A_H` has quadratic form `∫_0^∞ |⟨f, T_y h⟩|² dy`.  If the cumulative
discrepancy satisfies `|μ[0, y] - κ y| ≤ ε` on `[0, ∞)`, then the translate system is Bessel and

`‖A_μ - κ A_H‖ ≤ 2 ε ‖h‖₁ ‖h'‖₁`.

* `IsBesselFamily`, `besselAnalysis`, `besselFrameOp`, `besselSynthesis_single`;
* `translateSystem`, `translateSystemMeasure`;
* `haarAnalysis`, `haarFrameOp`, `re_inner_haarFrameOp_self`, `haarFrameOp_ne_zero`;
* `isBesselFamily_translateSystem`, **`norm_besselFrameOp_translateSystem_sub_le`**;
* `besselFrameOp_eq_tsum_rankOne`, `traceNorm_tsum_rankOne_le` — the square-summable case.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### Bessel families -/

section Bessel

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **Bessel family** with bound `B`: `∑ᵢ |⟨uᵢ, f⟩|² ≤ B ‖f‖²` for every `f`. -/
def IsBesselFamily (u : ι → H) (B : ℝ) : Prop :=
  ∀ f : H, Summable (fun i => ‖⟪u i, f⟫_ℂ‖ ^ 2) ∧ ∑' i, ‖⟪u i, f⟫_ℂ‖ ^ 2 ≤ B * ‖f‖ ^ 2

omit [CompleteSpace H] in
theorem IsBesselFamily.memℓp {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) (f : H) :
    Memℓp (fun i => ⟪u i, f⟫_ℂ) 2 := by
  refine memℓp_gen ?_
  simpa [Real.rpow_two] using (hB f).1

/-- The analysis map `f ↦ (⟨uᵢ, f⟩)ᵢ` as a linear map into `ℓ²(ι)`. -/
def besselAnalysisₗ (u : ι → H) {B : ℝ} (hB : IsBesselFamily u B) :
    H →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun f := ⟨fun i => ⟪u i, f⟫_ℂ, hB.memℓp f⟩
  map_add' _ _ := Subtype.ext (funext fun _ => inner_add_right _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => inner_smul_right _ _ _)

omit [CompleteSpace H] in
theorem norm_besselAnalysisₗ_sq {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) (f : H) :
    ‖besselAnalysisₗ u hB f‖ ^ 2 = ∑' i, ‖⟪u i, f⟫_ℂ‖ ^ 2 :=
  HilbertSchmidt.lp_norm_sq_eq _

/-- The **analysis operator** of a Bessel family. -/
def besselAnalysis (u : ι → H) {B : ℝ} (hB : IsBesselFamily u B) :
    H →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous (besselAnalysisₗ u hB) (Real.sqrt B) fun f => by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_besselAnalysisₗ_sq, ← Real.sqrt_sq (norm_nonneg f),
      ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (hB f).2

omit [CompleteSpace H] in
@[simp] theorem besselAnalysis_apply_coe {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) (f : H)
    (i : ι) : (besselAnalysis u hB f : ι → ℂ) i = ⟪u i, f⟫_ℂ :=
  rfl

omit [CompleteSpace H] in
theorem norm_besselAnalysis_sq {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) (f : H) :
    ‖besselAnalysis u hB f‖ ^ 2 = ∑' i, ‖⟪u i, f⟫_ℂ‖ ^ 2 :=
  norm_besselAnalysisₗ_sq hB f

/-- The **frame operator** `A = C* C = S S*` of a Bessel family. -/
def besselFrameOp (u : ι → H) {B : ℝ} (hB : IsBesselFamily u B) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint (besselAnalysis u hB) ∘L besselAnalysis u hB

/-- The frame operator does not depend on the chosen Bessel bound. -/
theorem besselFrameOp_congr {u : ι → H} {B B' : ℝ} (hB : IsBesselFamily u B)
    (hB' : IsBesselFamily u B') : besselFrameOp u hB = besselFrameOp u hB' := rfl

theorem besselFrameOp_isPositive {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) :
    (besselFrameOp u hB).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- **Quadratic form of the frame operator**: `⟨A f, f⟩ = ∑ |⟨uᵢ, f⟩|²`. -/
theorem inner_besselFrameOp_self {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) (f : H) :
    ⟪besselFrameOp u hB f, f⟫_ℂ = ((∑' i, ‖⟪u i, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [besselFrameOp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← norm_besselAnalysis_sq hB f]
  norm_cast

theorem re_inner_besselFrameOp_self {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) (f : H) :
    RCLike.re ⟪besselFrameOp u hB f, f⟫_ℂ = ∑' i, ‖⟪u i, f⟫_ℂ‖ ^ 2 := by
  rw [inner_besselFrameOp_self]
  simp

/-- The **synthesis operator** `S = C*` sends the coordinate vector `c eᵢ` to `c uᵢ`. -/
theorem besselSynthesis_single [DecidableEq ι] {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B)
    (i : ι) (c : ℂ) :
    ContinuousLinearMap.adjoint (besselAnalysis u hB) (lp.single 2 i c) = c • u i := by
  refine ext_inner_right ℂ fun f => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left, besselAnalysis_apply_coe,
    inner_smul_left, RCLike.inner_apply, mul_comm]

/-- **Coefficient-faithful synthesis on finite supports**: `S (∑_{i ∈ s} cᵢ eᵢ) = ∑_{i ∈ s} cᵢ uᵢ`.
-/
theorem besselSynthesis_finsetSum [DecidableEq ι] {u : ι → H} {B : ℝ}
    (hB : IsBesselFamily u B) (s : Finset ι) (c : ι → ℂ) :
    ContinuousLinearMap.adjoint (besselAnalysis u hB) (∑ i ∈ s, lp.single 2 i (c i)) =
      ∑ i ∈ s, c i • u i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => besselSynthesis_single hB i (c i)

omit [CompleteSpace H] in
/-- A square-summable family is Bessel. -/
theorem isBesselFamily_of_summable_sq {u : ι → H} (hu : Summable fun i => ‖u i‖ ^ 2) :
    IsBesselFamily u (∑' i, ‖u i‖ ^ 2) := by
  intro f
  have hle : ∀ i, ‖⟪u i, f⟫_ℂ‖ ^ 2 ≤ ‖u i‖ ^ 2 * ‖f‖ ^ 2 := fun i => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  have hs : Summable fun i => ‖⟪u i, f⟫_ℂ‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle (hu.mul_right _)
  refine ⟨hs, ?_⟩
  rw [← tsum_mul_right]
  exact hs.tsum_le_tsum hle (hu.mul_right _)

omit [CompleteSpace H] in
/-- A rank-one operator `|x⟩⟨y|` has rank at most one. -/
theorem rankOne_hasRankLE_one (x y : H) :
    _root_.RHTower.HasRankLE (InnerProductSpace.rankOne ℂ x y) 1 := by
  refine ⟨Submodule.span ℂ {x}, FiniteDimensional.span_of_finite ℂ (Set.finite_singleton x), ?_,
    fun z => ?_⟩
  · have := finrank_span_le_card (R := ℂ) ({x} : Set H)
    simpa using this
  · rw [InnerProductSpace.rankOne_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/-- For a square-summable family the frame operator is the norm-convergent rank-one series. -/
theorem besselFrameOp_eq_tsum_rankOne {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B)
    (hu : Summable fun i => ‖u i‖ ^ 2) :
    besselFrameOp u hB = ∑' i, InnerProductSpace.rankOne ℂ (u i) (u i) := by
  have hsum : Summable fun i => InnerProductSpace.rankOne ℂ (u i) (u i) := by
    refine Summable.of_norm ?_
    simpa [InnerProductSpace.norm_rankOne, sq] using hu
  refine ContinuousLinearMap.ext fun f => ext_inner_left ℂ fun g => ?_
  have hap : (∑' i, InnerProductSpace.rankOne ℂ (u i) (u i)) f =
      ∑' i, InnerProductSpace.rankOne ℂ (u i) (u i) f :=
    (ContinuousLinearMap.apply ℂ H f).map_tsum hsum
  have hsumf : Summable fun i => InnerProductSpace.rankOne ℂ (u i) (u i) f :=
    hsum.mapL (ContinuousLinearMap.apply ℂ H f)
  have hin : ⟪g, ∑' i, InnerProductSpace.rankOne ℂ (u i) (u i) f⟫_ℂ =
      ∑' i, ⟪g, InnerProductSpace.rankOne ℂ (u i) (u i) f⟫_ℂ :=
    (innerSL ℂ g).map_tsum hsumf
  rw [hap, hin, besselFrameOp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, besselAnalysis_apply_coe,
    besselAnalysis_apply_coe, RCLike.inner_apply, ← inner_conj_symm g (u i)]

/-- **Trace norm of a norm-convergent rank-one series** is at most the sum of the term norms. -/
theorem traceNorm_tsum_rankOne_le [Countable ι] {A : ι → H →L[ℂ] H}
    (hA : ∀ i, _root_.RHTower.HasRankLE (A i) 1) (hnorm : Summable fun i => ‖A i‖) :
    _root_.RHTower.traceNorm H (∑' i, A i) ≤ ∑' i, ‖A i‖ := by
  classical
  have hsum : Summable A := Summable.of_norm hnorm
  rw [_root_.RHTower.traceNorm]
  apply Real.tsum_le_of_sum_le (fun n => _root_.RHTower.approxNumber_nonneg _ n)
  intro s
  apply le_of_forall_pos_le_add
  intro ε hε
  let c : ℝ := s.card
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  obtain ⟨t, ht⟩ : ∃ t : Finset ι, c * ‖(∑' i, A i) - ∑ i ∈ t, A i‖ < ε := by
    by_cases hc : c = 0
    · exact ⟨∅, by simp [hc, hε]⟩
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
      have hevent : ∀ᶠ t : Finset ι in atTop, ‖(∑' i, A i) - ∑ i ∈ t, A i‖ < ε / c := by
        have hball := hsum.hasSum.eventually (Metric.ball_mem_nhds _ (div_pos hε hcpos))
        filter_upwards [hball] with t ht'
        rwa [dist_eq_norm, norm_sub_rev] at ht'
      obtain ⟨t, htail⟩ := hevent.exists
      exact ⟨t, by
        have heq : c * (ε / c) = ε := by field_simp [hc]
        nlinarith⟩
  set S : H →L[ℂ] H := ∑ i ∈ t, A i
  have hpoint : ∀ n, _root_.RHTower.approxNumber (∑' i, A i) n ≤
      ‖(∑' i, A i) - S‖ + _root_.RHTower.approxNumber S n := by
    intro n
    apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨F, hF, hFlt⟩ := _root_.RHTower.exists_hasRankLE_norm_sub_lt S n
      (lt_add_of_pos_right _ hδ)
    calc _root_.RHTower.approxNumber (∑' i, A i) n ≤ ‖(∑' i, A i) - F‖ :=
          _root_.RHTower.approxNumber_le _ n F hF
      _ = ‖((∑' i, A i) - S) + (S - F)‖ := by congr 1; abel
      _ ≤ ‖(∑' i, A i) - S‖ + ‖S - F‖ := norm_add_le _ _
      _ ≤ ‖(∑' i, A i) - S‖ + _root_.RHTower.approxNumber S n + δ := by linarith
  have hSrank : _root_.RHTower.HasRankLE S t.card :=
    _root_.RHTower.hasRankLE_sum_finset_of_rankOne A hA t
  calc ∑ n ∈ s, _root_.RHTower.approxNumber (∑' i, A i) n
      ≤ ∑ n ∈ s, (‖(∑' i, A i) - S‖ + _root_.RHTower.approxNumber S n) :=
        Finset.sum_le_sum fun n _ => hpoint n
    _ = c * ‖(∑' i, A i) - S‖ + ∑ n ∈ s, _root_.RHTower.approxNumber S n := by
        simp [c, Finset.sum_add_distrib]
    _ ≤ c * ‖(∑' i, A i) - S‖ + _root_.RHTower.traceNorm H S := by
        gcongr
        exact Summable.sum_le_tsum s (fun n _ => _root_.RHTower.approxNumber_nonneg S n)
          ((_root_.RHTower.memSchattenClass_of_hasRankLE one_pos hSrank).congr
            (fun n => Real.rpow_one _))
    _ ≤ c * ‖(∑' i, A i) - S‖ + ∑ i ∈ t, ‖A i‖ := by
        gcongr
        exact _root_.RHTower.traceNorm_sum_le_sum_norm_of_rankOneTerms A hA t
    _ ≤ c * ‖(∑' i, A i) - S‖ + ∑' i, ‖A i‖ := by
        gcongr
        exact hnorm.sum_le_tsum t (fun i _ => norm_nonneg _)
    _ ≤ ∑' i, ‖A i‖ + ε := by linarith

/-- The frame operator of a square-summable family is trace class with trace norm at most
`∑ ‖uᵢ‖²`. -/
theorem traceNorm_besselFrameOp_le [Countable ι] {u : ι → H} {B : ℝ}
    (hB : IsBesselFamily u B) (hu : Summable fun i => ‖u i‖ ^ 2) :
    _root_.RHTower.MemSchattenClass 1 (besselFrameOp u hB) ∧
      _root_.RHTower.traceNorm H (besselFrameOp u hB) ≤ ∑' i, ‖u i‖ ^ 2 := by
  have hnorm : Summable fun i => ‖InnerProductSpace.rankOne ℂ (u i) (u i)‖ := by
    simpa [InnerProductSpace.norm_rankOne, sq] using hu
  rw [besselFrameOp_eq_tsum_rankOne hB hu]
  refine ⟨_root_.RHTower.memSchattenClass_one_tsum_rankOneTerms_of_summable_norm _
    (fun i => rankOne_hasRankLE_one _ _) hnorm, ?_⟩
  refine (traceNorm_tsum_rankOne_le (fun i => rankOne_hasRankLE_one _ _) hnorm).trans
    (le_of_eq ?_)
  exact tsum_congr fun i => by rw [InnerProductSpace.norm_rankOne, sq]

omit [CompleteSpace H] in
/-- **Operator norm from the quadratic form.**  A symmetric operator whose quadratic form is
bounded by `M ‖f‖²` has norm at most `M`. -/
theorem norm_le_of_abs_re_inner_self_le {T : H →L[ℂ] H} (hT : (T : H →ₗ[ℂ] H).IsSymmetric)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ f, |RCLike.re ⟪T f, f⟫_ℂ| ≤ M * ‖f‖ ^ 2) : ‖T‖ ≤ M := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT]
  refine ciSup_le fun f => ?_
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  by_cases hf : f = 0
  · simp [hf, hM]
  · have hpos : 0 < ‖f‖ ^ 2 := by positivity
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h f

omit [CompleteSpace H] in
/-- **Lower norm bound from one test vector.** -/
theorem re_inner_self_le_norm_mul {T : H →L[ℂ] H} (f : H) :
    RCLike.re ⟪T f, f⟫_ℂ ≤ ‖T‖ * ‖f‖ ^ 2 := by
  calc RCLike.re ⟪T f, f⟫_ℂ ≤ ‖⟪T f, f⟫_ℂ‖ := RCLike.re_le_norm _
    _ ≤ ‖T f‖ * ‖f‖ := norm_inner_le_norm _ _
    _ ≤ ‖T‖ * ‖f‖ * ‖f‖ := by gcongr; exact T.le_opNorm f
    _ = ‖T‖ * ‖f‖ ^ 2 := by ring

/-- **Matrix form of the frame operator**: `⟨g, A f⟩ = ∑ ⟨g, uᵢ⟩ ⟨uᵢ, f⟩`. -/
theorem inner_besselFrameOp {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) (g f : H) :
    ⟪g, besselFrameOp u hB f⟫_ℂ = ∑' i, ⟪g, u i⟫_ℂ * ⟪u i, f⟫_ℂ := by
  rw [besselFrameOp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [besselAnalysis_apply_coe, besselAnalysis_apply_coe, RCLike.inner_apply,
    ← inner_conj_symm g (u i), mul_comm]

omit [CompleteSpace H] in
/-- The frame coefficients of two Bessel families pair summably. -/
theorem summable_inner_mul_inner {u : ι → H} {B : ℝ} (hB : IsBesselFamily u B) (g f : H) :
    Summable fun i => ⟪g, u i⟫_ℂ * ⟪u i, f⟫_ℂ := by
  refine Summable.of_norm_bounded (g := fun i => (‖⟪u i, g⟫_ℂ‖ ^ 2 + ‖⟪u i, f⟫_ℂ‖ ^ 2) / 2)
    (((hB g).1.add (hB f).1).div_const 2) fun i => ?_
  rw [norm_mul, norm_inner_symm]
  nlinarith [sq_nonneg (‖⟪u i, g⟫_ℂ‖ - ‖⟪u i, f⟫_ℂ‖)]

omit [CompleteSpace H] in
/-- Joining two Bessel families gives a Bessel family. -/
theorem isBesselFamily_sumElim {κ : Type*} {u : ι → H} {v : κ → H} {B₁ B₂ : ℝ}
    (h₁ : IsBesselFamily u B₁) (h₂ : IsBesselFamily v B₂) :
    IsBesselFamily (Sum.elim u v) (B₁ + B₂) := by
  intro f
  have hs : Summable fun i => ‖⟪Sum.elim u v i, f⟫_ℂ‖ ^ 2 :=
    Summable.sum _ (h₁ f).1 (h₂ f).1
  refine ⟨hs, ?_⟩
  rw [Summable.tsum_sum (f := fun i => ‖⟪Sum.elim u v i, f⟫_ℂ‖ ^ 2) (h₁ f).1 (h₂ f).1, add_mul]
  exact add_le_add (h₁ f).2 (h₂ f).2

/-- **The frame operator of a joined family is the sum of the frame operators.** -/
theorem besselFrameOp_sumElim {κ : Type*} {u : ι → H} {v : κ → H} {B₁ B₂ B : ℝ}
    (h₁ : IsBesselFamily u B₁) (h₂ : IsBesselFamily v B₂) (h : IsBesselFamily (Sum.elim u v) B) :
    besselFrameOp (Sum.elim u v) h = besselFrameOp u h₁ + besselFrameOp v h₂ := by
  refine ContinuousLinearMap.ext fun f => ext_inner_left ℂ fun g => ?_
  rw [add_apply, inner_add_right, inner_besselFrameOp, inner_besselFrameOp,
    inner_besselFrameOp]
  exact Summable.tsum_sum (f := fun i => ⟪g, Sum.elim u v i⟫_ℂ * ⟪Sum.elim u v i, f⟫_ℂ)
    (summable_inner_mul_inner h₁ g f) (summable_inner_mul_inner h₂ g f)

end Bessel

/-! ### Square norms in `L²` -/

/-- `‖[F]‖² = ∫ ‖F‖²` for an `L²` representative. -/
theorem norm_sq_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℂ}
    (hF : MemLp F 2 μ) : ‖hF.toLp F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  have h1 : ⟪hF.toLp F, hF.toLp F⟫_ℂ = ((∫ x, ‖F x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp] with x hx
    rw [hx, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h2 := congrArg RCLike.re h1
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ)] at h2
  simpa using h2

/-! ### Translate systems and the Haar frame -/

section Translate

variable {ι : Type*} {h h' : ℝ → ℂ}

/-- The **translate system** `uᵢ = cᵢ T_{tᵢ} w`, with literal coefficients `cᵢ` and clocks `tᵢ`. -/
def translateSystem (w : Lp ℂ 2 (volume : Measure ℝ)) (c : ι → ℂ) (t : ι → ℝ) (i : ι) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  c i • translateRight (t i) w

/-- The **weight measure** `∑ᵢ |cᵢ|² δ_{tᵢ}` of a translate system. -/
def translateSystemMeasure (c : ι → ℂ) (t : ι → ℝ) : Measure ℝ :=
  Measure.sum fun i => ENNReal.ofReal (‖c i‖ ^ 2) • Measure.dirac (t i)

/-- The phase of `cᵢ` cancels in the frame coefficient: `|⟨uᵢ, f⟩|² = |cᵢ|² |g_f(tᵢ)|²`. -/
theorem norm_inner_translateSystem_sq (w f : Lp ℂ 2 (volume : Measure ℝ)) (c : ι → ℂ)
    (t : ι → ℝ) (i : ι) :
    ‖⟪translateSystem w c t i, f⟫_ℂ‖ ^ 2 = ‖c i‖ ^ 2 * ‖translateCorrelation w f (t i)‖ ^ 2 := by
  rw [translateSystem, inner_smul_left, norm_mul, RCLike.norm_conj, mul_pow, translateCorrelation,
    norm_inner_symm]

theorem lintegral_translateSystemMeasure (c : ι → ℂ) (t : ι → ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ y, F y ∂translateSystemMeasure c t = ∑' i, ENNReal.ofReal (‖c i‖ ^ 2) * F (t i) := by
  rw [translateSystemMeasure, lintegral_sum_measure]
  refine tsum_congr fun i => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem translateSystemMeasure_apply (c : ι → ℂ) (t : ι → ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    translateSystemMeasure c t S = ∑' i, ENNReal.ofReal (‖c i‖ ^ 2) * S.indicator 1 (t i) := by
  rw [translateSystemMeasure, Measure.sum_apply _ hS]
  refine tsum_congr fun i => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]

/-- With clocks in `[0, ∞)`, integrals over `[0, ∞)` against the weight measure are full sums. -/
theorem setLIntegral_Ici_translateSystemMeasure (c : ι → ℂ) {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (F : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ici 0, F y ∂translateSystemMeasure c t =
      ∑' i, ENNReal.ofReal (‖c i‖ ^ 2) * F (t i) := by
  rw [← lintegral_indicator measurableSet_Ici, lintegral_translateSystemMeasure]
  refine tsum_congr fun i => ?_
  rw [indicator_of_mem (mem_Ici.mpr (ht i))]

namespace SobolevTranslateWindow

/-- The continuous analysis function `y ↦ ⟨T_y h, f⟩`. -/
def haarAnalysisFun (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ))
    (y : ℝ) : ℂ :=
  ⟪translateRight y W.toL2, f⟫_ℂ

theorem norm_haarAnalysisFun_sq (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) :
    ‖W.haarAnalysisFun f y‖ ^ 2 = W.corrSq f y := by
  rw [haarAnalysisFun, norm_inner_symm]
  rfl

theorem continuous_haarAnalysisFun (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Continuous (W.haarAnalysisFun f) := by
  have heq : W.haarAnalysisFun f = fun y => conj (translateCorrelation W.toL2 f y) := by
    funext y
    rw [haarAnalysisFun, translateCorrelation, inner_conj_symm]
  rw [heq]
  exact continuous_star.comp (W.continuous_translateCorrelation f)

theorem memLp_haarAnalysisFun (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (W.haarAnalysisFun f) 2 (volume.restrict (Ici (0 : ℝ))) := by
  refine MemLp.restrict _ ?_
  rw [memLp_two_iff_integrable_sq_norm (W.continuous_haarAnalysisFun f).aestronglyMeasurable]
  simp_rw [norm_haarAnalysisFun_sq]
  exact W.integrable_corrSq f

/-- `∫ q_f ≤ ‖h‖₁² ‖f‖₂²`. -/
theorem integral_corrSq_le (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ y, W.corrSq f y ≤ (∫ x, ‖h x‖) ^ 2 * ‖f‖ ^ 2 := by
  have hA : 0 ≤ ∫ x, ‖h x‖ := integral_nonneg fun _ => norm_nonneg _
  have key : ENNReal.ofReal (∫ y, W.corrSq f y) ≤ ENNReal.ofReal ((∫ x, ‖h x‖) ^ 2 * ‖f‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (W.integrable_corrSq f)
      (.of_forall (W.corrSq_nonneg f))]
    refine (W.lintegral_corrSq_le f).trans (le_of_eq ?_)
    rw [← ofReal_integral_norm_eq_lintegral_enorm W.integrable, lintegral_enorm_sq_eq,
      ← ENNReal.ofReal_pow hA, ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key

/-- The continuous analysis map as a linear map into `L²([0, ∞))`. -/
def haarAnalysisₗ (W : SobolevTranslateWindow h h') :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ici (0 : ℝ))) where
  toFun f := (W.memLp_haarAnalysisFun f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_forall fun y => inner_add_right _ _ _)
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun y => inner_smul_right _ _ _)

theorem norm_haarAnalysisₗ_sq (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖W.haarAnalysisₗ f‖ ^ 2 = ∫ y in Ici 0, W.corrSq f y := by
  change ‖(W.memLp_haarAnalysisFun f).toLp _‖ ^ 2 = _
  rw [norm_sq_toLp_eq_integral]
  simp_rw [norm_haarAnalysisFun_sq]

/-- The **continuous Haar analysis operator** `f ↦ (y ↦ ⟨T_y h, f⟩) : L²(ℝ) → L²([0, ∞))`. -/
def haarAnalysis (W : SobolevTranslateWindow h h') :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume.restrict (Ici (0 : ℝ))) :=
  LinearMap.mkContinuous W.haarAnalysisₗ (∫ x, ‖h x‖) fun f => by
    have hA : 0 ≤ ∫ x, ‖h x‖ := integral_nonneg fun _ => norm_nonneg _
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [norm_haarAnalysisₗ_sq, mul_pow]
    refine le_trans ?_ (W.integral_corrSq_le f)
    exact setIntegral_le_integral (W.integrable_corrSq f) (.of_forall (W.corrSq_nonneg f))

/-- The **continuous Haar frame operator** `A_H`, `⟨A_H f, f⟩ = ∫_0^∞ |⟨f, T_y h⟩|² dy`. -/
def haarFrameOp (W : SobolevTranslateWindow h h') :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ContinuousLinearMap.adjoint W.haarAnalysis ∘L W.haarAnalysis

theorem haarFrameOp_isPositive (W : SobolevTranslateWindow h h') : W.haarFrameOp.IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem re_inner_haarFrameOp_self (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    RCLike.re ⟪W.haarFrameOp f, f⟫_ℂ = ∫ y in Ici 0, W.corrSq f y := by
  rw [haarFrameOp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact W.norm_haarAnalysisₗ_sq f

/-- `T_0 w = w`. -/
theorem translateRight_zero (w : Lp ℂ 2 (volume : Measure ℝ)) : translateRight 0 w = w := by
  refine Lp.ext ?_
  filter_upwards [coeFn_translateRight 0 w] with x hx
  rw [hx, sub_zero]

/-- Near the origin the self-correlation of a nonzero window stays above half its peak. -/
theorem exists_corrSq_self_ge (W : SobolevTranslateWindow h h') (hw : W.toL2 ≠ 0) :
    ∃ δ > 0, ∀ y ∈ Icc (0 : ℝ) δ, ‖W.toL2‖ ^ 4 / 2 ≤ W.corrSq W.toL2 y := by
  have h0 : W.corrSq W.toL2 0 = ‖W.toL2‖ ^ 4 := by
    rw [corrSq, translateCorrelation, translateRight_zero, inner_self_eq_norm_sq_to_K]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    simp [norm_pow]
  have hpos : 0 < ‖W.toL2‖ ^ 4 := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (W.continuous_corrSq W.toL2).continuousAt
    (‖W.toL2‖ ^ 4 / 2) (by positivity)
  refine ⟨δ / 2, by positivity, fun y hy => ?_⟩
  have hdist : dist y 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1]
    linarith [hy.2]
  have := hball hdist
  rw [h0, Real.dist_eq] at this
  linarith [(abs_lt.mp this).1]

/-- **The Haar tangent is nonzero**: `⟨A_H h, h⟩ > 0` for a nonzero window. -/
theorem re_inner_haarFrameOp_window_pos (W : SobolevTranslateWindow h h') (hw : W.toL2 ≠ 0) :
    0 < RCLike.re ⟪W.haarFrameOp W.toL2, W.toL2⟫_ℂ := by
  rw [re_inner_haarFrameOp_self]
  obtain ⟨δ, hδ, hge⟩ := W.exists_corrSq_self_ge hw
  have hpos : 0 < ‖W.toL2‖ ^ 4 / 2 := by positivity
  calc 0 < ‖W.toL2‖ ^ 4 / 2 * δ := by positivity
    _ = ∫ _ in Icc (0 : ℝ) δ, ‖W.toL2‖ ^ 4 / 2 := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hδ.le, sub_zero, mul_comm]
    _ ≤ ∫ y in Icc (0 : ℝ) δ, W.corrSq W.toL2 y :=
        setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne)
          (W.integrable_corrSq _).integrableOn measurableSet_Icc hge
    _ ≤ ∫ y in Ici 0, W.corrSq W.toL2 y :=
        setIntegral_mono_set (W.integrable_corrSq _).integrableOn
          (.of_forall fun y => W.corrSq_nonneg _ y) Icc_subset_Ici_self.eventuallyLE

theorem haarFrameOp_ne_zero (W : SobolevTranslateWindow h h') (hw : W.toL2 ≠ 0) :
    W.haarFrameOp ≠ 0 := by
  intro h0
  have := W.re_inner_haarFrameOp_window_pos hw
  rw [h0] at this
  simp at this

/-- **Translate-system comparison.**  If the clocks lie in `[0, ∞)`, the weight measure is finite
on bounded windows and its cumulative discrepancy against `κ dy` is at most `ε`, then the frame
coefficients are square-summable and their sum is within `2 ε ‖h‖₁ ‖h'‖₁ ‖f‖²` of
`κ ∫_0^∞ |⟨f, T_y h⟩|² dy`. -/
theorem translateSystem_comparison (W : SobolevTranslateWindow h h') [Countable ι] (c : ι → ℂ)
    {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (hμ : ∀ R, translateSystemMeasure c t (Icc 0 R) ≠ ⊤)
    {κ ε : ℝ} (hκ : 0 ≤ κ)
    (hD : ∀ y, 0 ≤ y → |(translateSystemMeasure c t).real (Icc 0 y) - κ * y| ≤ ε)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Summable (fun i => ‖⟪translateSystem W.toL2 c t i, f⟫_ℂ‖ ^ 2) ∧
      |∑' i, ‖⟪translateSystem W.toL2 c t i, f⟫_ℂ‖ ^ 2 - κ * ∫ y in Ici 0, W.corrSq f y| ≤
        ε * (2 * ((∫ x, ‖h x‖) * (∫ x, ‖h' x‖) * ‖f‖ ^ 2)) := by
  set μ := translateSystemMeasure c t
  set ν : Measure ℝ := ENNReal.ofReal κ • volume
  have hD' : ∀ y, 0 ≤ y → |μ.real (Icc 0 y) - ν.real (Icc 0 y)| ≤ ε := fun y hy => by
    rw [measureReal_smul_volume_Icc hκ hy]
    exact hD y hy
  have hqν : IntegrableOn (W.corrSq f) (Ici 0) ν :=
    ((W.integrable_corrSq f).smul_measure ENNReal.ofReal_ne_top).integrableOn
  obtain ⟨hqμ, hcmp⟩ := abs_setIntegral_Ici_sub_le μ ν hμ (smul_volume_Icc_ne_top κ) hD'
    (W.corrSq_nonneg f) (W.continuous_corrSq f) hqν (W.integrable_corrSqDeriv f).integrableOn
    (W.corrSq_sub_eq_integral f) (W.tendsto_corrSq_atTop f)
  -- the `μ`-integral is the coefficient sum
  have hterm : ∀ i, ENNReal.ofReal (‖c i‖ ^ 2) * ENNReal.ofReal (W.corrSq f (t i)) =
      ENNReal.ofReal (‖⟪translateSystem W.toL2 c t i, f⟫_ℂ‖ ^ 2) := fun i => by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), norm_inner_translateSystem_sq]
    rfl
  have hlint : ENNReal.ofReal (∫ y in Ici 0, W.corrSq f y ∂μ) =
      ∑' i, ENNReal.ofReal (‖⟪translateSystem W.toL2 c t i, f⟫_ℂ‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hqμ
      ((ae_restrict_iff' measurableSet_Ici).mpr (.of_forall fun y _ => W.corrSq_nonneg f y)),
      setLIntegral_Ici_translateSystemMeasure c ht]
    exact tsum_congr hterm
  have hfin : ∑' i, ENNReal.ofReal (‖⟪translateSystem W.toL2 c t i, f⟫_ℂ‖ ^ 2) ≠ ⊤ := by
    rw [← hlint]
    exact ENNReal.ofReal_ne_top
  have hsum : Summable (fun i => ‖⟪translateSystem W.toL2 c t i, f⟫_ℂ‖ ^ 2) := by
    have := ENNReal.summable_toReal hfin
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have heq : ∑' i, ‖⟪translateSystem W.toL2 c t i, f⟫_ℂ‖ ^ 2 = ∫ y in Ici 0, W.corrSq f y ∂μ := by
    have h1 := ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsum
    rw [← hlint] at h1
    have h2 : 0 ≤ ∫ y in Ici 0, W.corrSq f y ∂μ :=
      setIntegral_nonneg measurableSet_Ici fun y _ => W.corrSq_nonneg f y
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun i => sq_nonneg _) h2).mp h1
  have hνint : ∫ y in Ici 0, W.corrSq f y ∂ν = κ * ∫ y in Ici 0, W.corrSq f y := by
    rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hκ, smul_eq_mul]
  refine ⟨hsum, ?_⟩
  rw [heq, ← hνint]
  refine hcmp.trans ?_
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hD 0 le_rfl)
  gcongr
  calc ∫ s in Ici 0, |W.corrSqDeriv f s| ≤ ∫ s, |W.corrSqDeriv f s| :=
        setIntegral_le_integral (W.integrable_corrSqDeriv f).abs (.of_forall fun _ => abs_nonneg _)
    _ ≤ _ := W.integral_norm_corrSqDeriv_le f

/-- **A translate system with controlled discrepancy is a Bessel family.** -/
theorem isBesselFamily_translateSystem (W : SobolevTranslateWindow h h') [Countable ι]
    (c : ι → ℂ) {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hμ : ∀ R, translateSystemMeasure c t (Icc 0 R) ≠ ⊤) {κ ε : ℝ} (hκ : 0 ≤ κ)
    (hD : ∀ y, 0 ≤ y → |(translateSystemMeasure c t).real (Icc 0 y) - κ * y| ≤ ε) :
    IsBesselFamily (translateSystem W.toL2 c t)
      (κ * (∫ x, ‖h x‖) ^ 2 + ε * (2 * ((∫ x, ‖h x‖) * (∫ x, ‖h' x‖)))) := by
  intro f
  obtain ⟨hsum, hcmp⟩ := W.translateSystem_comparison c ht hμ hκ hD f
  refine ⟨hsum, ?_⟩
  have hHaar : κ * ∫ y in Ici 0, W.corrSq f y ≤ κ * ((∫ x, ‖h x‖) ^ 2 * ‖f‖ ^ 2) := by
    gcongr
    exact (setIntegral_le_integral (W.integrable_corrSq f)
      (.of_forall (W.corrSq_nonneg f))).trans (W.integral_corrSq_le f)
  have := (abs_le.mp hcmp).2
  nlinarith

/-- **The operator-norm Haar tangent bound.**  For every Bessel bound `B` of a translate system
with cumulative discrepancy at most `ε` against `κ dy`,
`‖A_μ - κ A_H‖ ≤ 2 ε ‖h‖₁ ‖h'‖₁`. -/
theorem norm_besselFrameOp_translateSystem_sub_le (W : SobolevTranslateWindow h h')
    [Countable ι] (c : ι → ℂ) {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hμ : ∀ R, translateSystemMeasure c t (Icc 0 R) ≠ ⊤) {κ ε : ℝ} (hκ : 0 ≤ κ)
    (hD : ∀ y, 0 ≤ y → |(translateSystemMeasure c t).real (Icc 0 y) - κ * y| ≤ ε)
    {B : ℝ} (hB : IsBesselFamily (translateSystem W.toL2 c t) B) :
    ‖besselFrameOp _ hB - (κ : ℂ) • W.haarFrameOp‖ ≤
      ε * (2 * ((∫ x, ‖h x‖) * (∫ x, ‖h' x‖))) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hD 0 le_rfl)
  have hsa : IsSelfAdjoint (besselFrameOp _ hB - (κ : ℂ) • W.haarFrameOp) :=
    (besselFrameOp_isPositive hB).isSelfAdjoint.sub
      ((IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) W.haarFrameOp_isPositive.isSelfAdjoint))
  refine norm_le_of_abs_re_inner_self_le hsa.isSymmetric (by positivity) fun f => ?_
  have hre : RCLike.re ⟪(besselFrameOp _ hB - (κ : ℂ) • W.haarFrameOp) f, f⟫_ℂ =
      ∑' i, ‖⟪translateSystem W.toL2 c t i, f⟫_ℂ‖ ^ 2 - κ * ∫ y in Ici 0, W.corrSq f y := by
    rw [sub_apply, inner_sub_left, map_sub, re_inner_besselFrameOp_self,
      smul_apply, inner_smul_left, ← re_inner_haarFrameOp_self]
    simp
  rw [hre]
  refine (W.translateSystem_comparison c ht hμ hκ hD f).2.trans (le_of_eq ?_)
  ring

/-- **Local mass forces operator norm.**  There is a window `[0, δ]` such that for every finite
translate system indexed by `s` and every subfamily `s' ⊆ s` with clocks in `[0, δ]`, the frame
operator has norm at least `(‖h‖₂² / 2) ∑_{i ∈ s'} |cᵢ|²`. -/
theorem exists_window_norm_ge (W : SobolevTranslateWindow h h') (hw : W.toL2 ≠ 0) :
    ∃ δ > 0, ∀ (s s' : Finset ι), s' ⊆ s → ∀ (c : ι → ℂ) (t : ι → ℝ),
      (∀ i ∈ s', t i ∈ Icc (0 : ℝ) δ) →
      ‖W.toL2‖ ^ 2 / 2 * ∑ i ∈ s', ‖c i‖ ^ 2 ≤
        ‖∑ i ∈ s, InnerProductSpace.rankOne ℂ (translateSystem W.toL2 c t i)
          (translateSystem W.toL2 c t i)‖ := by
  obtain ⟨δ, hδ, hge⟩ := W.exists_corrSq_self_ge hw
  refine ⟨δ, hδ, fun s s' hss' c t hst => ?_⟩
  set T := ∑ i ∈ s, InnerProductSpace.rankOne ℂ (translateSystem W.toL2 c t i)
    (translateSystem W.toL2 c t i)
  have hre : RCLike.re ⟪T W.toL2, W.toL2⟫_ℂ =
      ∑ i ∈ s, ‖⟪translateSystem W.toL2 c t i, W.toL2⟫_ℂ‖ ^ 2 := by
    simp only [T, _root_.sum_apply, sum_inner, map_sum, InnerProductSpace.rankOne_apply,
      inner_smul_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hlow : ‖W.toL2‖ ^ 4 / 2 * ∑ i ∈ s', ‖c i‖ ^ 2 ≤ RCLike.re ⟪T W.toL2, W.toL2⟫_ℂ := by
    rw [hre, Finset.mul_sum]
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hss' fun i _ _ => sq_nonneg _)
    refine Finset.sum_le_sum fun i hi => ?_
    rw [norm_inner_translateSystem_sq, mul_comm]
    gcongr
    exact hge (t i) (hst i hi)
  have hupp := re_inner_self_le_norm_mul (T := T) W.toL2
  have hnpos : 0 < ‖W.toL2‖ ^ 2 := by positivity
  have hkey : ‖W.toL2‖ ^ 2 / 2 * (∑ i ∈ s', ‖c i‖ ^ 2) * ‖W.toL2‖ ^ 2 ≤ ‖T‖ * ‖W.toL2‖ ^ 2 := by
    calc ‖W.toL2‖ ^ 2 / 2 * (∑ i ∈ s', ‖c i‖ ^ 2) * ‖W.toL2‖ ^ 2
        = ‖W.toL2‖ ^ 4 / 2 * ∑ i ∈ s', ‖c i‖ ^ 2 := by ring
      _ ≤ _ := hlow.trans hupp
  exact le_of_mul_le_mul_right hkey hnpos

end SobolevTranslateWindow

end Translate

end GaloisForLFunctions.HTGeometry
