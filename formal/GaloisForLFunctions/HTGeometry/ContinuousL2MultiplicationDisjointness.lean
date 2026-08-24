import GaloisForLFunctions.HTGeometry.SourceLinearClosedRelationSplitting
import GaloisForLFunctions.HTGeometry.L2FourierMultiplier
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import GaloisForLFunctions.HTGeometry.WeightedHolder
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Disjointness of mutually singular continuous multiplication representations
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopologyEither X ℂ]

/-- Multiplication representation of `C(X)` on `L²(X, μ)`. -/
def continuousL2Mul (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (p := 2) (μ := μ) f.continuous.measurable
    (norm_nonneg f) f.norm_coe_le_norm

omit [SecondCountableTopologyEither X ℂ] in
/-- Equal finite measures have a nonzero closed source-linear sewing between their continuous
multiplication representations.  The witness is the diagonal graph after transporting the
measure equality. -/
theorem continuousL2Mul_nonzeroClosedSourceLinearSewing_of_measure_eq
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hνμ : ν = μ) (u : Lp ℂ 2 μ) (hu : u ≠ 0) :
    NonzeroClosedSourceLinearSewing (continuousL2Mul μ) (continuousL2Mul ν) := by
  subst ν
  exact nonzeroClosedSourceLinearSewing_self (continuousL2Mul μ) u hu

omit [SecondCountableTopologyEither X ℂ] in
theorem norm_continuousL2Mul_le (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    ‖continuousL2Mul μ f‖ ≤ ‖f‖ :=
  norm_lpBoundedMulCLM_le f.continuous.measurable (norm_nonneg f) f.norm_coe_le_norm

omit [SecondCountableTopologyEither X ℂ] in
@[simp] theorem continuousL2Mul_coeFn (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℂ)) (u : Lp ℂ 2 μ) :
    ((continuousL2Mul μ f u : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
      fun x => f x * (u : X → ℂ) x :=
  lpBoundedMulCLM_coeFn f.continuous.measurable (norm_nonneg f) f.norm_coe_le_norm u

@[simp] theorem continuousL2Mul_apply_toLp (μ : Measure X) [IsFiniteMeasure μ]
    (f g : C(X, ℂ)) :
    continuousL2Mul μ f (ContinuousMap.toLp 2 μ ℂ g) =
      ContinuousMap.toLp 2 μ ℂ (f * g) := by
  apply Lp.ext
  filter_upwards [continuousL2Mul_coeFn μ f (ContinuousMap.toLp 2 μ ℂ g),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ g,
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ (f * g : C(X, ℂ))]
    with x hmul hg hfg
  rw [hmul, hg, hfg, ContinuousMap.mul_apply]

omit [SecondCountableTopologyEither X ℂ] in
@[simp] theorem continuousL2Mul_one (μ : Measure X) [IsFiniteMeasure μ] :
    continuousL2Mul μ 1 = 1 := by
  apply lpBoundedMulCLM_eq_id
  filter_upwards with x
  exact ContinuousMap.one_apply x

omit [SecondCountableTopologyEither X ℂ] in
theorem continuousL2Mul_add (μ : Measure X) [IsFiniteMeasure μ] (f g : C(X, ℂ)) :
    continuousL2Mul μ (f + g) = continuousL2Mul μ f + continuousL2Mul μ g := by
  ext u
  change ((continuousL2Mul μ (f + g) u : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
    (((continuousL2Mul μ f u + continuousL2Mul μ g u : Lp ℂ 2 μ) : X → ℂ))
  filter_upwards [continuousL2Mul_coeFn μ (f + g) u,
    continuousL2Mul_coeFn μ f u, continuousL2Mul_coeFn μ g u,
    Lp.coeFn_add (continuousL2Mul μ f u) (continuousL2Mul μ g u)]
    with x hsum hf hg hadd
  rw [hsum, hadd]
  change (f + g) x * ((u : X → ℂ) x) =
    ((continuousL2Mul μ f u : Lp ℂ 2 μ) : X → ℂ) x +
      ((continuousL2Mul μ g u : Lp ℂ 2 μ) : X → ℂ) x
  rw [hf, hg, ContinuousMap.add_apply, add_mul]

omit [SecondCountableTopologyEither X ℂ] in
theorem continuousL2Mul_sub (μ : Measure X) [IsFiniteMeasure μ] (f g : C(X, ℂ)) :
    continuousL2Mul μ (f - g) = continuousL2Mul μ f - continuousL2Mul μ g := by
  ext u
  change ((continuousL2Mul μ (f - g) u : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
    (((continuousL2Mul μ f u - continuousL2Mul μ g u : Lp ℂ 2 μ) : X → ℂ))
  filter_upwards [continuousL2Mul_coeFn μ (f - g) u,
    continuousL2Mul_coeFn μ f u, continuousL2Mul_coeFn μ g u,
    Lp.coeFn_sub (continuousL2Mul μ f u) (continuousL2Mul μ g u)]
    with x hsub hf hg hsubout
  rw [hsub, hsubout]
  change (f - g) x * ((u : X → ℂ) x) =
    ((continuousL2Mul μ f u : Lp ℂ 2 μ) : X → ℂ) x -
      ((continuousL2Mul μ g u : Lp ℂ 2 μ) : X → ℂ) x
  rw [hf, hg, ContinuousMap.sub_apply, sub_mul]

omit [SecondCountableTopologyEither X ℂ] in
theorem adjoint_continuousL2Mul (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    (continuousL2Mul μ f).adjoint = continuousL2Mul μ (star f) := by
  symm
  apply lpBoundedMulCLM_eq_adjoint_conj_general
  intro x
  exact ContinuousMap.star_apply f x

/-- L² norm bound for a continuous function supported in a measurable set. -/
theorem norm_continuousMapToLp_sq_le_measureReal_mul
    (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ))
    {S : Set X} (hS : MeasurableSet S) {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (hsupp : Function.support f ⊆ S) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 ≤ μ.real S * B ^ 2 := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc
    (∫ x, ‖((ContinuousMap.toLp 2 μ ℂ f : Lp ℂ 2 μ) : X → ℂ) x‖ ^ 2 ∂μ) =
        ∫ x, ‖f x‖ ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ f] with x hx
      rw [hx]
    _ = ∫ x in S, ‖f x‖ ^ 2 ∂μ := by
      rw [← integral_indicator hS]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ S
      · simp [Set.indicator_of_mem hx]
      · have hzero : f x = 0 := by
          by_contra hne
          exact hx (hsupp hne)
        simp [Set.indicator_of_notMem hx, hzero]
    _ ≤ μ.real S * B ^ 2 :=
      integral_normSq_le_measure_mul_sq f.continuous.aestronglyMeasurable hB (measure_ne_top μ S)

/-- Quantitative consequence of the supported `L²` energy estimate. -/
theorem norm_continuousMapToLp_lt_mul_of_measureReal_lt_sq
    (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ))
    {S : Set X} (hS : MeasurableSet S) {a B : ℝ}
    (ha : 0 < a) (hBpos : 0 < B) (hmeasure : μ.real S < a ^ 2)
    (hB : ∀ x, ‖f x‖ ≤ B) (hsupp : Function.support f ⊆ S) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ < a * B := by
  have hle := norm_continuousMapToLp_sq_le_measureReal_mul μ f hS hB hsupp
  have hsq : ‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 < (a * B) ^ 2 :=
    hle.trans_lt <| by
      calc
        μ.real S * B ^ 2 < a ^ 2 * B ^ 2 :=
          mul_lt_mul_of_pos_right hmeasure (sq_pos_of_pos hBpos)
        _ = (a * B) ^ 2 := by ring
  exact (sq_lt_sq₀ (norm_nonneg _) (mul_nonneg ha.le hBpos.le)).mp hsq

@[simp] theorem continuousL2Mul_apply_oneToLp
    (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    continuousL2Mul μ f (ContinuousMap.toLp 2 μ ℂ (1 : C(X, ℂ))) =
      ContinuousMap.toLp 2 μ ℂ f := by
  rw [continuousL2Mul_apply_toLp]
  simp

/-- A bounded intertwiner between mutually singular `C(X)` multiplication representations is
zero.  The proof uses regularity to separate conull closed pieces and Urysohn's lemma, then density
of continuous functions in `L²`; no measurable-multiplier hypothesis is inserted. -/
theorem continuousL2Mul_intertwiner_eq_zero_of_mutuallySingular
    [NormalSpace X] {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.WeaklyRegular] [ν.WeaklyRegular]
    (hmut : μ ⟂ₘ ν) (V : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν)
    (hV : ∀ f : C(X, ℂ), V ∘L continuousL2Mul μ f = continuousL2Mul ν f ∘L V) :
    V = 0 := by
  let oneμ : Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ (1 : C(X, ℂ))
  let y : Lp ℂ 2 ν := V oneμ
  have hy : y = 0 := by
    by_contra hyne
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hyne
    obtain ⟨g : C(X, ℂ), hgclose⟩ :=
      (ContinuousMap.toLp_denseRange ℂ ν (p := 2) ℂ (by norm_num)).exists_dist_lt
        y (show 0 < ‖y‖ / 8 by positivity)
    have hgclose' : ‖y - ContinuousMap.toLp 2 ν ℂ g‖ < ‖y‖ / 8 := by
      simpa [dist_eq_norm] using hgclose
    let C : ℝ := ‖g‖ + 1
    have hC : 0 < C := by positivity
    let a : ℝ := ‖y‖ / (4 * (‖V‖ + 1))
    let b : ℝ := ‖y‖ / (8 * C)
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    let t : Set X := hmut.nullSet
    have ht : MeasurableSet t := hmut.measurableSet_nullSet
    have hmu_t : μ t = 0 := hmut.measure_nullSet
    have hnu_tc : ν tᶜ = 0 := hmut.measure_compl_nullSet
    obtain ⟨U, htU, hUopen, hUmeasure⟩ :=
      Set.exists_isOpen_lt_of_lt (μ := μ) t (ENNReal.ofReal (a ^ 2)) (by
        rw [hmu_t]
        exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos ha))
    obtain ⟨W, htcW, hWopen, hWmeasure⟩ :=
      Set.exists_isOpen_lt_of_lt (μ := ν) tᶜ (ENNReal.ofReal (b ^ 2)) (by
        rw [hnu_tc]
        exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos hb))
    let K : Set X := Uᶜ
    let L : Set X := Wᶜ
    have hKclosed : IsClosed K := hUopen.isClosed_compl
    have hLclosed : IsClosed L := hWopen.isClosed_compl
    have hLK : Disjoint L K := by
      rw [Set.disjoint_left]
      intro x hxL hxK
      have hxt : x ∈ t := by
        by_contra hnot
        exact hxL (htcW hnot)
      exact hxK (htU hxt)
    obtain ⟨q : C(X, ℝ), hqL, hqK, hqIcc⟩ :=
      exists_continuous_zero_one_of_isClosed hLclosed hKclosed hLK
    let φ : C(X, ℂ) :=
      ⟨fun x => (q x : ℂ), Complex.continuous_ofReal.comp q.continuous⟩
    have hφbound : ∀ x, ‖φ x‖ ≤ 1 := by
      intro x
      dsimp [φ]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hqIcc x).1]
      exact (hqIcc x).2
    have hφnorm : ‖φ‖ ≤ 1 := (ContinuousMap.norm_le φ zero_le_one).mpr hφbound
    have hcontract : ∀ u : Lp ℂ 2 ν, ‖continuousL2Mul ν φ u‖ ≤ ‖u‖ := by
      intro u
      calc
        ‖continuousL2Mul ν φ u‖ ≤ ‖continuousL2Mul ν φ‖ * ‖u‖ :=
          (continuousL2Mul ν φ).le_opNorm u
        _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right
          ((norm_continuousL2Mul_le ν φ).trans hφnorm) (norm_nonneg u)
        _ = ‖u‖ := one_mul _
    have hUreal : μ.real U < a ^ 2 := by
      change (μ U).toReal < a ^ 2
      rw [← ENNReal.toReal_ofReal (sq_nonneg a)]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top μ U) ENNReal.ofReal_ne_top).mpr hUmeasure
    have hWreal : ν.real W < b ^ 2 := by
      change (ν W).toReal < b ^ 2
      rw [← ENNReal.toReal_ofReal (sq_nonneg b)]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top ν W) ENNReal.ofReal_ne_top).mpr hWmeasure
    let ψ : C(X, ℂ) := 1 - φ
    have hψbound : ∀ x, ‖ψ x‖ ≤ 1 := by
      intro x
      dsimp [ψ, φ]
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hqIcc x).2)]
      linarith [(hqIcc x).1]
    have hψsupp : Function.support ψ ⊆ U := by
      intro x hx
      by_contra hxU
      have hxK : x ∈ K := hxU
      have hqx : q x = 1 := hqK hxK
      exact hx (by simp [ψ, φ, hqx])
    have hsource : ‖ContinuousMap.toLp 2 μ ℂ ψ‖ < a := by
      have h := norm_continuousMapToLp_lt_mul_of_measureReal_lt_sq
        μ ψ hUopen.measurableSet ha zero_lt_one hUreal hψbound hψsupp
      simpa using h
    let θ : C(X, ℂ) := φ * g
    have hθbound : ∀ x, ‖θ x‖ ≤ C := by
      intro x
      calc
        ‖θ x‖ = ‖φ x‖ * ‖g x‖ := by simp [θ]
        _ ≤ 1 * ‖g‖ :=
          mul_le_mul (hφbound x) (g.norm_coe_le_norm x) (norm_nonneg _) zero_le_one
        _ ≤ C := by dsimp [C]; simp
    have hθsupp : Function.support θ ⊆ W := by
      intro x hx
      by_contra hxW
      have hxL : x ∈ L := hxW
      have hqx : q x = 0 := hqL hxL
      exact hx (by simp [θ, φ, hqx])
    have htargetRaw : ‖ContinuousMap.toLp 2 ν ℂ θ‖ < b * C :=
      norm_continuousMapToLp_lt_mul_of_measureReal_lt_sq
        ν θ hWopen.measurableSet hb hC hWreal hθbound hθsupp
    have hbC : b * C = ‖y‖ / 8 := by
      dsimp [b]
      field_simp [ne_of_gt hC]
    have htarget : ‖ContinuousMap.toLp 2 ν ℂ θ‖ < ‖y‖ / 8 := by
      rwa [hbC] at htargetRaw
    have hφg : continuousL2Mul ν φ (ContinuousMap.toLp 2 ν ℂ g) =
        ContinuousMap.toLp 2 ν ℂ θ := by
      rw [continuousL2Mul_apply_toLp]
    have hφy : ‖continuousL2Mul ν φ y‖ < ‖y‖ / 4 := by
      calc
        ‖continuousL2Mul ν φ y‖ =
            ‖continuousL2Mul ν φ (y - ContinuousMap.toLp 2 ν ℂ g) +
              continuousL2Mul ν φ (ContinuousMap.toLp 2 ν ℂ g)‖ := by
          congr 1
          rw [← map_add]
          congr 1
          abel
        _ ≤ ‖continuousL2Mul ν φ (y - ContinuousMap.toLp 2 ν ℂ g)‖ +
            ‖continuousL2Mul ν φ (ContinuousMap.toLp 2 ν ℂ g)‖ := norm_add_le _ _
        _ < ‖y‖ / 8 + ‖y‖ / 8 := add_lt_add (lt_of_le_of_lt
          (hcontract _) hgclose') (by rw [hφg]; exact htarget)
        _ = ‖y‖ / 4 := by ring
    have hinterψ : V (ContinuousMap.toLp 2 μ ℂ ψ) = continuousL2Mul ν ψ y := by
      have h := DFunLike.congr_fun (hV ψ) oneμ
      simpa [ContinuousLinearMap.comp_apply, oneμ, y] using h
    have hVsource : ‖continuousL2Mul ν ψ y‖ < ‖y‖ / 4 := by
      rw [← hinterψ]
      calc
        ‖V (ContinuousMap.toLp 2 μ ℂ ψ)‖ ≤ ‖V‖ * ‖ContinuousMap.toLp 2 μ ℂ ψ‖ :=
          V.le_opNorm _
        _ ≤ ‖V‖ * a := mul_le_mul_of_nonneg_left hsource.le (norm_nonneg V)
        _ < ‖y‖ / 4 := by
          dsimp [a]
          have hden : 0 < ‖V‖ + 1 := by positivity
          calc
            ‖V‖ * (‖y‖ / (4 * (‖V‖ + 1)))
                < (‖V‖ + 1) * (‖y‖ / (4 * (‖V‖ + 1))) := by
              gcongr
              linarith
            _ = ‖y‖ / 4 := by field_simp [ne_of_gt hden]
    have hdecomp : y = continuousL2Mul ν φ y + continuousL2Mul ν ψ y := by
      rw [← add_apply, ← continuousL2Mul_add]
      have hsum : φ + ψ = 1 := by
        ext x
        simp [ψ]
      rw [hsum, continuousL2Mul_one]
      rfl
    have : ‖y‖ < ‖y‖ := by
      calc
        ‖y‖ = ‖continuousL2Mul ν φ y + continuousL2Mul ν ψ y‖ := congrArg norm hdecomp
        _ ≤ ‖continuousL2Mul ν φ y‖ + ‖continuousL2Mul ν ψ y‖ := norm_add_le _ _
        _ < ‖y‖ / 4 + ‖y‖ / 4 := add_lt_add hφy hVsource
        _ < ‖y‖ := by linarith
    exact (lt_irrefl _ this)
  have hkill : ∀ f : C(X, ℂ), V (ContinuousMap.toLp 2 μ ℂ f) = 0 := by
    intro f
    have h := DFunLike.congr_fun (hV f) oneμ
    simpa [ContinuousLinearMap.comp_apply, oneμ, y, hy] using h
  have hdense := ContinuousMap.toLp_denseRange ℂ μ (p := 2) ℂ (by norm_num)
  have hfun := hdense.equalizer V.continuous (0 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν).continuous (by
    funext f
    simpa using hkill f)
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- Mutually singular finite regular measures give disjoint `C(X)` multiplication
representations. -/
theorem continuousL2Mul_operatorFamiliesDisjoint_of_mutuallySingular
    [NormalSpace X] {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.WeaklyRegular] [ν.WeaklyRegular] (hmut : μ ⟂ₘ ν) :
    OperatorFamiliesDisjoint (continuousL2Mul μ) (continuousL2Mul ν) := by
  constructor
  · intro V hV
    exact continuousL2Mul_intertwiner_eq_zero_of_mutuallySingular hmut V hV
  · intro W hW
    exact continuousL2Mul_intertwiner_eq_zero_of_mutuallySingular hmut.symm W hW

end

end GaloisForLFunctions.HTGeometry
