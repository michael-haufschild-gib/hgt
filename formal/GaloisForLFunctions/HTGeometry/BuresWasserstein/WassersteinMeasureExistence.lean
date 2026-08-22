import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinMeasureField
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBanachInvariant

/-!
# Existence of the Wasserstein barycentre of a probability measure

On a Loewner interval the explicit gradient step `X ↦ X - tΦ_μ(X)` of the measure-weighted
Wasserstein field preserves the interval for `0 < t ≤ 2α` and contracts in the Hilbert–Schmidt
metric: strong monotonicity gives `⟨Φ_μ(X) - Φ_μ(Y), X - Y⟩ ≥ κ‖X - Y‖²` with
`κ = α²/(2β³)`, up to a second-order defect that telescoping along an `N`-fold subdivision makes
arbitrarily small, and the field is `L`-Lipschitz with `L = wassLipConst α β`.  Choosing
`t ≤ κ/(2L²)` makes the step a `√(1 - tκ/2)`-contraction, and the invariant-class Banach fixed
point theorem produces the barycentre.  With the uniqueness half this is Theorem 5.1 of
Kim–Mer–Pálfia.
-/

open scoped NNReal Ring BigOperators InnerProductSpace
open Filter Topology MeasureTheory ContinuousLinearMap

attribute [local instance] InnerProductSpace.complexToReal

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A probability space is nonempty. -/
lemma nonempty_of_isProbabilityMeasure [IsProbabilityMeasure μ] : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have huniv : (Set.univ : Set Ω) = ∅ := Set.univ_eq_empty_iff.mpr h
  have h0 : μ Set.univ = 0 := by rw [huniv, measure_empty]
  rw [measure_univ] at h0
  exact one_ne_zero h0

/-- The operator norm of a point of a Loewner interval is at most the upper constant. -/
lemma norm_le_of_Icc {X : E →L[ℂ] E} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E)) : ‖X‖ ≤ β := by
  have h0 : (0 : E →L[ℂ] E) ≤ X :=
    le_trans (smul_nonneg hα.le zero_le_one) hXα
  exact norm_le_of_le_smul_one h0 hβ.le hXβ

/-- **Theorem 5.1 (Kim–Mer–Pálfia), existence.**  A probability measure supported in a Loewner
interval has a Wasserstein barycentre in that interval. -/
theorem exists_wassFieldMeasure_eq_zero [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hAHS : ∀ w w', IsHilbertSchmidt (Av w - Av w'))
    (hint : ∀ X : E →L[ℂ] E, IsSelfAdjoint X → α • (1 : E →L[ℂ] E) ≤ X →
      X ≤ β • (1 : E →L[ℂ] E) → (∀ w, IsHilbertSchmidt (X - Av w)) →
      Integrable (fun w => wassSL (Av w) X) μ) :
    ∃ X : E →L[ℂ] E, IsSelfAdjoint X ∧ α • (1 : E →L[ℂ] E) ≤ X ∧ X ≤ β • (1 : E →L[ℂ] E)
      ∧ (∀ w, IsHilbertSchmidt (X - Av w)) ∧ wassFieldMeasure μ Av X = 0 := by
  classical
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  obtain ⟨w₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ := μ)
  -- the class preserved by the gradient step
  set P : (E →L[ℂ] E) → Prop := fun X => IsSelfAdjoint X ∧ α • (1 : E →L[ℂ] E) ≤ X
    ∧ X ≤ β • (1 : E →L[ℂ] E) ∧ ∀ w, IsHilbertSchmidt (X - Av w) with hPdef
  -- the constants
  set κ : ℝ := α * α / (2 * (β * (β * β))) with hκdef
  set L : ℝ := wassLipConst α β with hLdef
  set C : ℝ := secondOrderConst α β with hCdef
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  have hLpos : 0 < L := by
    rw [hLdef]
    unfold wassLipConst
    have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
    have hai : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
    positivity
  have hCpos : 0 < C := by rw [hCdef]; exact secondOrderConst_pos hα hβ
  set t : ℝ := min (κ / (2 * L ^ 2)) (min (2 * α) κ⁻¹) with htdef
  have htpos : 0 < t := by
    rw [htdef]
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have ht2α : t ≤ 2 * α := le_trans (min_le_right _ _) (min_le_left _ _)
  have htκinv : t ≤ κ⁻¹ := le_trans (min_le_right _ _) (min_le_right _ _)
  have htL : t ≤ κ / (2 * L ^ 2) := min_le_left _ _
  have htκ : t * κ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right htκinv hκpos.le
    rwa [inv_mul_cancel₀ (ne_of_gt hκpos)] at h
  have htsq : t ^ 2 * L ^ 2 ≤ t * κ / 2 := by
    have hLs : (0 : ℝ) < 2 * L ^ 2 := by positivity
    have h' : t * (2 * L ^ 2) ≤ κ := (le_div_iff₀ hLs).mp htL
    nlinarith [htpos.le, h']
  set θ : ℝ := Real.sqrt (1 - t * κ / 2) with hθdef
  have hθarg : (0 : ℝ) ≤ 1 - t * κ / 2 := by linarith
  have hθ0 : 0 ≤ θ := Real.sqrt_nonneg _
  have hθ1 : θ < 1 := by
    rw [hθdef, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    refine Real.sqrt_lt_sqrt hθarg ?_
    rw [Real.sqrt_one]
    nlinarith [htpos, hκpos]
  have hθsq : θ ^ 2 = 1 - t * κ / 2 := Real.sq_sqrt hθarg
  -- the subdivision parameter that kills the second-order defect
  obtain ⟨N, hNge⟩ := exists_nat_ge (C * (2 * β) / (κ / 2) + 1)
  have hCM : (0 : ℝ) ≤ C * (2 * β) / (κ / 2) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; norm_num at hN1
    · exact h
  have hNR : (0 : ℝ) < (N : ℝ) := by linarith
  -- structural facts about the class
  have hPpos : ∀ X : E →L[ℂ] E, P X → IsStrictlyPositive X := fun X hX =>
    isStrictlyPositive_of_smul_one_le hα hX.2.1
  have hPop : ∀ X : E →L[ℂ] E, P X → ∀ w,
      (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ := by
    intro X hX w
    exact wassSL_op hα hβ (hA w) (hPpos X hX) (hAα w) (hAβ w) hX.2.2.1 (hX.2.2.2 w)
  have hPint : ∀ X : E →L[ℂ] E, P X → Integrable (fun w => wassSL (Av w) X) μ := by
    intro X hX
    exact hint X hX.1 hX.2.1 hX.2.2.1 hX.2.2.2
  have hPfieldHS : ∀ X : E →L[ℂ] E, P X → IsHilbertSchmidt (wassFieldMeasure μ Av X) :=
    fun X hX => isHilbertSchmidt_wassFieldMeasure (hPint X hX) (hPop X hX)
  have hPfieldsa : ∀ X : E →L[ℂ] E, P X → IsSelfAdjoint (wassFieldMeasure μ Av X) :=
    fun X hX => isSelfAdjoint_wassFieldMeasure (hPint X hX) (hPop X hX)
  have hPdiffHS : ∀ X Y : E →L[ℂ] E, P X → P Y → IsHilbertSchmidt (X - Y) := by
    intro X Y hX hY
    have h := (hX.2.2.2 w₀).sub (hY.2.2.2 w₀)
    rwa [show (X - Av w₀) - (Y - Av w₀) = X - Y by abel] at h
  have hPnorm : ∀ X Y : E →L[ℂ] E, P X → P Y → ‖X - Y‖ ≤ 2 * β := by
    intro X Y hX hY
    have hx := norm_le_of_Icc hα hβ hX.2.1 hX.2.2.1
    have hy := norm_le_of_Icc hα hβ hY.2.1 hY.2.2.1
    calc ‖X - Y‖ ≤ ‖X‖ + ‖Y‖ := norm_sub_le _ _
      _ ≤ 2 * β := by linarith
  -- the gradient step
  set G : (E →L[ℂ] E) → (E →L[ℂ] E) := fun X => X - t • wassFieldMeasure μ Av X with hGdef
  have hPG : ∀ X : E →L[ℂ] E, P X → P (G X) := by
    intro X hX
    have hopint : Integrable (fun w => (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) μ :=
      integrable_one_sub_gm (hPint X hX) (hPop X hX)
    obtain ⟨hlo, hhi⟩ := sub_smul_wassFieldMeasure_mem_Icc' hα hαβ htpos ht2α
      (hPpos X hX) hA hAα hAβ hX.2.1 hX.2.2.1 hopint
    refine ⟨hX.1.sub (IsSelfAdjoint.smul (star_trivial t) (hPfieldsa X hX)), hlo, hhi, ?_⟩
    intro w
    have hid : G X - Av w = (X - Av w) - t • wassFieldMeasure μ Av X := by
      rw [hGdef]; abel_nf
    rw [hid]
    exact (hX.2.2.2 w).sub ((hPfieldHS X hX).real_smul t)
  have hPHS : ∀ X : E →L[ℂ] E, P X → IsHilbertSchmidt (X - Av w₀) := fun X hX => hX.2.2.2 w₀
  have hPclosed : ∀ (Y : ℕ → (E →L[ℂ] E)) (Z : E →L[ℂ] E), (∀ n, P (Y n)) →
      (∀ n, IsHilbertSchmidt (Y n - Z)) →
      Tendsto (fun n => hsNorm (Y n - Z)) atTop (nhds 0) → P Z := by
    intro Y Z hY hYHS hlim
    have hconv : Tendsto Y atTop (nhds Z) := tendsto_of_hs_limit hYHS hlim
    refine ⟨isSelfAdjoint_of_hs_limit (fun n => (hY n).1) hYHS hlim,
      ge_of_tendsto hconv (Filter.Eventually.of_forall fun n => (hY n).2.1),
      le_of_tendsto hconv (Filter.Eventually.of_forall fun n => (hY n).2.2.1), ?_⟩
    intro w
    have h1 : IsHilbertSchmidt (Z - Y 0) := by
      have h := (hYHS 0).neg
      rwa [show -(Y 0 - Z) = Z - Y 0 by abel] at h
    have h2 := h1.add ((hY 0).2.2.2 w)
    rwa [show (Z - Y 0) + (Y 0 - Av w) = Z - Av w by abel] at h2
  -- the contraction estimate
  have hcontr : ∀ X Y : E →L[ℂ] E, P X → P Y → hsNorm (G X - G Y) ≤ θ * hsNorm (X - Y) := by
    intro X Y hX hY
    have hPXY : IsHilbertSchmidt (X - Y) := hPdiffHS X Y hX hY
    have hstep := hsNormSq_gradientStepMeasure_sub_le (α := α) (β := β) (t := t)
      hα hβ htpos.le hA (hPpos X hX) (hPpos Y hY) hAα hAβ hX.2.1 hX.2.2.1 hY.2.1 hY.2.2.1
      hPXY (hPint X hX) (hPint Y hY) (hPop X hX) (hPop Y hY) hNpos
    have hdefect : C * (‖X - Y‖ / (N : ℝ)) ≤ κ / 2 := by
      have hxy := hPnorm X Y hX hY
      have h1 : ‖X - Y‖ / (N : ℝ) ≤ (2 * β) / (N : ℝ) :=
        div_le_div_of_nonneg_right hxy hNR
      have h2 : C * (‖X - Y‖ / (N : ℝ)) ≤ C * ((2 * β) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hCpos.le
      refine h2.trans ?_
      rw [mul_div_assoc', div_le_iff₀ hNR]
      have h3 : C * (2 * β) / (κ / 2) ≤ (N : ℝ) - 1 := by linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < κ / 2)] at h3
      nlinarith [hκpos, hNR]
    have hfac : 1 - 2 * t * (κ - C * (‖X - Y‖ / (N : ℝ))) + t ^ 2 * L ^ 2 ≤ θ ^ 2 := by
      rw [hθsq]
      nlinarith [htpos.le, hdefect, htsq]
    have hsq : hsNormSq (G X - G Y) ≤ θ ^ 2 * hsNormSq (X - Y) := by
      refine hstep.trans ?_
      exact mul_le_mul_of_nonneg_right hfac (hsNormSq_nonneg _)
    have h4 : hsNorm (G X - G Y) ^ 2 ≤ (θ * hsNorm (X - Y)) ^ 2 := by
      rw [sq_hsNorm, mul_pow, sq_hsNorm]
      exact hsq
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h4
  -- the base point of the iteration
  have hP0 : P (Av w₀) :=
    ⟨(hA w₀).isSelfAdjoint, hAα w₀, hAβ w₀, fun w => hAHS w₀ w⟩
  obtain ⟨X, hXP, -, hfix⟩ :=
    exists_fixedPoint_hs_invariant (G := G) (X₀ := Av w₀) (θ := θ) (P := P)
      hθ0 hθ1 hP0 hPG hPHS hPclosed hcontr
  refine ⟨X, hXP.1, hXP.2.1, hXP.2.2.1, hXP.2.2.2, ?_⟩
  have hzero : t • wassFieldMeasure μ Av X = 0 := by
    have h : X - t • wassFieldMeasure μ Av X = X := hfix
    have h2 : t • wassFieldMeasure μ Av X = X - X := by
      rw [← h]; abel_nf
    rw [h2, sub_self]
  have h3 := congrArg (fun z : E →L[ℂ] E => t⁻¹ • z) hzero
  simpa [inv_smul_smul₀ (ne_of_gt htpos)] using h3

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
