import GaloisForLFunctions.HTGeometry.BuresWasserstein.WeightedGeometricMeanSymmetry
import GaloisForLFunctions.HTGeometry.LoewnerRatio

/-!
# The power-mean map contracts the Loewner ratio

The Lim–Pálfia power mean of parameter `t ∈ (0,1]` is the fixed point of

`F(X) = ∑ᵢ wᵢ (X #_t Aᵢ)`.

On a Loewner interval containing the data, `F` maps the interval into itself, and it contracts
the Loewner ratio with factor `1 - t`:

`M(F X / F Y) ≤ M(X / Y)^{1-t}`,

because `X ≤ σ Y` gives `X #_t Aᵢ ≤ (σ Y) #_t Aᵢ = σ^{1-t}(Y #_t Aᵢ)` by monotonicity in the
first argument and left homogeneity.  In the Thompson metric this is the statement that `F` is a
`(1-t)`-contraction.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

/-- The weighted geometric mean of an element with itself. -/
@[simp] theorem wgm_self {t : ℝ} {c : A} (hc : IsStrictlyPositive c) : wgm t c c = c := by
  rw [wgm_def, rpow_neg_half_mul_self_mul_rpow_neg_half hc, CFC.one_rpow,
    mul_one, rpow_half_mul_rpow_half hc]

/-- The **power-mean map** `F(X) = ∑ᵢ wᵢ (X #_t Aᵢ)`. -/
def powerMeanMap (s : Finset ι) (w : ι → ℝ) (Av : ι → A) (t : ℝ) (X : A) : A :=
  ∑ i ∈ s, w i • wgm t X (Av i)

/-- The power-mean map preserves a Loewner interval containing the data. -/
theorem powerMeanMap_mem_Icc {t α β : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hα : 0 < α) (hβ : 0 < β) (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A))
    {X : A} (hX : IsStrictlyPositive X)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A)) :
    α • (1 : A) ≤ powerMeanMap s w Av t X ∧ powerMeanMap s w Av t X ≤ β • (1 : A) := by
  have hαpos : IsStrictlyPositive (α • (1 : A)) :=
    IsStrictlyPositive.smul hα isStrictlyPositive_one
  have hβpos : IsStrictlyPositive (β • (1 : A)) :=
    IsStrictlyPositive.smul hβ isStrictlyPositive_one
  constructor
  · rw [show (α • (1 : A)) = ∑ i ∈ s, w i • (α • (1 : A)) by
      rw [← Finset.sum_smul, hwsum, one_smul]]
    refine Finset.sum_le_sum fun i hi => ?_
    refine smul_le_smul_of_nonneg_left ?_ (hw i hi)
    rw [← wgm_self (t := t) hαpos]
    exact wgm_mono ht hαpos hX (hA i hi) hXα (hAα i hi)
  · unfold powerMeanMap
    rw [show (β • (1 : A)) = ∑ i ∈ s, w i • (β • (1 : A)) by
      rw [← Finset.sum_smul, hwsum, one_smul]]
    refine Finset.sum_le_sum fun i hi => ?_
    refine smul_le_smul_of_nonneg_left ?_ (hw i hi)
    rw [← wgm_self (t := t) hβpos]
    exact wgm_mono ht hX hβpos hβpos hXβ (hAβ i hi)

/-- The power-mean map turns a scalar Loewner bound into a `(1-t)`-scaled one. -/
theorem powerMeanMap_le_of_le {t σ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hσ : 0 < σ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    {X Y : A} (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (h : X ≤ σ • Y) :
    powerMeanMap s w Av t X ≤ (σ ^ (1 - t)) • powerMeanMap s w Av t Y := by
  unfold powerMeanMap
  rw [Finset.smul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hstep : wgm t X (Av i) ≤ wgm t (σ • Y) (Av i) :=
    wgm_mono_left ⟨ht, ht1⟩ hX (IsStrictlyPositive.smul hσ hY) (hA i hi) h
  have hhom : wgm t (σ • Y) (Av i) = (σ ^ (1 - t)) • wgm t Y (Av i) :=
    wgm_smul_left hσ ht ht1 hY (hA i hi)
  rw [hhom] at hstep
  have hfin := smul_le_smul_of_nonneg_left hstep (hw i hi)
  rw [smul_comm] at hfin
  exact hfin

/-- **The power-mean map is a `(1-t)`-contraction for the Loewner ratio.** -/
theorem loewnerRatio_powerMeanMap_le [Nontrivial A] {t α β : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (_hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (_hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (_hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A))
    {X Y : A} (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A))
    (hYα : α • (1 : A) ≤ Y) (hYβ : Y ≤ β • (1 : A)) :
    loewnerRatio (powerMeanMap s w Av t X) (powerMeanMap s w Av t Y)
      ≤ (loewnerRatio X Y) ^ (1 - t) := by
  have hM := le_loewnerRatio_smul hα hβ hY.nonneg hXβ hYα
  have hMpos : 0 < loewnerRatio X Y :=
    loewnerRatio_pos hα hβ hY.nonneg hXβ hYα hXα hYβ
  have hstep := powerMeanMap_le_of_le (s := s) (w := w) (Av := Av) (le_of_lt ht) ht1 hMpos
    hw hA hX hY hM
  exact loewnerRatio_le (by positivity) hstep

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
