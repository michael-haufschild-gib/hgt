import GaloisForLFunctions.RHTower.Deninger.DeningerLpIndicator
import GaloisForLFunctions.RHTower.Deninger.DeningerAdelicKummerGelfandTriple

/-!
# Restriction on the mixed `L¹/L²` space

Applying the indicator operator in both components preserves the mixed carrier, because the two
components of a mixed element agree almost everywhere and are hit by the same indicator.  This
gives a bounded operator of norm at most one on the mixed space, and the operators of a set and
its complement decompose the identity there.

That is the completed form of the split divisor row: restriction is bounded, extension by zero is
its complement, and the two together split the identity.

* `deningerMixedIndicator` is the operator.
* `deningerMixedIndicator_add_compl` is the decomposition of the identity.
-/

namespace RHTower

open MeasureTheory

open scoped ENNReal

section MixedIndicator

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {s : Set Y}

/-- The indicator operator applied in both components of the ambient mixed product. -/
noncomputable def deningerMixedIndicatorAmb (hs : MeasurableSet s) :
    WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ) →L[ℝ] WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ) :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        WithLp.toLp 1 (deningerLpIndicator hs x.fst, deningerLpIndicator hs x.snd)
      map_add' := fun x y => by
        refine WithLp.ofLp_injective 1 ?_
        exact Prod.ext (map_add _ _ _) (map_add _ _ _)
      map_smul' := fun c x => by
        refine WithLp.ofLp_injective 1 ?_
        exact Prod.ext (map_smul _ _ _) (map_smul _ _ _) } 1 (by
      intro x
      rw [one_mul, WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1]
      exact add_le_add (deningerLpIndicator_norm_le hs x.fst)
        (deningerLpIndicator_norm_le hs x.snd))

@[simp] theorem deningerMixedIndicatorAmb_fst (hs : MeasurableSet s)
    (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)) :
    (deningerMixedIndicatorAmb hs x).fst = deningerLpIndicator hs x.fst := rfl

@[simp] theorem deningerMixedIndicatorAmb_snd (hs : MeasurableSet s)
    (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)) :
    (deningerMixedIndicatorAmb hs x).snd = deningerLpIndicator hs x.snd := rfl

/-- The mixed carrier is stable under the indicator operator. -/
theorem deningerMixedIndicatorAmb_mem (hs : MeasurableSet s)
    {x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)} (hx : x ∈ deningerMixedL12 μ) :
    deningerMixedIndicatorAmb hs x ∈ deningerMixedL12 μ := by
  have hxe : (x.fst : Y → ℝ) =ᵐ[μ] (x.snd : Y → ℝ) := hx
  show ((deningerLpIndicator hs x.fst : Lp ℝ 1 μ) : Y → ℝ)
      =ᵐ[μ] ((deningerLpIndicator hs x.snd : Lp ℝ 2 μ) : Y → ℝ)
  filter_upwards [deningerLpIndicatorFun_coeFn hs x.fst,
    deningerLpIndicatorFun_coeFn hs x.snd, hxe] with t h1 h2 h3
  simp only [deningerLpIndicator_apply]
  rw [h1, h2]
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, h3]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]

/-- **Restriction on the mixed space.**  A bounded operator of norm at most one. -/
noncomputable def deningerMixedIndicator (hs : MeasurableSet s) :
    DeningerMixed μ →L[ℝ] DeningerMixed μ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨deningerMixedIndicatorAmb hs x, deningerMixedIndicatorAmb_mem hs x.2⟩
      map_add' := fun x y => Subtype.ext (map_add (deningerMixedIndicatorAmb hs) _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (deningerMixedIndicatorAmb hs) _ _) } 1 (by
      intro x
      rw [one_mul]
      show ‖deningerMixedIndicatorAmb hs (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ))‖
          ≤ ‖(x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ))‖
      rw [WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1]
      exact add_le_add (deningerLpIndicator_norm_le hs _) (deningerLpIndicator_norm_le hs _))

@[simp] theorem deningerMixedIndicator_coe (hs : MeasurableSet s) (x : DeningerMixed μ) :
    ((deningerMixedIndicator hs x : DeningerMixed μ) : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ))
      = deningerMixedIndicatorAmb hs x := rfl

/-- **The completed split.**  Restriction to a set and to its complement decompose the identity
of the mixed space. -/
theorem deningerMixedIndicator_add_compl (hs : MeasurableSet s) (x : DeningerMixed μ) :
    deningerMixedIndicator hs x + deningerMixedIndicator hs.compl x = x := by
  refine Subtype.ext ?_
  refine WithLp.ofLp_injective 1 ?_
  refine Prod.ext ?_ ?_
  · exact deningerLpIndicator_add_compl hs _
  · exact deningerLpIndicator_add_compl hs _

/-- Restriction on the mixed space is idempotent. -/
theorem deningerMixedIndicator_idem (hs : MeasurableSet s) (x : DeningerMixed μ) :
    deningerMixedIndicator hs (deningerMixedIndicator hs x) = deningerMixedIndicator hs x := by
  refine Subtype.ext ?_
  refine WithLp.ofLp_injective 1 ?_
  exact Prod.ext (deningerLpIndicatorFun_idem hs _) (deningerLpIndicatorFun_idem hs _)

/-- Restricting to a set and then to its complement is zero. -/
theorem deningerMixedIndicator_compl_comp (hs : MeasurableSet s) (x : DeningerMixed μ) :
    deningerMixedIndicator hs.compl (deningerMixedIndicator hs x) = 0 := by
  refine Subtype.ext ?_
  refine WithLp.ofLp_injective 1 ?_
  exact Prod.ext (deningerLpIndicatorFun_compl_comp hs _)
    (deningerLpIndicatorFun_compl_comp hs _)

/-- **The completed split row.**  The image of the restriction to a set is exactly the kernel of
the restriction to its complement: `ker ∂ = im ι` after completion. -/
theorem deningerMixedIndicator_range_eq_ker_compl (hs : MeasurableSet s) :
    LinearMap.range (deningerMixedIndicator (μ := μ) hs).toLinearMap
      = LinearMap.ker (deningerMixedIndicator (μ := μ) hs.compl).toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact deningerMixedIndicator_compl_comp hs y
  · intro hx
    refine ⟨x, ?_⟩
    have h := deningerMixedIndicator_add_compl hs x
    rw [show deningerMixedIndicator hs.compl x = 0 from hx, add_zero] at h
    exact h

/-- The kernel of the completed restriction is closed. -/
theorem deningerMixedIndicator_isClosed_ker (hs : MeasurableSet s) :
    IsClosed {x : DeningerMixed μ | deningerMixedIndicator hs x = 0} :=
  (deningerMixedIndicator hs).isClosed_ker

end MixedIndicator

end RHTower
