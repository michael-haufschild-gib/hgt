import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Transport of valued-field topology along a coordinate change

A field equivalence which preserves a valuation pointwise is a uniform equivalence of the
associated valued fields.  Passing to `UniformSpace.Completion.mapEquiv` then transports the
completion along the coordinate change.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

universe u v w

noncomputable section

/-- A valuation-preserving field equivalence is uniformly continuous for the induced valued-field
topologies. -/
theorem uniformContinuous_congr_of_valuation_eq
    {R : Type u} {S : Type v} {Γ₀ : Type w}
    [Field R] [Field S] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (w : Valuation S Γ₀) (e : R ≃+* S)
    (h : ∀ x, w (e x) = v x) :
    UniformContinuous (WithVal.congr v w e) := by
  refine uniformContinuous_of_continuousAt_zero (WithVal.congr v w e).toAddMonoidHom ?_
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero _ _).tendsto_iff
      (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  let δ := WithVal.valueGroupOrderIso₀ w γ.val
  obtain ⟨r, hr⟩ := restrict₀_surjective (.ofClass w) δ
  have hδ : δ ≠ 0 := by
    intro hzero
    have hγ : γ.val = 0 := by
      apply (WithVal.valueGroupOrderIso₀ w).injective
      change (WithVal.valueGroupOrderIso₀ w) γ.val = 0 at hzero
      exact hzero
    exact Units.ne_zero γ hγ
  have hwr : w.restrict r ≠ 0 := by
    change (ValueGroup₀.restrict₀ (.ofClass w)) r ≠ 0
    rw [hr]
    exact hδ
  have hvr : v.restrict (e.symm r) ≠ 0 := by
    intro hzero
    apply hwr
    change (ValueGroup₀.restrict₀ (.ofClass v)) (e.symm r) = 0 at hzero
    change (ValueGroup₀.restrict₀ (.ofClass w)) r = 0
    rw [ValueGroup₀.restrict₀_eq_zero_iff] at hzero ⊢
    calc
      w r = w (e (e.symm r)) := by rw [e.apply_symm_apply]
      _ = v (e.symm r) := h (e.symm r)
      _ = 0 := hzero
  refine ⟨Units.mk0 (Valued.v.restrict (WithVal.toVal v (e.symm r))) ?_, ?_⟩
  · intro hzero
    apply hvr
    have hzero' := congrArg (WithVal.valueGroupOrderIso₀ v) hzero
    change (WithVal.valueGroupOrderIso₀ v)
      ((WithVal.valuation v).restrict (WithVal.toVal v (e.symm r))) =
        (WithVal.valueGroupOrderIso₀ v) 0 at hzero'
    rw [WithVal.valueGroupOrderIso₀_restrict] at hzero'
    simpa using hzero'
  · intro x hx
    change Valued.v.restrict ((WithVal.congr v w e) x) < γ
    have hlt : WithVal.valueGroupOrderIso₀ w
        (Valued.v.restrict ((WithVal.congr v w e) x)) <
        WithVal.valueGroupOrderIso₀ w γ.val := by
      change (WithVal.valueGroupOrderIso₀ w)
        ((WithVal.valuation w).restrict ((WithVal.congr v w e) x)) <
          WithVal.valueGroupOrderIso₀ w γ.val
      rw [WithVal.valueGroupOrderIso₀_restrict]
      change w.restrict (e x.ofVal) < δ
      rw [← hr]
      change w.restrict (e x.ofVal) < w.restrict r
      rw [Valuation.restrict_lt_iff]
      calc
        w (e x.ofVal) = v x.ofVal := h _
        _ < v (e.symm r) := by
          rw [← Valuation.restrict_lt_iff]
          simp only [Set.mem_setOf_eq] at hx
          have hx' := (WithVal.strictMono_valueGroupOrderIso₀ v).lt_iff_lt.mpr hx
          change WithVal.valueGroupOrderIso₀ v ((WithVal.valuation v).restrict x) <
            WithVal.valueGroupOrderIso₀ v
              ((WithVal.valuation v).restrict (WithVal.toVal v (e.symm r))) at hx'
          simpa only [Units.val_mk0, WithVal.valueGroupOrderIso₀_restrict] using hx'
        _ = w (e (e.symm r)) := (h _).symm
        _ = w r := by rw [e.apply_symm_apply]
    exact (WithVal.strictMono_valueGroupOrderIso₀ w).lt_iff_lt.mp hlt

/-- A valuation-preserving field equivalence is a uniform equivalence for the induced valued-field
topologies. -/
def uniformEquiv_congr_of_valuation_eq
    {R : Type u} {S : Type v} {Γ₀ : Type w}
    [Field R] [Field S] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (w : Valuation S Γ₀) (e : R ≃+* S)
    (h : ∀ x, w (e x) = v x) :
    WithVal v ≃ᵤ WithVal w where
  __ := WithVal.congr v w e
  uniformContinuous_toFun := uniformContinuous_congr_of_valuation_eq v w e h
  uniformContinuous_invFun := by
    change UniformContinuous ((WithVal.congr v w e).symm)
    rw [WithVal.congr_symm]
    apply uniformContinuous_congr_of_valuation_eq w v e.symm
    intro y
    calc
      v (e.symm y) = w (e (e.symm y)) := (h _).symm
      _ = w y := by rw [e.apply_symm_apply]

end

end GaloisForLFunctions.HTGeometry.ABHN
