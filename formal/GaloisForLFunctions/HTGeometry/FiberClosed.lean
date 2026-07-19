import GaloisForLFunctions.HTGeometry.CountableWeightedDirac

/-!
# The denominator fibers are closed

`ClassicalNevanlinnaExtremalFamily` carries continuity of `B` and `D`, so each denominator fiber is
the preimage of `{0}` under a continuous function and is therefore closed — hence measurable.

Link 121 had to avoid measurability, proving leaf distinctness with subadditivity and monotonicity
alone because the structure did not obviously supply it.  It does supply it, through the continuity
fields, and the sharper statements measurability permits are available after all.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

open GaloisForLFunctions.HTGeometry

/-- A denominator fiber of a matrix with continuous entries is closed. -/
theorem isClosed_finiteDenominatorFiber_of_continuous (W : ClassicalNevanlinnaMatrixData ℝ)
    (hB : Continuous W.B) (hD : Continuous W.D) (tau : ℝ) :
    IsClosed (W.finiteDenominatorFiber tau) := by
  have hset : W.finiteDenominatorFiber tau = (fun x => W.B x * tau - W.D x) ⁻¹' {0} := rfl
  rw [hset]
  exact IsClosed.preimage (by fun_prop) isClosed_singleton

theorem measurableSet_finiteDenominatorFiber (W : ClassicalNevanlinnaMatrixData ℝ)
    (hB : Continuous W.B) (hD : Continuous W.D) (tau : ℝ) :
    MeasurableSet (W.finiteDenominatorFiber tau) :=
  (isClosed_finiteDenominatorFiber_of_continuous W hB hD tau).measurableSet

/-- The fiber at infinity is closed as well. -/
theorem isClosed_infinityDenominatorFiber_of_continuous (W : ClassicalNevanlinnaMatrixData ℝ)
    (hB : Continuous W.B) : IsClosed W.infinityDenominatorFiber := by
  have hset : W.infinityDenominatorFiber = W.B ⁻¹' {0} := rfl
  rw [hset]
  exact IsClosed.preimage hB isClosed_singleton

variable {s : ℕ → ℝ}

/-- **A leaf's fiber is measurable**, from the family's continuity fields. -/
theorem measurableSet_leaf_fiber (F : ClassicalNevanlinnaExtremalFamily s) (tau : ℝ) :
    MeasurableSet (F.matrix.finiteDenominatorFiber tau) :=
  measurableSet_finiteDenominatorFiber F.matrix F.continuous_B F.continuous_D tau

/-- **A leaf gives its fiber mass exactly one.**  With measurability available, the subadditivity
bound of link 121 sharpens to an equality. -/
theorem leaf_fiber_measure_eq_one (F : ClassicalNevanlinnaExtremalFamily s) (tau : ℝ) :
    (F.leaf (tau : OnePoint ℝ) : Measure ℝ) (F.matrix.finiteDenominatorFiber tau) = 1 := by
  have hmeas := measurableSet_leaf_fiber F tau
  have hcompl := F.finite_carried tau
  have hsum := measure_add_measure_compl (μ := (F.leaf (tau : OnePoint ℝ) : Measure ℝ)) hmeas
  rw [hcompl, add_zero, measure_univ] at hsum
  exact hsum

/-- **Leaves at distinct parameters are mutually singular.**  Each is carried by its own fiber, and
the fibers are disjoint measurable sets — a strictly stronger separation than distinctness. -/
theorem mutuallySingular_leaf (F : ClassicalNevanlinnaExtremalFamily s) {t1 t2 : ℝ}
    (hne : t1 ≠ t2) :
    (F.leaf (t1 : OnePoint ℝ) : Measure ℝ).MutuallySingular
      (F.leaf (t2 : OnePoint ℝ) : Measure ℝ) := by
  refine ⟨F.matrix.finiteDenominatorFiber t2, measurableSet_leaf_fiber F t2, ?_,
    F.finite_carried t2⟩
  have hsub : F.matrix.finiteDenominatorFiber t2 ⊆ (F.matrix.finiteDenominatorFiber t1)ᶜ :=
    fun x hx => Set.disjoint_right.mp (disjoint_finiteDenominatorFiber F.matrix hne) hx
  have hle := measure_mono (μ := (F.leaf (t1 : OnePoint ℝ) : Measure ℝ)) hsub
  rw [F.finite_carried t1] at hle
  exact nonpos_iff_eq_zero.mp hle

/-- The leaf is concentrated on its fiber: restricting changes nothing. -/
theorem leaf_restrict_fiber (F : ClassicalNevanlinnaExtremalFamily s) (tau : ℝ) :
    (F.leaf (tau : OnePoint ℝ) : Measure ℝ).restrict
        (F.matrix.finiteDenominatorFiber tau)
      = (F.leaf (tau : OnePoint ℝ) : Measure ℝ) := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  simpa using F.finite_carried tau

end HTGeometry
