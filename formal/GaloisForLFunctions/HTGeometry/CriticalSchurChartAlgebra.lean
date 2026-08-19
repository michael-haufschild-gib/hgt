import GaloisForLFunctions.HTGeometry.CriticalSchurChartInclusion

/-!
# The Schur coordinate ring inside the chart algebra

Every Schur coordinate is a polynomial in the horizon coordinates, so evaluation of the Schur
coordinate ring lands in the chart algebra.  Together with the inclusion of the chart algebra in
the Schur valuation ring this puts

```text
Schur coordinate ring  ⊆  chart algebra  ⊆  Schur valuation ring
```

and the Schur valuation ring is the localization of the first, so it is also the localization of
the middle one.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem algebraMap_ground_mem_chartAlgebra (a : K) :
    algebraMap K (criticalSourceField K m n) a ∈
      criticalSourceChartAlgebra K (m := m) (n := n) := by
  have h : algebraMap K (criticalSourceField K m n) a
      = algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)
        (algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n)
          (MvPolynomial.C a)) := by
    rw [← IsScalarTower.algebraMap_apply]
    show _ = algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
      (algebraMap K (criticalObservationRing K m n) a)
    rw [← IsScalarTower.algebraMap_apply]
  rw [h]
  exact Subalgebra.algebraMap_mem _ _

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem adjoinGround_le_chartAlgebra :
    ∀ x ∈ Algebra.adjoin K (criticalSourceCoordinateSet K m n),
      x ∈ criticalSourceChartAlgebra K (m := m) (n := n) := by
  intro x hx
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
  · intro y hy; exact Algebra.subset_adjoin hy
  · intro a; exact algebraMap_ground_mem_chartAlgebra K a
  · intro y z _ _ hy hz; exact Subalgebra.add_mem _ hy hz
  · intro y z _ _ hy hz; exact Subalgebra.mul_mem _ hy hz

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- **The Schur coordinate ring lands in the chart algebra.** -/
theorem schurCoordinateAeval_mem_chartAlgebra (p : criticalSchurSourceRing K m n) :
    MvPolynomial.aeval
        (criticalSourceSchurCoordinates K (Fact.out : 0 < m) (Fact.out : 0 < n)) p ∈
      criticalSourceChartAlgebra K (m := m) (n := n) := by
  have hcoord : ∀ i, criticalSourceSchurCoordinates K (Fact.out : 0 < m) (Fact.out : 0 < n) i ∈
      criticalSourceChartAlgebra K (m := m) (n := n) :=
    fun i => adjoinGround_le_chartAlgebra K _
      (criticalSourceSchurCoordinates_mem_adjoin K Fact.out Fact.out i)
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.aeval_C]
      exact algebraMap_ground_mem_chartAlgebra K a
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p s hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact Subalgebra.mul_mem _ hp (hcoord s)

/-- Inclusion of the chart algebra into the Schur valuation ring. -/
noncomputable def chartAlgebraToSchur :
    criticalSourceChartAlgebra K (m := m) (n := n) →+*
      criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) where
  toFun t := ⟨(t : criticalSourceField K m n),
    criticalSourceChartAlgebra_le_schur K (Fact.out : 1 < m) (Fact.out : 1 < n) t.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance chartAlgebraSchurAlgebra :
    Algebra (criticalSourceChartAlgebra K (m := m) (n := n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  (chartAlgebraToSchur K).toAlgebra

theorem chartAlgebraToSchur_injective :
    Function.Injective (chartAlgebraToSchur K (m := m) (n := n)) := by
  intro x y hxy
  refine Subtype.ext ?_
  exact congrArg (Subtype.val (p := fun z : criticalSourceField K m n =>
    z ∈ criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))) hxy

end

end GaloisForLFunctions.HTGeometry
