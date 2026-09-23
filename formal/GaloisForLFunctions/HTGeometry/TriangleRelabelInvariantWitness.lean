import GaloisForLFunctions.HTGeometry.NoOutsideQuadraticWitnessDescent

/-!
# Relabel-invariant reporters exist, and the descent applies to them

The quadratic-witness descent is stated for a scalar reporter blind to every relabeling of the
unlabeled triangle, and nothing produced such a reporter.  They are plentiful: constants, the
trace, the determinant, and every entrywise sum `∑_{i,j} φ (c i j)` are invariant, and invariance is
closed under sums, products and post-composition.

The entrywise square sum is an invariant reporter whose orientation restriction is entire and
non-constant, so the descent theorem applies to it and returns an explicit entire square factor.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Producers -/

/-- Constant reporters are relabel invariant. -/
theorem triangleRelabelInvariantReporter_const (k : ℂ) :
    TriangleRelabelInvariantReporter (fun _ => k) :=
  fun _ _ => rfl

/-- Every entrywise sum is relabel invariant: relabeling permutes the index pairs. -/
theorem triangleRelabelInvariantReporter_sumEntries (φ : ℂ → ℂ) :
    TriangleRelabelInvariantReporter (fun c => ∑ i, ∑ j, φ (c i j)) := by
  intro σ c
  show (∑ i, ∑ j, φ (c (σ.symm i) (σ.symm j))) = ∑ i, ∑ j, φ (c i j)
  calc (∑ i, ∑ j, φ (c (σ.symm i) (σ.symm j)))
      = ∑ i, ∑ j, φ (c (σ.symm i) j) :=
        Finset.sum_congr rfl fun i _ =>
          Equiv.sum_comp σ.symm (fun j => φ (c (σ.symm i) j))
    _ = ∑ i, ∑ j, φ (c i j) :=
        Equiv.sum_comp σ.symm (fun i => ∑ j, φ (c i j))

/-- The trace is relabel invariant. -/
theorem triangleRelabelInvariantReporter_trace :
    TriangleRelabelInvariantReporter Matrix.trace := by
  intro σ c
  show (∑ i, c (σ.symm i) (σ.symm i)) = ∑ i, c i i
  exact Equiv.sum_comp σ.symm (fun i => c i i)

/-- The determinant is relabel invariant: relabeling is a symmetric submatrix reindexing. -/
theorem triangleRelabelInvariantReporter_det :
    TriangleRelabelInvariantReporter Matrix.det := by
  intro σ c
  exact Matrix.det_submatrix_equiv_self σ.symm c

/-! ## Closure -/

theorem TriangleRelabelInvariantReporter.add {F G : Matrix (Fin 3) (Fin 3) ℂ → ℂ}
    (hF : TriangleRelabelInvariantReporter F) (hG : TriangleRelabelInvariantReporter G) :
    TriangleRelabelInvariantReporter (fun c => F c + G c) := by
  intro σ c
  show F (triangleRelabel σ c) + G (triangleRelabel σ c) = F c + G c
  rw [hF σ c, hG σ c]

theorem TriangleRelabelInvariantReporter.mul {F G : Matrix (Fin 3) (Fin 3) ℂ → ℂ}
    (hF : TriangleRelabelInvariantReporter F) (hG : TriangleRelabelInvariantReporter G) :
    TriangleRelabelInvariantReporter (fun c => F c * G c) := by
  intro σ c
  show F (triangleRelabel σ c) * G (triangleRelabel σ c) = F c * G c
  rw [hF σ c, hG σ c]

theorem TriangleRelabelInvariantReporter.comp {F : Matrix (Fin 3) (Fin 3) ℂ → ℂ}
    (hF : TriangleRelabelInvariantReporter F) (g : ℂ → ℂ) :
    TriangleRelabelInvariantReporter (fun c => g (F c)) := by
  intro σ c
  show g (F (triangleRelabel σ c)) = g (F c)
  rw [hF σ c]

/-! ## An entire invariant reporter, and the descent applied to it -/

/-- The entrywise square sum: an invariant reporter with a non-constant orientation
restriction. -/
def triangleSquareSumReport (c : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  ∑ i, ∑ j, (c i j) ^ (2 : ℕ)

theorem triangleRelabelInvariantReporter_squareSum :
    TriangleRelabelInvariantReporter triangleSquareSumReport :=
  triangleRelabelInvariantReporter_sumEntries (fun z => z ^ (2 : ℕ))

theorem differentiable_triangleResidualReport_squareSum :
    Differentiable ℂ (triangleResidualReport triangleSquareSumReport) := by
  have hfun : triangleResidualReport triangleSquareSumReport =
      fun a : ℂ => ∑ i, ∑ j, (a * triangleOrientationCycle ℂ i j) ^ (2 : ℕ) := by
    funext a
    simp [triangleResidualReport, triangleSquareSumReport, triangleOrientationResidual]
  rw [hfun]
  fun_prop

/-- **The descent is non-vacuous.**  The entrywise square sum is a relabel-invariant reporter with
entire orientation restriction, so it factors through the orientation square. -/
theorem exists_entire_squareFactor_triangleSquareSumReport :
    ∃ Q : ℂ → ℂ,
      Differentiable ℂ Q ∧
        ∀ a : ℂ, Q (triangleOrientationQuadraticWitness a) =
          triangleResidualReport triangleSquareSumReport a :=
  triangleResidualReport_exists_entire_squareFactor triangleSquareSumReport
    triangleRelabelInvariantReporter_squareSum
    differentiable_triangleResidualReport_squareSum

end

end GaloisForLFunctions.HTGeometry
