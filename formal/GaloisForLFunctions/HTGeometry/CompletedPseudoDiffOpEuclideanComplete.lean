import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpEuclideanMetricSpace

/-!
# Completeness of the Euclidean projective lattice-vertex metric

Centered integral coweights give a uniform separation: two vertices at Euclidean distance below
`1/2` are equal.  Every Cauchy filter is therefore eventually a singleton.  This proves literal
completeness of the vertex metric, including ranks zero and one.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]
variable {r : ℕ}

theorem abs_apply_le_euclideanNorm (v : Fin r → ℝ) (i : Fin r) :
    |v i| ≤ ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

theorem differentialVariationalProjectiveEuclideanVertexDistance_lt_half_eq
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (hxy : differentialVariationalProjectiveEuclideanVertexDistance x y < 1 / 2) :
    x = y := by
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro L M hLM
  by_cases hr : r = 0
  · subst r
    apply (differentialVariationalProjectiveEuclideanVertexDistance_eq_zero_iff
      (Quotient.mk _ L) (Quotient.mk _ M)).1
    rw [differentialVariationalProjectiveEuclideanVertexDistance]
    rw [EuclideanSpace.norm_eq]
    simp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let m := completedPseudoDiffOpDominantRelativePosition L M
    let c := centeredCoweight m
    have hcoord (i : Fin r) : |c i| < 1 / 2 := by
      calc
        |c i| ≤ ‖WithLp.toLp 2 c‖ := abs_apply_le_euclideanNorm c i
        _ < 1 / 2 := hLM
    have hmconst : m = fun _ => m ⟨0, hrpos⟩ := by
      funext i
      have hdiff : |((m i - m ⟨0, hrpos⟩ : ℤ) : ℝ)| < 1 := by
        have heq : ((m i - m ⟨0, hrpos⟩ : ℤ) : ℝ) = c i - c ⟨0, hrpos⟩ := by
          simp [c, centeredCoweight]
        rw [heq]
        calc
          |c i - c ⟨0, hrpos⟩| ≤ |c i| + |c ⟨0, hrpos⟩| := abs_sub _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add (hcoord i) (hcoord ⟨0, hrpos⟩)
          _ = 1 := by ring
      have hdiffInt : |m i - m ⟨0, hrpos⟩| < (1 : ℤ) := by
        exact_mod_cast hdiff
      have hbounds := (abs_lt.mp hdiffInt)
      omega
    apply (differentialVariationalProjectiveEuclideanVertexDistance_eq_zero_iff
      (Quotient.mk _ L) (Quotient.mk _ M)).1
    change ‖WithLp.toLp 2 (centeredCoweight m)‖ = 0
    rw [hmconst]
    have hz : centeredCoweight (fun _ : Fin r => m ⟨0, hrpos⟩) = 0 := by
      exact (centeredCoweight_eq_zero_iff_exists_const _).2 ⟨m ⟨0, hrpos⟩, rfl⟩
    rw [hz, WithLp.toLp_zero, norm_zero]

theorem differentialVariationalProjectiveEuclideanCompleteSpace :
    @CompleteSpace
      (DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
      differentialVariationalProjectiveEuclideanMetricSpace.toUniformSpace := by
  letI : MetricSpace (DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :=
    differentialVariationalProjectiveEuclideanMetricSpace
  exact
    { complete := by
        intro f hf
        have hf' := Metric.cauchy_iff.mp hf
        obtain ⟨s, hs, hdiam⟩ := hf'.2 (1 / 2) (by positivity)
        letI : f.NeBot := hf'.1
        obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hs
        refine ⟨x, le_trans ?_ (pure_le_nhds x)⟩
        rw [Filter.le_pure_iff]
        apply Filter.mem_of_superset hs
        intro y hy
        exact differentialVariationalProjectiveEuclideanVertexDistance_lt_half_eq y x
          (hdiam y hy x hx) }

end

end GaloisForLFunctions.HTGeometry.DiffOp
