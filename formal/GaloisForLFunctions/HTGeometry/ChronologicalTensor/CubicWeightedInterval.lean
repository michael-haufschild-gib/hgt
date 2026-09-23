import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicWeightedRecovery

/-!
# The intrinsic interval weight of chronological recovery

The edge ratio c/2-c^(2 : ℕ)/4 maps [0,1] bijectively to [0,1/4], with inverse
1-sqrt(1-4r). Both inverse identities and interval bounds are proved,
including the endpoints. The actual recovery-error set is therefore
exactly the set of weighted polynomial norms with this weight, raised
to the physical homogeneous degree, and one fixed coefficient.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicRadialWeight (r : ℝ) : ℝ := 1-Real.sqrt (1-4*r)

theorem cubicEdgeRatio_bounds (c : Icc (0:ℝ) 1) :
    cubicEdgeRatio c.val ∈ Icc (0:ℝ) (1/4) := by
  have hc0 := c.property.1
  have hc1 := c.property.2
  have hc2 := sq_nonneg (c.val-1)
  unfold cubicEdgeRatio
  constructor <;> nlinarith

theorem cubicRadialWeight_bounds (r : Icc (0:ℝ) (1/4)) :
    cubicRadialWeight r.val ∈ Icc (0:ℝ) 1 := by
  have hr0 := r.property.1
  have hr1 := r.property.2
  have hs0 := Real.sqrt_nonneg (1-4*r.val)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1-4*r.val by linarith)
  unfold cubicRadialWeight
  constructor <;> nlinarith

theorem cubicRadialWeight_edgeRatio (c : Icc (0:ℝ) 1) :
    cubicRadialWeight (cubicEdgeRatio c.val)=c.val := by
  have hid : 1-4*cubicEdgeRatio c.val=(1-c.val)^(2 : ℕ) := by unfold cubicEdgeRatio; ring
  unfold cubicRadialWeight
  rw [hid,Real.sqrt_sq_eq_abs,abs_of_nonneg (sub_nonneg.mpr c.property.2)]
  ring

theorem cubicEdgeRatio_radialWeight (r : Icc (0:ℝ) (1/4)) :
    cubicEdgeRatio (cubicRadialWeight r.val)=r.val := by
  have hs2 := Real.sq_sqrt (show 0 ≤ 1-4*r.val by linarith [r.property.2])
  unfold cubicEdgeRatio cubicRadialWeight
  nlinarith

def cubicWeightedIntervalNorm (k : ℕ) (R : Polynomial ℝ) : ℝ :=
  sSup ((fun r : ℝ => cubicRadialWeight r^k*|R.eval r|) '' Icc 0 (1/4))

theorem cubicWeightedIntervalNorm_changeVariable (k : ℕ) (R : Polynomial ℝ) :
    sSup ((fun c : ℝ => c^k*|R.eval (cubicEdgeRatio c)|) '' Icc 0 1)=
      cubicWeightedIntervalNorm k R := by
  unfold cubicWeightedIntervalNorm
  congr 1
  ext y
  constructor
  · rintro ⟨c,hc,rfl⟩
    refine ⟨cubicEdgeRatio c,cubicEdgeRatio_bounds ⟨c,hc⟩,?_⟩
    change cubicRadialWeight (cubicEdgeRatio c)^k*|R.eval (cubicEdgeRatio c)|=_
    rw [cubicRadialWeight_edgeRatio ⟨c,hc⟩]
  · rintro ⟨r,hr,rfl⟩
    refine ⟨cubicRadialWeight r,cubicRadialWeight_bounds ⟨r,hr⟩,?_⟩
    change cubicRadialWeight r^k*|R.eval (cubicEdgeRatio (cubicRadialWeight r))|=_
    rw [cubicEdgeRatio_radialWeight ⟨r,hr⟩]

theorem cubicHomogeneousRecoveryErrors_interval (k : ℕ) :
    cubicHomogeneousRecoveryErrors k=
      cubicWeightedIntervalNorm (k+1) ''
        {R : Polynomial ℝ | R.natDegree ≤ k+1 ∧ R.coeff k=1} := by
  rw [cubicHomogeneousRecoveryErrors_polynomial]
  have h : (fun R : Polynomial ℝ =>
      sSup ((fun c : ℝ => c^(k+1)*|R.eval (cubicEdgeRatio c)|) '' Icc 0 1))=
      cubicWeightedIntervalNorm (k+1) := by
    funext R
    exact cubicWeightedIntervalNorm_changeVariable (k+1) R
  rw [h]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
