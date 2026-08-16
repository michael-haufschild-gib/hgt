import GaloisForLFunctions.RHTower.HeatEnergyPrincipal
import GaloisForLFunctions.RHTower.JonquiereAllOrder

/-!
# The all-order principal part of the boundary germ

Replacing the constant `ζ(s)` of the first-order Jonquière expansion by the regular polynomial
`∑_{k ≤ K} ζ(s-k)(iθ)^k/k!` gives a principal approximation of the boundary germ with error
`O(|θ|^{K+1})` on both sides of the phase origin.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The `K`-th order principal part of the boundary germ. -/
noncomputable def germPrincipalOrder (s : ℂ) (K : ℕ) (θ : ℝ) : ℂ :=
  jonquiereLeadAt s θ * ((|θ| : ℝ) : ℂ) ^ (s - 1) + jonquiereRegPoly s K θ

theorem germPrincipalOrder_zero (s : ℂ) (θ : ℝ) :
    germPrincipalOrder s 0 θ = germPrincipal s θ := by
  rw [germPrincipalOrder, germPrincipal, jonquiereRegPoly]
  simp [jonquiereRegCoeff]

/-- **The all-order Jonquière error on the window.** -/
theorem norm_phaseGerm_sub_principalOrder_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ) :
    ∀ θ ∈ Ioc (-Real.pi) Real.pi, θ ≠ 0 →
      ‖phaseGerm s θ - germPrincipalOrder s K θ‖
        ≤ jonquiereOrderConst s K * |θ| ^ (K + 1) := by
  intro θ hθ hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hu : (0 : ℝ) < -θ := by linarith
    have hu2 : -θ ≤ Real.pi := by linarith [hθ.1]
    have hgerm : phaseGerm s θ = expZeta ((-((-θ) / (2 * Real.pi)) : ℝ) : UnitAddCircle) s := by
      rw [phaseGerm]; congr 2; ring
    have habs : |θ| = -θ := abs_of_neg hneg
    have hP : germPrincipalOrder s K θ
        = jonquiereLeadNeg s * (((-θ : ℝ)) : ℂ) ^ (s - 1) + jonquiereRegPoly s K (-(-θ)) := by
      rw [germPrincipalOrder, jonquiereLeadAt, if_neg (by linarith : ¬ (0 < θ)), habs, neg_neg]
    rw [hgerm, hP, habs, expZeta_neg_eq_jonquiere_order h0 h1 K hu hu2,
      show jonquiereLeadNeg s * (((-θ : ℝ)) : ℂ) ^ (s - 1)
        + jonquiereRegPoly s K (-(-θ)) + jonquiereRemainderOrderNeg s K (-θ)
        - (jonquiereLeadNeg s * (((-θ : ℝ)) : ℂ) ^ (s - 1) + jonquiereRegPoly s K (-(-θ)))
        = jonquiereRemainderOrderNeg s K (-θ) from by ring]
    exact norm_jonquiereRemainderOrderNeg_le h0 h1 K hu hu2
  · have hu2 : θ ≤ Real.pi := hθ.2
    have habs : |θ| = θ := abs_of_pos hpos
    have hP : germPrincipalOrder s K θ
        = jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + jonquiereRegPoly s K θ := by
      rw [germPrincipalOrder, jonquiereLeadAt, if_pos hpos, habs]
    rw [phaseGerm, hP, habs]
    exact norm_expZeta_sub_jonquiereRegPoly_le h0 h1 K hpos hu2

end RHTower
