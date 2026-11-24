import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.ScalarError

/-! # Observation length and angular accuracy for relative scalar mass -/
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- If the angular and temporal boundaries cost at most a share v each,
the scalar Haar mass is recovered within relative error 4v. -/
theorem scalar_accuracy_with_margin {N : ℕ} (H : selfAdjoint (Register N))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {δ G x v : ℝ}
    (hx : 0<x) (hδ : 0≤δ) (hG : 0<G) (hv : 0<v) (hv' : v≤1/2)
    (hc : ∀ u : ℝ, ∃ t ∈ Icc u (u+G), t ∈ visitSet H 0 δ)
    (hcost : ((2^N:ℕ):ℝ)*δ≤v*x) (hhi : x+δ≤1/2) (a T : ℝ) (ht : G≤v*T) :
    |visitFraction H 0 (zeroGateArcTolerance x) a (a+T)/zeroGateArcDensity (2^N) x-1|≤4*v := by
  have h₁ : v<1 := hv'.trans_lt (by norm_num)
  have hT : 0<T := pos_of_mul_pos_right (hG.trans_le ht) hv.le
  have hGT : G<T := ht.trans_lt (mul_lt_of_lt_one_left hT h₁)
  have hd : δ≤x := calc
    _ ≤ ((2^N:ℕ):ℝ)*δ := le_mul_of_one_le_left hδ (by exact_mod_cast (Nat.one_le_two_pow : 1≤2^N))
    _ ≤ v*x := hcost
    _ ≤ x := mul_le_of_le_one_left hx.le h₁.le
  have hα := (div_le_iff₀ hx).mpr hcost
  have hw := (div_le_iff₀ hT).mpr ht
  have hh := scalar_relative_error H hmax hx hδ hd hhi hG hc a T hGT (hα.trans hv')
  exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add hα hw) zero_lt_two.le).trans_eq (by ring))

/-- Every window lasting D deadlines attains relative error 4/D once
the target arc is at least D² times the error of the approximate periods. -/
theorem scalar_accuracy_at_scale {N : ℕ} (H : selfAdjoint (Register N))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {δ G x : ℝ}
    (hδ : 0<δ) (hG : 0<G)
    (hc : ∀ u : ℝ, ∃ t ∈ Icc u (u+G), t ∈ visitSet H 0 δ) (a T : ℝ) :
    let D : ℕ := 2^N
    (2:ℝ)≤D → (D:ℝ)^2*δ ≤ x → x+δ ≤ 1/2 → D*G ≤ T →
      |visitFraction H 0 (zeroGateArcTolerance x) a (a+T)/zeroGateArcDensity D x-1| ≤ 4/D := by
  intro D hD hlo hhi hT
  have hDp : (0:ℝ) < D := zero_lt_two.trans_le hD
  have hx : 0 < x := (mul_pos (sq_pos_of_pos hDp) hδ).trans_le hlo
  refine (scalar_accuracy_with_margin H hmax hx hδ.le hG (one_div_pos.mpr hDp)
    (one_div_le_one_div_of_le zero_lt_two hD) hc ?_ hhi a T ?_).trans_eq (by ring)
  · rw [show 1/(D:ℝ)*x=x/D by ring,le_div_iff₀ hDp]
    nlinarith only [hlo]
  · rw [show 1/(D:ℝ)*T=T/D by ring,le_div_iff₀ hDp]
    simpa only [mul_comm G] using hT

#print axioms scalar_accuracy_at_scale
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
