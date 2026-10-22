import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointConformalCoefficients

/-! The proved coordinate identities contract the actual Frechet Hessian and first derivative. -/
namespace RHTower.D4BMJointConformal
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

theorem linear_basis (L : Point3 →L[ℝ] ℂ) (v : Point3) :
    L v = ∑ j : Fin 3, (v j:ℂ)*L (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v,map_sum]
  simp only [map_smul,Complex.real_smul]

theorem bilinear_basis (B : Point3 →L[ℝ] Point3 →L[ℝ] ℂ) (v w : Point3) :
    B v w = ∑ j : Fin 3, ∑ k : Fin 3, (v j:ℂ)*(w k:ℂ)*B (Pi.single j 1) (Pi.single k 1) := by
  have hv : B v = ∑ j : Fin 3, v j • B (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v,map_sum]
    simp only [map_smul]
  rw [hv]
  simp only [sum_apply,smul_apply,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [linear_basis (B (Pi.single j 1)) w,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The full actual Hessian contracts to the Euclidean trace, without a symmetry premise. -/
theorem principal_contraction (p : Point3) (B : Point3 →L[ℝ] Point3 →L[ℝ] ℂ) :
    (∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*B (chartFirst p i) (chartFirst p i)) =
      (chart p 1:ℂ)^(2 : ℕ)*∑ j : Fin 3, B (Pi.single j 1) (Pi.single j 1) := by
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ((ellipticCoefficient p i:ℂ)*(chartFirst p i j:ℂ)*(chartFirst p i k:ℂ))*
          B (Pi.single j 1) (Pi.single k 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [bilinear_basis B (chartFirst p i) (chartFirst p i)]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j : Fin 3, ∑ k : Fin 3,
        ((∑ i : Fin 3, ellipticCoefficient p i*chartFirst p i j*chartFirst p i k:ℝ):ℂ)*
          B (Pi.single j 1) (Pi.single k 1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      rw [Finset.sum_mul]
    _ = _ := by
      simp_rw [chart_principalSymbol]
      simp [apply_ite,ite_mul,Finset.mul_sum]

/-- The actual first derivative sees zero total drift after field conjugation. -/
theorem drift_contraction (p : Point3) (hp : 0 < p 2) (L : Point3 →L[ℝ] ℂ) :
    (∑ i : Fin 3, (ellipticCoefficient p i:ℂ)*
      (2*(firstRatio p i:ℂ)*L (chartFirst p i)+L (chartSecond p i))) = 0 := by
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        ((ellipticCoefficient p i:ℂ)*((chartSecond p i j:ℂ)+
          2*(firstRatio p i:ℂ)*(chartFirst p i j:ℂ)))*L (Pi.single j 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [linear_basis L (chartFirst p i),linear_basis L (chartSecond p i)]
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin 3, ((∑ i : Fin 3, ellipticCoefficient p i*
        (chartSecond p i j+2*firstRatio p i*chartFirst p i j):ℝ):ℂ)*L (Pi.single j 1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      rw [Finset.sum_mul]
    _ = 0 := by simp [chart_driftCancellation p hp]

end
end RHTower.D4BMJointConformal
