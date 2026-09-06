import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicGradedCoefficient

/-!
# Physical multiplication contracts successive recovery gaps

Multiplication by the actual first mode u sends weight k to weight k+1.
It preserves the normalized missing coefficient and contracts physical capacity
by at least a factor of four. Attained minimizers therefore give a strictly
positive successor gap bounded by one quarter of the preceding gap.
-/


namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

theorem cubicRecoveryPhysical_mode_bound (g : cubicProbeSection) :
    0 ≤ cubicDecayMode 0 g.val ∧ cubicDecayMode 0 g.val ≤ 1/4 := by
  have hc := cubicRecoveryPhysical_middle g
  have hu := cubicRecoveryPhysical_mode g
  constructor
  · have hL : 0 ≤ cubicRecoveryLower (g.val 2) := by
      unfold cubicRecoveryLower
      nlinarith [mul_nonneg (sq_nonneg (g.val 2)) (sub_nonneg.mpr hc.2)]
    exact hL.trans hu.1
  · linarith [hu.2,hc.2]

theorem cubicPolynomialFlow_firstMode (q : ℝ) :
    cubicPolynomialFlow q (Polynomial.C Polynomial.X)=
      q • Polynomial.C Polynomial.X := by
  simp only [cubicPolynomialFlow,Polynomial.aevalTower_C,AlgHom.comp_apply,
    Polynomial.CAlgHom_apply,cubicInnerPolynomialFlow,Polynomial.aeval_X]
  rw [Polynomial.C_mul',Polynomial.smul_C]

def cubicHomogeneousMultiplyFirst (k : ℕ) :
    cubicHomogeneousSpace k →ₗ[ℝ] cubicHomogeneousSpace (k+1) where
  toFun P := ⟨Polynomial.C Polynomial.X*P.val,by
    rw [cubicHomogeneousSpace_mem,map_mul,cubicPolynomialFlow_firstMode,
      cubicHomogeneousSpace_flow,smul_mul_assoc,mul_smul_comm,smul_smul,pow_succ]
    congr 1
    ring⟩
  map_add' P Q := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' r P := by apply Subtype.ext; exact mul_smul_comm _ _ _

theorem cubicHomogeneousMultiplyFirst_val (k : ℕ) (P : cubicHomogeneousSpace k) :
    (cubicHomogeneousMultiplyFirst k P).val=Polynomial.C Polynomial.X*P.val := rfl

theorem cubicHomogeneousMultiplyFirst_observation (k : ℕ) (P : cubicHomogeneousSpace k)
    (g : cubicProbeSection) :
    cubicPolynomialObservation (cubicHomogeneousMultiplyFirst k P).val g=
      cubicDecayMode 0 g.val*cubicPolynomialObservation P.val g := by
  rw [cubicHomogeneousMultiplyFirst_val,map_mul,Pi.mul_apply,cubicPolynomialObservation_firstMode]

theorem cubicHomogeneousMultiplyFirst_capacity (k : ℕ) (P : cubicHomogeneousSpace k) :
    cubicHomogeneousCapacity (k+1) (cubicHomogeneousMultiplyFirst k P) ≤
      cubicHomogeneousCapacity k P/4 := by
  apply csSup_le (cubicHomogeneousValues_nonempty _ _)
  rintro y ⟨g,rfl⟩
  change |cubicPolynomialObservation (cubicHomogeneousMultiplyFirst k P).val g| ≤ _
  rw [cubicHomogeneousMultiplyFirst_observation,abs_mul,
    abs_of_nonneg (cubicRecoveryPhysical_mode_bound g).1]
  have h := mul_le_mul (cubicRecoveryPhysical_mode_bound g).2
    (cubicHomogeneousCapacity_bound k P g) (abs_nonneg _)
    (by positivity : (0:ℝ) ≤ 1/4)
  linarith

theorem cubicHomogeneousMultiplyFirst_coefficient (k : ℕ)
    (P : cubicHomogeneousSpace (k+1)) :
    cubicGradedCoefficient (k+1) (cubicHomogeneousMultiplyFirst (k+1) P)=
      cubicGradedCoefficient k P := by
  simp only [cubicGradedCoefficient_apply,cubicHomogeneousCoordinates,cubicMissingIndex,
    cubicHomogeneousMultiplyFirst_val,Nat.add_sub_cancel_left,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul]

theorem cubicHomogeneousMultiplyFirst_normalized (k : ℕ) :
    MapsTo (cubicHomogeneousMultiplyFirst (k+1)) (cubicNormalizedResiduals k)
      (cubicNormalizedResiduals (k+1)) := by
  intro P hP
  change cubicGradedCoefficient (k+1) (cubicHomogeneousMultiplyFirst (k+1) P)=1
  rw [cubicHomogeneousMultiplyFirst_coefficient]
  exact hP

theorem cubicGradedRecoveryGap_successor_bound (k : ℕ) :
    0<cubicGradedRecoveryGap (k+1) ∧
      cubicGradedRecoveryGap (k+1) ≤ cubicGradedRecoveryGap k/4 := by
  refine ⟨cubicGradedRecoveryGap_positive _,?_⟩
  obtain ⟨P,hP,hcap⟩ := cubicGradedRecoveryGap_attained k
  have hnext := cubicHomogeneousMultiplyFirst_normalized k hP
  have hm := (cubicGradedRecoveryGap_isLeast (k+1)).2
    ⟨cubicHomogeneousMultiplyFirst (k+1) P,
      (cubicNormalizedResiduals_mem (k+1) _).mp hnext,rfl⟩
  exact hm.trans (hcap ▸ cubicHomogeneousMultiplyFirst_capacity (k+1) P)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
