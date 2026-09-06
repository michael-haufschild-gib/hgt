import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryDomain
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryDuality

/-!
# Actual geometric quotient costs after polynomial surgery

The supremum of planar polynomial evaluation defines a genuine norm on every
homogeneous space. Every cusp-algebra residual class has an attained positive
minimum. The quotient cost is an infimum over these actual representatives;
its exact coefficient formula follows from sharp attainment and homogeneity.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set

theorem recoverySurgeryDomain_nonempty (n : ℕ) : (recoverySurgeryDomain n).Nonempty :=
  (recoverySurgeryDomain_interior n).mono interior_subset

def recoverySurgeryCapacity (n k : ℕ) (P : cubicHomogeneousSpace k) : ℝ :=
  sSup ((fun p => |recoveryPlaneEval P.val p|) '' recoverySurgeryDomain n)

theorem recoverySurgeryCapacity_values_nonempty (n k : ℕ) (P : cubicHomogeneousSpace k) :
    ((fun p => |recoveryPlaneEval P.val p|) '' recoverySurgeryDomain n).Nonempty :=
  (recoverySurgeryDomain_nonempty n).image _

theorem recoverySurgeryCapacity_values_bddAbove (n k : ℕ) (P : cubicHomogeneousSpace k) :
    BddAbove ((fun p => |recoveryPlaneEval P.val p|) '' recoverySurgeryDomain n) :=
  ((recoverySurgeryDomain_compact n).image
    (recoveryPlaneEval_continuous P.val).abs).bddAbove

theorem recoverySurgeryCapacity_bound (n k : ℕ) (P : cubicHomogeneousSpace k)
    (p : ℝ × ℝ) (hp : p ∈ recoverySurgeryDomain n) :
    |recoveryPlaneEval P.val p| ≤ recoverySurgeryCapacity n k P :=
  le_csSup (recoverySurgeryCapacity_values_bddAbove n k P) ⟨p,hp,rfl⟩

theorem recoverySurgeryCapacity_nonneg (n k : ℕ) (P : cubicHomogeneousSpace k) :
    0 ≤ recoverySurgeryCapacity n k P := by
  obtain ⟨p,hp⟩ := recoverySurgeryDomain_nonempty n
  exact (abs_nonneg _).trans (recoverySurgeryCapacity_bound n k P p hp)

theorem recoverySurgeryCapacity_le (n k : ℕ) (P : cubicHomogeneousSpace k) (b : ℝ)
    (hb : ∀ p ∈ recoverySurgeryDomain n, |recoveryPlaneEval P.val p| ≤ b) :
    recoverySurgeryCapacity n k P ≤ b := by
  apply csSup_le (recoverySurgeryCapacity_values_nonempty n k P)
  rintro y ⟨p,hp,rfl⟩
  exact hb p hp

theorem recoverySurgeryCapacity_attained (n k : ℕ) (P : cubicHomogeneousSpace k) :
    ∃ p ∈ recoverySurgeryDomain n,
      |recoveryPlaneEval P.val p| = recoverySurgeryCapacity n k P := by
  obtain ⟨p,hp,hmax⟩ := (recoverySurgeryDomain_compact n).exists_isMaxOn
    (recoverySurgeryDomain_nonempty n) (recoveryPlaneEval_continuous P.val).abs.continuousOn
  exact ⟨p,hp,le_antisymm (recoverySurgeryCapacity_bound n k P p hp)
    (recoverySurgeryCapacity_le n k P _ hmax)⟩

theorem recoverySurgeryCapacity_zero (n k : ℕ) :
    recoverySurgeryCapacity n k 0 = 0 := by
  apply le_antisymm _ (recoverySurgeryCapacity_nonneg n k 0)
  apply recoverySurgeryCapacity_le
  intro p hp
  simp only [ZeroMemClass.coe_zero, recoveryPlaneEval, eval₂_zero, abs_zero, le_refl]

theorem recoverySurgeryCapacity_add_le (n k : ℕ) (P Q : cubicHomogeneousSpace k) :
    recoverySurgeryCapacity n k (P+Q) ≤
      recoverySurgeryCapacity n k P + recoverySurgeryCapacity n k Q := by
  apply recoverySurgeryCapacity_le
  intro p hp
  change |recoveryPlaneEval (P.val+Q.val) p| ≤ _
  simp only [recoveryPlaneEval, eval₂_add]
  exact (abs_add_le _ _).trans
    (add_le_add (recoverySurgeryCapacity_bound n k P p hp)
      (recoverySurgeryCapacity_bound n k Q p hp))

theorem recoveryPlaneEval_smul (r : ℝ) (P : Polynomial (Polynomial ℝ)) (p : ℝ × ℝ) :
    recoveryPlaneEval (r • P) p = r * recoveryPlaneEval P p := by
  unfold recoveryPlaneEval
  rw [← smul_one_smul (Polynomial ℝ) r P, eval₂_smul]
  simp only [coe_evalRingHom, eval_smul, eval_one, smul_eq_mul, mul_one]

theorem recoverySurgeryCapacity_smul_le (n k : ℕ) (r : ℝ) (P : cubicHomogeneousSpace k) :
    recoverySurgeryCapacity n k (r • P) ≤ ‖r‖ * recoverySurgeryCapacity n k P := by
  apply recoverySurgeryCapacity_le
  intro p hp
  change |recoveryPlaneEval (r • P.val) p| ≤ _
  rw [recoveryPlaneEval_smul, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (recoverySurgeryCapacity_bound n k P p hp) (abs_nonneg r)

theorem recoverySurgeryCapacity_definite (n k : ℕ) (P : cubicHomogeneousSpace k) :
    recoverySurgeryCapacity n k P = 0 ↔ P = 0 := by
  constructor
  · intro hz
    have hprofile : recoveryHomogeneousProfile k P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.Icc_infinite (show (1:ℝ)<3 by linarith)).mono
      intro r hr
      have hp := recoverySurgeryDomain_core_param n r (recoverySurgeryCoreScale n) hr
        ⟨le_of_lt (recoverySurgeryCoreScale_positive n),le_refl _⟩
      have hb := recoverySurgeryCapacity_bound n k P _ hp
      rw [hz, recoveryPlaneEval_radial] at hb
      have he := abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
      exact (mul_eq_zero.mp he).resolve_left
        (pow_ne_zero _ (ne_of_gt (recoverySurgeryCoreScale_positive n)))
    apply (cubicHomogeneousCoordinatesEquiv k).injective
    funext i
    change cubicHomogeneousCoordinates k P i = cubicHomogeneousCoordinates k 0 i
    rw [← recoveryHomogeneousProfile_coefficient k P i, hprofile, coeff_zero]
    simp only [cubicHomogeneousCoordinates, ZeroMemClass.coe_zero, coeff_zero]
  · rintro rfl
    exact recoverySurgeryCapacity_zero n k

def recoverySurgerySeminorm (n k : ℕ) : Seminorm ℝ (cubicHomogeneousSpace k) :=
  Seminorm.ofSMulLE (recoverySurgeryCapacity n k) (recoverySurgeryCapacity_zero n k)
    (recoverySurgeryCapacity_add_le n k) (recoverySurgeryCapacity_smul_le n k)

def recoverySurgeryGroupNorm (n k : ℕ) : AddGroupNorm (cubicHomogeneousSpace k) where
  toAddGroupSeminorm := (recoverySurgerySeminorm n k).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' P h := (recoverySurgeryCapacity_definite n k P).mp h

@[implicit_reducible]
def recoverySurgeryNormedGroup (n k : ℕ) : NormedAddCommGroup (cubicHomogeneousSpace k) :=
  (recoverySurgeryGroupNorm n k).toNormedAddCommGroup

@[implicit_reducible]
def recoverySurgeryNormedSpace (n k : ℕ) :
    letI := recoverySurgeryNormedGroup n k
    NormedSpace ℝ (cubicHomogeneousSpace k) := by
  letI := recoverySurgeryNormedGroup n k
  exact { (inferInstance : Module ℝ (cubicHomogeneousSpace k)) with
    norm_smul_le := fun r P => recoverySurgeryCapacity_smul_le n k r P }

theorem recoverySurgeryCapacity_smul (n k : ℕ) (r : ℝ) (P : cubicHomogeneousSpace k) :
    recoverySurgeryCapacity n k (r • P) = |r| * recoverySurgeryCapacity n k P := by
  letI := recoverySurgeryNormedGroup n k
  letI := recoverySurgeryNormedSpace n k
  exact norm_smul r P

theorem recoverySurgeryResiduals_positiveMinimum (n k : ℕ) :
    ∃ P ∈ cubicNormalizedResiduals k, 0 < recoverySurgeryCapacity n (k+1) P ∧
      ∀ Q ∈ cubicNormalizedResiduals k,
        recoverySurgeryCapacity n (k+1) P ≤ recoverySurgeryCapacity n (k+1) Q := by
  letI := recoverySurgeryNormedGroup n (k+1)
  letI := recoverySurgeryNormedSpace n (k+1)
  letI := cubicHomogeneousSpace_finiteDimensional (k+1)
  letI := FiniteDimensional.proper ℝ (cubicHomogeneousSpace (k+1))
  have hclosed : IsClosed (cubicNormalizedResiduals k) :=
    isClosed_eq ((continuous_apply (cubicMissingIndex k)).comp
      (cubicHomogeneousCoordinatesEquiv (k+1)).toLinearMap.continuous_of_finiteDimensional)
      continuous_const
  obtain ⟨P,hP,hmin⟩ := hclosed.exists_infDist_eq_dist
    (cubicNormalizedResiduals_nonempty k) (0 : cubicHomogeneousSpace (k+1))
  have hne : P ≠ 0 := by
    intro hz
    subst P
    change (((0 : Polynomial (Polynomial ℝ)).coeff (k+1-k)).coeff k)=1 at hP
    simp only [Polynomial.coeff_zero] at hP
    exact zero_ne_one hP
  refine ⟨P,hP,?_,?_⟩
  · exact lt_of_le_of_ne (recoverySurgeryCapacity_nonneg n (k+1) P)
      (fun h => hne ((recoverySurgeryCapacity_definite n (k+1) P).mp h.symm))
  · intro Q hQ
    have hb := Metric.infDist_le_dist_of_mem (x := (0 : cubicHomogeneousSpace (k+1))) hQ
    rw [hmin,dist_zero_left,dist_zero_left] at hb
    exact hb

def recoverySurgeryErrors (n k : ℕ) : Set ℝ :=
  recoverySurgeryCapacity n (k+1) ''
    {P : cubicHomogeneousSpace (k+1) | (cubicHomogeneousMissing k-P).val ∈ cubicCuspAlgebra}

def recoverySurgeryGap (n k : ℕ) : ℝ := sInf (recoverySurgeryErrors n k)

theorem recoverySurgeryErrors_positiveLeast (n k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ IsLeast (recoverySurgeryErrors n k) δ := by
  obtain ⟨P,hP,hpos,hmin⟩ := recoverySurgeryResiduals_positiveMinimum n k
  refine ⟨recoverySurgeryCapacity n (k+1) P,hpos,?_,?_⟩
  · exact ⟨P,(cubicNormalizedResiduals_mem k P).mp hP,rfl⟩
  · rintro y ⟨Q,hQ,rfl⟩
    exact hmin Q ((cubicNormalizedResiduals_mem k Q).mpr hQ)

theorem recoverySurgeryGap_isLeast (n k : ℕ) :
    IsLeast (recoverySurgeryErrors n k) (recoverySurgeryGap n k) := by
  obtain ⟨δ,hδ,hmin⟩ := recoverySurgeryErrors_positiveLeast n k
  change IsLeast _ (sInf _)
  rw [hmin.csInf_eq]
  exact hmin

theorem recoverySurgeryGap_positive (n k : ℕ) : 0 < recoverySurgeryGap n k := by
  obtain ⟨δ,hδ,hmin⟩ := recoverySurgeryErrors_positiveLeast n k
  change 0 < sInf _
  rw [hmin.csInf_eq]
  exact hδ

theorem recoverySurgeryGap_attained (n k : ℕ) :
    ∃ P ∈ cubicNormalizedResiduals k,
      recoverySurgeryCapacity n (k+1) P = recoverySurgeryGap n k := by
  obtain ⟨P,hP,he⟩ := (recoverySurgeryGap_isLeast n k).1
  exact ⟨P,(cubicNormalizedResiduals_mem k P).mpr hP,he⟩

theorem recoverySurgeryGap_le (n k : ℕ) (P : cubicHomogeneousSpace (k+1))
    (hP : P ∈ cubicNormalizedResiduals k) :
    recoverySurgeryGap n k ≤ recoverySurgeryCapacity n (k+1) P :=
  (recoverySurgeryGap_isLeast n k).2 ⟨P,(cubicNormalizedResiduals_mem k P).mp hP,rfl⟩

theorem recoverySurgeryCoefficient_sharpBound (n k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    |cubicGradedCoefficient k P| * recoverySurgeryGap n k ≤ recoverySurgeryCapacity n (k+1) P := by
  by_cases hz : cubicGradedCoefficient k P=0
  · simpa only [hz,abs_zero,zero_mul] using recoverySurgeryCapacity_nonneg n (k+1) P
  · let R := (cubicGradedCoefficient k P)⁻¹ • P
    have hR : R ∈ cubicNormalizedResiduals k := by
      change cubicGradedCoefficient k ((cubicGradedCoefficient k P)⁻¹ • P)=1
      rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hz]
    have hb := recoverySurgeryGap_le n k R hR
    change recoverySurgeryGap n k ≤ recoverySurgeryCapacity n (k+1)
      ((cubicGradedCoefficient k P)⁻¹ • P) at hb
    rw [recoverySurgeryCapacity_smul,abs_inv] at hb
    have h := mul_le_mul_of_nonneg_left hb (abs_nonneg (cubicGradedCoefficient k P))
    rw [← mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr hz),one_mul] at h
    exact h

theorem recoverySurgeryCoefficient_sharpAttainment (n k : ℕ) (r : ℝ) :
    ∃ P : cubicHomogeneousSpace (k+1), cubicGradedCoefficient k P=r ∧
      recoverySurgeryCapacity n (k+1) P=|r| * recoverySurgeryGap n k := by
  obtain ⟨R,hR,hcap⟩ := recoverySurgeryGap_attained n k
  have hr : cubicGradedCoefficient k R=1 := hR
  refine ⟨r • R,?_,?_⟩
  · rw [map_smul,hr,smul_eq_mul,mul_one]
  · rw [recoverySurgeryCapacity_smul,hcap]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
