import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryNorm

/-!
# Exact geometric preservation and the first strict recovery-cost drop

Alternation duality on the surviving grids gives the exact initial quotient
costs. The homogeneous sublevel polynomial produces a strict upper bound for
the first changed cost, and the inscribed homothetic wedge gives its lower
bound. Every cost is the actual attained infimum defined in RecoverySurgeryNorm.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set

def recoveryWedgeGap (k : ℕ) : ℝ := 1 / ((k+1 : ℝ)*(2 : ℝ)^(k+1))

theorem recoveryWedgeGap_positive (k : ℕ) : 0 < recoveryWedgeGap k := by
  unfold recoveryWedgeGap
  positivity

theorem recoveryWedgeGap_denominator (k : ℕ) :
    recoveryWedgeGap k * ((k+1 : ℝ)*(2 : ℝ)^(k+1)) = 1 := by
  have h : ((k+1 : ℝ)*(2 : ℝ)^(k+1)) ≠ 0 := by positivity
  exact one_div_mul_cancel h

def recoveryWedgeExtremal (k : ℕ) : cubicHomogeneousSpace (k+1) :=
  recoveryHomogeneousLift (k+1) (taylor (-2 : ℝ) (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)))

theorem recoveryWedgeExtremal_profile (k : ℕ) :
    recoveryHomogeneousProfile (k+1) (recoveryWedgeExtremal k) =
      taylor (-2 : ℝ) (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)) := by
  apply recoveryHomogeneousProfile_lift
  rw [natDegree_taylor, Chebyshev.natDegree_T, Int.natAbs_natCast]

theorem recoveryWedgeExtremal_coefficient (k : ℕ) :
    cubicGradedCoefficient k (recoveryWedgeExtremal k) =
      -(k+1 : ℝ)*(2 : ℝ)^(k+1) := by
  rw [← recoveryHomogeneousProfile_missing, recoveryWedgeExtremal_profile,
    recoveryChebyshev_shifted_penultimate]

theorem recoveryWedgeExtremal_bound (k : ℕ) (p : ℝ × ℝ) (hp : p ∈ recoveryWedge) :
    |recoveryPlaneEval (recoveryWedgeExtremal k).val p| ≤ 1 := by
  obtain ⟨r,hr,c,hc,rfl⟩ := recoveryWedge_representation p hp
  rw [recoveryPlaneEval_radial, recoveryWedgeExtremal_profile, taylor_eval, abs_mul,
    abs_of_nonneg (pow_nonneg hc.1 _)]
  have hb := Chebyshev.abs_eval_T_real_le_one ((k+1 : ℕ) : ℤ)
    (show |r+(-2)| ≤ 1 by rw [abs_le]; constructor <;> linarith [hr.1,hr.2])
  exact (mul_le_mul (pow_le_one₀ hc.1 hc.2) hb (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem recoveryWedgeExtremal_normalized (k : ℕ) :
    (-recoveryWedgeGap k) • recoveryWedgeExtremal k ∈ cubicNormalizedResiduals k := by
  change cubicGradedCoefficient k ((-recoveryWedgeGap k) • recoveryWedgeExtremal k)=1
  rw [map_smul,smul_eq_mul,recoveryWedgeExtremal_coefficient]
  nlinarith [recoveryWedgeGap_denominator k]

theorem recoverySurgeryGap_le_wedge (n k : ℕ) : recoverySurgeryGap n k ≤ recoveryWedgeGap k := by
  apply (recoverySurgeryGap_le n k _ (recoveryWedgeExtremal_normalized k)).trans
  rw [recoverySurgeryCapacity_smul, abs_neg, abs_of_pos (recoveryWedgeGap_positive k)]
  have hb : recoverySurgeryCapacity n (k+1) (recoveryWedgeExtremal k) ≤ 1 :=
    recoverySurgeryCapacity_le n (k+1) _ 1 (fun p hp => recoveryWedgeExtremal_bound k p hp.1)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (le_of_lt (recoveryWedgeGap_positive k))

theorem recoverySurgeryResidual_prefix_bound (n : ℕ) (k : Fin (n+1))
    (P : cubicHomogeneousSpace (k.val+1)) (hP : P ∈ cubicNormalizedResiduals k.val) :
    recoveryWedgeGap k.val ≤ recoverySurgeryCapacity n (k.val+1) P := by
  have hb := recoveryCoefficient_grid_bound k.val (recoveryHomogeneousProfile (k.val+1) P)
    (recoveryHomogeneousProfile_degree _ P) (recoverySurgeryCapacity n (k.val+1) P) (by
      intro i hi
      rw [← recoveryPlaneEval_top]
      exact recoverySurgeryCapacity_bound n (k.val+1) P _
        (recoverySurgeryDomain_protected n k ⟨i,by omega⟩))
  rw [recoveryHomogeneousProfile_missing, show cubicGradedCoefficient k.val P=1 from hP, abs_one] at hb
  unfold recoveryWedgeGap
  exact (div_le_iff₀ (by positivity)).mpr hb

theorem recoverySurgeryGap_prefix (n : ℕ) (k : Fin (n+1)) :
    recoverySurgeryGap n k.val = recoveryWedgeGap k.val := by
  apply le_antisymm (recoverySurgeryGap_le_wedge n k.val)
  obtain ⟨P,hP,hcap⟩ := recoverySurgeryGap_attained n k.val
  rw [← hcap]
  exact recoverySurgeryResidual_prefix_bound n k P hP

theorem recoverySurgeryGap_core_lower (n k : ℕ) :
    (recoverySurgeryCoreScale n)^(k+1)*recoveryWedgeGap k ≤ recoverySurgeryGap n k := by
  obtain ⟨P,hP,hcap⟩ := recoverySurgeryGap_attained n k
  have hq : 0 < (recoverySurgeryCoreScale n)^(k+1) :=
    pow_pos (recoverySurgeryCoreScale_positive n) _
  have hb := recoveryCoefficient_grid_bound k (recoveryHomogeneousProfile (k+1) P)
    (recoveryHomogeneousProfile_degree _ P)
    (recoverySurgeryCapacity n (k+1) P / (recoverySurgeryCoreScale n)^(k+1)) (by
      intro i hi
      have hn := Chebyshev.node_mem_Icc (n := k+1) (i := i)
      have hm := recoverySurgeryDomain_core_param n (2+Chebyshev.node (k+1) i)
        (recoverySurgeryCoreScale n) (by constructor <;> linarith [hn.1,hn.2])
        ⟨le_of_lt (recoverySurgeryCoreScale_positive n),le_refl _⟩
      have hh := recoverySurgeryCapacity_bound n (k+1) P _ hm
      rw [recoveryPlaneEval_radial,abs_mul,abs_of_pos hq] at hh
      exact (le_div_iff₀ hq).mpr (by nlinarith))
  rw [recoveryHomogeneousProfile_missing, show cubicGradedCoefficient k P=1 from hP, abs_one] at hb
  rw [div_mul_eq_mul_div] at hb
  have hh := (le_div_iff₀ hq).mp hb
  rw [one_mul,hcap] at hh
  unfold recoveryWedgeGap
  rw [mul_one_div]
  exact (div_le_iff₀ (by positivity)).mpr hh

theorem recoveryCutPolynomial_normalized (n : ℕ) :
    (-recoveryWedgeGap (n+1)) • recoveryCutPolynomial n ∈ cubicNormalizedResiduals (n+1) := by
  change cubicGradedCoefficient (n+1) ((-recoveryWedgeGap (n+1)) • recoveryCutPolynomial n)=1
  rw [map_smul,smul_eq_mul,recoveryCutPolynomial_missing]
  have h := recoveryWedgeGap_denominator (n+1)
  push_cast at h
  nlinarith

theorem recoverySurgeryGap_drop_upper (n : ℕ) :
    recoverySurgeryGap n (n+1) ≤ recoverySurgeryHeight n * recoveryWedgeGap (n+1) := by
  apply (recoverySurgeryGap_le n (n+1) _ (recoveryCutPolynomial_normalized n)).trans
  rw [recoverySurgeryCapacity_smul, abs_neg, abs_of_pos (recoveryWedgeGap_positive (n+1))]
  have hb : recoverySurgeryCapacity n (n+2) (recoveryCutPolynomial n) ≤ recoverySurgeryHeight n :=
    recoverySurgeryCapacity_le n (n+2) _ _ (fun p hp => hp.2)
  nlinarith [recoveryWedgeGap_positive (n+1)]

theorem recoverySurgeryGap_drop_lower (n : ℕ) :
    recoverySurgeryCorePower n * recoveryWedgeGap (n+1) ≤ recoverySurgeryGap n (n+1) := by
  simpa only [show n+1+1=n+2 by omega, recoverySurgeryCoreScale_power]
    using recoverySurgeryGap_core_lower n (n+1)

theorem recoverySurgeryGap_strict_drop (n : ℕ) :
    recoverySurgeryGap n (n+1) < recoveryWedgeGap (n+1) := by
  exact (recoverySurgeryGap_drop_upper n).trans_lt
    (by nlinarith [recoverySurgeryHeight_lt_one n, recoveryWedgeGap_positive (n+1)])

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
