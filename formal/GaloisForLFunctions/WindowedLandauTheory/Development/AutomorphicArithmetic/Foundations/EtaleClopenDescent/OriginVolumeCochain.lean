import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLogarithmicForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedChartDenominators
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularChartFormProduct
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex

/-! The origin logarithmic form gives a regular top Čech cocycle.
On intersections containing the origin chart, the omitted coordinates
clear its poles. -/

noncomputable section

open GlobalTheory.CechDR KaehlerDifferential
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F L : Type} [Field k] [Field F] [Field L] [Algebra k F] [Algebra k L]
  [Algebra F L] [IsScalarTower k F L] {d : ℕ} {x : Fin (d + 1) → F}

variable (k L x) in
/-- The top wedge of the differentials of the affine origin coordinates. -/
def originAffineVolume : DR k L :=
  ExteriorAlgebra.ιMulti L d fun j => D k L (algebraMap F L (x j.succ / x 0))

theorem originAffineVolume_mem : originAffineVolume k L x ∈ omB k L (rB k L x {0}) d := by
  exact Submodule.subset_span ⟨1, one_mem _, fun j => algebraMap F L (x j.succ / x 0),
    tco_mem k L x, (one_smul L _).symm⟩

/-- The affine volume is the logarithmic volume multiplied by the
product of the affine coordinates. -/
theorem originAffineVolume_eq_smul (h : IsPd k x) :
    originAffineVolume k L x = (∏ j : Fin d, algebraMap F L (x j.succ / x 0)) • vol0 k L x := by
  rw [vol0, AlternatingMap.map_smul_univ, smul_smul, ← Finset.prod_mul_distrib]
  have he (j : Fin d) : algebraMap F L (x j.succ / x 0) ≠ 0 :=
    (map_ne_zero _).mpr (div_ne_zero (h.ne j.succ) (h.ne 0))
  have hp : (∏ j : Fin d, algebraMap F L (x j.succ / x 0) *
      (algebraMap F L (x j.succ / x 0))⁻¹) = 1 :=
    Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (he j)
  rw [hp, one_smul]
  rfl

/-- Multiplication by the affine coordinates of the omitted charts
removes the poles of the logarithmic volume on the intersection. -/
theorem omittedCoordinates_smul_originVolume_mem (h : IsPd k x)
    {I : Finset (Fin (d + 1))} (hi : 0 ∈ I) (a : rB k L x {0}) :
    (∏ j ∈ Iᶜ, algebraMap F L (x j / x 0)) • ((a : L) • vol0 k L x) ∈ omB k L (rB k L x I) d := by
  classical
  let t (j : Fin (d + 1)) := algebraMap F L (x j / x 0)
  have ht (j : Fin (d + 1)) : t j ≠ 0 := (map_ne_zero _).mpr (div_ne_zero (h.ne j) (h.ne 0))
  have hvol : vol0 k L x = (∏ j : Fin (d + 1), (t j)⁻¹) • originAffineVolume k L x := by
    rw [Fin.prod_univ_succ, show t 0 = 1 by simp only [t, div_self (h.ne 0), map_one],
      inv_one, one_mul, vol0, AlternatingMap.map_smul_univ]
    rfl
  have hp : (∏ j ∈ Iᶜ, t j) * (∏ j : Fin (d + 1), (t j)⁻¹) = ∏ j ∈ I, (t j)⁻¹ := by
    rw [← Finset.prod_mul_prod_compl I (fun j => (t j)⁻¹), mul_left_comm,
      ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one (fun j _ => mul_inv_cancel₀ (ht j)), mul_one]
  have hpreg : (∏ j ∈ I, (t j)⁻¹) ∈ rB k L x I := by
    refine Subalgebra.prod_mem _ fun j hj => ?_
    change (algebraMap F L (x j / x 0))⁻¹ ∈ rB k L x I
    rw [← map_inv₀, inv_div]
    exact chartRatio_mem_rB hj 0
  change (∏ j ∈ Iᶜ, t j) • ((a : L) • vol0 k L x) ∈ _
  rw [hvol, smul_comm (a : L), smul_smul, hp]
  have hle : rB k L x {0} ≤ rB k L x I := rB_mono (Finset.singleton_subset_iff.mpr hi)
  exact smul_mem_omB hpreg (smul_mem_omB (hle a.property)
    (omB_mono hle d originAffineVolume_mem))

/-- A logarithmic top form multiplied by an origin-chart function
gives a cochain on the full chart intersection. -/
def originVolumeCochain (a : rB k L x {0}) (I : Finset (Fin (d + 1))) : DR k L :=
  if I = Finset.univ then (a : L) • vol0 k L x else 0

theorem originVolumeCochain_mem_cycles (h : IsPd k x) (a : rB k L x {0}) :
    originVolumeCochain a ∈ (cech fun I => omB k L (rB k L x I) d).Z (d : ℤ) := by
  constructor
  · refine Submodule.mem_pi.mpr fun I _ => ?_
    by_cases he : I = Finset.univ
    · subst I
      have hc : (Finset.univ : Finset (Fin (d + 1))).Nonempty ∧
          ((Finset.univ : Finset (Fin (d + 1))).card : ℤ) = (d : ℤ) + 1 := by simp
      rw [if_pos hc, originVolumeCochain, if_pos rfl]
      simpa only [Finset.compl_univ, Finset.prod_empty, one_smul] using
        omittedCoordinates_smul_originVolume_mem h (Finset.mem_univ 0) a
    · rw [originVolumeCochain, if_neg he]
      exact zero_mem _
  · change deltaL k (Fin (d + 1)) (DR k L) (originVolumeCochain a) = 0
    funext I
    rw [deltaL_apply, Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have he : I.erase i ≠ Finset.univ := fun e => Finset.notMem_erase i I (e.symm ▸ Finset.mem_univ i)
    rw [originVolumeCochain, if_neg he, smul_zero]

end GlobalTheory.PD
