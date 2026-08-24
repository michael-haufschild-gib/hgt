import GaloisForLFunctions.HTGeometry.CayleyGeneralizedSchurCongruence
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeFamily

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One normalized Blaschke factor in upper-half-plane coordinates. -/
def upperHalfPlaneBlaschkeFactor (p z : ℂ) : ℂ :=
  (z - p) / (z - (starRingEnd ℂ) p)

/-- Unimodular normalization introduced by Cayley transport of an upper-half-plane factor. -/
def cayleyBlaschkeUnit (p : ℂ) : ℂ :=
  -(((starRingEnd ℂ) p - I) / (p + I))

theorem norm_cayleyBlaschkeUnit_eq_one {p : ℂ} (hp : 0 < p.im) :
    ‖cayleyBlaschkeUnit p‖ = 1 := by
  have hpI : p + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have hconj : (starRingEnd ℂ) (p + I) = (starRingEnd ℂ) p - I := by
    simp only [map_add, conj_I]
    ring
  rw [cayleyBlaschkeUnit, norm_neg, norm_div, ← hconj, RCLike.norm_conj,
    div_self (norm_ne_zero_iff.mpr hpI)]

theorem cayleyBlaschkeUnit_ne_zero {p : ℂ} (hp : 0 < p.im) :
    cayleyBlaschkeUnit p ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [norm_cayleyBlaschkeUnit_eq_one hp]; norm_num)

/-- Exact transport of one upper-half-plane Blaschke factor to the disk. -/
theorem blaschkeFactor_upperToDiskCayley {p z : ℂ}
    (hp : 0 < p.im) (hz : 0 < z.im) :
    blaschkeFactor (upperToDiskCayley p) (upperToDiskCayley z) =
      cayleyBlaschkeUnit p * upperHalfPlaneBlaschkeFactor p z := by
  have hpI : p + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have hzI : z + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have hcpI : (starRingEnd ℂ) p - I ≠ 0 := by
    intro h
    apply hpI
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have hzc : z - (starRingEnd ℂ) p ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have hnum :
      upperToDiskCayley z - upperToDiskCayley p =
        (2 * I * (z - p)) / ((z + I) * (p + I)) := by
    rw [upperToDiskCayley, upperToDiskCayley]
    field_simp [hpI, hzI]
    ring
  have hden :
      1 - (starRingEnd ℂ) (upperToDiskCayley p) * upperToDiskCayley z =
        (-2 * I * (z - (starRingEnd ℂ) p)) /
          ((z + I) * ((starRingEnd ℂ) p - I)) := by
    rw [mul_comm]
    exact one_sub_upperToDiskCayley_mul_conj hzI hcpI
  rw [blaschkeFactor, hnum, hden, cayleyBlaschkeUnit,
    upperHalfPlaneBlaschkeFactor]
  field_simp [hpI, hzI, hcpI, hzc]

/-- Finite Cayley transport: only one unimodular constant survives. -/
theorem prod_blaschkeFactor_upperToDiskCayley {ι : Type*} [Fintype ι]
    (p : ι → ℂ) (hp : ∀ i, 0 < (p i).im) {z : ℂ} (hz : 0 < z.im) :
    (∏ i : ι, blaschkeFactor (upperToDiskCayley (p i)) (upperToDiskCayley z)) =
      (∏ i : ι, cayleyBlaschkeUnit (p i)) *
        ∏ i : ι, upperHalfPlaneBlaschkeFactor (p i) z := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact blaschkeFactor_upperToDiskCayley (hp i) hz

theorem norm_prod_cayleyBlaschkeUnit_eq_one {ι : Type*} [Fintype ι]
    (p : ι → ℂ) (hp : ∀ i, 0 < (p i).im) :
    ‖∏ i : ι, cayleyBlaschkeUnit (p i)‖ = 1 := by
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => norm_cayleyBlaschkeUnit_eq_one (hp i)

end

end GaloisForLFunctions.HTGeometry
