import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivResidue

/-!
# The residue of an analytic function over a simple pole

`A(s)/(s − p)` has residue `A(p)` at `p`, and `A(s)/(p − s)` has residue `−A(p)`.  Both are read off
the second clearing shift, which is *globally* equal to `±t·A(p+t)` — the junk value at `t = 0`
matches, so no germ argument is needed.

## Main results

* `laurentCoeff_analytic_div_sub`
* `laurentCoeff_analytic_mul_inv_sub`
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem analyticAt_comp_const_add {A : ℂ → ℂ} {p : ℂ} (hA : AnalyticAt ℂ A p) :
    AnalyticAt ℂ (fun t : ℂ => A (p + t)) 0 := by
  have hinner : AnalyticAt ℂ (fun t : ℂ => p + t) 0 := analyticAt_const.add analyticAt_id
  have hA' : AnalyticAt ℂ A ((fun t : ℂ => p + t) 0) := by simpa using hA
  have h := hA'.comp hinner
  simpa [Function.comp_def] using h

theorem deriv_id_mul_shift {A : ℂ → ℂ} {p : ℂ} (hA : AnalyticAt ℂ A p) :
    deriv (fun t : ℂ => t * A (p + t)) 0 = A p := by
  have hshift := analyticAt_comp_const_add hA
  have hd : HasDerivAt (fun t : ℂ => t * A (p + t))
      (1 * A (p + 0) + 0 * deriv (fun t : ℂ => A (p + t)) 0) 0 :=
    (hasDerivAt_id 0).mul hshift.differentiableAt.hasDerivAt
  have hval := hd.deriv
  rw [hval]
  simp

/-- **The residue of an analytic function over a simple pole.** -/
theorem laurentCoeff_analytic_div_sub {A : ℂ → ℂ} {p : ℂ} (hA : AnalyticAt ℂ A p) :
    laurentCoeff (fun s => A s / (s - p)) p (-1) = A p := by
  have hshift : laurentShift (fun s => A s / (s - p)) p 2 = fun t : ℂ => t * A (p + t) := by
    funext t
    simp only [laurentShift]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · rw [show p + t - p = t from by ring]
      field_simp
  have hanalytic : AnalyticAt ℂ (laurentShift (fun s => A s / (s - p)) p 2) 0 := by
    rw [hshift]
    exact analyticAt_id.mul (analyticAt_comp_const_add hA)
  rw [laurentCoeff_eq_taylorCoeffZero hanalytic (by norm_num), hshift]
  have hidx : ((-1 : ℤ) + ((2 : ℕ) : ℤ)).toNat = 1 := by norm_num
  rw [hidx, taylorCoeffZero, iteratedDeriv_one, deriv_id_mul_shift hA]
  norm_num

/-- **The residue against the Cauchy kernel of the opposite orientation.** -/
theorem laurentCoeff_analytic_mul_inv_sub {A : ℂ → ℂ} {p : ℂ} (hA : AnalyticAt ℂ A p) :
    laurentCoeff (fun s => A s * (p - s)⁻¹) p (-1) = -A p := by
  have hshift : laurentShift (fun s => A s * (p - s)⁻¹) p 2
      = fun t : ℂ => -(t * A (p + t)) := by
    funext t
    simp only [laurentShift]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · rw [show p - (p + t) = -t from by ring]
      field_simp
  have hanalytic : AnalyticAt ℂ (laurentShift (fun s => A s * (p - s)⁻¹) p 2) 0 := by
    rw [hshift]
    exact (analyticAt_id.mul (analyticAt_comp_const_add hA)).neg
  rw [laurentCoeff_eq_taylorCoeffZero hanalytic (by norm_num), hshift]
  have hidx : ((-1 : ℤ) + ((2 : ℕ) : ℤ)).toNat = 1 := by norm_num
  rw [hidx, taylorCoeffZero, iteratedDeriv_one]
  have hderiv : deriv (fun t : ℂ => -(t * A (p + t))) 0 = -A p := by
    have hshiftA := analyticAt_comp_const_add hA
    have hd : HasDerivAt (fun t : ℂ => -(t * A (p + t))) (-(A p)) 0 := by
      have hbase : HasDerivAt (fun t : ℂ => t * A (p + t))
          (1 * A (p + 0) + 0 * deriv (fun t : ℂ => A (p + t)) 0) 0 :=
        (hasDerivAt_id 0).mul hshiftA.differentiableAt.hasDerivAt
      have hbase' : HasDerivAt (fun t : ℂ => t * A (p + t)) (A p) 0 := by
        refine hbase.congr_deriv ?_
        simp
      exact hbase'.neg
    exact hd.deriv
  rw [hderiv]
  norm_num

end

end GaloisForLFunctions.HTGeometry
