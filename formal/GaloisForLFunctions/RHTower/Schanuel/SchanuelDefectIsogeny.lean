import GaloisForLFunctions.RHTower.Schanuel.SchanuelDefectValueField

/-!
# Integral isogeny descent for Schanuel defect slopes

An integral linear change of additive coordinates, paired with its Laurent-monomial exponential
coordinates, transforms a two-dimensional defect slope fractionally linearly.  If the transformed
pair lives in a rank-one intermediate value field, nonzero determinant forces the original slope
to live there as well.
-/

namespace GaloisForLFunctions.RHTower

open Complex

noncomputable section

/-- Numerical Schanuel defects are additive. -/
theorem schanuelDefect_add (z w : ℂ) :
    schanuelDefect (z + w) = schanuelDefect z + schanuelDefect w := by
  let A := algebraicClosure ℚ ℂ
  let D := KaehlerDifferential.D A ℂ
  simp only [schanuelDefect, Complex.exp_add, map_add]
  rw [derivation_log_mul D _ _ (Complex.exp_ne_zero z) (Complex.exp_ne_zero w)]
  abel

/-- Numerical Schanuel defects commute with integral scaling. -/
theorem schanuelDefect_int_mul (m : ℤ) (z : ℂ) :
    schanuelDefect ((m : ℂ) * z) = (m : ℂ) • schanuelDefect z := by
  let A := algebraicClosure ℚ ℂ
  let D := KaehlerDifferential.D A ℂ
  have hD : D ((m : ℂ) * z) = (m : ℂ) • D z := by
    rw [D.leibniz]
    simp
  simp only [schanuelDefect, Complex.exp_int_mul]
  rw [derivation_log_zpow D _ _ (Complex.exp_ne_zero z)]
  rw [hD, smul_sub]

/-- Schanuel defects intertwine every integral linear combination. -/
theorem schanuelDefect_integer_linearCombination
    {n : ℕ} (m : Fin n → ℤ) (x : Fin n → ℂ) :
    schanuelDefect (∑ i, (m i : ℂ) * x i) =
      ∑ i, (m i : ℂ) • schanuelDefect (x i) := by
  classical
  let t : Finset (Fin n) := Finset.univ
  change schanuelDefect (∑ i ∈ t, (m i : ℂ) * x i) =
    ∑ i ∈ t, (m i : ℂ) • schanuelDefect (x i)
  induction t using Finset.induction_on with
  | empty => simp [schanuelDefect]
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        schanuelDefect_add, schanuelDefect_int_mul, ih]

/-- The original defect slope belongs to any rank-one intermediate value field carrying a
nondegenerate integral isogeny transform of the exponential pair. -/
theorem schanuelDefect_slope_mem_of_integral_isogeny
    (K : IntermediateField (algebraicClosure ℚ ℂ) ℂ)
    (x : Fin 2 → ℂ) (z w : Fin 2 → K)
    (hw : ∀ i, (w i : ℂ) = Complex.exp (z i : ℂ))
    (hzLI : LinearIndependent ℚ (fun i => (z i : ℂ)))
    (hfinrank : Module.finrank K
      (KaehlerDifferential (algebraicClosure ℚ ℂ) K) = 1)
    (rho : ℂ)
    (hslope : schanuelDefect (x 1) = rho • schanuelDefect (x 0))
    (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (hz0 : (z 0 : ℂ) = (a : ℂ) * x 0 + (b : ℂ) * x 1)
    (hz1 : (z 1 : ℂ) = (c : ℂ) * x 0 + (d : ℂ) * x 1) :
    ∃ tau : K, (tau : ℂ) = rho := by
  have hrow0 : schanuelDefect (z 0 : ℂ) =
      ((a : ℂ) + (b : ℂ) * rho) • schanuelDefect (x 0) := by
    rw [hz0, schanuelDefect_add, schanuelDefect_int_mul,
      schanuelDefect_int_mul, hslope, smul_smul]
    module
  have hrow1 : schanuelDefect (z 1 : ℂ) =
      ((c : ℂ) + (d : ℂ) * rho) • schanuelDefect (x 0) := by
    rw [hz1, schanuelDefect_add, schanuelDefect_int_mul,
      schanuelDefect_int_mul, hslope, smul_smul]
    module
  have hzeta0 : schanuelDefect (z 0 : ℂ) ≠ 0 := by
    intro hzero
    let m : Fin 2 → ℤ := fun i => if i = 0 then 1 else 0
    have hm := schanuelDefect_integer_relation (fun i => (z i : ℂ)) hzLI m (by
      simp [m, hzero])
    have hm0 := congrFun hm 0
    norm_num [m] at hm0
  have hdenom : (a : ℂ) + (b : ℂ) * rho ≠ 0 := by
    intro hzero
    apply hzeta0
    rw [hrow0, hzero, zero_smul]
  let rho' : ℂ :=
    ((c : ℂ) + (d : ℂ) * rho) / ((a : ℂ) + (b : ℂ) * rho)
  have hslope' : schanuelDefect (z 1 : ℂ) =
      rho' • schanuelDefect (z 0 : ℂ) := by
    rw [hrow1, hrow0, smul_smul]
    congr 1
    exact (div_mul_cancel₀ _ hdenom).symm
  obtain ⟨sigma, hsigma⟩ :=
    schanuelDefect_slope_mem_intermediateField_of_finrank_one
      K z w hw hzLI hfinrank rho' hslope'
  apply mobius_slope_mem_intermediateField K rho sigma a b c d hdet
  rw [hsigma]
  exact div_mul_cancel₀ _ hdenom

end

end GaloisForLFunctions.RHTower
