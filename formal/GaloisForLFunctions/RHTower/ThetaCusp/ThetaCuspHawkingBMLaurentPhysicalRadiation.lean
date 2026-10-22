import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorVectorLaurentMaster

/-!
# Physical values of the Laurent normalizable coefficients

At a Xi occurrence `ρ` the two physical branches have the rates `s₊ = ρ − 2`, `s₋ = −ρ − 1` and
share the angular eigenvalue `λ = ρ(ρ−1) = (s+1)(s+2)` of the fundamental profile. Evaluated at
that harmonic, the normalizable coefficients of the per-harmonic `++` responses are elementary
rational functions of `ρ`: vector–vector `A = (2/3)(ρ−2)(4ρ+3)` on the `+` branch and
`(2/3)(ρ+1)(4ρ−7)` on the `−` branch, the functional-equation image `ρ ↦ 1−ρ` of the former;
scalar–scalar `A = −(5ρ−7)(ρ+2)/(2(ρ+1))` and `(5ρ+2)(ρ−3)/(2(ρ−2))`. The two angular
resolvent denominators, `2 − λ = −(ρ−2)(ρ+1)` and `λ − (2s+1)(2s+2) = −3(ρ−1)(ρ−2)`
(respectively `−3ρ(ρ+1)`), are nonzero because `ρ` is not real.
-/

namespace RHTower.D4BMScalarStream
open D4BMModularCore
noncomputable section

/-- The fundamental angular eigenvalue of a Xi occurrence, `λ = ρ(ρ−1)`. -/
def physicalEigenvalue (q : XiZeroCopy) : ℂ := (q.1 : ℂ) * ((q.1 : ℂ) - 1)

/-- On both physical branches the fundamental eigenvalue is `(s+1)(s+2)`. -/
theorem physicalEigenvalue_eq (q : XiZeroCopy) (branch : Bool) :
    physicalEigenvalue q = (physicalRate q branch + 1) * (physicalRate q branch + 2) := by
  cases branch <;> simp only [physicalEigenvalue, physicalRate, Bool.false_eq_true, if_false, if_true] <;> ring

theorem xiCopy_add_real_ne_zero (q : XiZeroCopy) (c : ℝ) : (q.1 : ℂ) + c ≠ 0 := by
  intro h
  have hi := xi_divisor_support_im_ne_zero q.1
  apply hi
  have := congrArg Complex.im h
  simpa using this

theorem xiCopy_sub_real_ne_zero (q : XiZeroCopy) (c : ℝ) : (q.1 : ℂ) - c ≠ 0 := by
  have := xiCopy_add_real_ne_zero q (-c)
  push_cast at this
  simpa [sub_eq_add_neg] using this

/-- The angular resolvent at two is regular at the fundamental eigenvalue. -/
theorem two_sub_physicalEigenvalue_ne_zero (q : XiZeroCopy) : 2 - physicalEigenvalue q ≠ 0 := by
  rw [show 2 - physicalEigenvalue q = -(((q.1 : ℂ) - 2) * ((q.1 : ℂ) + 1)) by
    unfold physicalEigenvalue; ring]
  exact neg_ne_zero.mpr (mul_ne_zero (by simpa using xiCopy_sub_real_ne_zero q 2)
    (by simpa using xiCopy_add_real_ne_zero q 1))

/-- The doubled-rate resolvent is regular at the fundamental eigenvalue, on the `+` branch. -/
theorem physicalEigenvalue_resonance_plus_ne_zero (q : XiZeroCopy) :
    physicalEigenvalue q - (2 * ((q.1 : ℂ) - 2) + 1) * (2 * ((q.1 : ℂ) - 2) + 2) ≠ 0 := by
  rw [show physicalEigenvalue q - (2 * ((q.1 : ℂ) - 2) + 1) * (2 * ((q.1 : ℂ) - 2) + 2) =
      -3 * (((q.1 : ℂ) - 1) * ((q.1 : ℂ) - 2)) by unfold physicalEigenvalue; ring]
  exact mul_ne_zero (by norm_num) (mul_ne_zero (by simpa using xiCopy_sub_real_ne_zero q 1)
    (by simpa using xiCopy_sub_real_ne_zero q 2))

/-- The doubled-rate resolvent is regular at the fundamental eigenvalue, on the `−` branch. -/
theorem physicalEigenvalue_resonance_minus_ne_zero (q : XiZeroCopy) :
    physicalEigenvalue q - (2 * (-(q.1 : ℂ) - 1) + 1) * (2 * (-(q.1 : ℂ) - 1) + 2) ≠ 0 := by
  rw [show physicalEigenvalue q - (2 * (-(q.1 : ℂ) - 1) + 1) * (2 * (-(q.1 : ℂ) - 1) + 2) =
      -3 * ((q.1 : ℂ) * ((q.1 : ℂ) + 1)) by unfold physicalEigenvalue; ring]
  exact mul_ne_zero (by norm_num) (mul_ne_zero (by simpa using xiCopy_sub_real_ne_zero q 0)
    (by simpa using xiCopy_add_real_ne_zero q 1))

/-- Vector–vector normalizable coefficient on the `+` branch: `(2/3)(ρ−2)(4ρ+3)`. -/
theorem vvLaurentMasterA_physical_plus (q : XiZeroCopy) :
    vvLaurentMasterA (physicalRate q true) (physicalEigenvalue q) =
      2 / 3 * ((q.1 : ℂ) - 2) * (4 * (q.1 : ℂ) + 3) := by
  rw [vvLaurentMasterA_eq _ _ (two_sub_physicalEigenvalue_ne_zero q)]
  simp only [physicalRate, if_true]
  rw [div_eq_iff (physicalEigenvalue_resonance_plus_ne_zero q)]
  unfold physicalEigenvalue
  ring

/-- Vector–vector normalizable coefficient on the `−` branch: `(2/3)(ρ+1)(4ρ−7)`. -/
theorem vvLaurentMasterA_physical_minus (q : XiZeroCopy) :
    vvLaurentMasterA (physicalRate q false) (physicalEigenvalue q) =
      2 / 3 * ((q.1 : ℂ) + 1) * (4 * (q.1 : ℂ) - 7) := by
  rw [vvLaurentMasterA_eq _ _ (two_sub_physicalEigenvalue_ne_zero q)]
  simp only [physicalRate, Bool.false_eq_true, if_false]
  rw [div_eq_iff (physicalEigenvalue_resonance_minus_ne_zero q)]
  unfold physicalEigenvalue
  ring

/-- The `−` branch value is the functional-equation image `ρ ↦ 1 − ρ` of the `+` branch value. -/
theorem vvLaurentMasterA_physical_reflect (q : XiZeroCopy) :
    vvLaurentMasterA (physicalRate q false) (physicalEigenvalue q) =
      2 / 3 * ((1 - (q.1 : ℂ)) - 2) * (4 * (1 - (q.1 : ℂ)) + 3) := by
  rw [vvLaurentMasterA_physical_minus]
  ring

/-- Scalar–scalar normalizable coefficient on the `+` branch: `−(5ρ−7)(ρ+2)/(2(ρ+1))`. -/
theorem laurentMasterA_physical_plus (q : XiZeroCopy) :
    laurentMasterA (physicalRate q true) (physicalEigenvalue q) =
      -((5 * (q.1 : ℂ) - 7) * ((q.1 : ℂ) + 2)) / (2 * ((q.1 : ℂ) + 1)) := by
  have hμ := two_sub_physicalEigenvalue_ne_zero q
  have hres := physicalEigenvalue_resonance_plus_ne_zero q
  have h1 : (q.1 : ℂ) + 1 ≠ 0 := by simpa using xiCopy_add_real_ne_zero q 1
  rw [laurentMasterA_resolvents _ _ hμ (by simpa [physicalRate] using hres)]
  simp only [physicalRate, if_true]
  have h2 : (2 : ℂ) - physicalEigenvalue q = -(((q.1 : ℂ) - 2) * ((q.1 : ℂ) + 1)) := by
    unfold physicalEigenvalue; ring
  have h3 : physicalEigenvalue q - (2 * ((q.1 : ℂ) - 2) + 1) * (2 * ((q.1 : ℂ) - 2) + 2) =
      -3 * (((q.1 : ℂ) - 1) * ((q.1 : ℂ) - 2)) := by unfold physicalEigenvalue; ring
  rw [h2, h3]
  have hm2 : (q.1 : ℂ) - 2 ≠ 0 := by simpa using xiCopy_sub_real_ne_zero q 2
  have hm1 : (q.1 : ℂ) - 1 ≠ 0 := by simpa using xiCopy_sub_real_ne_zero q 1
  field_simp
  ring

/-- Scalar–scalar normalizable coefficient on the `−` branch: `(5ρ+2)(ρ−3)/(2(ρ−2))`. -/
theorem laurentMasterA_physical_minus (q : XiZeroCopy) :
    laurentMasterA (physicalRate q false) (physicalEigenvalue q) =
      (5 * (q.1 : ℂ) + 2) * ((q.1 : ℂ) - 3) / (2 * ((q.1 : ℂ) - 2)) := by
  have hμ := two_sub_physicalEigenvalue_ne_zero q
  have hres := physicalEigenvalue_resonance_minus_ne_zero q
  have hm2 : (q.1 : ℂ) - 2 ≠ 0 := by simpa using xiCopy_sub_real_ne_zero q 2
  rw [laurentMasterA_resolvents _ _ hμ (by simpa [physicalRate] using hres)]
  simp only [physicalRate, Bool.false_eq_true, if_false]
  have h2 : (2 : ℂ) - physicalEigenvalue q = -(((q.1 : ℂ) - 2) * ((q.1 : ℂ) + 1)) := by
    unfold physicalEigenvalue; ring
  have h3 : physicalEigenvalue q - (2 * (-(q.1 : ℂ) - 1) + 1) * (2 * (-(q.1 : ℂ) - 1) + 2) =
      -3 * ((q.1 : ℂ) * ((q.1 : ℂ) + 1)) := by unfold physicalEigenvalue; ring
  rw [h2, h3]
  have h1 : (q.1 : ℂ) + 1 ≠ 0 := by simpa using xiCopy_add_real_ne_zero q 1
  have h0 : (q.1 : ℂ) ≠ 0 := by simpa using xiCopy_sub_real_ne_zero q 0
  field_simp
  ring

/-- The scalar–scalar `−` branch value is the functional-equation image of the `+` branch value. -/
theorem laurentMasterA_physical_reflect (q : XiZeroCopy) :
    laurentMasterA (physicalRate q false) (physicalEigenvalue q) =
      -((5 * (1 - (q.1 : ℂ)) - 7) * ((1 - (q.1 : ℂ)) + 2)) / (2 * ((1 - (q.1 : ℂ)) + 1)) := by
  rw [laurentMasterA_physical_minus]
  have hm2 : (q.1 : ℂ) - 2 ≠ 0 := by simpa using xiCopy_sub_real_ne_zero q 2
  have h2' : (2 : ℂ) * ((1 - (q.1 : ℂ)) + 1) ≠ 0 := by
    rw [show (2 : ℂ) * ((1 - (q.1 : ℂ)) + 1) = -(2 * ((q.1 : ℂ) - 2)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero hm2)
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero hm2) h2']
  ring

end
end RHTower.D4BMScalarStream
