import GaloisForLFunctions.RHTower.Deninger.DeningerMultiplier
import GaloisForLFunctions.RHTower.Deninger.DeningerHarmonicMode

/-!
# The boundary Hodge operator as an operator

A multiplier family of modulus exactly one is an isometry, because the coefficient sums agree term
by term.  The sign of a diagonal generator is such a family, so the boundary Hodge operator — `i`
times that sign — is an isometry of the coefficient space that squares to `-1`.

* `deningerMultiplier_norm_eq` : unimodular multipliers are isometries.
* `deningerBoundaryHodgeOperator` : the boundary Hodge operator.
* `deningerBoundaryHodgeOperator_sq` : it squares to `-1`.
* `deningerBoundaryHodgeOperator_isometry` : it is an isometry.
-/

namespace RHTower

open scoped ENNReal

section BoundaryHodgeOperator

variable {ι : Type*}

/-- **A multiplier of modulus exactly one is an isometry.** -/
theorem deningerMultiplier_norm_eq {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) (hone : ∀ i, ‖g i‖ = 1)
    (x : lp (fun _ : ι => ℂ) 2) : ‖deningerMultiplier hg x‖ = ‖x‖ := by
  have htwo : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow htwo, lp.norm_eq_tsum_rpow htwo]
  congr 1
  refine tsum_congr fun i => ?_
  rw [deningerMultiplier_apply, norm_mul, hone i, one_mul]

/-- The unimodular sign family of a diagonal generator. -/
noncomputable def deningerSignFamily (ℓ : ι → ℝ) (i : ι) : ℂ :=
  Complex.I * ((deningerFreqSign (ℓ i) : ℝ) : ℂ)

theorem deningerSignFamily_norm (ℓ : ι → ℝ) (i : ι) : ‖deningerSignFamily ℓ i‖ = 1 := by
  rw [deningerSignFamily, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, deningerFreqSign]
  split_ifs <;> norm_num

theorem deningerSignFamily_norm_le (ℓ : ι → ℝ) (i : ι) : ‖deningerSignFamily ℓ i‖ ≤ 1 :=
  le_of_eq (deningerSignFamily_norm ℓ i)

/-- **The boundary Hodge operator**: `i` times the sign of the diagonal generator. -/
noncomputable def deningerBoundaryHodgeOperator (ℓ : ι → ℝ) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  deningerMultiplier (deningerSignFamily_norm_le ℓ)

@[simp] theorem deningerBoundaryHodgeOperator_apply (ℓ : ι → ℝ)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    (deningerBoundaryHodgeOperator ℓ x : ι → ℂ) i = deningerSignFamily ℓ i * (x : ι → ℂ) i := rfl

/-- **The boundary Hodge operator squares to `-1`.** -/
theorem deningerBoundaryHodgeOperator_sq (ℓ : ι → ℝ) (x : lp (fun _ : ι => ℂ) 2) :
    deningerBoundaryHodgeOperator ℓ (deningerBoundaryHodgeOperator ℓ x) = -x := by
  refine lp.ext ?_
  funext i
  have hsq : (deningerFreqSign (ℓ i) : ℂ) * (deningerFreqSign (ℓ i) : ℂ) = 1 := by
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (deningerFreqSign_sq (ℓ i))
  show deningerSignFamily ℓ i * (deningerSignFamily ℓ i * (x : ι → ℂ) i) = -((x : ι → ℂ) i)
  rw [deningerSignFamily]
  calc Complex.I * (deningerFreqSign (ℓ i) : ℂ)
        * (Complex.I * (deningerFreqSign (ℓ i) : ℂ) * (x : ι → ℂ) i)
      = (Complex.I ^ 2) * ((deningerFreqSign (ℓ i) : ℂ) * (deningerFreqSign (ℓ i) : ℂ))
        * (x : ι → ℂ) i := by ring
    _ = -((x : ι → ℂ) i) := by rw [Complex.I_sq, hsq]; ring

/-- **The boundary Hodge operator is an isometry.** -/
theorem deningerBoundaryHodgeOperator_isometry (ℓ : ι → ℝ) (x : lp (fun _ : ι => ℂ) 2) :
    ‖deningerBoundaryHodgeOperator ℓ x‖ = ‖x‖ :=
  deningerMultiplier_norm_eq _ (deningerSignFamily_norm ℓ) x

end BoundaryHodgeOperator

end RHTower
