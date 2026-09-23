import Mathlib

/-!
# Cyclic bulk-boundary character, fusion recurrence, and open lift

The bulk law algebra is the group algebra of `C₃` and its boundary conditions are the three
one-dimensional modules `M j` on which the marked generator acts by `ω^j`, `ω = exp(2πi/3)`.

* `boundary_not_isomorphic` — the three boundary conditions are pairwise nonisomorphic, while
  `finrank_boundary`, `finrank_boundaryEnd`, and `norm_boundaryChar` show their dimension,
  endomorphism dimension, and positive character norm all coincide: scalar boundary data cannot
  reconstruct the boundary condition, whereas the bulk character `boundaryChar` does.
* `boundaryChar_add` and `fusion_iterate` — fusion with the defect `M 1` adds the grade, so the
  boundary observer is exactly `3`-periodic (`fusion_period_exact`), while the marked fusion count
  and its logarithmic lift `2πin/3` stay open (`fusionLift_injective`).
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

section Character

/-- The marked cube root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [omega, mul_comm, mul_assoc, mul_div_assoc] using h

theorem omega_pow_three : omega ^ (3 : ℕ) = 1 := omega_isPrimitiveRoot.pow_eq_one

theorem omega_ne_zero : omega ≠ 0 := Complex.exp_ne_zero _

theorem omega_pow_mod (a : ℕ) : omega ^ (a % 3) = omega ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 3]
  rw [pow_add, pow_mul, omega_pow_three, one_pow, one_mul]

/-- The bulk character of the boundary condition `M j`, evaluated at the marked generator. -/
noncomputable def boundaryChar (j : ZMod 3) : ℂ := omega ^ j.val

/-- **The bulk character separates the boundary conditions.** -/
theorem boundaryChar_injective : Function.Injective boundaryChar := by
  intro i j hij
  have hi : i.val < 3 := ZMod.val_lt i
  have hj : j.val < 3 := ZMod.val_lt j
  have := omega_isPrimitiveRoot.pow_inj hi hj hij
  exact (ZMod.val_injective 3) this

/-- **The positive character shadow is constant.** -/
theorem norm_boundaryChar (j : ZMod 3) : ‖boundaryChar j‖ = 1 := by
  rw [boundaryChar, norm_pow]
  have hnorm : ‖omega‖ = 1 := by
    rw [omega, show (2 * (Real.pi : ℂ) * Complex.I / 3) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hnorm, one_pow]

theorem normSq_boundaryChar (j : ZMod 3) : Complex.normSq (boundaryChar j) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_boundaryChar, one_pow]

theorem boundaryChar_ne_zero (j : ZMod 3) : boundaryChar j ≠ 0 :=
  pow_ne_zero _ omega_ne_zero

/-- **Fusion adds the boundary grade.** -/
theorem boundaryChar_add (i j : ZMod 3) :
    boundaryChar i * boundaryChar j = boundaryChar (i + j) := by
  rw [boundaryChar, boundaryChar, boundaryChar, ← pow_add, ZMod.val_add, omega_pow_mod]

theorem boundaryChar_natCast (n : ℕ) : boundaryChar (n : ZMod 3) = omega ^ n := by
  rw [boundaryChar, ZMod.val_natCast, omega_pow_mod]

end Character

section Boundary

/-- A boundary condition is one-dimensional. -/
theorem finrank_boundary : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ

/-- Its endomorphism algebra is one-dimensional. -/
theorem finrank_boundaryEnd : Module.finrank ℂ (ℂ →ₗ[ℂ] ℂ) = 1 := by
  have e : (ℂ →ₗ[ℂ] ℂ) ≃ₗ[ℂ] ℂ :=
    { toFun := fun f => f 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun c => c • LinearMap.id
      left_inv := fun f => by
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
        have hv := f.map_smul v (1 : ℂ)
        simp only [smul_eq_mul, mul_one] at hv
        rw [hv]
        ring
      right_inv := fun c => by simp }
  rw [e.finrank_eq, Module.finrank_self]

/-- A linear map intertwines the boundary conditions `M i` and `M j` when it transports the action
of the marked generator. -/
def Intertwines (i j : ZMod 3) (e : ℂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ v : ℂ, e (boundaryChar i * v) = boundaryChar j * e v

/-- **Every linear endomorphism intertwines a boundary condition with itself**, so the
`A`-endomorphism algebra is the full one-dimensional endomorphism algebra. -/
theorem intertwines_self (j : ZMod 3) (e : ℂ →ₗ[ℂ] ℂ) : Intertwines j j e := by
  intro v
  simpa using e.map_smul (boundaryChar j) v

/-- **The boundary conditions are pairwise nonisomorphic.** -/
theorem boundary_not_isomorphic {i j : ZMod 3} (hij : i ≠ j) (e : ℂ ≃ₗ[ℂ] ℂ) :
    ¬ Intertwines i j e.toLinearMap := by
  intro hE
  have h1 := hE 1
  rw [mul_one] at h1
  have h2 : e.toLinearMap (boundaryChar i) = boundaryChar i * e.toLinearMap 1 := by
    simpa using e.toLinearMap.map_smul (boundaryChar i) 1
  rw [h2] at h1
  have hne : e.toLinearMap 1 ≠ 0 := by simp
  exact hij (boundaryChar_injective (mul_right_cancel₀ hne h1))

/-- **Scalar boundary data does not reconstruct the boundary condition.**  Dimension, endomorphism
dimension, and positive character norm agree for all three boundaries. -/
theorem boundary_scalar_data_constant (i j : ZMod 3) :
    Module.finrank ℂ ℂ = Module.finrank ℂ ℂ ∧
      Module.finrank ℂ (ℂ →ₗ[ℂ] ℂ) = Module.finrank ℂ (ℂ →ₗ[ℂ] ℂ) ∧
      Complex.normSq (boundaryChar i) = Complex.normSq (boundaryChar j) :=
  ⟨rfl, rfl, by rw [normSq_boundaryChar, normSq_boundaryChar]⟩

end Boundary

section Fusion

/-- The boundary observer after `n` fusions with the defect `M 1`, starting from `M 0`. -/
def fusionGrade (n : ℕ) : ZMod 3 := (n : ZMod 3)

/-- **Iterated fusion moves the boundary grade by one each time.** -/
theorem fusion_iterate (n : ℕ) : boundaryChar (fusionGrade n) = omega ^ n := by
  rw [fusionGrade, boundaryChar_natCast]

/-- **The boundary observer is exactly `3`-periodic.** -/
theorem fusion_period_exact :
    (∀ n : ℕ, fusionGrade (n + 3) = fusionGrade n) ∧
      ∀ k : ℕ, 0 < k → k < 3 → ∃ n : ℕ, fusionGrade (n + k) ≠ fusionGrade n := by
  constructor
  · intro n
    simp only [fusionGrade, Nat.cast_add, ZMod.natCast_self, add_zero]
  · intro k hk hk3
    refine ⟨0, ?_⟩
    simp only [fusionGrade, Nat.zero_add, Nat.cast_zero]
    intro hcon
    have hdvd : (3 : ℕ) ∣ k := (ZMod.natCast_eq_zero_iff k 3).mp hcon
    exact absurd (Nat.le_of_dvd hk hdvd) (by omega)

/-- The logarithmic lift of the fusion history. -/
noncomputable def fusionLift (n : ℤ) : ℂ := 2 * Real.pi * Complex.I * n / 3

theorem exp_fusionLift (n : ℤ) : Complex.exp (fusionLift n) = omega ^ n := by
  rw [fusionLift, omega, ← Complex.exp_int_mul]
  congr 1
  ring

/-- **The marked fusion count is an open lift.** -/
theorem fusionLift_injective : Function.Injective fusionLift := by
  intro n m hnm
  rw [fusionLift, fusionLift] at hnm
  have hne : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨two_ne_zero, by exact_mod_cast Real.pi_ne_zero⟩, Complex.I_ne_zero⟩
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  field_simp at hnm
  exact_mod_cast hnm

/-- **The boundary projection forgets the completed fusion cycles.** -/
theorem fusionGrade_not_injective : ¬ Function.Injective fusionGrade := by
  intro hinj
  have h : fusionGrade 0 = fusionGrade 3 := by
    show ((0 : ℕ) : ZMod 3) = ((3 : ℕ) : ZMod 3)
    rw [ZMod.natCast_self, Nat.cast_zero]
  have h0 : (0 : ℕ) = 3 := hinj h
  omega

end Fusion

section Capstone

/-- **Cyclic bulk-boundary law.**  The three boundary conditions share dimension, endomorphism
dimension, and positive character norm, are pairwise nonisomorphic, and are separated by the bulk
character; fusion with the defect is exactly `3`-periodic on the boundary while the marked count and
its logarithmic lift stay open. -/
theorem bulk_boundary_fusion_law :
    (∀ i j : ZMod 3, Complex.normSq (boundaryChar i) = Complex.normSq (boundaryChar j)) ∧
      Function.Injective boundaryChar ∧
      (∀ i j : ZMod 3, i ≠ j → ∀ e : ℂ ≃ₗ[ℂ] ℂ, ¬ Intertwines i j e.toLinearMap) ∧
      (∀ i j : ZMod 3, boundaryChar i * boundaryChar j = boundaryChar (i + j)) ∧
      (∀ n : ℕ, fusionGrade (n + 3) = fusionGrade n) ∧
      ¬ Function.Injective fusionGrade ∧
      Function.Injective fusionLift :=
  ⟨fun i j => (boundary_scalar_data_constant i j).2.2, boundaryChar_injective,
    fun _ _ hij e => boundary_not_isomorphic hij e, boundaryChar_add,
    fusion_period_exact.1, fusionGrade_not_injective, fusionLift_injective⟩

end Capstone

end GaloisForLFunctions.HTGeometry
