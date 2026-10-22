import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonSchwartz
import GaloisForLFunctions.RHTower.Deninger.DeningerExpSchwartz

/-!
# The Poisson operator lands in the exponentially decreasing source

Meyer's space is stable under the generator `A_0 = θ` of the multiplicative flow, and every
derivative of a Poisson sum is the Poisson sum of an iterate of that generator.  So the whole
derivative tower of `Z f` is again a Poisson sum of a member of Meyer's space, and a single
exponential-weight bound at derivative order zero controls every order.

That bound is the corpus's two-sided estimate for the integer weights: the exponential weight
`e^{A|t|}` is beaten by `e^{⌈A⌉t}` on the right half line and by `e^{-⌈A⌉t}` on the left, so real
exponents cost nothing beyond the integer ones already proved.

* `deningerPoissonLog_expBound` : **the Poisson sum beats every exponential weight.**
* `deningerPoissonSource` : **`Z : H_∩ → H_-`.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- **The Poisson sum of a member of Meyer's space beats every exponential weight.** -/
theorem deningerPoissonLog_expBound {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerMeyerCap) (A : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, Real.exp (A * |t|) * ‖deningerPoissonLog h t‖ ≤ C := by
  set s : ℤ := ⌈A⌉ with hs
  have hsA : A ≤ (s : ℝ) := Int.le_ceil A
  obtain ⟨Cp, hCp⟩ := exists_bound_deningerPoissonWeight s 0 hh
  obtain ⟨Cm, hCm⟩ := exists_bound_deningerPoissonWeight (-s) 0 hh
  refine ⟨max Cp Cm, fun t => ?_⟩
  rcases le_total 0 t with ht | ht
  · have hbase := hCp t
    rw [pow_zero, one_mul, norm_deningerPoissonWeight] at hbase
    have hexp : Real.exp (A * |t|) ≤ Real.exp ((s : ℝ) * t) := by
      refine Real.exp_le_exp.mpr ?_
      rw [abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_right hsA ht
    refine le_trans ?_ (le_max_left _ _)
    exact le_trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) hbase
  · have hbase := hCm t
    rw [pow_zero, one_mul, norm_deningerPoissonWeight] at hbase
    have hexp : Real.exp (A * |t|) ≤ Real.exp (((-s : ℤ) : ℝ) * t) := by
      refine Real.exp_le_exp.mpr ?_
      rw [abs_of_nonpos ht]
      have hsneg : ((-s : ℤ) : ℝ) = -(s : ℝ) := by push_cast; ring
      rw [hsneg]
      nlinarith
    refine le_trans ?_ (le_max_right _ _)
    exact le_trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) hbase

/-- The unweighted Poisson sum is the weight at exponent zero. -/
theorem deningerPoissonWeight_zero (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deningerPoissonWeight 0 f t = deningerPoissonLog f t := by
  rw [deningerPoissonWeight, deningerExpWeight]
  norm_num

/-- **The Poisson sum lies in the exponentially decreasing source.** -/
theorem deningerPoissonSchwartz_zero_mem {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerMeyerCap) :
    deningerPoissonSchwartz 0 h hh ∈ DeningerExpSchwartz := by
  intro A n
  obtain ⟨C, hC⟩ :=
    deningerPoissonLog_expBound (deningerMeyerCap_shiftCLM_iterate hh 0 n) A
  refine ⟨C, fun t => ?_⟩
  have hcoe : ((deningerPoissonSchwartz 0 h hh : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = deningerPoissonWeight 0 h := rfl
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hcoe,
    iteratedDeriv_deningerPoissonWeight n 0 h, deningerPoissonWeight_zero]
  exact hC t

/-- **The Poisson operator `Z : H_∩ → H_-`.** -/
def deningerPoissonSource (h : DeningerMeyerCap) : DeningerExpSchwartz :=
  ⟨deningerPoissonSchwartz 0 (h : 𝓢(ℝ, ℂ)) h.2, deningerPoissonSchwartz_zero_mem h.2⟩

@[simp]
theorem deningerPoissonSource_apply (h : DeningerMeyerCap) (t : ℝ) :
    ((deningerPoissonSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = deningerPoissonLog ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) t :=
  deningerPoissonWeight_zero _ t

/-- The Poisson operator is linear. -/
def deningerPoissonSourceLM : DeningerMeyerCap →ₗ[ℂ] DeningerExpSchwartz where
  toFun := deningerPoissonSource
  map_add' f g := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    rw [Submodule.coe_add]
    show ((deningerPoissonSource (f + g) : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((deningerPoissonSource f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
        + ((deningerPoissonSource g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
    rw [deningerPoissonSource_apply, deningerPoissonSource_apply,
      deningerPoissonSource_apply]
    exact deningerPoissonLog_add _ _ t
  map_smul' c f := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    rw [RingHom.id_apply, Submodule.coe_smul]
    show ((deningerPoissonSource (c • f) : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = c • ((deningerPoissonSource f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
    rw [deningerPoissonSource_apply, deningerPoissonSource_apply, smul_eq_mul]
    exact deningerPoissonLog_smul c _ t

end

end RHTower
