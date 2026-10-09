import GaloisForLFunctions.RHTower.RepCosetRepresentation

/-!
# Coset lifts with a nontrivial character are orthogonal to the invariant vectors

Let `A` normalize the finite-index subgroup `Γ`.  Right multiplication by `A` permutes the cosets
`SL(2,ℤ)/Γ` (`rightMulEquiv`).  If a `Γ`-invariant `f` picks up a factor `ω ≠ 1` under `A⁻¹`,
`f(A⁻¹w) = ω f(w)`, then the coordinates of its lift satisfy `Σ_q F_f(z)(q) = ω Σ_q F_f(z)(q)`, so they
sum to zero (`sum_cosetLift_eq_zero`).  Since the invariant vectors of the coset representation are
constant, the lift is pointwise orthogonal to them (`inner_cosetLift_eq_zero`).
-/

open UpperHalfPlane
open scoped MatrixGroups InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepCoset

noncomputable section

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

omit [Γ.FiniteIndex] in
/-- Right multiplication by an element normalizing `Γ`, on left cosets. -/
def rightMul (A : SL(2, ℤ)) (hA : ∀ γ ∈ Γ, A⁻¹ * γ * A ∈ Γ) : SL(2, ℤ) ⧸ Γ → SL(2, ℤ) ⧸ Γ :=
  Quotient.map' (fun g => g * A) fun g g' h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    have := hA _ h
    simpa [mul_assoc] using this

omit [Γ.FiniteIndex] in
theorem rightMul_mk (A : SL(2, ℤ)) (hA : ∀ γ ∈ Γ, A⁻¹ * γ * A ∈ Γ) (g : SL(2, ℤ)) :
    rightMul A hA (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) = QuotientGroup.mk (g * A) := rfl

omit [Γ.FiniteIndex] in
/-- Right multiplication by a normalizing element is a permutation of the cosets. -/
def rightMulEquiv (A : SL(2, ℤ)) (hA : ∀ γ ∈ Γ, A⁻¹ * γ * A ∈ Γ)
    (hA' : ∀ γ ∈ Γ, A * γ * A⁻¹ ∈ Γ) : (SL(2, ℤ) ⧸ Γ) ≃ (SL(2, ℤ) ⧸ Γ) where
  toFun := rightMul A hA
  invFun := rightMul A⁻¹ (by simpa using hA')
  left_inv q := by
    induction q using QuotientGroup.induction_on with
    | H g => rw [rightMul_mk, rightMul_mk, mul_inv_cancel_right]
  right_inv q := by
    induction q using QuotientGroup.induction_on with
    | H g => rw [rightMul_mk, rightMul_mk, inv_mul_cancel_right]

/-- **The coordinates of a twisted lift sum to zero.** -/
theorem sum_cosetLift_eq_zero {f : ℍ → ℂ} (hf : ∀ γ ∈ Γ, ∀ z, f (γ • z) = f z) {A : SL(2, ℤ)}
    (hA : ∀ γ ∈ Γ, A⁻¹ * γ * A ∈ Γ) (hA' : ∀ γ ∈ Γ, A * γ * A⁻¹ ∈ Γ) {ω : ℂ} (hω : ω ≠ 1)
    (hfA : ∀ w, f (A⁻¹ • w) = ω * f w) (z : ℍ) :
    ∑ q : SL(2, ℤ) ⧸ Γ, cosetLift f z q = 0 := by
  have hperm := Equiv.sum_comp (rightMulEquiv A hA hA') (fun q => cosetLift f z q)
  have hpt : ∀ q : SL(2, ℤ) ⧸ Γ, cosetLift f z (rightMulEquiv A hA hA' q) = ω * cosetLift f z q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      change cosetLift f z (rightMul A hA (QuotientGroup.mk g)) = _
      rw [rightMul_mk, cosetLift_mk hf, cosetLift_mk hf, mul_inv_rev, mul_smul, hfA]
  simp_rw [hpt, ← Finset.mul_sum] at hperm
  have h1 : (ω - 1) * ∑ q : SL(2, ℤ) ⧸ Γ, cosetLift f z q = 0 := by
    rw [sub_mul, hperm, one_mul, sub_self]
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hω)

/-- **A twisted lift is pointwise orthogonal to the invariant vectors.** -/
theorem inner_cosetLift_eq_zero {f : ℍ → ℂ} (hf : ∀ γ ∈ Γ, ∀ z, f (γ • z) = f z) {A : SL(2, ℤ)}
    (hA : ∀ γ ∈ Γ, A⁻¹ * γ * A ∈ Γ) (hA' : ∀ γ ∈ Γ, A * γ * A⁻¹ ∈ Γ) {ω : ℂ} (hω : ω ≠ 1)
    (hfA : ∀ w, f (A⁻¹ • w) = ω * f w) (z : ℍ) {c : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ)}
    (hc : ∀ B, cosetRep Γ B c = c) : ⟪c, cosetLift f z⟫_ℂ = 0 := by
  have hconst := eq_of_forall_cosetRep_eq Γ hc
  set q₀ : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk 1
  rw [PiLp.inner_apply]
  have e : ∀ q : SL(2, ℤ) ⧸ Γ, ⟪c q, cosetLift f z q⟫_ℂ = (starRingEnd ℂ) (c q₀) * cosetLift f z q := by
    intro q
    rw [hconst q q₀]
    simp [mul_comm]
  simp_rw [e]
  rw [← Finset.mul_sum, sum_cosetLift_eq_zero hf hA hA' hω hfA z, mul_zero]

end

end GaloisForLFunctions.RHTower.RepCoset
