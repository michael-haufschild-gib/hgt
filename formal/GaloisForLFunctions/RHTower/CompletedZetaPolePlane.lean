import GaloisForLFunctions.HTGeometry.CarrierExactPositiveInertia
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The polar part of the completed zeta function is one hyperbolic pole plane

The completed zeta function is `Λ(s) = Λ₀(s) - 1/s - 1/(1-s)` with `Λ₀` entire and invariant under
`s ↦ 1 - s`.  Its polar part is therefore two simple poles, exchanged by the functional equation,
with residues `-1` at `s = 0` and `+1` at `s = 1`: the polar part is reflection-invariant while the
residue vector is reflection-odd.

The two poles are the two rulings of one hyperbolic plane: the residue pairing `!![0, 1; 1, 0]` on
the two-dimensional pole space is symmetric under the exchange of the poles and has inertia
exactly `(1, 1)`.  This is proved from the factored carrier machinery with the two vectors
`(1, 1)` and `(1, -1)`, whose factored form is twice the residue pairing.
-/

open Complex Matrix Filter Topology GaloisForLFunctions
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The polar part -/

/-- The polar part `-1/s - 1/(1-s)` of the completed zeta function. -/
def completedZetaPolarPart (s : ℂ) : ℂ := -1 / s - 1 / (1 - s)

/-- `Λ = Λ₀ + (polar part)`, with `Λ₀` entire. -/
theorem completedRiemannZeta_eq_entire_add_polar (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s + completedZetaPolarPart s := by
  rw [completedRiemannZeta_eq]
  unfold completedZetaPolarPart
  ring

/-- The polar part is invariant under the functional-equation reflection `s ↦ 1 - s`. -/
theorem completedZetaPolarPart_one_sub (s : ℂ) :
    completedZetaPolarPart (1 - s) = completedZetaPolarPart s := by
  unfold completedZetaPolarPart
  rw [sub_sub_cancel]
  ring

/-- Exact residue algebra at `s = 0`: `s · P(s) = -1 - s/(1-s)`. -/
theorem mul_completedZetaPolarPart (s : ℂ) (hs : s ≠ 0) :
    s * completedZetaPolarPart s = -1 - s / (1 - s) := by
  unfold completedZetaPolarPart
  have h1 : s * (-1 / s) = -1 := by field_simp
  have h2 : s * (1 / (1 - s)) = s / (1 - s) := by ring
  rw [mul_sub, h1, h2]

/-- Exact residue algebra at `s = 1`: `(s - 1) · P(s) = 1 - (s-1)/s`. -/
theorem sub_one_mul_completedZetaPolarPart (s : ℂ) (hs : s ≠ 1) :
    (s - 1) * completedZetaPolarPart s = 1 - (s - 1) / s := by
  unfold completedZetaPolarPart
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have h1 : (s - 1) * (1 / (1 - s)) = -1 := by
    field_simp
    ring
  have h2 : (s - 1) * (-1 / s) = -((s - 1) / s) := by ring
  rw [mul_sub, h1, h2]
  ring

/-- The residue of the polar part at `s = 0` is `-1`. -/
theorem tendsto_mul_completedZetaPolarPart_zero :
    Tendsto (fun s : ℂ => s * completedZetaPolarPart s) (𝓝[≠] 0) (𝓝 (-1)) := by
  have hcont : ContinuousAt (fun s : ℂ => -1 - s / (1 - s)) 0 := by
    apply ContinuousAt.sub continuousAt_const
    apply ContinuousAt.div continuousAt_id (continuousAt_const.sub continuousAt_id)
    norm_num
  have hlim : Tendsto (fun s : ℂ => -1 - s / (1 - s)) (𝓝 0) (𝓝 (-1)) := by
    simpa using hcont.tendsto
  refine (tendsto_nhdsWithin_of_tendsto_nhds hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (mul_completedZetaPolarPart s hs).symm

/-- The residue of the polar part at `s = 1` is `+1`. -/
theorem tendsto_sub_one_mul_completedZetaPolarPart_one :
    Tendsto (fun s : ℂ => (s - 1) * completedZetaPolarPart s) (𝓝[≠] 1) (𝓝 1) := by
  have hcont : ContinuousAt (fun s : ℂ => 1 - (s - 1) / s) 1 := by
    apply ContinuousAt.sub continuousAt_const
    apply ContinuousAt.div (continuousAt_id.sub continuousAt_const) continuousAt_id
    norm_num
  have hlim : Tendsto (fun s : ℂ => 1 - (s - 1) / s) (𝓝 1) (𝓝 1) := by
    simpa using hcont.tendsto
  refine (tendsto_nhdsWithin_of_tendsto_nhds hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (sub_one_mul_completedZetaPolarPart s hs).symm

/-! ## The pole plane -/

/-- The residue pairing of the two poles: the rulings `F₀, F₁` with `F₀² = F₁² = 0`, `F₀·F₁ = 1`. -/
def polePlaneForm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Exchanging the two poles (the functional equation) preserves the residue pairing. -/
theorem polePlaneForm_swap :
    polePlaneForm.submatrix (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
      = polePlaneForm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The `+` ruling vector `(1, 1)`. -/
def poleW : Fin 1 → (Fin 2 → ℂ) := fun _ => ![1, 1]

/-- The `−` ruling vector `(1, -1)`. -/
def poleU : Fin 1 → (Fin 2 → ℂ) := fun _ => ![1, -1]

/-- The factored form of the two ruling vectors is twice the residue pairing. -/
theorem factored_poleW_poleU :
    (∑ i, Matrix.of (fun p q => poleW i p * star (poleW i q)))
        - (∑ i, Matrix.of (fun p q => poleU i p * star (poleU i q)))
      = (2 : ℂ) • polePlaneForm := by
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [poleW, poleU, polePlaneForm]

/-- The ruling vectors are linearly independent. -/
theorem poleWU_linearIndependent : LinearIndependent ℂ (Sum.elim poleW poleU) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp [Fintype.sum_sum_type, poleW, poleU] at h0 h1
  intro i
  rcases i with i | i
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    linear_combination (h0 + h1) / 2
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    linear_combination (h0 - h1) / 2

/-- The real Krein value scales by two under `2 • M`. -/
theorem re_krein_two_smul {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) :
    (star y ⬝ᵥ ((2 : ℂ) • M).mulVec y).re = 2 * (star y ⬝ᵥ M.mulVec y).re := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp [Complex.mul_re]

/-- **The pole plane has inertia exactly `(1, 1)`.**  Every negative-definite subspace of the residue
pairing has dimension at most one and a negative line exists; every positive-definite subspace has
dimension at most one and a positive line exists. -/
theorem polePlaneForm_exact_inertia :
    ((∀ W : Submodule ℂ (Fin 2 → ℂ),
        (∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ polePlaneForm.mulVec y).re < 0)
        → Module.finrank ℂ W ≤ 1)
      ∧ (∃ W : Submodule ℂ (Fin 2 → ℂ), Module.finrank ℂ W = 1 ∧
          ∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ polePlaneForm.mulVec y).re < 0))
    ∧ ((∀ W : Submodule ℂ (Fin 2 → ℂ),
        (∀ y ∈ W, y ≠ 0 → 0 < (star y ⬝ᵥ polePlaneForm.mulVec y).re)
        → Module.finrank ℂ W ≤ 1)
      ∧ (∃ W : Submodule ℂ (Fin 2 → ℂ), Module.finrank ℂ W = 1 ∧
          ∀ y ∈ W, y ≠ 0 → 0 < (star y ⬝ᵥ polePlaneForm.mulVec y).re)) := by
  classical
  let Φ : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun y => star (poleW i) ⬝ᵥ y
      map_add' := fun a b => dotProduct_add _ a b
      map_smul' := fun c a => dotProduct_smul c _ a })
  let Ψ : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun y => star (poleU i) ⬝ᵥ y
      map_add' := fun a b => dotProduct_add _ a b
      map_smul' := fun c a => dotProduct_smul c _ a })
  have hΦ : ∀ (y : Fin 2 → ℂ) (i : Fin 1), Φ y i = star (poleW i) ⬝ᵥ y := fun y i => rfl
  have hΨ : ∀ (y : Fin 2 → ℂ) (i : Fin 1), Ψ y i = star (poleU i) ⬝ᵥ y := fun y i => rfl
  have hE := eval_surjective_rect (Sum.elim poleW poleU) poleWU_linearIndependent
  have hT : Function.Surjective (Φ.prod Ψ) := by
    intro ab
    obtain ⟨y, hy⟩ := hE (Sum.elim ab.1 ab.2)
    refine ⟨y, ?_⟩
    rw [LinearMap.prod_apply]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · have hcf := congrFun hy (Sum.inl i)
      simpa [hΦ y i] using hcf
    · have hcf := congrFun hy (Sum.inr i)
      simpa [hΨ y i] using hcf
  have hneg := exact_neg_inertia poleW poleU Φ Ψ hΦ hΨ hT
  have hpos := exact_pos_inertia poleW poleU Φ Ψ hΦ hΨ hT
  rw [factored_poleW_poleU] at hneg hpos
  have htwo_neg : ∀ x : ℝ, 2 * x < 0 ↔ x < 0 := fun x => by constructor <;> intro h <;> linarith
  have htwo_pos : ∀ x : ℝ, 0 < 2 * x ↔ 0 < x := fun x => by constructor <;> intro h <;> linarith
  simp only [re_krein_two_smul, htwo_neg, htwo_pos] at hneg hpos
  exact ⟨hneg, hpos⟩

end

end RHTower
