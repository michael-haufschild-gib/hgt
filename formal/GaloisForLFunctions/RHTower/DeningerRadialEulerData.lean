import GaloisForLFunctions.RHTower.DeningerEulerStirling

/-!
# The radial data of the Euler iterates

The generator of the weighted flow is `A_τ = τ + θ`, and the weight of `A_τ f` is the derivative of
the weight of `f`.  Hence the weight of `θf` is `(D − τ)` applied to the weight of `f`, and the
weight of `θ^j f` is `(D − τ)^j` applied to it:

`Z_τ(θ^j f) = (D − τ)^j Z_τ(f)`.

Every seminorm of the radial datum of an Euler iterate is therefore bounded by finitely many
seminorms of the radial datum of `f` itself.

* `deningerMeyerCap_eulerSCLM_iterate` : Meyer's space is stable under the Euler iterates.
* `deningerPoissonSchwartz_euler_iterate` : **`Z_τ(θ^j f) = (D − τ)^j Z_τ(f)`.**
* `exists_bound_schwartzSup_euler` : **the radial data of `θ^j f` is bounded by that of `f`.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff NNReal
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## Stability of Meyer's space -/

theorem deningerMeyerCap_eulerSCLM_iterate {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) (j : ℕ) :
    ((eulerSCLM^[j]) f) ∈ DeningerMeyerCap := by
  induction j generalizing f with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (deningerMeyerCap_eulerSCLM hf)

/-! ## The weight generator of the Euler operator -/

/-- The operator `D − τ`, which the Poisson operator matches with the Euler operator on the
`τ`-th weight. -/
def deningerEulerWeightCLM (τ : ℤ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  derivSCLM - (τ : ℂ) • ContinuousLinearMap.id ℂ _

/-- **The weight of an Euler transform is `(D − τ)` applied to the weight.** -/
theorem deningerPoissonSchwartz_eulerSCLM (τ : ℤ) (g : 𝓢(ℝ, ℂ)) (hg : g ∈ DeningerMeyerCap) :
    deningerPoissonSchwartz τ (eulerSCLM g) (deningerMeyerCap_eulerSCLM hg)
      = deningerEulerWeightCLM τ (deningerPoissonSchwartz τ g hg) := by
  refine SchwartzMap.ext fun t => ?_
  have hE : eulerSCLM g = deningerShiftCLM τ g + (-(τ : ℂ)) • g := by
    rw [deningerShiftCLM_apply, neg_smul]
    abel
  have hderiv : deningerPoissonWeight τ (deningerShiftCLM τ g) t
      = deriv (deningerPoissonWeight τ g) t :=
    (congrFun (deriv_deningerPoissonWeight τ g) t).symm
  have hlhs : deningerPoissonWeight τ (eulerSCLM g) t
      = deriv (deningerPoissonWeight τ g) t + (-(τ : ℂ)) * deningerPoissonWeight τ g t := by
    rw [hE, deningerPoissonWeight_add, deningerPoissonWeight_smul, hderiv]
  show deningerPoissonWeight τ (eulerSCLM g) t
      = (derivSCLM (deningerPoissonSchwartz τ g hg)
          - ((τ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)) (deningerPoissonSchwartz τ g hg)) t
  rw [hlhs]
  simp only [_root_.sub_apply, _root_.smul_apply, derivSCLM_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  have hcoe : ((deningerPoissonSchwartz τ g hg : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = deningerPoissonWeight τ g := rfl
  rw [hcoe]
  ring

/-- The iterated weight generator. -/
def deningerEulerWeightPowCLM (τ : ℤ) : ℕ → (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ _
  | (j + 1) => (deningerEulerWeightPowCLM τ j).comp (deningerEulerWeightCLM τ)

/-- **The weight of an Euler iterate is `(D − τ)^j` applied to the weight.** -/
theorem deningerPoissonSchwartz_euler_iterate (τ : ℤ) (j : ℕ) (f : 𝓢(ℝ, ℂ))
    (hf : f ∈ DeningerMeyerCap) :
    deningerPoissonSchwartz τ ((eulerSCLM^[j]) f) (deningerMeyerCap_eulerSCLM_iterate hf j)
      = deningerEulerWeightPowCLM τ j (deningerPoissonSchwartz τ f hf) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    have hstep := ih (eulerSCLM f) (deningerMeyerCap_eulerSCLM hf)
    have hiter : ((eulerSCLM^[j + 1]) f) = (eulerSCLM^[j]) (eulerSCLM f) :=
      Function.iterate_succ_apply _ _ _
    have hleft : deningerPoissonSchwartz τ ((eulerSCLM^[j + 1]) f)
        (deningerMeyerCap_eulerSCLM_iterate hf (j + 1))
        = deningerPoissonSchwartz τ ((eulerSCLM^[j]) (eulerSCLM f))
          (deningerMeyerCap_eulerSCLM_iterate (deningerMeyerCap_eulerSCLM hf) j) := by
      congr 1
    rw [hleft, hstep, deningerPoissonSchwartz_eulerSCLM τ f hf]
    rfl

/-- **The radial data of an Euler iterate is bounded by the radial data of the function.** -/
theorem exists_bound_schwartzSup_euler (τ : ℤ) (j : ℕ) (K₀ : Finset (ℕ × ℕ)) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
      (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz τ ((eulerSCLM^[j]) f)
          (deningerMeyerCap_eulerSCLM_iterate hf j))
        ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz τ f hf) := by
  obtain ⟨K, C, hC, hb⟩ := exists_bound_schwartzSup_comp (deningerEulerWeightPowCLM τ j) K₀
  refine ⟨K, C, hC, fun f hf => ?_⟩
  rw [deningerPoissonSchwartz_euler_iterate τ j f hf]
  exact hb (deningerPoissonSchwartz τ f hf)

end RHTower

end
