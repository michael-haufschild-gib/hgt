import GaloisForLFunctions.HTGeometry.AnalyticGermUnit

/-!
# Making a germ regular in the distinguished coordinate

Every nonzero germ is regular along some line.  A linear automorphism of `ℂ^(n+1)` carries that
line to the first coordinate axis, so after a linear change of coordinates the germ is regular in
the distinguished variable and a Weierstrass preparation can be set up.

The automorphism is elementary: a transposition of coordinates brings a nonzero component of the
direction into the first slot, and a shear `w ↦ w + w₀ · c` with `c₀ = 0` — whose inverse is
`w ↦ w − w₀ · c` — moves the first axis onto the rescaled direction.  No basis extension is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {n : ℕ}

/-- The shear adding a multiple of the first coordinate. -/
def shearLinearEquiv (c : Fin (n + 1) → ℂ) (hc : c 0 = 0) :
    (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun w := w + (w 0) • c
  invFun w := w - (w 0) • c
  map_add' u w := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' a w := by
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv w := by
    funext i
    have h0 : (w + (w 0) • c) 0 = w 0 := by
      simp [hc]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0]
    ring
  right_inv w := by
    funext i
    have h0 : (w - (w 0) • c) 0 = w 0 := by
      simp [hc]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h0]
    ring

@[simp]
theorem shearLinearEquiv_apply (c : Fin (n + 1) → ℂ) (hc : c 0 = 0) (w : Fin (n + 1) → ℂ) :
    shearLinearEquiv c hc w = w + (w 0) • c := rfl

/-- Permuting the coordinates. -/
def permLinearEquiv (σ : Equiv.Perm (Fin (n + 1))) :
    (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun w := w ∘ σ
  invFun w := w ∘ σ.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv w := by
    funext i
    simp [Function.comp]
  right_inv w := by
    funext i
    simp [Function.comp]

@[simp]
theorem permLinearEquiv_apply (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → ℂ) :
    permLinearEquiv σ w = w ∘ σ := rfl

theorem cons_zero_eq_smul (z : ℂ) :
    (Fin.cons z (0 : Fin n → ℂ) : Fin (n + 1) → ℂ)
      = z • (Fin.cons 1 (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp

/-- **A nonzero germ becomes regular in the distinguished coordinate after a linear change of
coordinates.** -/
theorem exists_regular_coordinate_change {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) (hne : ¬ f =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] 0) :
    ∃ L : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ),
      ¬ (fun z : ℂ => f (L (Fin.cons z (0 : Fin n → ℂ)))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
  classical
  have hcons0 : (Fin.cons (0 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) = 0 := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  by_cases hf0 : f (0 : Fin (n + 1) → ℂ) ≠ 0
  · refine ⟨LinearEquiv.refl ℂ _, ?_⟩
    intro hz
    have hval := hz.self_of_nhds
    simp only [LinearEquiv.refl_apply, Pi.zero_apply, hcons0] at hval
    exact hf0 hval
  rw [not_not] at hf0
  obtain ⟨v, hv⟩ := exists_regular_direction hf hne
  have hvne : v ≠ 0 := by
    intro h
    refine hv ?_
    filter_upwards with t
    show f (lineMap (0 : Fin (n + 1) → ℂ) v t) = 0
    rw [lineMap, h]
    simpa using hf0
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), v i ≠ 0 := by
    by_contra hc
    exact hvne (funext fun i => by simpa using not_not.mp (fun h => hc ⟨i, h⟩))
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i with hσ
  set u : Fin (n + 1) → ℂ := (v i)⁻¹ • (v ∘ σ) with hu
  have hu0 : u 0 = 1 := by
    rw [hu]
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, hσ, Equiv.swap_apply_left]
    exact inv_mul_cancel₀ hi
  set c : Fin (n + 1) → ℂ := u - (Fin.cons 1 (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) with hc
  have hc0 : c 0 = 0 := by
    rw [hc]
    simp [hu0]
  refine ⟨(shearLinearEquiv c hc0).trans (permLinearEquiv σ), ?_⟩
  intro hzero
  refine hv ?_
  -- transport the vanishing back along the nonzero rescaling
  have hstep : ∀ z : ℂ,
      (permLinearEquiv σ) ((shearLinearEquiv c hc0) (Fin.cons z (0 : Fin n → ℂ)))
        = ((v i)⁻¹ * z) • v := by
    intro z
    have h1 : (shearLinearEquiv c hc0) (Fin.cons z (0 : Fin n → ℂ)) = z • u := by
      rw [shearLinearEquiv_apply, Fin.cons_zero, hc, cons_zero_eq_smul]
      module
    rw [h1]
    funext j
    simp only [permLinearEquiv_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, hu]
    rw [hσ]
    simp only [Equiv.swap_apply_self]
    ring
  have hscale : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), f (((v i)⁻¹ * s) • v) = 0 := by
    filter_upwards [hzero] with z hz
    rw [← hstep z]
    exact hz
  have hcont : Filter.Tendsto (fun t : ℂ => (v i) * t) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have h := (continuous_const_mul (v i)).tendsto (0 : ℂ)
    simpa using h
  filter_upwards [hcont.eventually hscale] with t ht
  have hrw : ((v i)⁻¹ * ((v i) * t)) = t := by
    field_simp
  rw [hrw] at ht
  show f (lineMap (0 : Fin (n + 1) → ℂ) v t) = 0
  rw [lineMap]
  simpa using ht

end GaloisForLFunctions.HTGeometry
