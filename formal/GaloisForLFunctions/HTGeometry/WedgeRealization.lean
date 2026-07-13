import GaloisForLFunctions.HTGeometry.TranscendentalPowerIndependence

/-!
# The dimension-two periodic-pencil realization of a simplex-boundary wedge

For a transcendental `τ`, the translation vectors of the wedge `∂σ^r ∧ ∂σ^s` in `ℂ²`

`a₀ = (τ^s, τ^r)`,   `a_{xᵢ} = (0, τ^i)` (`i < r`),   `a_{yⱼ} = (τ^j, 0)` (`j < s`)

are `ℚ`-linearly independent (`wedge_realization_linearIndependent`).  The first coordinate is a
`ℚ`-combination of distinct powers `τ^0,…,τ^{s-1}, τ^s`, so transcendence kills the `a₀` and
`y`-coefficients; the second coordinate then kills the `x`-coefficients.  This realizes the
periodic-pencil dimension of the wedge in dimension two.
-/

open Finset

namespace GaloisForLFunctions

/-- A `ℚ`-combination of distinct powers of a transcendental number vanishes only trivially. -/
theorem transcendental_pow_combination_eq_zero {ι : Type*} [Fintype ι] {τ : ℂ}
    (hτ : Transcendental ℚ τ) {p : ι → ℕ} (hp : Function.Injective p) (g : ι → ℚ)
    (h : ∑ i, g i • (τ ^ p i) = 0) : ∀ i, g i = 0 :=
  Fintype.linearIndependent_iff.mp (transcendental_pow_comp_linearIndependent hτ hp) g h

/-- The translation vectors `a₀, a_{xᵢ}, a_{yⱼ}` of the wedge `∂σ^r ∧ ∂σ^s`. -/
noncomputable def wedgeVec (τ : ℂ) (r s : ℕ) : Option (Fin r ⊕ Fin s) → ℂ × ℂ
  | none => (τ ^ s, τ ^ r)
  | some (Sum.inl i) => (0, τ ^ (i : ℕ))
  | some (Sum.inr j) => (τ ^ (j : ℕ), 0)

/-- **Wedge realization independence.**  For transcendental `τ`, the wedge translation vectors are
`ℚ`-linearly independent in `ℂ²`. -/
theorem wedge_realization_linearIndependent {τ : ℂ} (hτ : Transcendental ℚ τ) (r s : ℕ) :
    LinearIndependent ℚ (wedgeVec τ r s) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- first coordinate: g none • τ^s + ∑_j g (inr j) • τ^j = 0
  have hfst : g none • (τ ^ s) + ∑ j : Fin s, g (some (Sum.inr j)) • (τ ^ (j : ℕ)) = 0 := by
    have h := congrArg Prod.fst hg
    simp only [Prod.fst_sum, Prod.smul_fst, Prod.fst_zero, Prod.fst_add, Fintype.sum_option,
      Fintype.sum_sum_type, wedgeVec, smul_zero, Finset.sum_const_zero, zero_add] at h
    exact h
  -- reindex first coord as powers over Option (Fin s):  none ↦ s,  inr j ↦ j
  set p₁ : Option (Fin s) → ℕ := fun o => o.elim s (fun j => (j : ℕ)) with hp₁
  have hp₁inj : Function.Injective p₁ := by
    rintro (_ | a) (_ | b) hab <;> simp_all <;> omega
  set g₁ : Option (Fin s) → ℚ := fun o => o.elim (g none) (fun j => g (some (Sum.inr j))) with hg₁
  have hcomb₁ : ∑ o : Option (Fin s), g₁ o • (τ ^ p₁ o) = 0 := by
    rw [Fintype.sum_option]; simpa [hg₁, hp₁] using hfst
  have hz₁ := transcendental_pow_combination_eq_zero hτ hp₁inj g₁ hcomb₁
  have hnone : g none = 0 := by have := hz₁ none; simpa [hg₁] using this
  have hyj : ∀ j, g (some (Sum.inr j)) = 0 := fun j => by
    have := hz₁ (some j); simpa [hg₁] using this
  -- second coordinate with g none = 0: ∑_i g (inl i) • τ^i = 0
  have hsnd : ∑ i : Fin r, g (some (Sum.inl i)) • (τ ^ (i : ℕ)) = 0 := by
    have h := congrArg Prod.snd hg
    simp only [Prod.snd_sum, Prod.smul_snd, Prod.snd_zero, Prod.snd_add, Fintype.sum_option,
      Fintype.sum_sum_type, wedgeVec, smul_zero, Finset.sum_const_zero, add_zero] at h
    rw [hnone, zero_smul, zero_add] at h
    exact h
  set p₂ : Fin r → ℕ := fun i => (i : ℕ) with hp₂
  have hp₂inj : Function.Injective p₂ := fun a b h => Fin.ext h
  have hz₂ := transcendental_pow_combination_eq_zero hτ hp₂inj
    (fun i => g (some (Sum.inl i))) hsnd
  intro o
  rcases o with _ | (a | b)
  · exact hnone
  · exact hz₂ a
  · exact hyj b

end GaloisForLFunctions
