import GaloisForLFunctions.BiarithmeticGaugeGeometry.TheQuantizationOfTheSquareRootSurplus

/-!
# The Central Ceiling Transfers to Factors

`CentralVanishingCeiling γ` bounds the central order of every member of
`HeightCoupledSystem 2 1 1 γ` by that of `Λ_γ`, which is `2 ord_{½+iγ} ξ`. A member whose completion
splits off powers of the completed zeta function, `Λ = (2ξ)^k Λ_G`, passes the bound to the
cofactor `Λ_G`, because `ξ(½) ≠ 0`.

* **Transfer (`centralOrder_factor_le_of_ceiling`).** Under the ceiling,
  `ord_{½} Λ_G ≤ 2 ord_{½+iγ} ξ` for every such factorization.
* **Non-vanishing (`factor_ne_zero_of_ceiling`).** If moreover `ξ(½ + iγ) ≠ 0`, then `Λ_G(½) ≠ 0`.
* **Witnesses (`IsCentralCeilingWitness`, `centralVanishingCeiling_iff_forall_not_witness`).** The
  ceiling fails exactly when some member has a cofactor `Λ_G` exceeding `2 ord_{½+iγ} ξ` at the
  centre.

For a Rankin–Selberg function `L(s, u × ū) = ζ(s) L(s, sym² u)` of a level-one Maass form, the
completion would have this shape with `k = 1` and `Λ_G` the completed `L(s, sym² u)`; then the
ceiling would bound `ord_{½} L(s, sym² u)`. Neither the existence of such forms nor the analytic
theory of these `L`-functions is formalized; the theorems here are the unconditional implications.
-/

open Complex Filter Topology Set

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing

/-- A factor `(2ξ)^k` does not change the central order: `ord_{½} ((2ξ)^k Λ_G) = ord_{½} Λ_G`. -/
theorem centralOrder_xi_pow_mul {Λ_G : ℂ → ℂ} (hG : Differentiable ℂ Λ_G) (k : ℕ) :
    analyticOrderAt (fun s => (2 * RHTower.xi s) ^ k * Λ_G s) (1 / 2) =
      analyticOrderAt Λ_G (1 / 2) := by
  have hZ := completedPositiveSystem_riemannZeta
  have hξ : (2 * RHTower.xi (1 / 2)) ^ k ≠ 0 :=
    pow_ne_zero k (mul_ne_zero two_ne_zero (by simpa using RHTower.xi_ne_zero_of_real (1 / 2)))
  have hξan : AnalyticAt ℂ (fun s => (2 * RHTower.xi s) ^ k) (1 / 2) :=
    (hZ.entire_Λ.analyticAt _).pow k
  rw [show (fun s => (2 * RHTower.xi s) ^ k * Λ_G s) =
      (fun s => (2 * RHTower.xi s) ^ k) * Λ_G from rfl,
    analyticOrderAt_mul hξan (hG.analyticAt _), hξan.analyticOrderAt_eq_zero.mpr hξ, zero_add]

/-- **The ceiling transfers to factors.** If `CentralVanishingCeiling γ` holds and a member of
`HeightCoupledSystem 2 1 1 γ` has completion `Λ = (2ξ)^k Λ_G` with `Λ_G` entire, then
`ord_{½} Λ_G ≤ 2 ord_{½+iγ} ξ`. -/
theorem centralOrder_factor_le_of_ceiling {γ : ℝ} (hceil : CentralVanishingCeiling γ)
    {F Λ Λ_G : ℂ → ℂ} (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {k : ℕ}
    (hG : Differentiable ℂ Λ_G) (hfac : ∀ s, Λ s = (2 * RHTower.xi s) ^ k * Λ_G s) :
    (analyticOrderAt Λ_G (1 / 2)).toNat ≤
      2 * (analyticOrderAt (fun s => 2 * RHTower.xi s) (1 / 2 + (γ : ℂ) * I)).toNat := by
  have h := hceil F Λ hHC
  rw [show Λ = fun s => (2 * RHTower.xi s) ^ k * Λ_G s from funext hfac,
    centralOrder_xi_pow_mul hG k, centralOrder_heightCoupledΛ γ] at h
  exact h

/-- **Non-vanishing consequence.** If `CentralVanishingCeiling γ` holds and `ξ(½ + iγ) ≠ 0`, every
cofactor `Λ_G` of a member with completion `(2ξ)^k Λ_G` is nonzero at the centre. -/
theorem factor_ne_zero_of_ceiling {γ : ℝ} (hceil : CentralVanishingCeiling γ)
    (hγ : RHTower.xi (1 / 2 + (γ : ℂ) * I) ≠ 0) {F Λ Λ_G : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {k : ℕ} (hG : Differentiable ℂ Λ_G)
    (hfac : ∀ s, Λ s = (2 * RHTower.xi s) ^ k * Λ_G s) : Λ_G (1 / 2) ≠ 0 := by
  have hZ := completedPositiveSystem_riemannZeta
  have h := centralOrder_factor_le_of_ceiling hceil hHC hG hfac
  rw [(hZ.entire_Λ.analyticAt _).analyticOrderAt_eq_zero.mpr
    (mul_ne_zero two_ne_zero hγ)] at h
  have hord : analyticOrderAt Λ (1 / 2) = analyticOrderAt Λ_G (1 / 2) := by
    rw [show Λ = fun s => (2 * RHTower.xi s) ^ k * Λ_G s from funext hfac]
    exact centralOrder_xi_pow_mul hG k
  have hne : analyticOrderAt Λ_G (1 / 2) ≠ ⊤ := hord ▸ hHC.orderAt_ne_top _
  have h0 : (analyticOrderAt Λ_G (1 / 2)).toNat = 0 := by simpa using h
  have hz : analyticOrderAt Λ_G (1 / 2) = 0 := by
    rw [← ENat.coe_toNat hne, h0]
    rfl
  exact (hG.analyticAt _).analyticOrderAt_eq_zero.mp hz

/-- A **central ceiling witness** at `γ`: a member of `HeightCoupledSystem 2 1 1 γ` whose completion
is `(2ξ)^k Λ_G` with `Λ_G` entire and `ord_{½} Λ_G > 2 ord_{½+iγ} ξ`. -/
def IsCentralCeilingWitness (γ : ℝ) (k : ℕ) (Λ_G : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ_G ∧ (∃ F Λ : ℂ → ℂ, HeightCoupledSystem 2 1 1 γ F Λ ∧
    ∀ s, Λ s = (2 * RHTower.xi s) ^ k * Λ_G s) ∧
    2 * (analyticOrderAt (fun s => 2 * RHTower.xi s) (1 / 2 + (γ : ℂ) * I)).toNat <
      (analyticOrderAt Λ_G (1 / 2)).toNat

/-- **The ceiling fails exactly at a witness.** `CentralVanishingCeiling γ` holds iff no cofactor of
any power of `2ξ` in any member exceeds `2 ord_{½+iγ} ξ` at the centre. -/
theorem centralVanishingCeiling_iff_forall_not_witness (γ : ℝ) :
    CentralVanishingCeiling γ ↔ ∀ k Λ_G, ¬ IsCentralCeilingWitness γ k Λ_G := by
  constructor
  · rintro hceil k Λ_G ⟨hG, ⟨F, Λ, hHC, hfac⟩, hlt⟩
    exact absurd (centralOrder_factor_le_of_ceiling hceil hHC hG hfac) (not_le.mpr hlt)
  · intro hno F Λ hHC
    by_contra hgt
    push Not at hgt
    rw [centralOrder_heightCoupledΛ γ] at hgt
    exact hno 0 Λ ⟨hHC.entire_Λ, ⟨F, Λ, hHC, fun s => by simp⟩, hgt⟩

end GaloisForLFunctions.BiarithmeticGaugeGeometry
