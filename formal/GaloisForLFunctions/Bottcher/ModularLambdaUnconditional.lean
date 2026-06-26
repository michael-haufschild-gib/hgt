/-
# The modular `λ` generator-relations, now unconditional

`ModularLambdaModular.lean` proved the anharmonic / `Γ(2)` generator relations for the modular
`λ = (θ₂/θ₃)⁴` **conditional** on the Jacobi quartic identity `F(τ) = θ₃⁴−θ₂⁴−θ₄⁴ = 0`. That identity
is now a theorem (`Bottcher2Cusp.quarticDefect_eq_zero`, via `F² ∈ S₄(SL(2,ℤ)) = 0`), so every `hF`
hypothesis is discharged here. The results below are the unconditional **deck-group action data**:

* `modularLambda_S'      : λ(−1/τ) = 1 − λ(τ)`           — the `S` involution `λ ↦ 1−λ`.
* `modularLambda_T_mul'`, `modularLambda_T_eq'` : the `T`-action `λ ↦ λ/(λ−1)` (cleared / divided).
* `modularLambda_anharmonic' : (S) ∧ (T²)`               — the two `Γ(2)`-Hauptmodul relations.
* `modularLambda_at_I'   : λ(I) = 1/2`                   — value at the `S`-fixed point.

These exhibit `λ` as the `Γ(2)` Hauptmodul with the full anharmonic `S₃` action on its values — the
covering-deck data feeding `IsCoveringMap λ` (onto `ℂ∖{0,1}`) in the three-value Montel lane.

Consumes `QuarticModularForm` (the proven identity) + `ModularLambdaModular` (the conditional laws).
-/
import GaloisForLFunctions.Bottcher.QuarticModularForm
import GaloisForLFunctions.Bottcher.ModularLambdaModular
import GaloisForLFunctions.Bottcher.Gamma2Generators

open Complex Matrix ModularGroup CongruenceSubgroup
open scoped MatrixGroups

namespace Bottcher

/-- **`λ(−1/τ) = 1 − λ(τ)`** unconditionally — the `S` involution of the anharmonic group. The Jacobi
quartic identity is now proven, so `modularLambda_S_eq_one_sub`'s hypothesis is discharged. -/
theorem modularLambda_S' {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda (-1 / τ) = 1 - modularLambda τ :=
  modularLambda_S_eq_one_sub hτ (Bottcher2Cusp.quarticDefect_eq_zero hτ)

/-- **`λ(τ+1)·(λ(τ)−1) = λ(τ)`** unconditionally — the cleared `T`-action `λ ↦ λ/(λ−1)`. -/
theorem modularLambda_T_mul' {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda (τ + 1) * (modularLambda τ - 1) = modularLambda τ :=
  modularLambda_T_mul hτ (Bottcher2Cusp.quarticDefect_eq_zero hτ)

/-- **`λ(τ+1) = λ(τ)/(λ(τ)−1)`** unconditionally — the divided `T`-action (`λ ≠ 1` makes the
denominator nonzero). -/
theorem modularLambda_T_eq' {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda (τ + 1) = modularLambda τ / (modularLambda τ - 1) :=
  modularLambda_T_eq hτ (Bottcher2Cusp.quarticDefect_eq_zero hτ)

/-- **The two `Γ(2)`-Hauptmodul relations** unconditionally: the `S` involution `λ ↦ 1−λ` and the
`T²` translation invariance `λ(τ+2) = λ(τ)`. Together they realise `λ` as the `Γ(2)` Hauptmodul. -/
theorem modularLambda_anharmonic' {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda (-1 / τ) = 1 - modularLambda τ ∧ modularLambda (τ + 2) = modularLambda τ :=
  modularLambda_anharmonic_S hτ (Bottcher2Cusp.quarticDefect_eq_zero hτ)

/-- **`λ(I) = 1/2`** unconditionally — the value at the `S`-fixed point `τ = I` (`−1/I = I`), from
the involution `λ(−1/τ) = 1 − λ(τ)` at `I`: `λ(I) = 1 − λ(I)`. -/
theorem modularLambda_at_I' : modularLambda I = 1 / 2 :=
  modularLambda_at_I (Bottcher2Cusp.quarticDefect_eq_zero (by simp : (0 : ℝ) < I.im))

/-- **`λ(τ/(2τ+1)) = λ(τ)`** unconditionally — invariance under the second `Γ(2)` generator
`R = [[1,0],[2,1]]`. -/
theorem modularLambda_Gamma2_gen' {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda (τ / (2 * τ + 1)) = modularLambda τ :=
  modularLambda_Gamma2_gen (fun σ hσ => Bottcher2Cusp.quarticDefect_eq_zero hσ) hτ

open UpperHalfPlane in
/-- **`λ` is `Γ(2)`-invariant: `λ(γ • z) = λ(z)` for every `γ ∈ Γ(2)`** (the Hauptmodul property).
By induction over the generators `Γ(2) = ⟨T², R, −I⟩` (`Gamma2_eq_closure`): `T²` is `τ ↦ τ+2`
(`modularLambda_add_two`), `R` is `τ ↦ τ/(2τ+1)` (`modularLambda_Gamma2_gen'`), `−I` acts trivially;
the group multiplication closes under the Möbius action `(x*y) • z = x • (y • z)`. This is exactly the
statement that `λ` descends to `ℍ/Γ(2)` — the analytic core of `λ : ℍ → ℂ∖{0,1}` being the `Γ(2)`
universal-cover quotient (the target `IsCoveringMap λ` of the three-value Montel lane). -/
theorem modularLambda_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma 2) (z : ℍ) :
    modularLambda ((γ • z : ℍ) : ℂ) = modularLambda (z : ℂ) := by
  rw [Gamma2_eq_closure] at hγ
  induction hγ using Subgroup.closure_induction generalizing z with
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · have hc : ((ModularGroup.T ^ 2 • z : ℍ) : ℂ) = (z : ℂ) + 2 := by
          rw [show (ModularGroup.T ^ 2 : SL(2, ℤ)) = ModularGroup.T ^ (2 : ℤ) by norm_cast,
              ModularGroup.coe_T_zpow_smul_eq]
          push_cast; ring
        rw [hc]; exact modularLambda_add_two _
      · have hc : ((Rgen • z : ℍ) : ℂ) = (z : ℂ) / (2 * (z : ℂ) + 1) := by
          rw [coe_specialLinearGroup_apply]; simp [Rgen]
        rw [hc]; exact modularLambda_Gamma2_gen' z.im_pos
      · rw [SL_neg_smul, one_smul]
  | one => rw [one_smul]
  | mul x y _ _ ihx ihy => rw [mul_smul, ihx, ihy]
  | inv x _ ih =>
      have h := ih (x⁻¹ • z)
      rw [← mul_smul, mul_inv_cancel, one_smul] at h
      exact h.symm

open UpperHalfPlane in
/-- **`λ ∘ (↑·) : ℍ → ℂ` is continuous** — `λ` is holomorphic on `ℍ`
(`differentiableAt_modularLambda_of_im_pos`) and the inclusion `ℍ ↪ ℂ` is continuous. -/
theorem continuous_modularLambda_comp : Continuous (fun z : ℍ => modularLambda (z : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hz : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos
  exact ((differentiableAt_modularLambda_of_im_pos hz).continuousAt).comp
    UpperHalfPlane.continuous_coe.continuousAt

open UpperHalfPlane in
/-- **`λ` descends to a well-defined map `ℍ/Γ(2) → ℂ`** (`λ̄`), by `Γ(2)`-invariance
(`modularLambda_smul`). This is the function half of the Hauptmodul homeomorphism `ℍ/Γ(2) ≅ ℂ∖{0,1}`
that underlies `IsCoveringMap λ` in the three-value Montel lane; the remaining (deep) halves are that
`λ̄` is injective (separates `Γ(2)`-orbits) and surjective onto `ℂ∖{0,1}`. -/
noncomputable def modularLambdaQuotient :
    Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma 2) ℍ) → ℂ :=
  Quotient.lift (fun z : ℍ => modularLambda (z : ℂ)) <| by
    rintro a b ⟨g, rfl⟩
    exact modularLambda_smul g.property b

open UpperHalfPlane in
/-- **`λ̄ : ℍ/Γ(2) → ℂ` is continuous** for the quotient topology — `λ ∘ (↑·)` is continuous and
constant on `Γ(2)`-orbits, so it descends continuously. -/
theorem continuous_modularLambdaQuotient : Continuous modularLambdaQuotient :=
  continuous_modularLambda_comp.quotient_lift _

open UpperHalfPlane in
/-- The descended map evaluated on a point: `λ̄ ⟦z⟧ = λ(z)`. -/
@[simp] theorem modularLambdaQuotient_mk (z : ℍ) :
    modularLambdaQuotient (Quotient.mk _ z) = modularLambda (z : ℂ) := rfl

end Bottcher
