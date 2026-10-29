import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectivityBatteryOnPrimeTowers
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional

/-!
# Index zero selects the von Mangoldt weight

The selection principle in index language. For a weight `λ` (prime weights on `n ≥ 2`, with the
archimedean and pole terms of `ζ`) and a prime `p`:

**Selection** (`forall_negIndex_towerKernel_eq_zero_iff`). Every tower kernel of `λ` along `p` has
index zero, for every `C²` compactly supported generator, iff RH holds and `λ = Λ` on `n ≥ 2`. One
direction reads the `1 × 1` windows, which are the Weil forms `W_λ(g ⋆ g̃)`, so the full Weil cone
`{Λ}` (under RH, empty otherwise) applies; the other is RH along one prime tower.

**Every twin carries index** (`exists_negIndex_towerKernel_ne_zero`). A weight that differs from
`Λ` at some `n ≥ 2` has, on every prime tower, a generator whose tower kernel has a negative square.
This is unconditional: no twin of `Λ`, and no `n^{−η}` perturbation, can have index zero on a whole
tower. The parity barrier has this positive form: index zero on one prime tower is a property of
`Λ` alone.
-/

open Complex
open Zeta23
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (TowerPositive lagW
  weilGram_tower_apply towerPositive_vonMangoldt_of_riemannHypothesis)
open RHTower RHTower.WeilSpectral

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

local notation "Tr" => ArithmeticCastelnuovoSeveri.translate

/-- Tower positivity transfers between weights that agree on `n ≥ 2`. -/
theorem towerPositive_congr {lam lam' : ℕ → ℝ} (h : ∀ n, 2 ≤ n → lam n = lam' n) {g : ℝ → ℂ}
    {ℓ : ℝ} (hT : TowerPositive lam g ℓ) : TowerPositive lam' g ℓ := fun K => by
  have : ArithmeticCastelnuovoSeveri.weilGram lam' (fun k : K => Tr ((k : ℤ) * ℓ) g) =
      ArithmeticCastelnuovoSeveri.weilGram lam (fun k : K => Tr ((k : ℤ) * ℓ) g) := by
    ext i j
    rw [weilGram_tower_apply, weilGram_tower_apply, lagW, lagW, weilFullFunctional_congr h]
  rw [this]
  exact hT K

/-- The `1 × 1` window of a tower reads the Weil form of the generator. -/
theorem re_weilFullFunctional_nonneg_of_towerPositive {lam : ℕ → ℝ} {g : ℝ → ℂ} {ℓ : ℝ}
    (hT : TowerPositive lam g ℓ) : 0 ≤ (weilFullFunctional lam (EF.weilTest g g)).re := by
  have h0 := hT {0}
  have hq := ArithmeticCastelnuovoSeveri.hermQuad_nonneg_of_negIndex_eq_zero h0 (fun _ => 1)
  rw [HTGeometry.hermQuad] at hq
  simp only [dotProduct, Matrix.mulVec, Finset.univ_unique, Finset.sum_singleton, Pi.star_apply,
    star_one, one_mul, mul_one] at hq
  rw [weilGram_tower_apply, sub_self, zero_mul, lagW,
    show Tr 0 (EF.weilTest g g) = EF.weilTest g g from funext fun x => by
      simp [ArithmeticCastelnuovoSeveri.translate]] at hq
  exact hq

/-- **Index zero on one prime tower selects `Λ`.** -/
theorem forall_negIndex_towerKernel_eq_zero_iff (lam : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    (∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g →
        negIndex (towerKernel lam g (Real.log p)) = 0) ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  rw [← weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt]
  simp only [← towerPositive_iff_negIndex_towerKernel_eq_zero]
  constructor
  · exact fun h f hf hfc => re_weilFullFunctional_nonneg_of_towerPositive (h f hf hfc)
  · intro hW g hg hgc
    obtain ⟨hRH, heq⟩ := weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW
    exact towerPositive_congr (fun n hn => (heq n hn).symm)
      (towerPositive_vonMangoldt_of_riemannHypothesis hRH hp hg hgc)

/-- **Every twin carries index on every prime tower.** -/
theorem exists_negIndex_towerKernel_ne_zero {lam : ℕ → ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hne : lam n₀ ≠ ArithmeticFunction.vonMangoldt n₀) {p : ℕ} (hp : p.Prime) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      negIndex (towerKernel lam g (Real.log p)) ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (((forall_negIndex_towerKernel_eq_zero_iff lam hp).mp fun g hg hgc =>
    h g hg hgc).2 n₀ hn₀)

end GaloisForLFunctions.HeckeKreinToeplitz
