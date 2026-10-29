import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheDecidingInputTheorem
import GaloisForLFunctions.HeckeKreinToeplitz.IndexZeroSelectsTheVonMangoldtWeight

/-!
# Tower positivity is precision-exact

Two RH-equivalent statements about a weight can have very different precision classes. The count
selects `Λ` only modulo the square-root class `𝒬`. **Tower positivity** along one prime `p` — index
zero of the tower kernel `u ↦ W_λ(T_{log u} g, g)` for every `C²` compactly supported generator —
selects `Λ` exactly (HKT, `forall_negIndex_towerKernel_eq_zero_iff`).

* **Tower positivity implies the count** (`count_of_towerIndexZero`), so it is a deciding input: it is
  parity-breaking, precision-faithful and of unbounded aperture
  (`towerIndexZero_necessary_properties`).
* **Its stabilizer is trivial** (`towerIndexZero_add_iff`): `Λ + δ` is tower positive iff RH holds and
  `δ` vanishes on `n ≥ 2`. Its precision class is `{0}`, against `𝒬` for the count.
* **The gap is real** (`count_and_not_towerIndexZero_add_inv`): `Λ + 1/n` satisfies the count iff
  RH, and is never tower positive.

Precision is therefore not monotone along equivalences: at `Λ` the count and tower positivity are
the same statement (RH), while as properties of weights one sees `𝒬` and the other sees every
coefficient. Positivity carries the identities of `Λ`; the count carries only its square-root class.
-/

noncomputable section

open Filter Real

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

open HeckeKreinToeplitz

/-- **Tower positivity** along `p`: every `C²` compactly supported generator has a tower kernel of
index zero. -/
def TowerIndexZero (p : ℕ) (lam : ℕ → ℝ) : Prop :=
  ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g →
    negIndex (towerKernel lam g (Real.log p)) = 0

/-- Tower positivity is RH together with `λ = Λ` on `n ≥ 2` (HKT). -/
theorem towerIndexZero_iff {p : ℕ} (hp : p.Prime) (lam : ℕ → ℝ) :
    TowerIndexZero p lam ↔ RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = vonMangoldtWeight n :=
  forall_negIndex_towerKernel_eq_zero_iff lam hp

/-- **Tower positivity implies the count.** -/
theorem count_of_towerIndexZero {p : ℕ} (hp : p.Prime) {lam : ℕ → ℝ}
    (h : TowerIndexZero p lam) : Count lam := by
  obtain ⟨hRH, heq⟩ := (towerIndexZero_iff hp lam).mp h
  exact (count_congr_of_eventually_eq (N := 1) fun n hn => (heq n hn).symm).mp
    (count_vonMangoldt_iff.mpr hRH)

/-- Tower positivity at `Λ` is RH. -/
theorem towerIndexZero_vonMangoldt_iff {p : ℕ} (hp : p.Prime) :
    TowerIndexZero p vonMangoldtWeight ↔ RiemannHypothesis := by
  rw [towerIndexZero_iff hp]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => rfl⟩⟩

/-- **Tower positivity passes the deciding-input tests.** -/
theorem towerIndexZero_necessary_properties {p : ℕ} (hp : p.Prime) :
    ¬ TowerIndexZero p liouvilleWeight ∧
    (∀ (a : ℕ → ℝ) (ε η : ℝ), ε ≠ 0 → 0 ≤ η → η < 1 / 2 →
      ¬ (TowerIndexZero p a ∧ TowerIndexZero p (a + ε • powerWeight η))) ∧
    (∀ (a : ℕ → ℝ) (X : ℕ), ∃ b : ℕ → ℝ, (∀ n ≤ X, b n = a n) ∧ ¬ TowerIndexZero p b) :=
  let h := deciding_input_necessary_properties (TowerIndexZero p) fun _ => count_of_towerIndexZero hp
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **The stabilizer of tower positivity is trivial**: `Λ + δ` is tower positive iff RH holds and
`δ` vanishes on `n ≥ 2`. -/
theorem towerIndexZero_add_iff {p : ℕ} (hp : p.Prime) (δ : ℕ → ℝ) :
    TowerIndexZero p (vonMangoldtWeight + δ) ↔ RiemannHypothesis ∧ ∀ n, 2 ≤ n → δ n = 0 := by
  rw [towerIndexZero_iff hp]
  refine and_congr_right fun _ => forall_congr' fun n => imp_congr_right fun _ => ?_
  simp only [Pi.add_apply]
  constructor <;> intro h <;> linarith

/-- **The gap between the two precisions**: `Λ + 1/n` satisfies the count iff RH, and is never
tower positive. -/
theorem count_and_not_towerIndexZero_add_inv {p : ℕ} (hp : p.Prime) :
    (Count (vonMangoldtWeight + (1 : ℝ) • powerWeight 1) ↔ RiemannHypothesis) ∧
      ¬ TowerIndexZero p (vonMangoldtWeight + (1 : ℝ) • powerWeight 1) := by
  refine ⟨(count_add_iff_of_mem_sqrtClass (smul_powerWeight_mem_sqrtClass (by norm_num) 1)).trans
    count_vonMangoldt_iff, fun h => ?_⟩
  have := ((towerIndexZero_add_iff hp _).mp h).2 2 le_rfl
  simp [powerWeight] at this

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
