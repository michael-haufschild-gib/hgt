import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface

/-!
# A section count is the sign

Over `𝔽_q` the sign of Weil's inequality comes from counting sections: Riemann–Roch makes `nD` or
`K − nD` effective when `D² > 0`, and effective curves meet nonnegatively. The report asks for the
`ℤ`-analogue (B3.5): a section count `h⁰` on the classes (equivalently, by P1, on the normalized
graphs) of the scaling surface. Write `E_h = {x | h⁰(x) > 0}` for its effective classes. Its two
axioms are

* **Riemann–Roch**: `x² > 0 ⇒ h⁰(x) > 0 ∨ h⁰(−x) > 0`;
* **Bézout**: `h⁰(x) > 0 ∧ h⁰(y) > 0 ⇒ x · y ≥ 0`.

This file shows that each axiom alone is empty and that together they are exactly the sign.

* **Each axiom alone is free** (`sectionRR_const`, `sectionBezout_zero`): the count `h⁰ ≡ 1`
  satisfies Riemann–Roch and `h⁰ ≡ 0` satisfies Bézout, on every polar surface.
* **They pull apart** (`not_sectionBezout_of_symm`): a count with `h⁰(x) > 0` and `h⁰(−x) > 0` at a
  class with `x² > 0` violates Bézout, since `x · (−x) = −x² < 0`. Riemann–Roch must choose a side
  of every positive class, and Bézout forbids choosing both.
* **Together they are the Hodge index** (`hodgeIndex_iff_exists_sectionCount`): on every polar
  surface a count with both axioms exists iff the Hodge index holds. One direction is ACS's
  `hodgeIndex_of_riemannRoch_of_bezout`; for the other the indicator of the open positive cone is
  such a count under the Hodge index.
* **Over `ℤ` it is RH** (`riemannHypothesis_iff_exists_sectionCount`); **over `𝔽_q` it is
  purity** (`forall_window_exists_sectionCount_iff_unitary`): a curve datum has such a count on
  every window surface iff its Frobenius eigenvalues are unitary, and the golden datum has none on
  some window (`goldenDatum_not_forall_window_exists_sectionCount`).

So a section count on the correspondence surface is not a weaker input than the sign: with both
axioms it is the Hodge index, and with either one alone it is empty. The budget of `ℤ` cannot be a
section count unless the count already carries the sign.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **Riemann–Roch for a section count**: every class of positive square or its negative has a
section. -/
def SectionRR (h : C → ℕ) : Prop := ∀ x, 0 < S.pair x x → 0 < h x ∨ 0 < h (-x)

/-- **Bézout for a section count**: effective classes meet nonnegatively. -/
def SectionBezout (h : C → ℕ) : Prop := ∀ x y, 0 < h x → 0 < h y → 0 ≤ S.pair x y

/-- **Riemann–Roch alone is free.** -/
theorem sectionRR_const : SectionRR S fun _ => 1 := fun _ _ => Or.inl one_pos

/-- **Bézout alone is free.** -/
theorem sectionBezout_zero : SectionBezout S fun _ => 0 := fun _ _ h => absurd h (lt_irrefl 0)

/-- **The axioms pull apart**: a count with sections at `x` and `−x`, `x² > 0`, violates Bézout. -/
theorem not_sectionBezout_of_symm {h : C → ℕ} {x : C} (hx : 0 < S.pair x x) (h1 : 0 < h x)
    (h2 : 0 < h (-x)) : ¬ SectionBezout S h := by
  intro hB
  have := hB x (-x) h1 h2
  rw [map_neg, neg_nonneg] at this
  linarith

theorem riemannRochAxiom_of_sectionRR {h : C → ℕ} (hRR : SectionRR S h) :
    S.RiemannRochAxiom {x | 0 < h x} := hRR

theorem bezoutAxiom_of_sectionBezout {h : C → ℕ} (hB : SectionBezout S h) :
    S.BezoutAxiom {x | 0 < h x} := fun x hx y hy => hB x y hx hy

/-- **Together the axioms are the Hodge index.** -/
theorem hodgeIndex_iff_exists_sectionCount :
    S.HodgeIndex ↔ ∃ h : C → ℕ, SectionRR S h ∧ SectionBezout S h := by
  classical
  constructor
  · intro hH
    -- the indicator of the open positive cone
    refine ⟨fun x => if x ∈ S.openPositiveCone then 1 else 0, fun x hx => ?_, fun x y hx hy => ?_⟩
    · rcases (S.openPositiveCone_riemannRoch_iff_hodgeIndex.mpr hH) x hx with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
    · have hx' : x ∈ S.openPositiveCone := by by_contra h; simp [h] at hx
      have hy' : y ∈ S.openPositiveCone := by by_contra h; simp [h] at hy
      exact (S.pair_pos_of_openPositiveCone hH hx' hy').le
  · rintro ⟨h, hRR, hB⟩
    exact S.hodgeIndex_of_riemannRoch_of_bezout (riemannRochAxiom_of_sectionRR S hRR)
      (bezoutAxiom_of_sectionBezout S hB)

/-- **Over `ℤ` a section count with Riemann–Roch and Bézout is RH.** -/
theorem riemannHypothesis_iff_exists_sectionCount :
    RiemannHypothesis ↔
      ∃ h : ScalingCycle → ℕ, SectionRR scalingSurface h ∧ SectionBezout scalingSurface h :=
  scalingSurface_hodgeIndex_iff.symm.trans (hodgeIndex_iff_exists_sectionCount scalingSurface)

/-- **Over `𝔽_q` it is purity**: a curve datum has a section count with both axioms on every
window surface iff its Frobenius eigenvalues are unitary. -/
theorem forall_window_exists_sectionCount_iff_unitary {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    (∀ W : Finset ℕ, ∃ h : _ → ℕ, SectionRR (D.windowSurface W) h ∧
      SectionBezout (D.windowSurface W) h) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [← D.windowSurface_hodgeIndex_iff_unitary]
  exact forall_congr' fun W => (hodgeIndex_iff_exists_sectionCount _).symm

/-- The golden datum has no section count with both axioms on some window. -/
theorem goldenDatum_not_forall_window_exists_sectionCount :
    ¬ ∀ W : Finset ℕ, ∃ h : _ → ℕ, SectionRR (goldenDatum.windowSurface W) h ∧
      SectionBezout (goldenDatum.windowSurface W) h :=
  fun h => goldenDatum_not_unitary ((forall_window_exists_sectionCount_iff_unitary _).mp h)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
