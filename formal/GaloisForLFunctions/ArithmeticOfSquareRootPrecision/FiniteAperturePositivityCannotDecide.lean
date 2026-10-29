import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TowerPositivityIsPrecisionExact
import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight

/-!
# Finite-aperture positivity cannot decide

**Aperture-`A` positivity** of a weight asks `Re W_λ(f ⋆ f̃) ≥ 0` for every `C²` test `f` supported in
`[−A, A]`. The autocorrelation is supported in `[−2A, 2A]`, so the Weil functional reads `λ` only
at `n ≤ e^{2A}` (SRT, `weilFullFunctional_eq_of_eqOn`).

* **Window law** (`aperturePositive_congr`): aperture-`A` positivity is determined by the window
  `{n : log n ≤ 2A}`; its precision class contains every perturbation supported beyond `e^{2A}`.
* **No finite aperture decides** (`not_riemannHypothesis_of_aperturePositive_imp_count`): if
  aperture-`A` positivity implied the count, it would hold for no weight, and in particular RH would
  fail (under RH the full Weil positivity of `Λ` gives aperture-`A` positivity).
* **Below `log 2 / 2` positivity is weight-blind** (`aperturePositive_threeTenths`): every weight is
  aperture-`3/10` positive (SRT), so this positivity has the whole space of weights as its precision
  class, the Liouville twin included.

Together with the precision-exactness of tower positivity, positivity statements span the whole
precision scale: weight-blind at small aperture, window-determined at every finite aperture, exact on
a whole tower.
-/

noncomputable section

open Set Real
open GaloisForLFunctions.RHTower RHTower Zeta23

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- **Aperture-`A` positivity** of a weight. -/
def AperturePositive (A : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

/-- **Window law**: aperture-`A` positivity sees the weight only on `{n : log n ≤ 2A}`. -/
theorem aperturePositive_congr {A : ℝ} {lam lam' : ℕ → ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → Real.log n ≤ A + A → lam n = lam' n) :
    AperturePositive A lam ↔ AperturePositive A lam' := by
  refine forall_congr' fun f => forall_congr' fun _ => forall_congr' fun hfs => ?_
  rw [SquareRootThreshold.weilFullFunctional_eq_of_eqOn (tsupport_weilTest_subset_add hfs hfs) h]

/-- Aperture-`A` positivity is determined by the finite window `{0, …, ⌊e^{2A}⌋}`. -/
theorem aperturePositive_finite_window (A : ℝ) (a b : ℕ → ℝ)
    (h : ∀ n ≤ ⌊Real.exp (A + A)⌋₊, a n = b n) : AperturePositive A a ↔ AperturePositive A b := by
  refine aperturePositive_congr fun n hn hlog => h n ?_
  refine Nat.le_floor ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
    _ ≤ Real.exp (A + A) := Real.exp_le_exp.mpr hlog

/-- Full Weil positivity gives positivity at every aperture. -/
theorem aperturePositive_of_weilPositiveFull {lam : ℕ → ℝ} (h : WeilPositiveFull lam) (A : ℝ) :
    AperturePositive A lam := fun f hf hfs =>
  h f hf (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport f).trans hfs))

/-- **If some finite aperture decided the count, RH would fail.** -/
theorem not_riemannHypothesis_of_aperturePositive_imp_count {A : ℝ}
    (hA : ∀ lam, AperturePositive A lam → Count lam) : ¬ RiemannHypothesis := by
  intro hRH
  have hW : WeilPositiveFull vonMangoldtWeight :=
    WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr ⟨hRH, fun _ _ => rfl⟩
  exact not_of_finite_window (AperturePositive A) hA ⌊Real.exp (A + A)⌋₊
    (aperturePositive_finite_window A) vonMangoldtWeight (aperturePositive_of_weilPositiveFull hW A)

/-- **Below `log 2 / 2` positivity is weight-blind**: every weight is aperture-`3/10` positive. -/
theorem aperturePositive_threeTenths (lam : ℕ → ℝ) : AperturePositive (3 / 10) lam :=
  fun f hf hfs => le_trans (by positivity)
    (SquareRootThreshold.re_weilFullFunctional_ge_of_aperture_le_threeTenths lam hf hfs)

/-- Aperture-`3/10` positivity does not imply the count: it holds for the Liouville twin. -/
theorem aperturePositive_threeTenths_not_imp_count :
    AperturePositive (3 / 10) liouvilleWeight ∧ ¬ Count liouvilleWeight :=
  ⟨aperturePositive_threeTenths _, not_count_liouvilleWeight⟩

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
