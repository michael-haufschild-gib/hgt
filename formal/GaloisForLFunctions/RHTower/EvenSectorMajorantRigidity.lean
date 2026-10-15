import GaloisForLFunctions.RHTower.EvenSectorPoleFreeLogDensity
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity
import GaloisForLFunctions.RHTower.WeilParityPoleWeightWindows

/-!
# No even-positive weight system majorizes `Λ`, at any pole weight

**Theorem** (`eq_vonMangoldt_of_weilPositiveEvenAt_of_ge`).  If `lam` is Weil-positive at some pole
weight `β` on the autocorrelations of even compactly supported `C²` tests and `lam(n) ≥ Λ(n)` for
all `n ≥ 2`, then `lam(n) = Λ(n)` for all `n ≥ 2`.  No hypothesis on `ζ` is used.

**Corollaries.**
* `riemannHypothesis_iff_exists_weilPositiveEvenAt_ge`: RH holds iff some majorant of `Λ` is
  Weil-positive on even tests at some pole weight.
* `vonMangoldt_add_const_not_weilPositiveEvenAt`: for `c > 0`, `Λ + c` is not Weil-positive on even
  tests at any pole weight.

For `β > 1` even positivity is weaker than full positivity: the pole term `2(β − 1)|f̂(i/2)|²`
gives slack on every even test that does not vanish at `±i/2`.  The theorem says that this slack
cannot be spent on raising the weights.

Proof.  The polar second differences `Φχ_L − αΦχ_L(· − c) − αΦχ_L(· + c)` of the truncated Riemann
kernel, `α = 1/(2 cosh(c/2))`, are even (`polarRiemannDifference_neg`) and vanish at `±i/2`, so even
positivity at any pole weight applies to them with pole weight `1`.  The excess bound
`Σ_{n ≤ K} (lam(n) − Λ(n))/n = o(log K)` needs only the log-density ceiling, which holds at every
pole weight (`even_log_density_le`).  The full-cone majorant argument
(`eq_vonMangoldt_of_ge_of_log_density_le`) uses nothing else.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided

/-- The polar second difference of the truncated Riemann kernel is even. -/
theorem polarRiemannDifference_neg (L c u : ℝ) :
    polarRiemannDifference L c (-u) = polarRiemannDifference L c u := by
  simp only [polarRiemannDifference_eq, polarRiemannDifferenceReal]
  congr 1
  rw [truncatedRiemannKernelReal_neg, show -u - c = -(u - -c) by ring,
    truncatedRiemannKernelReal_neg, show -u - -c = -(u - c) by ring,
    truncatedRiemannKernelReal_neg]
  ring

/-- Even positivity at any pole weight gives nonnegative energy on the polar Riemann
differences. -/
theorem integral_weilAtomSymbol_polarRiemannDifference_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c) :
    0 ≤ ∫ τ : ℝ, ‖paperFT (polarRiemannDifference L c) τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * (L + c))⌋₊ (τ / (2 * π)) := by
  have hfd := contDiff_polarRiemannDifference L c
  have hfs := tsupport_polarRiemannDifference (L := L) hc
  obtain ⟨hp, hm⟩ := paperFT_polarRiemannDifference_pole L c
  have hfc : HasCompactSupport (polarRiemannDifference L c) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hfs
  refine integral_weilAtomSymbol_nonneg_of_polar (by linarith) hfd hfs hp hm ?_
  have h1 := h _ hfd hfc (polarRiemannDifference_neg L c)
  have hP0 : weilPoleTerm (EF.weilTest (polarRiemannDifference L c)
      (polarRiemannDifference L c)) = 0 := by
    rw [weilPoleTerm_weilTest_eq hfd.continuous hfc, hp, neg_div, hm]
    simp
  unfold WeilPoleWeight.weilPoleWeightFunctional at h1
  have e : paperFT (EF.weilTest (polarRiemannDifference L c) (polarRiemannDifference L c))
      (I / 2) + paperFT (EF.weilTest (polarRiemannDifference L c)
        (polarRiemannDifference L c)) (-I / 2) = 0 := hP0
  rwa [e, mul_zero, add_zero] at h1

/-- **No even-positive weight system majorizes `Λ`, at any pole weight.** -/
theorem eq_vonMangoldt_of_weilPositiveEvenAt_of_ge {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam)
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  eq_vonMangoldt_of_ge_of_log_density_le (fun _ hε => even_log_density_le h hε)
    (fun _ _ hL hc => integral_weilAtomSymbol_polarRiemannDifference_nonneg h hL hc) hge

/-- Even Weil positivity at pole weight `β` depends on the weights only at `n ≥ 2`. -/
theorem weilPositiveEvenAt_congr {β : ℝ} {lam lam' : ℕ → ℝ} (h : ∀ n, 2 ≤ n → lam n = lam' n)
    (hlam : WeilPositiveEvenAt β lam) : WeilPositiveEvenAt β lam' := fun f hf hfc hev => by
  have h1 := hlam f hf hfc hev
  rw [re_weilPoleWeightFunctional_eq β _ ⟨f, hf, hfc⟩] at h1 ⊢
  have e : (fun j : LogIndex => lam j) = fun j : LogIndex => lam' j :=
    funext fun j => h j j.2
  rwa [e] at h1

/-- **RH is the existence of an even-positive majorant of `Λ` at some pole weight.** -/
theorem riemannHypothesis_iff_exists_weilPositiveEvenAt_ge :
    RiemannHypothesis ↔ ∃ β : ℝ, ∃ lam : ℕ → ℝ, WeilPositiveEvenAt β lam ∧
      ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n := by
  constructor
  · intro hRH
    exact ⟨1, _, weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩, fun _ _ => le_rfl⟩
  · rintro ⟨β, lam, h, hge⟩
    by_contra hRH
    exact not_weilPositiveEvenAt_vonMangoldt_of_not_riemannHypothesis hRH β
      (weilPositiveEvenAt_congr (eq_vonMangoldt_of_weilPositiveEvenAt_of_ge h hge) h)

/-- **Constant shifts are not even-positive at any pole weight.** -/
theorem vonMangoldt_add_const_not_weilPositiveEvenAt (β : ℝ) {c : ℝ} (hc : 0 < c) :
    ¬ WeilPositiveEvenAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + c := by
  intro h
  have h2 := eq_vonMangoldt_of_weilPositiveEvenAt_of_ge h fun n _ => by linarith
  have := h2 2 le_rfl
  linarith

end RHTower.EvenSector

end
