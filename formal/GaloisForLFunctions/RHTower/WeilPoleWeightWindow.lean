import GaloisForLFunctions.RHTower.WeilConeDegreePoleSandwich
import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof

/-!
# The pole-weight window of the Weil cone

For a pole weight `β` the Weil functional `W_β(lam) = W(lam) + (β − 1)(k̂(i/2) + k̂(−i/2))`
(`WeilPoleWeight.weilPoleWeightFunctional`) counts the pole `β` times.  On a Weil test `f` with
autocorrelation `k_f` write `D_β(f) = Re A(k_f) + (β − 1) Re P(k_f)` (`poleWeightArchRe`), where
`A` is the pole and archimedean part and `P` the pole term.

**Farkas at every pole weight** (`exists_weilPositiveAt_iff`).  Some real weights `lam` make `W_β`
nonnegative on every autocorrelation iff `D_β` is nonnegative on every nonnegative combination of
autocorrelations vanishing at every `±log n`, `n ≥ 2` (`PrimeBlindPositiveAt β`).  Neither side
mentions `ζ` beyond its archimedean datum.

**The window is an interval** (`primeBlindPositiveAt_of_mem_Icc`).  On a fixed blind combination
`D_β` is affine in `β`, so the set of admissible pole weights is an interval.  Every blind combination
with negative total pole term `S_P < 0` bounds it from above by `1 + S_A/|S_P|`
(`le_one_add_div_of_primeBlindPositiveAt`), and every one with `S_P > 0` bounds it from below by
`1 − S_A/S_P` (`one_sub_div_le_of_primeBlindPositiveAt`).

**The Riemann hypothesis is the statement that `β = 1` lies in the window**
(`riemannHypothesis_iff_primeBlindPositiveAt_one`), by the twisted arc minimum principle.
-/

open Complex Zeta23 Finsupp

noncomputable section

namespace RHTower

open WeilOneSided

/-- The pole-weight-`β` part of a test: `Re A(k_f) + (β − 1) Re P(k_f)`. -/
def poleWeightArchRe (β : ℝ) (f : WeilTestFn) : ℝ :=
  weilArchRe (EF.weilTest f.1 f.1) + (β - 1) * (weilPoleTerm (EF.weilTest f.1 f.1)).re

/-- Prime-blind positivity at pole weight `β`. -/
def PrimeBlindPositiveAt (β : ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) →
    0 ≤ c.sum fun f t => t * poleWeightArchRe β f

/-- Weil positivity at pole weight `β`. -/
def WeilPositiveAt (β : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    0 ≤ (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f f)).re

theorem re_weilPoleWeightFunctional_eq (β : ℝ) (lam : ℕ → ℝ) (f : WeilTestFn) :
    (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f.1 f.1)).re =
      poleWeightArchRe β f - linearCombination ℝ (fun j : LogIndex => lam j) (logVector f) := by
  unfold WeilPoleWeight.weilPoleWeightFunctional poleWeightArchRe
  rw [add_re, re_weilFullFunctional_eq]
  have h : (((β : ℂ) - 1) * (paperFT (EF.weilTest f.1 f.1) (I / 2) +
      paperFT (EF.weilTest f.1 f.1) (-I / 2))).re =
      (β - 1) * (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
    rw [show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
    rfl
  rw [h]
  ring

theorem sum_re_weilPoleWeightFunctional (β : ℝ) (lam : ℕ → ℝ) (c : WeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f.1 f.1)).re) =
      (c.sum fun f t => t * poleWeightArchRe β f) -
        linearCombination ℝ (fun j : LogIndex => lam j) (linearCombination ℝ logVector c) := by
  simp_rw [re_weilPoleWeightFunctional_eq]
  have e2 : linearCombination ℝ (fun j : LogIndex => lam j) (linearCombination ℝ logVector c) =
      c.sum fun f t => t * linearCombination ℝ (fun j : LogIndex => lam j) (logVector f) := by
    rw [linearCombination_apply ℝ (v := logVector), map_finsuppSum]
    exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
  rw [e2, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun f _ => by ring

/-- **Farkas at pole weight `β`**: the `β`-cone is nonempty iff prime-blind positivity at `β`. -/
theorem exists_weilPositiveAt_iff (β : ℝ) :
    (∃ lam : ℕ → ℝ, WeilPositiveAt β lam) ↔ PrimeBlindPositiveAt β := by
  constructor
  · rintro ⟨lam, hW⟩ c hc hnull
    have h1 : 0 ≤ c.sum fun f t =>
        t * (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f.1 f.1)).re :=
      Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hW f.1 f.2.1 f.2.2)
    rw [sum_re_weilPoleWeightFunctional, linearCombination_logVector_eq_zero hnull, map_zero,
      sub_zero] at h1
    exact h1
  · intro h
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      logVector (poleWeightArchRe β)
      (fun j => ⟨pairTestFn j (-1), _, pairTest_weight_pos j, by
        rw [logVector_pairTestFn]; congr 1; ring⟩)
      (fun j => ⟨pairTestFn j 1, _, pairTest_weight_pos j, by
        rw [logVector_pairTestFn]; congr 1; ring⟩)
      (fun c hc hnull => by
        have e : linearCombination ℝ (poleWeightArchRe β) c =
            c.sum fun f t => t * poleWeightArchRe β f := by
          rw [linearCombination_apply]; simp only [smul_eq_mul]
        rw [e]
        refine h c hc fun n hn => ?_
        rw [← linearCombination_logVector_apply c ⟨n, hn⟩, hnull]
        rfl)
    refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0, fun f hf hfc => ?_⟩
    rw [re_weilPoleWeightFunctional_eq β _ ⟨f, hf, hfc⟩]
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
        lam := funext fun j => by simp [j.2]
    rw [e]
    linarith [hlam ⟨f, hf, hfc⟩]

/-- `D_β` summed over a combination is affine in `β`. -/
theorem sum_poleWeightArchRe (β : ℝ) (c : WeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * poleWeightArchRe β f) =
      (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) +
        (β - 1) * c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
  unfold poleWeightArchRe
  rw [Finsupp.mul_sum, ← Finsupp.sum_add]
  exact Finsupp.sum_congr fun f _ => by ring

/-- **The window is an interval.** -/
theorem primeBlindPositiveAt_of_mem_Icc {β₁ β₂ β : ℝ} (h₁ : PrimeBlindPositiveAt β₁)
    (h₂ : PrimeBlindPositiveAt β₂) (hβ : β ∈ Set.Icc β₁ β₂) : PrimeBlindPositiveAt β := by
  intro c hc hnull
  have a₁ := h₁ c hc hnull
  have a₂ := h₂ c hc hnull
  rw [sum_poleWeightArchRe] at a₁ a₂ ⊢
  set A := c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)
  set P := c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re
  rcases le_total 0 P with hP | hP
  · nlinarith [hβ.1]
  · nlinarith [hβ.2]

/-- **Upper end of the window.**  A blind combination with negative total pole term bounds every
admissible pole weight by `1 + S_A/|S_P|`. -/
theorem le_one_add_div_of_primeBlindPositiveAt {β : ℝ} (h : PrimeBlindPositiveAt β)
    {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hnull : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0)
    (hP : (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) < 0) :
    β ≤ 1 + (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) /
      |c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re| := by
  have a := h c hc hnull
  rw [sum_poleWeightArchRe] at a
  set A := c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)
  set P := c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re
  rw [abs_of_neg hP]
  have hP' : 0 < -P := by linarith
  have h2 : β - 1 ≤ A / -P := by rw [le_div_iff₀ hP']; linarith
  linarith

/-- **Lower end of the window.**  A blind combination with positive total pole term bounds every
admissible pole weight from below by `1 − S_A/S_P`. -/
theorem one_sub_div_le_of_primeBlindPositiveAt {β : ℝ} (h : PrimeBlindPositiveAt β)
    {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hnull : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0)
    (hP : 0 < c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) :
    1 - (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) /
      (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) ≤ β := by
  have a := h c hc hnull
  rw [sum_poleWeightArchRe] at a
  set A := c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)
  set P := c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re
  have h2 : -A / P ≤ β - 1 := by rw [div_le_iff₀ hP]; linarith
  have h3 : -A / P = -(A / P) := neg_div P A
  linarith

theorem primeBlindPositiveAt_one_iff : PrimeBlindPositiveAt 1 ↔ WeilOneSided.PrimeBlindPositive := by
  unfold PrimeBlindPositiveAt WeilOneSided.PrimeBlindPositive poleWeightArchRe
  simp only [sub_self, zero_mul, add_zero]

/-- **RH is the statement that the pole weight `1` lies in the window.** -/
theorem riemannHypothesis_iff_primeBlindPositiveAt_one :
    RiemannHypothesis ↔ PrimeBlindPositiveAt 1 :=
  riemannHypothesis_iff_primeBlindPositive_unconditional.trans primeBlindPositiveAt_one_iff.symm

end RHTower
