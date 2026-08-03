import GaloisForLFunctions.RHTower.Sieve.GoodStartCount
import GaloisForLFunctions.RHTower.MobiusReciprocalMarkerBlockCount

/-!
# Step 1 with the mean-square input made explicit

Feeding a mean-square bound through Markov's inequality bounds the first exceptional set, so

`#S ≤ #{good starts} + V/(DL/8)² + #Bad₂`.

The hypothesis `∑_{t ∈ S} M(t,L)² ≤ V` is precisely the published mean-square input; everything else
in the statement is proved.  Written this way, the dependence of step 1 on that input is a single
named hypothesis of a single theorem.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Step 1 of the proof, with the mean-square input as a hypothesis.** -/
theorem card_le_good_add_meanSquare {S Bad₂ : Finset ℕ} {L : ℕ} {D V : ℝ}
    (hδ : 0 < (1 / 8) * D * (L : ℝ))
    (hms : ∑ t ∈ S, (∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)) ^ 2 ≤ V)
    (h2 : ∀ t ∈ S, t ∉ Bad₂ →
      (1 / 2) * D * (L : ℝ) ≤ ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2) :
    (S.card : ℝ)
      ≤ ((S.filter (fun t =>
          (3 / 16) * D * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * D * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + V / ((1 / 8) * D * (L : ℝ)) ^ 2 + (Bad₂.card : ℝ) := by
  classical
  set δ : ℝ := (1 / 8) * D * (L : ℝ) with hδdef
  set M : ℕ → ℝ := fun t => ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) with hM
  set Bad₁ : Finset ℕ := S.filter (fun t => δ ≤ |M t|) with hBad₁
  have h1 : ∀ t ∈ S, t ∉ Bad₁ → |M t| ≤ δ := by
    intro t ht hnot
    have : ¬ (δ ≤ |M t|) := by
      intro hc
      exact hnot (by rw [hBad₁, Finset.mem_filter]; exact ⟨ht, hc⟩)
    linarith [not_le.mp this]
  have hcover := card_le_good_add_bad (S := S) (Bad₁ := Bad₁) (Bad₂ := Bad₂) (L := L) (D := D)
    h1 h2
  have hmarkov : (Bad₁.card : ℝ) ≤ V / δ ^ 2 := by
    rw [hBad₁]
    exact RHTower.card_large_le_of_sum_sq_le hδ hms
  have hcast : (S.card : ℝ)
      ≤ ((S.filter (fun t =>
          (3 / 16) * D * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * D * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + (Bad₁.card : ℝ) + (Bad₂.card : ℝ) := by
    exact_mod_cast hcover
  linarith

end RHTower.Sieve
