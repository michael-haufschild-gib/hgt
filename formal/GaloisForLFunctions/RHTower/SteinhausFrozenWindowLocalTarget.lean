import GaloisForLFunctions.RHTower.SteinhausFreePrimeWindow


open MeasureTheory Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- Every character prefix below the free-window threshold is retained. -/
theorem primesLE_subset_steinhausWindowRetainedPrimes
    {B L N Y : ℕ} (hBY : B ≤ Y) (hYN : Y ≤ N) (hNL : N ≤ L) :
    Nat.primesLE B ⊆ steinhausWindowRetainedPrimes L N Y := by
  intro p hp
  obtain ⟨hpB, hpp⟩ := Nat.mem_primesLE.mp hp
  apply mem_sdiff.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨hpB.trans (hBY.trans (hYN.trans hNL)), hpp⟩, ?_⟩
  intro hpP
  exact not_lt_of_ge (hpB.trans hBY) (mem_largePrimes.mp hpP).2

/-- The actual retained-prime projection in the finite Euclidean node space. -/
def steinhausHilbertRetainedCarrier {J : ℕ} (a : Fin J → ℕ → ℂ) (L : ℕ)
    (S : Finset ℕ) (ω : Omega) : EuclideanSpace ℂ (Fin J) :=
  WithLp.toLp 2 (fun j => ∑ n ∈ Sieve.smoothUpTo S L, a j n * X n ω)

private theorem sum_channel_apply {J : ℕ} (S : Finset ℕ) (a : ℕ → Fin J → ℂ)
    (η : Omega) (j : Fin J) :
    (∑ p ∈ S, charFactor 1 (η p) • (WithLp.toLp 2 (a p) : EuclideanSpace ℂ (Fin J))) j =
      ∑ p ∈ S, charFactor 1 (η p) * a p j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    simp only [Finset.sum_insert hp, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, ih]

/-- Exact vector decomposition with only the bounded prime window left free. -/
theorem steinhausHilbertCarrier_freeze_window_eq {J : ℕ} (a : Fin J → ℕ → ℂ)
    (L N Y : ℕ) (hYN : Y ≤ N) (hNL : N ≤ L) (hLY : L < Y * Y) (ω η : Omega) :
    steinhausHilbertCarrier a L (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω η) =
      steinhausHilbertRetainedCarrier a L (steinhausWindowRetainedPrimes L N Y) ω +
        ∑ p ∈ largePrimes N Y, charFactor 1 (η p) •
          (WithLp.toLp 2 (fun j => steinhausLargePrimeChannel (a j) L p ω) :
            EuclideanSpace ℂ (Fin J)) := by
  apply PiLp.ext
  intro j
  change (∑ n ∈ Icc 1 L, a j n * X n
      (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω η)) =
    (∑ n ∈ Sieve.smoothUpTo (steinhausWindowRetainedPrimes L N Y) L, a j n * X n ω) +
      (∑ p ∈ largePrimes N Y, charFactor 1 (η p) •
        (WithLp.toLp 2 (fun k => steinhausLargePrimeChannel (a k) L p ω) :
          EuclideanSpace ℂ (Fin J))) j
  rw [sum_channel_apply]
  exact steinhausCarrier_freeze_window_eq_smooth_add_circleChannels (a j) L N Y hYN hNL hLY ω η

/-- An original conditional probability lower bound for the actual carrier with the actual retained-prime background and bounded free window. -/
theorem measureReal_frozenSteinhausWindowCarrier_localTarget_ge {J : ℕ} (hJ : 0 < J)
    (a : Fin J → ℕ → ℂ) (L N Y : ℕ) (hYN : Y ≤ N) (hNL : N ≤ L) (hLY : L < Y * Y) (ω : Omega)
    {H M C r : ℝ} (hH : 0 < H) (hM : 0 ≤ M) (hr : 0 < r)
    (hlower : ∀ u : Fin J → ℂ, H * ‖u‖ ^ 2 ≤ ∑ p ∈ largePrimes N Y,
      ‖∑ j, steinhausLargePrimeChannel (a j) L p ω * u j‖ ^ 2)
    (hdot : ∀ p ∈ largePrimes N Y, ∀ u : Fin J → ℂ,
      ‖∑ j, steinhausLargePrimeChannel (a j) L p ω * u j‖ ≤ M * ‖u‖)
    (hupper : ∀ u : Fin J → ℂ, (∑ p ∈ largePrimes N Y,
      ‖∑ j, steinhausLargePrimeChannel (a j) L p ω * u j‖ ^ 2) ≤ C * ‖u‖ ^ 2)
    (t : EuclideanSpace ℂ (Fin J))
    (hsmall : M * ‖t - steinhausHilbertRetainedCarrier a L (steinhausWindowRetainedPrimes L N Y) ω‖ / (H / J) ≤ 1 / 2)
    (henergy : (J : ℝ) * C ≤ r ^ 2 / 2) :
    (1 / 4 : ℝ) * Real.exp (-2 * ‖t - steinhausHilbertRetainedCarrier a L (steinhausWindowRetainedPrimes L N Y) ω‖ ^ 2 / (H / J)) ≤
      steinhausMeasure.real {η |
        ‖steinhausHilbertCarrier a L (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω η) - t‖ < r} := by
  have h := measureReal_originalSteinhausChannelLocalTarget_ge hJ (largePrimes N Y)
    (fun p j => steinhausLargePrimeChannel (a j) L p ω) hH hM hr hlower hdot hupper
    (t - steinhausHilbertRetainedCarrier a L (steinhausWindowRetainedPrimes L N Y) ω) hsmall henergy
  have heq (η : Omega) :
      steinhausHilbertCarrier a L (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω η) - t =
        (∑ p ∈ largePrimes N Y, charFactor 1 (η p) •
          (WithLp.toLp 2 (fun j => steinhausLargePrimeChannel (a j) L p ω) :
            EuclideanSpace ℂ (Fin J))) - (t - steinhausHilbertRetainedCarrier a L (steinhausWindowRetainedPrimes L N Y) ω) := by
    rw [steinhausHilbertCarrier_freeze_window_eq a L N Y hYN hNL hLY ω η]
    abel
  simpa only [← heq] using h

end RHTower
