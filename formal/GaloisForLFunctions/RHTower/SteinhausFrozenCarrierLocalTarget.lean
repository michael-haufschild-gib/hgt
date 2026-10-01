import GaloisForLFunctions.RHTower.SteinhausFiniteChannelLocalTarget
import GaloisForLFunctions.RHTower.SteinhausLargestPrimeDecomposition
import GaloisForLFunctions.RHTower.SteinhausFrozenPrefixSecondMoment
import GaloisForLFunctions.RHTower.SteinhausPrimeDivergence


open MeasureTheory
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

/-- At a prime, the actual Steinhaus character is the first circle character. -/
theorem steinhausCharacter_prime_eq_charFactor {p : ℕ} (hp : p.Prime) (ω : Omega) :
    X p ω = charFactor 1 (ω p) := by
  simp [charFactor, GaloisForLFunctions.RHTower.X_prime_eq hp]

/-- The exact conditional carrier uses only independent first circle phases in the exterior coordinates. -/
theorem steinhausCarrier_freeze_eq_smooth_add_circleChannels (a : ℕ → ℂ)
    (N Y : ℕ) (ω η : Omega) (hNY : N < Y * Y) :
    (∑ n ∈ Finset.Icc 1 N, a n * X n (freezeSteinhausPrefix (Nat.primesLE Y) ω η)) =
      steinhausSmoothCarrier a N Y ω + ∑ p ∈ largePrimes N Y,
        charFactor 1 (η p) * steinhausLargePrimeChannel a N p ω := by
  have hphase (q : ℕ) (hq : q ∈ Nat.primesLE Y) :
      freezeSteinhausPrefix (Nat.primesLE Y) ω η q = ω q := by
    simp only [freezeSteinhausPrefix, if_pos hq]
  rw [steinhausCarrier_eq_smooth_add_largePrimeChannels a N Y _ hNY,
    steinhausSmoothCarrier_congr_of_eqOn_smallPrimes a N Y hphase]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [steinhausLargePrimeChannel_congr_of_eqOn_smallPrimes a hNY hp hphase,
    steinhausCharacter_prime_eq_charFactor (mem_largePrimes.mp hp).1.2]
  simp only [freezeSteinhausPrefix, if_neg (largePrime_not_mem_primesLE hp)]

/-- Literal finite-node carrier, using the Euclidean norm for simultaneous target control. -/
def steinhausHilbertCarrier {J : ℕ} (a : Fin J → ℕ → ℂ) (N : ℕ) (ω : Omega) :
    EuclideanSpace ℂ (Fin J) :=
  WithLp.toLp 2 (fun j => ∑ n ∈ Finset.Icc 1 N, a j n * X n ω)

/-- The literal smooth background in the same Euclidean node space. -/
def steinhausHilbertSmoothCarrier {J : ℕ} (a : Fin J → ℕ → ℂ) (N Y : ℕ) (ω : Omega) :
    EuclideanSpace ℂ (Fin J) :=
  WithLp.toLp 2 (fun j => steinhausSmoothCarrier (a j) N Y ω)

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

/-- Exact vector identity before any probability estimate or target selection. -/
theorem steinhausHilbertCarrier_freeze_eq {J : ℕ} (a : Fin J → ℕ → ℂ)
    (N Y : ℕ) (ω η : Omega) (hNY : N < Y * Y) :
    steinhausHilbertCarrier a N (freezeSteinhausPrefix (Nat.primesLE Y) ω η) =
      steinhausHilbertSmoothCarrier a N Y ω +
        ∑ p ∈ largePrimes N Y, charFactor 1 (η p) •
          (WithLp.toLp 2 (fun j => steinhausLargePrimeChannel (a j) N p ω) :
            EuclideanSpace ℂ (Fin J)) := by
  apply PiLp.ext
  intro j
  change (∑ n ∈ Finset.Icc 1 N, a j n * X n (freezeSteinhausPrefix (Nat.primesLE Y) ω η)) =
    steinhausSmoothCarrier (a j) N Y ω +
      (∑ p ∈ largePrimes N Y, charFactor 1 (η p) •
        (WithLp.toLp 2 (fun k => steinhausLargePrimeChannel (a k) N p ω) :
          EuclideanSpace ℂ (Fin J))) j
  rw [sum_channel_apply]
  exact steinhausCarrier_freeze_eq_smooth_add_circleChannels (a j) N Y ω η hNY

/-- An original conditional probability lower bound for the actual carrier with the actual smooth background. -/
theorem measureReal_frozenSteinhausCarrier_localTarget_ge {J : ℕ} (hJ : 0 < J)
    (a : Fin J → ℕ → ℂ) (N Y : ℕ) (ω : Omega) (hNY : N < Y * Y)
    {H L C r : ℝ} (hH : 0 < H) (hL : 0 ≤ L) (hr : 0 < r)
    (hlower : ∀ u : Fin J → ℂ, H * ‖u‖ ^ 2 ≤ ∑ p ∈ largePrimes N Y,
      ‖∑ j, steinhausLargePrimeChannel (a j) N p ω * u j‖ ^ 2)
    (hdot : ∀ p ∈ largePrimes N Y, ∀ u : Fin J → ℂ,
      ‖∑ j, steinhausLargePrimeChannel (a j) N p ω * u j‖ ≤ L * ‖u‖)
    (hupper : ∀ u : Fin J → ℂ, (∑ p ∈ largePrimes N Y,
      ‖∑ j, steinhausLargePrimeChannel (a j) N p ω * u j‖ ^ 2) ≤ C * ‖u‖ ^ 2)
    (t : EuclideanSpace ℂ (Fin J))
    (hsmall : L * ‖t - steinhausHilbertSmoothCarrier a N Y ω‖ / (H / J) ≤ 1 / 2)
    (henergy : (J : ℝ) * C ≤ r ^ 2 / 2) :
    (1 / 4 : ℝ) * Real.exp (-2 * ‖t - steinhausHilbertSmoothCarrier a N Y ω‖ ^ 2 / (H / J)) ≤
      steinhausMeasure.real {η |
        ‖steinhausHilbertCarrier a N (freezeSteinhausPrefix (Nat.primesLE Y) ω η) - t‖ < r} := by
  have h := measureReal_originalSteinhausChannelLocalTarget_ge hJ (largePrimes N Y)
    (fun p j => steinhausLargePrimeChannel (a j) N p ω) hH hL hr hlower hdot hupper
    (t - steinhausHilbertSmoothCarrier a N Y ω) hsmall henergy
  have heq (η : Omega) :
      steinhausHilbertCarrier a N (freezeSteinhausPrefix (Nat.primesLE Y) ω η) - t =
        (∑ p ∈ largePrimes N Y, charFactor 1 (η p) •
          (WithLp.toLp 2 (fun j => steinhausLargePrimeChannel (a j) N p ω) :
            EuclideanSpace ℂ (Fin J))) - (t - steinhausHilbertSmoothCarrier a N Y ω) := by
    rw [steinhausHilbertCarrier_freeze_eq a N Y ω η hNY]
    abel
  simpa only [← heq] using h

end RHTower
