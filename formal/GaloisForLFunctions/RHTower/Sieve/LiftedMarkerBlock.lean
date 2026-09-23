import GaloisForLFunctions.RHTower.Sieve.GoodMarkerData
import GaloisForLFunctions.RHTower.Sieve.MarkerBlockSignCount
import GaloisForLFunctions.RHTower.Sieve.MarkerHarmonicSupply

/-!
# One block of lifted markers

Every hypothesis below is an inequality between the block's own data.  The markers whose reciprocal
start is exceptional are discarded by the Cauchy--Schwarz device, which costs `b/M₀` of the harmonic
mass; the rest carry a good fibre, and their cells fill the window with integers of the prescribed
Möbius sign.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **The sign count of a window supplied by one block of lifted markers.** -/
theorem card_sign_window_ge_block {y hy : ℝ} {X H M₀ Q m K : ℕ} {σ : ℤ} {rho S B Pi b : ℝ}
    (hy4 : 4 ≤ y) (hy0 : 0 < hy) (hsy : Real.sqrt y = (m : ℝ)) (hσ : σ = 1 ∨ σ = -1)
    (hrho : 0 ≤ rho) (hm : 2 ≤ m) (hM₀ : 0 < M₀) (hXH : X + H ≤ M₀ * M₀)
    (hstartlow : ∀ p ∈ bigPrimeSet M₀ (Q * M₀), (m : ℝ) / 2 ≤ ((X / p : ℕ) : ℝ))
    (hstarthigh : ∀ p ∈ bigPrimeSet M₀ (Q * M₀), ((X / p : ℕ) : ℝ) + 1 ≤ (m : ℝ))
    (hfit : ∀ p ∈ bigPrimeSet M₀ (Q * M₀),
      (hy * (((X / p : ℕ) : ℝ) + 1) / (m : ℝ) + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsupply : ∀ p ∈ bigPrimeSet M₀ (Q * M₀), rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (hy * ((X / p : ℕ) : ℝ) / (m : ℝ) - 1))
    (hsep : ∀ p ∈ bigPrimeSet M₀ (Q * M₀), ∀ q ∈ bigPrimeSet M₀ (Q * M₀), p < q →
      X / q = X / p → q ≤ p + K)
    (hpair : ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet M₀ (Q * M₀)).filter
          (fun p => p + d ∈ bigPrimeSet M₀ (Q * M₀))).card : ℕ) : ℝ) ≤ Pi)
    (hbthr : (((badStart y hy).card : ℕ) : ℝ)
      * ((((bigPrimeSet M₀ (Q * M₀)).card : ℕ) : ℝ) + 2 * Pi) ≤ b ^ (2 : ℕ)) (hb0 : 0 ≤ b)
    (hS : S ≤ (∑ p ∈ bigPrimeSet M₀ (Q * M₀), 1 / (p : ℝ)) - b / (M₀ : ℝ))
    (hB : (((bigPrimeSet M₀ (Q * M₀)).card : ℕ) : ℝ) ≤ B) :
    rho * ((H : ℝ) * S - B)
      ≤ ((((Finset.Ioc X (X + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  set M : Finset ℕ := bigPrimeSet M₀ (Q * M₀) with hMdef
  set P : Finset ℕ := M.filter (fun p => X / p ∉ badStart y hy) with hPdef
  have hPM : P ⊆ M := Finset.filter_subset _ _
  have hlarge : ∀ p ∈ M, M₀ < p := fun p hp => lt_of_mem_bigPrimeSet hp
  -- the harmonic mass survives the device
  have hharm := sum_inv_good_markers_ge (X := X) (M₀ := M₀) (K := K) (S := badStart y hy)
    (M := M) (Pi := Pi) (b := b) hM₀ hlarge hsep hpair hbthr hb0
  have hSP : S ≤ ∑ p ∈ P, 1 / (p : ℝ) := le_trans hS hharm
  have hBP : ((P.card : ℕ) : ℝ) ≤ B :=
    le_trans (Nat.cast_le.2 (Finset.card_le_card hPM)) hB
  refine card_sign_window_ge_of_goodStarts (y := y) (hy := hy) (M₀ := M₀) (Q := Q)
    P hPM hXH hrho hσ ?_ hSP hBP
  intro p hp
  have hpM : p ∈ M := hPM hp
  have hpnot : X / p ∉ badStart y hy := (Finset.mem_filter.1 hp).2
  have hppos : 0 < p := (prime_of_mem_bigPrimeSet hpM).pos
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ht1 : 1 ≤ X / p := by
    have hlow := hstartlow p hpM
    have : (1 : ℝ) ≤ ((X / p : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  exact exists_good_marker_data hy4 hy0 hsy hppos ht1 (hstartlow p hpM) (hstarthigh p hpM)
    hpnot (hfit p hpM) (hsupply p hpM)

end RHTower.Sieve
