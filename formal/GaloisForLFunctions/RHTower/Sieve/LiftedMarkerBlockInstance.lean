import GaloisForLFunctions.RHTower.Sieve.LiftedMarkerFrame

/-!
# The lifted marker block at its own parameters

Every geometric hypothesis of `Sieve/LiftedMarkerBlock.card_sign_window_ge_block` is discharged by
the frame of `Sieve/LiftedMarkerFrame`.  What is left is the arithmetic of the block itself: the
shifted-pair budget, the harmonic mass of the markers, their number, and the device threshold.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The sign count of the physical window at the lifted parameters.** -/
theorem card_sign_window_ge_lifted {β : ℝ} {u : ℕ} {σ : ℤ} {S B Pi b : ℝ}
    (hu : 0 < u) (hσ : σ = 1 ∨ σ = -1)
    (hy3 : 3 ≤ cardLength β (liftScale u))
    (hW1 : 1 ≤ liftFactor u)
    (hL : u + liftCellLen β u ≤ u * liftFactor u)
    (hpair : ∑ d ∈ Finset.Icc 1 (4 * liftFactor u),
        ((((bigPrimeSet (liftMarkerScale u) (2 * liftMarkerScale u)).filter
          (fun p => p + d ∈ bigPrimeSet (liftMarkerScale u)
            (2 * liftMarkerScale u))).card : ℕ) : ℝ) ≤ Pi)
    (hbthr : (((badStart (liftScale u) (cardLength β (liftScale u))).card : ℕ) : ℝ)
      * ((((bigPrimeSet (liftMarkerScale u) (2 * liftMarkerScale u)).card : ℕ) : ℝ) + 2 * Pi)
        ≤ b ^ 2)
    (hb0 : 0 ≤ b)
    (hS : S ≤ (∑ p ∈ bigPrimeSet (liftMarkerScale u) (2 * liftMarkerScale u), 1 / (p : ℝ))
      - b / ((liftMarkerScale u : ℕ) : ℝ))
    (hB : (((bigPrimeSet (liftMarkerScale u) (2 * liftMarkerScale u)).card : ℕ) : ℝ) ≤ B) :
    (squarefreeDensity / 256)
        * (((liftWindow β u : ℕ) : ℝ) * S - B)
      ≤ ((((Finset.Ioc (liftPhysScale u) (liftPhysScale u + liftWindow β u)).filter
          (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hM0 : 0 < liftMarkerScale u := by
    rw [liftMarkerScale]
    have : 0 < 2 * u := by omega
    exact Nat.mul_pos this (by omega)
  have hy4 : (4 : ℝ) ≤ liftScale u := by
    rw [liftScale_eq]
    have : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
    nlinarith
  have hy0 : (0 : ℝ) < cardLength β (liftScale u) := cardLength_pos _ _
  have hQM : 2 * liftMarkerScale u = 2 * liftMarkerScale u := rfl
  refine card_sign_window_ge_block (y := liftScale u) (hy := cardLength β (liftScale u))
    (X := liftPhysScale u) (H := liftWindow β u) (M₀ := liftMarkerScale u) (Q := 2)
    (m := 2 * u) (K := 4 * liftFactor u) (σ := σ) (rho := squarefreeDensity / 256)
    (S := S) (B := B) (Pi := Pi) (b := b)
    hy4 hy0 (sqrt_liftScale u) hσ (div_nonneg squarefreeDensity_pos.le (by norm_num)) (by omega) hM0
    (liftPhys_add_window_le hL) ?_ ?_ ?_ ?_ ?_ hpair hbthr hb0 hS hB
  · intro p hp
    have hple : p ≤ 2 * liftMarkerScale u := (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).2
    have hppos : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
    have := liftStart_ge hppos hple
    have hcast : ((u : ℕ) : ℝ) ≤ ((liftPhysScale u / p : ℕ) : ℝ) := by exact_mod_cast this
    have h2u : (((2 * u : ℕ)) : ℝ) / 2 = (u : ℝ) := by push_cast; ring
    rw [h2u]
    exact hcast
  · intro p hp
    have hpM : liftMarkerScale u < p := lt_of_mem_bigPrimeSet hp
    have := liftStart_lt hu hpM
    have hnat : liftPhysScale u / p + 1 ≤ 2 * u := by omega
    exact_mod_cast hnat
  · intro p hp
    have hpM : liftMarkerScale u < p := lt_of_mem_bigPrimeSet hp
    have hple : p ≤ 2 * liftMarkerScale u := (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).2
    exact lift_fit hu hpM hple
  · intro p hp
    have hpM : liftMarkerScale u < p := lt_of_mem_bigPrimeSet hp
    have hple : p ≤ 2 * liftMarkerScale u := (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).2
    exact lift_supply hu hpM hple hM0 hy3
  · intro p hp q _ hpq heq
    have hple : p ≤ 2 * liftMarkerScale u := (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).2
    have hppos : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
    exact lift_separation hu hppos hpq hple heq

end

end RHTower.Sieve
