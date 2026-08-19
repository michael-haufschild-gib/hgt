import GaloisForLFunctions.RHTower.Sieve.MarkerSignFlip
import GaloisForLFunctions.RHTower.Sieve.SumCellMatching

/-!
# Counting integers of a prescribed Möbius sign in a window, marker by marker

A marker family whose cells each carry a definite proportion of one Möbius sign produces that
proportion of the *other* sign among the products, and the products are distinct.  Summing the cells
harmonically — rather than bounding every cell by the smallest — the window `(X, X+H]` receives at
least `ϱ·(H·∑_{p} 1/p − #P)` integers of the prescribed sign.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- A cofactor of a marker cell is below the marker, when the window fits inside `M₀²`. -/
theorem cofactor_lt_marker {X H M₀ Q : ℕ} {P : Finset ℕ} (hPsub : P ⊆ bigPrimeSet M₀ (Q * M₀))
    (hXH : X + H ≤ M₀ * M₀) :
    ∀ p ∈ P, ∀ a ∈ windowCell X H p, ∀ r ∈ P, a < r := by
  intro p hp a ha r hr
  have hppos : 0 < p := (prime_of_mem_bigPrimeSet (hPsub hp)).pos
  have hprod := ((mem_windowCell_iff hppos).1 ha).2
  have hMp : M₀ < p := lt_of_mem_bigPrimeSet (hPsub hp)
  have hMr : M₀ < r := lt_of_mem_bigPrimeSet (hPsub hr)
  have haM : a ≤ M₀ := by
    by_contra hcon
    have h1 : M₀ + 1 ≤ a := by omega
    have h2 : M₀ + 1 ≤ p := by omega
    have h3 : (M₀ + 1) * (M₀ + 1) ≤ a * p := Nat.mul_le_mul h1 h2
    have h4 : a * p ≤ M₀ * M₀ := le_trans hprod hXH
    nlinarith
  omega

/-- **The window receives the marker block's sign count.** -/
theorem card_sign_window_ge {X H M₀ Q : ℕ} {σ : ℤ} {rho S B : ℝ}
    (P : Finset ℕ) (hPsub : P ⊆ bigPrimeSet M₀ (Q * M₀)) (hXH : X + H ≤ M₀ * M₀)
    (hrho : 0 ≤ rho)
    (hcell : ∀ p ∈ P, rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ ((((windowCell X H p).filter (fun b => moebius b = -σ)).card : ℕ) : ℝ))
    (hS : S ≤ ∑ p ∈ P, 1 / (p : ℝ)) (hB : ((P.card : ℕ) : ℝ) ≤ B) :
    rho * ((H : ℝ) * S - B)
      ≤ ((((Finset.Ioc X (X + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  set C : ℕ → Finset ℕ :=
    fun p => (windowCell X H p).filter (fun b => moebius b = -σ) with hC
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => prime_of_mem_bigPrimeSet (hPsub hp)
  have hposW : ∀ p ∈ P, ∀ a ∈ windowCell X H p, 0 < a := fun p hp a ha =>
    pos_of_mem_windowCell (hprime p hp).pos ha
  have hposC : ∀ p ∈ P, ∀ a ∈ C p, 0 < a := by
    intro p hp a ha
    exact hposW p hp a (Finset.mem_filter.1 ha).1
  have hsmallW := cofactor_lt_marker hPsub hXH
  have hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r := by
    intro p hp a ha r hr
    exact hsmallW p hp a (Finset.mem_filter.1 ha).1 r hr
  -- the block is exactly the sum of the cells
  have hexact : ((RHTower.markerBlockTargets P C).card : ℕ) = ∑ p ∈ P, (C p).card :=
    RHTower.card_markerBlockTargets P C hprime hposC hsmall
  -- the block sits in the window and carries the sign
  have hsub : RHTower.markerBlockTargets P C
      ⊆ (Finset.Ioc X (X + H)).filter (fun n => moebius n = σ) := by
    intro n hn
    obtain ⟨p, hp, a, ha, rfl, hsign⟩ :=
      moebius_of_mem_markerBlockTargets hprime hposC hsmall hn
    have haW : a ∈ windowCell X H p := (Finset.mem_filter.1 ha).1
    have hasign : moebius a = -σ := (Finset.mem_filter.1 ha).2
    have hw := (mem_windowCell_iff (hprime p hp).pos).1 haW
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hw.1, hw.2⟩, ?_⟩
    rw [hsign, hasign]
    ring
  -- the harmonic lower bound on the block
  have hterm : ∀ p ∈ P, rho * ((H : ℝ) / (p : ℝ) - 1) ≤ (((C p).card : ℕ) : ℝ) := hcell
  have hsum : rho * ((H : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) - ((P.card : ℕ) : ℝ))
      ≤ ∑ p ∈ P, (((C p).card : ℕ) : ℝ) := by
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
    have hexp : ∑ p ∈ P, rho * ((H : ℝ) / (p : ℝ) - 1)
        = rho * ((H : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) - ((P.card : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, mul_sub, Finset.mul_sum]
      rw [show ∑ p ∈ P, rho * ((H : ℝ) / (p : ℝ) - 1)
          = ∑ p ∈ P, (rho * ((H : ℝ) * (1 / (p : ℝ))) - rho * 1) from
        Finset.sum_congr rfl fun p _ => by rw [mul_one_div]; ring]
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hexp]
  have hmono : rho * ((H : ℝ) * S - B)
      ≤ rho * ((H : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) - ((P.card : ℕ) : ℝ)) := by
    have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
    have h1 : (H : ℝ) * S ≤ (H : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hS hH
    exact mul_le_mul_of_nonneg_left (by linarith) hrho
  have hcast : ((∑ p ∈ P, (C p).card : ℕ) : ℝ) = ∑ p ∈ P, (((C p).card : ℕ) : ℝ) := by
    push_cast
    ring
  have hcard : (((RHTower.markerBlockTargets P C).card : ℕ) : ℝ)
      ≤ ((((Finset.Ioc X (X + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) :=
    Nat.cast_le.2 (Finset.card_le_card hsub)
  have hchain : rho * ((H : ℝ) * S - B)
      ≤ (((RHTower.markerBlockTargets P C).card : ℕ) : ℝ) := by
    rw [hexact, hcast]
    linarith [hmono, hsum]
  linarith [hchain, hcard]

end RHTower.Sieve
