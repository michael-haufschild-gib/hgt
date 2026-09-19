import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalSharpTransportPressure
import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalBidirectionalTransportRangeNoGo
import GaloisForLFunctions.RHTower.Sieve.LogLogTelescope

/-!
# Sharp bicausal transport pressure for the critical CCM--FU source

The existing two-sided locality law retained only half of a prime atom.  This module performs the
source accounting without that loss.  A bicausal block does, however, contain the prime cell's
own polar step.  The exact external transport burden is therefore

`log p / p - (log p - log (p - 1))`,

not the full prime atom.  After converting logarithmic polar span to event-label radius, this
forces at least `log p - 3 / 2` cells of combined bicausal memory.  Thus every proposed literal
CCM--FU cancellation law needs asymptotically full logarithmic, rather than half-logarithmic,
cross-cell transport.

This is a source-level necessary condition only.  It preserves the signed prime--polar current
and does not assert the RH-bearing global cancellation bound.
-/

namespace RHTower

noncomputable section

private theorem sub_sub_add_eq
    {p L : ℕ} (h : L + 2 ≤ p) :
    p - L - 2 + L = p - 2 := by
  have hsum : p - (L + 2) + (L + 2) = p := Nat.sub_add_cancel h
  rw [Nat.sub_sub]
  calc
    p - (L + 2) + L = (p - (L + 2) + L + 2) - 2 := by
      symm
      exact Nat.add_sub_cancel _ _
    _ = (p - (L + 2) + (L + 2)) - 2 := by
      rw [Nat.add_assoc]
    _ = p - 2 := by rw [hsum]

/-- A nonpositive bicausal critical-source block can spend the full prime atom only after
subtracting its own adjacent polar drift.  The remaining quantity is the exact outside-block
transport budget. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_net_log_span
    {p L R : ℕ} (hp : p.Prime) (hleft : L + 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0) :
    Real.log (p : ℝ) / p -
      (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) ≤
      (Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
        (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) := by
  let q : ℕ := p - L
  let W : ℕ := L + R
  have hq3 : 3 ≤ q := by
    dsimp only [q]
    omega
  have hqW : q + W = p + R := by
    dsimp only [q, W]
    calc
      p - L + (L + R) = (p - L + L) + R := by rw [← Nat.add_assoc]
      _ = p + R := by rw [Nat.sub_add_cancel (by omega)]
  have harg : q - 2 + W = p - 2 + R := by
    dsimp only [q, W]
    calc
      p - L - 2 + (L + R) = (p - L - 2 + L) + R := by rw [← Nat.add_assoc]
      _ = p - 2 + R := by rw [sub_sub_add_eq (by omega)]
  have hblock' : suzukiCheckpointCriticalMertensDeviationCore (q - 2 + W) -
      suzukiCheckpointCriticalMertensDeviationCore (q - 3) ≤ 0 := by
    rw [harg]
    exact hblock
  have hp_mem : p ∈ Finset.Icc q (q + W) := by
    dsimp only [q, W]
    exact Finset.mem_Icc.mpr (by omega)
  have hbudget :=
    suzukiCheckpointCriticalMertensDeviationCore_finsetPrime_nonpos_forwardBlock_full_log_budget
      (p := q) (L := W) hq3 hblock' ({p} : Finset ℕ)
      (by
        intro x hx
        have hx' : x = p := by simpa using hx
        subst x
        exact hp_mem)
      (by
        intro x hx
        have hx' : x = p := by simpa using hx
        simpa [hx'])
  have hbudget' : Real.log (p : ℝ) / p ≤
      Real.log ((p + R : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ) := by
    simp only [Finset.sum_singleton] at hbudget
    rw [hqW] at hbudget
    simpa only [q] using hbudget
  have hsplit :
      Real.log ((p + R : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ) =
        (Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
          (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) +
            (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) := by ring
  rw [hsplit] at hbudget'
  linarith

/-- A nonpositive bicausal block must pay the full harmonic mass of every selected finite family
of literal prime atoms.  Each selected atom's adjacent polar cell is retained as local debt, so
the right-hand side is exactly the polar budget external to those selected cells. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_finsetPrime_nonpos_bidirectionalBlock_forces_net_log_budget
    {p L R : ℕ} (hleft : L + 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc (p - L) (p + R))
    (hprime : ∀ q ∈ S, q.Prime) :
    (∑ q ∈ S, (Real.log (q : ℝ) / q -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)))) ≤
      (Real.log ((p + R : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) -
        ∑ q ∈ S, (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) := by
  let a : ℕ := p - L
  let W : ℕ := L + R
  have ha3 : 3 ≤ a := by
    dsimp only [a]
    omega
  have haW : a + W = p + R := by
    dsimp only [a, W]
    calc
      p - L + (L + R) = (p - L + L) + R := by rw [← Nat.add_assoc]
      _ = p + R := by rw [Nat.sub_add_cancel (by omega)]
  have harg : a - 2 + W = p - 2 + R := by
    dsimp only [a, W]
    calc
      p - L - 2 + (L + R) = (p - L - 2 + L) + R := by rw [← Nat.add_assoc]
      _ = p - 2 + R := by rw [sub_sub_add_eq (by omega)]
  have hblock' : suzukiCheckpointCriticalMertensDeviationCore (a - 2 + W) -
      suzukiCheckpointCriticalMertensDeviationCore (a - 3) ≤ 0 := by
    rw [harg]
    exact hblock
  have hS' : S ⊆ Finset.Icc a (a + W) := by
    intro q hq
    have hq' := hS hq
    rw [haW]
    simpa only [a] using hq'
  have hbudget :=
    suzukiCheckpointCriticalMertensDeviationCore_finsetPrime_nonpos_forwardBlock_full_log_budget
      (p := a) (L := W) ha3 hblock' S hS' hprime
  have hbudget' : (∑ q ∈ S, Real.log (q : ℝ) / q) ≤
      Real.log ((p + R : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ) := by
    rw [haW] at hbudget
    simpa only [a] using hbudget
  rw [Finset.sum_sub_distrib]
  linarith

private theorem sum_polar_cells_Icc_eq_log_span
    {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b,
      (Real.log ((j : ℕ) : ℝ) - Real.log ((j - 1 : ℕ) : ℝ)) =
        Real.log ((b : ℕ) : ℝ) - Real.log ((a - 1 : ℕ) : ℝ) := by
  have hIcc : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc]
  have htel := RHTower.Sieve.sum_Ico_telescope
    (fun j : ℕ => Real.log ((j - 1 : ℕ) : ℝ)) (show a ≤ b + 1 by omega)
  simpa only [Nat.add_sub_cancel] using htel

/-- After each selected prime has paid its own adjacent polar cell, a nonpositive bicausal block
can use only the literal polar cells not selected by that prime family.  This is an exact finite
source partition, so selected prime cells cannot be counted again as transport capacity. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_finsetPrime_nonpos_bidirectionalBlock_forces_external_polar_capacity
    {p L R : ℕ} (hleft : L + 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc (p - L) (p + R))
    (hprime : ∀ q ∈ S, q.Prime) :
    (∑ q ∈ S, (Real.log (q : ℝ) / q -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)))) ≤
      ∑ q ∈ (Finset.Icc (p - L) (p + R)) \ S,
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) := by
  have hbudget :=
    suzukiCheckpointCriticalMertensDeviationCore_finsetPrime_nonpos_bidirectionalBlock_forces_net_log_budget
      hleft hblock S hS hprime
  have hspan := sum_polar_cells_Icc_eq_log_span
    (a := p - L) (b := p + R) (by omega)
  calc
    _ ≤ (Real.log ((p + R : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) -
        ∑ q ∈ S, (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) := hbudget
    _ = (∑ q ∈ Finset.Icc (p - L) (p + R),
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) -
        ∑ q ∈ S, (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) := by rw [hspan]
    _ = _ := by
      rw [← Finset.sum_sdiff hS]
      ring

private theorem backward_drift_le
    {p L : ℕ} (hLP : L + 2 ≤ p) :
    Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ) ≤
      (L : ℝ) / ((p - L - 1 : ℕ) : ℝ) := by
  have hdenNat : 0 < p - L - 1 := by omega
  have hnumNat : 0 < p - 1 := by omega
  have hden : (0 : ℝ) < ((p - L - 1 : ℕ) : ℝ) := by exact_mod_cast hdenNat
  have hnum : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hnumNat
  have hbasepos : (0 : ℝ) < -1 + ((p - L : ℕ) : ℝ) := by
    have hlt : (1 : ℝ) < ((p - L : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < p - L by omega)
    linarith
  have hsplit : (p : ℝ) = ((p - L : ℕ) : ℝ) + L := by
    exact_mod_cast (Nat.sub_add_cancel (show L ≤ p by omega)).symm
  rw [← Real.log_div hnum.ne' hden.ne']
  calc
    Real.log (((p - 1 : ℕ) : ℝ) / ((p - L - 1 : ℕ) : ℝ)) ≤
        ((p - 1 : ℕ) : ℝ) / ((p - L - 1 : ℕ) : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hnum hden)
    _ = (L : ℝ) / ((p - L - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ p),
        Nat.cast_sub (by omega : 1 ≤ p - L)]
      push_cast
      rw [hsplit]
      have hinv : (-1 + ((p - L : ℕ) : ℝ)) *
          (-1 + ((p - L : ℕ) : ℝ))⁻¹ = 1 :=
        mul_inv_cancel₀ hbasepos.ne'
      linear_combination hinv

/-- Bicausal transport of a nonpositive literal source block must cover the exact prime atom
minus the local polar step before it can use exterior polar drift. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_net_combined_log_radius
    {p L R : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (htw : 2 * (L + 1) ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0) :
    Real.log (p : ℝ) -
      (p : ℝ) * (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) ≤
        2 * (L : ℝ) + R := by
  have hleft : L + 3 ≤ p := by omega
  have hspan :=
    suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_net_log_span
      hp hleft hblock
  have hback := backward_drift_le (show L + 2 ≤ p by omega)
  have hforward := log_suzukiCheckpointCritical_forwardBlock_drift_le
    (p := p) (L := R) hp.one_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hdenNat : 0 < p - L - 1 := by omega
  have hden : (0 : ℝ) < ((p - L - 1 : ℕ) : ℝ) := by exact_mod_cast hdenNat
  have htwR : (2 : ℝ) * ((L : ℝ) + 1) ≤ p := by
    exact_mod_cast htw
  have hdenComp : (p : ℝ) ≤ 2 * ((p - L - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p - L), Nat.cast_sub (by omega : L ≤ p)]
    push_cast
    nlinarith [htwR]
  have hbackScale : (L : ℝ) / ((p - L - 1 : ℕ) : ℝ) ≤
      (2 * (L : ℝ)) / p := by
    apply (div_le_div_iff₀ hden hp0).2
    nlinarith [mul_le_mul_of_nonneg_left hdenComp (Nat.cast_nonneg L)]
  have hsum :
      (Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
          (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) ≤
        (2 * (L : ℝ) + R) / p := by
    calc
      (Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
          (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) ≤
          (L : ℝ) / ((p - L - 1 : ℕ) : ℝ) + (R : ℝ) / p :=
        add_le_add hback hforward
      _ ≤ (2 * (L : ℝ)) / p + (R : ℝ) / p :=
        add_le_add hbackScale le_rfl
      _ = (2 * (L : ℝ) + R) / p := by ring
  have hbound : Real.log (p : ℝ) / p -
      (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) ≤
      (2 * (L : ℝ) + R) / p :=
    hspan.trans hsum
  calc
    Real.log (p : ℝ) -
        (p : ℝ) * (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) =
        (Real.log (p : ℝ) / p -
          (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ))) * p := by
            field_simp
    _ ≤ ((2 * (L : ℝ) + R) / p) * p :=
      mul_le_mul_of_nonneg_right hbound hp0.le
    _ = 2 * (L : ℝ) + R := by field_simp

private theorem prime_local_polar_debt_le_three_halves
    {p : ℕ} (hp3 : 3 ≤ p) :
    (p : ℝ) * (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) ≤ 3 / 2 := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hpm1Nat : 0 < p - 1 := by omega
  have hpm1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hpm1Nat
  have hratio :
      Real.log ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤
        (p : ℝ) / ((p - 1 : ℕ) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hp0 hpm1)
  have hquot : (p : ℝ) / ((p - 1 : ℕ) : ℝ) - 1 =
      1 / ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    have hden : (p : ℝ) - 1 ≠ 0 := by
      have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      nlinarith
    field_simp [hden]
    ring
  have hfrac : (p : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ 3 / 2 := by
    apply (div_le_iff₀ hpm1).2
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    nlinarith
  have hlog : Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) =
      Real.log ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
    rw [Real.log_div hp0.ne' hpm1.ne']
  rw [hlog]
  calc
    (p : ℝ) * Real.log ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤
        (p : ℝ) * ((p : ℝ) / ((p - 1 : ℕ) : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hratio hp0.le
    _ = (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by rw [hquot]; field_simp
    _ ≤ 3 / 2 := hfrac

/-- Every nonpositive bicausal block around a prime has combined event-label radius at least
`log p - 3 / 2`.  This is asymptotically sharp at the prime-cell scale and doubles the prior
half-logarithmic obstruction. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_combined_log_radius_sub_three_halves
    {p L R : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (htw : 2 * (L + 1) ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0) :
    Real.log (p : ℝ) - 3 / 2 ≤ 2 * (L : ℝ) + R := by
  have hnet :=
    suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_net_combined_log_radius
      hp hp3 htw hblock
  have hdebt := prime_local_polar_debt_le_three_halves hp3
  calc
    Real.log (p : ℝ) - 3 / 2 ≤
        Real.log (p : ℝ) -
          (p : ℝ) * (Real.log (p : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) := by
      linarith
    _ ≤ 2 * (L : ℝ) + R := hnet

end

end RHTower
