import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.HarmonicMassFollowsDelayedCounting
import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant
import GaloisForLFunctions.BezoutValuationIncidence.UniformLagWindowCovarianceAtQuadraticOrder
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesArePrimeQuasimodes

/-!
# A harmonic lower frame bound for growing Ramanujan families

Primitive roots of different orders are disjoint. Their normalized coefficient
mass is exactly the conductor coefficient mass. The two-sided large sieve
therefore gives a counting loss of `Q(Q-1)` for a whole Ramanujan packet.
Harmonic summation turns that loss into `H_{Q(Q-1)}` without summing pairwise
period errors. Every coefficient vector is controlled at the same horizon.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory

/-- The actual normalized Ramanujan packet has the sharp two-sided window bound. -/
theorem abs_ramanujanPacket_window_discrepancy_le {Q : ℕ} (hQ : 2 ≤ Q)
    (c : ℕ → ℝ) (A K : ℕ) :
    |(∑ n ∈ Icc (A + 1) (A + K),
        (∑ m ∈ Icc 1 Q, c m * normalizedRamanujanMode m n) ^ 2) -
      K * ∑ m ∈ Icc 1 Q, c m ^ 2| ≤
        ((Q : ℝ) * ((Q : ℝ) - 1)) * ∑ m ∈ Icc 1 Q, c m ^ 2 := by
  let a : ℂ → ℂ := fun ζ => (c (orderOf ζ) / Real.sqrt ((orderOf ζ).totient : ℝ) : ℝ)
  have hroots : ∀ ζ ∈ responseRoots Q, ∃ d, 1 ≤ d ∧ d ≤ Q ∧ ζ ^ d = 1 := by
    intro ζ hζ
    have ho := mem_Icc.mp (orderOf_mem_Icc_of_mem_responseRoots hζ)
    exact ⟨orderOf ζ, ho.1, ho.2, (IsPrimitiveRoot.orderOf ζ).pow_eq_one⟩
  have hpacket (n : ℕ) :
      (∑ ζ ∈ responseRoots Q, a ζ * ζ ^ n) =
        ((∑ m ∈ Icc 1 Q, c m * normalizedRamanujanMode m n : ℝ) : ℂ) := by
    change (∑ ζ ∈ responseRoots Q,
      ((c (orderOf ζ) / Real.sqrt ((orderOf ζ).totient : ℝ) : ℝ) : ℂ) * ζ ^ n) = _
    rw [sum_responseRoots_orderOf_mul_pow Q (fun m => c m / Real.sqrt (m.totient : ℝ)) n]
    congr 1
    apply sum_congr rfl
    intro m hm
    rw [ramanujanLagWeight_eq_ramanujanLagCoefficient,
      normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hm).1]
    ring
  have hcoef : (∑ ζ ∈ responseRoots Q, ‖a ζ‖ ^ 2) = ∑ m ∈ Icc 1 Q, c m ^ 2 := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [sum_responseRoots_orderOf Q (fun m => (c m / Real.sqrt (m.totient : ℝ)) ^ 2)]
    apply sum_congr rfl
    intro m hm
    have hφ : (0 : ℝ) < m.totient := by
      exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hm).1
    rw [div_pow, Real.sq_sqrt hφ.le]
    field_simp
  have h := abs_window_rootsOfUnity_sub_le hQ hroots a A K
  simpa only [hpacket, Complex.norm_real, Real.norm_eq_abs, sq_abs, hcoef] using h

private theorem ramanujanPacket_prefix_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (c : ℕ → ℝ) (L : ℕ) :
      ((L : ℝ) - (Q * (Q - 1) : ℕ)) * (∑ m ∈ Icc 1 Q, c m ^ 2) ≤
        ∑ i ∈ range L, (∑ m ∈ Icc 1 Q, c m * normalizedRamanujanMode m (i + 1)) ^ 2 := by
    have h := (abs_le.mp (abs_ramanujanPacket_window_discrepancy_le hQ c 0 L)).1
    simp only [zero_add] at h
    have hsum : (∑ n ∈ Icc 1 L, (∑ m ∈ Icc 1 Q, c m * normalizedRamanujanMode m n) ^ 2) =
        ∑ i ∈ range L, (∑ m ∈ Icc 1 Q, c m * normalizedRamanujanMode m (i + 1)) ^ 2 :=
      _root_.RHTower.RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range _ _
    rw [hsum] at h
    have hcast : ((Q * (Q - 1) : ℕ) : ℝ) = (Q : ℝ) * ((Q : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
    rw [hcast]
    nlinarith only [h]

private theorem ramanujanPolePacket_weighted_square (Q N : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ range N, (∑ m ∈ Icc 1 Q, c m * normalizedRamanujanMode m (i + 1)) ^ 2 /
      ((i : ℝ) + 1)) =
      ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, c m * ramanujanPoleProfile m n) ^ 2 := by
  rw [_root_.RHTower.RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp only [ramanujanPoleProfile, ← mul_div_assoc, ← sum_div, div_pow,
    Nat.cast_add, Nat.cast_one]
  rw [Real.sq_sqrt (by positivity)]

/-- All conductors up to `Q` retain harmonic mass with the single loss
`H_{Q(Q-1)}`, uniformly over every real coefficient vector and every horizon. -/
theorem ramanujanPoleProfile_family_harmonic_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (c : ℕ → ℝ) (N : ℕ) :
    ((harmonic N : ℝ) - (harmonic (Q * (Q - 1)) : ℝ)) *
        (∑ m ∈ Icc 1 Q, c m ^ 2) ≤
      ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, c m * ramanujanPoleProfile m n) ^ 2 := by
  have h := harmonic_mass_ge_of_delayed_prefix
    (fun i => (∑ m ∈ Icc 1 Q, c m * normalizedRamanujanMode m (i + 1)) ^ 2)
    (fun _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
    (Q * (Q - 1)) (ramanujanPacket_prefix_lower hQ c) N
  exact h.trans_eq (ramanujanPolePacket_weighted_square Q N c)

/-- The logarithmic lower frame constant has no loss beyond the conductor scale. -/
theorem ramanujanPoleProfile_family_logarithmic_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (c : ℕ → ℝ) (N : ℕ) :
    (Real.log ((N : ℝ) + 1) - Real.log ((Q * (Q - 1) : ℕ) + 1)) *
        (∑ m ∈ Icc 1 Q, c m ^ 2) ≤
      ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, c m * ramanujanPoleProfile m n) ^ 2 := by
  have h := logarithmic_mass_ge_of_delayed_prefix
    (fun i => (∑ m ∈ Icc 1 Q, c m * normalizedRamanujanMode m (i + 1)) ^ 2)
    (fun _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
    (Q * (Q - 1)) (ramanujanPacket_prefix_lower hQ c) N
  exact h.trans_eq (ramanujanPolePacket_weighted_square Q N c)

/-- A positive lower frame margin persists below the square-root conductor horizon. -/
theorem ramanujanPoleProfile_family_squareRoot_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (c : ℕ → ℝ) (N : ℕ) :
    (Real.log ((N : ℝ) + 1) - 2 * Real.log Q) * (∑ m ∈ Icc 1 Q, c m ^ 2) ≤
      ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, c m * ramanujanPoleProfile m n) ^ 2 := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hsize : (((Q * (Q - 1) : ℕ) : ℝ) + 1) ≤ (Q : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
    nlinarith only [hQR]
  have hlog := Real.log_le_log (by positivity) hsize
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  exact (mul_le_mul_of_nonneg_right (by linarith only [hlog])
    (sum_nonneg fun _ _ => sq_nonneg _)).trans
      (ramanujanPoleProfile_family_logarithmic_lower hQ c N)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ramanujanPoleProfile_family_harmonic_lower
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ramanujanPoleProfile_family_squareRoot_lower
