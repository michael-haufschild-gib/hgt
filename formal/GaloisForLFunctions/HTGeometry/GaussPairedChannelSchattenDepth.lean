import GaloisForLFunctions.HTGeometry.ArithmeticComplementRank
import Mathlib.NumberTheory.PrimeCounting

/-!
# Gauss-paired channel residue and cofinal Schatten depth

The arithmetic residue attached to one Gauss component is strictly positive, finite channel
residues add to a positive total, and the critical channel depth `2 * π(N)` is cofinal.  The same
module records the exact coefficient/complement rank split used by a nonautonomous realization.
-/

namespace GaloisForLFunctions.RHTower

open Filter Module Submodule
open scoped Nat.Prime Topology

noncomputable section

/-- Exact arithmetic Dixmier residue of one `m`-place Gauss channel at the prime `p`. -/
def gaussChannelResidue (m : ℕ) (p : Nat.Primes) : ℝ :=
  2 * ((p : ℝ) - 1) ^ (2 * m) * ((p : ℝ) ^ m - 1) ^ 2 /
    ((p : ℝ) ^ (2 * m) * (m : ℝ) ^ 2 * Real.log (p : ℝ))

/-- Every genuine Gauss channel has strictly positive arithmetic residue. -/
theorem gaussChannelResidue_pos {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    0 < gaussChannelResidue m p := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hm0 : m ≠ 0 := by omega
  have hpow : (1 : ℝ) < (p : ℝ) ^ m := one_lt_pow₀ hp hm0
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  rw [gaussChannelResidue]
  exact div_pos
    (mul_pos (mul_pos (by positivity) (pow_pos (sub_pos.mpr hp) _))
      (pow_pos (sub_pos.mpr hpow) _))
    (mul_pos (mul_pos (pow_pos (lt_trans zero_lt_one hp) _) (pow_pos hmR _))
      (Real.log_pos hp))

/-- The residue formula is independent of the Gauss-component label. -/
def gaussComponentResidue {m : ℕ} (_k : Fin m) (p : Nat.Primes) : ℝ :=
  gaussChannelResidue m p

theorem gaussChannelResidue_independent_of_component
    {m : ℕ} (p : Nat.Primes) (k l : Fin m) :
    gaussComponentResidue k p = gaussComponentResidue l p := by
  rfl

/-- Total residue of a finite labeled channel system. -/
def gaussPairedChannelResidue {J : Type*} [Fintype J]
    (m : ℕ) (prime : J → Nat.Primes) : ℝ :=
  ∑ j, gaussChannelResidue m (prime j)

/-- Every nonempty finite Gauss-paired system has nonzero positive total residue. -/
theorem gaussPairedChannelResidue_pos
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ} (hm : 1 ≤ m)
    (prime : J → Nat.Primes) :
    0 < gaussPairedChannelResidue m prime := by
  rw [gaussPairedChannelResidue]
  exact Finset.sum_pos (fun j _ => gaussChannelResidue_pos hm (prime j)) Finset.univ_nonempty

/-- Critical weak-Schatten exponent of the channel-resolved cutoff at `N`. -/
def gaussPairedCriticalDepth (N : ℕ) : ℕ :=
  2 * Nat.primeCounting N

/-- The channel-resolved critical depth tends to infinity with the prime aperture. -/
theorem tendsto_gaussPairedCriticalDepth :
    Tendsto gaussPairedCriticalDepth atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall fun N => by rw [gaussPairedCriticalDepth]; omega)
    Nat.tendsto_primeCounting

/-- No fixed real Schatten exponent dominates all channel-resolved critical depths. -/
theorem exists_gaussPairedCriticalDepth_gt (q : ℝ) :
    ∃ N : ℕ, q < gaussPairedCriticalDepth N := by
  obtain ⟨n, hn⟩ := exists_nat_gt q
  obtain ⟨N, hN⟩ := Nat.surjective_primeCounting n
  refine ⟨N, ?_⟩
  rw [gaussPairedCriticalDepth, hN]
  exact hn.trans_le (by exact_mod_cast Nat.le_mul_of_pos_left n (by omega : 0 < 2))

/-- No fixed integer regularization order stays strictly above every critical depth. -/
theorem exists_gaussPairedCriticalDepth_ge (r : ℕ) :
    ∃ N : ℕ, r ≤ gaussPairedCriticalDepth N := by
  obtain ⟨N, hN⟩ := Nat.surjective_primeCounting r
  refine ⟨N, ?_⟩
  rw [gaussPairedCriticalDepth, hN]
  omega

/-- At a fixed aperture, the least integer determinant order above the critical depth is its
successor. -/
theorem gaussPaired_regularizationOrder_iff (N r : ℕ) :
    gaussPairedCriticalDepth N < r ↔ gaussPairedCriticalDepth N + 1 ≤ r :=
  Nat.lt_iff_add_one_le

/-- Exact arithmetic complement split: prime-state rank equals the intersection rank plus the
quotient rank. -/
theorem finrank_eq_arithmeticIntersection_add_complement
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (V W : Submodule K E) :
    finrank K ↥V = finrank K ↥(V ⊓ W) +
      finrank K (↥V ⧸ Submodule.comap V.subtype W) := by
  have hquot := Submodule.finrank_quotient_add_finrank
    (R := K) (Submodule.comap V.subtype W)
  have hintersection :
      finrank K ↥(Submodule.comap V.subtype W) = finrank K ↥(V ⊓ W) := by
    rw [← Submodule.finrank_map_subtype_eq V (Submodule.comap V.subtype W),
      Submodule.map_comap_subtype]
  omega

/-- Coefficient--state budget specialized to a prime module of rank `π(N)`. -/
theorem primeCounting_le_coefficientRank_add_twice_stateCapacity
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (N kappa : ℕ) (V D : Submodule ℚ E)
    (hV : finrank ℚ ↥V = Nat.primeCounting N)
    (hstate : finrank ℚ (↥V ⧸ Submodule.comap V.subtype D) ≤ 2 * kappa) :
    Nat.primeCounting N ≤ finrank ℚ ↥(V ⊓ D) + 2 * kappa := by
  rw [← hV, finrank_eq_arithmeticIntersection_add_complement V D]
  omega

end

end GaloisForLFunctions.RHTower
