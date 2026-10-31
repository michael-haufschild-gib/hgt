import GaloisForLFunctions.CriticalScaleArithmeticRigidity.HarmonicPoleCentering
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# The sharp logarithmic scale of the arithmetic prime generator

The active-prime mass differs from the exact coherent pole norm by a
convergent correction of at most eight. The generator's optimal relative
square constant therefore lies between `B_Q` and `B_Q+8`, even when inputs
are restricted to the actual harmonic pole hyperplane.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SelectiveMultiscaleArithmeticPositivity

/-- The excess of tower activity over coherent pole response is a convergent prime sum. -/
theorem primeActivityMass_sub_primePoleScale (Q : ℕ) :
    primeActivityMass Q - primePoleScale Q =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [primeActivityMass, primePoleScale, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hpm : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hp1).ne'
  field_simp [hp0, hpm]
  ring

/-- All conductor sectors have at most an absolute additive excess over the sharp pole norm. -/
theorem primeActivityMass_le_primePoleScale_add_eight (Q : ℕ) :
    primeActivityMass Q ≤ primePoleScale Q + 8 := by
  have hset : (Icc 1 Q).filter Nat.Prime = Nat.primesBelow (Q + 1) := by
    ext p
    simp only [mem_filter, mem_Icc, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hp1, hpQ⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpQ, hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
  have h := _root_.RHTower.sum_primesBelow_log_div_le (Q + 1)
  rw [← hset, ← primeActivityMass_sub_primePoleScale] at h
  linarith only [h]

/-- The complete arithmetic generator has leading sector cost `log Q` with coefficient one. -/
theorem arithmeticPrimeGenerator_period_sq_le_mertens_add (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (fun n => arithmeticPrimeGenerator Q a n ^ 2) ≤
      (primePoleScale Q + 8) * primeAdjunctionMass Q a :=
  (arithmeticPrimeGenerator_period_sq_le Q a).trans
    (mul_le_mul_of_nonneg_right (primeActivityMass_le_primePoleScale_add_eight Q)
      (primeAdjunctionMass_nonneg Q a))

/-- The coherent generator cost diverges, by the actual prime Mertens theorem. -/
theorem primePoleScale_tendsto_atTop : Tendsto primePoleScale atTop atTop := by
  have hlog : Tendsto (fun Q : ℕ => Real.log (Q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.mpr
  intro b
  have hl := (tendsto_atTop.mp hlog)
    (b + ((Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)))
  filter_upwards [hl, eventually_ge_atTop 1] with Q hlarge hQ
  have hb := (abs_le.mp (primePoleScale_logarithmic hQ)).1
  linarith only [hlarge, hb]

/-- Actual harmonic pole neutrality cannot produce a uniform generator sector constant. -/
theorem no_uniform_harmonic_neutral_generator_bound {N : ℕ} (hN : 1 ≤ N) :
    ¬∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → ∀ a : ℕ → ℝ,
      harmonicSum N (conductorHorizonProfile Q a) = 0 →
        packetMean Q (fun n => arithmeticPrimeGenerator Q a n ^ 2) ≤
          C * primeAdjunctionMass Q a := by
  rintro ⟨C, hC⟩
  have hlarge := (tendsto_atTop.mp primePoleScale_tendsto_atTop) (C + 1)
  obtain ⟨Q, hQ, hB⟩ := ((eventually_ge_atTop 2).and hlarge).exists
  have hc := primePoleScale_le_harmonic_neutral_sector_constant hQ hN C (hC Q hQ)
  linarith only [hB, hc]

/-- The same obstruction persists on the growing quadratic sampling horizon. -/
theorem no_uniform_quadratic_horizon_generator_bound :
    ¬∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → ∀ a : ℕ → ℝ,
      harmonicSum (Q * Q) (conductorHorizonProfile Q a) = 0 →
        packetMean Q (fun n => arithmeticPrimeGenerator Q a n ^ 2) ≤
          C * primeAdjunctionMass Q a := by
  rintro ⟨C, hC⟩
  have hlarge := (tendsto_atTop.mp primePoleScale_tendsto_atTop) (C + 1)
  obtain ⟨Q, hQ, hB⟩ := ((eventually_ge_atTop 2).and hlarge).exists
  have hN : 1 ≤ Q * Q := Nat.mul_pos (by omega : 0 < Q) (by omega : 0 < Q)
  have hc := primePoleScale_le_harmonic_neutral_sector_constant hQ hN C (hC Q hQ)
  linarith only [hB, hc]

#print axioms primeActivityMass_le_primePoleScale_add_eight
#print axioms arithmeticPrimeGenerator_period_sq_le_mertens_add
#print axioms primePoleScale_tendsto_atTop
#print axioms no_uniform_harmonic_neutral_generator_bound
#print axioms no_uniform_quadratic_horizon_generator_bound

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
