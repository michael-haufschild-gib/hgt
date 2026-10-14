import GaloisForLFunctions.HTGeometry.FinitePhasePacket
import GaloisForLFunctions.HTGeometry.FiniteInfinitesimalProduct
import GaloisForLFunctions.RHTower.PaperPrimeRotationCompressionDeterminants

/-! # The coherent prime clock: arithmetic coefficients and energy limit

All primes share the same observation interval. The limiting packet keeps
the signed complex first-order phase coefficient of each native commutator.
-/

namespace RHTower
open GaloisForLFunctions.HTGeometry Filter Topology
noncomputable section

def paperPrimeCoherentCoefficient (a : Nat.Primes → ℂ) (q : ℕ) (p : Nat.Primes) : ℂ :=
  a p * ((((q : ℝ) + 1 : ℝ) : ℂ) *
    (paperRotationPhase (paperPrimeRotationFrequency p (q + 1)) - 1))

def paperPrimeCoherentLimitCoefficient (a : Nat.Primes → ℂ) (p : Nat.Primes) : ℂ :=
  a p * ((-Real.log p : ℝ) : ℂ) * Complex.I

def paperPrimeCoherentBound (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) : ℝ :=
  ∑ p ∈ s, ‖a p‖ * Real.log p

def paperPrimeCoherentEnergy (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) : ℝ :=
  finitePhaseEnergy s (paperPrimeCoherentLimitCoefficient a) (fun p => -Real.log p)

def paperPrimeCoherentGramProduct (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) (q : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (q + 1),
    (1 + ‖finitePhasePacket s (paperPrimeCoherentCoefficient a q) (fun p => -Real.log p)
      ((j : ℝ) / ((q : ℝ) + 1))‖ ^ 2 / ((q : ℝ) + 1))

theorem paperPrimeCoherentBound_nonneg (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    0 ≤ paperPrimeCoherentBound s a :=
  Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) p.2.log_pos.le

theorem paperPrimeCoherentCoefficient_norm_le (a : Nat.Primes → ℂ) (q : ℕ) (p : Nat.Primes) :
    ‖paperPrimeCoherentCoefficient a q p‖ ≤ ‖a p‖ * Real.log p := by
  rw [paperPrimeCoherentCoefficient, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (show 0 < (q : ℝ) + 1 by positivity),
    paperPrimeRotationFrequency_eq, Nat.cast_add, Nat.cast_one]
  have h := paperRotationPhase_scaled_norm_le (-Real.log p) q
  rw [abs_neg, abs_of_pos p.2.log_pos] at h
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

theorem paperPrimeCoherentLimitCoefficient_norm (a : Nat.Primes → ℂ) (p : Nat.Primes) :
    ‖paperPrimeCoherentLimitCoefficient a p‖ = ‖a p‖ * Real.log p := by
  rw [paperPrimeCoherentLimitCoefficient, norm_mul, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos p.2.log_pos]

theorem paperPrimeCoherentCoefficient_tendsto (a : Nat.Primes → ℂ) (p : Nat.Primes) :
    Tendsto (fun q => paperPrimeCoherentCoefficient a q p) atTop
      (𝓝 (paperPrimeCoherentLimitCoefficient a p)) := by
  simpa only [paperPrimeCoherentCoefficient, paperPrimeCoherentLimitCoefficient,
    paperPrimeRotationFrequency_eq, Nat.cast_add, Nat.cast_one, mul_assoc] using
    (paperRotationPhase_scaled_tendsto (-Real.log p)).const_mul (a p)

theorem paperPrimeCoherentSampleEnergy_tendsto (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    Tendsto (fun q => finitePhaseSampleEnergy s (paperPrimeCoherentCoefficient a q)
      (fun p => -Real.log p) q) atTop (𝓝 (paperPrimeCoherentEnergy s a)) := by
  apply finitePhaseSampleEnergy_coeff_tendsto s _ _ _ (paperPrimeCoherentBound_nonneg s a)
  · intro q
    exact Finset.sum_le_sum fun p _ => paperPrimeCoherentCoefficient_norm_le a q p
  · simp only [paperPrimeCoherentLimitCoefficient_norm, paperPrimeCoherentBound, le_refl]
  · exact fun p _ => paperPrimeCoherentCoefficient_tendsto a p

theorem paperPrimeCoherentGramProduct_tendsto (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    Tendsto (paperPrimeCoherentGramProduct s a) atTop (𝓝 (Real.exp (paperPrimeCoherentEnergy s a))) := by
  have hB := paperPrimeCoherentBound_nonneg s a
  have hn : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  apply tendsto_prod_one_add (fun q => Finset.range (q + 1)) _
    (fun q => paperPrimeCoherentBound s a ^ 2 / ((q : ℝ) + 1))
  · intro q j _; positivity
  · intro q j _
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hnorm : ‖finitePhasePacket s (paperPrimeCoherentCoefficient a q)
        (fun p => -Real.log p) ((j : ℝ) / ((q : ℝ) + 1))‖ ≤ paperPrimeCoherentBound s a :=
      (finitePhasePacket_norm_le s (paperPrimeCoherentCoefficient a q)
      (fun p => -Real.log p) ((j : ℝ) / ((q : ℝ) + 1))).trans
        (Finset.sum_le_sum fun p _ => paperPrimeCoherentCoefficient_norm_le a q p)
    have hpos := norm_nonneg (finitePhasePacket s (paperPrimeCoherentCoefficient a q)
      (fun p => -Real.log p) ((j : ℝ) / ((q : ℝ) + 1)))
    dsimp only [paperPrimeCoherentBound] at hB hnorm ⊢
    nlinarith
  · exact tendsto_const_nhds.div_atTop hn
  · simpa only [finitePhaseSampleEnergy, Finset.mul_sum, one_div, div_eq_mul_inv,
      mul_comm, one_mul] using paperPrimeCoherentSampleEnergy_tendsto s a

end
end RHTower
