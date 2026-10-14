import GaloisForLFunctions.RHTower.PaperPrimeRotationCoherentPacket
import GaloisForLFunctions.HTGeometry.FiniteBilateralWeightedShiftLinear

/-! # Literal coherent compressions of native prime commutators -/

namespace RHTower
open GaloisForLFunctions.HTGeometry HilbertSchmidt _root_.ContinuousLinearMap Filter Topology
noncomputable section

def paperPrimeCoherentOperator (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) (q : ℕ) :
    PaperRotationHilbert →L[ℂ] PaperRotationHilbert :=
  (Real.sqrt ((q : ℝ) + 1) : ℂ) •
    ∑ p ∈ s, a p • paperPrimeRotationCompression p (q + 1) (q + 1)

def paperPrimeCoherentEdgeWeight (s : Finset Nat.Primes) (a : Nat.Primes → ℂ)
    (q : ℕ) (j : ℤ) : ℂ :=
  (Real.sqrt ((q : ℝ) + 1) : ℂ) *
    ∑ p ∈ s, a p * paperPrimeRotationEdgeWeight p (q + 1) j

theorem paperPrimeCoherentOperator_eq_weightedShift (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) :
    paperPrimeCoherentOperator s a q =
      finiteBilateralWeightedShift (q + 1) (paperPrimeCoherentEdgeWeight s a q) := by
  simp only [paperPrimeCoherentOperator, paperPrimeRotationCompression_eq_weightedShift,
    finiteBilateralWeightedShift_smul, finiteBilateralWeightedShift_sum]
  rfl

theorem paperPrimeCoherentOperator_eq_compression (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) :
    paperPrimeCoherentOperator s a q = (Real.sqrt ((q : ℝ) + 1) : ℂ) •
      (coordTruncation (bilateralShiftWindow (q + 1)) ∘L
        (∑ p ∈ s, a p • paperPrimeRotationCommutator p (q + 1) 0 1 1 0) ∘L
        coordTruncation (bilateralShiftWindow (q + 1))) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [paperPrimeCoherentOperator, paperPrimeRotationCompression, smul_apply,
    FunLike.coe_sum, Finset.sum_apply, comp_apply, map_sum, map_smul]

theorem paperPrimeCoherentOperator_traceClass (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) : MemSchattenClass 1 (paperPrimeCoherentOperator s a q) := by
  rw [paperPrimeCoherentOperator_eq_weightedShift]
  exact finiteBilateralWeightedShift_traceClass _ _

theorem paperPrimeCoherentOperator_compact (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) : IsCompactOperator (paperPrimeCoherentOperator s a q) :=
  (paperPrimeCoherentOperator_traceClass s a q).isCompactOperator one_pos

theorem paperPrimeCoherentOperator_traceCost_zero (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) :
    compactOperatorTraceCost PaperRotationHilbert (paperPrimeCoherentOperator s a q) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr
    (paperPrimeCoherentOperator_compact s a q)

theorem paperPrimeCoherentOperator_opTrace (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) : opTrace (paperPrimeCoherentOperator s a q) = 0 := by
  rw [paperPrimeCoherentOperator_eq_weightedShift, opTrace_finiteBilateralWeightedShift]

theorem paperPrimeCoherentOperator_smul_fredholmDet (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) (z : ℂ) :
    fredholmDetOp (lpBasis ℤ) (z • paperPrimeCoherentOperator s a q) = 1 := by
  rw [paperPrimeCoherentOperator_eq_weightedShift, finiteBilateralWeightedShift_smul]
  exact fredholmDetOp_finiteBilateralWeightedShift _ _

theorem paperPrimeCoherentPacket_eq_scaled_edges (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) (j : ℤ) :
    finitePhasePacket s (paperPrimeCoherentCoefficient a q) (fun p => -Real.log p)
        ((j : ℝ) / ((q : ℝ) + 1)) =
      (((q : ℝ) + 1 : ℝ) : ℂ) *
        ∑ p ∈ s, a p * paperPrimeRotationEdgeWeight p (q + 1) j := by
  rw [finitePhasePacket, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [paperPrimeCoherentCoefficient, paperPrimeRotationEdgeWeight,
    paperPrimeRotationFrequency_eq, Nat.cast_add, Nat.cast_one]
  rw [show -Real.log p / ((q : ℝ) + 1) * j = -Real.log p * ((j : ℝ) / ((q : ℝ) + 1)) by ring]
  ring

theorem paperPrimeCoherentEdgeWeight_norm_sq (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) (j : ℤ) :
    ‖paperPrimeCoherentEdgeWeight s a q j‖ ^ 2 =
      ‖finitePhasePacket s (paperPrimeCoherentCoefficient a q) (fun p => -Real.log p)
        ((j : ℝ) / ((q : ℝ) + 1))‖ ^ 2 / ((q : ℝ) + 1) := by
  have hq : 0 < (q : ℝ) + 1 := by positivity
  rw [paperPrimeCoherentEdgeWeight, paperPrimeCoherentPacket_eq_scaled_edges,
    norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hq,
    mul_pow, mul_pow, Real.sq_sqrt hq.le]
  field_simp

theorem paperPrimeCoherentOperator_gram_fredholmDet (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) :
    fredholmDetOp (lpBasis ℤ)
      ((paperPrimeCoherentOperator s a q).adjoint ∘L paperPrimeCoherentOperator s a q) =
        (paperPrimeCoherentGramProduct s a q : ℂ) := by
  rw [paperPrimeCoherentOperator_eq_weightedShift, fredholmDetOp_finiteBilateralWeightedShift_gram,
    prod_bilateralShiftEdges]
  simp only [paperPrimeCoherentEdgeWeight_norm_sq, Int.cast_natCast,
    paperPrimeCoherentGramProduct, Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_one]

theorem paperPrimeCoherentOperator_gram_tendsto (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) :
    Tendsto (fun q => fredholmDetOp (lpBasis ℤ)
      ((paperPrimeCoherentOperator s a q).adjoint ∘L paperPrimeCoherentOperator s a q))
      atTop (𝓝 (Real.exp (paperPrimeCoherentEnergy s a) : ℂ)) := by
  simpa only [Function.comp_def, paperPrimeCoherentOperator_gram_fredholmDet] using
    (Complex.continuous_ofReal.tendsto _).comp (paperPrimeCoherentGramProduct_tendsto s a)

end
end RHTower
