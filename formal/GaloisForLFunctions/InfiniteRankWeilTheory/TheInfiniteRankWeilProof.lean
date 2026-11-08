import GaloisForLFunctions.InfiniteRankWeilTheory.TheCrudeStepAndTheCount

/-!
# The infinite-rank Weil proof

The curve proof has three steps: a crude count at every level, a self-improvement, and the
functional equation. This file states the proof at finite and at infinite rank in the same shape.

**Finite rank** (`curveDatum_tfae`). For a curve datum the following are equivalent: every normalized
eigenvalue is on the unit circle; the traces are bounded at every level; the traces are bounded on
one thick set of levels; the point counts are within `C q^{n/2}` of `qⁿ + 1` on one thick set of levels.
The crude count on a thick set of levels is the whole proof.

**Infinite rank** (`riemannHypothesis_tfae`). For `ζ` the following are equivalent: RH; ZAL and AAL;
ZAL and a bounded lag on a thick set of levels of one tower; ZAL and a positive count of one tower;
ZAL and a positive count of every tower; ZAL and a crude count `O(X^{½})` of the prime deviation along
a thick set of geometric scales. Each step of the curve proof has its infinite-rank form: the crude
count is the thick-set bound of one tower, the self-improvement is the window theorem for its isolated
top, the functional equation is the reflection of the tower; and over `ℤ` the crude count needs the
exceptional-coordinate input ZAL, which a curve gets from finite rank.

**The finite stratum** (`finiteOffLine_tfae`). If only finitely many zeros are off the line, the
following are equivalent: RH; some tower has a positive count; every tower has a positive count; some
tower has a bounded lag on a thick set of levels.
-/

open Complex
open RHTower (XiZeroCopy weilLagFunction)

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

open ArithmeticCastelnuovoSeveri in
/-- **The curve proof as one equivalence.** -/
theorem curveDatum_tfae {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    [∀ i, ‖D.β i‖ = 1,
      ∃ C : ℝ, ∀ n : ℕ, |D.trace n| ≤ C,
      ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ, ∀ n ∈ G, |D.trace n| ≤ C,
      ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ, ∀ n ∈ G,
        |D.pointCount n - (D.q ^ n + 1)| ≤ C * D.sqrtq ^ n].TFAE := by
  tfae_have 1 → 2 := by
    intro hu
    refine ⟨Fintype.card ι, fun n => ?_⟩
    have h : ‖D.powerSum n‖ ≤ Fintype.card ι := by
      unfold CurveDatum.powerSum
      calc ‖∑ i, D.β i ^ n‖ ≤ ∑ i, ‖D.β i ^ n‖ := norm_sum_le _ _
        _ = ∑ _i : ι, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by rw [norm_pow, hu, one_pow]
        _ = Fintype.card ι := by simp
    rwa [D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs] at h
  tfae_have 2 → 3 := fun ⟨C, hC⟩ => ⟨Set.univ, thick_univ, C, fun n _ => hC n⟩
  tfae_have 3 → 1 := fun ⟨G, hG, C, hC⟩ => D.unitary_of_thick_trace_bound hG hC
  tfae_have 3 → 4 := by
    rintro ⟨G, hG, C, hC⟩
    refine ⟨G, hG, C, fun n hn => ?_⟩
    have hpos : 0 < D.sqrtq ^ n := pow_pos D.sqrtq_pos n
    rw [show D.pointCount n - (D.q ^ n + 1) = -(D.sqrtq ^ n * D.trace n) by
      simp only [CurveDatum.pointCount]; ring, abs_neg, abs_mul, abs_of_pos hpos, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC n hn) hpos.le
  tfae_have 4 → 1 := fun ⟨G, hG, C, hC⟩ => D.unitary_of_thick_pointCount_bound hG hC
  tfae_finish

/-- **The infinite-rank Weil proof for `ζ` as one equivalence.** -/
theorem riemannHypothesis_tfae :
    [RiemannHypothesis,
      RHTower.BacklundConverse.ZerosApproachLine ∧ RHTower.AsymptoticAbscissaLaw,
      RHTower.BacklundConverse.ZerosApproachLine ∧ ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ G : Set ℕ, Thick G ∧
        ∃ C : ℝ, ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C,
      RHTower.BacklundConverse.ZerosApproachLine ∧ ∃ ℓ : ℝ, 0 < ℓ ∧ ToeplitzPositive (lagKernel ℓ),
      RHTower.BacklundConverse.ZerosApproachLine ∧ ∀ ℓ : ℝ, ToeplitzPositive (lagKernel ℓ),
      RHTower.BacklundConverse.ZerosApproachLine ∧ ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ G : Set ℕ, Thick G ∧
        ∃ C : ℝ, ∀ ν ∈ G, 1 ≤ ν →
          ‖primeDeviation (Real.exp (ν * ℓ))‖ ≤ C * Real.exp ((ν * ℓ) / 2)].TFAE := by
  tfae_have 1 ↔ 2 := RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_zerosApproachLine_and_toeplitzPositive_lagKernel
  tfae_have 1 → 5 := fun hRH =>
    ⟨(RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.1 hRH).1,
      fun ℓ => toeplitzPositive_lagKernel_of_riemannHypothesis hRH ℓ⟩
  tfae_have 5 → 4 := fun ⟨hZ, h⟩ => ⟨hZ, 1, one_pos, h 1⟩
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_zerosApproachLine_and_thick_primeDeviation
  tfae_finish

/-- **The finite stratum as one equivalence.** With finitely many off-line zeros, RH is a positive
count of some tower, of every tower, or a bounded lag on a thick set of levels of some tower. -/
theorem finiteOffLine_tfae (hF : FiniteOffLine) :
    [RiemannHypothesis,
      ∃ ℓ : ℝ, 0 < ℓ ∧ ToeplitzPositive (lagKernel ℓ),
      ∀ ℓ : ℝ, ToeplitzPositive (lagKernel ℓ),
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ,
        ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C].TFAE := by
  have hZ := zerosApproachLine_of_finiteOffLine hF
  tfae_have 1 → 3 := fun hRH ℓ => toeplitzPositive_lagKernel_of_riemannHypothesis hRH ℓ
  tfae_have 3 → 2 := fun h => ⟨1, one_pos, h 1⟩
  tfae_have 2 → 1 := fun h =>
    riemannHypothesis_iff_zerosApproachLine_and_toeplitzPositive_lagKernel.2 ⟨hZ, h⟩
  tfae_have 1 → 4 := fun hRH =>
    (riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded.1 hRH).2
  tfae_have 4 → 1 := fun h =>
    riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded.2 ⟨hZ, h⟩
  tfae_finish

end GaloisForLFunctions.InfiniteRankWeilTheory
