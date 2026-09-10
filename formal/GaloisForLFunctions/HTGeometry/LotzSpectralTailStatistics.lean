import GaloisForLFunctions.HTGeometry.LotzFiniteTailOrder
import GaloisForLFunctions.HTGeometry.FiniteNoiseMixingApplications

/-!
# Spectral tail statistics and exact preservation under mixing

The positive-tail representation used in Lotz, arXiv:2609.09335, Theorem 1.1
also organizes spectral majorization. All positive combinations of the corpus's
largest-coordinate sums, with arbitrary total-mass coefficient, recover exactly
the majorization order. They decrease under native bistochastic kernels and
unitary diagonal observations. Equality holds precisely on the active tails;
the exact deficit identifies the contribution of every tail.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators NNReal
open Matrix

/-- Positive combinations of spectral tails, with an arbitrary total-mass coefficient. -/
def lotzSpectralStatistic {n : ℕ} (a : ℝ) (c : Fin (n+1) → ℝ≥0) (x : Fin n → ℝ) : ℝ :=
  a * (∑ i, x i) + ∑ k, (c k : ℝ) * topSum k.val x

/-- These spectral tests recover exactly equal mass and every majorization inequality. -/
theorem lotzSpectralStatistic_order_iff {n : ℕ} (x y : Fin n → ℝ) :
    (∀ (a : ℝ) (c : Fin (n+1) → ℝ≥0),
      lotzSpectralStatistic a c x ≤ lotzSpectralStatistic a c y) ↔
      (∑ i, x i) = (∑ i, y i) ∧ ∀ k : Fin (n+1), topSum k.val x ≤ topSum k.val y := by
  constructor
  · intro h
    have hp := h 1 0
    have hn := h (-1) 0
    simp only [lotzSpectralStatistic, Pi.zero_apply, NNReal.coe_zero, zero_mul,
      Finset.sum_const_zero, add_zero, one_mul, neg_mul] at hp hn
    refine ⟨by linarith, ?_⟩
    intro k
    have hk := h 0 (Pi.single k 1)
    simpa [lotzSpectralStatistic, Pi.single_apply, apply_ite] using hk
  · rintro ⟨hm,hk⟩ a c
    unfold lotzSpectralStatistic
    rw [hm]
    exact add_le_add le_rfl (Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (hk k) (c k).property)

/-- Every bistochastic kernel decreases every statistic in the classified family. -/
theorem lotzSpectralStatistic_mixing_le {n : ℕ}
    (M : doublyStochastic ℝ (Fin n)) (x : Fin n → ℝ)
    (a : ℝ) (c : Fin (n+1) → ℝ≥0) :
    lotzSpectralStatistic a c (M.val *ᵥ x) ≤ lotzSpectralStatistic a c x :=
  (lotzSpectralStatistic_order_iff _ _).mpr
    ⟨sum_mulVec_of_mem_doublyStochastic M.property, bistochasticMixing_topSum_le M x⟩ a c

/-- Exact loss of a spectral statistic under mixing. -/
theorem lotzSpectralStatistic_mixing_defect {n : ℕ}
    (M : doublyStochastic ℝ (Fin n)) (x : Fin n → ℝ)
    (a : ℝ) (c : Fin (n+1) → ℝ≥0) :
    lotzSpectralStatistic a c x - lotzSpectralStatistic a c (M.val *ᵥ x) =
      ∑ k, (c k : ℝ) * (topSum k.val x-topSum k.val (M.val *ᵥ x)) := by
  simp only [lotzSpectralStatistic, sum_mulVec_of_mem_doublyStochastic M.property,
    mul_sub, Finset.sum_sub_distrib]
  ring

/-- A statistic is preserved exactly when each positively weighted spectral tail is preserved. -/
theorem lotzSpectralStatistic_mixing_eq_iff {n : ℕ}
    (M : doublyStochastic ℝ (Fin n)) (x : Fin n → ℝ)
    (a : ℝ) (c : Fin (n+1) → ℝ≥0) :
    lotzSpectralStatistic a c x = lotzSpectralStatistic a c (M.val *ᵥ x) ↔
      ∀ k, c k = 0 ∨ topSum k.val x = topSum k.val (M.val *ᵥ x) := by
  rw [← sub_eq_zero, lotzSpectralStatistic_mixing_defect,
    Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (f := fun k : Fin (n+1) =>
      (c k : ℝ) * (topSum k.val x-topSum k.val (M.val *ᵥ x))) (fun k _ => mul_nonneg (c k).property
      (sub_nonneg.mpr (bistochasticMixing_topSum_le M x k)))]
  simp only [Finset.mem_univ, forall_const, mul_eq_zero, NNReal.coe_eq_zero, sub_eq_zero]

/-- The entire spectral family applies to actual unitary diagonal observations. -/
theorem lotzSpectralStatistic_unitary_le {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (x : Fin n → ℝ)
    (a : ℝ) (c : Fin (n+1) → ℝ≥0) :
    lotzSpectralStatistic a c (finiteUnitaryDiagonalCoordinate x U) ≤ lotzSpectralStatistic a c x := by
  simpa only [finiteUnitaryMixing_mulVec] using lotzSpectralStatistic_mixing_le
    (finiteUnitaryMixing U) x a c

/-- Active-tail preservation classifies equality for the same unitary observations. -/
theorem lotzSpectralStatistic_unitary_eq_iff {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (x : Fin n → ℝ)
    (a : ℝ) (c : Fin (n+1) → ℝ≥0) :
    lotzSpectralStatistic a c x =
      lotzSpectralStatistic a c (finiteUnitaryDiagonalCoordinate x U) ↔
      ∀ k, c k = 0 ∨ topSum k.val x = topSum k.val (finiteUnitaryDiagonalCoordinate x U) := by
  simpa only [finiteUnitaryMixing_mulVec] using lotzSpectralStatistic_mixing_eq_iff
    (finiteUnitaryMixing U) x a c

/-- All tests decrease along arbitrary products of native probability-noise kernels. -/
theorem lotzSpectralStatistic_probability_evolution {n : ℕ}
    (p : FiniteProbabilityLaw (Fin n)) (M N : doublyStochastic ℝ (Fin n))
    (a : ℝ) (c : Fin (n+1) → ℝ≥0) :
    lotzSpectralStatistic a c (p.mix (N*M)).prob ≤ lotzSpectralStatistic a c (p.mix M).prob := by
  simpa only [FiniteProbabilityLaw.mix, Submonoid.coe_mul, Matrix.mulVec_mulVec] using
    lotzSpectralStatistic_mixing_le N (p.mix M).prob a c

end GaloisForLFunctions.HTGeometry
