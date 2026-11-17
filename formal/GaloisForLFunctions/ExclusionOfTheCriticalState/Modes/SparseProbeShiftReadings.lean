import GaloisForLFunctions.ExclusionOfTheCriticalState.TheProbeSamplesHaveNoFiniteRecurrence
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheGammaPairingInLevyForm
import GaloisForLFunctions.HTGeometry.SpectralHardyTraceFormation
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Sparse hyperplane hits of the shift orbit of a probe sequence

The return-set question in Yang, Proposition 2.1.1 (arXiv:2302.00948),
has a quantitative answer for a different dynamical system: the shift of
the arithmetic Laplace samples. Every nontrivial finite linear test of a
nonzero profile has a zero set of finite harmonic mass. In particular a
recurrence cannot hold even on all prime indices.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Polynomial Function
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry
  SignedWindowCriticality CanonicalSystemOfTheWindowTower

/-- A hyperplane on finitely many consecutive coordinates of the shifted probe sequence. -/
def probeShiftReading (P : ℝ[X]) (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ P.support, P.coeff j * criticalProbeSample F (n + j)

private def probeShiftTransform (P : ℝ[X]) (F : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ P.support, (P.coeff j : ℂ) * negativeHalfLineLaplace (cx F) (z + (4 + j))

private theorem sample_shiftTransform (P : ℝ[X]) (F : ℝ → ℝ) (n : ℕ) :
    probeShiftTransform P F (((n : ℝ) + 1 : ℝ) : ℂ) = (probeShiftReading P F n : ℂ) := by
  unfold probeShiftTransform probeShiftReading
  rw [ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : (((n : ℝ) + 1 : ℝ) : ℂ) + (4 + j) = ((5 + ((n+j : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, negativeHalfLineLaplace_ofReal, ofReal_mul]
  rfl

/-- Harmonic-divergent sampling detects every nonzero polynomial test of a nonzero profile. -/
theorem ae_zero_of_probeShiftReading_sparse {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {P : ℝ[X]} (hP : P ≠ 0) {ι : Type*} (a : ι ↪ ℕ)
    (ha : ¬ Summable fun i => (1 : ℝ) / ((a i : ℝ) + 1))
    (hz : ∀ i, probeShiftReading P F (a i) = 0) : F =ᵐ[volume] 0 := by
  let L := probeShiftTransform P F
  let rate := fun i => (a i : ℝ) + 1
  have hd : DifferentiableOn ℂ L {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.fun_sum
    intro j _
    apply DifferentiableOn.const_mul
    apply (differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential).comp
      (differentiableOn_id.add_const _)
    intro z (hz : 0 < z.re)
    change -(8 / 2 : ℝ) < (z + (4 + j : ℂ)).re
    simp only [add_re, natCast_re, re_ofNat]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hb (z : ℂ) (hz : 0 < z.re) : ‖L z‖ ≤ ∑ j ∈ P.support, ‖P.coeff j‖ * halfPoleMass F := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, norm_real]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply norm_laplace_le_halfPoleMass hF
    simp only [add_re, re_ofNat, natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hi : Injective rate := by
    intro i j h
    apply a.injective
    exact_mod_cast (add_right_cancel h : (a i : ℝ) = a j)
  have ht : Tendsto rate cofinite atTop := by
    have ht' := a.injective.tendsto_cofinite
    rw [Nat.cofinite_eq_atTop] at ht'
    exact tendsto_atTop_mono (fun i => by dsimp [rate]; linarith)
      (tendsto_natCast_atTop_atTop.comp ht')
  have hr (i : ι) : 1 ≤ rate i := by dsimp [rate]; positivity
  have hdv : ¬ Summable fun i => rate i / (1 + rate i ^ 2) := by
    intro hs
    apply ha
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hs.mul_left 2)
    change 1 / rate i ≤ 2 * (rate i / (1 + rate i ^ 2))
    rw [mul_div_assoc', div_le_div_iff₀ (lt_of_lt_of_le zero_lt_one (hr i)) (by positivity)]
    nlinarith only [hr i, sq_nonneg (rate i - 1)]
  have hzero := eqOn_zero_of_bounded_of_blaschke_divergent (δ := 0) le_rfl hd hb hi ht
    (fun i => zero_lt_one.trans_le (hr i)) (fun i => (sample_shiftTransform P F (a i)).trans
      (by rw [hz, ofReal_zero])) hdv
  apply ae_eq_zero_of_criticalProbeSample_recurrence hF hP 0
  intro n
  have h := hzero (((n : ℝ) + 1 : ℝ) : ℂ) (by simp; positivity)
  change probeShiftTransform P F _ = 0 at h
  rw [sample_shiftTransform, ofReal_eq_zero] at h
  simpa only [Nat.zero_add] using h

/-- The full set of hyperplane hit times of a nonzero profile has summable reciprocal weights. -/
theorem probeShiftReading_hit_summable {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hn : ¬ F =ᵐ[volume] 0) {P : ℝ[X]} (hP : P ≠ 0) :
    Summable fun i : {n : ℕ // probeShiftReading P F n = 0} => (1 : ℝ) / ((i.val : ℝ) + 1) := by
  by_contra h
  exact hn (ae_zero_of_probeShiftReading_sparse hF hP (Function.Embedding.subtype _) h
    fun i => i.property)

private theorem prime_shift_diverges :
    ¬ Summable fun i : Nat.Primes => (1 : ℝ) / ((i.val : ℝ) + 1) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun i => ?_) (h.mul_left 2)
  have hi : (1 : ℝ) ≤ i.val := by exact_mod_cast i.property.one_le
  change 1 / (i.val : ℝ) ≤ 2 * (1 / ((i.val : ℝ) + 1))
  rw [mul_div_assoc', div_le_div_iff₀ (lt_of_lt_of_le zero_lt_one hi) (by positivity)]
  linarith

/-- The shift orbit at prime times spans every finite coordinate projection of a nonzero profile. -/
theorem prime_probeShiftReading_detects {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hn : ¬ F =ᵐ[volume] 0) {P : ℝ[X]} (hP : P ≠ 0) :
    ∃ q : Nat.Primes, probeShiftReading P F q ≠ 0 := by
  by_contra! h
  exact hn (ae_zero_of_probeShiftReading_sparse hF hP (Function.Embedding.subtype _)
    prime_shift_diverges h)

#print axioms ae_zero_of_probeShiftReading_sparse
#print axioms probeShiftReading_hit_summable
#print axioms prime_probeShiftReading_detects

end GaloisForLFunctions.ExclusionOfTheCriticalState
