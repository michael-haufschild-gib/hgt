import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.CountLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.VacuumCalibration.Isometry

/-! # Resolving each count and detecting isometry from the octave law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower
open scoped NNReal

private def tent (k : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ℝ => 1-min 1 |x-k|)
    (by fun_prop) 1 (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
      exact sub_le_self _ (le_min zero_le_one (abs_nonneg _)))

private theorem tent_nat (k n : ℕ) : tent k (n:ℝ) = if n=k then 1 else 0 := by
  change 1-min 1 |(n:ℝ)-k| = _
  rcases lt_trichotomy n k with hn | rfl | hn
  · have hh : (n:ℝ)+1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hn
    rw [if_neg hn.ne,abs_of_nonpos (by linarith only [hh]),min_eq_left (by linarith only [hh]),sub_self]
  · simp
  · have hh : (k:ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
    rw [if_neg hn.ne',abs_of_nonneg (by linarith only [hh]),min_eq_left (by linarith only [hh]),sub_self]

/-- Finite probability of measuring exactly k occupied prime modes. -/
def atom (S : Finset Nat.Primes) (s : ℝ) (k : ℕ) :=
  ∑ x : SquarefreeBitConfig S, if (squarefreeOccupationFinset x).card=k then finiteSquarefreeBornWeight S s x else 0

private theorem finite_tent (c d : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) (k : ℕ) :
    (∫ x, tent k x ∂(countLaw c d h s : Measure ℝ)) = atom (added c d h) s k := by
  change (∫ x, tent k x ∂Measure.sum (fun y : SquarefreeBitConfig (added c d h) =>
    ENNReal.ofReal (finiteSquarefreeBornWeight _ s y) • Measure.dirac ((squarefreeOccupationFinset y).card:ℝ))) = _
  rw [integral_sum_dirac (by simp),tsum_fintype,atom]
  apply Finset.sum_congr rfl
  intro y _
  rw [tent_nat,ENNReal.toReal_ofReal (weight_pos _ _ y).le,smul_eq_mul]
  split <;> simp

private theorem poisson_tent (r : ℝ≥0) (k : ℕ) :
    (∫ x, tent k x ∂(poissonCount r : Measure ℝ)) = Real.exp (-(r:ℝ))*(r:ℝ)^k/k.factorial := by
  change (∫ x, tent k x ∂(poissonMeasure r).map (Nat.cast : ℕ → ℝ)) = _
  rw [integral_map Measurable.of_discrete.aemeasurable (tent k).continuous.aestronglyMeasurable,integral_poissonMeasure,
    tsum_eq_single k]
  · simp [tent_nat,smul_eq_mul]
  · intro n hn
    simp [tent_nat,hn]

/-- The zero atom identifies the rate of an integer-valued Poisson count. -/
theorem poissonCount_injective : Function.Injective poissonCount := by
  intro r t he
  have h := congrArg (fun μ : ProbabilityMeasure ℝ => ∫ x, tent 0 x ∂(μ : Measure ℝ)) he
  simp only [poisson_tent,pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one] at h
  have hn := congrArg Real.log h
  rw [Real.log_exp,Real.log_exp] at hn
  exact NNReal.eq (neg_inj.mp hn)

private theorem transfer_atoms {c d : ℝ} {s : Ioi (0:ℝ) → ℝ} {r : ℝ≥0}
    (H : Tendsto (fun h => countLaw c d h (s h)) criticalApproach (𝓝 (poissonCount r))) (k : ℕ) :
    Tendsto (fun h => atom (added c d h) (s h) k) criticalApproach
      (𝓝 (Real.exp (-(r:ℝ))*(r:ℝ)^k/k.factorial)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp H (tent k)
  simpa only [finite_tent,poisson_tent] using h

/-- Individual count probabilities converge, including the lattice atoms of the limiting law. -/
theorem atom_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) (k : ℕ) :
    Tendsto (fun h => atom (added c d h) (1+a*h.val) k) criticalApproach
      (𝓝 (Real.exp (-VacuumCalibration.mass c d a)*(VacuumCalibration.mass c d a)^k/k.factorial)) :=
  transfer_atoms (count_weak_limit hc hcd a) k

private theorem zero_atom (c d : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) :
    atom (added c d h) s 0 = VacuumCalibration.vacuum c d h s := by
  let S := added c d h
  have h0 : squarefreeOccupationFinset (0 : SquarefreeBitConfig S) = ∅ := by
    ext p
    simp [mem_squarefreeOccupationFinset]
  have he (x : SquarefreeBitConfig S) : (squarefreeOccupationFinset x).card = 0 ↔ x = 0 := by
    rw [Finset.card_eq_zero,← h0]
    exact (squarefreeOccupationEquiv S).injective.eq_iff
  change (∑ x : SquarefreeBitConfig S, if (squarefreeOccupationFinset x).card=0 then _ else _) = _
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,if_true,VacuumCalibration.vacuum]

/-- The full Poisson octave law characterizes norm-preserving cyclic-order composition. -/
theorem split_isometric_iff_poisson_count {c : ℝ} (hc : 0 < c) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      Tendsto (fun h => countLaw c (2*c) h (2*s.re)) criticalApproach
        (𝓝 (poissonCount ⟨Real.log 2,(Real.log_pos one_lt_two).le⟩)) := by
  constructor
  · intro H
    rw [show 2*s.re = 1 by rw [(split_isometric_iff s).mp H]; ring]
    exact doubled_count_limit hc
  · intro H
    apply (VacuumCalibration.split_isometric_iff_half_vacuum hc s).mpr
    have h := transfer_atoms H 0
    change Tendsto _ criticalApproach (𝓝 (Real.exp (-Real.log 2)*(Real.log 2)^0/(Nat.factorial 0:ℝ))) at h
    simpa only [zero_atom,pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one,Real.exp_neg,
      Real.exp_log (by norm_num : (0:ℝ) < 2),one_div] using h

#print axioms poissonCount_injective
#print axioms atom_limit
#print axioms split_isometric_iff_poisson_count

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks
