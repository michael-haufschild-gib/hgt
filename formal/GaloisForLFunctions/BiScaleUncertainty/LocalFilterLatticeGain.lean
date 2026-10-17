import GaloisForLFunctions.BiScaleUncertainty.LocalCoherentFilter

/-!
# Quantitative lattice gain from the finite hyperbolic filter

The actual finite filter has coefficient square sum at most `13/9`. Its signed
Gram energy therefore improves the earlier lattice price `2` before applying
the same source projection. The resulting explicit gain transfers to the full
odd plastic functional, including zero source energy.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.LocalFilterLatticeGain
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicMultiplierFrame DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter
noncomputable section

private def coefficient (k : ℕ) : ℝ :=
  1 / (2 * Real.cosh ((((k : ℝ) + 1) * Real.log 2) / 2))

/-- Coefficient energy of the finite symmetric hyperbolic filter. -/
def coefficientEnergy (L : ℕ) : ℝ := 2 * ∑ k ∈ Finset.range L, coefficient k ^ 2

private theorem coefficient_sq_le (k : ℕ) : coefficient k ^ 2 ≤ 1 / (2 : ℝ) ^ (k + 1) := by
  let t : ℝ := (((k : ℝ) + 1) * Real.log 2) / 2
  have h : Real.exp t ≤ 2 * Real.cosh t := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-t)]
  have he : Real.exp t ^ 2 = (2 : ℝ) ^ (k + 1) := by
    rw [sq, ← Real.exp_add, show t + t = ((k + 1 : ℕ) : ℝ) * Real.log 2 by
      dsimp [t]; push_cast; ring, Real.exp_nat_mul,
      Real.exp_log (by norm_num : 0 < (2 : ℝ))]
  have hsq : (2 : ℝ) ^ (k + 1) ≤ (2 * Real.cosh t) ^ 2 := by
    rw [← he]
    nlinarith [Real.exp_pos t, Real.cosh_pos t]
  change (1 / (2 * Real.cosh t)) ^ 2 ≤ _
  rw [div_pow, one_pow]
  exact one_div_le_one_div_of_le (by positivity) hsq

private theorem coefficient_zero_sq : coefficient 0 ^ 2 = 2 / 9 := by
  have h₁ := Real.cosh_two_mul (x := Real.log 2 / 2)
  have h₂ := Real.cosh_sq_sub_sinh_sq (Real.log 2 / 2)
  rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring,
    Real.cosh_log (by norm_num : 0 < (2 : ℝ))] at h₁
  have he : (2 * Real.cosh (Real.log 2 / 2)) ^ 2 = 9 / 2 := by
    norm_num at h₁
    nlinarith only [h₁, h₂]
  simp only [coefficient, Nat.cast_zero, zero_add, one_mul, div_pow, one_pow]
  rw [he]
  norm_num

private theorem geometric_tail (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (2 : ℝ) ^ (k + 2)) + 1 / (2 : ℝ) ^ (n + 1) = 1 / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hh : 1 / (2 : ℝ) ^ (n + 2) + 1 / (2 : ℝ) ^ (n + 2) =
        1 / (2 : ℝ) ^ (n + 1) := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      field_simp
      ring
    rw [Finset.sum_range_succ, show n + 1 + 1 = n + 2 by omega, add_assoc, hh]
    exact ih

/-- Exact first coefficient improves the geometric coefficient bound uniformly. -/
theorem coefficientEnergy_le (L : ℕ) : coefficientEnergy L ≤ 13 / 9 := by
  cases L with
  | zero => norm_num [coefficientEnergy]
  | succ n =>
    have ht : (∑ k ∈ Finset.range n, coefficient (k + 1) ^ 2) ≤ 1 / 2 := by
      have hs := Finset.sum_le_sum (s := Finset.range n)
        (fun k _ => coefficient_sq_le (k + 1))
      have hg := geometric_tail n
      have hp : 0 ≤ 1 / (2 : ℝ) ^ (n + 1) := by positivity
      linarith only [hs, hg, hp]
    unfold coefficientEnergy
    rw [Finset.sum_range_succ', coefficient_zero_sq]
    linarith only [ht]

private theorem lattice_quad_le {ι : Type*} [DecidableEq ι]
    (f : C_c(ℝ, ℝ)) (s : Finset ι) (z : ι → ℤ) (hz : Function.Injective z) (w : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * sourceSample f (z j - z i)) ≤
      correlationMass f * ∑ i ∈ s, w i ^ 2 := by
  have hs : Summable (fun k : ℤ => |sourceSample f k|) := by
    apply summable_of_hasFiniteSupport
    apply (sourceSample_finite f).subset
    intro k hk
    change |sourceSample f k| ≠ 0 at hk
    change sourceSample f k ≠ 0
    exact fun he => hk (by rw [he, abs_zero])
  have hrow (i : ι) : (∑ j ∈ s, |sourceSample f (z j - z i)|) ≤ correlationMass f := by
    have hinj : ∀ a ∈ s, ∀ b ∈ s, z a - z i = z b - z i → a = b := by
      intro a _ b _ hab
      apply hz
      omega
    rw [← Finset.sum_image (f := fun k : ℤ => |sourceSample f k|) hinj]
    exact hs.sum_le_tsum _ (fun _ _ => abs_nonneg _)
  have hpt (i j : ι) : 2 * (w i * w j * sourceSample f (z j - z i)) ≤
      (w i ^ 2 + w j ^ 2) * |sourceSample f (z j - z i)| := by
    have ha := le_abs_self (w i * w j * sourceSample f (z j - z i))
    rw [abs_mul, abs_mul] at ha
    have hb : 2 * (|w i| * |w j|) ≤ w i ^ 2 + w j ^ 2 := by
      nlinarith only [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
    have hc := mul_le_mul_of_nonneg_right hb (abs_nonneg (sourceSample f (z j - z i)))
    linarith only [ha, hc]
  have hsum : 2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * sourceSample f (z j - z i)) ≤
      ∑ i ∈ s, ∑ j ∈ s, (w i ^ 2 + w j ^ 2) * |sourceSample f (z j - z i)| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hpt i j
  have hswap : (∑ i ∈ s, ∑ j ∈ s, w j ^ 2 * |sourceSample f (z j - z i)|) =
      ∑ i ∈ s, ∑ j ∈ s, w i ^ 2 * |sourceSample f (z j - z i)| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show z i - z j = -(z j - z i) by ring, sourceSample_neg]
  have hsplit : (∑ i ∈ s, ∑ j ∈ s, (w i ^ 2 + w j ^ 2) * |sourceSample f (z j - z i)|) =
      2 * ∑ i ∈ s, w i ^ 2 * ∑ j ∈ s, |sourceSample f (z j - z i)| := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [hswap, ← two_mul]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
  have hrows : (∑ i ∈ s, w i ^ 2 * ∑ j ∈ s, |sourceSample f (z j - z i)|) ≤
      correlationMass f * ∑ i ∈ s, w i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (w i))
  rw [hsplit] at hsum
  linarith only [hsum, hrows]

private def position : ℕ ⊕ ℕ → ℤ := Sum.elim (fun k => (k : ℤ) + 1) (fun k => -((k : ℤ) + 1))
private def weight : ℕ ⊕ ℕ → ℝ := Sum.elim coefficient coefficient
private def nodes (L : ℕ) : Finset (ℕ ⊕ ℕ) := (Finset.range L).disjSum (Finset.range L)

private theorem position_injective : Function.Injective position := by
  intro i j hij
  cases i <;> cases j <;> simp only [position, Sum.elim_inl, Sum.elim_inr] at hij
  all_goals first | congr 1; omega | omega

/-- The actual finite filter is controlled by its coefficient energy, with signed correlations retained. -/
theorem sourceFilter_energy_le (f : C_c(ℝ, ℝ)) :
    autocorr (sourceFilter f) 0 ≤ correlationMass f * coefficientEnergy (sourceCutoff f) := by
  have h := lattice_quad_le f (nodes (sourceCutoff f)) position position_injective weight
  have he : autocorr (sourceFilter f) 0 =
      ∑ i ∈ nodes (sourceCutoff f), ∑ j ∈ nodes (sourceCutoff f),
        weight i * weight j * sourceSample f (position j - position i) := by
    rw [← integral_sq_eq_autocorr_zero]
    have hf (u : ℝ) : sourceFilter f u =
        ∑ i ∈ nodes (sourceCutoff f), weight i * f (u + (position i : ℝ) * Real.log 2) := by
      rw [sourceFilter_apply]
      simp only [nodes, Finset.sum_disjSum, weight, position, Sum.elim_inl, Sum.elim_inr,
        Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by rw [sub_eq_add_neg]; unfold coefficient; ring
    simp_rw [hf]
    rw [← translationGramEnergy_eq_integral]
    unfold translationGramEnergy sourceSample
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Int.cast_sub, sub_mul]
  have hw : (∑ i ∈ nodes (sourceCutoff f), weight i ^ 2) = coefficientEnergy (sourceCutoff f) := by
    simp only [nodes, weight, Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr, coefficientEnergy]
    ring
  rwa [← he, hw] at h

/-- Uniform improvement from `2` to `13/9` for the explicit source filter. -/
theorem sourceFilter_energy_le_thirteen_ninths (f : C_c(ℝ, ℝ)) :
    autocorr (sourceFilter f) 0 ≤ (13 / 9) * correlationMass f := by
  have h := mul_le_mul_of_nonneg_left (coefficientEnergy_le (sourceCutoff f)) (correlationMass_nonneg f)
  have he := sourceFilter_energy_le f
  nlinarith only [he, h]

/-- The source projection preserves the quantitative coefficient improvement. -/
theorem filterEnergy_gap (f : C_c(ℝ, ℝ)) :
    (5 / 9) * correlationMass f ≤ projectedEnergy f - filterEnergy f := by
  have h := sourceFilter_energy_le_thirteen_ninths f
  unfold projectedEnergy filterEnergy
  rw [filterCovariance_eq_covarianceMass]
  linarith only [h]

theorem filterEnergy_le_projectedEnergy (f : C_c(ℝ, ℝ)) : filterEnergy f ≤ projectedEnergy f := by
  have h := filterEnergy_gap f
  have hΓ := correlationMass_nonneg f
  linarith only [h, hΓ]

theorem localBudget_le_projectedBudget (f : C_c(ℝ, ℝ)) : localBudget f ≤ projectedBudget f := by
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (filterEnergy_le_projectedEnergy f)
    (autocorr_zero_nonneg (centeredSource f (1 / 2) (sourceMean f (1 / 2)))))
  unfold localBudget projectedBudget
  linarith only [h]

/-- Rationalized denominator for the finite-filter improvement. -/
def gainDenominator (f : C_c(ℝ, ℝ)) : ℝ :=
  Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * projectedEnergy f) +
    Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * filterEnergy f)

/-- Guaranteed finite-filter gain, totalized at a vanishing denominator. -/
def latticeGain (f : C_c(ℝ, ℝ)) : ℝ :=
  ((5 / 9) * autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * correlationMass f) /
    gainDenominator f

theorem budget_gap_product (f : C_c(ℝ, ℝ)) :
    (projectedBudget f - localBudget f) * gainDenominator f =
      autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 *
        (projectedEnergy f - filterEnergy f) := by
  let Q := autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0
  have hQ : 0 ≤ Q := autocorr_zero_nonneg _
  have hD := Real.sq_sqrt (mul_nonneg hQ (projectedEnergy_nonneg f))
  have hH := Real.sq_sqrt (mul_nonneg hQ (filterEnergy_nonneg f))
  unfold projectedBudget localBudget gainDenominator
  change (_ + Real.sqrt (Q * projectedEnergy f) - (_ + Real.sqrt (Q * filterEnergy f))) *
    (Real.sqrt (Q * projectedEnergy f) + Real.sqrt (Q * filterEnergy f)) = _
  calc
    _ = Real.sqrt (Q * projectedEnergy f) ^ 2 - Real.sqrt (Q * filterEnergy f) ^ 2 := by ring
    _ = Q * (projectedEnergy f - filterEnergy f) := by rw [hD, hH]; ring

theorem budget_gap_product_ge (f : C_c(ℝ, ℝ)) :
    (5 / 9) * autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * correlationMass f ≤
      (projectedBudget f - localBudget f) * gainDenominator f := by
  rw [budget_gap_product]
  have h := mul_le_mul_of_nonneg_left (filterEnergy_gap f)
    (autocorr_zero_nonneg (centeredSource f (1 / 2) (sourceMean f (1 / 2))))
  nlinarith only [h]

theorem latticeGain_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ latticeGain f := by
  unfold latticeGain gainDenominator
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (autocorr_zero_nonneg _))
    (correlationMass_nonneg f)) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The quantitative gain is valid even when both root terms vanish. -/
theorem latticeGain_le_budget_gap (f : C_c(ℝ, ℝ)) :
    latticeGain f ≤ projectedBudget f - localBudget f := by
  have hd : 0 ≤ gainDenominator f := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  by_cases hz : gainDenominator f = 0
  · simp only [latticeGain, hz, div_zero]
    exact sub_nonneg.mpr (localBudget_le_projectedBudget f)
  · exact (div_le_iff₀ (lt_of_le_of_ne hd (Ne.symm hz))).mpr (budget_gap_product_ge f)

/-- Explicit producer gain in the full plastic bound for arbitrary signed odd source data. -/
theorem odd_plasticCrossover_ge_latticeGain (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) - 2 * Real.log 2 * projectedBudget (oddCompactSource f) +
        2 * Real.log 2 * latticeGain (oddCompactSource f) ≤ plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_localBudget f N
  have hd := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hg := mul_le_mul_of_nonneg_left (latticeGain_le_budget_gap (oddCompactSource f)) hd
  nlinarith only [hp, hg]

end
end GaloisForLFunctions.BiScaleUncertainty.LocalFilterLatticeGain
