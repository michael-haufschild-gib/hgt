import GaloisForLFunctions.HTGeometry.DiagonalModeDivision
import GaloisForLFunctions.RHTower.StieltjesLogWeldTierOne

/-!
# Stieltjes–secular prime-log collision universality

A rationally shifted collision between a friable Stieltjes weight-one datum and a secular
combination-mode frequency occurs exactly when every prime lane agrees and the rational shift
vanishes.  Nontrivial secular frequencies, and the logarithms of their diagonal weights, are
therefore irrational.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open SecularWeld

noncomputable section

/-- **Stieltjes–secular prime-log collision universality law.**  Equality up to a rational offset
is equivalent to exact global equality of all prime lanes and zero offset. -/
theorem friableC1_eq_modeFrequency_add_rat_iff
    (A : Finset ℕ) (lam : ℕ → ℚ) (h0 : ∀ n ∈ A, n ≠ 0)
    (m : PrimeExponents) (q : ℚ) :
    friableC1 A lam = modeFrequency m + (q : ℝ) ↔
      q = 0 ∧ ∀ p : Nat.Primes, friableBeta A lam p = (m p : ℚ) := by
  let S : Finset Nat.Primes := friablePrimes A ∪ m.support
  have hbeta :
      friableC1 A lam =
        ∑ p ∈ S, (friableBeta A lam p : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    apply friableC1_eq_sum_beta_log A lam h0
    intro n hn p hp
    exact Finset.mem_union_left _ (mem_friablePrimes hn hp)
  have hmode :
      modeFrequency m =
        ∑ p ∈ S, (m p : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    rw [modeFrequency, Finsupp.sum]
    apply Finset.sum_subset Finset.subset_union_right
    intro p _ hpSupport
    have hmp : m p = 0 := Finsupp.notMem_support_iff.mp hpSupport
    rw [hmp]
    simp
  constructor
  · intro h
    have hrel :
        ∑ p ∈ S,
            ((friableBeta A lam p - (m p : ℚ) : ℚ) : ℝ) *
              Real.log ((p : ℕ) : ℝ) = (q : ℝ) := by
      calc
        ∑ p ∈ S,
              ((friableBeta A lam p - (m p : ℚ) : ℚ) : ℝ) *
                Real.log ((p : ℕ) : ℝ) =
            (∑ p ∈ S,
                (friableBeta A lam p : ℝ) * Real.log ((p : ℕ) : ℝ)) -
              ∑ p ∈ S, (m p : ℝ) * Real.log ((p : ℕ) : ℝ) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro p _
                push_cast
                ring
        _ = friableC1 A lam - modeFrequency m := by rw [hbeta, hmode]
        _ = (q : ℝ) := by rw [h]; ring
    obtain ⟨hq, hcoeff⟩ :=
      logPrime_rat_affine_relation_eq_zero S
        (fun p => friableBeta A lam p - (m p : ℚ)) q hrel
    refine ⟨hq, fun p => ?_⟩
    by_cases hp : p ∈ S
    · exact sub_eq_zero.mp (hcoeff p hp)
    · have hpBeta : p ∉ friablePrimes A := by
        intro hmem
        exact hp (Finset.mem_union_left _ hmem)
      have hpSupport : p ∉ m.support := by
        intro hmem
        exact hp (Finset.mem_union_right _ hmem)
      rw [friableBeta_eq_zero_of_not_mem hpBeta,
        Finsupp.notMem_support_iff.mp hpSupport]
      norm_num
  · rintro ⟨hq, hcoeff⟩
    rw [hbeta, hmode, hq, Rat.cast_zero, add_zero]
    apply Finset.sum_congr rfl
    intro p _
    rw [hcoeff p]
    norm_num

/-- Every nontrivial secular combination-mode frequency is irrational. -/
theorem modeFrequency_irrational_of_ne_zero
    {m : PrimeExponents} (hm : m ≠ 0) :
    Irrational (modeFrequency m) := by
  rintro ⟨q, hq⟩
  have hcollision :=
    (friableC1_eq_modeFrequency_add_rat_iff
      (∅ : Finset ℕ) (fun _ => 0) (by simp) m (-q)).mp
      (by simp [friableC1, ← hq])
  apply hm
  ext p
  have hp := hcollision.2 p
  simpa [friableBeta] using hp.symm

/-- The logarithm of every nontrivial secular diagonal weight is irrational. -/
theorem log_diagonalWeightReal_irrational_of_ne_zero
    {m : PrimeExponents} (hm : m ≠ 0) :
    Irrational (Real.log (diagonalWeightReal m)) := by
  rw [log_diagonalWeightReal]
  exact (modeFrequency_irrational_of_ne_zero hm).neg

end

end GaloisForLFunctions
