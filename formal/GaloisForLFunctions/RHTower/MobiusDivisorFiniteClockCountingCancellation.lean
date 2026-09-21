import GaloisForLFunctions.RHTower.MobiusDivisorFixedCorePrimeCorrelation
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalClockProductTransport

/-!
# Exact finite counting cancellation with a logarithmic clock weight

The weight `c + log r` retains the cofactor clock in the complete arithmetic
counting measure. Prime insertion consumes `p log p` times the copied diagonal
and retains both signed factors of every mixed term. The identity is exact at
every cutoff, including the clipped last block.

The unshifted triangular age loses the fully processed head. An offset of one
recovers its original squared action and dominates the unweighted finite
energy for every processed core. No comparison to an asymptotic density and
no cumulative signed-correlation bound is asserted.
-/

noncomputable section
open Finset
namespace RHTower

/-- Complete finite source energy with an affine logarithmic cofactor clock. -/
def mobiusDivisorFiniteClockEnergy (c : ℝ) (M : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ r ∈ fixedCoreSquarefreeIndices P M,
    (c + Real.log r) * (r : ℝ) * (mobiusDivisorInterpolatedFibre M r P ∅)^2

private lemma sample_vanish (P : Finset ℕ) {M r : ℕ} (hr : 0<r) (hMr : M≤r) :
    mobiusDivisorInterpolatedFibre M r P ∅=0 := by
  have h0 : mobiusDivisorSelectionFibre 0 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]
  have h1 : mobiusDivisorSelectionFibre 1 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]
  rcases hMr.eq_or_lt with rfl | hlt
  · have hw : divisorPrimeClipWeight M M=0 := by simp [divisorPrimeClipWeight, Nat.div_self hr]
    simp [mobiusDivisorInterpolatedFibre, Nat.div_self hr, hw, h1]
  · simp [mobiusDivisorInterpolatedFibre, Nat.div_eq_of_lt hlt, h0, h1]

private lemma source_mem_insert {p r M : ℕ} (hp : p.Prime) (P : Finset ℕ) :
    r ∈ fixedCoreSquarefreeIndices (insert p P) M ↔
      r ∈ fixedCoreSquarefreeIndices P M ∧ ¬p∣r := by
  simp only [fixedCoreSquarefreeIndices, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hr,hs,hd⟩
    refine ⟨⟨hr,hs,hd.mono_right (subset_insert _ _)⟩,?_⟩
    intro hpr
    exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp,hpr,by omega⟩) (mem_insert_self _ _)
  · rintro ⟨⟨hr,hs,hd⟩,hpr⟩
    refine ⟨hr,hs,disjoint_left.mpr ?_⟩
    intro q hqr hqP
    rcases mem_insert.mp hqP with rfl | hqP
    · exact hpr (Nat.mem_primeFactors.mp hqr).2.1
    · exact disjoint_left.mp hd hqr hqP

private lemma source_mul {p r : ℕ} (hp : p.Prime) (P : Finset ℕ)
    (hpP : p∉P) (hr : 0<r) :
    Squarefree (p*r) ∧ Disjoint (p*r).primeFactors P ↔
      Squarefree r ∧ Disjoint r.primeFactors (insert p P) := by
  rw [Nat.squarefree_mul_iff, Nat.primeFactors_mul hp.ne_zero hr.ne', hp.primeFactors]
  constructor
  · rintro ⟨⟨hc,_,hs⟩,hd⟩
    refine ⟨hs,disjoint_left.mpr ?_⟩
    intro q hqr hqP
    rcases mem_insert.mp hqP with rfl | hqP
    · exact (hp.coprime_iff_not_dvd.mp hc) (Nat.mem_primeFactors.mp hqr).2.1
    · exact disjoint_left.mp hd (mem_union_right _ hqr) hqP
  · rintro ⟨hs,hd⟩
    refine ⟨⟨hp.coprime_iff_not_dvd.mpr ?_,hp.squarefree,hs⟩, disjoint_left.mpr ?_⟩
    · intro hpr
      exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp,hpr,hr.ne'⟩) (mem_insert_self _ _)
    · intro q hq hqP
      rcases mem_union.mp hq with hq | hq
      · exact hpP ((mem_singleton.mp hq) ▸ hqP)
      · exact disjoint_left.mp hd hq (mem_insert_of_mem hqP)

private lemma source_split {p : ℕ} (hp : p.Prime) (P : Finset ℕ)
    (hpP : p∉P) (M : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ fixedCoreSquarefreeIndices P M, f r) =
      (∑ r ∈ fixedCoreSquarefreeIndices (insert p P) M, f r)+
      ∑ r ∈ fixedCoreSquarefreeIndices (insert p P) (M/p), f (p*r) := by
  let S := fixedCoreSquarefreeIndices P M
  have hfree : S.filter (fun r => ¬p∣r) = fixedCoreSquarefreeIndices (insert p P) M := by
    ext r
    exact mem_filter.trans (source_mem_insert hp P).symm
  have hdiv : (∑ r ∈ fixedCoreSquarefreeIndices (insert p P) (M/p), f (p*r)) =
      ∑ r ∈ S.filter (fun r => p∣r), f r := by
    apply sum_nbij' (fun r => p*r) (fun r => r/p)
    · intro r hr
      obtain ⟨hr,hs⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith [hp.pos], ?_⟩,
        (source_mul hp P hpP hr'.1).mpr hs⟩,dvd_mul_right _ _⟩
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hr'.2
    · intro r hr
      obtain ⟨hr,hpr⟩ := mem_filter.mp hr
      obtain ⟨hr,hs,hd⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      have he : p*(r/p)=r := Nat.mul_div_cancel' hpr
      have hq : 0<r/p := by nlinarith
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨hq,Nat.div_le_div_right hr'.2⟩,?_⟩
      apply (source_mul hp P hpP hq).mp
      rw [he]
      exact ⟨hs,hd⟩
    · intro r _
      exact Nat.mul_div_cancel_left r hp.pos
    · intro r hr
      exact Nat.mul_div_cancel' (mem_filter.mp hr).2
    · intro r _
      rfl
  rw [hdiv, ← hfree]
  exact (sum_filter_not_add_sum_filter S (fun r => p∣r) f).symm

/-- Exact sampling of the original critical head in logarithmic time.
The cofactor weight is the triangular age, with the indicated affine offset;
the measure is the literal finite arithmetic counting measure. -/
theorem mobiusDivisorFiniteClockEnergy_eq_clock_samples
    (P : Finset Nat.Primes) (M : ℕ) (c : ℝ) :
    let Q := P.image (fun p : Nat.Primes => (p : ℕ))
    mobiusDivisorFiniteClockEnergy c (M+1) Q / (M+1 : ℕ)^2 =
      ∑ r ∈ fixedCoreSquarefreeIndices Q (M+1),
        ((c + Real.log (M+1 : ℕ) - Real.log ((M+1 : ℕ)/ (r : ℝ))) / r) *
          (mobiusDivisorCriticalClockHead Q (Real.log ((M+1 : ℕ)/(r : ℝ))))^2 := by
  dsimp only
  let Q := P.image (fun p : Nat.Primes => (p : ℕ))
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := mem_image.mp hp
    exact q.property
  rw [mobiusDivisorFiniteClockEnergy, sum_div]
  apply sum_congr rfl
  intro r hr
  have hr0 : (0 : ℝ) < r := by
    exact_mod_cast (mem_Icc.mp (mem_filter.mp hr).1).1
  have hM0 : (0 : ℝ) < (M+1 : ℕ) := by positivity
  rw [mobiusDivisorCriticalClockHead, Real.exp_log (div_pos hM0 hr0),
    mobiusDivisorContinuousHead_div Q hQ _ r (by exact_mod_cast hr0),
    Real.log_div hM0.ne' hr0.ne']
  field_simp
  ring

private lemma weighted_insert (c : ℝ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpP : p ∉ P) (M : ℕ) :
    mobiusDivisorFiniteClockEnergy c M (insert p P) -
        mobiusDivisorFiniteClockEnergy c M P +
      2 * Real.sqrt p * ∑ r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        (c + Real.log r) * (r : ℝ) * mobiusDivisorInterpolatedFibre M r P ∅ *
          mobiusDivisorInterpolatedFibre M (p*r) P ∅ =
      -(p : ℝ) * Real.log p * ∑ r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        (r : ℝ) * (mobiusDivisorInterpolatedFibre M (p*r) P ∅)^2 := by
  unfold mobiusDivisorFiniteClockEnergy
  rw [source_split hp P hpP M]
  have he : (∑ r ∈ fixedCoreSquarefreeIndices (insert p P) (M/p),
      (c + Real.log (p*r : ℕ)) * ((p*r : ℕ) : ℝ) *
        (mobiusDivisorInterpolatedFibre M (p*r) P ∅)^2) =
      ∑ r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        (c + Real.log (p*r : ℕ)) * ((p*r : ℕ) : ℝ) *
          (mobiusDivisorInterpolatedFibre M (p*r) P ∅)^2 := by
    apply sum_subset
    · intro r hr
      obtain ⟨hr, hs⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      exact mem_filter.mpr ⟨mem_Icc.mpr
        ⟨hr'.1, hr'.2.trans (Nat.div_le_self M p)⟩, hs⟩
    · intro r hr hnot
      obtain ⟨hr, hs⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      have hsmall : ¬r ≤ M/p := fun h =>
        hnot (mem_filter.mpr ⟨mem_Icc.mpr ⟨hr'.1,h⟩,hs⟩)
      have hb : M ≤ p*r := by
        have hn : ¬r*p ≤ M := fun h => hsmall ((Nat.le_div_iff_mul_le hp.pos).mpr h)
        nlinarith
      rw [sample_vanish P (by nlinarith [hp.pos] : 0 < p*r) hb]
      ring
  rw [he, ← sum_add_distrib, ← sum_sub_distrib, mul_sum, mul_sum,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  obtain ⟨hr, hs, hd⟩ := mem_filter.mp hr
  have hr0 : 0 < r := (mem_Icc.mp hr).1
  rw [mobiusDivisorInterpolatedHead_insert_prime P hp hpP hr0 hs hd M]
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
    (by exact_mod_cast hr0.ne')]
  have hsq := Real.sq_sqrt (Nat.cast_nonneg p)
  linear_combination
    ((c + Real.log r) * (r : ℝ) *
      (mobiusDivisorInterpolatedFibre M (p*r) P ∅)^2) * hsq

/-- The exact finite counting measure pays a positive logarithmic copied
square. Both signed source factors and the full cutoff remain in the mixed
term; no density limit or correlation hypothesis is used. -/
theorem mobiusDivisorFiniteClockEnergy_source_cancellation :
    ∀ (P : Finset Nat.Primes) (p : Nat.Primes) (M : ℕ) (c : ℝ),
      let Q := (P.erase p).image (fun q : Nat.Primes => (q : ℕ))
      mobiusDivisorFiniteClockEnergy c M (insert (p : ℕ) Q) -
          mobiusDivisorFiniteClockEnergy c M Q +
        2 * Real.sqrt (p : ℕ) *
          ∑ r ∈ fixedCoreSquarefreeIndices (insert (p : ℕ) Q) M,
            (c + Real.log r) * (r : ℝ) * mobiusDivisorInterpolatedFibre M r Q ∅ *
              mobiusDivisorInterpolatedFibre M ((p : ℕ)*r) Q ∅ =
        -(p : ℝ) * Real.log (p : ℝ) *
          ∑ r ∈ fixedCoreSquarefreeIndices (insert (p : ℕ) Q) M,
            (r : ℝ) * (mobiusDivisorInterpolatedFibre M ((p : ℕ)*r) Q ∅)^2 := by
  intro P p M c
  apply weighted_insert c _ p.property
  intro hp
  obtain ⟨q, hq, he⟩ := mem_image.mp hp
  have hqp : q = p := Subtype.ext he
  exact (mem_erase.mp hq).1 hqp

/-- Every copied diagonal payment has the dissipative sign, uniformly in
prime, processed core, cutoff, and affine clock offset. -/
theorem mobiusDivisorFiniteClockEnergy_source_cancellation_nonpos :
    ∀ (P : Finset Nat.Primes) (p : Nat.Primes) (M : ℕ) (c : ℝ),
      let Q := (P.erase p).image (fun q : Nat.Primes => (q : ℕ))
      mobiusDivisorFiniteClockEnergy c M (insert (p : ℕ) Q) -
          mobiusDivisorFiniteClockEnergy c M Q +
        2 * Real.sqrt (p : ℕ) *
          ∑ r ∈ fixedCoreSquarefreeIndices (insert (p : ℕ) Q) M,
            (c + Real.log r) * (r : ℝ) * mobiusDivisorInterpolatedFibre M r Q ∅ *
              mobiusDivisorInterpolatedFibre M ((p : ℕ)*r) Q ∅ ≤ 0 := by
  intro P p M c
  dsimp only
  rw [mobiusDivisorFiniteClockEnergy_source_cancellation P p M c]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
  have hl := Real.log_nonneg hp1
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (le_trans zero_le_one hp1)) hl
  · exact sum_nonneg (fun r _ => mul_nonneg (Nat.cast_nonneg r) (sq_nonneg _))

/-- The offset clock dominates the complete finite arithmetic energy with
constant one for every core and cutoff. This comparison uses actual counts. -/
theorem mobiusDivisorSelectionEnergy_le_finiteClock (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorSelectionEnergy M P ≤ mobiusDivisorFiniteClockEnergy 1 M P := by
  rw [mobiusDivisorSelectionEnergy_eq_inclusive_squarefree, mobiusDivisorFiniteClockEnergy]
  apply sum_le_sum
  intro r hr
  have hr1 : (1 : ℝ) ≤ r := by
    exact_mod_cast (mem_Icc.mp (mem_filter.mp hr).1).1
  have hl := Real.log_nonneg hr1
  have h := mul_nonneg hl
    (mul_nonneg (Nat.cast_nonneg r) (sq_nonneg (mobiusDivisorInterpolatedFibre M r P ∅)))
  nlinarith only [h]

private lemma square_as_fibre (P : Finset ℕ) (M : ℕ) {r : ℕ}
    (hr : Squarefree r) (hd : Disjoint r.primeFactors P) :
    (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 =
      (mobiusDivisorSelectionFibre M P r.primeFactors)^2 := by
  have h := mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hd
  rw [Nat.prod_primeFactors_of_squarefree hr] at h
  have hm : (((ArithmeticFunction.moebius r : ℤ) : ℝ))^2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr
  rw [h, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg r), hm, mul_one]

/-- Exact classification of affine clock offsets at complete processing.
The unshifted triangular clock is blind to the head; offset one retains its
entire square with no loss depending on the cutoff. -/
theorem mobiusDivisorFiniteClockEnergy_complete (c : ℝ) (M : ℕ) :
    mobiusDivisorFiniteClockEnergy c M (mobiusDivisorSelectionPrimes M) =
      c * mobiusDivisorSelectionEnergy M (mobiusDivisorSelectionPrimes M) := by
  rw [mobiusDivisorFiniteClockEnergy, mobiusDivisorSelectionEnergy_eq_inclusive_squarefree,
    mul_sum]
  apply sum_congr rfl
  intro r hr
  obtain ⟨hr, hs, hd⟩ := mem_filter.mp hr
  have hr0 : 0 < r := (mem_Icc.mp hr).1
  rw [mul_assoc, square_as_fibre _ M hs hd]
  by_cases he : r.primeFactors = ∅
  · have hr1 : r = 1 := by
      have h := Nat.primeFactors_eq_empty.mp he
      omega
    simp [hr1]
  · rw [mobiusDivisorSelectionFibre_of_all_source_primes_processed M
      (mobiusDivisorSelectionPrimes M) r.primeFactors (by rfl), if_neg he]
    simp

/-- The literal finite triangular clock assigns zero to every completely
processed source, so this weighting alone cannot recover the critical head. -/
theorem mobiusDivisorFiniteClockEnergy_triangular_complete (M : ℕ) :
    mobiusDivisorFiniteClockEnergy 0 M (mobiusDivisorSelectionPrimes M) = 0 := by
  rw [mobiusDivisorFiniteClockEnergy_complete, zero_mul]

/-- At every positive integer wall the offset finite-count clock is exactly
the original critical action squared, with its original normalization. -/
theorem mobiusDivisorFiniteClockEnergy_complete_critical_wall (M : ℕ) :
    mobiusDivisorFiniteClockEnergy 1 (M+1) (mobiusDivisorSelectionPrimes (M+1)) /
        (M+1 : ℕ)^2 =
      (mobiusDivisorCriticalClockHead (mobiusDivisorSelectionPrimes (M+1))
        (Real.log (M+1 : ℕ)))^2 := by
  rw [mobiusDivisorFiniteClockEnergy_complete, one_mul,
    mobiusDivisorSelectionEnergy_full, mobiusDivisorCriticalClockHead_complete_integer_wall,
    div_pow, mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels]
  simp only [Nat.add_sub_cancel]
  rw [sum_Icc_succ_top (show 1 ≤ M+1 by omega)]
  have hz : mobiusDivisorDilationChannel (M+1) (M+1) = 0 := by
    simp [mobiusDivisorDilationChannel]
  rw [hz, add_zero]

end RHTower
