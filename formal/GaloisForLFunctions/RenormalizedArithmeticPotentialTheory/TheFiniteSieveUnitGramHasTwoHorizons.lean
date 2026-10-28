import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveClassesHaveExactPrimeGrams
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasTheMertensConstant
import GaloisForLFunctions.HTGeometry.HarmonicBoundaryLayer

/-!
# The finite-sieve unit Gram at two horizons

The exact row contains a sieved Mertens sum and a divisor logarithm. Their
logarithms cancel, leaving a constant row plus a controlled quotient boundary.
This gives the same Euler finite part uniformly for two unequal cutoffs.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-- The rectangular pole Gram on the units of a finite sieve. -/
def sieveUnitGram (Q : Finset Nat.Primes) (A B : ℕ) : ℝ :=
  ∑ k ∈ sieveUnits Q A, ∑ l ∈ sieveUnits Q B,
    poleVector k * poleVector l * weilPrimeKernel k l

theorem sieveUnitGram_comm (Q : Finset Nat.Primes) (A B : ℕ) :
    sieveUnitGram Q A B = sieveUnitGram Q B A := by
  unfold sieveUnitGram
  rw [sum_comm]
  exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by
    rw [weilPrimeKernel_comm]
    ring

theorem sievedHarmonic_nonneg (Q : Finset Nat.Primes) (A : ℕ) :
    0 ≤ sievedHarmonic Q A := sum_nonneg fun k _ => by positivity

theorem sievedHarmonic_le_harmonicSum (Q : Finset Nat.Primes) (A : ℕ) :
    sievedHarmonic Q A ≤ harmonicSum A := by
  unfold sievedHarmonic harmonicSum
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => by positivity

/-- Multiples of a sieve unit are indexed by their unit quotient. -/
theorem sieveUnits_filter_multiples {Q : Finset Nat.Primes} {k : ℕ}
    (hk : 0 < k) (hkunit : Nat.Coprime k (sievePrimorial Q)) (B : ℕ) :
    (sieveUnits Q B).filter (fun l => k ∣ l) =
      (sieveUnits Q (B / k)).image (fun l => k * l) := by
  ext l
  constructor
  · intro hl
    obtain ⟨hlunit, hdiv⟩ := mem_filter.mp hl
    obtain ⟨hrange, hcop⟩ := mem_filter.mp hlunit
    obtain ⟨r, rfl⟩ := hdiv
    have hr : 0 < r := by
      by_contra h
      have hz : r = 0 := by omega
      simp [hz] at hrange
    refine mem_image.mpr ⟨r, mem_filter.mpr ⟨mem_Icc.mpr ⟨hr, ?_⟩,
      (Nat.coprime_mul_iff_left.mp hcop).2⟩, rfl⟩
    exact (Nat.le_div_iff_mul_le hk).mpr (by simpa only [Nat.mul_comm] using (mem_Icc.mp hrange).2)
  · intro hl
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hl
    obtain ⟨hrange, hcop⟩ := mem_filter.mp hr
    obtain ⟨hr0, hrB⟩ := mem_Icc.mp hrange
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hk hr0, ?_⟩,
      Nat.coprime_mul_iff_left.mpr ⟨hkunit, hcop⟩⟩, dvd_mul_right k r⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).mp hrB

/-- The exact rectangular row is a sieved Mertens sum plus the divisor logarithm. -/
theorem sieveUnitGram_eq (Q : Finset Nat.Primes) {A B : ℕ} (hAB : A ≤ B) :
    sieveUnitGram Q A B =
      ∑ k ∈ sieveUnits Q A, (sievedMertensSum Q (B / k) + Real.log k) / (k : ℝ) := by
  unfold sieveUnitGram
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := (mem_Icc.mp (mem_filter.mp hk).1).1
  have hkunit := (mem_filter.mp hk).2
  have hkB : k ∈ sieveUnits Q B := mem_filter.mpr
    ⟨mem_Icc.mpr ⟨hk0, (mem_Icc.mp (mem_filter.mp hk).1).2.trans hAB⟩, hkunit⟩
  have hterms : (∑ l ∈ sieveUnits Q B,
      poleVector k * poleVector l * weilPrimeKernel k l) =
      ∑ l ∈ sieveUnits Q B,
        ((if k ∣ l then ArithmeticFunction.vonMangoldt (l / k) / l else 0) +
          (if l ∣ k then ArithmeticFunction.vonMangoldt (k / l) / k else 0)) := by
    exact sum_congr rfl fun l hl =>
      poleWeighted_primeKernel_eq hk0 (mem_Icc.mp (mem_filter.mp hl).1).1
  rw [hterms, sum_add_distrib]
  have hup : (∑ l ∈ sieveUnits Q B,
      if k ∣ l then ArithmeticFunction.vonMangoldt (l / k) / l else 0) =
        sievedMertensSum Q (B / k) / k := by
    rw [← sum_filter, sieveUnits_filter_multiples hk0 hkunit,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hk0 h,
      sievedMertensSum, sum_div]
    refine sum_congr rfl fun l _ => ?_
    rw [Nat.mul_div_cancel_left l hk0, Nat.cast_mul]
    ring
  have hdown : (∑ l ∈ sieveUnits Q B,
      if l ∣ k then ArithmeticFunction.vonMangoldt (k / l) / k else 0) =
        Real.log k / (k : ℝ) := by
    rw [← sum_filter, sieveUnits_filter_dvd hkB, ← sum_div,
      Nat.sum_div_divisors k ArithmeticFunction.vonMangoldt, ArithmeticFunction.vonMangoldt_sum]
  rw [hup, hdown]
  ring

/-- The total logarithmic roundoff at a quotient boundary is uniformly bounded. -/
theorem sieve_log_roundoff_sum_le (Q : Finset Nat.Primes) {A B : ℕ}
    (hA : 0 < A) (hAB : A ≤ B) :
    |∑ k ∈ sieveUnits Q A,
      (Real.log B - Real.log ((B / k : ℕ) : ℝ) - Real.log k) / (k : ℝ)| ≤ 2 := by
  have hB : (0 : ℝ) < B := by exact_mod_cast hA.trans_le hAB
  have hterm : ∀ k ∈ sieveUnits Q A,
      |(Real.log B - Real.log ((B / k : ℕ) : ℝ) - Real.log k) / (k : ℝ)| ≤ 2 / (B : ℝ) := by
    intro k hk
    obtain ⟨hk0, hkA⟩ := mem_Icc.mp (mem_filter.mp hk).1
    have hkB := hkA.trans hAB
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hq : 1 ≤ B / k := (Nat.le_div_iff_mul_le hk0).mpr (by simpa using hkB)
    have hqR : (1 : ℝ) ≤ ((B / k : ℕ) : ℝ) := by exact_mod_cast hq
    obtain ⟨hr0, hr1⟩ := roundoff_le hk0 hkB
    rw [abs_of_nonneg (div_nonneg hr0 hkR.le)]
    have hcast := RHTower.Mertens.cast_div_lt B k hk0
    rw [div_lt_iff₀ hkR] at hcast
    have hBq : (B : ℝ) ≤ 2 * ((B / k : ℕ) : ℝ) * k := by
      exact hcast.le.trans (mul_le_mul_of_nonneg_right (by linarith only [hqR]) hkR.le)
    calc
      (Real.log B - Real.log ((B / k : ℕ) : ℝ) - Real.log k) / (k : ℝ) ≤
        (1 / ((B / k : ℕ) : ℝ)) / k := div_le_div_of_nonneg_right hr1 hkR.le
      _ = 1 / (((B / k : ℕ) : ℝ) * k) := by ring
      _ ≤ 2 / (B : ℝ) := by
        rw [div_le_div_iff₀ (mul_pos (by linarith only [hqR]) hkR) hB]
        simpa only [one_mul, mul_assoc] using hBq
  have hcard : ((sieveUnits Q A).card : ℝ) ≤ (B : ℝ) := by
    have hnat : (sieveUnits Q A).card ≤ B :=
      (card_le_card (filter_subset _ _)).trans
        (by simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hAB)
    exact_mod_cast hnat
  calc
    |∑ k ∈ sieveUnits Q A,
      (Real.log B - Real.log ((B / k : ℕ) : ℝ) - Real.log k) / (k : ℝ)| ≤
      ∑ k ∈ sieveUnits Q A,
        |(Real.log B - Real.log ((B / k : ℕ) : ℝ) - Real.log k) / (k : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ sieveUnits Q A, 2 / (B : ℝ) := sum_le_sum hterm
    _ = ((sieveUnits Q A).card : ℝ) * (2 / (B : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ) * (2 / (B : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 := by field_simp

/-- The Euler finite part is uniform over both unit horizons. -/
theorem exists_sieveUnitGram_finitePart_bound (Q : Finset Nat.Primes)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B : ℕ, A ≤ B →
      |sieveUnitGram Q A B - sievedHarmonic Q A * sievedHarmonic Q B / sieveDensity Q +
        2 * sieveEuler Q * sievedHarmonic Q A| ≤ η * sievedHarmonic Q A + C := by
  let e : ℕ → ℝ := fun n => sievedMertensSum Q n - Real.log n + sieveEuler Q
  let h : ℕ → ℝ := fun n => sievedHarmonic Q n / sieveDensity Q - Real.log n - sieveEuler Q
  have hδ : sieveDensity Q ≠ 0 := (sieveDensity_pos Q).ne'
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [neg_add_cancel] using (tendsto_sievedMertensSum_sub_log Q).add_const (sieveEuler Q)
  have hh : Tendsto h atTop (𝓝 0) := by
    have ht := ((tendsto_sievedHarmonic_sub_sieveEuler Q).div_const (sieveDensity Q)).sub_const
      (sieveEuler Q)
    simp only [mul_div_cancel_left₀ _ hδ, sub_self] at ht
    refine ht.congr fun n => ?_
    dsimp only [h]
    field_simp
  obtain ⟨Ce, hCe, heBound⟩ := exists_harmonicBoundaryLayer_bound he (half_pos hη)
  obtain ⟨K, hKrange⟩ := hh.abs.bddAbove_range
  have hK : ∀ n, |h n| ≤ K := fun n => hKrange ⟨n, rfl⟩
  have hK0 : 0 ≤ K := (abs_nonneg (h 0)).trans (hK 0)
  obtain ⟨B₀, hB₀⟩ := Metric.tendsto_atTop.mp hh (η / 2) (half_pos hη)
  have hHB₀ : 0 ≤ harmonicSum B₀ := harmonicSum_nonneg B₀
  refine ⟨Ce + 2 + K * harmonicSum B₀,
    by positivity, fun A B hAB => ?_⟩
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simpa [sieveUnitGram, sieveUnits, sievedHarmonic] using
      (show 0 ≤ Ce + 2 + K * harmonicSum B₀ by positivity)
  have hHA := sievedHarmonic_nonneg Q A
  have heBound' : |∑ k ∈ sieveUnits Q A, e (B / k) / (k : ℝ)| ≤
      η / 2 * sievedHarmonic Q A + Ce :=
    heBound A B (sieveUnits Q A) (filter_subset _ _) hAB
  have hhBound : |sievedHarmonic Q A * h B| ≤
      η / 2 * sievedHarmonic Q A + K * harmonicSum B₀ := by
    rw [abs_mul, abs_of_nonneg hHA]
    by_cases hlarge : B₀ ≤ B
    · have hnear : |h B| ≤ η / 2 := by
        simpa only [Real.dist_eq, sub_zero] using (hB₀ B hlarge).le
      exact (mul_le_mul_of_nonneg_left hnear hHA).trans
        (by rw [mul_comm]; exact le_add_of_nonneg_right (by positivity))
    · have hmass : sievedHarmonic Q A ≤ harmonicSum B₀ :=
        (sievedHarmonic_le_harmonicSum Q A).trans
          (harmonicSum_mono (hAB.trans (Nat.le_of_lt (by omega : B < B₀))))
      calc
        sievedHarmonic Q A * |h B| ≤ harmonicSum B₀ * K :=
          mul_le_mul hmass (hK B) (abs_nonneg _) (harmonicSum_nonneg B₀)
        _ ≤ η / 2 * sievedHarmonic Q A + K * harmonicSum B₀ := by
          rw [mul_comm (harmonicSum B₀)]
          exact le_add_of_nonneg_left (mul_nonneg (half_pos hη).le hHA)
  have hrow : sieveUnitGram Q A B =
      (Real.log B - sieveEuler Q) * sievedHarmonic Q A +
        (∑ k ∈ sieveUnits Q A, e (B / k) / (k : ℝ)) -
        (∑ k ∈ sieveUnits Q A,
          (Real.log B - Real.log ((B / k : ℕ) : ℝ) - Real.log k) / (k : ℝ)) := by
    rw [sieveUnitGram_eq Q hAB]
    change (∑ k ∈ sieveUnits Q A, (sievedMertensSum Q (B / k) + Real.log k) / (k : ℝ)) =
      (Real.log B - sieveEuler Q) * (∑ k ∈ sieveUnits Q A, 1 / (k : ℝ)) + _ - _
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by dsimp only [e]; ring
  have hident : sieveUnitGram Q A B - sievedHarmonic Q A * sievedHarmonic Q B / sieveDensity Q +
      2 * sieveEuler Q * sievedHarmonic Q A =
      (∑ k ∈ sieveUnits Q A, e (B / k) / (k : ℝ)) -
        (∑ k ∈ sieveUnits Q A,
          (Real.log B - Real.log ((B / k : ℕ) : ℝ) - Real.log k) / (k : ℝ)) -
        sievedHarmonic Q A * h B := by
    rw [hrow]
    dsimp only [h]
    ring
  rw [hident]
  have hround := sieve_log_roundoff_sum_le Q hA hAB
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add heBound' hround)) hhBound)).trans_eq (by ring)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
