import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareEnergySampling

/-!
# Square-aperture von Mangoldt correlation energy

The surviving coefficient-nonlocal Route-I pivot is an exact finite two-point correlation problem.
For square apertures, this module expands the centered sharp-window energy into an explicit
von-Mangoldt pair sum weighted by the number of square windows containing each pair. It then proves
that an every-superlinear-power bound for this correlation energy implies the Riemann hypothesis.

The finite identities and implication are unconditional. The correlation-energy bound itself is
isolated as `SquarePrimeWindowCorrelationEnergySubpower`; no estimate for it is assumed elsewhere.
-/

open scoped BigOperators
open Complex Filter Real LSeries

noncomputable section

namespace RHTower

def squareApertureCarrier (M : ℕ) : Finset ℕ := Finset.range (M ^ 2 + 1)

def squareWindowContains (m k : ℕ) : Prop := m ^ 2 / 2 < k ∧ k ≤ m ^ 2

instance squareWindowContainsDecidable (m k : ℕ) : Decidable (squareWindowContains m k) := by
  unfold squareWindowContains
  infer_instance

def squareWindowTerm (m k : ℕ) : ℝ :=
  if squareWindowContains m k then
    ArithmeticFunction.vonMangoldt k / Real.sqrt k
  else 0

def squareWindowOverlapKernel (M k l : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    if squareWindowContains m k ∧ squareWindowContains m l then 1 else 0

def squareWindowFirstMomentKernel (M k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    if squareWindowContains m k then (m : ℝ) else 0

theorem squareWindowOverlapKernel_nonneg (M k l : ℕ) :
    0 ≤ squareWindowOverlapKernel M k l := by
  rw [squareWindowOverlapKernel]
  exact Finset.sum_nonneg fun m hm => by split_ifs <;> positivity

theorem squareWindowOverlapKernel_comm (M k l : ℕ) :
    squareWindowOverlapKernel M k l = squareWindowOverlapKernel M l k := by
  rw [squareWindowOverlapKernel, squareWindowOverlapKernel]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [and_comm]

def squareWindowCorrelationEnergy (M : ℕ) : ℝ :=
  let c : ℝ := 2 * (1 - (Real.sqrt 2)⁻¹)
  let T := squareApertureCarrier M
  (∑ k ∈ T, ∑ l ∈ T,
      (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
        (ArithmeticFunction.vonMangoldt l / Real.sqrt l) *
          squareWindowOverlapKernel M k l) +
    (-2 * c) *
      (∑ k ∈ T,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
          squareWindowFirstMomentKernel M k) +
    c ^ 2 * ∑ m ∈ Finset.Icc 1 M, (m : ℝ) ^ 2

theorem dyadicWeightedPrimeWindow_square_eq_carrier_sum
    {M m : ℕ} (hm : m ∈ Finset.Icc 1 M) :
    dyadicWeightedPrimeWindow (m ^ 2) =
      ∑ k ∈ squareApertureCarrier M, squareWindowTerm m k := by
  rw [dyadicWeightedPrimeWindow]
  symm
  rw [squareApertureCarrier]
  simp_rw [squareWindowTerm]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc,
      squareWindowContains]
    constructor
    · rintro ⟨hkcarrier, hlow, hhigh⟩
      exact ⟨hlow, hhigh⟩
    · intro hk
      refine ⟨?_, hk⟩
      have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
      have hsq : m ^ 2 ≤ M ^ 2 := by nlinarith
      omega
  · intro k hk
    rfl

theorem sum_sq_fubini
    {S T : Finset ℕ} (b : ℕ → ℕ → ℝ) :
    ∑ m ∈ S, (∑ k ∈ T, b m k) ^ 2 =
      ∑ k ∈ T, ∑ l ∈ T, ∑ m ∈ S, b m k * b m l := by
  calc
    ∑ m ∈ S, (∑ k ∈ T, b m k) ^ 2 =
        ∑ m ∈ S, ∑ k ∈ T, ∑ l ∈ T, b m k * b m l := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ k ∈ T, ∑ m ∈ S, ∑ l ∈ T, b m k * b m l := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ T, ∑ l ∈ T, ∑ m ∈ S, b m k * b m l := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]

theorem sum_weight_mul_sum_fubini
    {S T : Finset ℕ} (w : ℕ → ℝ) (b : ℕ → ℕ → ℝ) :
    ∑ m ∈ S, w m * (∑ k ∈ T, b m k) =
      ∑ k ∈ T, ∑ m ∈ S, w m * b m k := by
  calc
    ∑ m ∈ S, w m * (∑ k ∈ T, b m k) =
        ∑ m ∈ S, ∑ k ∈ T, w m * b m k := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ = ∑ k ∈ T, ∑ m ∈ S, w m * b m k := by
      rw [Finset.sum_comm]

theorem squareWindowTerm_pair_sum_eq_overlap
    (M k l : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, squareWindowTerm m k * squareWindowTerm m l =
      (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
        (ArithmeticFunction.vonMangoldt l / Real.sqrt l) *
          squareWindowOverlapKernel M k l := by
  rw [squareWindowOverlapKernel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [squareWindowTerm]
  by_cases hk : squareWindowContains m k <;>
    by_cases hl : squareWindowContains m l <;> simp [hk, hl]

theorem squareWindowTerm_firstMoment_sum_eq_kernel (M k : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * squareWindowTerm m k =
      (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
        squareWindowFirstMomentKernel M k := by
  rw [squareWindowFirstMomentKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [squareWindowTerm]
  by_cases hk : squareWindowContains m k <;> simp [hk]
  ring

theorem squareWindowCorrelationEnergy_eq_centered_deviation_square_sum (M : ℕ) :
    squareWindowCorrelationEnergy M =
      ∑ m ∈ Finset.Icc 1 M,
        (dyadicWeightedPrimeWindow (m ^ 2) -
          2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ)) ^ 2 := by
  let c : ℝ := 2 * (1 - (Real.sqrt 2)⁻¹)
  let S := Finset.Icc 1 M
  let T := squareApertureCarrier M
  have hwindow (m : ℕ) (hm : m ∈ S) :
      dyadicWeightedPrimeWindow (m ^ 2) = ∑ k ∈ T, squareWindowTerm m k := by
    exact dyadicWeightedPrimeWindow_square_eq_carrier_sum hm
  have hquad :
      (∑ k ∈ T, ∑ l ∈ T,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
          (ArithmeticFunction.vonMangoldt l / Real.sqrt l) *
            squareWindowOverlapKernel M k l) =
        ∑ m ∈ S, (dyadicWeightedPrimeWindow (m ^ 2)) ^ 2 := by
    calc
      _ = ∑ k ∈ T, ∑ l ∈ T, ∑ m ∈ S,
          squareWindowTerm m k * squareWindowTerm m l := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        rw [squareWindowTerm_pair_sum_eq_overlap]
      _ = ∑ m ∈ S, (∑ k ∈ T, squareWindowTerm m k) ^ 2 :=
        (sum_sq_fubini squareWindowTerm).symm
      _ = ∑ m ∈ S, (dyadicWeightedPrimeWindow (m ^ 2)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [hwindow m hm]
  have hcross :
      (∑ k ∈ T,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
          squareWindowFirstMomentKernel M k) =
        ∑ m ∈ S, (m : ℝ) * dyadicWeightedPrimeWindow (m ^ 2) := by
    calc
      _ = ∑ k ∈ T, ∑ m ∈ S, (m : ℝ) * squareWindowTerm m k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [squareWindowTerm_firstMoment_sum_eq_kernel]
      _ = ∑ m ∈ S, (m : ℝ) * (∑ k ∈ T, squareWindowTerm m k) :=
        (sum_weight_mul_sum_fubini (fun m => (m : ℝ)) squareWindowTerm).symm
      _ = ∑ m ∈ S, (m : ℝ) * dyadicWeightedPrimeWindow (m ^ 2) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [hwindow m hm]
  rw [squareWindowCorrelationEnergy]
  change
    (∑ k ∈ T, ∑ l ∈ T,
      (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
        (ArithmeticFunction.vonMangoldt l / Real.sqrt l) *
          squareWindowOverlapKernel M k l) +
      (-2 * c) *
        (∑ k ∈ T,
          (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
            squareWindowFirstMomentKernel M k) +
      c ^ 2 * ∑ m ∈ S, (m : ℝ) ^ 2 = _
  rw [hquad, hcross]
  calc
    _ = ∑ m ∈ S,
        ((dyadicWeightedPrimeWindow (m ^ 2)) ^ 2 +
          (-2 * c) * ((m : ℝ) * dyadicWeightedPrimeWindow (m ^ 2)) +
          c ^ 2 * (m : ℝ) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [c]
      ring

theorem squareWindowCorrelationEnergy_nonneg (M : ℕ) :
    0 ≤ squareWindowCorrelationEnergy M := by
  rw [squareWindowCorrelationEnergy_eq_centered_deviation_square_sum]
  exact Finset.sum_nonneg fun m hm => sq_nonneg _

def squarePrimeWindowCenteredDeviation (m : ℕ) : ℝ :=
  dyadicWeightedPrimeWindow (m ^ 2) -
    2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ)

theorem squarePrimeWindowPositiveExcess_eq_posPart_centeredDeviation (m : ℕ) :
    dyadicWeightedPrimeWindowPositiveExcess (m ^ 2) =
      (squarePrimeWindowCenteredDeviation m)⁺ := by
  rw [dyadicWeightedPrimeWindowPositiveExcess, squarePrimeWindowCenteredDeviation]
  simp only [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)]

theorem squareWindowCorrelationEnergy_eq_centeredDeviation_square_sum (M : ℕ) :
    squareWindowCorrelationEnergy M =
      ∑ m ∈ Finset.Icc 1 M, (squarePrimeWindowCenteredDeviation m) ^ 2 := by
  simpa [squarePrimeWindowCenteredDeviation] using
    squareWindowCorrelationEnergy_eq_centered_deviation_square_sum M

def SquarePrimeWindowCorrelationEnergySubpower : Prop :=
  ∀ delta : ℝ, 0 < delta →
    squareWindowCorrelationEnergy =O[Filter.atTop]
      (fun M : ℕ => (M : ℝ) ^ (1 + delta))

theorem squarePrimeWindowPositiveExcessSquare_summatory_isBigO
    (hCorrelation : SquarePrimeWindowCorrelationEnergySubpower)
    (delta : ℝ) (hdelta : 0 < delta) :
    (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
      (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2) =O[Filter.atTop]
        (fun M : ℕ => (M : ℝ) ^ (1 + delta)) := by
  let excessSquareSum : ℕ → ℝ := fun M => ∑ m ∈ Finset.Icc 1 M,
    (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2
  have hnonneg (M : ℕ) : 0 ≤ excessSquareSum M := by
    exact Finset.sum_nonneg fun m hm => sq_nonneg _
  have hle (M : ℕ) : excessSquareSum M ≤ squareWindowCorrelationEnergy M := by
    rw [squareWindowCorrelationEnergy_eq_centeredDeviation_square_sum]
    apply Finset.sum_le_sum
    intro m hm
    rw [squarePrimeWindowPositiveExcess_eq_posPart_centeredDeviation]
    rw [posPart_def]
    by_cases hx : 0 ≤ squarePrimeWindowCenteredDeviation m
    · rw [max_eq_left hx]
    · rw [max_eq_right (le_of_not_ge hx)]
      simpa using sq_nonneg (squarePrimeWindowCenteredDeviation m)
  have hdom : excessSquareSum =O[Filter.atTop] squareWindowCorrelationEnergy := by
    apply Asymptotics.IsBigO.of_norm_le
    intro M
    rw [Real.norm_of_nonneg (hnonneg M)]
    exact hle M
  exact hdom.trans (hCorrelation delta hdelta)

theorem riemannHypothesis_of_squarePrimeWindowCorrelationEnergySubpower
    (hCorrelation : SquarePrimeWindowCorrelationEnergySubpower) :
    RiemannHypothesis := by
  let squareExcessSquare : ℕ → ℝ := fun m =>
    (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2
  have hnonneg : ∀ m, 0 ≤ squareExcessSquare m := fun m => sq_nonneg _
  have hGrowth : ∀ delta : ℝ, 0 < delta →
      (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, squareExcessSquare m) =O[Filter.atTop]
        (fun M : ℕ => (M : ℝ) ^ (1 + delta)) := by
    intro delta hdelta
    simpa [squareExcessSquare] using
      squarePrimeWindowPositiveExcessSquare_summatory_isBigO
        hCorrelation delta hdelta
  have hAbscissa :
      LSeries.abscissaOfAbsConv (fun m => ((squareExcessSquare m : ℝ) : ℂ)) ≤
        ((1 : ℝ) : EReal) := by
    apply (abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
      hnonneg zero_le_one).mpr
    exact hGrowth
  apply riemannHypothesis_of_squarePrimeWindowPositiveExcessSquareEnergy
  intro epsilon hepsilon
  have hstrict :
      LSeries.abscissaOfAbsConv (fun m => ((squareExcessSquare m : ℝ) : ℂ)) <
        (((1 + epsilon : ℝ)) : EReal) := by
    apply hAbscissa.trans_lt
    exact_mod_cast (by linarith : (1 : ℝ) < 1 + epsilon)
  have hsum : Summable (fun m : ℕ =>
      squareExcessSquare m / (m : ℝ) ^ (1 + epsilon)) :=
    LSeries.summable_real_of_abscissaOfAbsConv_lt hstrict
  apply hsum.congr
  intro m
  by_cases hm : m = 0
  · subst m
    have hexp : 0 < 1 + epsilon := by linarith
    simp [realDirichletWeightedTerm, Real.zero_rpow hexp.ne']
  · simp [realDirichletWeightedTerm, squareExcessSquare, hm]

end RHTower
