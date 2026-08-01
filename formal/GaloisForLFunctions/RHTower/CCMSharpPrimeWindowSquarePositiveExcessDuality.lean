import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareCorrelationEnergy

/-!
# One-sided square-aperture convex duality for the sharp prime window

The full centered square correlation controls both signs of the prime-window deviation.  Route I
needs only the positive excess.  This module gives its exact finite Legendre dual over nonnegative
aperture weights, identifies the optimizer, and isolates the corresponding all-subpower source
predicate.  No estimate for that predicate is assumed or proved here.
-/

open Complex LSeries

namespace RHTower

noncomputable section

/-- The square-sampled one-sided Hilbert energy through aperture `M`. -/
def squarePrimeWindowPositiveExcessSquareEnergy (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, (squarePrimeWindowCenteredDeviation m)⁺ ^ 2

/-- The finite convex-dual functional at aperture weight `u`. -/
def squarePrimeWindowPositiveExcessDualFunctional (M : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    (2 * u m * squarePrimeWindowCenteredDeviation m - (u m) ^ 2)

/-- Admissibility for a one-sided aperture weight. -/
def SquarePrimeWindowApertureWeightNonnegative (M : ℕ) (u : ℕ → ℝ) : Prop :=
  ∀ m ∈ Finset.Icc 1 M, 0 ≤ u m

/-- The canonical optimizer is the positive part of the centered deviation. -/
def squarePrimeWindowOptimalApertureWeight (m : ℕ) : ℝ :=
  (squarePrimeWindowCenteredDeviation m)⁺

/-- The square-sampled centered deviation is minus one half of the existing sharp source. -/
theorem squarePrimeWindowCenteredDeviation_eq_neg_half_sharpSource (m : ℕ) :
    squarePrimeWindowCenteredDeviation m =
      -(1 / 2 : ℝ) * dyadicSharpPrimeSourceCoefficient (m ^ 2) := by
  rw [squarePrimeWindowCenteredDeviation, dyadicSharpPrimeSourceCoefficient]
  simp only [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)]
  ring

/-- The dual functional written directly in the pre-existing Route-I sharp-source coordinate. -/
theorem squarePrimeWindowPositiveExcessDualFunctional_eq_sharpSource
    (M : ℕ) (u : ℕ → ℝ) :
    squarePrimeWindowPositiveExcessDualFunctional M u =
      ∑ m ∈ Finset.Icc 1 M,
        (-u m * dyadicSharpPrimeSourceCoefficient (m ^ 2) - (u m) ^ 2) := by
  rw [squarePrimeWindowPositiveExcessDualFunctional]
  apply Finset.sum_congr rfl
  intro m hm
  rw [squarePrimeWindowCenteredDeviation_eq_neg_half_sharpSource]
  ring

/-- Prime-side aperture weight induced by the dual vector. -/
def squareWindowDualPrimeWeight (M : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    u m * if squareWindowContains m k then 1 else 0

/-- The weighted square-window source is a finite pairing against the induced prime weight. -/
theorem sum_apertureWeight_mul_dyadicWeightedPrimeWindow_square
    (M : ℕ) (u : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 M, u m * dyadicWeightedPrimeWindow (m ^ 2) =
      ∑ k ∈ squareApertureCarrier M,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
          squareWindowDualPrimeWeight M u k := by
  let S := Finset.Icc 1 M
  let T := squareApertureCarrier M
  have hwindow (m : ℕ) (hm : m ∈ S) :
      dyadicWeightedPrimeWindow (m ^ 2) = ∑ k ∈ T, squareWindowTerm m k :=
    dyadicWeightedPrimeWindow_square_eq_carrier_sum hm
  calc
    ∑ m ∈ S, u m * dyadicWeightedPrimeWindow (m ^ 2) =
        ∑ m ∈ S, u m * (∑ k ∈ T, squareWindowTerm m k) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hwindow m hm]
    _ = ∑ k ∈ T, ∑ m ∈ S, u m * squareWindowTerm m k :=
      sum_weight_mul_sum_fubini u squareWindowTerm
    _ = ∑ k ∈ T,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
          squareWindowDualPrimeWeight M u k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [squareWindowDualPrimeWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [squareWindowTerm]
      by_cases hmk : squareWindowContains m k <;> simp [hmk]
      ring

/-- Exact prime-side expansion of the one-sided dual functional. -/
theorem squarePrimeWindowPositiveExcessDualFunctional_eq_primePairing
    (M : ℕ) (u : ℕ → ℝ) :
    squarePrimeWindowPositiveExcessDualFunctional M u =
      2 * (∑ k ∈ squareApertureCarrier M,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
          squareWindowDualPrimeWeight M u k) -
      4 * (1 - (Real.sqrt 2)⁻¹) *
        (∑ m ∈ Finset.Icc 1 M, (m : ℝ) * u m) -
      ∑ m ∈ Finset.Icc 1 M, (u m) ^ 2 := by
  rw [squarePrimeWindowPositiveExcessDualFunctional]
  have hpair := sum_apertureWeight_mul_dyadicWeightedPrimeWindow_square M u
  rw [← hpair]
  simp_rw [squarePrimeWindowCenteredDeviation]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Scalar one-sided Legendre inequality. -/
theorem two_mul_mul_sub_sq_le_posPart_sq {x u : ℝ} (hu : 0 ≤ u) :
    2 * u * x - u ^ 2 ≤ x⁺ ^ 2 := by
  rw [posPart_def]
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    nlinarith [sq_nonneg (u - x)]
  · rw [max_eq_right (le_of_not_ge hx)]
    nlinarith

/-- The scalar inequality is sharp at `u=x⁺`. -/
theorem two_mul_posPart_mul_sub_posPart_sq (x : ℝ) :
    2 * x⁺ * x - x⁺ ^ 2 = x⁺ ^ 2 := by
  rw [posPart_def]
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    ring
  · rw [max_eq_right (le_of_not_ge hx)]
    ring

/-- Exact scalar defect: optimizer distance plus weight spent on the negative channel. -/
theorem posPart_sq_sub_two_mul_mul_sub_sq_eq_dualDefect (x u : ℝ) :
    x⁺ ^ 2 - (2 * u * x - u ^ 2) =
      (u - x⁺) ^ 2 + 2 * u * x⁻ := by
  rw [posPart_def, negPart_def]
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ 0)]
    ring
  · rw [max_eq_right (le_of_not_ge hx), max_eq_left (by linarith : 0 ≤ -x)]
    ring

/-- Every noncanonical scalar test misses the untruncated quadratic optimum strictly. -/
theorem two_mul_mul_sub_sq_lt_sq_of_ne
    {x u : ℝ} (hne : u ≠ x) :
    2 * u * x - u ^ 2 < x ^ 2 := by
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]

/-- No fixed finite scalar test dictionary recovers every positive quadratic ray. -/
theorem exists_pos_dualTerm_lt_sq_forall_finset (U : Finset ℝ) :
    ∃ x : ℝ, 0 < x ∧ ∀ u ∈ U, 2 * u * x - u ^ 2 < x ^ 2 := by
  let x : ℝ := ∑ u ∈ U, |u| + 1
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  refine ⟨x, hx, ?_⟩
  intro u hu
  have huabs : |u| ≤ ∑ v ∈ U, |v| := by
    exact Finset.single_le_sum (fun v hv => abs_nonneg v) hu
  have hux : u < x := by
    dsimp only [x]
    linarith [le_abs_self u]
  exact two_mul_mul_sub_sq_lt_sq_of_ne (ne_of_lt hux)

/-- Exact finite defect decomposition for an arbitrary aperture weight. -/
theorem squarePrimeWindowPositiveExcessSquareEnergy_sub_dualFunctional_eq_defect
    (M : ℕ) (u : ℕ → ℝ) :
    squarePrimeWindowPositiveExcessSquareEnergy M -
        squarePrimeWindowPositiveExcessDualFunctional M u =
      ∑ m ∈ Finset.Icc 1 M,
        ((u m - (squarePrimeWindowCenteredDeviation m)⁺) ^ 2 +
          2 * u m * (squarePrimeWindowCenteredDeviation m)⁻) := by
  rw [squarePrimeWindowPositiveExcessSquareEnergy,
    squarePrimeWindowPositiveExcessDualFunctional,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  exact posPart_sq_sub_two_mul_mul_sub_sq_eq_dualDefect
    (squarePrimeWindowCenteredDeviation m) (u m)

/-- Every admissible dual test is bounded by the one-sided square energy. -/
theorem squarePrimeWindowPositiveExcessDualFunctional_le_energy
    {M : ℕ} {u : ℕ → ℝ}
    (hu : SquarePrimeWindowApertureWeightNonnegative M u) :
    squarePrimeWindowPositiveExcessDualFunctional M u ≤
      squarePrimeWindowPositiveExcessSquareEnergy M := by
  rw [squarePrimeWindowPositiveExcessDualFunctional,
    squarePrimeWindowPositiveExcessSquareEnergy]
  apply Finset.sum_le_sum
  intro m hm
  exact two_mul_mul_sub_sq_le_posPart_sq (hu m hm)

/-- The canonical positive-part weight attains the one-sided square energy exactly. -/
theorem squarePrimeWindowPositiveExcessDualFunctional_optimal_eq_energy (M : ℕ) :
    squarePrimeWindowPositiveExcessDualFunctional M
        squarePrimeWindowOptimalApertureWeight =
      squarePrimeWindowPositiveExcessSquareEnergy M := by
  rw [squarePrimeWindowPositiveExcessDualFunctional,
    squarePrimeWindowPositiveExcessSquareEnergy]
  apply Finset.sum_congr rfl
  intro m hm
  exact two_mul_posPart_mul_sub_posPart_sq
    (squarePrimeWindowCenteredDeviation m)

/-- The canonical aperture weight is admissible. -/
theorem squarePrimeWindowOptimalApertureWeight_nonnegative (M : ℕ) :
    SquarePrimeWindowApertureWeightNonnegative M
      squarePrimeWindowOptimalApertureWeight := by
  intro m hm
  exact posPart_nonneg _

/-- Exact finite dual characterization of every upper bound for the one-sided energy. -/
theorem squarePrimeWindowPositiveExcessSquareEnergy_le_iff_forall_dual_le
    (M : ℕ) (B : ℝ) :
    squarePrimeWindowPositiveExcessSquareEnergy M ≤ B ↔
      ∀ u : ℕ → ℝ, SquarePrimeWindowApertureWeightNonnegative M u →
        squarePrimeWindowPositiveExcessDualFunctional M u ≤ B := by
  constructor
  · intro hEnergy u hu
    exact (squarePrimeWindowPositiveExcessDualFunctional_le_energy hu).trans hEnergy
  · intro hDual
    rw [← squarePrimeWindowPositiveExcessDualFunctional_optimal_eq_energy M]
    exact hDual squarePrimeWindowOptimalApertureWeight
      (squarePrimeWindowOptimalApertureWeight_nonnegative M)

/-- The one-sided energy is exactly the squared positive-excess summatory function. -/
theorem squarePrimeWindowPositiveExcessSquareEnergy_eq_summatory (M : ℕ) :
    squarePrimeWindowPositiveExcessSquareEnergy M =
      ∑ m ∈ Finset.Icc 1 M,
        (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2 := by
  rw [squarePrimeWindowPositiveExcessSquareEnergy]
  apply Finset.sum_congr rfl
  intro m hm
  rw [squarePrimeWindowPositiveExcess_eq_posPart_centeredDeviation]

/-- Exact collision with the square-sampled Hilbert energy of Route I's sharp-source negative
part. -/
theorem four_mul_squarePrimeWindowPositiveExcessSquareEnergy_eq_sharpSourceNegativePart
    (M : ℕ) :
    4 * squarePrimeWindowPositiveExcessSquareEnergy M =
      ∑ m ∈ Finset.Icc 1 M,
        (dyadicSharpPrimeSourceNegativePart (m ^ 2)) ^ 2 := by
  rw [squarePrimeWindowPositiveExcessSquareEnergy_eq_summatory, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess]
  ring

/-- The exact surviving Route-I source predicate in one-sided Hilbert form. -/
def SquarePrimeWindowPositiveExcessSquareEnergySubpower : Prop :=
  ∀ delta : ℝ, 0 < delta →
    squarePrimeWindowPositiveExcessSquareEnergy =O[Filter.atTop]
      (fun M : ℕ => (M : ℝ) ^ (1 + delta))

/-- Near-linear growth of the one-sided square-aperture energy proves RH. -/
theorem riemannHypothesis_of_squarePrimeWindowPositiveExcessSquareEnergySubpower
    (hEnergy : SquarePrimeWindowPositiveExcessSquareEnergySubpower) :
    RiemannHypothesis := by
  let squareExcessSquare : ℕ → ℝ := fun m =>
    (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2
  have hnonneg : ∀ m, 0 ≤ squareExcessSquare m := fun m => sq_nonneg _
  have hGrowth : ∀ delta : ℝ, 0 < delta →
      (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, squareExcessSquare m) =O[Filter.atTop]
        (fun M : ℕ => (M : ℝ) ^ (1 + delta)) := by
    intro delta hdelta
    have h := hEnergy delta hdelta
    have hfun : squarePrimeWindowPositiveExcessSquareEnergy =
        fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
          (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2 :=
      funext squarePrimeWindowPositiveExcessSquareEnergy_eq_summatory
    rw [hfun] at h
    simpa only [squareExcessSquare] using h
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

end

end RHTower
