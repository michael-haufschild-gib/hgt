import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBounded
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueFirstBranchPublishedRegime

/-!
# Refined bounded-coefficient Heath--Brown sparse mean value

This supplies the published refinement used in Matomäki--Teräväinen Lemma 3.4: the mixed
`R^(7/4) T^(3/4)` term disappears when either the dense length is at least `T^(2/3)` or the
sparse support has cardinality at most `T^(1/3)`.  The first alternative uses Heath--Brown's
separate square-root branch; it is not inferred from the unrefined three-term estimate.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- Explicit coefficient obtained from Heath--Brown's first branch at exponent `eta / 2`. -/
def heathBrownFirstBranchCoefficient (eta : ℝ) : ℝ :=
  (25 * Real.pi) ^ 2 *
    (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) *
    divisorBoundConst (eta / 2) ^ 2 *
    (25 * Real.pi / 8) ^ 2

/-- One coefficient valid in both published mixed-term deletion regimes. -/
def heathBrownRefinedCoefficient (eta : ℝ) : ℝ :=
  max (heathBrownFirstBranchCoefficient eta)
    (2 * heathBrownTheoremFourCoefficient eta)

theorem heathBrownFirstBranchCoefficient_nonneg (eta : ℝ) :
    0 ≤ heathBrownFirstBranchCoefficient eta := by
  dsimp only [heathBrownFirstBranchCoefficient]
  positivity

theorem heathBrownRefinedCoefficient_nonneg (eta : ℝ) :
    0 ≤ heathBrownRefinedCoefficient eta := by
  exact (heathBrownFirstBranchCoefficient_nonneg eta).trans (le_max_left _ _)

private theorem heathBrown_rpow_half_sq {x eta : ℝ} (hx : 0 ≤ x) :
    (x ^ (eta / 2)) ^ 2 = x ^ eta := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem heathBrown_mixed_le_linear_of_card_le_oneThird
    {R T : ℝ} (hR : 0 ≤ R) (hT : 1 ≤ T)
    (hsmall : R ≤ T ^ (1 / 3 : ℝ)) :
    R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ≤ R * T := by
  by_cases hRzero : R = 0
  · subst R
    norm_num
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hquarter : R ^ (3 / 4 : ℝ) ≤ T ^ (1 / 4 : ℝ) := by
      calc
        R ^ (3 / 4 : ℝ) ≤ (T ^ (1 / 3 : ℝ)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow hR hsmall (by norm_num)
        _ = T ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_mul hTpos.le]
          norm_num
    calc
      R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) =
          (R * R ^ (3 / 4 : ℝ)) * T ^ (3 / 4 : ℝ) := by
        rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num,
          Real.rpow_add hRpos, Real.rpow_one]
      _ ≤ (R * T ^ (1 / 4 : ℝ)) * T ^ (3 / 4 : ℝ) := by
        gcongr
      _ = R * T := by
        rw [mul_assoc, ← Real.rpow_add hTpos]
        norm_num

/-- Bounded sparse coefficients in Heath--Brown's published first regime.  The mixed term is
absent because this uses the independent square-root branch. -/
theorem integral_Icc_normSq_heathBrownBounded_factors_le_firstBranchPublishedRegime
    (A B : Finset PNat) (c : ℕ → ℂ) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    (hc : ∀ m ∈ A, ‖c (m : ℕ)‖ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    (hregime : (T : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (25 * Real.pi / 4) *
        (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          heathBrownFirstBranchCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ))) := by
  let Jhalf : ℝ := ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
      (heathBrownHalfHeight T : ℝ),
    ‖heathBrownSparseFactor A (fun _ => 1) t *
      heathBrownDenseFactor (heathBrownPositiveInterval N hN)
        heathBrownDenseUnitWeight t‖ ^ 2
  let J : ℝ := ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
    ‖heathBrownSparseFactor A (fun _ => 1) t *
      heathBrownDenseFactor (heathBrownPositiveInterval N hN)
        heathBrownDenseUnitWeight t‖ ^ 2
  have hforward :=
    integral_Icc_normSq_heathBrownBounded_factors_le_weightedCollision A B c q T hc
  have haggregate := heathBrownPositiveWeightedCollision_le_collisionAggregate A B q T hB
  have hreverse :=
    cast_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightIntegral A T hN
  have hheight : Jhalf ≤ J := by
    apply integral_Icc_normSq_heathBrown_fullUnit_height_mono A N hN
    change (T : ℝ) / 2 ≤ (T : ℝ)
    linarith [T.property]
  have hunit := integral_Icc_normSq_heathBrown_fullUnit_le_firstBranchPublishedRegime
    A T hT hA hN hregime (eta := eta / 2) (by linarith)
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hT0 : 0 ≤ (T : ℝ) := T.property.le
  have hTone : 1 ≤ (T : ℝ) := by linarith
  have hTeta : 1 ≤ (T : ℝ) ^ eta := Real.one_le_rpow hTone heta.le
  have hhalf : (((N : ℝ) ^ (eta / 2)) ^ 2) = (N : ℝ) ^ eta :=
    heathBrown_rpow_half_sq hN0
  have hC0 : 0 ≤ heathBrownFirstBranchCoefficient eta :=
    heathBrownFirstBranchCoefficient_nonneg eta
  have hmain0 : 0 ≤ (N : ℝ) * (A.card : ℝ) * (T : ℝ) := by positivity
  have hterm :
      (25 * Real.pi) ^ 2 * (N : ℝ) *
          (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
            (A.card : ℝ) *
            ((divisorBoundConst (eta / 2) * (N : ℝ) ^ (eta / 2)) ^ 2 *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) ≤
        heathBrownFirstBranchCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
          ((N : ℝ) * (A.card : ℝ) * (T : ℝ)) := by
    have heq :
        (25 * Real.pi) ^ 2 * (N : ℝ) *
            (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
              (A.card : ℝ) *
              ((divisorBoundConst (eta / 2) * (N : ℝ) ^ (eta / 2)) ^ 2 *
                (25 * Real.pi / 8) * (25 * Real.pi / 8))) =
          heathBrownFirstBranchCoefficient eta * (N : ℝ) ^ eta *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ)) := by
      dsimp only [heathBrownFirstBranchCoefficient]
      simp only [mul_pow]
      rw [hhalf]
      ring
    rw [heq, Real.mul_rpow hN0 hT0]
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTeta (Real.rpow_nonneg hN0 eta)) hmain0)
      hC0
  have hunit' : J ≤
      110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        heathBrownFirstBranchCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
          ((N : ℝ) * (A.card : ℝ) * (T : ℝ)) := by
    exact hunit.trans (add_le_add le_rfl hterm)
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) * heathBrownPositiveWeightedCollision A B q T :=
        hforward
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
        (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) := by
      gcongr
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) * ((5 / (2 * (T : ℝ))) * Jhalf) := by
      gcongr
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) * ((5 / (2 * (T : ℝ))) * J) := by
      gcongr
    _ = (25 * Real.pi / 4) * J := by
      have hTne : (T : ℝ) ≠ 0 := ne_of_gt T.property
      field_simp [hTne]
      ring
    _ ≤ (25 * Real.pi / 4) *
        (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          heathBrownFirstBranchCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ))) :=
      mul_le_mul_of_nonneg_left hunit' (by positivity)

/-- Coefficient-faithful Heath--Brown estimate with the mixed term deleted in either published
regime, for heights at least two. -/
theorem integral_Icc_normSq_heathBrownBounded_factors_le_refined_of_two_le
    (A B : Finset PNat) (c : ℕ → ℂ) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    (hc : ∀ m ∈ A, ‖c (m : ℕ)‖ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    (hregime : (T : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ∨
      (A.card : ℝ) ≤ (T : ℝ) ^ (1 / 3 : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (25 * Real.pi / 4) *
        (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          heathBrownRefinedCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ))) := by
  rcases hregime with hlarge | hsmall
  · have hbase :=
      integral_Icc_normSq_heathBrownBounded_factors_le_firstBranchPublishedRegime
        A B c q T hT hA hc hN hB hlarge heta
    have hcoeff : heathBrownFirstBranchCoefficient eta ≤ heathBrownRefinedCoefficient eta :=
      le_max_left _ _
    calc
      _ ≤ (25 * Real.pi / 4) *
          (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
            heathBrownFirstBranchCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
              ((N : ℝ) * (A.card : ℝ) * (T : ℝ))) := hbase
      _ ≤ _ := by gcongr
  · have hbase := integral_Icc_normSq_heathBrownBounded_factors_le_theoremFour_of_two_le
      A B c q T hT hA hc hN hB heta
    have hmixed :
        (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) ≤
          (A.card : ℝ) * (T : ℝ) :=
      heathBrown_mixed_le_linear_of_card_le_oneThird (by positivity) (by linarith) hsmall
    have hsum :
        (N : ℝ) * (A.card : ℝ) * (T : ℝ) +
            (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) ≤
          2 * ((N : ℝ) * (A.card : ℝ) * (T : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hmixed (Nat.cast_nonneg N)
      nlinarith
    have hC0 : 0 ≤ heathBrownTheoremFourCoefficient eta := by
      dsimp only [heathBrownTheoremFourCoefficient,
        heathBrownTheoremFourUniversalCoefficient, heathBrownMeanSquareCoefficient]
      positivity
    have hpow0 : 0 ≤ (((N : ℝ) * (T : ℝ)) ^ eta) :=
      Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) T.property.le) eta
    have hterm :
        heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
              (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) *
                (T : ℝ) ^ (3 / 4 : ℝ)) ≤
          (2 * heathBrownTheoremFourCoefficient eta) *
            (((N : ℝ) * (T : ℝ)) ^ eta) *
              ((N : ℝ) * (A.card : ℝ) * (T : ℝ)) := by
      calc
        _ ≤ heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            (2 * ((N : ℝ) * (A.card : ℝ) * (T : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hC0 hpow0)
        _ = _ := by ring
    have hdiag :
        95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 ≤
          110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by
      have hmass : 0 ≤ (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by positivity
      have hcoef : 95 * Real.pi / 2 ≤ 110 * Real.pi := by
        nlinarith [Real.pi_pos]
      nlinarith
    have href : 2 * heathBrownTheoremFourCoefficient eta ≤
        heathBrownRefinedCoefficient eta := le_max_right _ _
    have hmain0 : 0 ≤ (N : ℝ) * (A.card : ℝ) * (T : ℝ) := by positivity
    calc
      _ ≤ (25 * Real.pi / 4) *
          (95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
            heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
              ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
                (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) *
                  (T : ℝ) ^ (3 / 4 : ℝ))) := hbase
      _ ≤ (25 * Real.pi / 4) *
          (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
            (2 * heathBrownTheoremFourCoefficient eta) *
              (((N : ℝ) * (T : ℝ)) ^ eta) *
                ((N : ℝ) * (A.card : ℝ) * (T : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hdiag hterm) (by positivity)
      _ ≤ _ := by
        gcongr

/-- Full published mixed-term deletion refinement, including the compact range `1 ≤ T < 2`. -/
theorem integral_Icc_normSq_heathBrownBounded_factors_le_refined
    (A B : Finset PNat) (c : ℕ → ℂ) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    (hc : ∀ m ∈ A, ‖c (m : ℕ)‖ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    (hregime : (T : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ∨
      (A.card : ℝ) ≤ (T : ℝ) ^ (1 / 3 : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (25 * Real.pi / 4) *
        (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          heathBrownRefinedCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ))) := by
  by_cases htwo : 2 ≤ (T : ℝ)
  · exact integral_Icc_normSq_heathBrownBounded_factors_le_refined_of_two_le
      A B c q T htwo hA hc hN hB hregime heta
  · have hforward :=
      integral_Icc_normSq_heathBrownBounded_factors_le_weightedCollision A B c q T hc
    have hcollision := heathBrownPositiveWeightedCollision_le_cardProduct_sq A B q T
    have hBcard : (B.card : ℝ) ≤ (N : ℝ) :=
      cast_card_le_height_of_pnat_support B (Nat.cast_nonneg N)
        (fun n hn => by exact_mod_cast hB n hn)
    have hcard0 : 0 ≤ (A.card : ℝ) := by positivity
    have hBcard0 : 0 ≤ (B.card : ℝ) := by positivity
    have hsquare : ((A.card : ℝ) * (B.card : ℝ)) ^ 2 ≤
        (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by
      have hmul : (A.card : ℝ) * (B.card : ℝ) ≤
          (A.card : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left hBcard hcard0
      calc
        ((A.card : ℝ) * (B.card : ℝ)) ^ 2 ≤
            ((A.card : ℝ) * (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hcard0 hBcard0) hmul 2
        _ = (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by ring
    have hdiag :
        (5 * Real.pi / 2) * (T : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) ^ 2 ≤
          (25 * Real.pi / 4) *
            (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
      have hTlt : (T : ℝ) < 2 := lt_of_not_ge htwo
      calc
        _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
            ((N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by gcongr
        _ ≤ (5 * Real.pi) * ((N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
          have hcoefT : (5 * Real.pi / 2) * (T : ℝ) ≤ 5 * Real.pi := by
            nlinarith [Real.pi_pos]
          exact mul_le_mul_of_nonneg_right hcoefT (by positivity)
        _ ≤ (25 * Real.pi / 4) *
            (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
          have hmass : 0 ≤ (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by positivity
          have hcoef : 5 * Real.pi ≤ (25 * Real.pi / 4) * (110 * Real.pi) := by
            nlinarith [Real.pi_gt_three]
          nlinarith
    have hoff0 : 0 ≤
        heathBrownRefinedCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
          ((N : ℝ) * (A.card : ℝ) * (T : ℝ)) := by
      exact mul_nonneg
        (mul_nonneg (heathBrownRefinedCoefficient_nonneg eta)
          (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) T.property.le) eta))
        (by positivity)
    calc
      _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
          heathBrownPositiveWeightedCollision A B q T := hforward
      _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
          ((A.card : ℝ) * (B.card : ℝ)) ^ 2 := by gcongr
      _ ≤ (25 * Real.pi / 4) *
          (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := hdiag
      _ ≤ (25 * Real.pi / 4) *
          (110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
            heathBrownRefinedCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
              ((N : ℝ) * (A.card : ℝ) * (T : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hoff0) (by positivity)

end

end RHTower.Sieve
