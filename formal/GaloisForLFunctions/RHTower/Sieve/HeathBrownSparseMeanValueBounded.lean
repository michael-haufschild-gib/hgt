import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueTheoremFour

/-!
# Heath--Brown sparse mean value with bounded sparse coefficients

The published source allows arbitrary complex sparse coefficients of modulus at most one, not
only circle-valued coefficients.  This module closes that coefficient gap by returning to the
weighted collision form of the finite-frequency estimate.  The existing two-scale collision
theorem and its reverse comparison then reduce the result to the already-closed unit-coefficient
Theorem 4(iii).
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- Sparse physical factor with arbitrary complex coefficients. -/
def heathBrownBoundedSparseFactor (A : Finset PNat) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ A, c (m : ℕ) * heathBrownDirichletPhase m t

theorem continuous_heathBrownBoundedSparseFactor (A : Finset PNat) (c : ℕ → ℂ) :
    Continuous (heathBrownBoundedSparseFactor A c) := by
  unfold heathBrownBoundedSparseFactor
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  unfold heathBrownDirichletPhase
  fun_prop

private def heathBrownBoundedPositiveCoefficient (c : ℕ → ℂ)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (p : PNat × PNat) : ℂ :=
  c (p.1 : ℕ) * (((q (p.2 : ℕ) : ℝ) : ℂ))

private theorem heathBrown_bounded_product_phase (m n : PNat) (t : ℝ) :
    Complex.exp (((2 * Real.pi
      * (t * heathBrownPositiveProductFrequency (m, n)) : ℝ) : ℂ) * Complex.I)
      = heathBrownDirichletPhase m t * heathBrownDirichletPhase n t := by
  have hm : (((m : ℕ) : ℝ)) ≠ 0 := by positivity
  have hn : (((n : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [heathBrownDirichletPhase, heathBrownDirichletPhase, ← Complex.exp_add,
    heathBrownPositiveProductFrequency, heathBrownProductFrequency]
  have hcast : ((((m : ℕ) * (n : ℕ) : ℕ) : ℝ)) =
      ((m : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by norm_cast
  rw [hcast, Real.log_mul hm hn]
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Real.pi_pos)
  field_simp
  ring

private theorem finiteFrequencyPoly_heathBrownBounded_eq_mul
    (A B : Finset PNat) (c : ℕ → ℂ) (q : ℕ → Set.Icc (0 : ℝ) 1) (t : ℝ) :
    finiteFrequencyPoly (heathBrownBoundedPositiveCoefficient c q) (A.product B)
        heathBrownPositiveProductFrequency t =
      heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t := by
  rw [finiteFrequencyPoly]
  calc
    (∑ p ∈ A.product B, heathBrownBoundedPositiveCoefficient c q p *
        Complex.exp (((2 * Real.pi *
          (t * heathBrownPositiveProductFrequency p) : ℝ) : ℂ) * Complex.I)) =
        ∑ m ∈ A, ∑ n ∈ B, heathBrownBoundedPositiveCoefficient c q (m, n) *
          Complex.exp (((2 * Real.pi *
            (t * heathBrownPositiveProductFrequency (m, n)) : ℝ) : ℂ) * Complex.I) :=
      Finset.sum_product A B _
    _ = heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t := by
      rw [heathBrownBoundedSparseFactor, heathBrownDenseFactor, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [heathBrownBoundedPositiveCoefficient, heathBrown_bounded_product_phase]
      ring

private theorem heathBrown_bounded_frequency_close_iff (p r : PNat × PNat)
    (T : Set.Ioi (0 : ℝ)) :
    |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r| <
        1 / (2 * Real.pi * (T : ℝ)) ↔
      |Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ) -
          Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)| < ((T : ℝ))⁻¹ := by
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  have hleft :
      |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r| =
        |Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ) -
          Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)| / (2 * Real.pi) := by
    rw [heathBrownPositiveProductFrequency, heathBrownProductFrequency,
      heathBrownPositiveProductFrequency, heathBrownProductFrequency]
    rw [show -Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ) / (2 * Real.pi) -
          -Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ) / (2 * Real.pi) =
        -(Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ) -
          Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)) / (2 * Real.pi) by ring,
      abs_div, abs_neg, abs_of_pos hden]
  have hright : 1 / (2 * Real.pi * (T : ℝ)) = ((T : ℝ))⁻¹ / (2 * Real.pi) := by
    field_simp
  rw [hleft, hright, div_lt_div_iff₀ hden hden]
  constructor <;> intro h <;> nlinarith [hden]

private theorem finiteFrequencyCollisionWeight_heathBrownBounded_le
    (A B : Finset PNat) (c : ℕ → ℂ) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hc : ∀ m ∈ A, ‖c (m : ℕ)‖ ≤ 1) :
    finiteFrequencyCollisionWeight (heathBrownBoundedPositiveCoefficient c q)
        (A.product B) heathBrownPositiveProductFrequency
        (1 / (2 * Real.pi * (T : ℝ))) ≤
      heathBrownPositiveWeightedCollision A B q T := by
  rw [finiteFrequencyCollisionWeight, heathBrownPositiveWeightedCollision]
  refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun r hr => ?_
  have hpmem := (Finset.mem_product.mp hp).1
  have hrmem := (Finset.mem_product.mp hr).1
  have hpcoeff : ‖heathBrownBoundedPositiveCoefficient c q p‖ ≤
      (q (p.2 : ℕ) : ℝ) := by
    rw [heathBrownBoundedPositiveCoefficient, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (q (p.2 : ℕ)).property.1]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hc p.1 hpmem) (q (p.2 : ℕ)).property.1
  have hrcoeff : ‖heathBrownBoundedPositiveCoefficient c q r‖ ≤
      (q (r.2 : ℕ) : ℝ) := by
    rw [heathBrownBoundedPositiveCoefficient, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (q (r.2 : ℕ)).property.1]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hc r.1 hrmem) (q (r.2 : ℕ)).property.1
  by_cases hclose :
      |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r| <
        1 / (2 * Real.pi * (T : ℝ))
  · rw [if_pos hclose,
      if_pos ((heathBrown_bounded_frequency_close_iff p r T).mp hclose)]
    exact mul_le_mul hpcoeff hrcoeff (norm_nonneg _)
      (q (p.2 : ℕ)).property.1
  · rw [if_neg hclose,
      if_neg (mt (heathBrown_bounded_frequency_close_iff p r T).mpr hclose)]

/-- Finite-window sparse mean value for arbitrary coefficients bounded by one. -/
theorem integral_Icc_normSq_heathBrownBounded_factors_le_weightedCollision
    (A B : Finset PNat) (c : ℕ → ℂ) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hc : ∀ m ∈ A, ‖c (m : ℕ)‖ ≤ 1) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) * heathBrownPositiveWeightedCollision A B q T := by
  have hdelta : (0 : ℝ) < 1 / (2 * Real.pi * (T : ℝ)) := by
    exact one_div_pos.mpr (mul_pos (by positivity) T.property)
  have hscale : 2 * Real.pi * (1 / (2 * Real.pi * (T : ℝ))) * (T : ℝ) ≤ 1 := by
    have hTpos : (0 : ℝ) < (T : ℝ) := T.property
    field_simp
    exact le_rfl
  have hbase := integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
    (heathBrownBoundedPositiveCoefficient c q) (A.product B)
      heathBrownPositiveProductFrequency hdelta hscale
  have hpoly : ∀ t : ℝ,
      finiteFrequencyPoly (heathBrownBoundedPositiveCoefficient c q) (A.product B)
          heathBrownPositiveProductFrequency t =
        heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t :=
    finiteFrequencyPoly_heathBrownBounded_eq_mul A B c q
  have hbase' :
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
        (5 / (4 * (1 / (2 * Real.pi * (T : ℝ))))) *
          finiteFrequencyCollisionWeight (heathBrownBoundedPositiveCoefficient c q)
            (A.product B) heathBrownPositiveProductFrequency
            (1 / (2 * Real.pi * (T : ℝ))) := by
    simpa only [hpoly] using hbase
  calc
    _ ≤ (5 / (4 * (1 / (2 * Real.pi * (T : ℝ))))) *
        heathBrownPositiveWeightedCollision A B q T :=
      hbase'.trans (mul_le_mul_of_nonneg_left
        (finiteFrequencyCollisionWeight_heathBrownBounded_le A B c q T hc) (by positivity))
    _ = (5 * Real.pi / 2) * (T : ℝ) *
        heathBrownPositiveWeightedCollision A B q T := by
      field_simp
      ring

/-- The bounded-coefficient collision mass never exceeds the square of the full product support. -/
theorem heathBrownPositiveWeightedCollision_le_cardProduct_sq
    (A B : Finset PNat) (q : ℕ → Set.Icc (0 : ℝ) 1) (T : Set.Ioi (0 : ℝ)) :
    heathBrownPositiveWeightedCollision A B q T ≤
      ((A.card : ℝ) * (B.card : ℝ)) ^ 2 := by
  have hsubset : heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹) ⊆
      (A.product B).product (A.product B) := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  calc
    heathBrownPositiveWeightedCollision A B q T ≤
        ((heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹)).card : ℝ) :=
      heathBrownPositiveWeightedCollision_le_card_strictCollision A B q T
    _ ≤ (((A.product B).product (A.product B)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ = ((A.card : ℝ) * (B.card : ℝ)) ^ 2 := by
      simp [pow_two]

/-- Heath--Brown Theorem 4(iii) with arbitrary complex sparse coefficients of modulus at most
one.  The explicit constant is enlarged only by the unconditional collision-reversal factor. -/
theorem integral_Icc_normSq_heathBrownBounded_factors_le_theoremFour_of_two_le
    (A B : Finset PNat) (c : ℕ → ℂ) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    (hc : ∀ m ∈ A, ‖c (m : ℕ)‖ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (25 * Real.pi / 4) *
        (95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
              (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) *
                (T : ℝ) ^ (3 / 4 : ℝ))) := by
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
  have hunit := integral_Icc_normSq_heathBrown_factors_le_theoremFour
    A (heathBrownPositiveInterval N hN) (fun _ => 1) heathBrownDenseUnitWeight
      T hT hA (N := N) (fun n hn => (Finset.mem_Icc.mp hn).2) heta
  have hunit' : J ≤
      95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
          ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
            (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) *
              (T : ℝ) ^ (3 / 4 : ℝ)) := by
    simpa only [J] using hunit
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
        (95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
              (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) *
                (T : ℝ) ^ (3 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hunit' (by positivity)

/-- Heath--Brown Theorem 4(iii) for every source height `T ≥ 1`.  The compact range `1 ≤ T < 2`
is discharged directly by the full product-support collision count. -/
theorem integral_Icc_normSq_heathBrownBounded_factors_le_theoremFour
    (A B : Finset PNat) (c : ℕ → ℂ) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    (hc : ∀ m ∈ A, ‖c (m : ℕ)‖ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (25 * Real.pi / 4) *
        (95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
              (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) *
                (T : ℝ) ^ (3 / 4 : ℝ))) := by
  by_cases htwo : 2 ≤ (T : ℝ)
  · exact integral_Icc_normSq_heathBrownBounded_factors_le_theoremFour_of_two_le
      A B c q T htwo hA hc hN hB heta
  · have hforward :=
      integral_Icc_normSq_heathBrownBounded_factors_le_weightedCollision A B c q T hc
    have hcollision := heathBrownPositiveWeightedCollision_le_cardProduct_sq A B q T
    have hBcard : (B.card : ℝ) ≤ (N : ℝ) :=
      cast_card_le_height_of_pnat_support B (Nat.cast_nonneg N)
        (fun n hn => by exact_mod_cast hB n hn)
    have hcard0 : 0 ≤ (A.card : ℝ) := by positivity
    have hBcard0 : 0 ≤ (B.card : ℝ) := by positivity
    have hN0 : 0 ≤ (N : ℝ) := by positivity
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
            (95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
      have hTlt : (T : ℝ) < 2 := lt_of_not_ge htwo
      have hpi : 0 < Real.pi := Real.pi_pos
      calc
        _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
            ((N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by gcongr
        _ ≤ (5 * Real.pi) * ((N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
          have hcoefT : (5 * Real.pi / 2) * (T : ℝ) ≤ 5 * Real.pi := by
            nlinarith
          exact mul_le_mul_of_nonneg_right hcoefT (by positivity)
        _ ≤ (25 * Real.pi / 4) *
            (95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by
          have hmass : 0 ≤ (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by positivity
          have hcoef : 5 * Real.pi ≤
              (25 * Real.pi / 4) * (95 * Real.pi / 2) := by
            nlinarith [Real.pi_gt_three]
          nlinarith
    calc
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2) ≤
        (5 * Real.pi / 2) * (T : ℝ) *
          heathBrownPositiveWeightedCollision A B q T := hforward
      _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
          ((A.card : ℝ) * (B.card : ℝ)) ^ 2 := by gcongr
      _ ≤ (25 * Real.pi / 4) *
          (95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := hdiag
      _ ≤ (25 * Real.pi / 4) *
          (95 * Real.pi / 2 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
            heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
              ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
                (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) *
                  (T : ℝ) ^ (3 / 4 : ℝ))) := by
        gcongr
        apply le_add_of_nonneg_right
        dsimp [heathBrownTheoremFourCoefficient,
          heathBrownTheoremFourUniversalCoefficient,
          heathBrownMeanSquareCoefficient]
        positivity

end

end RHTower.Sieve
