import GaloisForLFunctions.RHTower.Sieve.VinogradovBilinearHolder

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovRouteTMoment (s : ℕ) : ℕ :=
  vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s

def vinogradovRouteTMeanBoundExponent (s : ℕ) : ℕ :=
  2 * vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s -
      vinogradovRouteTOrder s * (vinogradovRouteTOrder s + 1) / 2 +
    (350 * s + 2)

theorem vinogradovRouteTMoment_ne_zero {s : ℕ} (hs : 1 ≤ s) :
    vinogradovRouteTMoment s ≠ 0 := by
  unfold vinogradovRouteTMoment vinogradovRouteTOrder
  exact mul_ne_zero (by omega) (Nat.ne_of_gt (vinogradovRouteTMomentSteps_pos hs))

theorem vinogradovRouteT_mean_value_bound_real
    {s N : ℕ} (hs : 1 ≤ s) (hN : N ≠ 0) :
    (Fintype.card (VinogradovDiagonalSolution N
        (vinogradovRouteTMoment s) (vinogradovRouteTOrder s)) : ℝ) ≤
      (vinogradovMeanConstant
          (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) : ℝ) *
        (N : ℝ) ^ vinogradovRouteTMeanBoundExponent s := by
  exact_mod_cast vinogradovRouteT_mean_value_bound hs hN

/-- Route-T specialization of the complete finite MV24.7 bridge.  Both
mean values have been replaced by the unconditional PNT-free C14 bound;
the only unsimplified factors are explicit powers and rational-coordinate
costs. -/
theorem norm_vinogradovRouteTBilinearSum_pow_le_rationalProduct
    {s X Y : ℕ} (hs : 1 ≤ s) (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin (vinogradovRouteTOrder s) → ℝ)
    (a q : Fin (vinogradovRouteTOrder s) → ℕ)
    (hq : ∀ j, 0 < q j) (hcop : ∀ j, Nat.Coprime (a j) (q j))
    (happrox : ∀ j,
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ (2 : ℕ)) :
    ‖vinogradovBilinearSum (X := X) (Y := Y) α‖ ^
        (4 * vinogradovRouteTMoment s ^ (2 : ℕ)) ≤
      (((X : ℝ) ^ (2 * vinogradovRouteTMoment s - 1)) ^
          (2 * vinogradovRouteTMoment s) *
        ((Y : ℝ) ^ (2 * vinogradovRouteTMoment s)) ^
          (2 * vinogradovRouteTMoment s - 1)) *
        (((vinogradovMeanConstant
            (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) : ℝ) *
              (Y : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
          ((vinogradovMeanConstant
            (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) : ℝ) *
              (X : ℝ) ^ vinogradovRouteTMeanBoundExponent s)) *
            ∏ j : Fin (vinogradovRouteTOrder s),
              vinogradovRationalCoordinateCost X Y
                (vinogradovRouteTMoment s) (q j) j := by
  let k := vinogradovRouteTOrder s
  let b := vinogradovRouteTMoment s
  have hbase := norm_vinogradovBilinearSum_pow_le_rationalProduct
    (b := b) (k := k) (vinogradovRouteTMoment_ne_zero hs) hX hY
    α a q hq hcop happrox
  have hcard :
      (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) =
        (Y : ℝ) ^ (2 * b) := by
    norm_cast
    exact card_vinogradovTuplePair Y b
  rw [hcard] at hbase
  have hmeanY := vinogradovRouteT_mean_value_bound_real hs hY
  have hmeanX := vinogradovRouteT_mean_value_bound_real hs hX
  have hmeanProduct :
      ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
        Fintype.card (VinogradovDiagonalSolution X b k)) ≤
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
            (Y : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
          ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
            (X : ℝ) ^ vinogradovRouteTMeanBoundExponent s) := by
    exact mul_le_mul hmeanY hmeanX (by positivity) (by positivity)
  have hcost : 0 ≤ ∏ j : Fin k,
      vinogradovRationalCoordinateCost X Y b (q j) j :=
    Finset.prod_nonneg fun j _ =>
      vinogradovRationalCoordinateCost_nonneg X Y b (q j) j
  calc
    _ ≤ ((((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        ((Y : ℝ) ^ (2 * b)) ^ (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k))) *
            ∏ j : Fin k,
              vinogradovRationalCoordinateCost X Y b (q j) j := by
      simpa [k, b] using hbase
    _ ≤ ((((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        ((Y : ℝ) ^ (2 * b)) ^ (2 * b - 1)) *
        (((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
            (Y : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
          ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
            (X : ℝ) ^ vinogradovRouteTMeanBoundExponent s))) *
            ∏ j : Fin k,
              vinogradovRationalCoordinateCost X Y b (q j) j := by
      apply mul_le_mul_of_nonneg_right _ hcost
      apply mul_le_mul_of_nonneg_left hmeanProduct
      positivity
    _ = (((X : ℝ) ^ (2 * vinogradovRouteTMoment s - 1)) ^
          (2 * vinogradovRouteTMoment s) *
        ((Y : ℝ) ^ (2 * vinogradovRouteTMoment s)) ^
          (2 * vinogradovRouteTMoment s - 1)) *
        (((vinogradovMeanConstant
            (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) : ℝ) *
              (Y : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
          ((vinogradovMeanConstant
            (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) : ℝ) *
              (X : ℝ) ^ vinogradovRouteTMeanBoundExponent s)) *
            ∏ j : Fin (vinogradovRouteTOrder s),
              vinogradovRationalCoordinateCost X Y
                (vinogradovRouteTMoment s) (q j) j := by rfl

end

end RHTower.Sieve
