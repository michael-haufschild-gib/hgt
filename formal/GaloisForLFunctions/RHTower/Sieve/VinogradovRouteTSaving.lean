import GaloisForLFunctions.RHTower.Sieve.VinogradovUsefulCoordinates
import GaloisForLFunctions.RHTower.Sieve.VinogradovRouteTBilinear

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovRouteTUsefulReserve (u : ℕ) : ℕ :=
  200 * u ^ 2 - (2800 * u + 4)

def vinogradovRouteTMomentConstant (u : ℕ) : ℕ :=
  vinogradovMeanConstant
      (vinogradovRouteTOrder (4 * u))
      (vinogradovRouteTMomentSteps (4 * u)) ^ 2 *
    (24 * vinogradovRouteTMoment (4 * u) ^ 2) ^
      vinogradovRouteTOrder (4 * u)

def vinogradovRouteTMomentSaving (u : ℕ) : ℕ :=
  100 * u ^ 2 - 1

def vinogradovRouteTPowerSavingExponent (u : ℕ) : ℝ :=
  (vinogradovRouteTMomentSaving u : ℝ) /
    (4 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2)

private theorem pow_add_mul_inv_pow_add
    {x : ℝ} (hx : x ≠ 0) (a b c : ℕ) :
    x ^ (a + b) * (x ^ (b + c))⁻¹ = x ^ a * (x ^ c)⁻¹ := by
  rw [pow_add, pow_add, mul_inv_rev]
  have hxb : x ^ b ≠ 0 := pow_ne_zero _ hx
  calc
    x ^ a * x ^ b * ((x ^ c)⁻¹ * (x ^ b)⁻¹) =
        x ^ a * (x ^ c)⁻¹ * (x ^ b * (x ^ b)⁻¹) := by ring
    _ = x ^ a * (x ^ c)⁻¹ := by rw [mul_inv_cancel₀ hxb, mul_one]

private theorem le_rpow_inv_nat_of_pow_le
    {x y : ℝ} {n : ℕ} (hn : n ≠ 0) (hy : 0 ≤ y)
    (hxy : x ^ n ≤ y) :
    x ≤ y ^ ((n : ℝ)⁻¹) := by
  apply le_of_pow_le_pow_left₀ hn (Real.rpow_nonneg hy _)
  rw [Real.rpow_inv_natCast_pow hy hn]
  exact hxy

theorem vinogradovRouteTUsefulReserve_ge
    {u : ℕ} (hu : 29 ≤ u) :
    100 * u ^ 2 ≤ vinogradovRouteTUsefulReserve u := by
  unfold vinogradovRouteTUsefulReserve
  have hcost : 2800 * u + 4 ≤ 100 * u ^ 2 := by nlinarith
  omega

theorem routeT_two_meanExponent_add_degree
    {u : ℕ} (hu : 1 ≤ u) :
    2 * vinogradovRouteTMeanBoundExponent (4 * u) +
        vinogradovRouteTOrder (4 * u) *
          (vinogradovRouteTOrder (4 * u) + 1) =
      4 * vinogradovRouteTMoment (4 * u) + (2800 * u + 4) := by
  let k := vinogradovRouteTOrder (4 * u)
  let r := vinogradovRouteTMomentSteps (4 * u)
  let b := vinogradovRouteTMoment (4 * u)
  let h := k * (k + 1) / 2
  have hkpos : 1 ≤ k := by unfold k vinogradovRouteTOrder; omega
  have hrpos : 1 ≤ r := vinogradovRouteTMomentSteps_pos (by omega)
  have hkr : k + 1 ≤ 2 * r := by
    have hbudget : 400 * u + 1 + 800 * u ≤ 40000 * u ^ 2 := by
      nlinarith
    have hfirst : 400 * u + 1 ≤ 40000 * u ^ 2 - 800 * u :=
      Nat.le_sub_of_add_le hbudget
    unfold k r vinogradovRouteTOrder vinogradovRouteTMomentSteps
    norm_num [mul_pow]
    omega
  have hh_le : h ≤ 2 * b := by
    calc
      h ≤ k * (k + 1) := Nat.div_le_self _ _
      _ ≤ k * (2 * r) := Nat.mul_le_mul_left k hkr
      _ = 2 * b := by unfold b vinogradovRouteTMoment; ring
  have heven : 2 ∣ k * (k + 1) := by
    unfold k vinogradovRouteTOrder
    refine dvd_mul_of_dvd_left ?_ _
    omega
  have hdouble : 2 * h = k * (k + 1) := by
    unfold h
    exact Nat.mul_div_cancel' heven
  have hE : vinogradovRouteTMeanBoundExponent (4 * u) =
      2 * b - h + (1400 * u + 2) := by
    unfold vinogradovRouteTMeanBoundExponent b vinogradovRouteTMoment h k
    ring_nf
  rw [hE]
  change 2 * (2 * b - h + (1400 * u + 2)) + k * (k + 1) =
    4 * b + (2800 * u + 4)
  omega

theorem routeT_total_phase_exponent
    {u : ℕ} (hu : 1 ≤ u) :
    2 * ((2 * vinogradovRouteTMoment (4 * u) - 1) *
          (2 * vinogradovRouteTMoment (4 * u))) +
        2 * vinogradovRouteTMeanBoundExponent (4 * u) +
        vinogradovRouteTOrder (4 * u) *
          (vinogradovRouteTOrder (4 * u) + 1) =
      8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4) := by
  let b := vinogradovRouteTMoment (4 * u)
  have hb : 1 ≤ b := by
    exact Nat.one_le_iff_ne_zero.mpr
      (vinogradovRouteTMoment_ne_zero (by omega))
  have hmean := routeT_two_meanExponent_add_degree hu
  change 2 * vinogradovRouteTMeanBoundExponent (4 * u) +
      vinogradovRouteTOrder (4 * u) *
        (vinogradovRouteTOrder (4 * u) + 1) =
    4 * b + (2800 * u + 4) at hmean
  change 2 * ((2 * b - 1) * (2 * b)) +
      2 * vinogradovRouteTMeanBoundExponent (4 * u) +
      vinogradovRouteTOrder (4 * u) *
        (vinogradovRouteTOrder (4 * u) + 1) =
    8 * b ^ 2 + (2800 * u + 4)
  have hpred : 2 * b - 1 + 1 = 2 * b := by omega
  nlinarith

/-- Complete Route-T bilinear moment bound after useful-coordinate
selection.  Every factor is explicit: outer Hölder cardinalities, two
PNT-free mean-value bounds, natural coordinate mass, and the aggregate
`Q^(-200u²)` rational reserve. -/
theorem norm_vinogradovRouteTUsefulBilinearSum_pow_le
    {u Q : ℕ} (hu : 1 ≤ u) (hQ : 1 ≤ Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        (Q ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovBilinearSum (X := Q) (Y := Q) α‖ ^
        (4 * vinogradovRouteTMoment (4 * u) ^ 2) ≤
      ((((Q : ℝ) ^ (2 * vinogradovRouteTMoment (4 * u) - 1)) ^
          (2 * vinogradovRouteTMoment (4 * u)) *
        (((Q : ℝ) ^ (2 * vinogradovRouteTMoment (4 * u))) ^
          (2 * vinogradovRouteTMoment (4 * u) - 1))) *
        (((vinogradovMeanConstant
            (vinogradovRouteTOrder (4 * u))
            (vinogradovRouteTMomentSteps (4 * u)) : ℝ) *
              (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent (4 * u)) *
          ((vinogradovMeanConstant
            (vinogradovRouteTOrder (4 * u))
            (vinogradovRouteTMomentSteps (4 * u)) : ℝ) *
              (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent (4 * u)))) *
        ((24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
            (vinogradovRouteTOrder (4 * u)) *
          (Q : ℝ) ^
            (vinogradovRouteTOrder (4 * u) *
              (vinogradovRouteTOrder (4 * u) + 1)) *
            ((Q : ℝ) ^ (200 * u ^ 2))⁻¹) := by
  let s : ℕ := 4 * u
  let k : ℕ := vinogradovRouteTOrder s
  let b : ℕ := vinogradovRouteTMoment s
  let U : Fin k → Prop := vinogradovUsefulCoordinate u
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hb : b ≠ 0 := vinogradovRouteTMoment_ne_zero hs
  have hQ0 : Q ≠ 0 := Nat.ne_of_gt (by omega)
  have hbase := norm_vinogradovBilinearSum_pow_le_mixedProduct
    (b := b) (k := k) hb hQ0 hQ0 α U a q hq hcop happrox
  have hcard :
      (Fintype.card ((Fin b → Fin Q) × (Fin b → Fin Q)) : ℝ) =
        (Q : ℝ) ^ (2 * b) := by
    norm_cast
    exact card_vinogradovTuplePair Q b
  rw [hcard] at hbase
  have hmean := vinogradovRouteT_mean_value_bound_real hs hQ0
  have hmeanProduct :
      ((Fintype.card (VinogradovDiagonalSolution Q b k) : ℝ) *
        Fintype.card (VinogradovDiagonalSolution Q b k)) ≤
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent s) := by
    exact mul_le_mul hmean hmean (by positivity) (by positivity)
  have hmixed := prod_vinogradovMixedCoordinateCost_le_envelope
    (Q := Q) (b := b) hQ (by
      have := vinogradovRouteTMoment_ne_zero hs
      omega) U q hRq hqR habsorb
  have henvelope := prod_vinogradovUsefulCoordinateEnvelope_le
    (Q := Q) (b := b) (u := u) hQ
  have hcoord :
      (∏ j : Fin k, vinogradovMixedCoordinateCost U Q Q b q j) ≤
        (24 * (b : ℝ) ^ 2) ^ k *
          (Q : ℝ) ^ (k * (k + 1)) * ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ :=
    hmixed.trans (by simpa [s, k, b, U] using henvelope)
  have houter : 0 ≤
      ((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1)) := by positivity
  have hmean0 : 0 ≤
      ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
        (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
      ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
        (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent s) := by positivity
  calc
    _ ≤ (((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
        ((Fintype.card (VinogradovDiagonalSolution Q b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution Q b k)) *
        ∏ j : Fin k, vinogradovMixedCoordinateCost U Q Q b q j := by
      simpa [s, k, b, U] using hbase
    _ ≤ (((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
        (((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent s)) *
        ∏ j : Fin k, vinogradovMixedCoordinateCost U Q Q b q j := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmeanProduct houter)
        (Finset.prod_nonneg fun j _ =>
          vinogradovMixedCoordinateCost_nonneg U Q Q b q j)
    _ ≤ (((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
        (((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent s)) *
        ((24 * (b : ℝ) ^ 2) ^ k *
          (Q : ℝ) ^ (k * (k + 1)) * ((Q : ℝ) ^ (200 * u ^ 2))⁻¹) := by
      exact mul_le_mul_of_nonneg_left hcoord (mul_nonneg houter hmean0)
    _ = ((((Q : ℝ) ^ (2 * vinogradovRouteTMoment (4 * u) - 1)) ^
          (2 * vinogradovRouteTMoment (4 * u)) *
        (((Q : ℝ) ^ (2 * vinogradovRouteTMoment (4 * u))) ^
          (2 * vinogradovRouteTMoment (4 * u) - 1))) *
        (((vinogradovMeanConstant
            (vinogradovRouteTOrder (4 * u))
            (vinogradovRouteTMomentSteps (4 * u)) : ℝ) *
              (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent (4 * u)) *
          ((vinogradovMeanConstant
            (vinogradovRouteTOrder (4 * u))
            (vinogradovRouteTMomentSteps (4 * u)) : ℝ) *
              (Q : ℝ) ^ vinogradovRouteTMeanBoundExponent (4 * u)))) *
        ((24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
            (vinogradovRouteTOrder (4 * u)) *
          (Q : ℝ) ^
            (vinogradovRouteTOrder (4 * u) *
              (vinogradovRouteTOrder (4 * u) + 1)) *
            ((Q : ℝ) ^ (200 * u ^ 2))⁻¹) := by rfl

/-- The complete useful-coordinate estimate with all powers of `Q`
collected.  The positive loss beyond the critical `8b²` moment scale is
exactly `2800u+4`; the rational coordinates contribute `200u²` in the
opposite direction. -/
theorem norm_vinogradovRouteTUsefulBilinearSum_pow_le_collected
    {u Q : ℕ} (hu : 1 ≤ u) (hQ : 1 ≤ Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        (Q ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovBilinearSum (X := Q) (Y := Q) α‖ ^
        (4 * vinogradovRouteTMoment (4 * u) ^ 2) ≤
      (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        (Q : ℝ) ^
          (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
        ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ := by
  let b := vinogradovRouteTMoment (4 * u)
  let k := vinogradovRouteTOrder (4 * u)
  let E := vinogradovRouteTMeanBoundExponent (4 * u)
  let D := vinogradovMeanConstant k (vinogradovRouteTMomentSteps (4 * u))
  let C : ℝ := 24 * (b : ℝ) ^ 2
  have hraw := norm_vinogradovRouteTUsefulBilinearSum_pow_le
    hu hQ α a q hq hcop happrox hRq hqR habsorb
  have hphase :
      2 * ((2 * b - 1) * (2 * b)) + 2 * E + k * (k + 1) =
        8 * b ^ 2 + (2800 * u + 4) := by
    simpa [b, k, E] using routeT_total_phase_exponent hu
  have hexponent :
      (2 * b - 1) * (2 * b) + (2 * b) * (2 * b - 1) + E + E +
          k * (k + 1) =
        8 * b ^ 2 + (2800 * u + 4) := by
    calc
      (2 * b - 1) * (2 * b) + (2 * b) * (2 * b - 1) + E + E +
            k * (k + 1) =
          2 * ((2 * b - 1) * (2 * b)) + 2 * E + k * (k + 1) := by
            ring
      _ = 8 * b ^ 2 + (2800 * u + 4) := hphase
  have hQphase :
      ((((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
          (Q : ℝ) ^ E * (Q : ℝ) ^ E) *
          (Q : ℝ) ^ (k * (k + 1)) =
        (Q : ℝ) ^ (8 * b ^ 2 + (2800 * u + 4)) := by
    rw [← pow_mul, ← pow_mul]
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    rw [hexponent]
  calc
    _ ≤ ((((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
        (((D : ℝ) * (Q : ℝ) ^ E) * ((D : ℝ) * (Q : ℝ) ^ E))) *
        (C ^ k * (Q : ℝ) ^ (k * (k + 1)) *
          ((Q : ℝ) ^ (200 * u ^ 2))⁻¹) := by
      simpa [b, k, E, D, C] using hraw
    _ = (D : ℝ) ^ 2 * C ^ k *
        (((((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
          (Q : ℝ) ^ E * (Q : ℝ) ^ E) *
          (Q : ℝ) ^ (k * (k + 1))) *
        ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ := by ring
    _ = (D : ℝ) ^ 2 * C ^ k *
        (Q : ℝ) ^ (8 * b ^ 2 + (2800 * u + 4)) *
        ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ := by rw [hQphase]
    _ = (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        (Q : ℝ) ^
          (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
        ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ := by rfl

/-- Net Route-T moment saving after cancelling the complete finite
mean-value loss against the useful rational-coordinate reserve. -/
theorem norm_vinogradovRouteTUsefulBilinearSum_pow_le_reserve
    {u Q : ℕ} (hu : 29 ≤ u) (hQ : 1 ≤ Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        (Q ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovBilinearSum (X := Q) (Y := Q) α‖ ^
        (4 * vinogradovRouteTMoment (4 * u) ^ 2) ≤
      (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
        ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ := by
  have hu1 : 1 ≤ u := by omega
  have hraw := norm_vinogradovRouteTUsefulBilinearSum_pow_le_collected
    hu1 hQ α a q hq hcop happrox hRq hqR habsorb
  have hcost : 2800 * u + 4 ≤ 200 * u ^ 2 := by nlinarith
  have hsplit :
      (2800 * u + 4) + vinogradovRouteTUsefulReserve u = 200 * u ^ 2 := by
    unfold vinogradovRouteTUsefulReserve
    omega
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  have hcancel :
      (Q : ℝ) ^
          (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
          ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ =
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ := by
    rw [← hsplit]
    exact pow_add_mul_inv_pow_add hQ0 _ _ _
  calc
    _ ≤ (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        (Q : ℝ) ^
          (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
        ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ := hraw
    _ = (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
        ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ := by
      rw [mul_assoc, mul_assoc, hcancel]
      ring

/-- Explicit-threshold form of the Route-T power saving.  Once `Q`
dominates the fixed moment constant, one power of `Q` absorbs every
finite combinatorial factor, leaving `100u²-1` powers of saving. -/
theorem norm_vinogradovRouteTUsefulBilinearSum_pow_le_powerSaving
    {u Q : ℕ} (hu : 29 ≤ u)
    (hQ : vinogradovRouteTMomentConstant u ≤ Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        (Q ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovBilinearSum (X := Q) (Y := Q) α‖ ^
        (4 * vinogradovRouteTMoment (4 * u) ^ 2) ≤
      (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
        ((Q : ℝ) ^ vinogradovRouteTMomentSaving u)⁻¹ := by
  have hconstant_pos : 1 ≤ vinogradovRouteTMomentConstant u := by
    unfold vinogradovRouteTMomentConstant
    have hmean : 1 ≤ vinogradovMeanConstant
        (vinogradovRouteTOrder (4 * u))
        (vinogradovRouteTMomentSteps (4 * u)) := by
      generalize vinogradovRouteTMomentSteps (4 * u) = r
      cases r with
      | zero => simp [vinogradovMeanConstant]
      | succ r => simp only [vinogradovMeanConstant]; omega
    have hb : 1 ≤ vinogradovRouteTMoment (4 * u) :=
      Nat.one_le_iff_ne_zero.mpr
        (vinogradovRouteTMoment_ne_zero (by omega))
    have hbase : 1 ≤ 24 * vinogradovRouteTMoment (4 * u) ^ 2 := by
      have hb0 : 0 < vinogradovRouteTMoment (4 * u) := by omega
      exact Nat.mul_pos (by omega) (pow_pos hb0 2)
    exact Nat.mul_pos (pow_pos (by omega) 2)
      (pow_pos (by omega) (vinogradovRouteTOrder (4 * u)))
  have hQ1 : 1 ≤ Q := hconstant_pos.trans hQ
  have hraw := norm_vinogradovRouteTUsefulBilinearSum_pow_le_reserve
    hu hQ1 α a q hq hcop happrox hRq hqR habsorb
  have hconstant_cast :
      (vinogradovRouteTMomentConstant u : ℝ) =
        (vinogradovMeanConstant
            (vinogradovRouteTOrder (4 * u))
            (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
          (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
            vinogradovRouteTOrder (4 * u) := by
    simp [vinogradovRouteTMomentConstant, Nat.cast_mul, Nat.cast_pow]
  have hconstant_le : (vinogradovRouteTMomentConstant u : ℝ) ≤ Q := by
    exact_mod_cast hQ
  have hreserve := vinogradovRouteTUsefulReserve_ge hu
  have hpow :
      (Q : ℝ) ^ (100 * u ^ 2) ≤
        (Q : ℝ) ^ vinogradovRouteTUsefulReserve u :=
    pow_le_pow_right₀ (by exact_mod_cast hQ1) hreserve
  have hinv :
      ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ ≤
        ((Q : ℝ) ^ (100 * u ^ 2))⁻¹ :=
    inv_anti₀ (by positivity) hpow
  have hsplit :
      1 + vinogradovRouteTMomentSaving u = 100 * u ^ 2 := by
    unfold vinogradovRouteTMomentSaving
    have : 1 ≤ 100 * u ^ 2 := by nlinarith
    omega
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  have hcancel :
      (Q : ℝ) * (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ (100 * u ^ 2))⁻¹ =
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ vinogradovRouteTMomentSaving u)⁻¹ := by
    calc
      (Q : ℝ) * (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
            ((Q : ℝ) ^ (100 * u ^ 2))⁻¹ =
          (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2 + 1) *
            ((Q : ℝ) ^ (1 + vinogradovRouteTMomentSaving u))⁻¹ := by
              rw [hsplit, pow_add, pow_one]
              ring
      _ = (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
            ((Q : ℝ) ^ vinogradovRouteTMomentSaving u)⁻¹ :=
          pow_add_mul_inv_pow_add hQ0 _ _ _
  calc
    _ ≤ (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
        ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ := hraw
    _ = (vinogradovRouteTMomentConstant u : ℝ) *
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
        ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ := by
      rw [hconstant_cast]
    _ ≤ (Q : ℝ) *
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
        ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant_le (by positivity))
        (by positivity)
    _ ≤ (Q : ℝ) *
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
        ((Q : ℝ) ^ (100 * u ^ 2))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
        ((Q : ℝ) ^ vinogradovRouteTMomentSaving u)⁻¹ := hcancel

/-- Pointwise Route-T bilinear estimate obtained by taking the exact
`4b²`-th root.  Its exponent is strictly below the trivial exponent
`2` by the explicit positive amount
`(100u²-1)/(4b²)`. -/
theorem norm_vinogradovRouteTUsefulBilinearSum_le_rpow
    {u Q : ℕ} (hu : 29 ≤ u)
    (hQ : vinogradovRouteTMomentConstant u ≤ Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        (Q ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovBilinearSum (X := Q) (Y := Q) α‖ ≤
      (Q : ℝ) ^ (2 - vinogradovRouteTPowerSavingExponent u) := by
  let b := vinogradovRouteTMoment (4 * u)
  let M := 4 * b ^ 2
  let S := vinogradovRouteTMomentSaving u
  have hb : b ≠ 0 := by
    exact vinogradovRouteTMoment_ne_zero (by omega)
  have hM : M ≠ 0 := by unfold M; positivity
  have hmoment :=
    norm_vinogradovRouteTUsefulBilinearSum_pow_le_powerSaving
      hu hQ α a q hq hcop happrox hRq hqR habsorb
  have hQ1 : 1 ≤ Q := by
    have hconstant_pos : 1 ≤ vinogradovRouteTMomentConstant u := by
      unfold vinogradovRouteTMomentConstant
      have hmean : 1 ≤ vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) := by
        generalize vinogradovRouteTMomentSteps (4 * u) = r
        cases r with
        | zero => simp [vinogradovMeanConstant]
        | succ r => simp only [vinogradovMeanConstant]; omega
      have hbase : 1 ≤ 24 * vinogradovRouteTMoment (4 * u) ^ 2 := by
        exact Nat.mul_pos (by omega) (pow_pos (Nat.pos_of_ne_zero hb) 2)
      exact Nat.mul_pos (pow_pos (by omega) 2)
        (pow_pos (by omega) (vinogradovRouteTOrder (4 * u)))
    exact hconstant_pos.trans hQ
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hy : 0 ≤
      (Q : ℝ) ^ (8 * b ^ 2) * ((Q : ℝ) ^ S)⁻¹ := by positivity
  have hroot :
      ‖vinogradovBilinearSum (X := Q) (Y := Q) α‖ ≤
        ((Q : ℝ) ^ (8 * b ^ 2) * ((Q : ℝ) ^ S)⁻¹) ^
          ((M : ℝ)⁻¹) := by
    apply le_rpow_inv_nat_of_pow_le hM hy
    simpa [b, M, S] using hmoment
  have hexponent :
      ((((8 * b ^ 2 : ℕ) : ℝ) + -(S : ℝ)) * (M : ℝ)⁻¹) =
        2 - vinogradovRouteTPowerSavingExponent u := by
    unfold vinogradovRouteTPowerSavingExponent
    change ((((8 * b ^ 2 : ℕ) : ℝ) + -(S : ℝ)) * (M : ℝ)⁻¹) =
      2 - (S : ℝ) / (4 * (b : ℝ) ^ 2)
    simp only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    field_simp [hbR]
    ring
  have hroot_eq :
      ((Q : ℝ) ^ (8 * b ^ 2) * ((Q : ℝ) ^ S)⁻¹) ^ ((M : ℝ)⁻¹) =
        (Q : ℝ) ^ (2 - vinogradovRouteTPowerSavingExponent u) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_neg hQpos.le, ← Real.rpow_add hQpos]
    rw [← Real.rpow_mul hQpos.le, hexponent]
  rw [← hroot_eq]
  exact hroot

/-- Generic constant absorption for any object satisfying the collected
Route-T moment inequality.  This separates analytic production of the
moment bound from its exact arithmetic endgame. -/
theorem routeTMoment_powerSaving_of_collected
    {u Q : ℕ} {z : ℂ} (hu : 29 ≤ u)
    (hQ : vinogradovRouteTMomentConstant u ≤ Q)
    (hcollected :
      ‖z‖ ^ (4 * vinogradovRouteTMoment (4 * u) ^ 2) ≤
        (vinogradovMeanConstant
            (vinogradovRouteTOrder (4 * u))
            (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
          (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
            vinogradovRouteTOrder (4 * u) *
          (Q : ℝ) ^
            (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
          ((Q : ℝ) ^ (200 * u ^ 2))⁻¹) :
      ‖z‖ ^ (4 * vinogradovRouteTMoment (4 * u) ^ 2) ≤
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ vinogradovRouteTMomentSaving u)⁻¹ := by
  have hconstant_pos : 1 ≤ vinogradovRouteTMomentConstant u := by
    unfold vinogradovRouteTMomentConstant
    have hmean : 1 ≤ vinogradovMeanConstant
        (vinogradovRouteTOrder (4 * u))
        (vinogradovRouteTMomentSteps (4 * u)) := by
      generalize vinogradovRouteTMomentSteps (4 * u) = r
      cases r with
      | zero => simp [vinogradovMeanConstant]
      | succ r => simp only [vinogradovMeanConstant]; omega
    have hb : 1 ≤ vinogradovRouteTMoment (4 * u) :=
      Nat.one_le_iff_ne_zero.mpr
        (vinogradovRouteTMoment_ne_zero (by omega))
    have hbase : 1 ≤ 24 * vinogradovRouteTMoment (4 * u) ^ 2 := by
      exact Nat.mul_pos (by omega) (pow_pos (by omega) 2)
    exact Nat.mul_pos (pow_pos (by omega) 2)
      (pow_pos (by omega) (vinogradovRouteTOrder (4 * u)))
  have hQ1 : 1 ≤ Q := hconstant_pos.trans hQ
  have hcost : 2800 * u + 4 ≤ 200 * u ^ 2 := by nlinarith
  have hsplitReserve :
      (2800 * u + 4) + vinogradovRouteTUsefulReserve u = 200 * u ^ 2 := by
    unfold vinogradovRouteTUsefulReserve
    omega
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  have hreserveCancel :
      (Q : ℝ) ^
          (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
          ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ =
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ := by
    rw [← hsplitReserve]
    exact pow_add_mul_inv_pow_add hQ0 _ _ _
  have hconstant_cast :
      (vinogradovRouteTMomentConstant u : ℝ) =
        (vinogradovMeanConstant
            (vinogradovRouteTOrder (4 * u))
            (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
          (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
            vinogradovRouteTOrder (4 * u) := by
    simp [vinogradovRouteTMomentConstant, Nat.cast_mul, Nat.cast_pow]
  have hconstant_le : (vinogradovRouteTMomentConstant u : ℝ) ≤ Q := by
    exact_mod_cast hQ
  have hreserve := vinogradovRouteTUsefulReserve_ge hu
  have hpow :
      (Q : ℝ) ^ (100 * u ^ 2) ≤
        (Q : ℝ) ^ vinogradovRouteTUsefulReserve u :=
    pow_le_pow_right₀ (by exact_mod_cast hQ1) hreserve
  have hinv :
      ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ ≤
        ((Q : ℝ) ^ (100 * u ^ 2))⁻¹ :=
    inv_anti₀ (by positivity) hpow
  have hsplitSaving :
      1 + vinogradovRouteTMomentSaving u = 100 * u ^ 2 := by
    unfold vinogradovRouteTMomentSaving
    have : 1 ≤ 100 * u ^ 2 := by nlinarith
    omega
  have hsavingCancel :
      (Q : ℝ) * (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ (100 * u ^ 2))⁻¹ =
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ vinogradovRouteTMomentSaving u)⁻¹ := by
    calc
      _ = (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2 + 1) *
          ((Q : ℝ) ^ (1 + vinogradovRouteTMomentSaving u))⁻¹ := by
            rw [hsplitSaving, pow_add, pow_one]
            ring
      _ = _ := pow_add_mul_inv_pow_add hQ0 _ _ _
  calc
    _ ≤ (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        (Q : ℝ) ^
          (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
        ((Q : ℝ) ^ (200 * u ^ 2))⁻¹ := hcollected
    _ = (vinogradovRouteTMomentConstant u : ℝ) *
        ((Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹) := by
      rw [hconstant_cast, hreserveCancel]
      ring
    _ ≤ (Q : ℝ) *
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ vinogradovRouteTUsefulReserve u)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hconstant_le (by positivity)
    _ ≤ (Q : ℝ) *
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ (100 * u ^ 2))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := hsavingCancel

/-- Generic exact-root extraction from the Route-T saved moment. -/
theorem norm_le_rpow_of_routeTMomentSaving
    {u Q : ℕ} {z : ℂ} (hu : 29 ≤ u) (hQ : 1 ≤ Q)
    (hmoment :
      ‖z‖ ^ (4 * vinogradovRouteTMoment (4 * u) ^ 2) ≤
        (Q : ℝ) ^ (8 * vinogradovRouteTMoment (4 * u) ^ 2) *
          ((Q : ℝ) ^ vinogradovRouteTMomentSaving u)⁻¹) :
    ‖z‖ ≤ (Q : ℝ) ^ (2 - vinogradovRouteTPowerSavingExponent u) := by
  let b := vinogradovRouteTMoment (4 * u)
  let M := 4 * b ^ 2
  let S := vinogradovRouteTMomentSaving u
  have hb : b ≠ 0 := vinogradovRouteTMoment_ne_zero (by omega)
  have hM : M ≠ 0 := by unfold M; positivity
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hy : 0 ≤ (Q : ℝ) ^ (8 * b ^ 2) * ((Q : ℝ) ^ S)⁻¹ := by
    positivity
  have hroot : ‖z‖ ≤
      ((Q : ℝ) ^ (8 * b ^ 2) * ((Q : ℝ) ^ S)⁻¹) ^ ((M : ℝ)⁻¹) := by
    apply le_rpow_inv_nat_of_pow_le hM hy
    simpa [b, M, S] using hmoment
  have hexponent :
      ((((8 * b ^ 2 : ℕ) : ℝ) + -(S : ℝ)) * (M : ℝ)⁻¹) =
        2 - vinogradovRouteTPowerSavingExponent u := by
    unfold vinogradovRouteTPowerSavingExponent
    change ((((8 * b ^ 2 : ℕ) : ℝ) + -(S : ℝ)) * (M : ℝ)⁻¹) =
      2 - (S : ℝ) / (4 * (b : ℝ) ^ 2)
    simp only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    field_simp [hbR]
    ring
  have hroot_eq :
      ((Q : ℝ) ^ (8 * b ^ 2) * ((Q : ℝ) ^ S)⁻¹) ^ ((M : ℝ)⁻¹) =
        (Q : ℝ) ^ (2 - vinogradovRouteTPowerSavingExponent u) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_neg hQpos.le, ← Real.rpow_add hQpos]
    rw [← Real.rpow_mul hQpos.le, hexponent]
  rw [← hroot_eq]
  exact hroot

end

end RHTower.Sieve
