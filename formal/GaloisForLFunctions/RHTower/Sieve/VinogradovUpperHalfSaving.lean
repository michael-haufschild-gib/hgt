import GaloisForLFunctions.RHTower.Sieve.VinogradovEmbeddedBilinear
import GaloisForLFunctions.RHTower.Sieve.VinogradovRouteTSaving

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Exact embedding of the integer interval `[Q,2Q)` into the ambient
power-sum box `[0,2Q)`. -/
def vinogradovUpperHalfEmbedding (Q : ℕ) : Fin Q ↪ Fin (2 * Q) where
  toFun n := ⟨Q + n.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

theorem vinogradovUpperHalfEmbedding_val (Q : ℕ) (n : Fin Q) :
    (vinogradovUpperHalfEmbedding Q n).val = Q + n.val := rfl

def vinogradovUpperHalfBilinearSum (Q : ℕ) {k : ℕ} (α : Fin k → ℝ) : ℂ :=
  vinogradovEmbeddedBilinearSum
    (vinogradovUpperHalfEmbedding Q) (vinogradovUpperHalfEmbedding Q) α

theorem vinogradovUpperHalfBilinearSum_eq
    {Q k : ℕ} (α : Fin k → ℝ) :
    vinogradovUpperHalfBilinearSum Q α =
      ∑ l : Fin Q, ∑ m : Fin Q,
        finitePhaseChar
          (∑ j : Fin k, α j *
            ((((Q + l.val) : ℝ) * ((Q + m.val) : ℝ)) ^ (j.val + 1))) := by
  unfold vinogradovUpperHalfBilinearSum vinogradovEmbeddedBilinearSum
  unfold finitePhaseSum vinogradovEmbeddedBilinearPolynomialPhase
  unfold vinogradovBilinearPolynomialPhase
  simp_rw [vinogradovUpperHalfEmbedding_val, Nat.cast_add]

theorem vinogradovUpperHalfPairPhase_neg
    {Q k : ℕ} (α : Fin k → ℝ) (l m : Fin Q) :
    (∑ j : Fin k, (-α j) *
        ((((Q + l.val) : ℝ) * ((Q + m.val) : ℝ)) ^ (j.val + 1))) =
      -(∑ j : Fin k, α j *
        ((((Q + l.val) : ℝ) * ((Q + m.val) : ℝ)) ^ (j.val + 1))) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vinogradovUpperHalfBilinearSum_neg
    {Q k : ℕ} (α : Fin k → ℝ) :
    vinogradovUpperHalfBilinearSum Q (fun j => -α j) =
      starRingEnd ℂ (vinogradovUpperHalfBilinearSum Q α) := by
  rw [vinogradovUpperHalfBilinearSum_eq,
    vinogradovUpperHalfBilinearSum_eq, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [vinogradovUpperHalfPairPhase_neg, finitePhaseChar_neg]

theorem norm_vinogradovUpperHalfBilinearSum_neg
    {Q k : ℕ} (α : Fin k → ℝ) :
    ‖vinogradovUpperHalfBilinearSum Q (fun j => -α j)‖ =
      ‖vinogradovUpperHalfBilinearSum Q α‖ := by
  rw [vinogradovUpperHalfBilinearSum_neg]
  exact RCLike.norm_conj _

/-- Collected Route-T moment estimate on the true upper-half interval.
The interval has only `Q` points, but its power differences are grouped
inside the ambient box `2Q`; this is the source-faithful MV24.7 geometry. -/
theorem norm_vinogradovUpperHalfBilinearSum_pow_le_collected
    {u Q : ℕ} (hu : 1 ≤ u) (hQ : 1 ≤ Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      (2 * Q) ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * (2 * Q) ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        ((2 * Q) ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        ((2 * Q : ℕ) : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovUpperHalfBilinearSum Q α‖ ^
        (4 * vinogradovRouteTMoment (4 * u) ^ 2) ≤
      (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        ((2 * Q : ℕ) : ℝ) ^
          (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
        (((2 * Q : ℕ) : ℝ) ^ (40 * u ^ 2))⁻¹ := by
  let s := 4 * u
  let k := vinogradovRouteTOrder s
  let b := vinogradovRouteTMoment s
  let P := 2 * Q
  let U : Fin k → Prop := vinogradovUsefulCoordinate u
  let e := vinogradovUpperHalfEmbedding Q
  have hs : 1 ≤ s := by unfold s; omega
  have hb : b ≠ 0 := vinogradovRouteTMoment_ne_zero hs
  have hP1 : 1 ≤ P := by unfold P; omega
  have hP0 : P ≠ 0 := Nat.ne_of_gt (by omega)
  have hbase := norm_vinogradovEmbeddedBilinearSum_pow_le_mixedProduct
    hb hP0 hP0 e e α U a q hq hcop happrox
  have hcard :
      (Fintype.card ((Fin b → Fin Q) × (Fin b → Fin Q)) : ℝ) =
        (Q : ℝ) ^ (2 * b) := by
    norm_cast
    exact card_vinogradovTuplePair Q b
  rw [hcard] at hbase
  have hmean := vinogradovRouteT_mean_value_bound_real hs hP0
  have hmeanProduct :
      ((Fintype.card (VinogradovDiagonalSolution P b k) : ℝ) *
        Fintype.card (VinogradovDiagonalSolution P b k)) ≤
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) := by
    exact mul_le_mul hmean hmean (by positivity) (by positivity)
  have hmixed := prod_vinogradovMixedCoordinateCost_le_envelope
    (Q := P) (b := b) hP1 (Nat.one_le_iff_ne_zero.mpr hb) U q
    hRq hqR habsorb
  have henvelope := prod_vinogradovUsefulCoordinateEnvelope_le
    (Q := P) (b := b) (u := u) hP1
  have hcoord :
      (∏ j : Fin k, vinogradovMixedCoordinateCost U P P b q j) ≤
        (24 * (b : ℝ) ^ 2) ^ k *
          (P : ℝ) ^ (k * (k + 1)) *
          ((P : ℝ) ^ (40 * u ^ 2))⁻¹ :=
    hmixed.trans (by simpa [s, k, b, P, U] using henvelope)
  have hQP : (Q : ℝ) ≤ P := by
    unfold P
    exact_mod_cast (show Q ≤ 2 * Q by omega)
  have houterLe :
      (((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) ≤
      (((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (((P : ℝ) ^ (2 * b)) ^ (2 * b - 1))) := by
    have h1 : (Q : ℝ) ^ (2 * b - 1) ≤ (P : ℝ) ^ (2 * b - 1) :=
      pow_le_pow_left₀ (by positivity) hQP _
    have h2 : (Q : ℝ) ^ (2 * b) ≤ (P : ℝ) ^ (2 * b) :=
      pow_le_pow_left₀ (by positivity) hQP _
    exact mul_le_mul
      (pow_le_pow_left₀ (by positivity) h1 _)
      (pow_le_pow_left₀ (by positivity) h2 _)
      (by positivity) (by positivity)
  have houter0 : 0 ≤
      (((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (((P : ℝ) ^ (2 * b)) ^ (2 * b - 1))) := by positivity
  have hmean0 : 0 ≤
      ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
        (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
      ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
        (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) := by positivity
  have hphase :
      2 * ((2 * b - 1) * (2 * b)) +
          2 * vinogradovRouteTMeanBoundExponent s + k * (k + 1) =
        8 * b ^ 2 + (2800 * u + 4) := by
    simpa [s, k, b] using routeT_total_phase_exponent hu
  have hQphase :
      ((((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((P : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
          (P : ℝ) ^ (k * (k + 1)) =
        (P : ℝ) ^ (8 * b ^ 2 + (2800 * u + 4)) := by
    rw [← pow_mul, ← pow_mul]
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    nlinarith
  calc
    _ ≤ ((((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
        ((Fintype.card (VinogradovDiagonalSolution P b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution P b k))) *
        ∏ j : Fin k, vinogradovMixedCoordinateCost U P P b q j := by
      simpa [vinogradovUpperHalfBilinearSum, s, k, b, P, U, e] using hbase
    _ ≤ ((((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
        (((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s))) *
        ∏ j : Fin k, vinogradovMixedCoordinateCost U P P b q j := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmeanProduct (by positivity))
        (Finset.prod_nonneg fun j _ =>
          vinogradovMixedCoordinateCost_nonneg U P P b q j)
    _ ≤ (((((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((P : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
        (((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s))) *
        ∏ j : Fin k, vinogradovMixedCoordinateCost U P P b q j) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right houterLe hmean0)
        (Finset.prod_nonneg fun j _ =>
          vinogradovMixedCoordinateCost_nonneg U P P b q j)
    _ ≤ (((((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((P : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
        (((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
        ((vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s))) *
        ((24 * (b : ℝ) ^ 2) ^ k *
          (P : ℝ) ^ (k * (k + 1)) *
          ((P : ℝ) ^ (40 * u ^ 2))⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hcoord (mul_nonneg houter0 hmean0)
    _ = (vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) ^ 2 *
        (24 * (b : ℝ) ^ 2) ^ k *
        (((((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
          (((P : ℝ) ^ (2 * b)) ^ (2 * b - 1))) *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s *
          (P : ℝ) ^ vinogradovRouteTMeanBoundExponent s) *
          (P : ℝ) ^ (k * (k + 1))) *
        ((P : ℝ) ^ (40 * u ^ 2))⁻¹ := by ring
    _ = (vinogradovMeanConstant k (vinogradovRouteTMomentSteps s) : ℝ) ^ 2 *
        (24 * (b : ℝ) ^ 2) ^ k *
        (P : ℝ) ^ (8 * b ^ 2 + (2800 * u + 4)) *
        ((P : ℝ) ^ (40 * u ^ 2))⁻¹ := by
      rw [hQphase]
    _ = (vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) : ℝ) ^ 2 *
        (24 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2) ^
          vinogradovRouteTOrder (4 * u) *
        ((2 * Q : ℕ) : ℝ) ^
          (8 * vinogradovRouteTMoment (4 * u) ^ 2 + (2800 * u + 4)) *
        (((2 * Q : ℕ) : ℝ) ^ (40 * u ^ 2))⁻¹ := by rfl

theorem norm_vinogradovUpperHalfBilinearSum_le_rpow
    {u Q : ℕ} (hu : 141 ≤ u)
    (hQ : vinogradovRouteTMomentConstant u ≤ 2 * Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      (2 * Q) ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * (2 * Q) ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        ((2 * Q) ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        ((2 * Q : ℕ) : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovUpperHalfBilinearSum Q α‖ ≤
      ((2 * Q : ℕ) : ℝ) ^ (2 - vinogradovRouteTPowerSavingExponent u) := by
  have hP1 : 1 ≤ 2 * Q := by
    have hc : 1 ≤ vinogradovRouteTMomentConstant u := by
      unfold vinogradovRouteTMomentConstant
      have hmean : 1 ≤ vinogradovMeanConstant
          (vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentSteps (4 * u)) := by
        generalize vinogradovRouteTMomentSteps (4 * u) = r
        cases r with
        | zero => simp [vinogradovMeanConstant]
        | succ r => simp only [vinogradovMeanConstant]; omega
      have hb := vinogradovRouteTMoment_ne_zero (s := 4 * u) (by omega)
      have hbase : 1 ≤ 24 * vinogradovRouteTMoment (4 * u) ^ 2 := by
        exact Nat.mul_pos (by omega) (pow_pos (Nat.pos_of_ne_zero hb) 2)
      exact Nat.mul_pos (pow_pos (by omega) 2)
        (pow_pos (by omega) (vinogradovRouteTOrder (4 * u)))
    exact hc.trans hQ
  have hcollected := norm_vinogradovUpperHalfBilinearSum_pow_le_collected
    (u := u) (Q := Q) (by omega) (by omega) α a q hq hcop happrox hRq hqR habsorb
  have hmoment := routeTMoment_powerSaving_of_collected hu hQ hcollected
  exact norm_le_rpow_of_routeTMomentSaving hu hP1 hmoment

/-- Sign-reversed approximation form used by logarithmic Taylor phases,
whose degree-`j` coefficients all have the same negative sign after the
MV24.11 substitution. -/
theorem norm_vinogradovUpperHalfBilinearSum_le_rpow_of_negApprox
    {u Q : ℕ} (hu : 141 ≤ u)
    (hQ : vinogradovRouteTMomentConstant u ≤ 2 * Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |-α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      (2 * Q) ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * (2 * Q) ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        ((2 * Q) ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        ((2 * Q : ℕ) : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovUpperHalfBilinearSum Q α‖ ≤
      ((2 * Q : ℕ) : ℝ) ^ (2 - vinogradovRouteTPowerSavingExponent u) := by
  rw [← norm_vinogradovUpperHalfBilinearSum_neg α]
  exact norm_vinogradovUpperHalfBilinearSum_le_rpow hu hQ
    (fun j => -α j) a q hq hcop happrox hRq hqR habsorb

end

end RHTower.Sieve
