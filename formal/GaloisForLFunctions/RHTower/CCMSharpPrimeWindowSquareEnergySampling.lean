import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareSampling
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowExcessEnergyGate
import GaloisForLFunctions.RHTower.CCMCumulativeNegativeMassSpectrum
import GaloisForLFunctions.RHTower.CCMCompletedErrorVariationEnergyGate

/-!
# Critical square-sample energy for the dyadic sharp prime window

Let `E(n)` be the positive excess of the weighted von Mangoldt window above its exact
square-root main term. This module proves that the full Dirichlet-energy RH criterion need only
be checked at perfect squares:

`Summable (m ↦ E(m^2) / m^(1+epsilon))` for every positive `epsilon` implies RH.

The proof partitions the apertures into the exact square blocks
`r^2 ≤ n < (r+1)^2`. A block has `2r+1` members, and the next-square interpolation error is only
logarithmic. Consequently the all-aperture energy at exponent `1+epsilon` is controlled by the
square-sample energy at exponent `1+2*epsilon`, plus a summable subpower correction.

This is an unconditional reduction theorem, not a proof of the square-sample summability premise.
-/

open scoped BigOperators
open Complex LSeries Set

noncomputable section

namespace RHTower

private def sqrtBlock (r : ℕ) : Set ℕ :=
  Set.Ico (r ^ 2) ((r + 1) ^ 2)

private theorem existsUnique_mem_sqrtBlock (n : ℕ) :
    ∃! r : ℕ, n ∈ sqrtBlock r := by
  refine ⟨Nat.sqrt n, ?_, ?_⟩
  · exact ⟨Nat.sqrt_le' n, Nat.lt_succ_sqrt' n⟩
  · intro r hr
    exact Nat.eq_sqrt'.mpr hr

private theorem sqrtBlock_finite (r : ℕ) : (sqrtBlock r).Finite :=
  Set.finite_Ico _ _

private noncomputable instance sqrtBlockFintype (r : ℕ) : Fintype (sqrtBlock r) :=
  (sqrtBlock_finite r).fintype

private def sqrtBlockEquiv (r : ℕ) :
    sqrtBlock r ≃ ↥(Finset.Ico (r ^ 2) ((r + 1) ^ 2)) where
  toFun n := ⟨n.1, by
    exact Finset.mem_Ico.mpr n.2⟩
  invFun n := ⟨n.1, by
    exact Finset.mem_Ico.mp n.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sqrtBlock_card (r : ℕ) : Fintype.card (sqrtBlock r) = 2 * r + 1 := by
  rw [Fintype.card_congr (sqrtBlockEquiv r), Fintype.card_coe,
    Nat.card_Ico]
  rw [tsub_eq_iff_eq_add_of_le (by
    simp only [pow_two]
    exact Nat.mul_le_mul (Nat.le_succ r) (Nat.le_succ r))]
  ring

private def squareBlockLift (a : ℕ → ℝ) (sigma : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else a (Nat.sqrt n + 1) / (n : ℝ) ^ sigma

private theorem squareBlockLift_nonneg {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    (sigma : ℝ) (n : ℕ) :
    0 ≤ squareBlockLift a sigma n := by
  rw [squareBlockLift]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (ha _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem squareBlockLift_le_on_block {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    {sigma : ℝ} (hsigma : 0 < sigma) {r n : ℕ} (hr : 0 < r)
    (hn : n ∈ sqrtBlock r) :
    squareBlockLift a sigma n ≤
      a (r + 1) / ((r ^ 2 : ℕ) : ℝ) ^ sigma := by
  have hnpos : 0 < n := by
    have : r ^ 2 ≤ n := hn.1
    have : 0 < r ^ 2 := pow_pos hr _
    omega
  have hsqrt : Nat.sqrt n = r := by
    exact (Nat.eq_sqrt'.mpr hn).symm
  rw [squareBlockLift, if_neg hnpos.ne', hsqrt]
  apply div_le_div_of_nonneg_left (ha (r + 1))
  · exact Real.rpow_pos_of_pos (by positivity) _
  · exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast hn.1) hsigma.le

private theorem sqrtBlock_tsum_squareBlockLift_le {a : ℕ → ℝ}
    (ha : ∀ m, 0 ≤ a m) {sigma : ℝ} (hsigma : 0 < sigma) (r : ℕ) :
    (∑' n : sqrtBlock r, squareBlockLift a sigma n) ≤
      (2 * r + 1 : ℝ) *
        (a (r + 1) / ((r ^ 2 : ℕ) : ℝ) ^ sigma) := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [tsum_fintype]
    have hsum : (∑ n : sqrtBlock 0, squareBlockLift a sigma n) = 0 := by
      apply Finset.sum_eq_zero
      intro n _hn
      have hnzero : n.1 = 0 := by
        have hnlt : n.1 < (0 + 1) ^ 2 := n.2.2
        omega
      rw [squareBlockLift, if_pos hnzero]
    rw [hsum]
    exact mul_nonneg (by positivity)
      (div_nonneg (ha 1) (Real.rpow_nonneg (by positivity) _))
  · rw [tsum_fintype]
    calc
      (∑ n : sqrtBlock r, squareBlockLift a sigma n) ≤
          ∑ _n : sqrtBlock r,
            (a (r + 1) / ((r ^ 2 : ℕ) : ℝ) ^ sigma) := by
        exact Finset.sum_le_sum fun n _ =>
          squareBlockLift_le_on_block ha hsigma hr n.2
      _ = (2 * r + 1 : ℝ) *
          (a (r + 1) / ((r ^ 2 : ℕ) : ℝ) ^ sigma) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          sqrtBlock_card]
        norm_num

private def successorSquareWeightedTerm (a : ℕ → ℝ) (tau : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else a (r + 1) / (r : ℝ) ^ tau

private theorem square_rpow_eq (r : ℕ) (sigma : ℝ) :
    (((r ^ 2 : ℕ) : ℝ) ^ sigma) = (r : ℝ) ^ (2 * sigma) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg r)]
  norm_num

private theorem sqrtBlock_tsum_squareBlockLift_le_successorTerm
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    {sigma : ℝ} (hsigma : 0 < sigma) (r : ℕ) :
    (∑' n : sqrtBlock r, squareBlockLift a sigma n) ≤
      3 * successorSquareWeightedTerm a (2 * sigma - 1) r := by
  rcases r.eq_zero_or_pos with rfl | hr
  · have hzero : (∑' n : sqrtBlock 0, squareBlockLift a sigma n) = 0 := by
      rw [tsum_fintype]
      apply Finset.sum_eq_zero
      intro n _hn
      have hnzero : n.1 = 0 := by
        have hnlt : n.1 < (0 + 1) ^ 2 := n.2.2
        omega
      rw [squareBlockLift, if_pos hnzero]
    rw [hzero]
    simp [successorSquareWeightedTerm]
  · refine (sqrtBlock_tsum_squareBlockLift_le ha hsigma r).trans ?_
    rw [successorSquareWeightedTerm, if_neg hr.ne', square_rpow_eq]
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hden : (r : ℝ) ^ (2 * sigma) =
        (r : ℝ) * (r : ℝ) ^ (2 * sigma - 1) := by
      calc
        (r : ℝ) ^ (2 * sigma) =
            (r : ℝ) ^ (1 + (2 * sigma - 1)) := by congr 1; ring
        _ = (r : ℝ) ^ (1 : ℝ) *
            (r : ℝ) ^ (2 * sigma - 1) := Real.rpow_add hrR _ _
        _ = (r : ℝ) * (r : ℝ) ^ (2 * sigma - 1) := by
          rw [Real.rpow_one]
    rw [hden]
    have hcount : (2 * r + 1 : ℝ) ≤ 3 * (r : ℝ) := by
      exact_mod_cast (show 2 * r + 1 ≤ 3 * r by omega)
    have hquot : 0 ≤ a (r + 1) /
        ((r : ℝ) * (r : ℝ) ^ (2 * sigma - 1)) :=
      div_nonneg (ha (r + 1))
        (mul_nonneg hrR.le (Real.rpow_nonneg hrR.le _))
    calc
      (2 * r + 1 : ℝ) *
          (a (r + 1) /
            ((r : ℝ) * (r : ℝ) ^ (2 * sigma - 1))) ≤
          (3 * (r : ℝ)) *
            (a (r + 1) /
              ((r : ℝ) * (r : ℝ) ^ (2 * sigma - 1))) :=
        mul_le_mul_of_nonneg_right hcount hquot
      _ = 3 * (a (r + 1) / (r : ℝ) ^ (2 * sigma - 1)) := by
        have hpow : 0 < (r : ℝ) ^ (2 * sigma - 1) :=
          Real.rpow_pos_of_pos hrR _
        field_simp

private theorem summable_squareBlockLift_of_successorSquareWeightedTerm
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (h : Summable (successorSquareWeightedTerm a (2 * sigma - 1))) :
    Summable (squareBlockLift a sigma) := by
  rw [summable_partition (squareBlockLift_nonneg ha sigma)
    existsUnique_mem_sqrtBlock]
  constructor
  · intro r
    exact (hasSum_fintype (fun n : sqrtBlock r =>
      squareBlockLift a sigma n)).summable
  · apply (h.mul_left 3).of_nonneg_of_le
    · intro r
      exact tsum_nonneg fun n => squareBlockLift_nonneg ha sigma n
    · intro r
      exact sqrtBlock_tsum_squareBlockLift_le_successorTerm ha hsigma r

private theorem summable_successorSquareWeightedTerm_of_weightedTerm
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    {tau : ℝ} (htau : 0 < tau)
    (h : Summable (realDirichletWeightedTerm a tau)) :
    Summable (successorSquareWeightedTerm a tau) := by
  have hshift : Summable (fun r =>
      realDirichletWeightedTerm a tau (r + 1)) :=
    h.comp_injective Nat.succ_injective
  have hmajor : Summable (fun r =>
      (2 : ℝ) ^ tau * realDirichletWeightedTerm a tau (r + 1)) :=
    hshift.mul_left ((2 : ℝ) ^ tau)
  apply hmajor.of_nonneg_of_le
  · intro r
    rw [successorSquareWeightedTerm]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (ha (r + 1))
        (Real.rpow_nonneg (Nat.cast_nonneg r) _)
  · intro r
    rcases r.eq_zero_or_pos with rfl | hr
    · simp only [successorSquareWeightedTerm]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (by simp [realDirichletWeightedTerm, ha 1])
    · rw [successorSquareWeightedTerm, if_neg hr.ne',
        realDirichletWeightedTerm, if_neg (Nat.succ_ne_zero r)]
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      have hmR : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
      have hmle : ((r + 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by
        exact_mod_cast (show r + 1 ≤ 2 * r by omega)
      have hpow : ((r + 1 : ℕ) : ℝ) ^ tau ≤
          (2 : ℝ) ^ tau * (r : ℝ) ^ tau := by
        calc
          ((r + 1 : ℕ) : ℝ) ^ tau ≤ (2 * (r : ℝ)) ^ tau :=
            Real.rpow_le_rpow hmR.le hmle htau.le
          _ = (2 : ℝ) ^ tau * (r : ℝ) ^ tau := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrR.le]
      have hrpow : 0 < (r : ℝ) ^ tau := Real.rpow_pos_of_pos hrR _
      have hmpow : 0 < ((r + 1 : ℕ) : ℝ) ^ tau :=
        Real.rpow_pos_of_pos hmR _
      rw [show (2 : ℝ) ^ tau *
          (a (r + 1) / ((r + 1 : ℕ) : ℝ) ^ tau) =
          ((2 : ℝ) ^ tau * a (r + 1)) /
            ((r + 1 : ℕ) : ℝ) ^ tau by ring,
        div_le_div_iff₀ hrpow hmpow]
      calc
        a (r + 1) * ((r + 1 : ℕ) : ℝ) ^ tau ≤
            a (r + 1) * ((2 : ℝ) ^ tau * (r : ℝ) ^ tau) :=
          mul_le_mul_of_nonneg_left hpow (ha (r + 1))
        _ = (2 : ℝ) ^ tau * a (r + 1) * (r : ℝ) ^ tau := by ring

private def upperSquareLiftCoefficient (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else a (Nat.sqrt n + 1)

private theorem realDirichletWeightedTerm_upperSquareLiftCoefficient
    (a : ℕ → ℝ) (sigma : ℝ) :
    realDirichletWeightedTerm (upperSquareLiftCoefficient a) sigma =
      squareBlockLift a sigma := by
  funext n
  by_cases hn : n = 0
  · simp [realDirichletWeightedTerm,
      squareBlockLift, hn]
  · simp [realDirichletWeightedTerm, upperSquareLiftCoefficient,
      squareBlockLift, hn]

private theorem LSeriesSummable_of_realDirichletWeightedTerm_summable
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {sigma : ℝ}
    (h : Summable (realDirichletWeightedTerm f sigma)) :
    LSeriesSummable (fun n => ((f n : ℝ) : ℂ)) (sigma : ℂ) := by
  change Summable (LSeries.term (fun n => ((f n : ℝ) : ℂ)) (sigma : ℂ))
  apply h.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp [realDirichletWeightedTerm]
  · rw [LSeries.term_of_ne_zero hn, norm_div, norm_real,
      Real.norm_of_nonneg (hf n), realDirichletWeightedTerm, if_neg hn,
      Complex.norm_cpow_real, Complex.norm_natCast]

theorem realDirichletWeightedTerm_summable_of_LSeriesSummable
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {sigma : ℝ}
    (h : LSeriesSummable (fun n => ((f n : ℝ) : ℂ)) (sigma : ℂ)) :
    Summable (realDirichletWeightedTerm f sigma) := by
  have hnorm := h.norm
  apply hnorm.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [realDirichletWeightedTerm]
  · rw [LSeries.term_of_ne_zero hn, norm_div, norm_real,
      Real.norm_of_nonneg (hf n), realDirichletWeightedTerm, if_neg hn,
      Complex.norm_cpow_real, Complex.norm_natCast]

private theorem posPart_le_posPart_add_of_le_add
    {x y B : ℝ} (hB : 0 ≤ B) (hxy : x ≤ y + B) :
    x⁺ ≤ y⁺ + B := by
  change max x 0 ≤ max y 0 + B
  apply max_le
  · exact hxy.trans (add_le_add (le_max_left y 0) le_rfl)
  · exact add_nonneg (le_max_right y 0) hB

theorem dyadicWeightedPrimeWindowPositiveExcess_le_upperSquare_add_log
    {n : ℕ} (hn : 0 < n) :
    dyadicWeightedPrimeWindowPositiveExcess n ≤
      dyadicWeightedPrimeWindowPositiveExcess ((Nat.sqrt n + 1) ^ 2) +
        2 * (1 - (Real.sqrt 2)⁻¹) +
          3 * Real.sqrt 2 * Real.log ((Nat.sqrt n + 1) ^ 2) := by
  let c : ℝ := 2 * (1 - (Real.sqrt 2)⁻¹)
  let m : ℕ := Nat.sqrt n + 1
  let N : ℕ := m ^ 2
  have hsqrtTwo : 1 ≤ Real.sqrt 2 :=
    Real.one_le_sqrt.mpr (by norm_num)
  have hinv : (Real.sqrt 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hsqrtTwo
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hNpos : 0 < N := by
    dsimp only [N, m]
    positivity
  have hlog : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hNpos)
  have hlocal := dyadicWeightedPrimeWindow_le_upperSquare_add_log hn
  have hlocalN : dyadicWeightedPrimeWindow n ≤
      dyadicWeightedPrimeWindow N + 3 * Real.sqrt 2 * Real.log N := by
    simpa only [N, m, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hlocal
  have hmle : (m : ℝ) ≤ Real.sqrt n + 1 := by
    dsimp only [m]
    push_cast
    have hrSqNat : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
    have hrle : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
      have hrSq : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by
        exact_mod_cast hrSqNat
      exact (Real.le_sqrt (by positivity) (by positivity)).mpr hrSq
    linarith
  have hmain : c * (m : ℝ) ≤ c * Real.sqrt n + c := by
    have h := mul_le_mul_of_nonneg_left hmle hc
    linarith
  have hraw :
      dyadicWeightedPrimeWindow n - c * Real.sqrt n ≤
        (dyadicWeightedPrimeWindow N - c * (m : ℝ)) +
          (c + 3 * Real.sqrt 2 * Real.log N) := by
    linarith
  have hB : 0 ≤ c + 3 * Real.sqrt 2 * Real.log N := by
    positivity
  have hpos := posPart_le_posPart_add_of_le_add hB hraw
  have hsqrtN : Real.sqrt N = (m : ℝ) := by
    dsimp only [N]
    push_cast
    exact Real.sqrt_sq (Nat.cast_nonneg m)
  have hsqrtUpper :
      Real.sqrt ((((Nat.sqrt n + 1) ^ 2 : ℕ) : ℝ)) =
        ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
    push_cast
    exact Real.sqrt_sq (by positivity)
  rw [dyadicWeightedPrimeWindowPositiveExcess,
    dyadicWeightedPrimeWindowPositiveExcess, hsqrtUpper]
  simpa [c, N, m, Nat.cast_pow, add_assoc] using hpos

private theorem exists_dyadicWeightedPrimeWindowPositiveExcess_upperSquare_powerMajorant
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      dyadicWeightedPrimeWindowPositiveExcess n ≤
        upperSquareLiftCoefficient
            (fun m => dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) n +
          D * powerCorrectionCoefficient delta n := by
  let c : ℝ := 2 * (1 - (Real.sqrt 2)⁻¹)
  let K : ℝ := (4 : ℝ) ^ delta
  let D : ℝ := c + 3 * Real.sqrt 2 * (K / delta)
  have hsqrtTwo : 1 ≤ Real.sqrt 2 :=
    Real.one_le_sqrt.mpr (by norm_num)
  have hinv : (Real.sqrt 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hsqrtTwo
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, fun n => ?_⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num [dyadicWeightedPrimeWindowPositiveExcess,
      dyadicWeightedPrimeWindow, upperSquareLiftCoefficient,
      powerCorrectionCoefficient]
  · let m : ℕ := Nat.sqrt n + 1
    let N : ℕ := m ^ 2
    have hpoint := dyadicWeightedPrimeWindowPositiveExcess_le_upperSquare_add_log hn
    have hpointN : dyadicWeightedPrimeWindowPositiveExcess n ≤
        dyadicWeightedPrimeWindowPositiveExcess N + c +
          3 * Real.sqrt 2 * Real.log N := by
      simpa only [c, N, m, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        using hpoint
    have hN4Nat : N ≤ 4 * n := by
      have hrpos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
      have hrSqNat : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
      dsimp only [N, m]
      nlinarith
    have hN4 : (N : ℝ) ≤ 4 * (n : ℝ) := by
      exact_mod_cast hN4Nat
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpowOne : 1 ≤ (n : ℝ) ^ delta :=
      Real.one_le_rpow hnOne hdelta.le
    have hNpow : (N : ℝ) ^ delta ≤ K * (n : ℝ) ^ delta := by
      calc
        (N : ℝ) ^ delta ≤ (4 * (n : ℝ)) ^ delta :=
          Real.rpow_le_rpow (by positivity) hN4 hdelta.le
        _ = (4 : ℝ) ^ delta * (n : ℝ) ^ delta := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
        _ = K * (n : ℝ) ^ delta := rfl
    have hlog : Real.log N ≤ (K / delta) * (n : ℝ) ^ delta := by
      have hraw := Real.log_le_rpow_div (x := (N : ℝ))
        (by positivity) hdelta
      calc
        Real.log N ≤ (N : ℝ) ^ delta / delta := hraw
        _ ≤ (K * (n : ℝ) ^ delta) / delta := by
          exact div_le_div_of_nonneg_right hNpow hdelta.le
        _ = (K / delta) * (n : ℝ) ^ delta := by ring
    have hcCost : c ≤ c * (n : ℝ) ^ delta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowOne hc
    have hlogCost : 3 * Real.sqrt 2 * Real.log N ≤
        (3 * Real.sqrt 2 * (K / delta)) * (n : ℝ) ^ delta := by
      have := mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ 3 * Real.sqrt 2 by positivity)
      simpa only [mul_assoc] using this
    have hcost : c + 3 * Real.sqrt 2 * Real.log N ≤
        D * (n : ℝ) ^ delta := by
      calc
        c + 3 * Real.sqrt 2 * Real.log N ≤
            c * (n : ℝ) ^ delta +
              (3 * Real.sqrt 2 * (K / delta)) * (n : ℝ) ^ delta :=
          add_le_add hcCost hlogCost
        _ = D * (n : ℝ) ^ delta := by
          dsimp only [D]
          ring
    have hfinal : dyadicWeightedPrimeWindowPositiveExcess n ≤
        dyadicWeightedPrimeWindowPositiveExcess N +
          D * (n : ℝ) ^ delta :=
      hpointN.trans (by linarith [hcost])
    simpa [upperSquareLiftCoefficient, powerCorrectionCoefficient,
      hn.ne', N, m] using hfinal

/-- Critical Dirichlet energy of the positive excess on successor-square apertures is enough
to prove RH. The interpolation from all apertures to the next square loses only a summable
subpower correction. -/
private theorem riemannHypothesis_of_successorSquarePrimeWindowPositiveExcessEnergy
    (hSquare : ∀ epsilon : ℝ, 0 < epsilon →
      Summable
        (successorSquareWeightedTerm
          (fun m => dyadicWeightedPrimeWindowPositiveExcess (m ^ 2))
          (1 + epsilon))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessEnergy
  intro epsilon hepsilon
  let squareExcess : ℕ → ℝ := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)
  have hsquareNonneg : ∀ m, 0 ≤ squareExcess m := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2)
  have hSquareAt : Summable
      (successorSquareWeightedTerm squareExcess
        (2 * (1 + epsilon) - 1)) := by
    have h := hSquare (2 * epsilon) (by positivity)
    rw [show 2 * (1 + epsilon) - 1 = 1 + 2 * epsilon by ring]
    exact h
  have hBlock : Summable (squareBlockLift squareExcess (1 + epsilon)) :=
    summable_squareBlockLift_of_successorSquareWeightedTerm
      hsquareNonneg (by linarith) hSquareAt
  have hLiftReal : Summable
      (realDirichletWeightedTerm
        (upperSquareLiftCoefficient squareExcess) (1 + epsilon)) := by
    simpa only [realDirichletWeightedTerm_upperSquareLiftCoefficient]
      using hBlock
  have hliftNonneg : ∀ n, 0 ≤ upperSquareLiftCoefficient squareExcess n := by
    intro n
    rw [upperSquareLiftCoefficient]
    split_ifs
    · exact le_rfl
    · exact hsquareNonneg _
  have hLift : LSeriesSummable
      (fun n => (((upperSquareLiftCoefficient squareExcess n : ℝ) : ℂ)))
      (((1 + epsilon : ℝ) : ℂ)) :=
    LSeriesSummable_of_realDirichletWeightedTerm_summable
      hliftNonneg hLiftReal
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  obtain ⟨D, hD, hmajor⟩ :=
    exists_dyadicWeightedPrimeWindowPositiveExcess_upperSquare_powerMajorant
      hdelta
  have hpower : LSeriesSummable
      (fun n => ((powerCorrectionCoefficient delta n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) := by
    apply powerCorrectionCoefficient_LSeriesSummable
    simp only [Complex.ofReal_re]
    dsimp only [delta]
    linarith
  have hadd := hLift.add (hpower.smul (D : ℂ))
  have hmajorSummable : LSeriesSummable
      (fun n => (((upperSquareLiftCoefficient squareExcess n +
        D * powerCorrectionCoefficient delta n : ℝ) : ℂ)))
      (((1 + epsilon : ℝ) : ℂ)) := by
    change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ)))
    change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hadd
    apply hadd.congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        ofReal_add, ofReal_mul]
  apply LSeriesSummable_of_nonneg_of_le
    dyadicWeightedPrimeWindowPositiveExcess_nonneg
    (fun n => add_nonneg (hliftNonneg n)
      (mul_nonneg hD (powerCorrectionCoefficient_nonneg delta n)))
  · intro n
    simpa only [squareExcess] using hmajor n
  · exact hmajorSummable

/-- **Fixed-abscissa square-to-full energy transfer.**  Summability of the positive excess at
perfect-square apertures with weight `m^(-1-2*alpha)` implies summability of the full positive
excess with weight `n^(-1-alpha)`.  The factor two is the exact change of exponent forced by the
cardinality `2*m+1` of a square block. -/
theorem dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareEnergy
    {alpha : ℝ} (halpha : 0 < alpha)
    (hSquare : Summable
      (realDirichletWeightedTerm
        (fun m => dyadicWeightedPrimeWindowPositiveExcess (m ^ 2))
        (1 + 2 * alpha))) :
    LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)) := by
  let squareExcess : ℕ → ℝ := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)
  have hsquareNonneg : ∀ m, 0 ≤ squareExcess m := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2)
  have hSquareAt : Summable
      (successorSquareWeightedTerm squareExcess
        (2 * (1 + alpha) - 1)) := by
    have hshift : Summable
        (successorSquareWeightedTerm squareExcess (1 + 2 * alpha)) :=
      summable_successorSquareWeightedTerm_of_weightedTerm
        hsquareNonneg (by linarith) (by
          simpa only [squareExcess] using hSquare)
    rw [show 2 * (1 + alpha) - 1 = 1 + 2 * alpha by ring]
    exact hshift
  have hBlock : Summable (squareBlockLift squareExcess (1 + alpha)) :=
    summable_squareBlockLift_of_successorSquareWeightedTerm
      hsquareNonneg (by linarith) hSquareAt
  have hLiftReal : Summable
      (realDirichletWeightedTerm
        (upperSquareLiftCoefficient squareExcess) (1 + alpha)) := by
    simpa only [realDirichletWeightedTerm_upperSquareLiftCoefficient]
      using hBlock
  have hliftNonneg : ∀ n, 0 ≤ upperSquareLiftCoefficient squareExcess n := by
    intro n
    rw [upperSquareLiftCoefficient]
    split_ifs
    · exact le_rfl
    · exact hsquareNonneg _
  have hLift : LSeriesSummable
      (fun n => (((upperSquareLiftCoefficient squareExcess n : ℝ) : ℂ)))
      (((1 + alpha : ℝ) : ℂ)) :=
    LSeriesSummable_of_realDirichletWeightedTerm_summable
      hliftNonneg hLiftReal
  let delta : ℝ := alpha / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  obtain ⟨D, hD, hmajor⟩ :=
    exists_dyadicWeightedPrimeWindowPositiveExcess_upperSquare_powerMajorant
      hdelta
  have hpower : LSeriesSummable
      (fun n => ((powerCorrectionCoefficient delta n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)) := by
    apply powerCorrectionCoefficient_LSeriesSummable
    simp only [Complex.ofReal_re]
    dsimp only [delta]
    linarith
  have hadd := hLift.add (hpower.smul (D : ℂ))
  have hmajorSummable : LSeriesSummable
      (fun n => (((upperSquareLiftCoefficient squareExcess n +
        D * powerCorrectionCoefficient delta n : ℝ) : ℂ)))
      (((1 + alpha : ℝ) : ℂ)) := by
    change Summable (LSeries.term _ (((1 + alpha : ℝ) : ℂ)))
    change Summable (LSeries.term _ (((1 + alpha : ℝ) : ℂ))) at hadd
    apply hadd.congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        ofReal_add, ofReal_mul]
  apply LSeriesSummable_of_nonneg_of_le
    dyadicWeightedPrimeWindowPositiveExcess_nonneg
    (fun n => add_nonneg (hliftNonneg n)
      (mul_nonneg hD (powerCorrectionCoefficient_nonneg delta n)))
  · intro n
    simpa only [squareExcess] using hmajor n
  · exact hmajorSummable

/-- L-series form of the fixed-abscissa square-to-full transfer. -/
theorem dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareLSeriesEnergy
    {alpha : ℝ} (halpha : 0 < alpha)
    (hSquare : LSeriesSummable
      (fun m => ((dyadicWeightedPrimeWindowPositiveExcess (m ^ 2) : ℝ) : ℂ))
      (((1 + 2 * alpha : ℝ) : ℂ))) :
    LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)) := by
  apply dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareEnergy
    halpha
  exact realDirichletWeightedTerm_summable_of_LSeriesSummable
    (fun m => dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2)) hSquare

/-- Hilbert-space form of the fixed-abscissa square-to-full transfer.  Weighted `L²` energy at
the square apertures, with the same exact exponent doubling, already gives absolute convergence
of the full positive-excess Dirichlet series. -/
theorem dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareSquareEnergy
    {alpha : ℝ} (halpha : 0 < alpha)
    (hSquare : Summable
      (realDirichletWeightedTerm
        (fun m => (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2)
        (1 + 2 * alpha))) :
    LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)) := by
  let squareExcess : ℕ → ℝ := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)
  have hsquareNonneg : ∀ m, 0 ≤ squareExcess m := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2)
  have hcomplex : LSeriesSummable
      (fun m => ((squareExcess m : ℝ) : ℂ))
      (((1 + 2 * alpha : ℝ) : ℂ)) :=
    LSeriesSummable_of_squareWeightedTerm_summable hsquareNonneg
      (by linarith) (by simpa only [squareExcess] using hSquare)
  have hlinear : Summable
      (realDirichletWeightedTerm squareExcess (1 + 2 * alpha)) :=
    realDirichletWeightedTerm_summable_of_LSeriesSummable
      hsquareNonneg hcomplex
  apply dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareEnergy
    halpha
  simpa only [squareExcess] using hlinear

/-- Natural square-sample form of the critical energy criterion. It is enough that, for every
positive `epsilon`, the series
`sum_m E(m^2) / m^(1+epsilon)` converges, where `E` is the positive excess above the exact
dyadic square-root main term. -/
theorem riemannHypothesis_of_squarePrimeWindowPositiveExcessEnergy
    (hSquare : ∀ epsilon : ℝ, 0 < epsilon →
      Summable
        (realDirichletWeightedTerm
          (fun m => dyadicWeightedPrimeWindowPositiveExcess (m ^ 2))
          (1 + epsilon))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_successorSquarePrimeWindowPositiveExcessEnergy
  intro epsilon hepsilon
  apply summable_successorSquareWeightedTerm_of_weightedTerm
    (fun m => dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2))
    (by linarith)
  exact hSquare epsilon hepsilon

/-- Hilbert-space predecessor of the square-sample criterion. Weighted square energy of the
positive excess only at perfect-square apertures implies RH. -/
theorem riemannHypothesis_of_squarePrimeWindowPositiveExcessSquareEnergy
    (hSquare : ∀ epsilon : ℝ, 0 < epsilon →
      Summable
        (realDirichletWeightedTerm
          (fun m => (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2)
          (1 + epsilon))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_squarePrimeWindowPositiveExcessEnergy
  intro epsilon hepsilon
  let squareExcess : ℕ → ℝ := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)
  have hnonneg : ∀ m, 0 ≤ squareExcess m := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2)
  have hcomplex : LSeriesSummable
      (fun m => ((squareExcess m : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) :=
    LSeriesSummable_of_squareWeightedTerm_summable hnonneg
      (by linarith) (by simpa only [squareExcess] using hSquare epsilon hepsilon)
  exact realDirichletWeightedTerm_summable_of_LSeriesSummable hnonneg hcomplex

/-- Cesaro form of the square-sample criterion. It is enough that the cumulative positive excess
on square apertures have every superlinear power as an upper bound. -/
theorem riemannHypothesis_of_squarePrimeWindowCumulativePositiveExcessGrowth
    (hGrowth : ∀ delta : ℝ, 0 < delta →
      (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
        dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) =O[Filter.atTop]
          (fun M : ℕ => (M : ℝ) ^ (1 + delta))) :
    RiemannHypothesis := by
  let squareExcess : ℕ → ℝ := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)
  have hsquareNonneg : ∀ m, 0 ≤ squareExcess m := fun m =>
    dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2)
  have hAbscissa :
      LSeries.abscissaOfAbsConv (fun m => ((squareExcess m : ℝ) : ℂ)) ≤
        ((1 : ℝ) : EReal) := by
    apply (abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
      hsquareNonneg zero_le_one).mpr
    exact hGrowth
  apply riemannHypothesis_of_squarePrimeWindowPositiveExcessEnergy
  intro epsilon hepsilon
  have hstrict :
      LSeries.abscissaOfAbsConv (fun m => ((squareExcess m : ℝ) : ℂ)) <
        (((1 + epsilon : ℝ)) : EReal) := by
    apply hAbscissa.trans_lt
    exact_mod_cast (by linarith : (1 : ℝ) < 1 + epsilon)
  have hsum : Summable (fun m : ℕ =>
      squareExcess m / (m : ℝ) ^ (1 + epsilon)) :=
    LSeries.summable_real_of_abscissaOfAbsConv_lt hstrict
  apply hsum.congr
  intro m
  by_cases hm : m = 0
  · subst m
    have hexp : 0 < 1 + epsilon := by linarith
    simp [realDirichletWeightedTerm, Real.zero_rpow hexp.ne']
  · simp [realDirichletWeightedTerm, squareExcess, hm]

/-- Completed-error form of the square-sample criterion. Only the positive backward `log 2`
variation at square logarithmic samples needs critical Dirichlet energy. -/
theorem riemannHypothesis_of_squareCompletedErrorBackwardPositiveVariationEnergy
    (hSquare : ∀ epsilon : ℝ, 0 < epsilon →
      Summable
        (realDirichletWeightedTerm
          (fun m => dyadicCompletedErrorBackwardPositiveVariation (m ^ 2))
          (1 + epsilon))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_squarePrimeWindowPositiveExcessEnergy
  intro epsilon hepsilon
  simpa only [dyadicCompletedErrorBackwardPositiveVariation_eq_positiveExcess] using
    hSquare epsilon hepsilon

end RHTower
