import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePositiveCoreOfTheDilationForm
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheWorkIsACorrelationWithWindowMeans

/-!
# The complete accounting of the work

Splitting the dilation form at the constant row leaves four pieces, and three of them can be named.

* The **core** `Q_ε(1) = Σ_{n ≤ T} ψ_ε(n)/(n(n+1))` is explicit and positive, with
  `ψ_ε(n) = Σ_{j ≤ n} Λ(j) j^{-ε}` the damped Chebyshev prefix.
* One **cross term** is the pairing of the deviation with that same prefix:
  `B_ε(v, 1) = ⟪v, ψ_ε⟫_T` (`rowDilationPairing_right_one`) — a classical weighted prime sum
  against the deviation.
* The other **cross term** is the pairing of the deviation with the prime-weighted window means of
  the constant row (`rowDilationPairing_left_one`), again an explicit row.
* The **quadratic** piece is the deviation's own dilation form, and the sharp pronic contraction
  bounds it by the explicit prime-dilation series times the deviation's energy:
  `|Q_ε(v)| ≤ (Σ_{j ≤ T} Λ(j) j^{-ε}/√j) ‖v‖_T²` (`abs_rowDilationForm_le`).

So the whole signed work is accounted for: an explicit positive core, two explicit linear
functionals of the deviation, one quadratic term controlled by the deviation's energy through the
dilation series, and the explicit polar correction
(`signedDampingWork_accounting`).  Since subtracting the constant source changes neither admission
nor the continuation demand, the quadratic term is the only unpaid one — and it is quadratic in a
quantity that vanishes with the deviation from constancy.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The two cross terms are explicit -/

/-- The dilation of the constant row is the damped Chebyshev prefix. -/
theorem rowDilationPairing_right_one (ε : ℝ) (T : ℕ) (u : ℕ → ℝ) :
    rowDilationPairing ε T u (fun _ => 1) = pronicPairing T u (dampedPrimePrefix ε) := by
  simp only [rowDilationPairing, pronicPairing]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hsum : (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * (1 : ℝ)) = dampedPrimePrefix ε n := by
    rw [dampedPrimePrefix]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]

/-- The left cross term is the pairing against the prime-weighted window means of the constant
row. -/
theorem rowDilationPairing_left_one (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    rowDilationPairing ε T (fun _ => 1) v =
      ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j *
        pronicPairing T (rowFibreAverage j T (fun _ => 1)) v := by
  have hext : ∀ n ∈ Icc 1 T,
      (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) =
      ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * rowDilate j v n := by
    intro n hn
    rw [mem_Icc] at hn
    have hsub : (Icc 1 n : Finset ℕ) ⊆ Icc 1 T := by
      intro j hj
      rw [mem_Icc] at hj ⊢
      exact ⟨hj.1, hj.2.trans hn.2⟩
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun j _ => by rw [rowDilate]
    · intro j hjT hjn
      rw [mem_Icc] at hjT hjn
      have hjn' : n < j := by
        by_contra hcon
        exact hjn ⟨hjT.1, by omega⟩
      rw [rowDilate, Nat.div_eq_of_lt hjn', hv0]
      ring
  have hstep : rowDilationPairing ε T (fun _ => 1) v =
      ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * pronicPairing T (fun _ => 1) (rowDilate j v) := by
    unfold rowDilationPairing pronicPairing
    have hcell : ∀ n ∈ Icc 1 T,
        (1 : ℝ) * (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) /
            ((n : ℝ) * ((n : ℝ) + 1)) =
          ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j *
            ((1 : ℝ) * rowDilate j v n / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      rw [one_mul, hext n hn, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl hcell, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [hstep]
  exact Finset.sum_congr rfl fun j _ => by
    rw [pronicPairing_rowDilate_eq j T (fun _ => 1) v hv0]

/-! ## §2. The quadratic piece is controlled by the dilation series -/

/-- **The quadratic piece is bounded by the prime-dilation series times the energy.** -/
theorem abs_rowDilationForm_le (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    |rowDilationForm ε T v| ≤
      (∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ))) *
        pronicNorm T v ^ 2 := by
  have hv : pronicNorm T v ^ 2 = pronicNorm T v * pronicNorm T v := by ring
  have hS : 0 ≤ ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ)) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have h1 : 0 ≤ ArithmeticFunction.vonMangoldt j := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (0 : ℝ) ≤ (j : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg j) _
    have h3 : (0 : ℝ) ≤ 1 / Real.sqrt (j : ℝ) := by positivity
    rw [dampedPrimeWeight]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  -- the dilated row is bounded in the pronic norm by the series
  have hnorm : pronicNorm T (fun n => ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) ≤
      (∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ))) * pronicNorm T v := by
    have hext : ∀ n ∈ Icc 1 T,
        (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) =
        ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * rowDilate j v n := by
      intro n hn
      rw [mem_Icc] at hn
      have hsub : (Icc 1 n : Finset ℕ) ⊆ Icc 1 T := by
        intro j hj
        rw [mem_Icc] at hj ⊢
        exact ⟨hj.1, hj.2.trans hn.2⟩
      rw [← Finset.sum_subset hsub]
      · exact Finset.sum_congr rfl fun j _ => by rw [rowDilate]
      · intro j hjT hjn
        rw [mem_Icc] at hjT hjn
        have hjn' : n < j := by
          by_contra hcon
          exact hjn ⟨hjT.1, by omega⟩
        rw [rowDilate, Nat.div_eq_of_lt hjn', hv0]
        ring
    rw [pronicNorm_congr hext]
    refine (pronicNorm_sum_le T (Icc 1 T)
      (fun j n => dampedPrimeWeight ε j * rowDilate j v n)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hw : (0 : ℝ) ≤ dampedPrimeWeight ε j := by
      rw [dampedPrimeWeight]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg j) _)
    rw [pronicNorm_const_mul hw, mul_assoc]
    exact mul_le_mul_of_nonneg_left (pronicNorm_rowDilate_le_sharp hj1 T v hv0) hw
  -- Cauchy–Schwarz for the form
  have hcs : |rowDilationForm ε T v| ≤ pronicNorm T v *
      pronicNorm T (fun n => ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) := by
    have hpos := sum_mul_div_le_pronicNorm T v
      (fun n => ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j))
    have hneg := sum_mul_div_le_pronicNorm T v
      (fun n => -∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j))
    rw [pronicNorm_neg] at hneg
    have hform : rowDilationForm ε T v =
        ∑ n ∈ Icc 1 T, v n * (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) /
          ((n : ℝ) * ((n : ℝ) + 1)) := rfl
    have hnegform : (∑ n ∈ Icc 1 T, v n * (-∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) /
        ((n : ℝ) * ((n : ℝ) + 1))) = -rowDilationForm ε T v := by
      rw [hform, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hnegform] at hneg
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hnonneg := pronicNorm_nonneg T v
  calc |rowDilationForm ε T v|
      ≤ pronicNorm T v *
        pronicNorm T (fun n => ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) := hcs
    _ ≤ pronicNorm T v *
        ((∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ))) *
          pronicNorm T v) := mul_le_mul_of_nonneg_left hnorm hnonneg
    _ = (∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ))) *
        pronicNorm T v ^ 2 := by rw [hv]; ring

/-! ## §3. Congruence on the observed range -/

/-- The dilation form only sees the horizons in `[1, T]`. -/
theorem rowDilationForm_congr {ε : ℝ} {T : ℕ} {u v : ℕ → ℝ} (h : ∀ n ∈ Icc 1 T, u n = v n) :
    rowDilationForm ε T u = rowDilationForm ε T v := by
  unfold rowDilationForm
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := mem_Icc.mp hn
  have hinner : (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * u (n / j)) =
      ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := mem_Icc.mp hj
    have hmem : n / j ∈ Icc 1 T :=
      mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr hj'.2,
        le_trans (Nat.div_le_self n j) hn'.2⟩
    rw [h _ hmem]
  rw [hinner, h n hn]

/-- The bilinear dilation pairing only sees the horizons in `[1, T]`. -/
theorem rowDilationPairing_congr_right {ε : ℝ} {T : ℕ} {u v w : ℕ → ℝ}
    (h : ∀ n ∈ Icc 1 T, v n = w n) :
    rowDilationPairing ε T u v = rowDilationPairing ε T u w := by
  simp only [rowDilationPairing, pronicPairing]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := mem_Icc.mp hn
  have hinner : (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) =
      ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * w (n / j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := mem_Icc.mp hj
    have hmem : n / j ∈ Icc 1 T :=
      mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr hj'.2,
        le_trans (Nat.div_le_self n j) hn'.2⟩
    rw [h _ hmem]
  rw [hinner]

theorem pronicPairing_congr_left {T : ℕ} {u v w : ℕ → ℝ} (h : ∀ n ∈ Icc 1 T, u n = v n) :
    pronicPairing T u w = pronicPairing T v w := by
  unfold pronicPairing
  exact Finset.sum_congr rfl fun n hn => by rw [h n hn]

/-! ## §4. The accounting -/

/-- The deviation of the source from the constant one, extended by zero at the origin. -/
def deviationRow (ε : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else pmPowerDampedCenteredDivisorPrefix ε n - 1

theorem deviationRow_zero (ε : ℝ) : deviationRow ε 0 = 0 := by rw [deviationRow, if_pos rfl]

theorem deviationRow_eq {ε : ℝ} {T : ℕ} : ∀ n ∈ Icc 1 T,
    deviationRow ε n = pmPowerDampedCenteredDivisorPrefix ε n - 1 := by
  intro n hn
  rw [deviationRow, if_neg (by have := (mem_Icc.mp hn).1; omega : n ≠ 0)]

/-- **The complete accounting of the signed work.**  Explicit positive core, two explicit linear
functionals of the deviation, one quadratic term in the deviation, and the polar correction. -/
theorem signedDampingWork_accounting (ε : ℝ) (T : ℕ) :
    signedDampingWork ε T =
      (∑ n ∈ Icc 1 T, dampedPrimePrefix ε n / ((n : ℝ) * ((n : ℝ) + 1))) +
        (∑ j ∈ Icc 1 T, dampedPrimeWeight ε j *
          pronicPairing T (rowFibreAverage j T (fun _ => 1)) (deviationRow ε)) +
        pronicPairing T (deviationRow ε) (dampedPrimePrefix ε) +
        rowDilationForm ε T (deviationRow ε) +
        polarDilationCorrection ε T := by
  rw [signedDampingWork_split_at_one, rowDilationForm_one_eq, rowDilationPairing_right_one,
    rowDilationPairing_congr_right (ε := ε) (T := T) (u := fun _ => 1)
      (v := fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) (w := deviationRow ε)
      (fun n hn => (deviationRow_eq n hn).symm),
    rowDilationPairing_left_one ε T (deviationRow ε) (deviationRow_zero ε),
    pronicPairing_congr_left (T := T)
      (u := fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) (v := deviationRow ε)
      (w := dampedPrimePrefix ε) (fun n hn => (deviationRow_eq n hn).symm),
    rowDilationForm_congr (ε := ε) (T := T)
      (u := fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) (v := deviationRow ε)
      (fun n hn => (deviationRow_eq n hn).symm)]

/-- **The quadratic term is controlled by the deviation's energy.** -/
theorem abs_rowDilationForm_deviationRow_le (ε : ℝ) (T : ℕ) :
    |rowDilationForm ε T (deviationRow ε)| ≤
      (∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ))) *
        pronicNorm T (deviationRow ε) ^ 2 :=
  abs_rowDilationForm_le ε T (deviationRow ε) (deviationRow_zero ε)

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
