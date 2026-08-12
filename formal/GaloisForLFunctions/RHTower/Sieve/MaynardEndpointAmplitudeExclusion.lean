import GaloisForLFunctions.RHTower.Sieve.MaynardEndpointMass

/-!
# Near-one exclusion from endpoint-long factor deficits

This module composes the `19/20` endpoint mass law with exact fixed-abscissa amplitude cells.  A
uniform local deficit `Delta` on every factor above Maynard's relative cutoff forces global product
deficit `(19/20)Delta`, minus only the literal logarithmic atom's exact slack mass.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- Maynard's constants close exactly: local deficit `3η/2` on `19/20` of logarithmic mass leaves
`57η/40`; after paying slack `17η/40`, one full global `η` remains. -/
theorem maynard_endpoint_three_halves_deficit_closes
    {alpha eta E : ℝ}
    (hglobal : alpha ≤
      1 - ((19 / 20 : ℝ) * ((3 / 2 : ℝ) * eta) - E))
    (hslack : E ≤ (17 / 40 : ℝ) * eta) :
    alpha ≤ 1 - eta := by
  linarith

/-- **Literal endpoint amplitude exclusion.**  It is enough to control every positive-length box
factor carrying at least `1/(40k)` of total logarithmic mass.  No single distinguished factor is
chosen. -/
theorem maynard_heathBrownBox_endpoint_long_deficits_trimmed
    {L X k : ℕ} (hk : 0 < k) (box : HeathBrownBoxChoice L X k)
    (hL : 1 ≤ L) (hX : 1 ≤ X)
    {T0 c y alpha Delta E : ℝ}
    (hT0 : 1 < T0) (hc : 0 ≤ c) (hDelta : 0 ≤ Delta)
    (hlong : ∀ j : PositiveHeathBrownBoxFactorIndex box,
      (∑ i : PositiveHeathBrownBoxFactorIndex box,
          dyadicLogExponent T0
            (heathBrownBoxFactorExponent box.a box.b box.q i)) /
            (40 * k : ℕ) ≤
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent box.a box.b box.q j) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X k box
              ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
        1 - Delta)
    (hslackMass :
      ∑ i : HeathBrownBoxFactorIndex k box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        E * Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ))
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖) :
    alpha ≤ 1 - ((19 / 20 : ℝ) * Delta - E) := by
  classical
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  have hlog : 1 ≤ box.q :=
    heathBrownBox_log_exponent_pos_of_large_core box s (by simpa [s] using hlarge)
  let I := PositiveHeathBrownBoxFactorIndex box
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent box.a box.b box.q i
  let kind : I → HeathBrownFactorKind := fun i =>
    heathBrownBoxFactorKind k box.m i
  let N : I → ℝ := fun i => (((2 ^ q i : ℕ) : ℝ))
  let Z : I → ℂ := fun i => heathBrownBoxFactorValue L X k box s i
  let W : I → ℝ := fun i => ‖Z i‖
  let slack : I → ℝ := fun i => heathBrownFactorAmplitudeSlack (kind i) (q i)
  let w : I → ℝ := fun i => dyadicLogExponent T0 (q i)
  let u : Finset I := Finset.univ.filter fun i =>
    (∑ j : I, w j) / (40 * k : ℕ) ≤ w i
  let logIndex : I := ⟨Sum.inr (Sum.inr ()), hlog⟩
  letI : Nonempty I := ⟨logIndex⟩
  have hN : ∀ i, 1 < N i := by
    intro i
    dsimp [N, q]
    exact_mod_cast (show 1 < 2 ^
        heathBrownBoxFactorExponent box.a box.b box.q
          (i : HeathBrownBoxFactorIndex k box.m) by
      exact pow_lt_pow_right₀ (by norm_num) i.property)
  have hNprod : (∏ i, N i) =
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    change (∏ i : I, (((2 ^ q i : ℕ) : ℝ))) =
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
    norm_cast
    exact prod_positive_heathBrownBoxFactorLength_eq_groupedLower box
  have hZprod : (∏ i, Z i) =
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s := by
    simpa [Z, I] using
      prod_positive_heathBrownBoxFactorValue_eq_core box hL hX hlog s
  have hWprod : (∏ i, W i) =
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ := by
    rw [← hZprod]
    simp [W]
  have hNprodPos : 0 < ∏ i, N i :=
    Finset.prod_pos fun i _ => (hN i).trans' zero_lt_one
  have hthreshold : 0 < (∏ i, N i) ^ (alpha - c) :=
    Real.rpow_pos_of_pos hNprodPos _
  have hWprodPos : 0 < ∏ i, W i := by
    rw [hWprod]
    exact hthreshold.trans_le (by simpa [hNprod, s] using hlarge)
  have hW : ∀ i, 0 < W i := by
    intro i
    by_contra hi
    have hi0 : W i = 0 := le_antisymm (le_of_not_gt hi) (norm_nonneg _)
    have hzero : ∏ r, W r = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi0
    rw [hzero] at hWprodPos
    exact (lt_irrefl 0) hWprodPos
  have hslack : ∀ i, 0 ≤ slack i := by
    intro i
    exact heathBrownFactorAmplitudeSlack_nonneg (kind i) i.property
  have hall : ∀ i, maynardAmplitude c (N i) (W i) ≤ 1 + slack i := by
    intro i
    exact maynard_heathBrownFactor_amplitude_le_one_add_slack
      L X (q i) (kind i) hc i.property (hW i)
  have hu : ∀ i ∈ u, maynardAmplitude c (N i) (W i) ≤ 1 - Delta := by
    intro i hi
    apply hlong i
    simpa [u, w, q] using (Finset.mem_filter.mp hi).2
  have hw : ∀ i, 0 ≤ w i := fun i => dyadicLogExponent_nonneg hT0 (q i)
  have hm : box.m < k := box.1.isLt
  have hcardOriginal : Fintype.card (HeathBrownBoxFactorIndex k box.m) ≤ 2 * k := by
    rw [card_heathBrownBoxFactorIndex hm]
    omega
  have hcardI : Fintype.card I ≤
      Fintype.card (HeathBrownBoxFactorIndex k box.m) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hcard : Fintype.card I ≤ 2 * k := hcardI.trans hcardOriginal
  have hmass := nineteen_twentieths_total_le_sum_endpoint_long_weights
    k hk w hw hcard
  have hlogNw : ∀ i, Real.log (N i) = w i * Real.log T0 := by
    intro i
    have hr := rpow_dyadicLogExponent hT0 (q i)
    calc
      Real.log (N i) = Real.log (T0 ^ w i) := by rw [hr]
      _ = w i * Real.log T0 := by rw [Real.log_rpow (by linarith)]
  have hlogMass : (19 / 20 : ℝ) * ∑ i, Real.log (N i) ≤
      ∑ i ∈ u, Real.log (N i) := by
    have hmulg := mul_le_mul_of_nonneg_right hmass (Real.log_nonneg hT0.le)
    simp_rw [hlogNw]
    calc
      (19 / 20 : ℝ) * ∑ i, w i * Real.log T0 =
          ((19 / 20 : ℝ) * ∑ i, w i) * Real.log T0 := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ (∑ i ∈ u, w i) * Real.log T0 := by simpa [u] using hmulg
      _ = ∑ i ∈ u, w i * Real.log T0 := by rw [Finset.sum_mul]
  have hlogTotal : Real.log (∏ i, N i) = ∑ i, Real.log (N i) :=
    Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i)))
  have hlengthMass : (19 / 20 : ℝ) * Real.log (∏ i, N i) ≤
      ∑ i ∈ u, Real.log (N i) := by
    rw [hlogTotal]
    exact hlogMass
  have hslackMass' : ∑ i, slack i * Real.log (N i) ≤
      E * Real.log (∏ i, N i) := by
    rw [hNprod]
    have htrim := sum_positive_heathBrownBoxFactorAmplitudeSlack_eq box hlog
    calc
      ∑ i, slack i * Real.log (N i) =
          ∑ i : HeathBrownBoxFactorIndex k box.m,
            heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i) *
              Real.log
                (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) := by
          simpa [slack, N, q, kind, I] using htrim
      _ ≤ E * Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := hslackMass
  apply maynard_product_threshold_subset_deficit_with_log_slack
    N W slack u hN hW hDelta hslack hall hu hlengthMass hslackMass'
  rw [hNprod, hWprod]
  simpa [s] using hlarge

end RHTower.Sieve
