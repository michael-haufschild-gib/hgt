import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeCells
import GaloisForLFunctions.RHTower.Sieve.MaynardZeroExponentTrimming

/-!
# Amplitude rigidity after exact length-one trimming

This module applies the actual-amplitude weighted-mean argument to the positive-length subtype of
a literal Heath--Brown box.  It removes the false requirement that every original dyadic exponent
be positive.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- Exponent-zero atoms carry zero logarithmic slack mass, so trimming preserves total slack. -/
theorem sum_positive_heathBrownBoxFactorAmplitudeSlack_eq
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) (hlog : 1 ≤ box.q) :
    (∑ i : PositiveHeathBrownBoxFactorIndex box,
      heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
          (heathBrownBoxFactorExponent box.a box.b box.q i) *
        Real.log (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))) =
      ∑ i : HeathBrownBoxFactorIndex k box.m,
        heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
          Real.log
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) := by
  classical
  let q : HeathBrownBoxFactorIndex k box.m → ℕ :=
    heathBrownBoxFactorExponent box.a box.b box.q
  let f : HeathBrownBoxFactorIndex k box.m → ℝ := fun i =>
    heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i) (q i) *
      Real.log (((2 ^ q i : ℕ) : ℝ))
  let u : Finset (HeathBrownBoxFactorIndex k box.m) :=
    Finset.univ.filter fun i => 1 ≤ q i
  have hu (i : HeathBrownBoxFactorIndex k box.m) : i ∈ u ↔ 1 ≤ q i := by
    simp [u]
  have hreindex := Finset.sum_subtype
    (F := Subtype.fintype fun i : HeathBrownBoxFactorIndex k box.m => 1 ≤ q i)
    u hu f
  calc
    (∑ i : PositiveHeathBrownBoxFactorIndex box,
        heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
          Real.log
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))) =
        ∑ i ∈ u, f i := by
          simpa [PositiveHeathBrownBoxFactorIndex, q, f] using hreindex.symm
    _ = ∑ i : HeathBrownBoxFactorIndex k box.m, f i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _hi hiu
      have hqi : q i = 0 := by
        have : ¬ 1 ≤ q i := by simpa [u] using hiu
        omega
      rcases i with i | i
      · simp [f, q, heathBrownBoxFactorKind, heathBrownFactorAmplitudeSlack]
      · rcases i with i | i
        · simp [f, q, heathBrownBoxFactorKind, heathBrownFactorAmplitudeSlack]
        · rcases i with ⟨⟩
          simp [q, heathBrownBoxFactorExponent] at hqi
          omega
    _ = ∑ i : HeathBrownBoxFactorIndex k box.m,
        heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
          Real.log
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) := by
      rfl

/-- **Literal box amplitude exclusion with length-one atoms removed exactly.** -/
theorem maynard_heathBrownBox_threshold_one_factor_deficit_trimmed
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (hL : 1 ≤ L) (hX : 1 ≤ X)
    {c y alpha ell Delta E : ℝ}
    (hc : 0 ≤ c) (hDelta : 0 ≤ Delta)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hjpos : 1 ≤ heathBrownBoxFactorExponent box.a box.b box.q j)
    (hj : maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖heathBrownBoxFactorValue L X k box
            ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤ 1 - Delta)
    (hlength :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ ell ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
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
    alpha ≤ 1 - (ell * Delta - E) := by
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
  let jp : I := ⟨j, hjpos⟩
  letI : Nonempty I := ⟨jp⟩
  have hN : ∀ i, 1 < N i := by
    intro i
    dsimp [N, q]
    exact_mod_cast (show 1 < 2 ^
        heathBrownBoxFactorExponent box.a box.b box.q (i : HeathBrownBoxFactorIndex k box.m) by
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
  apply maynard_product_threshold_one_factor_deficit_with_log_slack
    N W slack jp hN hW hDelta hslack hall
  · simpa [jp, N, W, Z, q, s] using hj
  · rw [hNprod]
    simpa [jp, N, q] using hlength
  · rw [hNprod]
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
  · rw [hNprod, hWprod]
    simpa [s] using hlarge

end RHTower.Sieve
