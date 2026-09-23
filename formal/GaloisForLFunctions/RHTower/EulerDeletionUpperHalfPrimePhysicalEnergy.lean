import GaloisForLFunctions.RHTower.EulerDeletionUpperHalfPrimePhysicalSuppression

/-!
Physical beta integral and harmonic-fibre energy for the literal upper-half prime
packet. The pointwise estimate is already in UpperHalfPrimePhysicalSuppression.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory
open scoped Interval
namespace RHTower.DeletionPrimeWindowPhase

def upperHalfPrimePacketKernel (N L p r : ℕ) (x : ℝ) : ℝ :=
  x ^ r *
    (x ^ DeletionResidueMartingale.clock L *
      (1 - x ^ DeletionResidueMartingale.clock L) *
      DeletionResidueMartingale.clockResidualBetaWeight L (r + 1)
        (DeletionResidueMartingale.canonicalClockRatio N L - 1) x p /
        ((1 - x ^ DeletionResidueMartingale.clock N) *
          (∑ a ∈ range (DeletionResidueMartingale.clock L), x ^ a)))

theorem upperHalfPrimePacketKernel_abs_le_on_Icc
    (N L p r : ℕ) (hLN : L ≤ N) (hp : p.Prime)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |upperHalfPrimePacketKernel N L p r x| ≤
      x ^ r * (DeletionResidueMartingale.clock L : ℝ)⁻¹ := by
  rcases hx with ⟨hx0, hx1⟩
  rcases eq_or_lt_of_le hx1 with hxeq | hxlt
  · subst x
    simp [upperHalfPrimePacketKernel]
  · exact upper_half_prime_packet_kernel_abs_le N L p r x hLN hp hx0 hxlt

theorem upperHalfPrimePacketKernel_integral_abs_le
    (N L p r : ℕ) (hLN : L ≤ N) (hp : p.Prime) :
    |∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x| ≤
      1 / ((DeletionResidueMartingale.clock L : ℝ) * (r + 1)) := by
  have hbound : ∀ᵐ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 →
      ‖upperHalfPrimePacketKernel N L p r x‖ ≤
        x ^ r * (DeletionResidueMartingale.clock L : ℝ)⁻¹ := by
    filter_upwards [] with x hx
    rw [Real.norm_eq_abs]
    exact upperHalfPrimePacketKernel_abs_le_on_Icc N L p r hLN hp ⟨hx.1.le, hx.2⟩
  have hgintegrable : IntervalIntegrable
      (fun x : ℝ => x ^ r * (DeletionResidueMartingale.clock L : ℝ)⁻¹)
      volume 0 1 :=
    ((continuous_id.pow r).mul continuous_const).intervalIntegrable _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le (by norm_num) hbound hgintegrable
  rw [Real.norm_eq_abs] at h
  calc
    |∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x| ≤
        ∫ x in (0 : ℝ)..1,
          x ^ r * (DeletionResidueMartingale.clock L : ℝ)⁻¹ := h
    _ = 1 / ((DeletionResidueMartingale.clock L : ℝ) * (r + 1)) := by
      rw [intervalIntegral.integral_mul_const, integral_pow]
      simp only [one_pow, zero_pow (Nat.succ_ne_zero r), sub_zero]
      simp only [one_div, mul_inv_rev]

private theorem harmonic_fibre_energy_atom
    {C R m A : ℝ} (hC : 0 < C) (hR : 1 ≤ R)
    (hm : 1 / (R * (R + 1)) ≤ m)
    (hA : |A| ≤ 1 / (C * R)) :
    A ^ 2 / m ≤ 2 / C ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hR1 : 0 < R + 1 := by linarith
  have hm0 : 0 < m :=
    (one_div_pos.mpr (mul_pos hR0 hR1)).trans_le hm
  have hA2 : A ^ 2 ≤ (1 / (C * R)) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg A) (one_div_nonneg.mpr (mul_pos hC hR0).le)).mpr hA
  calc
    A ^ 2 / m ≤ (1 / (C * R)) ^ 2 / m :=
      div_le_div_of_nonneg_right hA2 hm0.le
    _ ≤ (1 / (C * R)) ^ 2 / (1 / (R * (R + 1))) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (one_div_pos.mpr (mul_pos hR0 hR1)) hm
    _ = (R + 1) / (C ^ 2 * R) := by field_simp
    _ ≤ 2 / C ^ 2 := by
      apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hC) hR0) (sq_pos_of_pos hC)).2
      have hR2 : R + 1 ≤ 2 * R := by linarith
      calc
        (R + 1) * C ^ 2 ≤ (2 * R) * C ^ 2 :=
          mul_le_mul_of_nonneg_right hR2 (sq_nonneg C)
        _ = 2 * (C ^ 2 * R) := by ring

theorem physicalFibre_mass_ge_cellWeight (L r : ℕ)
    (hr : r < DeletionResidueMartingale.clock L) :
    DeletionResidueMartingale.cellWeight r ≤
      DeletionResidueMartingale.cellMeasure.real
        (DeletionResidueMartingale.historyFibre L r) := by
  rw [← DeletionResidueMartingale.cellMeasure_singleton r]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro j hj
  have hjr : j = r := by simpa only [Set.mem_singleton_iff] using hj
  subst j
  simp only [DeletionResidueMartingale.historyFibre, Set.mem_setOf_eq]
  exact Nat.mod_eq_of_lt hr

theorem upperHalfPrimePacketKernel_physical_fibre_energy_le
    (N L p : ℕ) (hLN : L ≤ N) (hp : p.Prime) :
    (∑ r ∈ range (DeletionResidueMartingale.clock L),
        (∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x) ^ 2 /
          DeletionResidueMartingale.cellMeasure.real
            (DeletionResidueMartingale.historyFibre L r)) ≤
      2 / (DeletionResidueMartingale.clock L : ℝ) := by
  let C := DeletionResidueMartingale.clock L
  have hC : 0 < C := DeletionResidueMartingale.clock_pos L
  have hCReal : (0 : ℝ) < C := Nat.cast_pos.mpr hC
  calc
    (∑ r ∈ range C,
        (∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x) ^ 2 /
          DeletionResidueMartingale.cellMeasure.real
            (DeletionResidueMartingale.historyFibre L r)) ≤
      ∑ _r ∈ range C, 2 / (C : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        have hr' : r < C := Finset.mem_range.mp hr
        have hmass :
            1 / (((r : ℝ) + 1) * (((r : ℝ) + 1) + 1)) ≤
              DeletionResidueMartingale.cellMeasure.real
                (DeletionResidueMartingale.historyFibre L r) := by
          simpa [DeletionResidueMartingale.cellWeight, add_assoc, one_add_one_eq_two] using
            physicalFibre_mass_ge_cellWeight L r hr'
        have hA :
            |∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x| ≤
              1 / ((C : ℝ) * ((r : ℝ) + 1)) := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            upperHalfPrimePacketKernel_integral_abs_le N L p r hLN hp
        exact harmonic_fibre_energy_atom (C := (C : ℝ)) (R := (r : ℝ) + 1)
          hCReal (by have := Nat.cast_nonneg (α := ℝ) r; linarith) hmass hA
    _ = 2 / (C : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

open DeletionResidueMartingale

/-- The upper-half physical EDQ block is its paired source endpoint plus literal prime packets. -/
theorem truncatedDivisorBlockKernel_eq_sourceEndpoint_add_upperHalfPrimePackets
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) (hN : N ≤ 2 * (l + 1)) :
    truncatedDivisorBlockKernel N l u b x =
      (x ^ (u + b * clock l) *
        ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l)) *
          (1 - x ^ clock N)⁻¹) /
        (∑ a ∈ range (clock (l + 1)), x ^ a) +
      ∑ p ∈ (Icc (l + 2) N).filter Nat.Prime,
        upperHalfPrimePacketKernel N (l + 1) p (u + b * clock l) x := by
  rw [truncatedDivisorBlockKernel_eq_source_prime_window_prefix_of_upper_half
    N l u b x hlN hN]
  simp_rw [moebius_divisor_betaPrefix_eq_clockResidualBetaWeight]
  simp_rw [upperHalfPrimePacketKernel, div_eq_mul_inv]
  simp only [mul_add, add_mul]
  congr 1
  calc
    x ^ (u + b * clock l) *
        (x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
          ∑ p ∈ (Icc (l + 2) N).filter Nat.Prime,
            clockResidualBetaWeight (l + 1) (u + b * clock l + 1)
              (canonicalClockRatio N (l + 1) - 1) x p) *
        (1 - x ^ clock N)⁻¹ *
          (∑ a ∈ range (clock (l + 1)), x ^ a)⁻¹ =
      ∑ p ∈ (Icc (l + 2) N).filter Nat.Prime,
        x ^ (u + b * clock l) *
          (x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
            clockResidualBetaWeight (l + 1) (u + b * clock l + 1)
              (canonicalClockRatio N (l + 1) - 1) x p) *
          (1 - x ^ clock N)⁻¹ *
            (∑ a ∈ range (clock (l + 1)), x ^ a)⁻¹ := by
        simp only [mul_sum, sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [mul_inv_rev]
      ring

/-- A literal prime packet is measurable and integrable on the physical beta interval. -/
theorem upperHalfPrimePacketKernel_measurable
    (N L p r : ℕ) (hp : p.Prime) :
    Measurable (upperHalfPrimePacketKernel N L p r) := by
  unfold upperHalfPrimePacketKernel
  simp_rw [clockResidualBetaWeight_prime_eq_neg_betaPacket L p (r + 1)
    (DeletionResidueMartingale.canonicalClockRatio N L - 1) _ hp]
  unfold betaPacket
  fun_prop

theorem upperHalfPrimePacketKernel_intervalIntegrable
    (N L p r : ℕ) (hLN : L ≤ N) (hp : p.Prime) :
    IntervalIntegrable (upperHalfPrimePacketKernel N L p r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  apply Measure.integrableOn_of_bounded
    (M := (DeletionResidueMartingale.clock L : ℝ)⁻¹) (by simp)
    (upperHalfPrimePacketKernel_measurable N L p r hp).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs]
  have h := upperHalfPrimePacketKernel_abs_le_on_Icc N L p r hLN hp ⟨hx.1.le, hx.2⟩
  calc
    |upperHalfPrimePacketKernel N L p r x| ≤
        x ^ r * (DeletionResidueMartingale.clock L : ℝ)⁻¹ := h
    _ ≤ (DeletionResidueMartingale.clock L : ℝ)⁻¹ := by
      have hxpow : x ^ r ≤ 1 := pow_le_one₀ hx.1.le hx.2
      simpa using mul_le_mul_of_nonneg_right hxpow
        (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) _))

/-- Finite prime-packet aggregation costs only the square of packet count. -/
theorem upperHalfPrimePackets_physical_fibre_energy_le
    (N L : ℕ) (P : Finset ℕ) (hLN : L ≤ N)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ r ∈ range (DeletionResidueMartingale.clock L),
        (∑ p ∈ P, ∫ x in (0 : ℝ)..1,
          upperHalfPrimePacketKernel N L p r x) ^ 2 /
          DeletionResidueMartingale.cellMeasure.real
            (DeletionResidueMartingale.historyFibre L r)) ≤
      2 * (P.card : ℝ) ^ 2 / (DeletionResidueMartingale.clock L : ℝ) := by
  let C := DeletionResidueMartingale.clock L
  have hC : (0 : ℝ) < C := Nat.cast_pos.mpr (DeletionResidueMartingale.clock_pos L)
  have hpoint (r : ℕ) (hr : r ∈ range C) :
      (∑ p ∈ P, ∫ x in (0 : ℝ)..1,
          upperHalfPrimePacketKernel N L p r x) ^ 2 /
          DeletionResidueMartingale.cellMeasure.real
            (DeletionResidueMartingale.historyFibre L r) ≤
        (P.card : ℝ) *
          ∑ p ∈ P,
            (∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x) ^ 2 /
              DeletionResidueMartingale.cellMeasure.real
                (DeletionResidueMartingale.historyFibre L r) := by
    have hm : 0 < DeletionResidueMartingale.cellMeasure.real
        (DeletionResidueMartingale.historyFibre L r) :=
      DeletionResidueMartingale.historyFibre_mass_pos L r (Finset.mem_range.mp hr)
    have hs :
        (∑ p ∈ P, ∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x) ^ 2 ≤
          (P.card : ℝ) *
            ∑ p ∈ P,
              (∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    calc
      _ ≤ ((P.card : ℝ) *
            ∑ p ∈ P,
              (∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x) ^ 2) /
            DeletionResidueMartingale.cellMeasure.real
              (DeletionResidueMartingale.historyFibre L r) :=
        div_le_div_of_nonneg_right hs hm.le
      _ = _ := by
        rw [mul_div_assoc, Finset.sum_div]
  calc
    (∑ r ∈ range C,
        (∑ p ∈ P, ∫ x in (0 : ℝ)..1,
          upperHalfPrimePacketKernel N L p r x) ^ 2 /
          DeletionResidueMartingale.cellMeasure.real
            (DeletionResidueMartingale.historyFibre L r)) ≤
      ∑ r ∈ range C, (P.card : ℝ) *
        ∑ p ∈ P,
          (∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x) ^ 2 /
            DeletionResidueMartingale.cellMeasure.real
              (DeletionResidueMartingale.historyFibre L r) := by
        exact Finset.sum_le_sum hpoint
    _ = (P.card : ℝ) *
          ∑ p ∈ P,
            ∑ r ∈ range C,
              (∫ x in (0 : ℝ)..1, upperHalfPrimePacketKernel N L p r x) ^ 2 /
                DeletionResidueMartingale.cellMeasure.real
                  (DeletionResidueMartingale.historyFibre L r) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (P.card : ℝ) * ∑ _p ∈ P, 2 / (C : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro p hp
        exact upperHalfPrimePacketKernel_physical_fibre_energy_le N L p hLN (hP p hp)
    _ = 2 * (P.card : ℝ) ^ 2 / (C : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp

/-- Actual integral of the finite physical prime sum obeys the same aggregate energy bound. -/
theorem upperHalfPrimePackets_actual_sum_integral_fibre_energy_le
    (N L : ℕ) (P : Finset ℕ) (hLN : L ≤ N)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ r ∈ range (DeletionResidueMartingale.clock L),
        (∫ x in (0 : ℝ)..1,
          ∑ p ∈ P, upperHalfPrimePacketKernel N L p r x) ^ 2 /
          DeletionResidueMartingale.cellMeasure.real
            (DeletionResidueMartingale.historyFibre L r)) ≤
      2 * (P.card : ℝ) ^ 2 / (DeletionResidueMartingale.clock L : ℝ) := by
  calc
    _ = ∑ r ∈ range (DeletionResidueMartingale.clock L),
          (∑ p ∈ P, ∫ x in (0 : ℝ)..1,
            upperHalfPrimePacketKernel N L p r x) ^ 2 /
            DeletionResidueMartingale.cellMeasure.real
              (DeletionResidueMartingale.historyFibre L r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [intervalIntegral.integral_finsetSum]
      intro p hp
      exact upperHalfPrimePacketKernel_intervalIntegrable N L p r hLN (hP p hp)
    _ ≤ _ := upperHalfPrimePackets_physical_fibre_energy_le N L P hLN hP

/-- The actual upper-half prime window costs at most `2 N² / clock L` in physical energy. -/
theorem upperHalfPhysicalPrimeWindow_fibre_energy_le
    (N L : ℕ) (hLN : L ≤ N) (hN : N ≤ 2 * L) :
    (∑ r ∈ range (DeletionResidueMartingale.clock L),
        (∫ x in (0 : ℝ)..1,
          ∑ p ∈ (Icc (L + 1) N).filter Nat.Prime,
            upperHalfPrimePacketKernel N L p r x) ^ 2 /
          DeletionResidueMartingale.cellMeasure.real
            (DeletionResidueMartingale.historyFibre L r)) ≤
      2 * (N : ℝ) ^ 2 / (DeletionResidueMartingale.clock L : ℝ) := by
  have hcard : ((Icc (L + 1) N).filter Nat.Prime).card ≤ N := by
    calc
      ((Icc (L + 1) N).filter Nat.Prime).card ≤ (Icc 1 N).card := by
        apply Finset.card_le_card
        intro p hp
        have hpIcc := (Finset.mem_filter.mp hp).1
        have hpBounds := Finset.mem_Icc.mp hpIcc
        exact Finset.mem_Icc.mpr ⟨by omega, hpBounds.2⟩
      _ = N := by simp
  have hP : ∀ p ∈ (Icc (L + 1) N).filter Nat.Prime, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  calc
    _ ≤ 2 * (((Icc (L + 1) N).filter Nat.Prime).card : ℝ) ^ 2 /
          (DeletionResidueMartingale.clock L : ℝ) :=
      upperHalfPrimePackets_actual_sum_integral_fibre_energy_le N L _ hLN hP
    _ ≤ 2 * (N : ℝ) ^ 2 / (DeletionResidueMartingale.clock L : ℝ) := by
      gcongr

end RHTower.DeletionPrimeWindowPhase
