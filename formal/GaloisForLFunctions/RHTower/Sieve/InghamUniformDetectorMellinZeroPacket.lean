import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorFullZeroPacket
import GaloisForLFunctions.RHTower.Sieve.MaynardPositiveMellinKernel

open Complex Filter Metric Set ArithmeticFunction Finset Topology

namespace RHTower.Sieve

noncomputable section

/-- Physical center associated to contour-height parameter `X`. -/
def inghamRouteTMellinPhysicalCenter (X : ℕ) : ℝ :=
  (X : ℝ) ^ inghamRouteTPhysicalScaleExponent

/-- Exact `701/1000` physical window attached to the Route-T contour height. -/
def inghamRouteTMellinPhysicalWidth (X : ℕ) : ℝ :=
  inghamRouteTMellinPhysicalCenter X / (X : ℝ)

theorem inghamRouteTMellinPhysicalCenter_pos {X : ℕ} (hX : 1 ≤ X) :
    0 < inghamRouteTMellinPhysicalCenter X := by
  unfold inghamRouteTMellinPhysicalCenter
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)) _

theorem inghamRouteTMellinPhysicalWidth_pos {X : ℕ} (hX : 1 ≤ X) :
    0 < inghamRouteTMellinPhysicalWidth X := by
  unfold inghamRouteTMellinPhysicalWidth
  exact div_pos (inghamRouteTMellinPhysicalCenter_pos hX) (by positivity)

theorem inghamRouteTMellinPhysicalWidth_div_center
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinPhysicalWidth X / inghamRouteTMellinPhysicalCenter X =
      1 / (X : ℝ) := by
  unfold inghamRouteTMellinPhysicalWidth
  have hN := (inghamRouteTMellinPhysicalCenter_pos hX).ne'
  field_simp

/-- The contour-height parametrization realizes exactly the physical exponent `701/1000`. -/
theorem inghamRouteTMellinPhysicalWidth_eq_center_rpow
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinPhysicalWidth X =
      inghamRouteTMellinPhysicalCenter X ^ (701 / 1000 : ℝ) := by
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  unfold inghamRouteTMellinPhysicalWidth inghamRouteTMellinPhysicalCenter
  calc
    (X : ℝ) ^ inghamRouteTPhysicalScaleExponent / (X : ℝ) =
        (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent - 1) := by
      rw [Real.rpow_sub hXR, Real.rpow_one]
    _ = (X : ℝ) ^
        (inghamRouteTPhysicalScaleExponent * (701 / 1000 : ℝ)) := by
      congr 1
      unfold inghamRouteTPhysicalScaleExponent
      norm_num
    _ = ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ (701 / 1000 : ℝ) := by
      rw [Real.rpow_mul hXR.le]

theorem inghamRouteTMellinPhysicalCenter_rpow_sub_one
    {X : ℕ} (hX : 1 ≤ X) (sigma : ℝ) :
    inghamRouteTMellinPhysicalCenter X ^ (sigma - 1) =
      (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (sigma - 1)) := by
  unfold inghamRouteTMellinPhysicalCenter
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  rw [← Real.rpow_mul (zero_le_one.trans hXR)]

/-- Every zero in the common packet lies within distance `X` of the zeta pole. -/
theorem norm_sub_one_le_of_mem_inghamRouteTCommonZeroPacket
    {X : ℕ} {w : ℂ} (hX : 3 ≤ X)
    (hw : w ∈ inghamRouteTCommonZeroPacket X) :
    ‖w - 1‖ ≤ (X : ℝ) := by
  have hstrip := mem_inghamRouteTCommonZeroPacket_strip hw
  have hre : |w.re - 1| ≤ 1 := by
    rw [abs_of_nonpos (by linarith [hstrip.2.1.le])]
    linarith [hstrip.1]
  have hXR : (3 : ℝ) ≤ X := by exact_mod_cast hX
  have hheight : 0 ≤ (X : ℝ) - 2 := by linarith
  have hwdata := mem_zetaResidueUnitClosedRectangleZeros.mp hw
  have hwK := Complex.mem_reProdIm.mp hwdata.1
  have himBounds :
      (2 - (X : ℝ) ≤ w.im ∧ w.im ≤ (X : ℝ) - 2) := by
    simpa [inghamRouteTCommonZeroPacket,
      uIcc_of_le (by linarith : 2 - (X : ℝ) ≤ (X : ℝ) - 2)] using hwK.2
  have him : |w.im| ≤ (X : ℝ) - 2 :=
    abs_le.mpr ⟨by linarith [himBounds.1], himBounds.2⟩
  calc
    ‖w - 1‖ = ‖((w.re - 1 : ℝ) : ℂ) + (w.im : ℂ) * I‖ := by
      congr 1
      apply Complex.ext <;> simp
    _ ≤ ‖((w.re - 1 : ℝ) : ℂ)‖ + ‖(w.im : ℂ) * I‖ := norm_add_le _ _
    _ = |w.re - 1| + |w.im| := by
      rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_I]
      simp only [Real.norm_eq_abs, mul_one]
    _ ≤ 1 + ((X : ℝ) - 2) := add_le_add hre him
    _ ≤ (X : ℝ) := by linarith

/-- On the complete common packet, positivity gives the normalized adjacent Mellin kernel with
no loss relative to its left-endpoint physical weight. -/
theorem norm_routeTNormalizedSmoothWindowMellin_physical_le
    {X : ℕ} {w : ℂ} (hX : 3 ≤ X)
    (hw : w ∈ inghamRouteTCommonZeroPacket X) :
    ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinPhysicalWidth X) w‖ ≤
      (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) := by
  have hX1 : 1 ≤ X := by omega
  have hN := inghamRouteTMellinPhysicalCenter_pos hX1
  have hH := inghamRouteTMellinPhysicalWidth_pos hX1
  have hstrip := mem_inghamRouteTCommonZeroPacket_strip hw
  have hkernel := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
    hN hH hstrip.2.1.le
  simpa only [inghamRouteTMellinPhysicalCenter_rpow_sub_one hX1 w.re] using hkernel

/-- Exact normalized Mellin zero residue sum on the common Route-T rectangle. -/
def inghamRouteTCommonNormalizedMellinZeroPacket (X : ℕ) : ℂ :=
  ∑ w ∈ inghamRouteTCommonZeroPacket X,
    ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinPhysicalWidth X) w

theorem norm_inghamRouteTCommonNormalizedMellinZeroPacket_le
    {X : ℕ} (hX : 3 ≤ X) :
    ‖inghamRouteTCommonNormalizedMellinZeroPacket X‖ ≤
      inghamRouteTCommonZeroWeightedMass X := by
  unfold inghamRouteTCommonNormalizedMellinZeroPacket
  calc
    ‖∑ w ∈ inghamRouteTCommonZeroPacket X,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinPhysicalWidth X) w‖ ≤
      ∑ w ∈ inghamRouteTCommonZeroPacket X,
        ‖((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinPhysicalWidth X) w‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ inghamRouteTCommonZeroPacket X,
        (X : ℝ) ^
          (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
            inghamRouteTZeroMultiplicity w := by
      apply Finset.sum_le_sum
      intro w hw
      rw [norm_mul, Complex.norm_natCast]
      change inghamRouteTZeroMultiplicity w *
          ‖routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinPhysicalWidth X) w‖ ≤ _
      calc
        inghamRouteTZeroMultiplicity w *
            ‖routeTNormalizedSmoothWindowMellin
              (inghamRouteTMellinPhysicalCenter X)
              (inghamRouteTMellinPhysicalWidth X) w‖ ≤
          inghamRouteTZeroMultiplicity w *
            ((X : ℝ) ^
              (inghamRouteTPhysicalScaleExponent * (w.re - 1))) :=
            mul_le_mul_of_nonneg_left
              (norm_routeTNormalizedSmoothWindowMellin_physical_le hX hw)
              (inghamRouteTZeroMultiplicity_nonneg w)
        _ = (X : ℝ) ^
            (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
              inghamRouteTZeroMultiplicity w := by ring
    _ = inghamRouteTCommonZeroWeightedMass X := by
      unfold inghamRouteTCommonZeroWeightedMass
      rfl

/-- **Smooth-window transfer.**  The complete analytic-multiplicity-weighted normalized Mellin
zero residue packet on the common Route-T contour tends to zero. -/
theorem tendsto_norm_inghamRouteTCommonNormalizedMellinZeroPacket_zero :
    Tendsto (fun X : ℕ => ‖inghamRouteTCommonNormalizedMellinZeroPacket X‖)
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun X : ℕ =>
      inghamRouteTCommonZeroWeightedMass X) atTop (𝓝 0) :=
    tendsto_inghamRouteTCommonZeroWeightedMass_zero
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards with X
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with X hX
    exact norm_inghamRouteTCommonNormalizedMellinZeroPacket_le hX

end

end RHTower.Sieve
