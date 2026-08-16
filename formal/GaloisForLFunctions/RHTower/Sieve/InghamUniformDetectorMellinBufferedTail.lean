import GaloisForLFunctions.RHTower.Sieve.MaynardMellinArbitraryOrderDecay
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinZeroPacket
import GaloisForLFunctions.RHTower.CCMRectangularTwoEdge
import GaloisForLFunctions.RHTower.XiEndpointReflectionDefectEnergy

/-!
# Buffered Route-T Mellin packet and complete Xi tail

The critical schedule `N/H = X` leaves no room to sum zeros above contour height `X`.  The
universal positive-kernel bound permits a strict frequency buffer instead: take `N/H = X^(999/1000)`.
The physical window only widens from exponent `701/1000` to `701299/1000000`, while the already
proved finite density packet remains unchanged.  Arbitrary-order Mellin decay at order `2002`,
combined with unconditional inverse-square summability of the exact-multiplicity Xi divisor,
then bounds the complete high-ordinate tail by `X^(-1/500)`.
-/

open Complex Filter Metric Set ArithmeticFunction Finset Topology

namespace RHTower.Sieve

noncomputable section

/-- Natural Mellin frequency kept strictly below contour height. -/
def inghamRouteTMellinBufferedFrequencyExponent : ℝ := 999 / 1000

def inghamRouteTMellinBufferedFrequency (X : ℕ) : ℝ :=
  (X : ℝ) ^ inghamRouteTMellinBufferedFrequencyExponent

/-- Slightly wider physical window whose natural frequency has a fixed power gap below `X`. -/
def inghamRouteTMellinBufferedPhysicalWidth (X : ℕ) : ℝ :=
  inghamRouteTMellinPhysicalCenter X / inghamRouteTMellinBufferedFrequency X

theorem inghamRouteTMellinBufferedFrequency_pos {X : ℕ} (hX : 1 ≤ X) :
    0 < inghamRouteTMellinBufferedFrequency X := by
  unfold inghamRouteTMellinBufferedFrequency
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)) _

theorem inghamRouteTMellinBufferedFrequency_one_le {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ inghamRouteTMellinBufferedFrequency X := by
  unfold inghamRouteTMellinBufferedFrequency inghamRouteTMellinBufferedFrequencyExponent
  exact Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)

theorem inghamRouteTMellinBufferedPhysicalWidth_pos {X : ℕ} (hX : 1 ≤ X) :
    0 < inghamRouteTMellinBufferedPhysicalWidth X := by
  unfold inghamRouteTMellinBufferedPhysicalWidth
  exact div_pos (inghamRouteTMellinPhysicalCenter_pos hX)
    (inghamRouteTMellinBufferedFrequency_pos hX)

theorem inghamRouteTMellinBufferedPhysicalWidth_le_center {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinBufferedPhysicalWidth X ≤ inghamRouteTMellinPhysicalCenter X := by
  unfold inghamRouteTMellinBufferedPhysicalWidth
  exact div_le_self (inghamRouteTMellinPhysicalCenter_pos hX).le
    (inghamRouteTMellinBufferedFrequency_one_le hX)

/-- Exact physical exponent after inserting the `X^(1/1000)` frequency buffer. -/
theorem inghamRouteTMellinBufferedPhysicalWidth_eq_center_rpow
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinBufferedPhysicalWidth X =
      inghamRouteTMellinPhysicalCenter X ^ (701299 / 1000000 : ℝ) := by
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  unfold inghamRouteTMellinBufferedPhysicalWidth inghamRouteTMellinPhysicalCenter
    inghamRouteTMellinBufferedFrequency inghamRouteTMellinBufferedFrequencyExponent
  calc
    (X : ℝ) ^ inghamRouteTPhysicalScaleExponent / (X : ℝ) ^ (999 / 1000 : ℝ) =
        (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent - 999 / 1000) := by
      rw [Real.rpow_sub hXR]
    _ = (X : ℝ) ^
        (inghamRouteTPhysicalScaleExponent * (701299 / 1000000 : ℝ)) := by
      congr 1
      unfold inghamRouteTPhysicalScaleExponent
      norm_num
    _ = ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^
        (701299 / 1000000 : ℝ) := by
      rw [Real.rpow_mul hXR.le]

theorem norm_routeTNormalizedSmoothWindowMellin_buffered_physical_le
    {X : ℕ} {w : ℂ} (hX : 3 ≤ X)
    (hw : w ∈ inghamRouteTCommonZeroPacket X) :
    ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) w‖ ≤
      (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) := by
  have hX1 : 1 ≤ X := by omega
  have hstrip := mem_inghamRouteTCommonZeroPacket_strip hw
  have hkernel := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
    (inghamRouteTMellinPhysicalCenter_pos hX1)
    (inghamRouteTMellinBufferedPhysicalWidth_pos hX1) hstrip.2.1.le
  simpa only [inghamRouteTMellinPhysicalCenter_rpow_sub_one hX1 w.re] using hkernel

def inghamRouteTCommonBufferedNormalizedMellinZeroPacket (X : ℕ) : ℂ :=
  ∑ w ∈ inghamRouteTCommonZeroPacket X,
    ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) w

theorem norm_inghamRouteTCommonBufferedNormalizedMellinZeroPacket_le
    {X : ℕ} (hX : 3 ≤ X) :
    ‖inghamRouteTCommonBufferedNormalizedMellinZeroPacket X‖ ≤
      inghamRouteTCommonZeroWeightedMass X := by
  unfold inghamRouteTCommonBufferedNormalizedMellinZeroPacket
  calc
    ‖∑ w ∈ inghamRouteTCommonZeroPacket X,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X) w‖ ≤
      ∑ w ∈ inghamRouteTCommonZeroPacket X,
        ‖((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X) w‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ inghamRouteTCommonZeroPacket X,
        (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
          inghamRouteTZeroMultiplicity w := by
      apply Finset.sum_le_sum
      intro w hw
      rw [norm_mul, Complex.norm_natCast]
      change inghamRouteTZeroMultiplicity w *
          ‖routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X) w‖ ≤ _
      calc
        _ ≤ inghamRouteTZeroMultiplicity w *
            ((X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1))) :=
          mul_le_mul_of_nonneg_left
            (norm_routeTNormalizedSmoothWindowMellin_buffered_physical_le hX hw)
            (inghamRouteTZeroMultiplicity_nonneg w)
        _ = _ := by ring
    _ = inghamRouteTCommonZeroWeightedMass X := by
      unfold inghamRouteTCommonZeroWeightedMass
      rfl

theorem tendsto_norm_inghamRouteTCommonBufferedNormalizedMellinZeroPacket_zero :
    Tendsto (fun X : ℕ =>
      ‖inghamRouteTCommonBufferedNormalizedMellinZeroPacket X‖) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_inghamRouteTCommonZeroWeightedMass_zero
  · filter_upwards with X
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with X hX
    exact norm_inghamRouteTCommonBufferedNormalizedMellinZeroPacket_le hX

theorem inghamRouteTMellinPhysicalCenter_one_le {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ inghamRouteTMellinPhysicalCenter X := by
  unfold inghamRouteTMellinPhysicalCenter
  exact Real.one_le_rpow (by exact_mod_cast hX)
    inghamRouteTPhysicalScaleExponent_pos.le

/-- Every vertical decay order specializes to the buffered schedule with pure frequency cost. -/
theorem exists_routeTBufferedMellin_natOrder_frequency_bound (j : ℕ) :
    ∃ Dj : ℝ, 0 ≤ Dj ∧ ∀ {X : ℕ} {w : ℂ}, 3 ≤ X →
      0 < w.re → w.re ≤ 1 →
      |w.im| ^ (j + 1) *
          ‖routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X) w‖ ≤
        Dj * inghamRouteTMellinBufferedFrequency X ^ (j + 1) := by
  obtain ⟨Dj, hDj, hbound⟩ :=
    exists_routeTNormalizedSmoothWindowMellin_natOrder_narrow_bound j
  refine ⟨Dj, hDj, ?_⟩
  intro X w hX hw0 hw1
  have hX1 : 1 ≤ X := by omega
  let N : ℝ := inghamRouteTMellinPhysicalCenter X
  let H : ℝ := inghamRouteTMellinBufferedPhysicalWidth X
  let F : ℝ := inghamRouteTMellinBufferedFrequency X
  have hN1 : 1 ≤ N := inghamRouteTMellinPhysicalCenter_one_le hX1
  have hN : 0 < N := zero_lt_one.trans_le hN1
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  have hHN : H ≤ N := inghamRouteTMellinBufferedPhysicalWidth_le_center hX1
  have hF : 0 < F := inghamRouteTMellinBufferedFrequency_pos hX1
  have hraw := hbound N H hN1 hH hHN w hw0 hw1
  have hpow : N ^ (w.re + (j : ℝ)) =
      N ^ (w.re - 1) * N ^ (j + 1) := by
    calc
      N ^ (w.re + (j : ℝ)) = N ^ ((w.re - 1) + ((j + 1 : ℕ) : ℝ)) := by
        congr 1
        norm_num
      _ = N ^ (w.re - 1) * N ^ ((j + 1 : ℕ) : ℝ) := by
        rw [Real.rpow_add hN]
      _ = N ^ (w.re - 1) * N ^ (j + 1) := by
        rw [Real.rpow_natCast]
  have hrewrite :
      Dj / H ^ (j + 1) * N ^ (w.re + (j : ℝ)) =
        Dj * F ^ (j + 1) * N ^ (w.re - 1) := by
    rw [hpow, show H = N / F by rfl]
    rw [div_pow]
    field_simp [hN.ne', hF.ne']
  have hNweight : N ^ (w.re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  calc
    |w.im| ^ (j + 1) *
        ‖routeTNormalizedSmoothWindowMellin N H w‖ ≤
      Dj / H ^ (j + 1) * N ^ (w.re + (j : ℝ)) := hraw
    _ = Dj * F ^ (j + 1) * N ^ (w.re - 1) := hrewrite
    _ ≤ Dj * F ^ (j + 1) * 1 := by
      exact mul_le_mul_of_nonneg_left hNweight
        (mul_nonneg hDj (pow_nonneg hF.le _))
    _ = Dj * F ^ (j + 1) := by ring

/-- Exact-multiplicity Xi ordinates have a summable reciprocal square. -/
theorem summable_xiZeroCopy_one_div_abs_im_sq :
    Summable (fun q : RHTower.XiZeroCopy =>
      1 / |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2) := by
  obtain ⟨eta, heta, hheight⟩ := RHTower.exists_xiZeroCopy_abs_im_lower_bound
  let K : ℝ := 1 + 1 / eta
  have hK : 0 < K := by dsimp only [K]; positivity
  have hmajor := RHTower.summable_norm_xiRawReciprocalCoordinate_sq.mul_left (K ^ 2)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun q => ?_) hmajor
  let rho : ℂ := (q.1 : RHTower.XiDivisorSupport)
  let gamma : ℝ := |rho.im|
  have hgamma : 0 < gamma := heta.trans_le (hheight q)
  have hrho0 : rho ≠ 0 := by
    intro h
    have hs := RHTower.xi_divisor_support_re_mem_open_unit q.1
    rw [show (q.1 : ℂ) = rho by rfl, h] at hs
    norm_num at hs
  have hre : |rho.re| ≤ 1 := by
    have hs := RHTower.xi_divisor_support_re_mem_open_unit q.1
    rw [abs_le]
    constructor <;> linarith
  have hnorm : ‖rho‖ ≤ K * gamma := by
    calc
      ‖rho‖ ≤ |rho.re| + |rho.im| := Complex.norm_le_abs_re_add_abs_im rho
      _ ≤ 1 + gamma := add_le_add hre le_rfl
      _ ≤ K * gamma := by
        dsimp only [K, gamma]
        field_simp [heta.ne']
        nlinarith [hheight q]
  have hsq : ‖rho‖ ^ 2 ≤ K ^ 2 * gamma ^ 2 := by
    calc
      ‖rho‖ ^ 2 ≤ (K * gamma) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg rho) hnorm 2
      _ = K ^ 2 * gamma ^ 2 := by ring
  change 1 / gamma ^ 2 ≤ K ^ 2 * ‖RHTower.xiRawReciprocalCoordinate q‖ ^ 2
  rw [RHTower.xiRawReciprocalCoordinate, norm_inv]
  change 1 / gamma ^ 2 ≤ K ^ 2 * ‖rho‖⁻¹ ^ 2
  field_simp [hgamma.ne', (norm_pos_iff.mpr hrho0).ne']
  simpa only [mul_comm] using hsq

/-- Multiplicity-copy Xi tail above contour height, tested by the buffered physical kernel. -/
def inghamRouteTBufferedXiMellinHighTail (X : ℕ) : ℂ :=
  ∑' q : {q : RHTower.XiZeroCopy //
      (X : ℝ) ≤ |((q.1 : RHTower.XiDivisorSupport) : ℂ).im|},
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X)
      (q.1.1 : ℂ)

/-- At derivative order `2001`, the buffered high Xi tail is bounded by inverse-square divisor
mass times `frequency^2002 / height^2000`. -/
theorem exists_norm_inghamRouteTBufferedXiMellinHighTail_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {X : ℕ}, 3 ≤ X →
      ‖inghamRouteTBufferedXiMellinHighTail X‖ ≤
        (D * inghamRouteTMellinBufferedFrequency X ^ 2002 /
          (X : ℝ) ^ 2000) *
            ∑' q : RHTower.XiZeroCopy,
              1 / |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2 := by
  obtain ⟨D, hD, hfrequency⟩ :=
    exists_routeTBufferedMellin_natOrder_frequency_bound 2001
  refine ⟨D, hD, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by omega
  have hXR : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX1)
  let Q := {q : RHTower.XiZeroCopy //
    (X : ℝ) ≤ |((q.1 : RHTower.XiDivisorSupport) : ℂ).im|}
  let B : Q → ℝ := fun q =>
    1 / |((q.1.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2
  let A : ℝ := D * inghamRouteTMellinBufferedFrequency X ^ 2002 / (X : ℝ) ^ 2000
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : Summable B := by
    exact summable_xiZeroCopy_one_div_abs_im_sq.subtype _
  have hmajor : Summable (fun q : Q => A * B q) := hB.mul_left A
  have hpoint : ∀ q : Q,
      ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        (q.1.1 : ℂ)‖ ≤ A * B q := by
    intro q
    let rho : ℂ := (q.1.1 : RHTower.XiDivisorSupport)
    let gamma : ℝ := |rho.im|
    have hgammaX : (X : ℝ) ≤ gamma := q.2
    have hgamma : 0 < gamma := hXR.trans_le hgammaX
    have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1.1
    have hweighted := hfrequency (X := X) (w := rho) hX hstrip.1 hstrip.2.le
    norm_num at hweighted
    have hkernel :
        ‖routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) rho‖ ≤
        D * inghamRouteTMellinBufferedFrequency X ^ 2002 / gamma ^ 2002 := by
      apply (le_div_iff₀ (pow_pos hgamma 2002)).2
      simpa only [mul_comm] using hweighted
    have hpow : (X : ℝ) ^ 2000 ≤ gamma ^ 2000 :=
      pow_le_pow_left₀ hXR.le hgammaX 2000
    have htail :
        D * inghamRouteTMellinBufferedFrequency X ^ 2002 / gamma ^ 2002 ≤
          A * (1 / gamma ^ 2) := by
      dsimp only [A]
      have hF : 0 ≤ D * inghamRouteTMellinBufferedFrequency X ^ 2002 :=
        mul_nonneg hD (pow_nonneg (inghamRouteTMellinBufferedFrequency_pos hX1).le _)
      field_simp [hXR.ne', hgamma.ne']
      exact mul_le_mul_of_nonneg_left hpow hF
    exact hkernel.trans (by simpa only [A, B, rho, gamma] using htail)
  have hsum : Summable (fun q : Q =>
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        (q.1.1 : ℂ)) :=
    Summable.of_norm_bounded hmajor hpoint
  unfold inghamRouteTBufferedXiMellinHighTail
  change ‖∑' q : Q, routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1.1 : ℂ)‖ ≤ _
  calc
    _ ≤ ∑' q : Q, ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (q.1.1 : ℂ)‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' q : Q, A * B q := hsum.norm.tsum_le_tsum hpoint hmajor
    _ = A * ∑' q : Q, B q := tsum_mul_left
    _ ≤ A * ∑' q : RHTower.XiZeroCopy,
        1 / |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Summable.tsum_subtype_le _ _ (fun _ => by positivity)
        summable_xiZeroCopy_one_div_abs_im_sq
    _ = _ := rfl

theorem inghamRouteTMellinBufferedFrequency_pow_2002_div_height_pow_2000
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinBufferedFrequency X ^ 2002 / (X : ℝ) ^ 2000 =
      (X : ℝ) ^ (-(1 / 500 : ℝ)) := by
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  unfold inghamRouteTMellinBufferedFrequency inghamRouteTMellinBufferedFrequencyExponent
  rw [← Real.rpow_natCast, ← Real.rpow_mul hXR.le, ← Real.rpow_natCast,
    ← Real.rpow_sub hXR]
  congr 1
  norm_num

/-- The full exact-multiplicity Xi tail above Route-T contour height tends to zero.  The explicit
power margin is `X^(-1/500)`. -/
theorem tendsto_norm_inghamRouteTBufferedXiMellinHighTail_zero :
    Tendsto (fun X : ℕ => ‖inghamRouteTBufferedXiMellinHighTail X‖)
      atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_norm_inghamRouteTBufferedXiMellinHighTail_le
  let S : ℝ := ∑' q : RHTower.XiZeroCopy,
    1 / |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2
  have hcore : Tendsto (fun X : ℕ => (X : ℝ) ^ (-(1 / 500 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 500)).comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun X : ℕ =>
      (D * inghamRouteTMellinBufferedFrequency X ^ 2002 /
        (X : ℝ) ^ 2000) * S) atTop (𝓝 0) := by
    have hscaled : Tendsto (fun X : ℕ =>
        (D * S) * (X : ℝ) ^ (-(1 / 500 : ℝ))) atTop (𝓝 0) := by
      simpa using hcore.const_mul (D * S)
    refine hscaled.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    rw [← inghamRouteTMellinBufferedFrequency_pow_2002_div_height_pow_2000 hX]
    ring
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards with X
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with X hX
    simpa only [S] using hbound hX

end

end RHTower.Sieve
