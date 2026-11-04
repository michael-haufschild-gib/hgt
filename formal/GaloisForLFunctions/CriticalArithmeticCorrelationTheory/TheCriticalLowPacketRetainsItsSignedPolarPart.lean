import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSignedCriticalResidualAboveOverlapDecays
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit

/-!
# The critical low packet retains its signed polar part

The summable array below overlap and the decaying array above overlap
control the same moving conductor packet. Energy-weighted finite
Cauchy–Schwarz turns their squared sum into a bound uniform over all
packet coefficients.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticHodgeTheoryOfDegenerations SpacingScaleHarmonicAnalysis

private theorem signed_square_sum_le_low_add_high {c : ℝ} (hc : 0 < c) (N Q : ℕ) :
    (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, signedCriticalRelativeSquare c N m l) ≤
      (∑ m ∈ Icc 1 ⌊c⌋₊, ∑ l ∈ Icc 1 ⌊c⌋₊, signedCriticalRelativeSquare c N m l) +
      ((∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
          if c < (m : ℝ) then signedCriticalRelativeSquare c N m l else 0) +
        (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
          if c < (l : ℝ) then signedCriticalRelativeSquare c N m l else 0)) := by
  let S : Finset ℕ := (Icc 1 Q).filter fun m : ℕ => (m : ℝ) ≤ c
  have hS : S ⊆ Icc 1 ⌊c⌋₊ := by
    intro m hm
    obtain ⟨hmQ, hmc⟩ := mem_filter.mp hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hmQ).1, Nat.le_floor hmc⟩
  have hlow : (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
      if (m : ℝ) ≤ c ∧ (l : ℝ) ≤ c then signedCriticalRelativeSquare c N m l else 0) ≤
      ∑ m ∈ Icc 1 ⌊c⌋₊, ∑ l ∈ Icc 1 ⌊c⌋₊, signedCriticalRelativeSquare c N m l := by
    calc
      _ = ∑ m ∈ S, ∑ l ∈ S, signedCriticalRelativeSquare c N m l := by
        simp only [S, sum_filter]
        apply sum_congr rfl
        intro m hm
        by_cases hmc : (m : ℝ) ≤ c
        · simp only [hmc, true_and, if_true]
        · simp only [hmc, false_and, if_false, sum_const_zero]
      _ ≤ ∑ m ∈ S, ∑ l ∈ Icc 1 ⌊c⌋₊, signedCriticalRelativeSquare c N m l :=
        sum_le_sum fun m hm => sum_le_sum_of_subset_of_nonneg hS fun l hl _ =>
          signedCriticalRelativeSquare_nonneg hc N (mem_Icc.mp (hS hm)).1 (mem_Icc.mp hl).1
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hS fun m hm _ =>
        sum_nonneg fun l hl =>
          signedCriticalRelativeSquare_nonneg hc N (mem_Icc.mp hm).1 (mem_Icc.mp hl).1
  have hpt : ∀ m ∈ Icc 1 Q, ∀ l ∈ Icc 1 Q,
      signedCriticalRelativeSquare c N m l ≤
        (if (m : ℝ) ≤ c ∧ (l : ℝ) ≤ c then signedCriticalRelativeSquare c N m l else 0) +
        ((if c < (m : ℝ) then signedCriticalRelativeSquare c N m l else 0) +
          (if c < (l : ℝ) then signedCriticalRelativeSquare c N m l else 0)) := by
    intro m hm l hl
    have hf := signedCriticalRelativeSquare_nonneg hc N (mem_Icc.mp hm).1 (mem_Icc.mp hl).1
    by_cases hmc : (m : ℝ) ≤ c <;> by_cases hlc : (l : ℝ) ≤ c
    · simp only [hmc, hlc, and_self, if_true, not_lt_of_ge hmc, not_lt_of_ge hlc,
        if_false, add_zero, le_refl]
    · simp only [hmc, hlc, and_false, if_false, not_lt_of_ge hmc, lt_of_not_ge hlc,
        if_true, zero_add, le_refl]
    · simp only [hmc, hlc, false_and, if_false, lt_of_not_ge hmc, not_lt_of_ge hlc,
        if_true, zero_add, add_zero, le_refl]
    · simp only [hmc, hlc, false_and, if_false, lt_of_not_ge hmc, lt_of_not_ge hlc,
        if_true, zero_add]
      linarith only [hf]
  have hsum := sum_le_sum fun m hm => sum_le_sum fun l hl => hpt m hm l hl
  simp only [sum_add_distrib] at hsum
  exact hsum.trans (add_le_add hlow le_rfl)

/-- The whole logarithmic packet has vanishing energy-normalized signed square. -/
theorem tendsto_sum_signedCriticalRelativeSquare_low_packet {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => ∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
      ∑ l ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
        signedCriticalRelativeSquare (c N) N m l) atTop (𝓝 0) := by
  have h := (tendsto_sum_signedCriticalRelativeSquare_below_overlap hc hR hcrit).add
    (tendsto_sum_signedCriticalRelativeSquare_above_overlap hc hR hcrit)
  simp only [zero_add] at h
  refine squeeze_zero (fun N => sum_nonneg fun m hm => sum_nonneg fun l hl =>
    signedCriticalRelativeSquare_nonneg (zero_lt_one.trans_le (hc N)) N
      (mem_Icc.mp hm).1 (mem_Icc.mp hl).1) ?_ h
  intro N
  exact signed_square_sum_le_low_add_high (zero_lt_one.trans_le (hc N)) N _

private theorem abs_weighted_bilinear_le {S : Finset ℕ} {E : ℕ → ℝ}
    (hE : ∀ m ∈ S, 0 < E m) {d : ℕ → ℕ → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hd : (∑ m ∈ S, ∑ l ∈ S, d m l ^ 2 / (E m * E l)) ≤ ε ^ 2)
    (b : ℕ → ℝ) :
    |∑ m ∈ S, ∑ l ∈ S, b m * b l * d m l| ≤ ε * ∑ m ∈ S, E m * b m ^ 2 := by
  let t : ℕ → ℝ := fun m => Real.sqrt (E m) * b m
  let u : ℕ × ℕ → ℝ := fun p => d p.1 p.2 / (Real.sqrt (E p.1) * Real.sqrt (E p.2))
  let B : ℝ := ∑ m ∈ S, E m * b m ^ 2
  have hB : 0 ≤ B := sum_nonneg fun m hm => mul_nonneg (hE m hm).le (sq_nonneg _)
  have ht : (∑ p ∈ S ×ˢ S, (t p.1 * t p.2) ^ 2) = B ^ 2 := by
    rw [Finset.sum_product]
    have htm : ∀ m ∈ S, t m ^ 2 = E m * b m ^ 2 := fun m hm => by
      dsimp only [t]
      rw [mul_pow, Real.sq_sqrt (hE m hm).le]
    calc
      _ = (∑ m ∈ S, t m ^ 2) * ∑ l ∈ S, t l ^ 2 := by
        rw [Finset.sum_mul_sum]
        exact sum_congr rfl fun m _ => sum_congr rfl fun l _ => mul_pow _ _ 2
      _ = B ^ 2 := by rw [sum_congr rfl htm]; exact (pow_two B).symm
  have hu : (∑ p ∈ S ×ˢ S, u p ^ 2) ≤ ε ^ 2 := by
    rw [Finset.sum_product]
    convert hd using 1
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro l hl
    dsimp only [u]
    rw [div_pow, mul_pow, Real.sq_sqrt (hE m hm).le, Real.sq_sqrt (hE l hl).le]
  have hid : (∑ p ∈ S ×ˢ S, (t p.1 * t p.2) * u p) =
      ∑ m ∈ S, ∑ l ∈ S, b m * b l * d m l := by
    rw [Finset.sum_product]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro l hl
    dsimp only [t, u]
    field_simp [(Real.sqrt_pos.mpr (hE m hm)).ne', (Real.sqrt_pos.mpr (hE l hl)).ne']
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ S) (fun p => t p.1 * t p.2) u
  rw [ht, hid] at hcs
  have hsq : (∑ m ∈ S, ∑ l ∈ S, b m * b l * d m l) ^ 2 ≤ (ε * B) ^ 2 :=
    hcs.trans ((mul_le_mul_of_nonneg_left hu (sq_nonneg B)).trans_eq (by ring))
  have habs := sq_abs (∑ m ∈ S, ∑ l ∈ S, b m * b l * d m l)
  have heB := mul_nonneg hε hB
  have hn := abs_nonneg (∑ m ∈ S, ∑ l ∈ S, b m * b l * d m l)
  nlinarith only [hsq, habs, heB, hn]

/-- The signed residual is small uniformly over every coefficient vector in the moving low packet. -/
theorem eventually_signedCriticalConductorResidual_low_packet_le {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      |∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
        ∑ l ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
          b m * b l * signedCriticalConductorResidual (c N) N m l| ≤
        ε * ∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 := by
  filter_upwards [(tendsto_sum_signedCriticalRelativeSquare_low_packet hc hR hcrit).eventually
    (gt_mem_nhds (sq_pos_of_pos hε))] with N hN
  intro b
  apply abs_weighted_bilinear_le (E := completedConductorEnergy tiltedUnitSpline (c N))
    (d := signedCriticalConductorResidual (c N) N) ?_ hε.le hN.le b
  intro m hm
  have hf := tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor (hc N) (mem_Icc.mp hm).1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  exact (div_pos tiltedSplineSpectralFloorConstant_pos (pow_pos hc0 7)).trans_le hf

private theorem abs_energy_weighted_gram_sub_le {Q N : ℕ} (hQ : 2 ≤ Q)
    (hQN : Q * Q ≤ N) (hL : 0 < Real.log (N : ℝ)) {c : ℝ} (hc : 1 ≤ c)
    (b : ℕ → ℝ) :
    |⟪∑ m ∈ Icc 1 Q, (completedConductorEnergy tiltedUnitSpline c m * b m) •
          normalizedRamanujanHorizonVector m N,
        ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N⟫ -
      ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline c m * b m ^ 2| ≤
      (9 * ((|completeWeilSelfFinitePart tiltedUnitSpline 1| + 5) /
          tiltedSplineSpectralFloorConstant + 1) *
        (1 + Real.log Q) ^ 2 * c ^ 4 / Real.log N) *
        ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline c m * b m ^ 2 := by
  let E : ℕ → ℝ := completedConductorEnergy tiltedUnitSpline c
  let κ : ℝ := tiltedSplineSpectralFloorConstant
  let C : ℝ := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 5
  let S : ℝ := ∑ m ∈ Icc 1 Q, E m * b m ^ 2
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  have hC : 0 < C := by dsimp only [C]; positivity
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hfloor : ∀ m ∈ Icc 1 Q, κ / c ^ 7 ≤ E m := fun m hm =>
    tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc (mem_Icc.mp hm).1
  have hE : ∀ m ∈ Icc 1 Q, 0 < E m := fun m hm =>
    (div_pos hκ (pow_pos hc0 7)).trans_le (hfloor m hm)
  have hS : 0 ≤ S := sum_nonneg fun m hm => mul_nonneg (hE m hm).le (sq_nonneg _)
  have hub : ∀ m ∈ Icc 1 Q, E m ≤ C * (1 + Real.log Q) := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
    have hlogm := Real.log_le_log hm0 hmQ
    have hlogQ := Real.log_natCast_nonneg Q
    have hanti := completedConductorEnergy_anti contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos zero_lt_one hc hm1
    have hbase := CompletedArithmeticForms.completedConductorEnergy_le_of_one_le contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos le_rfl hm1
    simp only [one_pow, mul_one] at hbase
    have habs := abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1)
    dsimp only [E, C]
    nlinarith only [hanti, hbase, hlogm, hlogQ, habs]
  have hd : (∑ m ∈ Icc 1 Q, (E m * b m) ^ 2) ≤ C * (1 + Real.log Q) * S := by
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    calc
      (E m * b m) ^ 2 = E m * (E m * b m ^ 2) := by ring
      _ ≤ (C * (1 + Real.log Q)) * (E m * b m ^ 2) :=
        mul_le_mul_of_nonneg_right (hub m hm)
          (mul_nonneg (hE m hm).le (sq_nonneg _))
  have hb : (∑ m ∈ Icc 1 Q, b m ^ 2) ≤ (c ^ 7 / κ) * S := by
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    calc
      _ = (c ^ 7 / κ) * ((κ / c ^ 7) * b m ^ 2) := by field_simp [hc0.ne', hκ.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hfloor m hm) (sq_nonneg _)) (by positivity)
  have hprod : Real.sqrt (∑ m ∈ Icc 1 Q, (E m * b m) ^ 2) *
      Real.sqrt (∑ m ∈ Icc 1 Q, b m ^ 2) ≤
      (C / κ + 1) * (1 + Real.log Q) * c ^ 4 * S := by
    let U : ℝ := (C / κ + 1) * (1 + Real.log Q) * c ^ 4 * S
    have h1Q : 1 ≤ 1 + Real.log Q := by linarith [Real.log_natCast_nonneg Q]
    have hU : 0 ≤ U := by dsimp only [U]; positivity
    have hc78 : c ^ 7 ≤ c ^ 8 := pow_le_pow_right₀ hc (by norm_num : 7 ≤ 8)
    have hlog2 : 1 + Real.log Q ≤ (1 + Real.log Q) ^ 2 := by
      simpa only [pow_one] using pow_le_pow_right₀ h1Q (by norm_num : 1 ≤ 2)
    have hC2 : C / κ ≤ (C / κ + 1) ^ 2 := by
      have h := div_nonneg hC.le hκ.le
      nlinarith only [h]
    have hfactor : (C / κ) * (1 + Real.log Q) * c ^ 7 ≤
        (C / κ + 1) ^ 2 * (1 + Real.log Q) ^ 2 * c ^ 8 :=
      mul_le_mul (mul_le_mul hC2 hlog2 (by positivity) (sq_nonneg _)) hc78
        (by positivity) (by positivity)
    have hsq : (Real.sqrt (∑ m ∈ Icc 1 Q, (E m * b m) ^ 2) *
        Real.sqrt (∑ m ∈ Icc 1 Q, b m ^ 2)) ^ 2 ≤ U ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _),
        Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
      calc
        _ ≤ (C * (1 + Real.log Q) * S) * ((c ^ 7 / κ) * S) :=
          mul_le_mul hd hb (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = ((C / κ) * (1 + Real.log Q) * c ^ 7) * S ^ 2 := by ring
        _ ≤ ((C / κ + 1) ^ 2 * (1 + Real.log Q) ^ 2 * c ^ 8) * S ^ 2 :=
          mul_le_mul_of_nonneg_right hfactor (sq_nonneg S)
        _ = U ^ 2 := by dsimp only [U]; ring
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hU] at h
  have hp := CompletedArithmeticForms.abs_inner_sum_normalizedRamanujanHorizonVector_sub_le
    hQ hQN (fun m => E m * b m) b
  have heq : (∑ m ∈ Icc 1 Q, E m * b m * b m) = S :=
    sum_congr rfl fun m _ => by ring
  rw [heq, mul_assoc (9 * (1 + Real.log Q) / Real.log N)] at hp
  exact hp.trans ((mul_le_mul_of_nonneg_left hprod
    (by have := Real.log_natCast_nonneg Q; positivity)).trans_eq (by ring))

/-- The energy-weighted Gram discrepancy vanishes uniformly on the moving low packet. -/
theorem eventually_energy_weighted_gram_low_packet_le {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      |⟪∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
            (completedConductorEnergy tiltedUnitSpline (c N) m * b m) •
              normalizedRamanujanHorizonVector m N,
          ∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
            b m • normalizedRamanujanHorizonVector m N⟫ -
        ∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2| ≤
        ε * ∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 := by
  let C : ℝ := 9 * ((|completeWeilSelfFinitePart tiltedUnitSpline 1| + 5) /
    tiltedSplineSpectralFloorConstant + 1)
  have hκ := tiltedSplineSpectralFloorConstant_pos
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => 1 / Real.log N ^ (1 / 4 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlog)
  have hNlim := criticalCurve_pow_log_div_natCast hc hR hcrit 0 2
  simp only [pow_zero, one_mul] at hNlim
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp hlog).eventually_ge_atTop 2,
    hNlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_criticalCurve_le_log_rpow hc hcrit (by norm_num : (1 / 8 : ℝ) < 129 / 1024),
    hlog.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (129 / 256 : ℝ) < 3 / 4) 2 C),
    hsmall.eventually (gt_mem_nhds hε)] with N hN hL1 hQ2 hL2N hcL hpoly hεN
  change 1 ≤ Real.log (N : ℝ) at hL1
  change 2 ≤ Real.log (N : ℝ) ^ (13 / 32 : ℝ) at hQ2
  let L : ℝ := Real.log N
  let Q : ℕ := ⌊L ^ (13 / 32 : ℝ)⌋₊
  change C * L ^ (129 / 256 : ℝ) * (1 + Real.log L) ^ 2 ≤ L ^ (3 / 4 : ℝ) at hpoly
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hQ : 2 ≤ Q := Nat.le_floor (by exact_mod_cast hQ2)
  have hQL : (Q : ℝ) ≤ L := (Nat.floor_le (by positivity : 0 ≤ L ^ (13 / 32 : ℝ))).trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 / 32 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hQN : Q * Q ≤ N := by
    have hsq := (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQL 2).trans
      ((div_le_one hN0).mp hL2N.le)
    exact_mod_cast (show (Q : ℝ) * Q ≤ N by simpa only [pow_two] using hsq)
  have hc4 : c N ^ 4 ≤ L ^ (129 / 256 : ℝ) := by
    calc
      _ ≤ (L ^ (129 / 1024 : ℝ)) ^ 4 := pow_le_pow_left₀ (zero_le_one.trans (hc N)) hcL 4
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogQ : (1 + Real.log Q) ^ 2 ≤ (1 + Real.log L) ^ 2 :=
    pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg Q])
      (add_le_add le_rfl (Real.log_le_log hQ0 hQL)) 2
  have hfactor : C * (1 + Real.log Q) ^ 2 * c N ^ 4 / L ≤ ε := by
    calc
      _ ≤ C * (1 + Real.log L) ^ 2 * L ^ (129 / 256 : ℝ) / L :=
        div_le_div_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hlogQ hC) hc4 (by positivity) (by positivity)) hL0.le
      _ ≤ L ^ (3 / 4 : ℝ) / L := div_le_div_of_nonneg_right
        ((le_of_eq (by ring)).trans hpoly) hL0.le
      _ = 1 / L ^ (1 / 4 : ℝ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hL0]
        norm_num
        rw [Real.rpow_neg hL0.le, one_div]
      _ ≤ ε := hεN.le
  intro b
  exact (abs_energy_weighted_gram_sub_le hQ hQN hL0 (hc N) b).trans
    (mul_le_mul_of_nonneg_right hfactor (sum_nonneg fun m hm =>
      mul_nonneg (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
        tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos
          (zero_lt_one.trans_le (hc N)) (mem_Icc.mp hm).1) (sq_nonneg _)))

/-- The actual complete form equals its conductor energy plus the polar finite part,
up to a uniformly small relative error on the entire moving low packet. -/
theorem eventually_completeWeil_low_packet_signed_approx {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, y⟫ -
        (∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) -
        tiltedPolarFinitePart * (c N / Real.log N) * b 1 ^ 2| ≤
        ε * ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_signedCriticalConductorResidual_low_packet_le hc hR hcrit
      (half_pos hε), eventually_energy_weighted_gram_low_packet_le hc hR hcrit (half_pos hε),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp hlog).eventually_ge_atTop 1]
    with N hres hgram hQpow
  change 1 ≤ Real.log (N : ℝ) ^ (13 / 32 : ℝ) at hQpow
  intro b Q y
  have hQ : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hQpow)
  have h1 : 1 ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
  let E : ℕ → ℝ := completedConductorEnergy tiltedUnitSpline (c N)
  let yd := ∑ m ∈ Icc 1 Q, (E m * b m) • normalizedRamanujanHorizonVector m N
  let S := ∑ m ∈ Icc 1 Q, E m * b m ^ 2
  let P := tiltedPolarFinitePart * (c N / Real.log N) * b 1 ^ 2
  have hpolar : (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, b m * b l *
      (if m = 1 ∧ l = 1 then tiltedPolarFinitePart * (c N / Real.log N) else 0)) = P := by
    rw [sum_eq_single_of_mem 1 h1]
    · rw [sum_eq_single_of_mem 1 h1]
      · rw [if_pos ⟨rfl, rfl⟩]
        dsimp only [P]
        ring
      · intro l hl hl1
        rw [if_neg (fun h : 1 = 1 ∧ l = 1 => hl1 h.2), mul_zero]
    · intro m hm hm1
      apply sum_eq_zero
      intro l hl
      rw [if_neg (fun h : m = 1 ∧ l = 1 => hm1 h.1), mul_zero]
  have hexpand :
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, y⟫ =
        ⟪yd, y⟫ +
          (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
            b m * b l * signedCriticalConductorResidual (c N) N m l) +
          (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, b m * b l *
            (if m = 1 ∧ l = 1 then tiltedPolarFinitePart * (c N / Real.log N) else 0)) := by
    simp only [y, yd, map_sum, map_smul]
    simp only [sum_inner]
    simp only [inner_sum,
      real_inner_smul_left, real_inner_smul_right, ← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro l hl
    simp only [signedCriticalConductorResidual, inner_sub_left, real_inner_smul_left, E]
    ring
  have hid :
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, y⟫ - S - P =
        (⟪yd, y⟫ - S) + ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
          b m * b l * signedCriticalConductorResidual (c N) N m l := by
    rw [hexpand, hpolar]
    ring
  change |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, y⟫ - S - P| ≤ ε * S
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hgram b) (hres b)).trans_eq (by ring))

/-- The polar finite part of the tilted spline is nonnegative. -/
theorem tiltedPolarFinitePart_nonneg : 0 ≤ tiltedPolarFinitePart := by
  change 0 ≤ ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
    RHTower.poleSharpConstant
  exact mul_nonneg (div_nonneg (sq_nonneg _) integral_tiltedUnitSpline_sq_pos.le)
    RHTower.poleSharpConstant_pos.le

/-- Every positive critical ratio preserves half the conductor energy uniformly on the low packet. -/
theorem eventually_completeWeil_low_packet_energy_ge {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      (1 / 2 : ℝ) * ∑ m ∈ Icc 1 Q,
        completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, y⟫ := by
  filter_upwards [eventually_completeWeil_low_packet_signed_approx hc hR hcrit
    (by norm_num : (0 : ℝ) < 1 / 2)] with N hN
  intro b Q y
  have h := (abs_le.mp (hN b)).1
  have hpolar : 0 ≤ tiltedPolarFinitePart * (c N / Real.log N) * b 1 ^ 2 :=
    mul_nonneg (mul_nonneg tiltedPolarFinitePart_nonneg
      (div_nonneg (zero_le_one.trans (hc N)) (Real.log_natCast_nonneg N))) (sq_nonneg _)
  nlinarith only [h, hpolar]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_sum_signedCriticalRelativeSquare_low_packet
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_signedCriticalConductorResidual_low_packet_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_energy_weighted_gram_low_packet_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeil_low_packet_signed_approx
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeil_low_packet_energy_ge
