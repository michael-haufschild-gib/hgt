import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiPrimePowerSignClassification

/-!
# Two-sided Jordan escape for exact Suzuki curvature

The exact signed Suzuki checkpoint curvature has infinite positive and negative Jordan mass after
every uniformly nondegenerate positive diagonal gauge. Positive mass is forced on the explicit
multiple-of-six lattice; negative mass is forced at every sufficiently large prime endpoint.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter
open GaloisForLFunctions.RHTower
open scoped Interval

/-- Positive Jordan mass of the exact signed Suzuki curvature cell. -/
def suzukiCheckpointSignedCurvaturePositiveMass (N : ℕ) : ℝ :=
  max (suzukiCheckpointSignedCurvatureCell N) 0

/-- Negative Jordan mass of the exact signed Suzuki curvature cell. -/
def suzukiCheckpointSignedCurvatureNegativeMass (N : ℕ) : ℝ :=
  max (-suzukiCheckpointSignedCurvatureCell N) 0

theorem jordanEscape_sqrt_endpoint_data {k : ℕ} (hk : 4 ≤ k) :
    let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
    let b := Real.sqrt (k : ℝ)
    0 < a ∧ 0 < b ∧ a ≤ b ∧
      (b - a) * (b + a) = 1 ∧ 23 * b ≤ 27 * a :=
  sqrt_endpoint_data hk

theorem jordanEscape_integral_checkpoint_upper {k : ℕ} (hk : 3 ≤ k) :
    (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t) ≤
      2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) :=
  integral_screwRegularKernel_checkpoint_upper hk

theorem jordanEscape_integral_checkpoint_lower {k : ℕ} (hk : 4 ≤ k) :
    (4 / 5 : ℝ) / Real.sqrt k ≤
      ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t :=
  integral_screwRegularKernel_checkpoint_lower hk

theorem jordanEscape_expHalf_checkpoint_scaled_le {k : ℕ} (hk : 4 ≤ k) :
    2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) * Real.sqrt k ≤ 27 / 25 :=
  expHalf_checkpoint_scaled_le hk

private theorem jordanEscape_not_isPrimePow_six_mul_succ (m : ℕ) :
    ¬ IsPrimePow (6 * (m + 1)) := by
  have hn2 : 2 ≤ 6 * (m + 1) := by omega
  rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le hn2]
  refine ⟨2, Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ?_, by omega⟩,
    3, Nat.mem_primeFactors.mpr ⟨Nat.prime_three, ?_, by omega⟩, by norm_num⟩
  · exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) _
  · exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) _

/-- Positive curvature mass dominates one sixth of the shifted harmonic series on the explicit
multiple-of-six endpoint lattice. -/
theorem suzukiCheckpointSignedCurvaturePositiveMass_ge_sixthHarmonic (m : ℕ) :
    1 / ((6 * (m + 1) : ℕ) : ℝ) ≤
      suzukiCheckpointSignedCurvaturePositiveMass (6 * m + 5) := by
  let k := 6 * (m + 1)
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  have hsqrtSq : (Real.sqrt (k : ℝ)) ^ (2 : ℕ) = (k : ℝ) := Real.sq_sqrt hkpos.le
  have hsqrtTwo : (2 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    have hkFour : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [Real.sqrt_nonneg (k : ℝ)]
  have hfrac : 1 / (k : ℝ) ≤ (4 / 5 : ℝ) / Real.sqrt (k : ℝ) := by
    rw [div_le_div_iff₀ hkpos hsqrt]
    nlinarith
  have hnot := jordanEscape_not_isPrimePow_six_mul_succ m
  have hvm : ArithmeticFunction.vonMangoldt k = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot
  have hlower := jordanEscape_integral_checkpoint_lower hk
  have hindex : 6 * m + 5 = k - 1 := by dsimp [k]; omega
  rw [hindex, suzukiCheckpointSignedCurvaturePositiveMass]
  have hpos := suzukiCheckpointSignedCurvatureCell_pos_of_not_primePower
    (k := k) (by omega : 3 ≤ k) hnot
  rw [max_eq_left hpos.le]
  unfold suzukiCheckpointSignedCurvatureCell
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k), criticalMellinAtomWeight_eq_div_sqrt, hvm]
  simp only [zero_div, sub_zero]
  exact hfrac.trans hlower

/-- At every prime endpoint `p ≥ 11`, negative curvature mass dominates the prime harmonic atom. -/
theorem suzukiCheckpointSignedCurvatureNegativeMass_ge_primeHarmonic
    (p : Nat.Primes) (hp11 : 11 ≤ (p : ℕ)) :
    1 / ((p : ℕ) : ℝ) ≤
      suzukiCheckpointSignedCurvatureNegativeMass ((p : ℕ) - 1) := by
  let k : ℕ := p
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  have hsqrtSq : (Real.sqrt (k : ℝ)) ^ (2 : ℕ) = (k : ℝ) := Real.sq_sqrt hkpos.le
  have hsqrtTwo : (2 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    have hkFour : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [Real.sqrt_nonneg (k : ℝ)]
  have hupper := jordanEscape_integral_checkpoint_upper (k := k) (by omega : 3 ≤ k)
  have hscale := jordanEscape_expHalf_checkpoint_scaled_le hk
  have hintScaled :
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          screwRegularKernel t) * Real.sqrt k ≤ 27 / 25 := by
    exact (mul_le_mul_of_nonneg_right hupper hsqrt.le).trans hscale
  have hlogNine : (9 / 5 : ℝ) < Real.log 9 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_three_gt_d9]
  have hlogMono : Real.log 9 ≤ Real.log (k : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact hkpos
    · exact_mod_cast (by omega : 9 ≤ k)
  have hlogLower : (9 / 5 : ℝ) < Real.log (k : ℝ) := hlogNine.trans_le hlogMono
  have hvm : ArithmeticFunction.vonMangoldt k = Real.log (k : ℝ) := by
    exact ArithmeticFunction.vonMangoldt_apply_prime p.property
  have hcell : suzukiCheckpointSignedCurvatureCell (k - 1) =
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t) - Real.log (k : ℝ) / Real.sqrt (k : ℝ) := by
    unfold suzukiCheckpointSignedCurvatureCell
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k), criticalMellinAtomWeight_eq_div_sqrt, hvm]
  have hnegLower : (18 / 25 : ℝ) / Real.sqrt (k : ℝ) ≤
      -suzukiCheckpointSignedCurvatureCell (k - 1) := by
    rw [hcell, div_le_iff₀ hsqrt]
    have hcancel : Real.log (k : ℝ) / Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) =
        Real.log (k : ℝ) := by field_simp
    nlinarith
  have hfrac : 1 / (k : ℝ) ≤ (18 / 25 : ℝ) / Real.sqrt (k : ℝ) := by
    rw [div_le_div_iff₀ hkpos hsqrt]
    nlinarith
  rw [suzukiCheckpointSignedCurvatureNegativeMass]
  have hnegNonneg : 0 ≤ -suzukiCheckpointSignedCurvatureCell (k - 1) := by
    have hconstPos : 0 < (18 / 25 : ℝ) / Real.sqrt (k : ℝ) := by positivity
    linarith
  rw [max_eq_left hnegNonneg]
  exact hfrac.trans hnegLower

/-- Every uniformly nondegenerate diagonal gauge leaves positive Jordan sector nonsummable. -/
theorem not_summable_suzukiCheckpointSignedCurvaturePositiveMass_mul_of_uniformLowerBound
    (w : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (hw : ∀ N, ε ≤ w N) :
    ¬ Summable (fun N => w N * suzukiCheckpointSignedCurvaturePositiveMass N) := by
  intro hsummable
  let i : ℕ → ℕ := fun m => 6 * m + 5
  have hi : Function.Injective i := by
    intro a b hab
    dsimp [i] at hab
    omega
  have hsubsequence : Summable (fun m =>
      w (i m) * suzukiCheckpointSignedCurvaturePositiveMass (i m)) :=
    hsummable.comp_injective hi
  have hscaled : Summable (fun m => ε⁻¹ *
      (w (i m) * suzukiCheckpointSignedCurvaturePositiveMass (i m))) :=
    hsubsequence.mul_left ε⁻¹
  have hdom : ∀ m : ℕ, 1 / ((6 * (m + 1) : ℕ) : ℝ) ≤ ε⁻¹ *
      (w (i m) * suzukiCheckpointSignedCurvaturePositiveMass (i m)) := by
    intro m
    have hmass := suzukiCheckpointSignedCurvaturePositiveMass_ge_sixthHarmonic m
    have hmass0 : 0 ≤ suzukiCheckpointSignedCurvaturePositiveMass (i m) := by
      exact le_max_right _ _
    have hweighted : ε / ((6 * (m + 1) : ℕ) : ℝ) ≤
        w (i m) * suzukiCheckpointSignedCurvaturePositiveMass (i m) := by
      calc
        ε / ((6 * (m + 1) : ℕ) : ℝ) =
            ε * (1 / ((6 * (m + 1) : ℕ) : ℝ)) := by ring
        _ ≤ ε * suzukiCheckpointSignedCurvaturePositiveMass (i m) :=
          mul_le_mul_of_nonneg_left hmass hε.le
        _ ≤ w (i m) * suzukiCheckpointSignedCurvaturePositiveMass (i m) :=
          mul_le_mul_of_nonneg_right (hw (i m)) hmass0
    calc
      1 / ((6 * (m + 1) : ℕ) : ℝ) =
          ε⁻¹ * (ε / ((6 * (m + 1) : ℕ) : ℝ)) := by
            field_simp [hε.ne']
      _ ≤ ε⁻¹ * (w (i m) * suzukiCheckpointSignedCurvaturePositiveMass (i m)) :=
        mul_le_mul_of_nonneg_left hweighted (inv_nonneg.mpr hε.le)
  have hsixth : Summable (fun m : ℕ => 1 / ((6 * (m + 1) : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hdom hscaled
  have hshifted : Summable (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) := by
    have hmul := hsixth.mul_left (6 : ℝ)
    apply hmul.congr
    intro m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    field_simp [hm.ne']
  have hnotShifted : ¬ Summable (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) := by
    exact mt
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
      Real.not_summable_one_div_natCast
  exact hnotShifted hshifted

/-- Every uniformly nondegenerate diagonal gauge leaves negative Jordan sector nonsummable. -/
theorem not_summable_suzukiCheckpointSignedCurvatureNegativeMass_mul_of_uniformLowerBound
    (w : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (hw : ∀ N, ε ≤ w N) :
    ¬ Summable (fun N => w N * suzukiCheckpointSignedCurvatureNegativeMass N) := by
  intro hsummable
  let i : Nat.Primes → ℕ := fun p => (p : ℕ) - 1
  have hi : Function.Injective i := by
    intro p q hpq
    apply Subtype.ext
    dsimp [i] at hpq
    have hp2 := p.property.two_le
    have hq2 := q.property.two_le
    omega
  have hsubsequence : Summable (fun p : Nat.Primes =>
      w (i p) * suzukiCheckpointSignedCurvatureNegativeMass (i p)) :=
    hsummable.comp_injective hi
  have hscaled : Summable (fun p : Nat.Primes => ε⁻¹ *
      (w (i p) * suzukiCheckpointSignedCurvatureNegativeMass (i p))) :=
    hsubsequence.mul_left ε⁻¹
  have hlarge : ∀ᶠ p : Nat.Primes in cofinite, 11 ≤ (p : ℕ) := by
    rw [Filter.eventually_cofinite]
    have hval : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
    simp only [Nat.not_le]
    change ((fun p : Nat.Primes => (p : ℕ)) ⁻¹' Set.Iio 11).Finite
    exact (Set.finite_Iio 11).preimage hval.injOn
  let patched : Nat.Primes → ℝ := fun p =>
    if 11 ≤ (p : ℕ) then
      ε⁻¹ * (w (i p) * suzukiCheckpointSignedCurvatureNegativeMass (i p))
    else 1 / ((p : ℕ) : ℝ)
  have hpatched : Summable patched := by
    apply hscaled.congr_cofinite
    filter_upwards [hlarge] with p hp
    simp [patched, hp]
  have hdom : ∀ p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ≤ patched p := by
    intro p
    by_cases hp : 11 ≤ (p : ℕ)
    · have hmass := suzukiCheckpointSignedCurvatureNegativeMass_ge_primeHarmonic p hp
      have hmass0 : 0 ≤ suzukiCheckpointSignedCurvatureNegativeMass (i p) := by
        exact le_max_right _ _
      have hweighted : ε / ((p : ℕ) : ℝ) ≤
          w (i p) * suzukiCheckpointSignedCurvatureNegativeMass (i p) := by
        calc
          ε / ((p : ℕ) : ℝ) = ε * (1 / ((p : ℕ) : ℝ)) := by ring
          _ ≤ ε * suzukiCheckpointSignedCurvatureNegativeMass (i p) :=
            mul_le_mul_of_nonneg_left hmass hε.le
          _ ≤ w (i p) * suzukiCheckpointSignedCurvatureNegativeMass (i p) :=
            mul_le_mul_of_nonneg_right (hw (i p)) hmass0
      have hpatchedEq : patched p = ε⁻¹ *
          (w (i p) * suzukiCheckpointSignedCurvatureNegativeMass (i p)) := by
        simp [patched, hp]
      rw [hpatchedEq]
      calc
        1 / ((p : ℕ) : ℝ) = ε⁻¹ * (ε / ((p : ℕ) : ℝ)) := by
          field_simp [hε.ne']
        _ ≤ ε⁻¹ * (w (i p) * suzukiCheckpointSignedCurvatureNegativeMass (i p)) :=
          mul_le_mul_of_nonneg_left hweighted (inv_nonneg.mpr hε.le)
    · simp [patched, hp]
  have hone : Summable (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hdom hpatched
  exact Nat.Primes.not_summable_one_div hone

/-- **Suzuki curvature Jordan-gauge escape.** No uniformly nondegenerate positive diagonal gauge
turns both Jordan sectors of exact signed curvature source into summable families. -/
theorem no_uniformlyNondegenerate_summable_suzukiCheckpointCurvatureJordanGauge :
    ¬ ∃ (w : ℕ → ℝ) (ε : ℝ),
      0 < ε ∧
      (∀ N, ε ≤ w N) ∧
      Summable (fun N => w N * suzukiCheckpointSignedCurvaturePositiveMass N) ∧
      Summable (fun N => w N * suzukiCheckpointSignedCurvatureNegativeMass N) := by
  rintro ⟨w, ε, hε, hw, hpositive, hnegative⟩
  exact not_summable_suzukiCheckpointSignedCurvaturePositiveMass_mul_of_uniformLowerBound
    w ε hε hw hpositive

end RHTower
