import GaloisForLFunctions.RHTower.SourceHorizontalAbelianClassLawInformationEvacuation
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixThetaConditioningLyapunov

/-!
# Gamma-six shell amplification cannot replenish the abelian source aperture

The most literal cross-corpus renewal attempt pairs canonical abelian two-class apertures at the
ordered Gamma-six labels `(2,3)` and amplifies them by the complete coefficient-faithful
two-orientation Gamma-six shell.  Exact exponent bookkeeping shows that this still evacuates on
every Xi divisor copy.  Sharp geometric majorants are

* forward base `6^(2*a-2)`, exposing twice the Xi strip slack `1-a`;
* reverse base `6^(a-2)`.

Thus natural shell rank supplies horizontal amplification but cannot pay the source admission
cost.  Prime labels, both reflection orientations, and analytic multiplicity copies are retained.
No RH premise, numerical computation, or asymptotic hypothesis is used.
-/

open Real Set MeasureTheory Filter Topology

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

def sourceHorizontalGammaSixForwardApertureTrace
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (m : ℕ) : ℝ :=
  sourceHorizontalAbelianTwoClassAdmission
      (sourceHorizontalAbelianForwardParameters a ha0 ha1)
      ⟨2, Nat.prime_two⟩ m *
    sourceHorizontalAbelianTwoClassAdmission
      (sourceHorizontalAbelianForwardParameters a ha0 ha1)
      ⟨3, Nat.prime_three⟩ m *
    deningerGammaSixTwoOrientationShellTraceMass a m

def sourceHorizontalGammaSixReverseApertureTrace
    (a : ℝ) (ha0 : 0 ≤ a) (m : ℕ) : ℝ :=
  sourceHorizontalAbelianTwoClassAdmission
      (sourceHorizontalAbelianReverseParameters a ha0)
      ⟨2, Nat.prime_two⟩ m *
    sourceHorizontalAbelianTwoClassAdmission
      (sourceHorizontalAbelianReverseParameters a ha0)
      ⟨3, Nat.prime_three⟩ m *
    deningerGammaSixTwoOrientationShellTraceMass a m

theorem sourceHorizontalAbelianForwardUnnormalizedAdmission_le_stripSharp
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) (_ha1 : a < 1) :
    (p : ℝ) ^ ((a - 2) * (N + 1)) + (p : ℝ) ^ (-2 * N - 1 + a) ≤
      ((p : ℝ) + 1) * (p : ℝ) ^ ((a - 2) * (N + 1)) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  have hNr : (0 : ℝ) ≤ N := by positivity
  have hexp : -2 * (N : ℝ) - 1 + a ≤
      (a - 2) * ((N : ℝ) + 1) + 1 := by
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hp hexp
  have hrhs : (p : ℝ) ^ ((a - 2) * ((N : ℝ) + 1) + 1) =
      (p : ℝ) ^ ((a - 2) * ((N : ℝ) + 1)) * (p : ℝ) := by
    rw [Real.rpow_add (by exact_mod_cast p.2.pos), Real.rpow_one]
  rw [hrhs] at hpow
  nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ p)
    ((a - 2) * ((N : ℝ) + 1))]

theorem sourceHorizontalAbelianReverseUnnormalizedAdmission_le_stripSharp
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N) {a : ℝ} (ha0 : 0 ≤ a) :
    (p : ℝ) ^ (-(a + 2) * (N + 1)) + (p : ℝ) ^ (-2 * N - 1 - a) ≤
      2 * (p : ℝ) ^ (-2 * N - 1 - a) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  have hNr : (0 : ℝ) ≤ N := by positivity
  have hexp : -(a + 2) * ((N : ℝ) + 1) ≤
      -2 * (N : ℝ) - 1 - a := by
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hp hexp
  nlinarith

private theorem six_rpow_forward_strip_factor
    {a : ℝ} (ha1 : a < 1) :
    0 ≤ (6 : ℝ) ^ (2 * a - 2) ∧ (6 : ℝ) ^ (2 * a - 2) < 1 := by
  exact ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

private theorem forward_strip_majorant_shell_eq
    {a : ℝ} (ha0 : 0 ≤ a) {m : ℕ} (hm : 3 ≤ m) :
    ((2 : ℝ) + 1) * (2 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) *
        (((3 : ℝ) + 1) * (3 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1))) *
          deningerGammaSixTwoOrientationShellTraceMass a m =
      (60 * (6 : ℝ) ^ (a - 2)) * ((6 : ℝ) ^ (2 * a - 2)) ^ m := by
  rw [deningerGammaSixTwoOrientationShellTraceMass_eq_five_mul_exp_distortion hm,
    deningerGammaSixBalancingLogDistortion_eq, abs_of_nonneg ha0]
  rw [show (m : ℝ) * Real.log 6 * a = Real.log 6 * ((m : ℝ) * a) by ring,
    ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
  rw [show
      ((2 : ℝ) + 1) * (2 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) *
          (((3 : ℝ) + 1) * (3 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1))) *
            (5 * (6 : ℝ) ^ ((m : ℝ) * a)) =
        60 * ((2 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) *
          (3 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1))) *
            (6 : ℝ) ^ ((m : ℝ) * a) by ring,
    ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num only
  rw [show
      60 * (6 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) * (6 : ℝ) ^ ((m : ℝ) * a) =
        60 * ((6 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) *
          (6 : ℝ) ^ ((m : ℝ) * a)) by ring,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  rw [← Real.rpow_natCast ((6 : ℝ) ^ (2 * a - 2)) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  rw [show
      60 * (6 : ℝ) ^ (a - 2) * (6 : ℝ) ^ ((2 * a - 2) * (m : ℝ)) =
        60 * ((6 : ℝ) ^ (a - 2) * (6 : ℝ) ^ ((2 * a - 2) * (m : ℝ))) by ring,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  congr 1
  ring_nf

theorem tendsto_sourceHorizontalGammaSixForwardApertureTrace_zero
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (sourceHorizontalGammaSixForwardApertureTrace a ha0 ha1)
      atTop (nhds 0) := by
  let c := ((sourceHorizontalAbelianForwardParameters a ha0 ha1).ennNormalizer).toReal
  let r := (6 : ℝ) ^ (2 * a - 2)
  have hr := six_rpow_forward_strip_factor ha1
  have hlim : Tendsto
      (fun m : ℕ => (60 * c ^ 2 * (6 : ℝ) ^ (a - 2)) * r ^ m)
      atTop (nhds 0) :=
    by simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2).const_mul
        (60 * c ^ 2 * (6 : ℝ) ^ (a - 2))
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 3] with m hm
    unfold sourceHorizontalGammaSixForwardApertureTrace
    apply mul_nonneg
    · apply mul_nonneg
      · unfold sourceHorizontalAbelianTwoClassAdmission
        exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      · unfold sourceHorizontalAbelianTwoClassAdmission
        exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · rw [deningerGammaSixTwoOrientationShellTraceMass_eq_five_mul_exp_distortion hm]
      positivity
  · filter_upwards [eventually_ge_atTop 3] with m hm
    have h2 := sourceHorizontalAbelianForwardUnnormalizedAdmission_le_stripSharp
      ⟨2, Nat.prime_two⟩ m (by omega) ha0 ha1
    have h3 := sourceHorizontalAbelianForwardUnnormalizedAdmission_le_stripSharp
      ⟨3, Nat.prime_three⟩ m (by omega) ha0 ha1
    have h2' :
        (2 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) +
            (2 : ℝ) ^ (-2 * (m : ℝ) - 1 + a) ≤
          ((2 : ℝ) + 1) * (2 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) := by
      convert h2 using 1 <;> norm_num
    have h3' :
        (3 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) +
            (3 : ℝ) ^ (-2 * (m : ℝ) - 1 + a) ≤
          ((3 : ℝ) + 1) * (3 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)) := by
      convert h3 using 1 <;> norm_num
    unfold sourceHorizontalGammaSixForwardApertureTrace
    rw [
      sourceHorizontalAbelianForwardAdmission_eq ⟨2, Nat.prime_two⟩ m (by omega) ha0 ha1,
      sourceHorizontalAbelianForwardAdmission_eq ⟨3, Nat.prime_three⟩ m (by omega) ha0 ha1]
    change (c * _) * (c * _) * _ ≤ _
    have hc : 0 ≤ c := ENNReal.toReal_nonneg
    have hshell : 0 ≤ deningerGammaSixTwoOrientationShellTraceMass a m := by
      rw [deningerGammaSixTwoOrientationShellTraceMass_eq_five_mul_exp_distortion hm]
      positivity
    have h2c := mul_le_mul_of_nonneg_left h2' hc
    have h3c := mul_le_mul_of_nonneg_left h3' hc
    calc
      (c * _) * (c * _) * deningerGammaSixTwoOrientationShellTraceMass a m ≤
          (c * (((2 : ℝ) + 1) * (2 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)))) *
            (c * (((3 : ℝ) + 1) * (3 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)))) *
              deningerGammaSixTwoOrientationShellTraceMass a m := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul h2c h3c
            (by positivity)
            (mul_nonneg hc (by positivity))) hshell
      _ = (60 * c ^ 2 * (6 : ℝ) ^ (a - 2)) * r ^ m := by
        rw [show
          (c * (((2 : ℝ) + 1) * (2 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)))) *
              (c * (((3 : ℝ) + 1) * (3 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1)))) *
                deningerGammaSixTwoOrientationShellTraceMass a m =
            c ^ 2 *
              ((((2 : ℝ) + 1) * (2 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1))) *
                (((3 : ℝ) + 1) * (3 : ℝ) ^ ((a - 2) * ((m : ℝ) + 1))) *
                  deningerGammaSixTwoOrientationShellTraceMass a m) by ring,
          forward_strip_majorant_shell_eq ha0 hm]
        dsimp only [r]
        ring

private theorem six_rpow_reverse_strip_factor
    {a : ℝ} (ha1 : a < 1) :
    0 ≤ (6 : ℝ) ^ (a - 2) ∧ (6 : ℝ) ^ (a - 2) < 1 := by
  exact ⟨by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

private theorem reverse_strip_majorant_shell_eq
    {a : ℝ} (ha0 : 0 ≤ a) {m : ℕ} (hm : 3 ≤ m) :
    (2 * (2 : ℝ) ^ (-2 * (m : ℝ) - 1 - a)) *
        (2 * (3 : ℝ) ^ (-2 * (m : ℝ) - 1 - a)) *
          deningerGammaSixTwoOrientationShellTraceMass a m =
      (20 * (6 : ℝ) ^ (-1 - a)) * ((6 : ℝ) ^ (a - 2)) ^ m := by
  rw [deningerGammaSixTwoOrientationShellTraceMass_eq_five_mul_exp_distortion hm,
    deningerGammaSixBalancingLogDistortion_eq, abs_of_nonneg ha0]
  rw [show (m : ℝ) * Real.log 6 * a = Real.log 6 * ((m : ℝ) * a) by ring,
    ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
  rw [show
      (2 * (2 : ℝ) ^ (-2 * (m : ℝ) - 1 - a)) *
          (2 * (3 : ℝ) ^ (-2 * (m : ℝ) - 1 - a)) *
            (5 * (6 : ℝ) ^ ((m : ℝ) * a)) =
        20 * ((2 : ℝ) ^ (-2 * (m : ℝ) - 1 - a) *
          (3 : ℝ) ^ (-2 * (m : ℝ) - 1 - a)) *
            (6 : ℝ) ^ ((m : ℝ) * a) by ring,
    ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num only
  rw [show
      20 * (6 : ℝ) ^ (-2 * (m : ℝ) - 1 - a) * (6 : ℝ) ^ ((m : ℝ) * a) =
        20 * ((6 : ℝ) ^ (-2 * (m : ℝ) - 1 - a) *
          (6 : ℝ) ^ ((m : ℝ) * a)) by ring,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  rw [← Real.rpow_natCast ((6 : ℝ) ^ (a - 2)) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  rw [show
      20 * (6 : ℝ) ^ (-1 - a) * (6 : ℝ) ^ ((a - 2) * (m : ℝ)) =
        20 * ((6 : ℝ) ^ (-1 - a) * (6 : ℝ) ^ ((a - 2) * (m : ℝ))) by ring,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  congr 1
  ring_nf

theorem tendsto_sourceHorizontalGammaSixReverseApertureTrace_zero
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (sourceHorizontalGammaSixReverseApertureTrace a ha0)
      atTop (nhds 0) := by
  let c := ((sourceHorizontalAbelianReverseParameters a ha0).ennNormalizer).toReal
  let r := (6 : ℝ) ^ (a - 2)
  have hr := six_rpow_reverse_strip_factor ha1
  have hlim : Tendsto
      (fun m : ℕ => (20 * c ^ 2 * (6 : ℝ) ^ (-1 - a)) * r ^ m)
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2).const_mul
        (20 * c ^ 2 * (6 : ℝ) ^ (-1 - a))
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 3] with m hm
    unfold sourceHorizontalGammaSixReverseApertureTrace
    apply mul_nonneg
    · apply mul_nonneg
      · unfold sourceHorizontalAbelianTwoClassAdmission
        exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      · unfold sourceHorizontalAbelianTwoClassAdmission
        exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · rw [deningerGammaSixTwoOrientationShellTraceMass_eq_five_mul_exp_distortion hm]
      positivity
  · filter_upwards [eventually_ge_atTop 3] with m hm
    have h2 := sourceHorizontalAbelianReverseUnnormalizedAdmission_le_stripSharp
      ⟨2, Nat.prime_two⟩ m (by omega) ha0
    have h3 := sourceHorizontalAbelianReverseUnnormalizedAdmission_le_stripSharp
      ⟨3, Nat.prime_three⟩ m (by omega) ha0
    have h2' :
        (2 : ℝ) ^ (-(a + 2) * ((m : ℝ) + 1)) +
            (2 : ℝ) ^ (-2 * (m : ℝ) - 1 - a) ≤
          2 * (2 : ℝ) ^ (-2 * (m : ℝ) - 1 - a) := by
      convert h2 using 1 <;> norm_num
    have h3' :
        (3 : ℝ) ^ (-(a + 2) * ((m : ℝ) + 1)) +
            (3 : ℝ) ^ (-2 * (m : ℝ) - 1 - a) ≤
          2 * (3 : ℝ) ^ (-2 * (m : ℝ) - 1 - a) := by
      convert h3 using 1 <;> norm_num
    unfold sourceHorizontalGammaSixReverseApertureTrace
    rw [
      sourceHorizontalAbelianReverseAdmission_eq ⟨2, Nat.prime_two⟩ m (by omega) ha0,
      sourceHorizontalAbelianReverseAdmission_eq ⟨3, Nat.prime_three⟩ m (by omega) ha0]
    change (c * _) * (c * _) * _ ≤ _
    have hc : 0 ≤ c := ENNReal.toReal_nonneg
    have hshell : 0 ≤ deningerGammaSixTwoOrientationShellTraceMass a m := by
      rw [deningerGammaSixTwoOrientationShellTraceMass_eq_five_mul_exp_distortion hm]
      positivity
    have h2c := mul_le_mul_of_nonneg_left h2' hc
    have h3c := mul_le_mul_of_nonneg_left h3' hc
    calc
      (c * _) * (c * _) * deningerGammaSixTwoOrientationShellTraceMass a m ≤
          (c * (2 * (2 : ℝ) ^ (-2 * (m : ℝ) - 1 - a))) *
            (c * (2 * (3 : ℝ) ^ (-2 * (m : ℝ) - 1 - a))) *
              deningerGammaSixTwoOrientationShellTraceMass a m := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul h2c h3c
            (by positivity)
            (mul_nonneg hc (by positivity))) hshell
      _ = (20 * c ^ 2 * (6 : ℝ) ^ (-1 - a)) * r ^ m := by
        rw [show
          (c * (2 * (2 : ℝ) ^ (-2 * (m : ℝ) - 1 - a))) *
              (c * (2 * (3 : ℝ) ^ (-2 * (m : ℝ) - 1 - a))) *
                deningerGammaSixTwoOrientationShellTraceMass a m =
            c ^ 2 *
              ((2 * (2 : ℝ) ^ (-2 * (m : ℝ) - 1 - a)) *
                (2 * (3 : ℝ) ^ (-2 * (m : ℝ) - 1 - a)) *
                  deningerGammaSixTwoOrientationShellTraceMass a m) by ring,
          reverse_strip_majorant_shell_eq ha0 hm]
        dsimp only [r]
        ring

/-- For every multiplicity-labelled Xi zero, both natural Gamma-six attempts to replenish the
canonical two-class source aperture still lose all admitted mass. -/
theorem sourceHorizontalXiGammaSixAbelianStripSlack_evacuates
    (q : XiZeroCopy) :
    let a := |primeDepthBVWoldXiCenteredRate q.1|
    Tendsto
        (sourceHorizontalGammaSixForwardApertureTrace a (abs_nonneg _)
          (sourceHorizontalXiCenteredRate_abs_lt_one q)) atTop (nhds 0) ∧
      Tendsto
        (sourceHorizontalGammaSixReverseApertureTrace a (abs_nonneg _))
          atTop (nhds 0) := by
  dsimp only
  exact ⟨
    tendsto_sourceHorizontalGammaSixForwardApertureTrace_zero
      (abs_nonneg _) (sourceHorizontalXiCenteredRate_abs_lt_one q),
    tendsto_sourceHorizontalGammaSixReverseApertureTrace_zero
      (abs_nonneg _) (sourceHorizontalXiCenteredRate_abs_lt_one q)⟩

end

end RHTower
