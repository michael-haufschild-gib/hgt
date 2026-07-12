import GaloisForLFunctions.RHTower.PrimePowerCommonClockRigidity
import GaloisForLFunctions.RHTower.GaussLattice
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Mean-square one-prime common-clock rigidity

Pointwise decay of the normalized reflected defect is stronger than a Gram or trace source naturally
produces. This file replaces it by vanishing Cesaro mean-square energy. For a genuine horizontal
displacement, the defect is a decaying radial term minus `cos (m * theta)`. The discrete mean square
of the common-clock cosine is `1/2`, except at the resonant phases where it is `1`; hence its energy
cannot vanish.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem tendsto_complex_geom_cesaro_of_norm_eq_one_of_ne_one
    {w : ℂ} (hw : ‖w‖ = 1) (hne : w ≠ 1) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, w ^ m)
      atTop (nhds 0) := by
  apply squeeze_zero_norm'
    (a := fun N : ℕ => (2 / ‖1 - w‖) / (N : ℝ))
  · exact Eventually.of_forall fun N => by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg N)]
      calc
        (N : ℝ)⁻¹ * ‖∑ m ∈ Finset.range N, w ^ m‖
            ≤ (N : ℝ)⁻¹ * (2 / ‖1 - w‖) :=
              mul_le_mul_of_nonneg_left (norm_geom_sum_le hw hne N)
                (inv_nonneg.mpr (Nat.cast_nonneg N))
        _ = (2 / ‖1 - w‖) / (N : ℝ) := by ring
  · simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖1 - w‖))

private theorem tendsto_cos_two_mul_cesaro_of_exp_ne_one (theta : ℝ)
    (hne : Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I) ≠ 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ m ∈ Finset.range N, Real.cos (2 * (m : ℝ) * theta))
      atTop (nhds 0) := by
  let w : ℂ := Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I)
  have hw : ‖w‖ = 1 := by
    simp [w, Complex.norm_exp]
  have hwne : w ≠ 1 := by simpa [w] using hne
  have h := tendsto_complex_geom_cesaro_of_norm_eq_one_of_ne_one hw hwne
  have hre := (Complex.continuous_re.tendsto (0 : ℂ)).comp h
  apply hre.congr'
  exact Eventually.of_forall fun N => by
    change ((((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, w ^ m).re) = _
    have hsum : (∑ m ∈ Finset.range N, w ^ m).re =
        ∑ m ∈ Finset.range N, Real.cos (2 * (m : ℝ) * theta) := by
      rw [← Complex.reCLM_apply, map_sum]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [w]
      rw [← Complex.exp_nat_mul]
      change (Complex.exp ((m : ℂ) * (((2 * theta : ℝ) : ℂ) * Complex.I))).re = _
      rw [show (m : ℂ) * (((2 * theta : ℝ) : ℂ) * Complex.I) =
          (((2 * (m : ℝ) * theta : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
      rw [Complex.exp_ofReal_mul_I_re]
    rw [Complex.mul_re]
    norm_num [hsum]

private theorem tendsto_cos_sq_cesaro_of_exp_ne_one (theta : ℝ)
    (hne : Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I) ≠ 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ m ∈ Finset.range N, Real.cos ((m : ℝ) * theta) ^ 2)
      atTop (nhds (1 / 2 : ℝ)) := by
  have hcos := tendsto_cos_two_mul_cesaro_of_exp_ne_one theta hne
  have hlim : Tendsto
      (fun N : ℕ => (1 / 2 : ℝ) + (1 / 2 : ℝ) *
        ((N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, Real.cos (2 * (m : ℝ) * theta)))
      atTop (nhds (1 / 2 : ℝ)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hcos) using 1
    all_goals norm_num
  apply hlim.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hpoint (m : ℕ) :
      Real.cos ((m : ℝ) * theta) ^ 2 =
        (1 + Real.cos (2 * (m : ℝ) * theta)) / 2 := by
    rw [show 2 * (m : ℝ) * theta = 2 * ((m : ℝ) * theta) by ring,
      Real.cos_two_mul]
    ring
  have hsumid :
      (∑ m ∈ Finset.range N, (1 + Real.cos (2 * (m : ℝ) * theta)) / 2) =
        ((N : ℝ) + ∑ m ∈ Finset.range N, Real.cos (2 * (m : ℝ) * theta)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp
  symm
  calc
    (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, Real.cos ((m : ℝ) * theta) ^ 2 =
        (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
          (1 + Real.cos (2 * (m : ℝ) * theta)) / 2 := by
            congr 1
            exact Finset.sum_congr rfl (fun m _ => hpoint m)
    _ = (N : ℝ)⁻¹ *
        ((N : ℝ) + ∑ m ∈ Finset.range N, Real.cos (2 * (m : ℝ) * theta)) / 2 := by
          rw [hsumid]
          ring
    _ = (1 / 2 : ℝ) + (1 / 2 : ℝ) *
        ((N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
          Real.cos (2 * (m : ℝ) * theta)) := by
            have harg (m : ℕ) : 2 * (m : ℝ) * theta = theta * (m : ℝ) * 2 := by ring
            simp_rw [harg]
            field_simp [hN0]
            ring

private theorem cos_sq_nat_mul_eq_one_of_exp_two_mul_I_eq_one (theta : ℝ)
    (heq : Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I) = 1) (m : ℕ) :
    Real.cos ((m : ℝ) * theta) ^ 2 = 1 := by
  have hpow := congrArg (fun z : ℂ => z ^ m) heq
  have hexp : Complex.exp ((((2 * (m : ℝ) * theta : ℝ) : ℂ)) * Complex.I) = 1 := by
    rw [show (((2 * (m : ℝ) * theta : ℝ) : ℂ) * Complex.I) =
        (m : ℂ) * (((2 * theta : ℝ) : ℂ) * Complex.I) by
          push_cast
          ring]
    rw [Complex.exp_nat_mul]
    simpa using hpow
  have hre := congrArg Complex.re hexp
  rw [Complex.exp_ofReal_mul_I_re] at hre
  norm_num at hre
  rw [show 2 * (m : ℝ) * theta = 2 * ((m : ℝ) * theta) by ring,
    Real.cos_two_mul] at hre
  nlinarith

private theorem tendsto_cos_sq_cesaro_of_exp_eq_one (theta : ℝ)
    (heq : Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I) = 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ m ∈ Finset.range N, Real.cos ((m : ℝ) * theta) ^ 2)
      atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with N hN
  symm
  rw [Finset.sum_congr rfl (fun m _ =>
    cos_sq_nat_mul_eq_one_of_exp_two_mul_I_eq_one theta heq m)]
  simp [Nat.ne_of_gt hN]

private theorem
    tendsto_primePowerNormalizedReflectedModulusDefect_cesaro_sq_sub_cos_sq
    {p : ℕ} (hp : 1 < p) {epsilon theta : ℝ}
    (hepsilonPos : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2) :
    Tendsto
      (fun N : ℕ =>
        ((N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
          primePowerNormalizedReflectedModulusDefect p epsilon theta m ^ 2) -
        ((N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
          Real.cos ((m : ℝ) * theta) ^ 2))
      atTop (nhds 0) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  let rplus : ℝ := (p : ℝ) ^ (-1 / 2 + epsilon)
  let rminus : ℝ := (p : ℝ) ^ (-1 / 2 - epsilon)
  have hrplusPos : 0 < rplus := Real.rpow_pos_of_pos (by positivity) _
  have hrminusPos : 0 < rminus := Real.rpow_pos_of_pos (by positivity) _
  have hrorder : rminus < rplus := by
    exact Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith)
  have hrplusOne : rplus < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  have hrminusOne : rminus < 1 := hrorder.trans hrplusOne
  have hrplusNorm : ‖rplus‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrplusPos]
    exact hrplusOne
  have hrminusNorm : ‖rminus‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrminusPos]
    exact hrminusOne
  have hplus : Tendsto (fun m : ℕ => rplus ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hrplusNorm
  have hminus : Tendsto (fun m : ℕ => rminus ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hrminusNorm
  let a : ℕ → ℝ := fun m => (rplus ^ m + rminus ^ m) / 2
  have ha : Tendsto a atTop (nhds 0) := by
    simpa [a] using (hplus.add hminus).div_const 2
  have hac : Tendsto (fun m : ℕ => a m * Real.cos ((m : ℝ) * theta))
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (g := fun m => ‖a m‖)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · exact Eventually.of_forall fun m => by
        rw [norm_mul]
        have hcosnorm : ‖Real.cos ((m : ℝ) * theta)‖ ≤ 1 := by
          simpa [Real.norm_eq_abs] using Real.abs_cos_le_one ((m : ℝ) * theta)
        exact mul_le_of_le_one_right (norm_nonneg (a m)) hcosnorm
    · simpa using ha.norm
  have hdelta : Tendsto
      (fun m : ℕ =>
        primePowerNormalizedReflectedModulusDefect p epsilon theta m ^ 2 -
          Real.cos ((m : ℝ) * theta) ^ 2)
      atTop (nhds 0) := by
    have hmodel : Tendsto
        (fun m : ℕ => a m ^ 2 - 2 * (a m * Real.cos ((m : ℝ) * theta)))
        atTop (nhds 0) := by
      simpa using (ha.pow 2).sub (tendsto_const_nhds.mul hac)
    apply hmodel.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with m hm
    rw [primePowerNormalizedReflectedModulusDefect_eq hp hepsilonPos hm]
    dsimp [a, rplus, rminus]
    ring
  have hdeltaCesaro := hdelta.cesaro
  simpa only [Finset.sum_sub_distrib, mul_sub] using hdeltaCesaro

/-- **Universal off-line one-ray energy law.** For a positive horizontal displacement, the Cesaro
mean-square normalized reflected defect converges to `1/2`; at the resonant common-clock phases
`exp (2 i theta) = 1`, it converges to `1`. Thus every off-line displacement carries a universal
quadratic energy floor of `1/2`. -/
theorem primePowerNormalizedReflectedModulusDefect_cesaro_sq_tendsto_of_pos
    {p : ℕ} (hp : 1 < p) {epsilon theta : ℝ}
    (hepsilonPos : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
        primePowerNormalizedReflectedModulusDefect p epsilon theta m ^ 2)
      atTop (nhds (if Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I) = 1
        then 1 else (1 / 2 : ℝ))) := by
  have hdiff :=
    tendsto_primePowerNormalizedReflectedModulusDefect_cesaro_sq_sub_cos_sq
      hp (theta := theta) hepsilonPos hepsilonHalf
  by_cases hphase : Complex.exp ((2 : ℂ) * (theta : ℂ) * Complex.I) = 1
  · have hphase' : Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I) = 1 := by
      simpa using hphase
    have hcos := tendsto_cos_sq_cesaro_of_exp_eq_one theta hphase'
    simpa [hphase] using hdiff.add hcos
  · have hphase' : Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I) ≠ 1 := by
      simpa using hphase
    have hcos := tendsto_cos_sq_cesaro_of_exp_ne_one theta hphase'
    simpa [hphase] using hdiff.add hcos

/-- **Mean-square one-prime all-power rigidity.** If the Cesaro mean-square energy of the normalized
reflected defect vanishes on one complete prime-power ray, then the horizontal displacement is zero.
This weakens pointwise defect decay to the averaged quadratic form naturally exposed by Gram and
trace constructions. -/
theorem epsilon_eq_zero_of_primePower_normalized_reflected_modulus_defect_cesaro_sq
    {p : ℕ} (hp : 1 < p) {epsilon theta : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (henergy : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
        primePowerNormalizedReflectedModulusDefect p epsilon theta m ^ 2)
      atTop (nhds 0)) :
    epsilon = 0 := by
  by_contra hepsilon
  have hepsilonPos : 0 < epsilon := lt_of_le_of_ne hepsilon0 (Ne.symm hepsilon)
  have hlimit := primePowerNormalizedReflectedModulusDefect_cesaro_sq_tendsto_of_pos
    hp (theta := theta) hepsilonPos hepsilonHalf
  have hzero := tendsto_nhds_unique hlimit henergy
  by_cases hphase : Complex.exp ((2 : ℂ) * (theta : ℂ) * Complex.I) = 1
  · norm_num [hphase] at hzero
  · norm_num [hphase] at hzero

/-- **Sub-half one-ray energy pins the critical line.** It is unnecessary to prove that the
normalized reflected-defect energy vanishes. Any eventual uniform upper bound strictly below the
universal off-line floor `1/2` already forces the horizontal displacement to be zero. -/
theorem epsilon_eq_zero_of_primePower_normalized_reflected_modulus_defect_eventually_lt_half
    {p : ℕ} (hp : 1 < p) {epsilon theta : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (henergy : ∃ c : ℝ, c < 1 / 2 ∧
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
          primePowerNormalizedReflectedModulusDefect p epsilon theta m ^ 2 ≤ c) :
    epsilon = 0 := by
  by_contra hepsilon
  have hepsilonPos : 0 < epsilon := lt_of_le_of_ne hepsilon0 (Ne.symm hepsilon)
  obtain ⟨c, hc, hbound⟩ := henergy
  have hlimit := primePowerNormalizedReflectedModulusDefect_cesaro_sq_tendsto_of_pos
    hp (theta := theta) hepsilonPos hepsilonHalf
  have hle := le_of_tendsto hlimit hbound
  by_cases hphase : Complex.exp ((2 : ℂ) * (theta : ℂ) * Complex.I) = 1
  · norm_num [hphase] at hle
    linarith
  · norm_num [hphase] at hle
    linarith

end

end RHTower
