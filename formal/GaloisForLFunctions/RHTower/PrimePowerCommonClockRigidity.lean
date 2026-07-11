import GaloisForLFunctions.RHTower.PrimeEulerCommonClockRigidity
import GaloisForLFunctions.RHTower.RotationDip
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# One-prime all-power common-clock rigidity

Primewise reflected-modulus neutrality needs short logarithmic prime windows to defeat independently
chosen local phases.  A complete degree-one Euler ray has more structure: its prime-power amplitudes
are geometric and all levels use integer multiples of one phase.  Rotation recurrence then supplies
cofinally many levels with positive cosine, while a genuine off-line displacement would force those
cosines to decay to zero.

Thus reflected neutrality at every level of one prime-power ray pins the displacement to zero,
without any prime-distribution theorem.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Folding a real phase to the absolute principal angle does not change any cosine multiple. -/
theorem cos_nat_mul_eq_cos_nat_mul_abs_angle (theta : ℝ) (n : ℕ) :
    Real.cos ((n : ℝ) * theta) =
      Real.cos ((n : ℝ) * |(theta : Real.Angle).toReal|) := by
  let a : Real.Angle := theta
  let x : ℝ := a.toReal
  have hcoe : (x : Real.Angle) = a := Real.Angle.coe_toReal a
  have hleft : (((n : ℝ) * theta : ℝ) : Real.Angle) = n • a := by
    change (((n : ℝ) * theta : ℝ) : Real.Angle) = n • (theta : Real.Angle)
    rw [← Real.Angle.coe_nsmul]
    congr 1
    simp [nsmul_eq_mul]
  by_cases hx : 0 ≤ x
  · have hright : (((n : ℝ) * |x| : ℝ) : Real.Angle) = n • a := by
      rw [abs_of_nonneg hx]
      calc
        (((n : ℝ) * x : ℝ) : Real.Angle) = n • (x : Real.Angle) := by
          rw [← Real.Angle.coe_nsmul]
          congr 1
          simp [nsmul_eq_mul]
        _ = n • a := by rw [hcoe]
    rw [← Real.Angle.cos_coe, ← Real.Angle.cos_coe, hleft, hright]
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hright : (((n : ℝ) * |x| : ℝ) : Real.Angle) = -(n • a) := by
      rw [abs_of_neg hxneg]
      change (((n : ℝ) * (-x) : ℝ) : Real.Angle) = -(n • a)
      calc
        (((n : ℝ) * (-x) : ℝ) : Real.Angle) = n • ((-x : ℝ) : Real.Angle) := by
          rw [← Real.Angle.coe_nsmul]
          congr 1
          simp [nsmul_eq_mul]
        _ = n • (-(x : Real.Angle)) := by rw [Real.Angle.coe_neg]
        _ = -(n • (x : Real.Angle)) := by simp
        _ = -(n • a) := by rw [hcoe]
    rw [← Real.Angle.cos_coe, ← Real.Angle.cos_coe, hleft, hright,
      Real.Angle.cos_neg]

/-- Every real phase has cofinally many positive cosine multiples, uniformly bounded away from
zero by a phase-dependent constant. -/
theorem exists_pos_le_cos_nat_mul_cofinally (theta : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ N : ℕ, ∃ n : ℕ, N < n ∧ c ≤ Real.cos ((n : ℝ) * theta) := by
  let phi : ℝ := |(theta : Real.Angle).toReal|
  have hphi0 : 0 ≤ phi := abs_nonneg _
  have hphipi : phi ≤ Real.pi := Real.Angle.abs_toReal_le_pi (theta : Real.Angle)
  by_cases hphi : phi = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro N
    refine ⟨N + 1, by omega, ?_⟩
    rw [cos_nat_mul_eq_cos_nat_mul_abs_angle theta (N + 1)]
    change 1 ≤ Real.cos ((N + 1 : ℕ) * phi)
    rw [hphi]
    simp
  · by_cases hphipiEq : phi = Real.pi
    · refine ⟨1, zero_lt_one, ?_⟩
      intro N
      refine ⟨2 * (N + 1), by omega, ?_⟩
      rw [cos_nat_mul_eq_cos_nat_mul_abs_angle theta (2 * (N + 1))]
      change 1 ≤ Real.cos (((2 * (N + 1) : ℕ) : ℝ) * phi)
      rw [hphipiEq]
      have hangle : (((2 * (N + 1) : ℕ) : ℝ) * Real.pi) =
          (N + 1 : ℕ) * (2 * Real.pi) := by push_cast; ring
      rw [hangle, Real.cos_nat_mul_two_pi]
    · have hphipos : 0 < phi := lt_of_le_of_ne hphi0 (Ne.symm hphi)
      have hphilt : phi < Real.pi := lt_of_le_of_ne hphipi hphipiEq
      have hcpos : 0 < Real.cos (phi / 2) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> linarith [Real.pi_pos]
      refine ⟨Real.cos (phi / 2), hcpos, ?_⟩
      intro N
      obtain ⟨M, hMpos, _hMbound, hMcos⟩ :=
        exists_orbit_cos_ge (θ := phi) (γ := (N : ℝ) * phi)
          hphipos hphipi
      refine ⟨N + M, by omega, ?_⟩
      rw [cos_nat_mul_eq_cos_nat_mul_abs_angle theta (N + M)]
      change Real.cos (phi / 2) ≤ Real.cos (((N + M : ℕ) : ℝ) * phi)
      simpa only [Nat.cast_add, add_mul] using hMcos

/-- **One-prime all-power common-clock rigidity.** If every prime-power level of one degree-one
Euler ray is reflected-modulus neutral under the same phase, then the horizontal displacement is
zero. No prime-distribution input is needed. -/
theorem epsilon_eq_zero_of_primePower_reflected_modulus_neutral
    {p : ℕ} (hp : 1 < p) {epsilon theta : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hneutral : ∀ m : ℕ, 1 ≤ m →
      ‖(1 : ℂ) - ((((p : ℝ) ^ (-1 / 2 + epsilon)) ^ m : ℝ) : ℂ) *
          Complex.exp (((((m : ℝ) * theta : ℝ) : ℂ)) * Complex.I)‖ =
        ‖(1 : ℂ) - ((((p : ℝ) ^ (-1 / 2 - epsilon)) ^ m : ℝ) : ℂ) *
          Complex.exp (((((m : ℝ) * theta : ℝ) : ℂ)) * Complex.I)‖) :
    epsilon = 0 := by
  by_contra hepsilon
  have hepsilonPos : 0 < epsilon := lt_of_le_of_ne hepsilon0 (Ne.symm hepsilon)
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
  have hcos (m : ℕ) (hm : 1 ≤ m) :
      Real.cos ((m : ℝ) * theta) = (rplus ^ m + rminus ^ m) / 2 := by
    apply cos_eq_radius_average_of_norm_one_sub_mul_eq
    · exact ne_of_lt (pow_lt_pow_left₀ hrorder hrminusPos.le (by omega))
    · simpa only [rplus, rminus] using hneutral m hm
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
  have havg : Tendsto (fun m : ℕ => (rplus ^ m + rminus ^ m) / 2)
      atTop (nhds 0) := by
    simpa using (hplus.add hminus).div_const 2
  obtain ⟨c, hcpos, hrec⟩ := exists_pos_le_cos_nat_mul_cofinally theta
  have hevent : ∀ᶠ m : ℕ in atTop, (rplus ^ m + rminus ^ m) / 2 < c :=
    (tendsto_order.1 havg).2 c hcpos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨m, hNm, hcm⟩ := hrec N
  have hm1 : 1 ≤ m := by omega
  have havgm := hN m hNm.le
  rw [hcos m hm1] at hcm
  linarith

/-! ## Asymptotic normalized neutrality -/

/-- The reflected squared-modulus defect at level `m`, divided by the natural gap between the two
geometric radii.  This normalization retains the phase information that an unnormalized defect
loses as both radii decay. -/
def primePowerNormalizedReflectedModulusDefect
    (p : ℕ) (epsilon theta : ℝ) (m : ℕ) : ℝ :=
  let rplus : ℝ := (p : ℝ) ^ (-1 / 2 + epsilon)
  let rminus : ℝ := (p : ℝ) ^ (-1 / 2 - epsilon)
  (‖(1 : ℂ) - ((rplus ^ m : ℝ) : ℂ) *
        Complex.exp (((m : ℝ) * theta : ℂ) * Complex.I)‖ ^ 2 -
      ‖(1 : ℂ) - ((rminus ^ m : ℝ) : ℂ) *
        Complex.exp (((m : ℝ) * theta : ℂ) * Complex.I)‖ ^ 2) /
    (2 * (rplus ^ m - rminus ^ m))

/-- The normalized reflected defect is the decaying radial average minus the common-clock phase
cosine. -/
theorem primePowerNormalizedReflectedModulusDefect_eq
    {p m : ℕ} (hp : 1 < p) {epsilon theta : ℝ}
    (hepsilon : 0 < epsilon) (hm : 1 ≤ m) :
    primePowerNormalizedReflectedModulusDefect p epsilon theta m =
      (((p : ℝ) ^ (-1 / 2 + epsilon)) ^ m +
        ((p : ℝ) ^ (-1 / 2 - epsilon)) ^ m) / 2 -
        Real.cos ((m : ℝ) * theta) := by
  let rplus : ℝ := (p : ℝ) ^ (-1 / 2 + epsilon)
  let rminus : ℝ := (p : ℝ) ^ (-1 / 2 - epsilon)
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hrminusPos : 0 < rminus := Real.rpow_pos_of_pos (by positivity) _
  have hrorder : rminus < rplus := by
    exact Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith)
  have hpow : rminus ^ m < rplus ^ m :=
    pow_lt_pow_left₀ hrorder hrminusPos.le (by omega)
  have hgap : rplus ^ m - rminus ^ m ≠ 0 := sub_ne_zero.mpr hpow.ne'
  have hplusSq :
      ‖(1 : ℂ) - ((((p : ℝ) ^ (-1 / 2 + epsilon)) ^ m : ℝ) : ℂ) *
          Complex.exp (((m : ℂ) * (theta : ℂ)) * Complex.I)‖ ^ 2 =
        1 + (((p : ℝ) ^ (-1 / 2 + epsilon)) ^ m) ^ 2 -
          2 * (((p : ℝ) ^ (-1 / 2 + epsilon)) ^ m) *
            Real.cos ((m : ℝ) * theta) := by
    simpa using norm_one_sub_real_mul_exp_mul_I_sq
      (((p : ℝ) ^ (-1 / 2 + epsilon)) ^ m) ((m : ℝ) * theta)
  have hminusSq :
      ‖(1 : ℂ) - ((((p : ℝ) ^ (-1 / 2 - epsilon)) ^ m : ℝ) : ℂ) *
          Complex.exp (((m : ℂ) * (theta : ℂ)) * Complex.I)‖ ^ 2 =
        1 + (((p : ℝ) ^ (-1 / 2 - epsilon)) ^ m) ^ 2 -
          2 * (((p : ℝ) ^ (-1 / 2 - epsilon)) ^ m) *
            Real.cos ((m : ℝ) * theta) := by
    simpa using norm_one_sub_real_mul_exp_mul_I_sq
      (((p : ℝ) ^ (-1 / 2 - epsilon)) ^ m) ((m : ℝ) * theta)
  rw [primePowerNormalizedReflectedModulusDefect]
  rw [show (((m : ℝ) : ℂ)) = (m : ℂ) by norm_num]
  rw [hplusSq, hminusSq]
  change
    ((1 + (rplus ^ m) ^ 2 - 2 * rplus ^ m * Real.cos ((m : ℝ) * theta)) -
      (1 + (rminus ^ m) ^ 2 - 2 * rminus ^ m * Real.cos ((m : ℝ) * theta))) /
        (2 * (rplus ^ m - rminus ^ m)) =
      (rplus ^ m + rminus ^ m) / 2 - Real.cos ((m : ℝ) * theta)
  field_simp [hgap]
  ring

/-- **Asymptotic one-prime all-power rigidity.** Exact reflected neutrality is unnecessary. If the
normalized reflected defect tends to zero along one complete prime-power ray, the horizontal
displacement is zero. -/
theorem epsilon_eq_zero_of_primePower_normalized_reflected_modulus_defect_tendsto_zero
    {p : ℕ} (hp : 1 < p) {epsilon theta : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hneutral : Tendsto
      (primePowerNormalizedReflectedModulusDefect p epsilon theta)
      atTop (nhds 0)) :
    epsilon = 0 := by
  by_contra hepsilon
  have hepsilonPos : 0 < epsilon := lt_of_le_of_ne hepsilon0 (Ne.symm hepsilon)
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
  have havg : Tendsto (fun m : ℕ => (rplus ^ m + rminus ^ m) / 2)
      atTop (nhds 0) := by
    simpa using (hplus.add hminus).div_const 2
  have hcos : Tendsto (fun m : ℕ => Real.cos ((m : ℝ) * theta))
      atTop (nhds 0) := by
    have hsub : Tendsto
        (fun m : ℕ => (rplus ^ m + rminus ^ m) / 2 -
          primePowerNormalizedReflectedModulusDefect p epsilon theta m)
        atTop (nhds 0) := by
      simpa using havg.sub hneutral
    apply hsub.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hm
    rw [primePowerNormalizedReflectedModulusDefect_eq hp hepsilonPos hm]
    dsimp [rplus, rminus]
    ring
  obtain ⟨c, hcpos, hrec⟩ := exists_pos_le_cos_nat_mul_cofinally theta
  have hevent : ∀ᶠ m : ℕ in atTop, Real.cos ((m : ℝ) * theta) < c :=
    (tendsto_order.1 hcos).2 c hcpos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨m, hNm, hcm⟩ := hrec N
  exact (not_lt_of_ge hcm) (hN m hNm.le)

end

end RHTower
