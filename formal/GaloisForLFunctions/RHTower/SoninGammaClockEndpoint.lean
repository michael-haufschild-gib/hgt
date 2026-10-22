import GaloisForLFunctions.RHTower.SoninPrimePolarChronologicalWork
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilArchimedeanOddSource
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Gamma clock endpoint and its exact relative ground completion

The literal clock-divided Gamma density has a forced homogeneous singular
part. Exact physical annulus pairings prove that its symmetric finite-cutoff
vectors diverge on every positive-aperture ground cutoff. After retaining
that principal term, the exact remainder is absolutely Bochner integrable
and has one limit for every cofinal removal of both cutoffs.

These are statements about the explicitly defined Gamma family. Identification
with the completed TG source and admission on the full Hardy carrier are
separate obligations. No RH conclusion is asserted.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem entry_inner (a : ℝ) (ha : 0 ≤ a) (u v : ℝ) :
    inner ℂ (soninGroundEntry a u) (soninGroundEntry a v) =
      ((2*a*Real.exp (-max u v):ℝ):ℂ) := by
  rcases le_total u v with h | h
  · rw [max_eq_right h]
    exact inner_soninGroundEntry_of_le a ha u v h
  · rw [← inner_conj_symm, inner_soninGroundEntry_of_le a ha v u h,
      Complex.conj_ofReal, max_eq_left h]

private theorem entry_norm_sq (a : ℝ) (ha : 0 ≤ a) (u : ℝ) :
    ‖soninGroundEntry a u‖^2 = 2*a*Real.exp (-u) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_soninGroundEntry_of_le a ha u u le_rfl]
  rfl

private theorem orbit_eq_entry (a u : ℝ) :
    rayDilate (Real.exp u) (soninCutoffMonomial a 0) =
      (Real.exp (u/2):ℂ) • soninGroundEntry a u := by
  rw [soninGroundEntry, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
  rw [show u/2+-u/2=0 by ring, Real.exp_zero, Complex.ofReal_one, one_smul]

/-- Literal symmetric dilation difference on the actual ground cutoff. -/
def gammaGroundDifference (a u : ℝ) : SoninL2 :=
  rayDilate (Real.exp u) (soninCutoffMonomial a 0)+
    rayDilate (Real.exp (-u)) (soninCutoffMonomial a 0)-
      (2:ℂ) • soninGroundEntry a 0

private theorem difference_eq_entries (a u : ℝ) :
    gammaGroundDifference a u =
      (Real.exp (u/2):ℂ) • soninGroundEntry a u+
        (Real.exp (-u/2):ℂ) • soninGroundEntry a (-u)-
          (2:ℂ) • soninGroundEntry a 0 := by
  rw [gammaGroundDifference, orbit_eq_entry, orbit_eq_entry]

/-- The actual physical annulus exposed by a lower Gamma cutoff. -/
def gammaGroundEndpointShell (a ε : ℝ) : SoninL2 := soninGroundEntry a 0-soninGroundEntry a ε

private theorem shell_norm_sq (a : ℝ) (ha : 0 ≤ a) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖gammaGroundEndpointShell a ε‖^2 = 2*a*(1-Real.exp (-ε)) := by
  rw [gammaGroundEndpointShell, norm_sub_sq (𝕜 := ℂ), entry_norm_sq a ha, entry_norm_sq a ha,
    inner_soninGroundEntry_of_le a ha 0 ε hε]
  change 2*a*Real.exp (-0)-2*(2*a*Real.exp (-ε))+2*a*Real.exp (-ε) = _
  rw [neg_zero, Real.exp_zero]
  ring

/-- Exact inner-annulus response; no estimate or asymptotic replacement. -/
theorem inner_gammaGroundEndpointShell_difference (a : ℝ) (ha : 0 ≤ a)
    (ε u : ℝ) (hε : 0 ≤ ε) (hεu : ε ≤ u) :
    inner ℂ (gammaGroundEndpointShell a ε) (gammaGroundDifference a u) =
      ((2*a*(1-Real.exp (-ε))*(Real.exp (-u/2)-2):ℝ):ℂ) := by
  have hu : 0 ≤ u := hε.trans hεu
  rw [gammaGroundEndpointShell, difference_eq_entries]
  simp only [inner_sub_left, inner_sub_right, inner_add_right, inner_smul_right,
    entry_inner a ha, max_eq_right hu, max_eq_right hεu,
    max_eq_left (neg_nonpos.mpr hu), max_eq_left (le_trans (neg_nonpos.mpr hu) hε),
    max_self, max_eq_left hε, neg_zero, Real.exp_zero, mul_one]
  push_cast
  ring

private theorem continuous_difference (a : ℝ) : Continuous (gammaGroundDifference a) := by
  change Continuous (fun u => gammaGroundDifference a u)
  simp_rw [difference_eq_entries]
  have h := continuous_soninGroundEntry a
  fun_prop

private theorem density_continuous {ε b : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun u => ccmPublishedArchimedeanDensity u/u) (Icc ε b) := by
  intro u hu
  have hu0 : 0 < u := hε.trans_le hu.1
  have hden : Real.exp u-Real.exp (-u) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))).ne'
  have hn : ContinuousAt (fun t : ℝ => Real.exp (t/2)) u := by fun_prop
  have hd : ContinuousAt (fun t : ℝ => Real.exp t-Real.exp (-t)) u := by fun_prop
  exact ((hn.div hd hden).div continuousAt_id hu0.ne').continuousWithinAt

/-- Finite-cutoff Gamma clock-divided ground vector, with the exact density. -/
def gammaGroundTruncated (a ε b : ℝ) : SoninL2 :=
  ∫ u in Icc ε b, ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) • gammaGroundDifference a u

private theorem gamma_integrable (a ε b : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun u => ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
      gammaGroundDifference a u) (Icc ε b) :=
  ((Complex.continuous_ofReal.comp_continuousOn (density_continuous (b := b) hε)).smul
    (continuous_difference a).continuousOn).integrableOn_Icc

/-- Exact finite Gamma boundary pairing, retaining its literal archimedean density. -/
theorem inner_gammaGroundEndpointShell_truncated (a : ℝ) (ha : 0 ≤ a)
    (ε b : ℝ) (hε : 0 < ε) :
    inner ℂ (gammaGroundEndpointShell a ε) (gammaGroundTruncated a ε b) =
      ((2*a*(1-Real.exp (-ε))*
        ∫ u in Icc ε b, (Real.exp (-u/2)-2)*ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) := by
  rw [gammaGroundTruncated, ← integral_inner (gamma_integrable a ε b hε),
    Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [inner_smul_right, inner_gammaGroundEndpointShell_difference a ha ε u hε.le hu.1]
  push_cast
  ring

private def gammaWork (u : ℝ) : ℝ :=
  (2-Real.exp (-u/2))*(ccmPublishedArchimedeanDensity u/u)

private theorem gamma_density_pos {u : ℝ} (hu : 0 < u) :
    0 < ccmPublishedArchimedeanDensity u := by
  rw [ccmPublishedArchimedeanDensity]
  exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))

private theorem gamma_density_lower {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    1/(4*u) ≤ ccmPublishedArchimedeanDensity u := by
  rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu]
  have hd : 0 < 1-Real.exp (-2*u) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  apply (div_le_div_iff₀ (by positivity) hd).mpr
  have hn : 1/2 ≤ Real.exp (-u/2) := by linarith [Real.add_one_le_exp (-u/2)]
  have hden : 1-Real.exp (-2*u) ≤ 2*u := by linarith [Real.add_one_le_exp (-2*u)]
  nlinarith

private theorem gammaWork_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ gammaWork u := by
  have he : Real.exp (-u/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold gammaWork
  exact mul_nonneg (by linarith) (div_nonneg (gamma_density_pos hu).le hu.le)

private theorem gammaWork_integrable (ε b : ℝ) (hε : 0 < ε) :
    IntegrableOn gammaWork (Icc ε b) := by
  have hc : Continuous (fun u : ℝ => 2-Real.exp (-u/2)) := by fun_prop
  exact (hc.continuousOn.mul (density_continuous hε)).integrableOn_Icc

private theorem gammaWork_local_lower {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (hu : u ∈ Icc ε (2*ε)) : 1/(16*ε^2) ≤ gammaWork u := by
  have hu0 : 0 < u := hε.trans_le hu.1
  have hu1 : u ≤ 1 := by linarith [hu.2]
  have he : Real.exp (-u/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hγ := gamma_density_lower hu0 hu1
  calc
    1/(16*ε^2) ≤ 1/(4*u^2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [pow_le_pow_left₀ hu0.le hu.2 2]
    _ = (1/(4*u))/u := by field_simp
    _ ≤ ccmPublishedArchimedeanDensity u/u := div_le_div_of_nonneg_right hγ hu0.le
    _ ≤ gammaWork u := by
      unfold gammaWork
      nlinarith [div_nonneg (gamma_density_pos hu0).le hu0.le]

private theorem gammaWork_integral_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    1/(16*ε) ≤ ∫ u in Icc ε 1, gammaWork u := by
  have hs : Icc ε (2*ε) ⊆ Icc ε 1 := fun u hu => ⟨hu.1, by linarith [hu.2]⟩
  calc
    1/(16*ε) = ∫ _u in Icc ε (2*ε), (1/(16*ε^2):ℝ) := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      field_simp
      ring
    _ ≤ ∫ u in Icc ε (2*ε), gammaWork u :=
      setIntegral_mono_on continuous_const.integrableOn_Icc
        (gammaWork_integrable ε (2*ε) hε) measurableSet_Icc
        (fun u hu => gammaWork_local_lower hε hε1 hu)
    _ ≤ _ := setIntegral_mono_set (gammaWork_integrable ε 1 hε)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
          exact gammaWork_nonneg (hε.trans_le hu.1)) (Eventually.of_forall hs)

private theorem shell_mass_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε/2 ≤ 1-Real.exp (-ε) := by
  have hinv : Real.exp (-ε) ≤ (1+ε)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos ε) (by positivity)).mpr (by linarith [Real.add_one_le_exp ε])
  have hid : (1+ε)⁻¹*(1+ε)=1 := inv_mul_cancel₀ (by positivity)
  have h : (1-Real.exp (-ε))*(1+ε) ≥ ε := by nlinarith
  have hn : 0 ≤ 1-Real.exp (-ε) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  nlinarith

private theorem inner_shell_gamma_negative (a : ℝ) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    inner ℂ (gammaGroundEndpointShell a ε) (gammaGroundTruncated a ε 1) =
      ((-(2*a*(1-Real.exp (-ε)))*(∫ u in Icc ε 1, gammaWork u):ℝ):ℂ) := by
  rw [inner_gammaGroundEndpointShell_truncated a ha ε 1 hε]
  have hi : (∫ u in Icc ε 1, (Real.exp (-u/2)-2)*ccmPublishedArchimedeanDensity u/u) =
      -(∫ u in Icc ε 1, gammaWork u) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with u
    unfold gammaWork
    ring
  rw [hi]
  congr 1
  ring

/-- The actual Gamma clock-divided source has a nonzero inverse-cutoff energy residue. -/
theorem gammaGroundTruncated_energy_lower (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    a/256 ≤ ε*‖gammaGroundTruncated a ε 1‖^2 := by
  let M := 2*a*(1-Real.exp (-ε))
  let J := ∫ u in Icc ε 1, gammaWork u
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos (by positivity) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hJ : 1/(16*ε) ≤ J := gammaWork_integral_lower hε hε1
  have hJ0 : 0 ≤ J := le_trans (by positivity) hJ
  have hn := norm_inner_le_norm (𝕜 := ℂ) (gammaGroundEndpointShell a ε) (gammaGroundTruncated a ε 1)
  rw [inner_shell_gamma_negative a ha.le ε hε] at hn
  change ‖(((-M)*J:ℝ):ℂ)‖ ≤ _ at hn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_pos hM, abs_of_nonneg hJ0] at hn
  have hl : M/(16*ε) ≤ ‖gammaGroundEndpointShell a ε‖*‖gammaGroundTruncated a ε 1‖ := by
    calc
      _ = M*(1/(16*ε)) := by ring
      _ ≤ M*J := mul_le_mul_of_nonneg_left hJ hM.le
      _ ≤ _ := hn
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ M/(16*ε)) hl 2
  rw [div_pow, mul_pow ‖gammaGroundEndpointShell a ε‖, shell_norm_sq a ha.le ε hε.le] at hs
  change M^2/(16*ε)^2 ≤ M*‖gammaGroundTruncated a ε 1‖^2 at hs
  have hs' := (div_le_iff₀ (by positivity : 0 < (16*ε)^2)).mp hs
  have hc : M ≤ ‖gammaGroundTruncated a ε 1‖^2*(16*ε)^2 := by
    apply le_of_mul_le_mul_left ?_ hM
    calc
      M*M = M^2 := by ring
      _ ≤ (M*‖gammaGroundTruncated a ε 1‖^2)*(16*ε)^2 := hs'
      _ = _ := by ring
  have hm : a*ε ≤ M := by
    have h := mul_le_mul_of_nonneg_left (shell_mass_lower hε (by linarith))
      (show 0 ≤ 2*a by positivity)
    dsimp [M]
    nlinarith
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<256)).mpr
  apply le_of_mul_le_mul_left ?_ hε
  nlinarith [hm.trans hc]

/-- Divergence occurs on every approach to the lower Gamma endpoint. -/
theorem gammaGroundTruncated_norm_tendsto_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ‖gammaGroundTruncated a ε 1‖) (𝓝[>] 0) atTop := by
  apply tendsto_atTop.2
  intro B
  have hd : 0 < a/(256*(B^2+1)) := by positivity
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (min (1/2) (a/(256*(B^2+1)))) :=
    (nhdsGT_basis (0:ℝ)).mem_of_mem (lt_min (by norm_num) hd)
  filter_upwards [he] with ε hε
  have heps : 0 < ε := hε.1
  have hhalf : ε ≤ 1/2 := (lt_of_lt_of_le hε.2 (min_le_left _ _)).le
  have hsmall : ε*(256*(B^2+1)) < a :=
    (lt_div_iff₀ (by positivity)).mp (lt_of_lt_of_le hε.2 (min_le_right _ _))
  have hbound := gammaGroundTruncated_energy_lower a ha ε heps hhalf
  have hbound' := (div_le_iff₀ (by norm_num : (0:ℝ)<256)).mp hbound
  by_contra h
  have hn : ‖gammaGroundTruncated a ε 1‖ < B := lt_of_not_ge h
  have hs : ‖gammaGroundTruncated a ε 1‖^2 ≤ B^2 := by
    nlinarith [norm_nonneg (gammaGroundTruncated a ε 1)]
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 256*ε by positivity)
  nlinarith

private theorem ground_orbit_difference_norm_sq (a : ℝ) (ha : 0 ≤ a) (u : ℝ) :
    ‖rayDilate (Real.exp u) (soninCutoffMonomial a 0)-soninGroundEntry a 0‖^2 =
      4*a*(1-Real.exp (-|u|/2)) := by
  have hz : soninGroundEntry a 0 = rayDilate (Real.exp 0) (soninCutoffMonomial a 0) := by
    simp [soninGroundEntry]
  rw [hz, norm_sub_sq (𝕜 := ℂ), norm_rayDilate (Real.exp_pos _),
    norm_rayDilate (Real.exp_pos _), inner_logDilation_soninCutoffMonomial,
    norm_sq_soninCutoffMonomial a ha 0]
  simp only [mul_zero, zero_add, pow_one, Nat.cast_zero, div_one, sub_zero]
  change 2*a-2*(2*a*Real.exp (-(1/2)*|u|))+2*a = _
  rw [show -(1/2)*|u| = -|u|/2 by ring]
  ring

/-- Actual cutoff geometry gives a square-root modulus for the symmetric difference. -/
theorem gammaGroundDifference_norm_sq_le (a : ℝ) (ha : 0 ≤ a) (u : ℝ) (hu : 0 ≤ u) :
    ‖gammaGroundDifference a u‖^2 ≤ 8*a*u := by
  let x := rayDilate (Real.exp u) (soninCutoffMonomial a 0)-soninGroundEntry a 0
  let y := rayDilate (Real.exp (-u)) (soninCutoffMonomial a 0)-soninGroundEntry a 0
  have hx : ‖x‖^2 = 4*a*(1-Real.exp (-u/2)) := by
    simpa only [x, abs_of_nonneg hu] using ground_orbit_difference_norm_sq a ha u
  have hy : ‖y‖^2 = 4*a*(1-Real.exp (-u/2)) := by
    simpa only [y, abs_neg, abs_of_nonneg hu] using ground_orbit_difference_norm_sq a ha (-u)
  have hxy : ‖x‖ = ‖y‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hx.trans hy.symm)
  have hf : gammaGroundDifference a u = x+y := by
    dsimp [gammaGroundDifference, x, y]
    module
  have hn : ‖gammaGroundDifference a u‖ ≤ 2*‖x‖ := by
    rw [hf]
    have h := norm_add_le x y
    rw [← hxy] at h
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow, hx] at hs
  have he := Real.add_one_le_exp (-u/2)
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 16*a by positivity)
  nlinarith

private theorem difference_norm_sqrt_le (a : ℝ) (ha : 0 ≤ a) (u : ℝ) (hu : 0 ≤ u) :
    ‖gammaGroundDifference a u‖ ≤ Real.sqrt (8*a)*Real.sqrt u := by
  have hs : (Real.sqrt (8*a)*Real.sqrt u)^2 = 8*a*u := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hu]
  have h := gammaGroundDifference_norm_sq_le a ha u hu
  nlinarith [norm_nonneg (gammaGroundDifference a u),
    mul_nonneg (Real.sqrt_nonneg (8*a)) (Real.sqrt_nonneg u)]

/-- Exact density after retaining the forced homogeneous Gamma principal part. -/
def gammaClockRemainderDensity (u : ℝ) : ℝ :=
  ccmPublishedArchimedeanDensity u/u-1/(2*u^2)

private theorem gamma_density_positive_exp {u : ℝ} (_hu : 0 < u) :
    ccmPublishedArchimedeanDensity u = Real.exp (3*u/2)/(Real.exp (2*u)-1) := by
  have hd : Real.exp u-Real.exp (-u) = Real.exp (-u)*(Real.exp (2*u)-1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  have hn : Real.exp (u/2) = Real.exp (3*u/2)*Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ccmPublishedArchimedeanDensity, hn, hd]
  field_simp

/-- One degree of endpoint singularity is removed by the source-forced principal part. -/
theorem gammaClockRemainderDensity_near_zero {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1/2) :
    |gammaClockRemainderDensity u| ≤ (5/2)/u := by
  have hd : 0 < Real.exp (2*u)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
  have he1 := Real.abs_exp_sub_one_le (x := 3*u/2)
    (by rw [abs_of_nonneg (by positivity)]; linarith)
  have he2 := Real.abs_exp_sub_one_sub_id_le (x := 2*u)
    (by rw [abs_of_nonneg (by positivity)]; linarith)
  rw [abs_of_nonneg (by positivity : 0 ≤ 3*u/2)] at he1
  have hn : |2*u*(Real.exp (3*u/2)-1)-(Real.exp (2*u)-1-2*u)| ≤ 10*u^2 := by
    calc
      _ ≤ |2*u*(Real.exp (3*u/2)-1)|+|Real.exp (2*u)-1-2*u| := abs_sub _ _
      _ = (2*u)*|Real.exp (3*u/2)-1|+|Real.exp (2*u)-1-2*u| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 2*u)]
      _ ≤ (2*u)*(2*(3*u/2))+(2*u)^2 := by gcongr
      _ = _ := by ring
  have hid : ccmPublishedArchimedeanDensity u-1/(2*u) =
      (2*u*(Real.exp (3*u/2)-1)-(Real.exp (2*u)-1-2*u))/(2*u*(Real.exp (2*u)-1)) := by
    rw [gamma_density_positive_exp hu, div_sub_div _ _ hd.ne' (show 2*u ≠ 0 by positivity)]
    congr 1 <;> ring
  have hb : |ccmPublishedArchimedeanDensity u-1/(2*u)| ≤ 5/2 := by
    rw [hid, abs_div, abs_of_pos (by positivity : 0 < 2*u*(Real.exp (2*u)-1))]
    apply (div_le_iff₀ (by positivity)).mpr
    have he := Real.add_one_le_exp (2*u)
    have hm := mul_le_mul_of_nonneg_left he hu.le
    nlinarith
  have hr : gammaClockRemainderDensity u = (ccmPublishedArchimedeanDensity u-1/(2*u))/u := by
    unfold gammaClockRemainderDensity
    field_simp
  rw [hr, abs_div, abs_of_pos hu]
  exact div_le_div_of_nonneg_right hb hu.le

private theorem remainder_measurable : Measurable gammaClockRemainderDensity := by
  unfold gammaClockRemainderDensity ccmPublishedArchimedeanDensity
  fun_prop

private theorem remainder_ground_measurable (a : ℝ) :
    AEStronglyMeasurable (fun u => (gammaClockRemainderDensity u:ℂ) •
      gammaGroundDifference a u) volume :=
  ((Complex.continuous_ofReal.measurable.comp remainder_measurable).stronglyMeasurable.smul
    (continuous_difference a).stronglyMeasurable).aestronglyMeasurable

private theorem remainder_ground_integrable_zero (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun u => (gammaClockRemainderDensity u:ℂ) •
      gammaGroundDifference a u) (Ioo 0 (1/2)) := by
  have hi := ((intervalIntegral.integrableOn_Ioo_rpow_iff
    (s := -(1/2:ℝ)) (t := 1/2) (by norm_num)).mpr (by norm_num)).const_mul
      ((5/2)*Real.sqrt (8*a))
  apply hi.mono' ((remainder_ground_measurable a).restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ((5/2)/u)*(Real.sqrt (8*a)*Real.sqrt u) :=
      mul_le_mul (gammaClockRemainderDensity_near_zero hu.1 hu.2.le)
        (difference_norm_sqrt_le a ha u hu.1.le) (norm_nonneg _)
          (div_nonneg (by norm_num) hu.1.le)
    _ = ((5/2)*Real.sqrt (8*a))*u^(-(1/2:ℝ)) := by
      rw [show -(1/2:ℝ) = 1/2-1 by ring, Real.rpow_sub_one hu.1.ne', ← Real.sqrt_eq_rpow]
      ring

private theorem difference_norm_uniform (a u : ℝ) :
    ‖gammaGroundDifference a u‖ ≤ 4*‖soninCutoffMonomial a 0‖ := by
  have hz : ‖soninGroundEntry a 0‖ = ‖soninCutoffMonomial a 0‖ := by
    simp only [soninGroundEntry, neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one,
      one_smul, norm_rayDilate zero_lt_one]
  unfold gammaGroundDifference
  calc
    _ ≤ ‖rayDilate (Real.exp u) (soninCutoffMonomial a 0)+
      rayDilate (Real.exp (-u)) (soninCutoffMonomial a 0)‖+
        ‖(2:ℂ) • soninGroundEntry a 0‖ := norm_sub_le _ _
    _ ≤ (‖rayDilate (Real.exp u) (soninCutoffMonomial a 0)‖+
      ‖rayDilate (Real.exp (-u)) (soninCutoffMonomial a 0)‖)+
        ‖(2:ℂ) • soninGroundEntry a 0‖ := by gcongr; exact norm_add_le _ _
    _ = _ := by
      rw [norm_rayDilate (Real.exp_pos _), norm_rayDilate (Real.exp_pos _), norm_smul, hz]
      norm_num
      ring

private theorem gamma_density_at_infinity {u : ℝ} (hu : 1/2 ≤ u) :
    ccmPublishedArchimedeanDensity u/u ≤
      (2/(1-Real.exp (-1)))*Real.exp (-u/2) := by
  have hu0 : 0 < u := by linarith
  have hd0 : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hd : 1-Real.exp (-1) ≤ 1-Real.exp (-2*u) := by
    have h := Real.exp_le_exp.mpr (show -2*u ≤ -1 by linarith)
    linarith
  rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu0]
  have hg : Real.exp (-u/2)/(1-Real.exp (-2*u)) ≤
      Real.exp (-u/2)/(1-Real.exp (-1)) :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hd0 hd
  calc
    _ ≤ (Real.exp (-u/2)/(1-Real.exp (-1)))/u :=
      div_le_div_of_nonneg_right hg hu0.le
    _ ≤ (Real.exp (-u/2)/(1-Real.exp (-1)))/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hu
    _ = _ := by ring

private theorem remainder_ground_integrable_infinity (a : ℝ) :
    IntegrableOn (fun u => (gammaClockRemainderDensity u:ℂ) •
      gammaGroundDifference a u) (Ioi (1/2)) := by
  have he := (integrableOn_exp_mul_Ioi (a := -(1/2:ℝ)) (by norm_num) (1/2)).const_mul
    (2/(1-Real.exp (-1)))
  have hp := (integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (c := 1/2)
    (by norm_num) (by norm_num)).const_mul (1/2:ℝ)
  have hi := (he.add hp).const_mul (4*‖soninCutoffMonomial a 0‖)
  apply hi.mono' ((remainder_ground_measurable a).restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := lt_trans (by norm_num : (0:ℝ) < 1/2) hu
  have hd0 : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hr : |gammaClockRemainderDensity u| ≤
      (2/(1-Real.exp (-1)))*Real.exp (-u/2)+(1/2)*u^(-2:ℝ) := by
    calc
      _ ≤ |ccmPublishedArchimedeanDensity u/u|+|1/(2*u^2)| := abs_sub _ _
      _ = ccmPublishedArchimedeanDensity u/u+1/(2*u^2) := by
        rw [abs_of_pos (div_pos (gamma_density_pos hu0) hu0), abs_of_pos (by positivity)]
      _ ≤ (2/(1-Real.exp (-1)))*Real.exp (-u/2)+1/(2*u^2) := by
        gcongr
        exact gamma_density_at_infinity hu.le
      _ = _ := by rw [Real.rpow_neg hu0.le, Real.rpow_two]; ring
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hm := mul_le_mul hr (difference_norm_uniform a u) (norm_nonneg _)
    (show 0 ≤ (2/(1-Real.exp (-1)))*Real.exp (-u/2)+(1/2)*u^(-2:ℝ) by positivity)
  change |gammaClockRemainderDensity u| * ‖gammaGroundDifference a u‖ ≤
    (4*‖soninCutoffMonomial a 0‖)*
      ((2/(1-Real.exp (-1)))*Real.exp (-(1/2:ℝ)*u)+(1/2)*u^(-2:ℝ))
  rw [show -(1/2:ℝ)*u = -u/2 by ring]
  exact hm.trans_eq (mul_comm _ _)

/-- The exact source-forced Gamma remainder admits the actual cutoff ground vector. -/
theorem gammaClockRemainder_ground_integrable (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun u => (gammaClockRemainderDensity u:ℂ) •
      gammaGroundDifference a u) (Ioi 0) := by
  have hz := remainder_ground_integrable_zero a ha
  have ht := (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (remainder_ground_integrable_infinity a)
  have hu := hz.union ht
  have hs : Ioo (0:ℝ) (1/2) ∪ Ici (1/2) = Ioi 0 := by
    ext u
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h|h) <;> linarith
    · intro h
      by_cases ht : u < 1/2
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr (le_of_not_gt ht)
  rwa [hs] at hu

/-- The homogeneous principal term forced by the actual Gamma density at zero. -/
def gammaHomogeneousGroundTruncated (a ε b : ℝ) : SoninL2 :=
  ∫ u in Icc ε b, ((1/(2*u^2):ℝ):ℂ) • gammaGroundDifference a u

private theorem homogeneous_integrable (a ε b : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun u => ((1/(2*u^2):ℝ):ℂ) • gammaGroundDifference a u) (Icc ε b) := by
  have hc : ContinuousOn (fun u : ℝ => ((1/(2*u^2):ℝ):ℂ)) (Icc ε b) := by
    intro u hu
    have hu0 : u ≠ 0 := (hε.trans_le hu.1).ne'
    have hd : 2*u^2 ≠ 0 := by positivity
    have hr : ContinuousAt (fun t : ℝ => 1/(2*t^2)) u := by fun_prop
    exact (Complex.continuous_ofReal.continuousAt.comp hr).continuousWithinAt
  exact (hc.smul (continuous_difference a).continuousOn).integrableOn_Icc

/-- Exact finite principal/remainder split: no Gamma source term is discarded. -/
theorem gammaGroundTruncated_sub_homogeneous (a ε b : ℝ) (hε : 0 < ε) :
    gammaGroundTruncated a ε b-gammaHomogeneousGroundTruncated a ε b =
      ∫ u in Icc ε b, (gammaClockRemainderDensity u:ℂ) • gammaGroundDifference a u := by
  rw [gammaGroundTruncated, gammaHomogeneousGroundTruncated,
    ← integral_sub (gamma_integrable a ε b hε) (homogeneous_integrable a ε b hε)]
  congr 1
  funext u
  simp only [gammaClockRemainderDensity, Complex.ofReal_sub, sub_smul]

/-- Actual ground value of the admitted relative Gamma operator. -/
def gammaClockRemainderGround (a : ℝ) : SoninL2 :=
  ∫ u in Ioi 0, (gammaClockRemainderDensity u:ℂ) • gammaGroundDifference a u

/-- Every cofinal removal of the two cutoffs gives the same exact relative Gamma vector. -/
theorem gammaGroundTruncated_sub_homogeneous_tendsto
    (a : ℝ) (ha : 0 ≤ a) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε b : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hb : Tendsto b l atTop) :
    Tendsto (fun i => gammaGroundTruncated a (ε i) (b i)-
      gammaHomogeneousGroundTruncated a (ε i) (b i)) l (𝓝 (gammaClockRemainderGround a)) := by
  have hc : AECover (volume.restrict (Ioi (0:ℝ))) l (fun i => Icc (ε i) (b i)) :=
    (aecover_Ioi_of_Ici (hε.mono_right nhdsWithin_le_nhds)).inter (aecover_Iic hb)
  have ht := hc.integral_tendsto_of_countably_generated (gammaClockRemainder_ground_integrable a ha)
  apply ht.congr'
  filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
  rw [Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (show Icc (ε i) (b i) ⊆ Ioi 0 from fun x hx => lt_of_lt_of_le hi hx.1)]
  exact (gammaGroundTruncated_sub_homogeneous a (ε i) (b i) hi).symm

end RHTower
