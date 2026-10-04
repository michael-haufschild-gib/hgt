import GaloisForLFunctions.RHTower.SoninGammaClockEndpoint

/-!
# The Gamma endpoint cannot be repaired by distant prime-polar clocks

An exact mean-zero physical annulus probe annihilates every distant dilation.
It therefore annihilates the native finite prime-polar source with no bound
on the prime set or continuum upper endpoints. Its remaining one-signed
Gamma work forces joint norm divergence along every cofinal Gamma cutoff.

The positive survivor is the exact local source invariant, together with
the retained homogeneous reference and admitted remainder from
`SoninGammaClockEndpoint`. The raw bounded-ground assembly is excluded;
no RH falsification or completed Hardy identification is claimed.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
namespace RHTower

/-- Exact mass of the physical ground annulus. -/
def gammaClockAnnulusMass (a ε : ℝ) : ℝ := 2*a*(1-Real.exp (-ε))

/-- An actual mean-zero physical annulus probe, with all source coefficients retained. -/
def gammaClockAnnulusProbe (a ε : ℝ) : SoninL2 :=
  (gammaClockAnnulusMass a (2*ε):ℂ) • gammaGroundEndpointShell a ε-
    (gammaClockAnnulusMass a ε:ℂ) • gammaGroundEndpointShell a (2*ε)

private theorem annulus_entry_inner (a : ℝ) (ha : 0 ≤ a) (u v : ℝ) :
    inner ℂ (soninGroundEntry a u) (soninGroundEntry a v) =
      ((2*a*Real.exp (-max u v):ℝ):ℂ) := by
  rcases le_total u v with h|h
  · rw [max_eq_right h]
    exact inner_soninGroundEntry_of_le a ha u v h
  · rw [← inner_conj_symm, inner_soninGroundEntry_of_le a ha v u h,
      Complex.conj_ofReal, max_eq_left h]

private theorem probe_entry (a : ℝ) (ha : 0 ≤ a) (ε u : ℝ) :
    inner ℂ (gammaClockAnnulusProbe a ε) (soninGroundEntry a u) =
      ((gammaClockAnnulusMass a (2*ε)*2*a*(Real.exp (-max 0 u)-Real.exp (-max ε u))-
        gammaClockAnnulusMass a ε*2*a*(Real.exp (-max 0 u)-Real.exp (-max (2*ε) u)):ℝ):ℂ) := by
  simp only [gammaClockAnnulusProbe, gammaGroundEndpointShell, inner_sub_left,
    inner_smul_left, Complex.conj_ofReal, annulus_entry_inner a ha]
  push_cast
  ring

/-- Every clock outside the small positive annulus is annihilated exactly. -/
theorem inner_gammaClockAnnulusProbe_entry_eq_zero (a : ℝ) (ha : 0 ≤ a)
    (ε u : ℝ) (hε : 0 ≤ ε) (hu : u ≤ 0 ∨ 2*ε ≤ u) :
    inner ℂ (gammaClockAnnulusProbe a ε) (soninGroundEntry a u) = 0 := by
  rw [probe_entry a ha]
  rcases hu with hu|hu
  · rw [max_eq_left hu, max_eq_left (hu.trans hε),
      max_eq_left (hu.trans (by positivity : 0 ≤ 2*ε)), neg_zero, Real.exp_zero]
    unfold gammaClockAnnulusMass
    push_cast
    ring
  · rw [max_eq_right (le_trans (by positivity : 0 ≤ 2*ε) hu),
      max_eq_right (by linarith : ε ≤ u), max_eq_right hu]
    simp

/-- The primitive directions at distant clocks cannot change the annular Gamma test. -/
theorem inner_gammaClockAnnulusProbe_ray_eq_zero (a : ℝ) (ha : 0 ≤ a)
    (ε u : ℝ) (hε : 0 ≤ ε) (hu : u ≤ 0 ∨ 2*ε ≤ u) :
    inner ℂ (gammaClockAnnulusProbe a ε)
      (rayDilate (Real.exp u) (soninCutoffMonomial a 0)) = 0 := by
  have he : rayDilate (Real.exp u) (soninCutoffMonomial a 0) =
      (Real.exp (u/2):ℂ) • soninGroundEntry a u := by
    rw [soninGroundEntry, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show u/2+-u/2=0 by ring, Real.exp_zero, Complex.ofReal_one, one_smul]
  rw [he, inner_smul_right, inner_gammaClockAnnulusProbe_entry_eq_zero a ha ε u hε hu, mul_zero]

/-- The entire tested symmetric Gamma response is confined to its short local clock window. -/
theorem inner_gammaClockAnnulusProbe_difference (a : ℝ) (ha : 0 ≤ a)
    (ε u : ℝ) (hε : 0 ≤ ε) (hεu : ε ≤ u) :
    inner ℂ (gammaClockAnnulusProbe a ε) (gammaGroundDifference a u) =
      ((-2*a*gammaClockAnnulusMass a ε*Real.exp (u/2)*
        (Real.exp (-u)-Real.exp (-max (2*ε) u)):ℝ):ℂ) := by
  have hu : 0 ≤ u := hε.trans hεu
  have he : rayDilate (Real.exp u) (soninCutoffMonomial a 0) =
      (Real.exp (u/2):ℂ) • soninGroundEntry a u := by
    rw [soninGroundEntry, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show u/2+-u/2=0 by ring, Real.exp_zero, Complex.ofReal_one, one_smul]
  rw [gammaGroundDifference, inner_sub_right, inner_add_right, inner_smul_right,
    inner_gammaClockAnnulusProbe_entry_eq_zero a ha ε 0 hε (Or.inl le_rfl),
    inner_gammaClockAnnulusProbe_ray_eq_zero a ha ε (-u) hε (Or.inl (neg_nonpos.mpr hu)),
    mul_zero, add_zero, sub_zero, he, inner_smul_right, probe_entry a ha,
    max_eq_right hu, max_eq_right hεu]
  push_cast
  ring

/-- Exact norm of the physical mean-zero annulus probe. -/
theorem gammaClockAnnulusProbe_norm_sq (a : ℝ) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ‖gammaClockAnnulusProbe a ε‖^2 =
      gammaClockAnnulusMass a ε*gammaClockAnnulusMass a (2*ε)*
        (gammaClockAnnulusMass a (2*ε)-gammaClockAnnulusMass a ε) := by
  have hi : inner ℂ (gammaClockAnnulusProbe a ε) (gammaClockAnnulusProbe a ε) =
      ((gammaClockAnnulusMass a ε*gammaClockAnnulusMass a (2*ε)*
        (gammaClockAnnulusMass a (2*ε)-gammaClockAnnulusMass a ε):ℝ):ℂ) := by
    change inner ℂ (gammaClockAnnulusProbe a ε)
      ((gammaClockAnnulusMass a (2*ε):ℂ) • gammaGroundEndpointShell a ε-
        (gammaClockAnnulusMass a ε:ℂ) • gammaGroundEndpointShell a (2*ε)) = _
    simp only [gammaGroundEndpointShell, inner_sub_right, inner_smul_right]
    rw [inner_gammaClockAnnulusProbe_entry_eq_zero a ha ε 0 hε (Or.inl le_rfl),
      inner_gammaClockAnnulusProbe_entry_eq_zero a ha ε (2*ε) hε (Or.inr le_rfl),
      probe_entry a ha, max_eq_right hε, max_self, max_eq_left (by linarith : ε ≤ 2*ε)]
    unfold gammaClockAnnulusMass
    push_cast
    ring
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),hi]
  rfl

private theorem annulus_polar_integrable (a b R sign : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u => soninLogPolarDensity u •
      rayDilate (Real.exp (sign*u)) (soninCutoffMonomial a 0)) (Icc b R) := by
  have hd : ContinuousOn soninLogPolarDensity (Icc b R) := by
    intro u hu
    have hu0 : u ≠ 0 := (hb.trans_le hu.1).ne'
    apply ContinuousAt.continuousWithinAt
    unfold soninLogPolarDensity
    fun_prop
  exact (hd.smul ((continuous_dilationOrbit (soninCutoffMonomial a 0)).comp
    (continuous_const.mul continuous_id)).continuousOn).integrableOn_Icc

/-- Every literal finite prime-polar source vanishes against the small annulus probe,
without a bound on the prime set or the upper continuum cutoff. -/
theorem inner_gammaClockAnnulusProbe_primePolar_eq_zero (a : ℝ) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 ≤ ε) (P : Finset Nat.Primes) (b R sign : ℝ) (hb : 0 < b)
    (hεb : 2*ε ≤ b) (hεp : 2*ε ≤ Real.log 2) (hsign : sign=1 ∨ sign = -1) :
    inner ℂ (gammaClockAnnulusProbe a ε)
      (soninPrimePolarSourceOperator P b R sign hb (soninCutoffMonomial a 0)) = 0 := by
  have hray (u : ℝ) (hu : 2*ε ≤ u) : inner ℂ (gammaClockAnnulusProbe a ε)
      (rayDilate (Real.exp (sign*u)) (soninCutoffMonomial a 0)) = 0 := by
    rcases hsign with rfl|rfl
    · simpa only [one_mul] using
        inner_gammaClockAnnulusProbe_ray_eq_zero a ha ε u hε (Or.inr hu)
    · simpa only [neg_one_mul] using
        inner_gammaClockAnnulusProbe_ray_eq_zero a ha ε (-u) hε
          (Or.inl (by linarith : -u ≤ 0))
  rw [soninPrimePolarSourceOperator_apply, inner_sub_right, inner_sum,
    ← integral_inner (annulus_polar_integrable a b R sign hb)]
  have hp : (∑ p ∈ P, inner ℂ (gammaClockAnnulusProbe a ε)
      (((Real.sqrt (p:ℝ))⁻¹:ℂ) •
        rayDilate (Real.exp (sign*Real.log (p:ℝ))) (soninCutoffMonomial a 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast p.prop.two_le
    rw [inner_smul_right, hray _ (hεp.trans (Real.log_le_log (by norm_num) hp2)), mul_zero]
  rw [hp]
  have hc : (∫ u in Icc b R, inner ℂ (gammaClockAnnulusProbe a ε)
      (soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) (soninCutoffMonomial a 0))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [inner_smul_right, hray u (hεb.trans hu.1), mul_zero]
    rfl
  rw [hc,sub_self]

private def gammaAnnulusWeight (a ε u : ℝ) : ℝ :=
  2*a*gammaClockAnnulusMass a ε*Real.exp (u/2)*
    (Real.exp (-u)-Real.exp (-max (2*ε) u))

/-- The literal local Gamma work extracted by the physical annulus probe. -/
def gammaClockAnnulusWork (a ε u : ℝ) : ℝ :=
  gammaAnnulusWeight a ε u*(ccmPublishedArchimedeanDensity u/u)

private theorem annulus_gamma_density_continuous {ε R : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun u => ccmPublishedArchimedeanDensity u/u) (Icc ε R) := by
  intro u hu
  have hu0 : 0 < u := hε.trans_le hu.1
  have hden : Real.exp u-Real.exp (-u) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))).ne'
  have hn : ContinuousAt (fun t : ℝ => Real.exp (t/2)) u := by fun_prop
  have hd : ContinuousAt (fun t : ℝ => Real.exp t-Real.exp (-t)) u := by fun_prop
  exact ((hn.div hd hden).div continuousAt_id hu0.ne').continuousWithinAt

private theorem annulus_gamma_integrable (a ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun u => ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
      gammaGroundDifference a u) (Icc ε R) := by
  have hf : Continuous (gammaGroundDifference a) := by
    change Continuous (fun u => gammaGroundDifference a u)
    unfold gammaGroundDifference
    have h := continuous_dilationOrbit (soninCutoffMonomial a 0)
    exact (h.add (h.comp continuous_neg)).sub continuous_const
  exact ((Complex.continuous_ofReal.comp_continuousOn (annulus_gamma_density_continuous hε)).smul
    hf.continuousOn).integrableOn_Icc

private theorem annulus_work_integrable (a ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (gammaClockAnnulusWork a ε) (Icc ε R) := by
  have hw : Continuous (gammaAnnulusWeight a ε) := by
    unfold gammaAnnulusWeight
    fun_prop
  exact (hw.continuousOn.mul (annulus_gamma_density_continuous hε)).integrableOn_Icc

private theorem annulus_gamma_density_pos {u : ℝ} (hu : 0 < u) :
    0 < ccmPublishedArchimedeanDensity u := by
  rw [ccmPublishedArchimedeanDensity]
  exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))

private theorem annulus_work_nonneg (a : ℝ) (ha : 0 ≤ a)
    (ε u : ℝ) (hε : 0 < ε) (hu : ε ≤ u) : 0 ≤ gammaClockAnnulusWork a ε u := by
  have hu0 : 0 < u := hε.trans_le hu
  have hm : 0 ≤ gammaClockAnnulusMass a ε := by
    unfold gammaClockAnnulusMass
    exact mul_nonneg (by positivity)
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
  have he : 0 ≤ Real.exp (-u)-Real.exp (-max (2*ε) u) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _)))
  have hg := annulus_gamma_density_pos hu0
  unfold gammaClockAnnulusWork gammaAnnulusWeight
  positivity

/-- Exact annular Gamma work; its later clocks cancel before any estimate. -/
theorem inner_gammaClockAnnulusProbe_truncated (a : ℝ) (ha : 0 ≤ a)
    (ε R : ℝ) (hε : 0 < ε) :
    inner ℂ (gammaClockAnnulusProbe a ε) (gammaGroundTruncated a ε R) =
      ((-(∫ u in Icc ε R, gammaClockAnnulusWork a ε u):ℝ):ℂ) := by
  rw [gammaGroundTruncated, ← integral_inner (annulus_gamma_integrable a ε R hε),
    ← integral_neg, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [inner_smul_right, inner_gammaClockAnnulusProbe_difference a ha ε u hε.le hu.1]
  unfold gammaClockAnnulusWork gammaAnnulusWeight
  push_cast
  ring

private theorem annulus_mass_nonneg (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε) :
    0 ≤ gammaClockAnnulusMass a ε := by
  unfold gammaClockAnnulusMass
  exact mul_nonneg (by positivity)
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))

private theorem annulus_mass_upper (a ε : ℝ) (ha : 0 ≤ a) :
    gammaClockAnnulusMass a ε ≤ 2*a*ε := by
  have h := Real.add_one_le_exp (-ε)
  unfold gammaClockAnnulusMass
  nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ 2*a by positivity)]

private theorem annulus_exp_loss_lower {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    t/2 ≤ 1-Real.exp (-t) := by
  have hinv : Real.exp (-t) ≤ (1+t)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos t) (by positivity)).mpr (by linarith [Real.add_one_le_exp t])
  have hid : (1+t)⁻¹*(1+t)=1 := inv_mul_cancel₀ (by positivity)
  have h : (1-Real.exp (-t))*(1+t) ≥ t := by nlinarith
  have hn : 0 ≤ 1-Real.exp (-t) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  nlinarith

private theorem annulus_mass_lower (a : ℝ) (ha : 0 ≤ a) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) : a*ε ≤ gammaClockAnnulusMass a ε := by
  have h := mul_le_mul_of_nonneg_left (annulus_exp_loss_lower hε hε1)
    (show 0 ≤ 2*a by positivity)
  unfold gammaClockAnnulusMass
  nlinarith

private theorem annulus_weight_local_lower (a : ℝ) (ha : 0 ≤ a)
    {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hu : u ∈ Icc ε (3*ε/2)) :
    a^2*ε^2/4 ≤ gammaAnnulusWeight a ε u := by
  have hu0 : 0 < u := hε.trans_le hu.1
  have hm := annulus_mass_lower a ha hε (by linarith)
  have ht : 0 < 2*ε-u := by linarith [hu.2]
  have ht1 : 2*ε-u ≤ 1 := by linarith [hu.1]
  have hcut := annulus_exp_loss_lower ht ht1
  have he : 1/2 ≤ Real.exp (-u/2) := by
    linarith [Real.add_one_le_exp (-u/2),hu.2]
  have hl : ε/4 ≤ 1-Real.exp (-(2*ε-u)) := by linarith [hu.2]
  have hid : Real.exp (u/2)*(Real.exp (-u)-Real.exp (-(2*ε))) =
      Real.exp (-u/2)*(1-Real.exp (-(2*ε-u))) := by
    rw [mul_sub,mul_sub,mul_one,← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have hd : ε/8 ≤ Real.exp (u/2)*(Real.exp (-u)-Real.exp (-(2*ε))) := by
    rw [hid]
    calc
      _ = (1/2)*(ε/4) := by ring
      _ ≤ _ := mul_le_mul he hl (by positivity) (Real.exp_pos _).le
  have hw : gammaAnnulusWeight a ε u = (2*a*gammaClockAnnulusMass a ε)*
      (Real.exp (u/2)*(Real.exp (-u)-Real.exp (-(2*ε)))) := by
    unfold gammaAnnulusWeight
    rw [max_eq_left (by linarith [hu.2] : u ≤ 2*ε)]
    ring
  rw [hw]
  calc
    _ = (2*a*(a*ε))*(ε/8) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hd
      (by positivity) (mul_nonneg (by positivity) (annulus_mass_nonneg a ε ha hε.le))

private theorem annulus_gamma_density_lower {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    1/(4*u) ≤ ccmPublishedArchimedeanDensity u := by
  rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu]
  have hd : 0 < 1-Real.exp (-2*u) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  apply (div_le_div_iff₀ (by positivity) hd).mpr
  have hn : 1/2 ≤ Real.exp (-u/2) := by linarith [Real.add_one_le_exp (-u/2)]
  have hden : 1-Real.exp (-2*u) ≤ 2*u := by linarith [Real.add_one_le_exp (-2*u)]
  nlinarith

private theorem annulus_work_local_lower (a : ℝ) (ha : 0 ≤ a)
    {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hu : u ∈ Icc ε (3*ε/2)) :
    a^2/36 ≤ gammaClockAnnulusWork a ε u := by
  have hu0 : 0 < u := hε.trans_le hu.1
  have hγ := annulus_gamma_density_lower hu0 (by linarith [hu.2])
  have hg : 1/(9*ε^2) ≤ ccmPublishedArchimedeanDensity u/u := by
    calc
      _ ≤ 1/(4*u^2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [pow_le_pow_left₀ hu0.le hu.2 2]
      _ = (1/(4*u))/u := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hγ hu0.le
  have hw := annulus_weight_local_lower a ha hε hε1 hu
  calc
    _ = (a^2*ε^2/4)*(1/(9*ε^2)) := by
      field_simp
      ring
    _ ≤ gammaClockAnnulusWork a ε u :=
      mul_le_mul hw hg (by positivity) (le_trans (by positivity) hw)

private theorem annulus_work_integral_lower (a : ℝ) (ha : 0 ≤ a)
    {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hR : 2*ε ≤ R) :
    a^2*ε/72 ≤ ∫ u in Icc ε R, gammaClockAnnulusWork a ε u := by
  have hs : Icc ε (3*ε/2) ⊆ Icc ε R := fun u hu => ⟨hu.1,by linarith [hu.2]⟩
  calc
    _ = ∫ _u in Icc ε (3*ε/2), (a^2/36:ℝ) := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      ring
    _ ≤ ∫ u in Icc ε (3*ε/2), gammaClockAnnulusWork a ε u :=
      setIntegral_mono_on continuous_const.integrableOn_Icc
        (annulus_work_integrable a ε (3*ε/2) hε) measurableSet_Icc
        (fun u hu => annulus_work_local_lower a ha hε hε1 hu)
    _ ≤ _ := setIntegral_mono_set (annulus_work_integrable a ε R hε)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
          exact annulus_work_nonneg a ha ε u hε hu.1) (Eventually.of_forall hs)

private theorem annulus_probe_norm_upper (a : ℝ) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 ≤ ε) : ‖gammaClockAnnulusProbe a ε‖^2 ≤ 32*a^3*ε^3 := by
  have hm1 := annulus_mass_nonneg a ε ha hε
  have hm2 := annulus_mass_nonneg a (2*ε) ha (by positivity)
  have h1 := annulus_mass_upper a ε ha
  have h2 : gammaClockAnnulusMass a (2*ε) ≤ 4*a*ε := by
    nlinarith [annulus_mass_upper a (2*ε) ha]
  rw [gammaClockAnnulusProbe_norm_sq a ha ε hε]
  calc
    _ ≤ gammaClockAnnulusMass a ε*gammaClockAnnulusMass a (2*ε)*gammaClockAnnulusMass a (2*ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hm1 hm2)
    _ ≤ (2*a*ε)*(4*a*ε)*(4*a*ε) := by gcongr
    _ = _ := by ring

private theorem annulus_joint_energy_lower (a : ℝ) (ha : 0 < a)
    (ε R : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hR : 2*ε ≤ R)
    (W : SoninL2) (hW : inner ℂ (gammaClockAnnulusProbe a ε) W = 0) :
    a/(32*72^2) ≤ ε*‖gammaGroundTruncated a ε R+W‖^2 := by
  let J := ∫ u in Icc ε R, gammaClockAnnulusWork a ε u
  let L := gammaGroundTruncated a ε R+W
  have hJ : a^2*ε/72 ≤ J := annulus_work_integral_lower a ha.le hε hε1 hR
  have hJ0 : 0 ≤ J := le_trans (by positivity) hJ
  have hp : inner ℂ (gammaClockAnnulusProbe a ε) L = ((-J:ℝ):ℂ) := by
    dsimp [L,J]
    rw [inner_add_right,hW,add_zero,inner_gammaClockAnnulusProbe_truncated a ha.le ε R hε]
  have hn := norm_inner_le_norm (𝕜 := ℂ) (gammaClockAnnulusProbe a ε) L
  rw [hp,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_nonneg hJ0] at hn
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a^2*ε/72) (hJ.trans hn) 2
  rw [mul_pow ‖gammaClockAnnulusProbe a ε‖ ‖L‖] at hs
  have hb := mul_le_mul_of_nonneg_right (annulus_probe_norm_upper a ha.le ε hε.le)
    (sq_nonneg ‖L‖)
  have ht := hs.trans hb
  rw [div_pow] at ht
  have ht' := (div_le_iff₀ (by norm_num : (0:ℝ)<72^2)).mp ht
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<32*72^2)).mpr
  apply le_of_mul_le_mul_left ?_ (show 0 < a^3*ε^2 by positivity)
  change (a^3*ε^2)*a ≤ (a^3*ε^2)*(ε*‖L‖^2*(32*72^2))
  nlinarith only [ht']

/-- The actual symmetric prime-polar source cannot cancel the Gamma lower endpoint,
regardless of its prime set or either continuum upper endpoint. -/
theorem gammaPrimePolar_joint_energy_lower (a : ℝ) (ha : 0 < a)
    (ε R : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hR : 2*ε ≤ R)
    (P : Finset Nat.Primes) (b X Y : ℝ) (hb : 0 < b)
    (hεb : 2*ε ≤ b) (hεp : 2*ε ≤ Real.log 2) :
    a/(32*72^2) ≤ ε*‖gammaGroundTruncated a ε R+
      soninPrimePolarSourceOperator P b X 1 hb (soninCutoffMonomial a 0)+
      soninPrimePolarSourceOperator P b Y (-1) hb (soninCutoffMonomial a 0)‖^2 := by
  rw [add_assoc]
  apply annulus_joint_energy_lower a ha ε R hε hε1 hR
  rw [inner_add_right,
    inner_gammaClockAnnulusProbe_primePolar_eq_zero a ha.le ε hε.le P b X 1 hb hεb hεp (Or.inl rfl),
    inner_gammaClockAnnulusProbe_primePolar_eq_zero a ha.le ε hε.le P b Y (-1) hb hεb hεp (Or.inr rfl),
    add_zero]

/-- Joint norm escape under every cofinal Gamma cutoff and arbitrary native prime-polar cutoffs. -/
theorem gammaPrimePolar_joint_norm_tendsto_atTop (a : ℝ) (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (P : ℝ → Finset Nat.Primes) (X Y U : ℝ → ℝ)
    (hU : Tendsto U (𝓝[>] (0:ℝ)) atTop) :
    Tendsto (fun ε => ‖gammaGroundTruncated a ε (U ε)+
      soninPrimePolarSourceOperator (P ε) b (X ε) 1 hb (soninCutoffMonomial a 0)+
      soninPrimePolarSourceOperator (P ε) b (Y ε) (-1) hb (soninCutoffMonomial a 0)‖)
      (𝓝[>] (0:ℝ)) atTop := by
  let δ := min (1/2:ℝ) (min (b/2) (Real.log 2/2))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  rw [tendsto_atTop]
  intro B
  have hsmall : Ioo (0:ℝ) (min δ (a/((32*72^2)*(B^2+1)))) ∈ 𝓝[>] (0:ℝ) :=
    (nhdsGT_basis (0:ℝ)).mem_of_mem (by positivity)
  filter_upwards [hsmall,hU.eventually (eventually_ge_atTop 1)] with ε hεmem hUε
  have hε : 0 < ε := hεmem.1
  have heδ : ε < δ := (lt_min_iff.mp hεmem.2).1
  have heb : ε < a/((32*72^2)*(B^2+1)) := (lt_min_iff.mp hεmem.2).2
  have hε1 : ε ≤ 1/2 := heδ.le.trans (min_le_left _ _)
  have hεb : 2*ε ≤ b := by
    have h := heδ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hεp : 2*ε ≤ Real.log 2 := by
    have h := heδ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hR : 2*ε ≤ U ε := by linarith
  have henergy := gammaPrimePolar_joint_energy_lower a ha ε (U ε) hε hε1 hR
    (P ε) b (X ε) (Y ε) hb hεb hεp
  by_contra hnot
  have hn := lt_of_not_ge hnot
  have hs : ‖gammaGroundTruncated a ε (U ε)+
      soninPrimePolarSourceOperator (P ε) b (X ε) 1 hb (soninCutoffMonomial a 0)+
      soninPrimePolarSourceOperator (P ε) b (Y ε) (-1) hb (soninCutoffMonomial a 0)‖^2 ≤ B^2 := by
    nlinarith [norm_nonneg (gammaGroundTruncated a ε (U ε)+
      soninPrimePolarSourceOperator (P ε) b (X ε) 1 hb (soninCutoffMonomial a 0)+
      soninPrimePolarSourceOperator (P ε) b (Y ε) (-1) hb (soninCutoffMonomial a 0))]
  have hm := mul_le_mul_of_nonneg_left hs hε.le
  have heclear := (div_le_iff₀ (by norm_num : (0:ℝ)<32*72^2)).mp (henergy.trans hm)
  have hbclear := (lt_div_iff₀ (by positivity : (0:ℝ)<(32*72^2)*(B^2+1))).mp heb
  nlinarith only [heclear,hbclear,hε]

end RHTower
