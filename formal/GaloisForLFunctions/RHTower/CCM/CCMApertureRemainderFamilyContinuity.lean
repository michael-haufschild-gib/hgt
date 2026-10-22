import GaloisForLFunctions.RHTower.CCM.CCMApertureRemainderFamily
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEnergyContinuity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRayleighInfimum

/-!
# Continuity of the ground energy of an aperture family, and zero crossings

For any aperture-compatible family of bounded self-adjoint remainders (`CCMRemainderFamily`), the
ground energy is a continuous antitone function of the aperture.  Right continuity comes from the
compactness of the form embedding: normalized ground states of slightly larger apertures have a
strong limit supported in the closed limiting aperture, and sublevel sets of the form are closed.
Left continuity comes from the smooth interior core: one compactly supported smooth source
realises a Rayleigh value close to the ground energy on a whole neighbourhood of smaller apertures.

Consequently a family whose ground energy is positive at one aperture and negative at a larger one
has an aperture at which the ground energy vanishes, and there the Friedrichs operator of the
family has a nonzero kernel element.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CCMRemainderFamily

variable (F : CCMRemainderFamily)

/-! ## Ground eigenstates -/

theorem exists_groundEigenstate (a : SuzukiPositiveAperture) :
    ∃ x : (F.operator a).domain, (x : suzukiApertureHilbert a) ≠ 0 ∧
      F.operator a x = (F.energy a : ℂ) • (x : suzukiApertureHilbert a) := by
  set J := ccmArchimedeanFormToAperture a with hJ
  set B := F.B a with hB
  have hBsa := F.selfAdjoint a
  have hJinj := ccmArchimedeanFormToAperture_injective a
  have hDense := denseRange_ccmArchimedeanFormToAperture a
  set C := boundedPerturbedFormCovariance J B hBsa with hC
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B hBsa hJinj hDense
  obtain ⟨e, hene, he⟩ := boundedPerturbedFormCovariance_exists_norm_eigenvector J B hBsa hJinj
    hDense (isCompactOperator_ccmArchimedeanFormToAperture a)
  set mu : ℝ := ‖C‖ with hmu_def
  change C e = (mu : ℂ) • e at he
  have hmu0 : mu ≠ 0 := by
    intro h0
    apply hene
    apply hCinj
    rw [he, h0, map_zero]
    simp
  have hmuC : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu0
  set z : suzukiApertureHilbert a := (mu : ℂ)⁻¹ • e with hz
  have hCz : C z = e := by
    rw [hz, map_smul, he, smul_smul, inv_mul_cancel₀ hmuC, one_smul]
  have hedom : e ∈ (closedDenseInverse C).domain := by
    rw [closedDenseInverse_domain]
    exact ⟨z, hCz⟩
  have hinv : closedDenseInverse C ⟨e, hedom⟩ = z := by
    have h := (closedDenseInverse_apply_C C hCinj z).2
    have heq : (⟨e, hedom⟩ : (closedDenseInverse C).domain) =
        ⟨C z, (closedDenseInverse_apply_C C hCinj z).1⟩ := Subtype.ext hCz.symm
    rw [heq]
    exact h
  let x : (F.operator a).domain := ⟨e, by
    change e ∈ (closedDenseInverse C).domain
    exact hedom⟩
  refine ⟨x, hene, ?_⟩
  change boundedPerturbedFriedrichsOperator J B hBsa x = _
  rw [boundedPerturbedFriedrichsOperator_apply]
  have hsub : closedDenseInverse C ⟨(x : suzukiApertureHilbert a), x.property⟩ = z := by
    have heq : (⟨(x : suzukiApertureHilbert a), x.property⟩ :
        (closedDenseInverse C).domain) = ⟨e, hedom⟩ := Subtype.ext rfl
    rw [heq, hinv]
  rw [hsub]
  change (mu : ℂ)⁻¹ • e - (boundedPerturbedFormShift B : ℂ) • e = (F.energy a : ℂ) • e
  unfold energy
  rw [← hC, ← hmu_def]
  push_cast
  module

/-! ## Normalized ground states and right extensions -/

def groundFormVector (a : SuzukiPositiveAperture) : CCMArchimedeanFormDomain a :=
  Classical.choose (F.exists_groundFormState a)

theorem groundFormVector_embedding_ne_zero (a : SuzukiPositiveAperture) :
    ccmArchimedeanFormToAperture a (F.groundFormVector a) ≠ 0 :=
  (Classical.choose_spec (F.exists_groundFormState a)).1

theorem groundFormVector_Q (a : SuzukiPositiveAperture) :
    F.Q a (F.groundFormVector a) =
      F.energy a * ‖ccmArchimedeanFormToAperture a (F.groundFormVector a)‖ ^ 2 :=
  (Classical.choose_spec (F.exists_groundFormState a)).2

def normalizedGround (a : SuzukiPositiveAperture) : CCMArchimedeanFormDomain a :=
  ((‖ccmArchimedeanFormToAperture a (F.groundFormVector a)‖ : ℂ)⁻¹) • F.groundFormVector a

theorem norm_normalizedGround_embedding (a : SuzukiPositiveAperture) :
    ‖ccmArchimedeanFormToAperture a (F.normalizedGround a)‖ = 1 := by
  have hr : 0 < ‖ccmArchimedeanFormToAperture a (F.groundFormVector a)‖ :=
    norm_pos_iff.mpr (F.groundFormVector_embedding_ne_zero a)
  rw [normalizedGround, map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  exact inv_mul_cancel₀ hr.ne'

theorem normalizedGround_Q (a : SuzukiPositiveAperture) :
    F.Q a (F.normalizedGround a) = F.energy a := by
  have hr : 0 < ‖ccmArchimedeanFormToAperture a (F.groundFormVector a)‖ :=
    norm_pos_iff.mpr (F.groundFormVector_embedding_ne_zero a)
  rw [normalizedGround, Q_smul, groundFormVector_Q, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  field_simp

theorem rightAperture_le_zero (a : SuzukiPositiveAperture) (n : ℕ) :
    (suzukiRightAperture a n).1 ≤ (suzukiRightAperture a 0).1 :=
  Subtype.coe_le_coe.mpr (antitone_suzukiRightAperture a (Nat.zero_le n))

def rightExt (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMArchimedeanFormDomain (suzukiRightAperture a 0) :=
  Classical.choose (exists_ccmArchimedeanFormDomain_extension (rightAperture_le_zero a n)
    (F.normalizedGround (suzukiRightAperture a n)))

theorem rightExt_val (a : SuzukiPositiveAperture) (n : ℕ) :
    (F.rightExt a n).1 = (F.normalizedGround (suzukiRightAperture a n)).1 :=
  Classical.choose_spec (exists_ccmArchimedeanFormDomain_extension (rightAperture_le_zero a n)
    (F.normalizedGround (suzukiRightAperture a n)))

theorem norm_rightExt_embedding (a : SuzukiPositiveAperture) (n : ℕ) :
    ‖ccmArchimedeanFormToAperture (suzukiRightAperture a 0) (F.rightExt a n)‖ = 1 := by
  rw [norm_ccmArchimedeanFormToAperture_eq_of_val_eq (F.rightExt_val a n)]
  exact F.norm_normalizedGround_embedding _

theorem rightExt_Q (a : SuzukiPositiveAperture) (n : ℕ) :
    F.Q (suzukiRightAperture a 0) (F.rightExt a n) = F.energy (suzukiRightAperture a n) := by
  rw [F.Q_eq_of_val_eq (rightAperture_le_zero a n) (F.rightExt_val a n)]
  exact F.normalizedGround_Q _

theorem norm_rightExt_le (a : SuzukiPositiveAperture) (n : ℕ) :
    ‖F.rightExt a n‖ ≤
      Real.sqrt (max 0 (F.energy a + ‖F.B (suzukiRightAperture a 0)‖)) := by
  have hbound := F.norm_sq_le_Q_add (suzukiRightAperture a 0) (F.rightExt a n)
  rw [rightExt_Q, norm_rightExt_embedding] at hbound
  simp only [one_pow, mul_one] at hbound
  have hmono : F.energy (suzukiRightAperture a n) ≤ F.energy a :=
    F.energy_antitone (suzukiRightAperture_gt a n).le
  have hsq : ‖F.rightExt a n‖ ^ 2 ≤ max 0 (F.energy a + ‖F.B (suzukiRightAperture a 0)‖) :=
    hbound.trans (le_max_of_le_right (by linarith))
  have hnonneg : 0 ≤ max 0 (F.energy a + ‖F.B (suzukiRightAperture a 0)‖) := le_max_left _ _
  nlinarith [Real.sq_sqrt hnonneg, norm_nonneg (F.rightExt a n), Real.sqrt_nonneg
    (max 0 (F.energy a + ‖F.B (suzukiRightAperture a 0)‖))]

/-- Compactness extracts a normalized physical limit from the right-ground family, supported in
the limiting closed aperture. -/
theorem exists_rightGroundCompactLimit (a : SuzukiPositiveAperture) :
    ∃ fstar : suzukiApertureHilbert (suzukiRightAperture a 0), ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      Tendsto (fun n => ccmArchimedeanFormToAperture (suzukiRightAperture a 0)
        (F.rightExt a (phi n))) atTop (nhds fstar) ∧
      indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (fstar : SoninL2) = (fstar : SoninL2) ∧
      ‖fstar‖ = 1 := by
  set b := suzukiRightAperture a 0 with hb
  set J := ccmArchimedeanFormToAperture b with hJ
  set radius := Real.sqrt (max 0 (F.energy a + ‖F.B b‖)) with hradius
  have hmem : ∀ n : ℕ, J (F.rightExt a n) ∈
      closure (J '' Metric.closedBall (0 : CCMArchimedeanFormDomain b) radius) := by
    intro n
    apply subset_closure
    refine ⟨F.rightExt a n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact F.norm_rightExt_le a n
  obtain ⟨fstar, -, phi, hphi, hconv⟩ :=
    (isCompactOperator_ccmArchimedeanFormToAperture b
      |>.isCompact_closure_image_closedBall radius).tendsto_subseq hmem
  refine ⟨fstar, phi, hphi, hconv, ?_, ?_⟩
  · have hconvGlobal : Tendsto (fun n => (J (F.rightExt a (phi n)) : SoninL2)) atTop
        (nhds (fstar : SoninL2)) :=
      (continuous_subtype_val.tendsto fstar).comp hconv
    apply indicatorCutoff_limit_suzukiRightAperture a phi hphi.tendsto_atTop _ _ _ hconvGlobal
    intro n
    have hcoe := ccmArchimedeanFormToAperture_coe_eq_of_val_eq (F.rightExt_val a (phi n))
    rw [hcoe]
    exact indicatorCutoff_suzukiApertureHilbert (suzukiRightAperture a (phi n))
      (ccmArchimedeanFormToAperture (suzukiRightAperture a (phi n))
        (F.normalizedGround (suzukiRightAperture a (phi n))))
  · have hnormLim : Tendsto (fun n => ‖J (F.rightExt a (phi n))‖) atTop (nhds ‖fstar‖) :=
      (continuous_norm.tendsto fstar).comp hconv
    have hnormOne : Tendsto (fun n => ‖J (F.rightExt a (phi n))‖) atTop (nhds 1) := by
      have hnormEq : ∀ n : ℕ, ‖J (F.rightExt a (phi n))‖ = 1 := fun n =>
        F.norm_rightExt_embedding a (phi n)
      simpa only [hnormEq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    exact tendsto_nhds_unique hnormLim hnormOne

/-! ## Right continuity -/

theorem tendsto_energy_rightAperture (a : SuzukiPositiveAperture) :
    Tendsto (fun n => F.energy (suzukiRightAperture a n)) atTop (nhds (F.energy a)) := by
  have henergyMono : Monotone (fun n => F.energy (suzukiRightAperture a n)) := by
    intro m n hmn
    exact F.energy_antitone (antitone_suzukiRightAperture a hmn)
  refine Metric.tendsto_atTop.2 fun epsilon hepsilon => ?_
  have hexists : ∃ k : ℕ, F.energy a - epsilon < F.energy (suzukiRightAperture a k) := by
    by_contra hnone
    have hnone' : ∀ k, F.energy (suzukiRightAperture a k) ≤ F.energy a - epsilon := fun k =>
      le_of_not_gt fun h => hnone ⟨k, h⟩
    set b := suzukiRightAperture a 0 with hb
    obtain ⟨fstar, phi, hphi, hconv, hsupport, hnorm⟩ := F.exists_rightGroundCompactLimit a
    have hmem : ∀ n : ℕ, ccmArchimedeanFormToAperture b (F.rightExt a (phi n)) ∈
        {f : suzukiApertureHilbert b | ∃ u : CCMArchimedeanFormDomain b,
          ccmArchimedeanFormToAperture b u = f ∧ F.Q b u ≤ F.energy a - epsilon} := by
      intro n
      refine ⟨F.rightExt a (phi n), rfl, ?_⟩
      rw [F.rightExt_Q]
      exact hnone' (phi n)
    obtain ⟨w, hwJ, hwQ⟩ := (F.isClosed_sublevel b (F.energy a - epsilon)).mem_of_tendsto hconv
      (Eventually.of_forall hmem)
    obtain ⟨u, huw, huJ⟩ := exists_ccmArchimedeanFormDomain_of_limit_support a b w fstar hwJ hsupport
    have hab : a.1 ≤ b.1 := (suzukiRightAperture_gt a 0).le
    have hnormu : ‖ccmArchimedeanFormToAperture a u‖ = 1 := by
      have hnormeq := norm_ccmArchimedeanFormToAperture_eq_of_val_eq huw.symm
      rw [hwJ, hnorm] at hnormeq
      exact hnormeq.symm
    have hQ : F.Q a u = F.Q b w := (F.Q_eq_of_val_eq hab huw.symm).symm
    have hfloor := F.energy_mul_formNorm_sq_le a u
    rw [hnormu, one_pow, mul_one, hQ] at hfloor
    linarith
  obtain ⟨k, hk⟩ := hexists
  refine ⟨k, fun n hkn => ?_⟩
  have hlower := lt_of_lt_of_le hk (henergyMono hkn)
  have hupper : F.energy (suzukiRightAperture a n) ≤ F.energy a :=
    F.energy_antitone (suzukiRightAperture_gt a n).le
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-! ## The smooth interior Rayleigh infimum and left continuity -/

def rayleigh (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  F.Q a u / ‖ccmArchimedeanFormToAperture a u‖ ^ 2

theorem continuousAt_rayleigh (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hu : ccmArchimedeanFormToAperture a u ≠ 0) : ContinuousAt (F.rayleigh a) u := by
  unfold rayleigh
  refine (F.continuous_Q a).continuousAt.div
    ((continuous_norm.pow 2).comp (ccmArchimedeanFormToAperture a).continuous).continuousAt ?_
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)

def smoothRayleighSet (a : SuzukiPositiveAperture) : Set ℝ :=
  {r | ∃ u : CCMComplexSmoothInteriorSource a,
    ccmArchimedeanFormToAperture a u.toCCMFormVector ≠ 0 ∧ r = F.rayleigh a u.toCCMFormVector}

theorem isGLB_smoothRayleighSet (a : SuzukiPositiveAperture) :
    IsGLB (F.smoothRayleighSet a) (F.energy a) := by
  constructor
  · rintro r ⟨v, hvJ, rfl⟩
    have hmass : 0 < ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr hvJ) 2
    rw [rayleigh, le_div_iff₀ hmass]
    exact F.energy_mul_formNorm_sq_le a v.toCCMFormVector
  · intro b hb
    obtain ⟨u, hJu, hground⟩ := F.exists_groundFormState a
    have hmass : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hJu)
    have hrayleigh : F.rayleigh a u = F.energy a := by
      rw [rayleigh, hground]
      exact mul_div_cancel_right₀ _ hmass
    have hcont : ContinuousAt (F.rayleigh a) u := F.continuousAt_rayleigh a u hJu
    have hu : u ≠ 0 := by
      intro hu0
      rw [hu0, map_zero] at hJu
      exact hJu rfl
    refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
    have hrayNhds : {v | F.rayleigh a v < F.energy a + epsilon} ∈ 𝓝 u := by
      have hIio : Iio (F.energy a + epsilon) ∈ 𝓝 (F.rayleigh a u) := by
        rw [hrayleigh]
        exact Iio_mem_nhds (lt_add_of_pos_right _ hepsilon)
      exact hcont hIio
    have hneNhds : ({0}ᶜ : Set (CCMArchimedeanFormDomain a)) ∈ 𝓝 u :=
      isOpen_compl_singleton.mem_nhds hu
    obtain ⟨v, hvRay, hvne⟩ :=
      (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).mem_nhds
        (inter_mem hrayNhds hneNhds)
    have hvJ : ccmArchimedeanFormToAperture a v.toCCMFormVector ≠ 0 := by
      intro hvzero
      apply hvne
      apply ccmArchimedeanFormToAperture_injective a
      simpa using hvzero
    change F.rayleigh a v.toCCMFormVector < F.energy a + epsilon at hvRay
    exact (lt_of_le_of_lt (hb ⟨v, hvJ, rfl⟩) hvRay).le

theorem exists_smoothRayleigh_lt_energy_add (a : SuzukiPositiveAperture) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ u : CCMComplexSmoothInteriorSource a,
      ccmArchimedeanFormToAperture a u.toCCMFormVector ≠ 0 ∧
        F.rayleigh a u.toCCMFormVector < F.energy a + epsilon := by
  have hGLB := F.isGLB_smoothRayleighSet a
  have hexists : ∃ r ∈ F.smoothRayleighSet a, r < F.energy a + epsilon := by
    by_contra hnone
    have hlower : F.energy a + epsilon ∈ lowerBounds (F.smoothRayleighSet a) := by
      intro r hr
      exact le_of_not_gt fun hlt => hnone ⟨r, hr, hlt⟩
    have hle := hGLB.2 hlower
    linarith
  obtain ⟨r, ⟨u, huJ, rfl⟩, huray⟩ := hexists
  exact ⟨u, huJ, huray⟩

theorem exists_left_aperture_uniform_energy_upper (a : SuzukiPositiveAperture) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ b : SuzukiPositiveAperture, b.1 < a.1 ∧
      ∀ c : SuzukiPositiveAperture, b.1 ≤ c.1 → c.1 ≤ a.1 →
        F.energy c < F.energy a + epsilon := by
  obtain ⟨u, huJ, huRayleigh⟩ := F.exists_smoothRayleigh_lt_energy_add a hepsilon
  obtain ⟨b, hba, hsupport⟩ := exists_strict_smaller_aperture_of_compact_tsupport a u
  refine ⟨b, hba, fun c hbc hca => ?_⟩
  have hsupportC : tsupport (u : ℝ → ℂ) ⊆ Ioo (-c.1) c.1 := by
    intro x hx
    have hxb := hsupport hx
    rw [mem_Ioo] at hxb ⊢
    constructor <;> linarith
  let uc := u.restrictAperture c hsupportC
  have hval : uc.toCCMFormVector.1 = u.toCCMFormVector.1 :=
    u.restrictAperture_toCCMFormVector_val c hsupportC
  have hnorm : ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture c uc.toCCMFormVector‖ :=
    (norm_ccmArchimedeanFormToAperture_eq_of_val_eq hval).symm
  have hQ : F.Q a u.toCCMFormVector = F.Q c uc.toCCMFormVector :=
    F.Q_eq_of_val_eq hca hval.symm
  have hRayleigh : F.rayleigh c uc.toCCMFormVector = F.rayleigh a u.toCCMFormVector := by
    unfold rayleigh
    rw [hQ, hnorm]
  have hucJ : ccmArchimedeanFormToAperture c uc.toCCMFormVector ≠ 0 := by
    intro hzero
    apply huJ
    rw [← norm_eq_zero, hnorm, hzero, norm_zero]
  have hfloor := (F.isGLB_smoothRayleighSet c).1 ⟨uc, hucJ, rfl⟩
  rw [hRayleigh] at hfloor
  exact lt_of_le_of_lt hfloor huRayleigh

/-! ## Continuity -/

theorem continuousAt_energy (a : SuzukiPositiveAperture) : ContinuousAt F.energy a := by
  refine Metric.continuousAt_iff.2 fun epsilon hepsilon => ?_
  obtain ⟨b, hba, hleft⟩ := F.exists_left_aperture_uniform_energy_upper a hepsilon
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (F.tendsto_energy_rightAperture a) epsilon hepsilon
  let r := suzukiRightAperture a N
  have har : a.1 < r.1 := suzukiRightAperture_gt a N
  let delta := min (a.1 - b.1) (r.1 - a.1)
  have hdelta : 0 < delta := lt_min (sub_pos.mpr hba) (sub_pos.mpr har)
  refine ⟨delta, hdelta, fun c hc => ?_⟩
  change dist c.1 a.1 < delta at hc
  rw [Real.dist_eq] at hc
  have hcLeft : b.1 < c.1 := by
    have hdist : |c.1 - a.1| < a.1 - b.1 := lt_of_lt_of_le hc (min_le_left _ _)
    linarith [neg_le_abs (c.1 - a.1)]
  have hcRight : c.1 < r.1 := by
    have hdist : |c.1 - a.1| < r.1 - a.1 := lt_of_lt_of_le hc (min_le_right _ _)
    linarith [le_abs_self (c.1 - a.1)]
  by_cases hca : c.1 ≤ a.1
  · have hlower : F.energy a ≤ F.energy c := F.energy_antitone hca
    have hupper := hleft c hcLeft.le hca
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith
  · have hac : a.1 ≤ c.1 := le_of_not_ge hca
    have hlower : F.energy r ≤ F.energy c := F.energy_antitone hcRight.le
    have hupper : F.energy c ≤ F.energy a := F.energy_antitone hac
    have hrclose := hN N le_rfl
    change dist (F.energy r) (F.energy a) < epsilon at hrclose
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (F.energy_antitone har.le))] at hrclose
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
    linarith

theorem continuous_energy : Continuous F.energy :=
  continuous_iff_continuousAt.2 F.continuousAt_energy

/-! ## Zero crossings -/

/-- A family whose ground energy is positive at one aperture and negative at a larger one has an
aperture in between at which the ground energy vanishes. -/
theorem exists_energy_eq_zero {a₀ a₁ : SuzukiPositiveAperture} (h01 : a₀.1 ≤ a₁.1)
    (h0 : 0 < F.energy a₀) (h1 : F.energy a₁ < 0) :
    ∃ a : SuzukiPositiveAperture, a₀.1 ≤ a.1 ∧ a.1 ≤ a₁.1 ∧ F.energy a = 0 := by
  let lift : ℝ → SuzukiPositiveAperture := fun t =>
    ⟨max t a₀.1, lt_of_lt_of_le a₀.2 (le_max_right _ _)⟩
  have hlift : Continuous lift :=
    (continuous_id.max continuous_const).subtype_mk _
  let g : ℝ → ℝ := fun t => F.energy (lift t)
  have hg : Continuous g := F.continuous_energy.comp hlift
  have hga : g a₀.1 = F.energy a₀ := by
    show F.energy ⟨max a₀.1 a₀.1, _⟩ = F.energy a₀
    congr 1
    exact Subtype.ext (max_self _)
  have hgb : g a₁.1 = F.energy a₁ := by
    show F.energy ⟨max a₁.1 a₀.1, _⟩ = F.energy a₁
    congr 1
    exact Subtype.ext (max_eq_left h01)
  have hmem : (0 : ℝ) ∈ Icc (g a₁.1) (g a₀.1) := by
    rw [hga, hgb]
    exact ⟨h1.le, h0.le⟩
  obtain ⟨t, ⟨hta, htb⟩, hgt⟩ := intermediate_value_Icc' h01 hg.continuousOn hmem
  refine ⟨lift t, ?_, ?_, hgt⟩
  · exact le_max_right _ _
  · show max t a₀.1 ≤ a₁.1
    exact max_le htb h01

/-- At an aperture where the ground energy vanishes, the Friedrichs operator of the family has a
nonzero kernel element. -/
theorem exists_kernel_of_energy_eq_zero {a : SuzukiPositiveAperture} (h : F.energy a = 0) :
    ∃ x : (F.operator a).domain, (x : suzukiApertureHilbert a) ≠ 0 ∧ F.operator a x = 0 := by
  obtain ⟨x, hxne, hx⟩ := F.exists_groundEigenstate a
  refine ⟨x, hxne, ?_⟩
  rw [hx, h]
  simp

end RHTower.CCMRemainderFamily

end
