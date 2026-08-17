import GaloisForLFunctions.RHTower.CCMRestrictedWeilCanonicalGroundHeadConvergence

/-!
# Energy convergence and reverse-prime criterion on canonical Γ--Slepian heads

For the literal canonical finite heads converging to the exact restricted-Weil ground, this module
proves an exact shifted-defect identity: head defect equals omitted-tail defect. Consequently every
shifted head defect is nonnegative and obeys an explicit source-aligned rate. The unshifted head
energies converge to the true ground energy times physical ground mass.

The final theorem identifies the RH-bearing arithmetic datum without replacing either operator:
at each fixed aperture, nonnegativity of the true restricted-Weil floor is equivalent to eventual
reverse-prime control on the actual canonical Γ--Slepian heads.

The normalized head margin has an exact limit.  In particular, at a zero-energy first contact it
converges to zero, so no fixed positive coercivity constant can hold cofinally on these heads.  Any
lawful Route O estimate must retain the vanishing head error rather than replace it by a uniform
positive gap.

All statements are unconditional. The module does not prove that reverse-prime control holds, does
not prove RH, and does not identify common-clock heads with Γ--Slepian heads.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

namespace RHTower

theorem ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger
    (a : SuzukiPositiveAperture) (E : ℝ)
    (x y : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a x y -
        inner ℂ ((E : ℂ) • ccmArchimedeanFormToAperture a x)
          (ccmArchimedeanFormToAperture a y) =
      inner ℂ
        ((ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) -
          ccmRestrictedWeilFormBirmanSchwinger a E) x) y := by
  unfold ccmRestrictedWeilForm ccmRestrictedWeilFormBirmanSchwinger
    ccmRestrictedWeilBirmanSchwingerForcing
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply]
  rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
  simp only [smul_apply]
  rw [inner_sub_left]
  rw [show (1 : suzukiApertureHilbert a →L[ℂ]
      suzukiApertureHilbert a) (ccmArchimedeanFormToAperture a x) =
      ccmArchimedeanFormToAperture a x by rfl]
  rw [inner_smul_left
    (ccmArchimedeanFormToAperture a x)
    (ccmArchimedeanFormToAperture a y) (E : ℂ), Complex.conj_ofReal]
  ring

theorem ccmRestrictedWeilCanonicalGround_shiftedDefect_eq_tail
    (a : SuzukiPositiveAperture) (h : CCMArchimedeanFormDomain a) :
    let u := ccmRestrictedWeilCanonicalGroundFormLift a
    let m := u - h
    ccmRestrictedWeilSourceQuadratic a h -
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a h‖ ^ 2 =
      ccmRestrictedWeilSourceQuadratic a m -
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a m‖ ^ 2 := by
  dsimp only
  let E := ccmRestrictedWeilGroundEnergy a
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  let m := u - h
  let K := ccmRestrictedWeilFormBirmanSchwinger a E
  let T := ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) - K
  have hKu : K u = u := by
    dsimp only [K, E, u]
    exact ccmRestrictedWeilCanonicalGroundFormLift_birmanSchwinger_fixed a
  have hTu : T u = 0 := by
    dsimp only [T]
    simp [hKu]
  have hTm : T m = -(T h) := by
    dsimp only [m]
    rw [map_sub, hTu, zero_sub]
  have hsymm : inner ℂ (T h) u = inner ℂ h (T u) := by
    have hKsymm : inner ℂ (K h) u = inner ℂ h (K u) := by
      exact (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a E).isSymmetric h u
    dsimp only [T]
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, inner_sub_right]
    rw [hKsymm]
  have hquad : inner ℂ (T h) h = inner ℂ (T m) m := by
    have hhm : h = u - m := by
      dsimp only [m]
      abel
    have hsecond : inner ℂ (T h) h = inner ℂ (T h) (u - m) :=
      congrArg (fun z => inner ℂ (T h) z) hhm
    rw [hsecond, inner_sub_right, hsymm, hTu, inner_zero_right, zero_sub,
      hTm, inner_neg_left]
  have hh := congrArg Complex.re (ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger a E h h)
  have hm := congrArg Complex.re (ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger a E m m)
  have hmass (x : CCMArchimedeanFormDomain a) :
      (inner ℂ ((E : ℂ) • ccmArchimedeanFormToAperture a x)
        (ccmArchimedeanFormToAperture a x)).re =
        E * ‖ccmArchimedeanFormToAperture a x‖ ^ 2 := by
    rw [inner_smul_left
        (ccmArchimedeanFormToAperture a x)
        (ccmArchimedeanFormToAperture a x) (E : ℂ), Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K]
    let r : ℝ := ‖ccmArchimedeanFormToAperture a x‖
    change (((E : ℂ) * (r : ℂ) ^ 2).re) = E * r ^ 2
    have hr : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by norm_cast
    have hre : ((r : ℂ) ^ 2).re = r ^ 2 := by
      rw [hr]
      exact Complex.ofReal_re _
    have him : ((r : ℂ) ^ 2).im = 0 := by
      rw [hr]
      exact Complex.ofReal_im _
    rw [Complex.mul_re, hre, him]
    norm_num
  rw [Complex.sub_re, ccmRestrictedWeilForm_self_re_eq_source, hmass] at hh hm
  dsimp only [T, K] at hquad hh hm
  calc
    ccmRestrictedWeilSourceQuadratic a h -
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a h‖ ^ 2 =
      (inner ℂ
        ((ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) -
          ccmRestrictedWeilFormBirmanSchwinger a E) h) h).re := hh
    _ = (inner ℂ
        ((ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) -
          ccmRestrictedWeilFormBirmanSchwinger a E) m) m).re :=
      congrArg Complex.re hquad
    _ = ccmRestrictedWeilSourceQuadratic a m -
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a m‖ ^ 2 := hm.symm

/-- Shifted energy defect of one canonical actual Gamma--Slepian head. -/
def ccmRestrictedWeilCanonicalGroundHeadDefect
    (a : SuzukiPositiveAperture) (n : ℕ) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a
      (ccmRestrictedWeilCanonicalGroundHead a n) -
    ccmRestrictedWeilGroundEnergy a *
      ‖ccmArchimedeanFormToAperture a
        (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2

theorem ccmRestrictedWeilCanonicalGroundHeadDefect_eq_tail
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilCanonicalGroundHeadDefect a n =
      ccmRestrictedWeilSourceQuadratic a
          (ccmRestrictedWeilCanonicalGroundFormLift a -
            ccmRestrictedWeilCanonicalGroundHead a n) -
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundFormLift a -
              ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 := by
  exact ccmRestrictedWeilCanonicalGround_shiftedDefect_eq_tail a
    (ccmRestrictedWeilCanonicalGroundHead a n)

theorem ccmRestrictedWeilCanonicalGroundHeadDefect_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    0 ≤ ccmRestrictedWeilCanonicalGroundHeadDefect a n := by
  rw [ccmRestrictedWeilCanonicalGroundHeadDefect_eq_tail]
  exact sub_nonneg.mpr
    (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a
      (ccmRestrictedWeilCanonicalGroundFormLift a -
        ccmRestrictedWeilCanonicalGroundHead a n))

/-- Explicit source-aligned rate for the shifted head-energy defect. -/
theorem ccmRestrictedWeilCanonicalGroundHeadDefect_le_rate
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilCanonicalGroundHeadDefect a n ≤
      ccmRestrictedWeilSourceAccuracyThreshold a
          (ccmRestrictedWeilCanonicalHeadAccuracy n) *
          ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2 +
        (‖ccmRestrictedWeilBoundedRemainder a‖ +
            |ccmRestrictedWeilGroundEnergy a|) *
          (ccmRestrictedWeilSourceAccuracyThreshold a
            (ccmRestrictedWeilCanonicalHeadAccuracy n)) ^ 2 *
          ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2 := by
  let m := ccmRestrictedWeilCanonicalGroundFormLift a -
    ccmRestrictedWeilCanonicalGroundHead a n
  let A := ccmArchimedeanFormToAperture a
  let B := ccmRestrictedWeilBoundedRemainder a
  let E := ccmRestrictedWeilGroundEnergy a
  let tau := ccmRestrictedWeilSourceAccuracyThreshold a
    (ccmRestrictedWeilCanonicalHeadAccuracy n)
  let F := ccmRestrictedWeilCanonicalGroundForcing a
  have hform := ccmRestrictedWeilForm_self_re_eq_norm_add_physicalRemainder a m
  rw [ccmRestrictedWeilForm_self_re_eq_source] at hform
  have hinner : (inner ℂ (B (A m)) (A m)).re ≤ ‖B‖ * ‖A m‖ ^ 2 := by
    calc
      (inner ℂ (B (A m)) (A m)).re ≤
          ‖inner ℂ (B (A m)) (A m)‖ := Complex.re_le_norm _
      _ ≤ ‖B (A m)‖ * ‖A m‖ := norm_inner_le_norm (B (A m)) (A m)
      _ ≤ (‖B‖ * ‖A m‖) * ‖A m‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm (A m)) (norm_nonneg _)
      _ = ‖B‖ * ‖A m‖ ^ 2 := by ring
  have hE : -E ≤ |E| := neg_le_abs E
  have hshifted :
      ccmRestrictedWeilSourceQuadratic a m - E * ‖A m‖ ^ 2 ≤
        ‖m‖ ^ 2 + (‖B‖ + |E|) * ‖A m‖ ^ 2 := by
    rw [hform]
    nlinarith [sq_nonneg ‖A m‖]
  have hformRate : ‖m‖ ^ 2 ≤ tau * ‖F‖ ^ 2 := by
    dsimp only [m, tau, F]
    exact ccmRestrictedWeilCanonicalGroundHead_rate a n
  have hphysicalRate : ‖A m‖ ^ 2 ≤ tau ^ 2 * ‖F‖ ^ 2 := by
    dsimp only [m, A, tau, F]
    exact ccmRestrictedWeilCanonicalGroundHead_physical_rate a n
  rw [ccmRestrictedWeilCanonicalGroundHeadDefect_eq_tail]
  change ccmRestrictedWeilSourceQuadratic a m - E * ‖A m‖ ^ 2 ≤ _
  calc
    _ ≤ ‖m‖ ^ 2 + (‖B‖ + |E|) * ‖A m‖ ^ 2 := hshifted
    _ ≤ tau * ‖F‖ ^ 2 + (‖B‖ + |E|) *
          (tau ^ 2 * ‖F‖ ^ 2) := by
      gcongr
    _ = tau * ‖F‖ ^ 2 + (‖B‖ + |E|) * tau ^ 2 * ‖F‖ ^ 2 := by ring

theorem ccmRestrictedWeilCanonicalGroundFormLift_source (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a
        (ccmRestrictedWeilCanonicalGroundFormLift a) =
      ccmRestrictedWeilGroundEnergy a *
        ‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
          suzukiApertureHilbert a)‖ ^ 2 := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source]
  have h := congrArg Complex.re
    (ccmRestrictedWeilCanonicalGroundFormLift_mixed a
      (ccmRestrictedWeilCanonicalGroundFormLift a))
  rw [ccmRestrictedWeilCanonicalGroundFormLift_embedding] at h
  rw [h]
  rw [inner_smul_left
    (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)
    (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)
    (ccmRestrictedWeilGroundEnergy a : ℂ)]
  rw [inner_self_eq_norm_sq_to_K]
  rw [Complex.conj_ofReal]
  let r : ℝ := ‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
    suzukiApertureHilbert a)‖
  change (((ccmRestrictedWeilGroundEnergy a : ℂ) * (r : ℂ) ^ 2).re) =
    ccmRestrictedWeilGroundEnergy a * r ^ 2
  have hr : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by norm_cast
  have hre : ((r : ℂ) ^ 2).re = r ^ 2 := by
    rw [hr]
    exact Complex.ofReal_re _
  have him : ((r : ℂ) ^ 2).im = 0 := by
    rw [hr]
    exact Complex.ofReal_im _
  rw [Complex.mul_re, hre, him]
  norm_num

theorem tendsto_ccmRestrictedWeilCanonicalGroundHead_sourceQuadratic (a : SuzukiPositiveAperture) :
    Tendsto
      (fun n => ccmRestrictedWeilSourceQuadratic a
        (ccmRestrictedWeilCanonicalGroundHead a n)) atTop
      (nhds (ccmRestrictedWeilGroundEnergy a *
        ‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
          suzukiApertureHilbert a)‖ ^ 2)) := by
  rw [← ccmRestrictedWeilCanonicalGroundFormLift_source]
  exact (continuous_ccmRestrictedWeilSourceQuadratic a).continuousAt.tendsto.comp
    (tendsto_ccmRestrictedWeilCanonicalGroundHead a)

/-- Exact asymptotic margin on the canonical actual heads.  The limiting head Rayleigh quotient is
the physical ground energy divided by the complete-form mass of its canonical lift. -/
theorem tendsto_ccmRestrictedWeilCanonicalGroundHead_sourceQuadratic_div_normSq
    (a : SuzukiPositiveAperture) :
    Tendsto
      (fun n => ccmRestrictedWeilSourceQuadratic a
          (ccmRestrictedWeilCanonicalGroundHead a n) /
        ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2) atTop
      (nhds ((ccmRestrictedWeilGroundEnergy a *
          ‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
            suzukiApertureHilbert a)‖ ^ 2) /
        ‖ccmRestrictedWeilCanonicalGroundFormLift a‖ ^ 2)) := by
  have hu : ccmRestrictedWeilCanonicalGroundFormLift a ≠ 0 := by
    intro hu
    have he := ccmRestrictedWeilCanonicalGroundFormLift_embedding a
    rw [hu, map_zero] at he
    exact ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a he.symm
  have hnorm : Tendsto
      (fun n => ‖ccmRestrictedWeilCanonicalGroundHead a n‖) atTop
      (nhds ‖ccmRestrictedWeilCanonicalGroundFormLift a‖) :=
    (continuous_norm.tendsto _).comp
      (tendsto_ccmRestrictedWeilCanonicalGroundHead a)
  exact (tendsto_ccmRestrictedWeilCanonicalGroundHead_sourceQuadratic a).div
    (hnorm.pow 2) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))

/-- At a zero-energy first contact, canonical-head coercivity margins necessarily vanish. -/
theorem tendsto_ccmRestrictedWeilCanonicalGroundHead_margin_zero_of_groundEnergy_eq_zero
    (a : SuzukiPositiveAperture)
    (hE : ccmRestrictedWeilGroundEnergy a = 0) :
    Tendsto
      (fun n => ccmRestrictedWeilSourceQuadratic a
          (ccmRestrictedWeilCanonicalGroundHead a n) /
        ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2) atTop
      (nhds 0) := by
  convert
    tendsto_ccmRestrictedWeilCanonicalGroundHead_sourceQuadratic_div_normSq a using 1
  rw [hE, zero_mul, zero_div]

/-- **Uniform-margin no-go at first contact.**  If the exact restricted-Weil ground energy is zero,
then no fixed positive `delta` can satisfy `delta * ‖h_n‖² ≤ Q_a(h_n)` on the canonical cofinal
Gamma--Slepian heads.  Route O must therefore prove a vanishing-error inequality, not a fixed-gap
coercivity estimate, at a possible first-contact aperture. -/
theorem not_eventually_ccmRestrictedWeilCanonicalGroundHead_uniform_positive_margin_of_groundEnergy_eq_zero
    (a : SuzukiPositiveAperture)
    (hE : ccmRestrictedWeilGroundEnergy a = 0) {delta : ℝ} (hdelta : 0 < delta) :
    ¬ ∀ᶠ n in atTop,
      delta * ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 ≤
        ccmRestrictedWeilSourceQuadratic a
          (ccmRestrictedWeilCanonicalGroundHead a n) := by
  intro hmargin
  have hu : ccmRestrictedWeilCanonicalGroundFormLift a ≠ 0 := by
    intro hu
    have he := ccmRestrictedWeilCanonicalGroundFormLift_embedding a
    rw [hu, map_zero] at he
    exact ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a he.symm
  have hnorm : Tendsto
      (fun n => ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2) atTop
      (nhds (‖ccmRestrictedWeilCanonicalGroundFormLift a‖ ^ 2)) :=
    ((continuous_norm.tendsto _).comp
      (tendsto_ccmRestrictedWeilCanonicalGroundHead a)).pow 2
  have hnormPos : 0 < ‖ccmRestrictedWeilCanonicalGroundFormLift a‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hnormEventually : ∀ᶠ n in atTop,
      0 < ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 :=
    (hnorm.eventually (Ioi_mem_nhds hnormPos)).mono fun n hn => hn
  have hratio : ∀ᶠ n in atTop,
      delta ≤ ccmRestrictedWeilSourceQuadratic a
          (ccmRestrictedWeilCanonicalGroundHead a n) /
        ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 := by
    filter_upwards [hmargin, hnormEventually] with n hn hnpos
    exact (le_div_iff₀ hnpos).2 hn
  have hzero :=
    tendsto_ccmRestrictedWeilCanonicalGroundHead_margin_zero_of_groundEnergy_eq_zero a hE
  have hlt : ∀ᶠ n in atTop,
      ccmRestrictedWeilSourceQuadratic a
          (ccmRestrictedWeilCanonicalGroundHead a n) /
        ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 < delta :=
    hzero.eventually (Iio_mem_nhds hdelta)
  obtain ⟨n, hn, hnl⟩ := (hratio.and hlt).exists
  exact (not_lt_of_ge hn) hnl

/-- A fixed positive cofinal coercivity margin on canonical heads is equivalent to *strictly*
positive ground energy.  It is stronger than endpoint nonnegativity and therefore cannot be the
vanishing-error estimate used at a possible first contact. -/
theorem ccmRestrictedWeilGroundEnergy_pos_iff_exists_eventually_canonicalGroundHead_uniform_margin
    (a : SuzukiPositiveAperture) :
    0 < ccmRestrictedWeilGroundEnergy a ↔
      ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ n in atTop,
        delta * ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a
            (ccmRestrictedWeilCanonicalGroundHead a n) := by
  let E := ccmRestrictedWeilGroundEnergy a
  let p := ‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
    suzukiApertureHilbert a)‖ ^ 2
  let f := ‖ccmRestrictedWeilCanonicalGroundFormLift a‖ ^ 2
  let L := E * p / f
  have hp : 0 < p := by
    dsimp only [p]
    exact sq_pos_of_pos (norm_pos_iff.mpr
      (ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a))
  have hu : ccmRestrictedWeilCanonicalGroundFormLift a ≠ 0 := by
    intro hu
    have he := ccmRestrictedWeilCanonicalGroundFormLift_embedding a
    rw [hu, map_zero] at he
    exact ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a he.symm
  have hf : 0 < f := by
    dsimp only [f]
    exact sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hlimit : Tendsto
      (fun n => ccmRestrictedWeilSourceQuadratic a
          (ccmRestrictedWeilCanonicalGroundHead a n) /
        ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2) atTop
      (nhds L) := by
    dsimp only [L, E, p, f]
    exact tendsto_ccmRestrictedWeilCanonicalGroundHead_sourceQuadratic_div_normSq a
  have hnorm : Tendsto
      (fun n => ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2) atTop
      (nhds f) := by
    dsimp only [f]
    exact ((continuous_norm.tendsto _).comp
      (tendsto_ccmRestrictedWeilCanonicalGroundHead a)).pow 2
  have hnormEventually : ∀ᶠ n in atTop,
      0 < ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 :=
    hnorm.eventually (Ioi_mem_nhds hf)
  constructor
  · intro hE
    have hL : 0 < L := by
      dsimp only [L, E]
      exact div_pos (mul_pos hE hp) hf
    refine ⟨L / 2, half_pos hL, ?_⟩
    have hratio : ∀ᶠ n in atTop, L / 2 <
        ccmRestrictedWeilSourceQuadratic a
            (ccmRestrictedWeilCanonicalGroundHead a n) /
          ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 :=
      hlimit.eventually (Ioi_mem_nhds (half_lt_self hL))
    filter_upwards [hratio, hnormEventually] with n hn hnpos
    exact ((lt_div_iff₀ hnpos).1 hn).le
  · rintro ⟨delta, hdelta, hmargin⟩
    have hratio : ∀ᶠ n in atTop, delta ≤
        ccmRestrictedWeilSourceQuadratic a
            (ccmRestrictedWeilCanonicalGroundHead a n) /
          ‖ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 := by
      filter_upwards [hmargin, hnormEventually] with n hn hnpos
      exact (le_div_iff₀ hnpos).2 hn
    have hdeltaL : delta ≤ L := ge_of_tendsto hlimit hratio
    have hL : 0 < L := hdelta.trans_le hdeltaL
    have hmul : L * f = E * p := by
      dsimp only [L]
      field_simp
    have hEp : 0 < E * p := by
      rw [← hmul]
      exact mul_pos hL hf
    nlinarith

/-- Literal reverse-prime inequality on one canonical actual Gamma--Slepian head. -/
def CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound
    (a : SuzukiPositiveAperture) (n : ℕ) : Prop :=
  let h := ccmRestrictedWeilCanonicalGroundHead a n
  (inner ℂ (ccmRestrictedWeilFormPrimeCompression a h) h).re ≤
    ‖h‖ ^ 2 +
      (inner ℂ
        ((ccmArchimedeanRemainderScalar •
          ccmArchimedeanGammaSlepianGram a) h) h).re +
      (inner ℂ (ccmRestrictedWeilFormPolarCompression a h) h).re

theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_source_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmRestrictedWeilSourceQuadratic a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  let h := ccmRestrictedWeilCanonicalGroundHead a n
  have hform := ccmRestrictedWeilForm_self_re_eq_norm_add_formRemainder a h
  rw [ccmRestrictedWeilFormRemainder_eq_scalarGamma_add_polar_sub_prime] at hform
  simp only [add_apply, sub_apply, inner_add_left, inner_sub_left,
    Complex.add_re, Complex.sub_re] at hform
  rw [ccmRestrictedWeilForm_self_re_eq_source] at hform
  dsimp only [CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound]
  change (inner ℂ (ccmRestrictedWeilFormPrimeCompression a h) h).re ≤
      ‖h‖ ^ 2 +
        (inner ℂ ((ccmArchimedeanRemainderScalar •
          ccmArchimedeanGammaSlepianGram a) h) h).re +
        (inner ℂ (ccmRestrictedWeilFormPolarCompression a h) h).re ↔
      0 ≤ ccmRestrictedWeilSourceQuadratic a h
  rw [hform]
  constructor <;> intro hx <;> linarith

/-- At fixed aperture, eventual reverse-prime control on the canonical actual heads is exactly
nonnegativity of the true restricted-Weil floor. -/
theorem ccmRestrictedWeilGroundEnergy_nonneg_iff_eventually_canonicalGroundHead_reversePrimeBound
    (a : SuzukiPositiveAperture) :
    0 ≤ ccmRestrictedWeilGroundEnergy a ↔
      ∀ᶠ n in atTop, CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n := by
  constructor
  · intro hE
    filter_upwards with n
    apply (ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_source_nonneg a n).2
    have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a
      (ccmRestrictedWeilCanonicalGroundHead a n)
    exact (mul_nonneg hE (sq_nonneg _)).trans hfloor
  · intro hheads
    have hnonneg : ∀ᶠ n in atTop,
        0 ≤ ccmRestrictedWeilSourceQuadratic a
          (ccmRestrictedWeilCanonicalGroundHead a n) := by
      filter_upwards [hheads] with n hn
      exact (ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_source_nonneg a n).1 hn
    have hlimitNonneg : 0 ≤ ccmRestrictedWeilGroundEnergy a *
        ‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
          suzukiApertureHilbert a)‖ ^ 2 :=
      ge_of_tendsto (tendsto_ccmRestrictedWeilCanonicalGroundHead_sourceQuadratic a) hnonneg
    have hgroundNormPos : 0 <
        ‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
          suzukiApertureHilbert a)‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr
        (ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a))
    nlinarith

end RHTower
