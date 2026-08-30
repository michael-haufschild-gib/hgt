import GaloisForLFunctions.RHTower.FZZCigarParityReflectedFermiInformationGradientFlow
import GaloisForLFunctions.RHTower.FZZCigarParityDiagonalSuperKMSNoGo
import GaloisForLFunctions.RHTower.SuzukiTorqueContinuationPole
import GaloisForLFunctions.RHTower.XiLogDerivSymmetry
import GaloisForLFunctions.RHTower.SuzukiXiFirstDefectJet
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.HTGeometry.SampledSmallSmooth
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles
import GaloisForLFunctions.RHTower.HedenmalmStokesCurvatureNormalizedFluxBudget
import GaloisForLFunctions.HTGeometry.MeromorphicPuncturedRepresentation

/-!
# FZZ parity real-slice holomorphic Fermi-generator no-go

The literal FZZ parity Mellin transform factors on the open critical strip as a holomorphic
nonvanishing completion unit times `xi`. Consequently its exact reflected-Fermi information
velocity has a unique meromorphic continuation. At every Xi zero `ρ` of multiplicity `m`,
that velocity is

`2 * m * (2 * ρ - 1) / (s - ρ)^2`

plus an analytic remainder: all possible simple-pole terms cancel. The coefficient is nonzero.
An identity-theorem argument after clearing the denominator by `xi^2` then rules out every
holomorphic function on the full strip agreeing with the velocity only on the physical real slice.
This kills FZZ-P-D2 without RH, zero simplicity, or any off-axis restriction on the candidate flow.
-/

open Complex Set Filter Topology GaloisForLFunctions

noncomputable section

namespace RHTower

def fzzD2OpenStrip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

theorem isOpen_fzzD2OpenStrip : IsOpen fzzD2OpenStrip := by
  rw [fzzD2OpenStrip]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem isPreconnected_fzzD2OpenStrip : IsPreconnected fzzD2OpenStrip := by
  rw [fzzD2OpenStrip]
  exact ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected

theorem fzzD2OpenStrip_reflect {s : ℂ} (hs : s ∈ fzzD2OpenStrip) :
    1 - s ∈ fzzD2OpenStrip := by
  rw [fzzD2OpenStrip] at hs ⊢
  simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.one_re]
  rcases hs with ⟨h0, h1⟩
  constructor <;> linarith

def fzzCigarParityXiCompletionUnit (s : ℂ) : ℂ :=
  Complex.Gamma s * (1 - (2 : ℂ) ^ (1 - s)) / archFactor s

theorem analyticAt_fzzCigarParityXiCompletionUnit {s : ℂ}
    (hs : s ∈ fzzD2OpenStrip) :
    AnalyticAt ℂ fzzCigarParityXiCompletionUnit s := by
  have hGamma : AnalyticAt ℂ Complex.Gamma s :=
    HTGeometry.analyticAt_Gamma_of_re_pos hs.1
  have hdyadic : AnalyticAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) s := by
    have hslit : (2 : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    fun_prop
  have harch : AnalyticAt ℂ archFactor s :=
    archFactor_analyticOnNhd_re_pos s hs.1
  exact (hGamma.mul hdyadic).div harch (archFactor_ne_zero_strip hs)

theorem fzzCigarParityXiCompletionUnit_ne_zero {s : ℂ}
    (hs : s ∈ fzzD2OpenStrip) :
    fzzCigarParityXiCompletionUnit s ≠ 0 := by
  have hdyadic : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    simpa only [salemSpectralParameter_re_im] using
      (salemDyadicFactor_ne_zero (delta := s.re) (gamma := s.im) hs.2)
  exact div_ne_zero
    (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hs.1) hdyadic)
    (archFactor_ne_zero_strip hs)

theorem fzzCigarParityMellin_eq_completionUnit_mul_xi {s : ℂ}
    (hs : s ∈ fzzD2OpenStrip) :
    fzzCigarParityMellin s = fzzCigarParityXiCompletionUnit s * xi s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    have : ¬ ((0 : ℂ) ∈ fzzD2OpenStrip) := by
      simp [fzzD2OpenStrip]
    exact this hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    have : ¬ ((1 : ℂ) ∈ fzzD2OpenStrip) := by
      simp [fzzD2OpenStrip]
    exact this hs
  rw [fzzCigarParityMellin_eq_closedForm hs.1 hs1,
    xi_eq_archFactor_mul_zeta hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hs.1)]
  rw [fzzCigarParityXiCompletionUnit]
  field_simp [archFactor_ne_zero_strip hs]

theorem eventuallyEq_fzzCigarParityMellin_completionUnit_mul_xi {s : ℂ}
    (hs : s ∈ fzzD2OpenStrip) :
    fzzCigarParityMellin =ᶠ[nhds s]
      fun z => fzzCigarParityXiCompletionUnit z * xi z := by
  filter_upwards [isOpen_fzzD2OpenStrip.mem_nhds hs] with z hz
  exact fzzCigarParityMellin_eq_completionUnit_mul_xi hz

def fzzCigarParityXiCompletionConnection (s : ℂ) : ℂ :=
  logDeriv fzzCigarParityXiCompletionUnit s

theorem analyticAt_fzzCigarParityXiCompletionConnection {s : ℂ}
    (hs : s ∈ fzzD2OpenStrip) :
    AnalyticAt ℂ fzzCigarParityXiCompletionConnection s := by
  have hu := analyticAt_fzzCigarParityXiCompletionUnit hs
  change AnalyticAt ℂ
    (fun z => deriv fzzCigarParityXiCompletionUnit z /
      fzzCigarParityXiCompletionUnit z) s
  exact hu.deriv.div hu (fzzCigarParityXiCompletionUnit_ne_zero hs)

theorem eventuallyEq_logDeriv_fzzCigarParityMellin_eq_completion_add_xi
    {s : ℂ} (hs : s ∈ fzzD2OpenStrip) (hxi : xi s ≠ 0) :
    logDeriv fzzCigarParityMellin =ᶠ[nhds s]
      fun z => fzzCigarParityXiCompletionConnection z + logDeriv xi z := by
  have hu := analyticAt_fzzCigarParityXiCompletionUnit hs
  have hune := hu.continuousAt.eventually_ne
    (fzzCigarParityXiCompletionUnit_ne_zero hs)
  have hxian : AnalyticAt ℂ xi s := xi_analyticOnNhd_univ s (Set.mem_univ s)
  have hxine := hxian.continuousAt.eventually_ne hxi
  filter_upwards [isOpen_fzzD2OpenStrip.mem_nhds hs, hune, hxine,
      hu.eventually_analyticAt, hxian.eventually_analyticAt] with
      z hzstrip hzu hzxi hzuan hzxia
  have hzprod := eventuallyEq_fzzCigarParityMellin_completionUnit_mul_xi hzstrip
  rw [logDeriv_apply, hzprod.deriv_eq, hzprod.eq_of_nhds]
  exact logDeriv_mul z hzu hzxi hzuan.differentiableAt hzxia.differentiableAt

theorem logDeriv_fzzCigarParityMellin_eq_completion_add_xi
    {s : ℂ} (hs : s ∈ fzzD2OpenStrip) (hxi : xi s ≠ 0) :
    logDeriv fzzCigarParityMellin s =
      fzzCigarParityXiCompletionConnection s + logDeriv xi s :=
  (eventuallyEq_logDeriv_fzzCigarParityMellin_eq_completion_add_xi hs hxi).eq_of_nhds

theorem deriv_logDeriv_fzzCigarParityMellin_eq_completion_add_xi
    {s : ℂ} (hs : s ∈ fzzD2OpenStrip) (hxi : xi s ≠ 0) :
    deriv (logDeriv fzzCigarParityMellin) s =
      deriv fzzCigarParityXiCompletionConnection s + deriv (logDeriv xi) s := by
  have h :=
    (eventuallyEq_logDeriv_fzzCigarParityMellin_eq_completion_add_xi hs hxi).deriv_eq
  have ha := analyticAt_fzzCigarParityXiCompletionConnection hs
  have hL : AnalyticAt ℂ (logDeriv xi) s := by
    rw [logDeriv]
    exact (xi_analyticOnNhd_univ s (Set.mem_univ s)).deriv.div
      (xi_analyticOnNhd_univ s (Set.mem_univ s)) hxi
  calc
    deriv (logDeriv fzzCigarParityMellin) s =
        deriv (fun z => fzzCigarParityXiCompletionConnection z + logDeriv xi z) s := h
    _ = deriv fzzCigarParityXiCompletionConnection s + deriv (logDeriv xi) s :=
      (ha.differentiableAt.hasDerivAt.add hL.differentiableAt.hasDerivAt).deriv

theorem logDeriv_fzzCigarParityMellin_ofReal_eq_fermiLogMean
    {sigma : ℝ} (hsigma : 0 < sigma) :
    logDeriv fzzCigarParityMellin (sigma : ℂ) =
      (fermiLogMean sigma : ℂ) := by
  have hMAt : AnalyticAt ℂ fzzCigarParityMellin (sigma : ℂ) :=
    analyticOnNhd_fzzCigarParityMellin (sigma : ℂ) (by simpa using hsigma)
  have hrestrict :=
    HTGeometry.iteratedDeriv_comp_ofReal_of_analyticAt (T := 0) 1
      (H := fzzCigarParityMellin)
      (fun t ht => analyticOnNhd_fzzCigarParityMellin (t : ℂ) (by simpa using ht))
      sigma hsigma
  simp only [iteratedDeriv_one] at hrestrict
  have hZder : HasDerivAt fermiMellinNormalizer (fermiLogMoment sigma 1) sigma := by
    have h := hasDerivAt_fermiLogMoment hsigma 0
    simpa only [fermiLogMoment_zero, Nat.zero_add] using h
  have hfun : (fun x : ℝ => fzzCigarParityMellin (x : ℂ)) =
      fun x : ℝ => (fermiMellinNormalizer x : ℂ) := by
    funext x
    exact fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer x
  have hder := congrArg (fun f : ℝ → ℂ => deriv f sigma) hfun
  rw [hrestrict, hZder.ofReal_comp.deriv] at hder
  rw [logDeriv_apply, hder,
    fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer]
  rw [fermiLogMean, fermiLogMoment_zero]
  push_cast
  rfl

theorem deriv_logDeriv_fzzCigarParityMellin_ofReal_eq_fermiLogVariance
    {sigma : ℝ} (hsigma : 0 < sigma) :
    deriv (logDeriv fzzCigarParityMellin) (sigma : ℂ) =
      (fermiLogVariance sigma : ℂ) := by
  have hMlog : ∀ t : ℝ, 0 < t →
      AnalyticAt ℂ (logDeriv fzzCigarParityMellin) (t : ℂ) := by
    intro t ht
    have hMAt : AnalyticAt ℂ fzzCigarParityMellin (t : ℂ) :=
      analyticOnNhd_fzzCigarParityMellin (t : ℂ) (by simpa using ht)
    have hMne : fzzCigarParityMellin (t : ℂ) ≠ 0 := by
      rw [fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer]
      exact Complex.ofReal_ne_zero.mpr (fermiMellinNormalizer_pos ht).ne'
    rw [logDeriv]
    exact hMAt.deriv.div hMAt hMne
  have hrestrict :=
    HTGeometry.iteratedDeriv_comp_ofReal_of_analyticAt (T := 0) 1
      (H := logDeriv fzzCigarParityMellin) hMlog sigma hsigma
  simp only [iteratedDeriv_one] at hrestrict
  have hev : (fun x : ℝ => logDeriv fzzCigarParityMellin (x : ℂ)) =ᶠ[nhds sigma]
      fun x : ℝ => (fermiLogMean x : ℂ) := by
    filter_upwards [Ioi_mem_nhds hsigma] with x hx
    exact logDeriv_fzzCigarParityMellin_ofReal_eq_fermiLogMean hx
  have hder := hev.deriv_eq
  rw [hrestrict, (hasDerivAt_fermiLogMean hsigma).ofReal_comp.deriv] at hder
  exact hder

def fzzCigarParityMeromorphicInformationForce (s : ℂ) : ℂ :=
  4 * logDeriv xi s +
    2 * (fzzCigarParityXiCompletionConnection s -
      fzzCigarParityXiCompletionConnection (1 - s)) +
    (2 * s - 1) *
      (2 * deriv (logDeriv xi) s +
        deriv fzzCigarParityXiCompletionConnection s +
        deriv fzzCigarParityXiCompletionConnection (1 - s))

def fzzCigarParityMeromorphicInformationVelocity (s : ℂ) : ℂ :=
  -fzzCigarParityMeromorphicInformationForce s

def fzzCigarParityCompletionRemainder (s : ℂ) : ℂ :=
  2 * (fzzCigarParityXiCompletionConnection s -
    fzzCigarParityXiCompletionConnection (1 - s)) +
  (2 * s - 1) *
    (deriv fzzCigarParityXiCompletionConnection s +
      deriv fzzCigarParityXiCompletionConnection (1 - s))

theorem analyticAt_fzzCigarParityCompletionRemainder {s : ℂ}
    (hs : s ∈ fzzD2OpenStrip) :
    AnalyticAt ℂ fzzCigarParityCompletionRemainder s := by
  have ha := analyticAt_fzzCigarParityXiCompletionConnection hs
  have har := analyticAt_fzzCigarParityXiCompletionConnection
    (fzzD2OpenStrip_reflect hs)
  have hcomp : AnalyticAt ℂ
      (fun z : ℂ => fzzCigarParityXiCompletionConnection (1 - z)) s := by
    exact har.comp (x := s) (g := fzzCigarParityXiCompletionConnection)
      (f := fun z : ℂ => 1 - z) (by fun_prop)
  have hb := ha.deriv
  have hbr := har.deriv
  have hbcomp : AnalyticAt ℂ
      (fun z : ℂ => deriv fzzCigarParityXiCompletionConnection (1 - z)) s := by
    exact hbr.comp (x := s) (g := deriv fzzCigarParityXiCompletionConnection)
      (f := fun z : ℂ => 1 - z) (by fun_prop)
  change AnalyticAt ℂ (fun z : ℂ =>
    2 * (fzzCigarParityXiCompletionConnection z -
      fzzCigarParityXiCompletionConnection (1 - z)) +
    (2 * z - 1) *
      (deriv fzzCigarParityXiCompletionConnection z +
        deriv fzzCigarParityXiCompletionConnection (1 - z))) s
  exact (analyticAt_const.mul (ha.sub hcomp)).add
    ((analyticAt_const.mul analyticAt_id |>.sub analyticAt_const).mul
      (hb.add hbcomp))

private theorem fzzD2_analytic_meromorphicOrderAt_ne_neg_one {f : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) :
    meromorphicOrderAt f p ≠ ((-1 : ℤ) : WithTop ℤ) := by
  rw [hf.meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f p) ⊤ with htop | hne
  · rw [htop]
    simp only [ENat.map_top]
    exact WithTop.top_ne_coe
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hm]
    simp only [ENat.map_coe]
    intro hcon
    have : (m : ℤ) = -1 := by exact_mod_cast hcon
    omega

private theorem fzzD2_analytic_neg_one_le_meromorphicOrderAt {f : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p := by
  rw [hf.meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f p) ⊤ with htop | hne
  · rw [htop]
    simp
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hm]
    simp only [ENat.map_coe]
    have hle : ((-1 : ℤ)) ≤ (m : ℤ) := by omega
    exact_mod_cast WithTop.coe_le_coe.mpr hle

theorem meromorphicOrderAt_fzzCigarParityMeromorphicInformationForce_eq_neg_two
    {ρ : ℂ} (hstrip : ρ ∈ fzzD2OpenStrip) (hz : xi ρ = 0) :
    meromorphicOrderAt fzzCigarParityMeromorphicInformationForce ρ =
      ((-2 : ℤ) : WithTop ℤ) := by
  have hcenter : 2 * ρ - 1 ≠ 0 := by
    intro hzero
    have hrho : ρ = 1 / 2 := by
      linear_combination hzero / 2
    apply xi_one_half_ne_zero
    rw [← hrho]
    exact hz
  let dominant : ℂ → ℂ := fun z =>
    (2 * (2 * z - 1)) * deriv (logDeriv xi) z
  let correction : ℂ → ℂ := fun z =>
    2 * (fzzCigarParityXiCompletionConnection z -
      fzzCigarParityXiCompletionConnection (1 - z)) +
    (2 * z - 1) *
      (deriv fzzCigarParityXiCompletionConnection z +
        deriv fzzCigarParityXiCompletionConnection (1 - z))
  let remainder : ℂ → ℂ := fun z => 4 * logDeriv xi z + correction z
  have hfactorA : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * z - 1)) ρ := by
    fun_prop
  have hfactor0 : (fun z : ℂ => 2 * (2 * z - 1)) ρ ≠ 0 :=
    mul_ne_zero (by norm_num) hcenter
  have hfactorOrder :
      meromorphicOrderAt (fun z : ℂ => 2 * (2 * z - 1)) ρ = 0 := by
    rw [hfactorA.meromorphicOrderAt_eq,
      hfactorA.analyticOrderAt_eq_zero.mpr hfactor0]
    simp
  have hdominantM : MeromorphicAt dominant ρ := by
    exact hfactorA.meromorphicAt.mul (meromorphicAt_deriv_logDeriv_xi ρ)
  have hdominantOrder :
      meromorphicOrderAt dominant ρ = ((-2 : ℤ) : WithTop ℤ) := by
    rw [show dominant = (fun z : ℂ => 2 * (2 * z - 1)) *
        deriv (logDeriv xi) by rfl,
      meromorphicOrderAt_mul hfactorA.meromorphicAt
        (meromorphicAt_deriv_logDeriv_xi ρ),
      hfactorOrder, meromorphicOrderAt_deriv_logDeriv_xi_eq_neg_two hz]
    norm_num
  have hcorrectionA : AnalyticAt ℂ correction ρ :=
    analyticAt_fzzCigarParityCompletionRemainder hstrip
  have hfourA : AnalyticAt ℂ (fun _z : ℂ => (4 : ℂ)) ρ := analyticAt_const
  have hfour0 : (4 : ℂ) ≠ 0 := by norm_num
  have hfourOrder : meromorphicOrderAt (fun _z : ℂ => (4 : ℂ)) ρ = 0 := by
    rw [hfourA.meromorphicOrderAt_eq,
      hfourA.analyticOrderAt_eq_zero.mpr hfour0]
    simp
  have hfourLM : MeromorphicAt (fun z : ℂ => 4 * logDeriv xi z) ρ :=
    hfourA.meromorphicAt.mul (meromorphicAt_logDeriv_xi ρ)
  have hfourLOrder :
      meromorphicOrderAt (fun z : ℂ => 4 * logDeriv xi z) ρ =
        ((-1 : ℤ) : WithTop ℤ) := by
    rw [show (fun z : ℂ => 4 * logDeriv xi z) =
        (fun _z : ℂ => (4 : ℂ)) * logDeriv xi by rfl,
      meromorphicOrderAt_mul hfourA.meromorphicAt (meromorphicAt_logDeriv_xi ρ),
      hfourOrder, meromorphicOrderAt_logDeriv_xi_eq_neg_one hz]
    norm_num
  have hremainderM : MeromorphicAt remainder ρ :=
    hfourLM.add hcorrectionA.meromorphicAt
  have hremainderOrder :
      meromorphicOrderAt remainder ρ = ((-1 : ℤ) : WithTop ℤ) := by
    have hne : meromorphicOrderAt (fun z : ℂ => 4 * logDeriv xi z) ρ ≠
        meromorphicOrderAt correction ρ := by
      rw [hfourLOrder]
      exact (fzzD2_analytic_meromorphicOrderAt_ne_neg_one hcorrectionA).symm
    have hadd := meromorphicOrderAt_add_of_ne hfourLM hcorrectionA.meromorphicAt hne
    change meromorphicOrderAt remainder ρ = _ at hadd ⊢
    rw [hadd, hfourLOrder]
    exact min_eq_left (fzzD2_analytic_neg_one_le_meromorphicOrderAt hcorrectionA)
  have hforce : fzzCigarParityMeromorphicInformationForce = dominant + remainder := by
    funext z
    rw [fzzCigarParityMeromorphicInformationForce]
    dsimp [dominant, remainder, correction]
    ring
  rw [hforce]
  have hne : meromorphicOrderAt dominant ρ ≠ meromorphicOrderAt remainder ρ := by
    rw [hdominantOrder, hremainderOrder]
    norm_num
  rw [meromorphicOrderAt_add_of_ne hdominantM hremainderM hne,
    hdominantOrder, hremainderOrder]
  exact min_eq_left (WithTop.coe_le_coe.mpr (by omega))

theorem meromorphicOrderAt_fzzCigarParityMeromorphicInformationVelocity_eq_neg_two
    {ρ : ℂ} (hstrip : ρ ∈ fzzD2OpenStrip) (hz : xi ρ = 0) :
    meromorphicOrderAt fzzCigarParityMeromorphicInformationVelocity ρ =
      ((-2 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    (fun z => -fzzCigarParityMeromorphicInformationForce z) ρ = _
  rw [← meromorphicOrderAt_fun_neg]
  exact meromorphicOrderAt_fzzCigarParityMeromorphicInformationForce_eq_neg_two hstrip hz

/-- Local multiplicity-sensitive principal parts of the Xi connection and curvature. -/
theorem exists_xi_logDeriv_curvature_principalParts (ρ : ℂ) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ (logDeriv h) ρ ∧
      AnalyticAt ℂ (deriv (logDeriv h)) ρ ∧
      logDeriv xi =ᶠ[nhdsWithin ρ {ρ}ᶜ]
        (fun z => ((analyticOrderAt xi ρ).toNat : ℂ) / (z - ρ) + logDeriv h z) ∧
      deriv (logDeriv xi) =ᶠ[nhdsWithin ρ {ρ}ᶜ]
        (fun z => -((analyticOrderAt xi ρ).toNat : ℂ) / (z - ρ) ^ 2 +
          deriv (logDeriv h) z) := by
  obtain ⟨R, hR, h, hhan, hh0, hlocal⟩ :=
    exists_xi_normalizedLogDeriv_factorization ρ
  have hρball : ρ ∈ Metric.ball ρ R := Metric.mem_ball_self hR
  have hhρ : AnalyticAt ℂ h ρ := hhan ρ hρball
  have hlogh : AnalyticAt ℂ (logDeriv h) ρ := by
    rw [logDeriv]
    exact hhρ.deriv.div hhρ (hh0 ρ hρball)
  have hball : Metric.ball ρ R ∈ nhds ρ := Metric.ball_mem_nhds ρ hR
  have hL : logDeriv xi =ᶠ[nhdsWithin ρ {ρ}ᶜ]
      (fun z => ((analyticOrderAt xi ρ).toNat : ℂ) / (z - ρ) + logDeriv h z) := by
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hzball hzne
    have hzsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
    have hz := hlocal z hzball hzne
    field_simp [hzsub] at hz ⊢
    linear_combination hz
  have hQraw := GaloisForLFunctions.EventuallyEq.nhdsNE_iteratedDeriv hL 1
  simp only [iteratedDeriv_one] at hQraw
  have hQ : deriv (logDeriv xi) =ᶠ[nhdsWithin ρ {ρ}ᶜ]
      (fun z => -((analyticOrderAt xi ρ).toNat : ℂ) / (z - ρ) ^ 2 +
        deriv (logDeriv h) z) := by
    filter_upwards [hQraw, nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with
        z hzQ hzball hzne
    rw [hzQ]
    have hzsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
    have hp : HasDerivAt
        (fun w : ℂ => ((analyticOrderAt xi ρ).toNat : ℂ) / (w - ρ))
        (-((analyticOrderAt xi ρ).toNat : ℂ) / (z - ρ) ^ 2) z := by
      have hden := (hasDerivAt_id z).sub_const ρ
      have hinv := hden.inv hzsub
      have hmul := HasDerivAt.const_mul
        ((analyticOrderAt xi ρ).toNat : ℂ) hinv
      convert hmul using 1
      all_goals try rfl
      simp only [id_eq]
      ring
    have hhAt : AnalyticAt ℂ (logDeriv h) z := by
      have hhz := hhan z hzball
      rw [logDeriv]
      exact hhz.deriv.div hhz (hh0 z hzball)
    exact (hp.add hhAt.differentiableAt.hasDerivAt).deriv
  exact ⟨h, hlogh, hlogh.deriv, hL, hQ⟩

/-- The FZZ information velocity has a pure double principal part at every Xi zero.
The possible simple pole cancels identically between the connection and curvature terms. -/
theorem exists_fzzCigarParityMeromorphicInformationVelocity_principalPart
    {ρ : ℂ} (hstrip : ρ ∈ fzzD2OpenStrip) (hz : xi ρ = 0) :
    ∃ remainder : ℂ → ℂ,
      AnalyticAt ℂ remainder ρ ∧
      2 * ((analyticOrderAt xi ρ).toNat : ℂ) * (2 * ρ - 1) ≠ 0 ∧
      fzzCigarParityMeromorphicInformationVelocity =ᶠ[nhdsWithin ρ {ρ}ᶜ]
        fun z =>
          2 * ((analyticOrderAt xi ρ).toNat : ℂ) * (2 * ρ - 1) / (z - ρ) ^ 2 +
            remainder z := by
  obtain ⟨h, hlog, hcurv, hL, hQ⟩ :=
    exists_xi_logDeriv_curvature_principalParts ρ
  let remainder : ℂ → ℂ := fun z =>
    -(4 * logDeriv h z +
      2 * (2 * z - 1) * deriv (logDeriv h) z +
      fzzCigarParityCompletionRemainder z)
  have hlinear : AnalyticAt ℂ (fun z : ℂ => 2 * z - 1) ρ := by
    fun_prop
  have hrem : AnalyticAt ℂ remainder ρ := by
    dsimp [remainder]
    exact (((analyticAt_const.mul hlog).add
      ((analyticAt_const.mul hlinear).mul hcurv)).add
        (analyticAt_fzzCigarParityCompletionRemainder hstrip)).neg
  have hmNat : (analyticOrderAt xi ρ).toNat ≠ 0 := by
    have hmOrder : analyticOrderAt xi ρ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr
        ⟨xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), hz⟩
    intro hm0
    rcases ENat.toNat_eq_zero.mp hm0 with hzero | htop
    · exact hmOrder hzero
    · exact xi_order_ne_top ρ htop
  have hmComplex : ((analyticOrderAt xi ρ).toNat : ℂ) ≠ 0 := by
    exact_mod_cast hmNat
  have hcenter : 2 * ρ - 1 ≠ 0 := by
    intro hzero
    have hrho : ρ = 1 / 2 := by
      linear_combination hzero / 2
    apply xi_one_half_ne_zero
    rw [← hrho]
    exact hz
  have hcoefficient :
      2 * ((analyticOrderAt xi ρ).toNat : ℂ) * (2 * ρ - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hmComplex) hcenter
  refine ⟨remainder, hrem, hcoefficient, ?_⟩
  filter_upwards [hL, hQ, self_mem_nhdsWithin] with z hzL hzQ hzne
  have hzsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
  rw [fzzCigarParityMeromorphicInformationVelocity,
    fzzCigarParityMeromorphicInformationForce, hzL, hzQ]
  dsimp [fzzCigarParityCompletionRemainder, remainder]
  field_simp [hzsub]
  ring

theorem fzzCigarParityMeromorphicInformationForce_ofReal
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) :
    fzzCigarParityMeromorphicInformationForce (sigma : ℂ) =
      (fzzCigarParityReflectedFermiInformationForce sigma : ℂ) := by
  let s : ℂ := (sigma : ℂ)
  let r : ℂ := 1 - s
  have hs : s ∈ fzzD2OpenStrip := by
    exact ⟨by simpa [s] using h0, by simpa [s] using h1⟩
  have hr : r ∈ fzzD2OpenStrip := fzzD2OpenStrip_reflect hs
  have hMr : r = ((1 - sigma : ℝ) : ℂ) := by
    simp [r, s]
  have hMne : fzzCigarParityMellin s ≠ 0 := by
    rw [show s = (sigma : ℂ) by rfl,
      fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer]
    exact Complex.ofReal_ne_zero.mpr (fermiMellinNormalizer_pos h0).ne'
  have hxi : xi s ≠ 0 := by
    intro hz
    apply hMne
    rw [fzzCigarParityMellin_eq_completionUnit_mul_xi hs, hz, mul_zero]
  have hMrne : fzzCigarParityMellin r ≠ 0 := by
    rw [hMr, fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer]
    exact Complex.ofReal_ne_zero.mpr (fermiMellinNormalizer_pos (by linarith)).ne'
  have hxir : xi r ≠ 0 := by
    intro hz
    apply hMrne
    rw [fzzCigarParityMellin_eq_completionUnit_mul_xi hr, hz, mul_zero]
  have hLs := logDeriv_fzzCigarParityMellin_eq_completion_add_xi hs hxi
  have hLr := logDeriv_fzzCigarParityMellin_eq_completion_add_xi hr hxir
  have hQs := deriv_logDeriv_fzzCigarParityMellin_eq_completion_add_xi hs hxi
  have hQr := deriv_logDeriv_fzzCigarParityMellin_eq_completion_add_xi hr hxir
  calc
    fzzCigarParityMeromorphicInformationForce (sigma : ℂ) =
        2 * (logDeriv fzzCigarParityMellin s - logDeriv fzzCigarParityMellin r) +
          (2 * s - 1) *
            (deriv (logDeriv fzzCigarParityMellin) s +
              deriv (logDeriv fzzCigarParityMellin) r) := by
      rw [fzzCigarParityMeromorphicInformationForce]
      rw [hLs, hLr, hQs, hQr]
      rw [show r = 1 - s by rfl, logDeriv_xi_one_sub,
        deriv_logDeriv_xi_one_sub]
      ring
    _ = (fzzCigarParityReflectedFermiInformationForce sigma : ℂ) := by
      rw [show s = (sigma : ℂ) by rfl, hMr,
        logDeriv_fzzCigarParityMellin_ofReal_eq_fermiLogMean h0,
        logDeriv_fzzCigarParityMellin_ofReal_eq_fermiLogMean (by linarith),
        deriv_logDeriv_fzzCigarParityMellin_ofReal_eq_fermiLogVariance h0,
        deriv_logDeriv_fzzCigarParityMellin_ofReal_eq_fermiLogVariance (by linarith)]
      rw [fzzCigarParityReflectedFermiInformationForce]
      push_cast
      ring

theorem fzzCigarParityMeromorphicInformationVelocity_ofReal
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) :
    fzzCigarParityMeromorphicInformationVelocity (sigma : ℂ) =
      (fzzCigarParityReflectedFermiInformationVelocity sigma : ℂ) := by
  rw [fzzCigarParityMeromorphicInformationVelocity,
    fzzCigarParityReflectedFermiInformationVelocity,
    fzzCigarParityMeromorphicInformationForce_ofReal h0 h1]
  push_cast
  rfl

/-- Holomorphic numerator obtained by clearing the squared Xi denominator from the meromorphic
Fermi information velocity. -/
def fzzCigarParityInformationVelocityPoleCleared (s : ℂ) : ℂ :=
  -(4 * deriv xi s * xi s +
    2 * (fzzCigarParityXiCompletionConnection s -
      fzzCigarParityXiCompletionConnection (1 - s)) * xi s ^ 2 +
    (2 * s - 1) *
      (2 * (deriv (deriv xi) s * xi s - deriv xi s ^ 2) +
        (deriv fzzCigarParityXiCompletionConnection s +
          deriv fzzCigarParityXiCompletionConnection (1 - s)) * xi s ^ 2))

theorem analyticAt_fzzCigarParityInformationVelocityPoleCleared
    {s : ℂ} (hs : s ∈ fzzD2OpenStrip) :
    AnalyticAt ℂ fzzCigarParityInformationVelocityPoleCleared s := by
  have hxi : AnalyticAt ℂ xi s := xi_analyticOnNhd_univ s (Set.mem_univ s)
  have ha := analyticAt_fzzCigarParityXiCompletionConnection hs
  have har := analyticAt_fzzCigarParityXiCompletionConnection
    (fzzD2OpenStrip_reflect hs)
  have hcomp : AnalyticAt ℂ
      (fun z : ℂ => fzzCigarParityXiCompletionConnection (1 - z)) s := by
    exact har.comp (x := s) (g := fzzCigarParityXiCompletionConnection)
      (f := fun z : ℂ => 1 - z) (by fun_prop)
  have hb := ha.deriv
  have hbr := har.deriv
  have hbcomp : AnalyticAt ℂ
      (fun z : ℂ => deriv fzzCigarParityXiCompletionConnection (1 - z)) s := by
    exact hbr.comp (x := s) (g := deriv fzzCigarParityXiCompletionConnection)
      (f := fun z : ℂ => 1 - z) (by fun_prop)
  change AnalyticAt ℂ
    (fun z : ℂ =>
      -(4 * deriv xi z * xi z +
        2 * (fzzCigarParityXiCompletionConnection z -
          fzzCigarParityXiCompletionConnection (1 - z)) * xi z ^ 2 +
        (2 * z - 1) *
          (2 * (deriv (deriv xi) z * xi z - deriv xi z ^ 2) +
            (deriv fzzCigarParityXiCompletionConnection z +
              deriv fzzCigarParityXiCompletionConnection (1 - z)) * xi z ^ 2))) s
  fun_prop

theorem fzzCigarParityInformationVelocityPoleCleared_eq
    {s : ℂ} (hxi : xi s ≠ 0) :
    fzzCigarParityInformationVelocityPoleCleared s =
      xi s ^ 2 * fzzCigarParityMeromorphicInformationVelocity s := by
  have hxian : AnalyticAt ℂ xi s := xi_analyticOnNhd_univ s (Set.mem_univ s)
  have hquot := hxian.deriv.differentiableAt.hasDerivAt.div
    hxian.differentiableAt.hasDerivAt hxi
  have hQ : deriv (logDeriv xi) s =
      (deriv (deriv xi) s * xi s - deriv xi s * deriv xi s) / xi s ^ 2 := by
    change deriv (deriv xi / xi) s = _
    exact hquot.deriv
  rw [fzzCigarParityInformationVelocityPoleCleared,
    fzzCigarParityMeromorphicInformationVelocity,
    fzzCigarParityMeromorphicInformationForce, logDeriv_apply, hQ]
  field_simp [hxi]
  ring

/-- Minimal D2 premise: a holomorphic strip generator agreeing only with exact physical velocity
on the real source slice. -/
def FZZCigarParityRealSliceHolomorphicFermiGeneratorExists : Prop :=
  ∃ G : ℂ → ℂ,
    AnalyticOnNhd ℂ G fzzD2OpenStrip ∧
      ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
        G (sigma : ℂ) =
          (fzzCigarParityReflectedFermiInformationVelocity sigma : ℂ)

theorem not_FZZCigarParityRealSliceHolomorphicFermiGeneratorExists :
    ¬ FZZCigarParityRealSliceHolomorphicFermiGeneratorExists := by
  rintro ⟨G, hG, hreal⟩
  let H : ℂ → ℂ := fun s =>
    xi s ^ 2 * G s - fzzCigarParityInformationVelocityPoleCleared s
  have hH : AnalyticOnNhd ℂ H fzzD2OpenStrip := by
    intro s hs
    have hxi : AnalyticAt ℂ xi s := xi_analyticOnNhd_univ s (Set.mem_univ s)
    exact (hxi.pow 2 |>.mul (hG s hs)).sub
      (analyticAt_fzzCigarParityInformationVelocityPoleCleared hs)
  have hhalf : (1 / 2 : ℂ) ∈ fzzD2OpenStrip := by
    norm_num [fzzD2OpenStrip]
  have hfreq : ∃ᶠ z in nhdsWithin (1 / 2 : ℂ) {(1 / 2 : ℂ)}ᶜ, H z = 0 := by
    let x : ℕ → ℝ := fun n => 1 / 2 + (1 / 4) * (1 / (n + 1 : ℝ))
    have hsmall : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hxR : Tendsto x atTop (nhds (1 / 2 : ℝ)) := by
      simpa [x] using tendsto_const_nhds.add (hsmall.const_mul (1 / 4 : ℝ))
    have hxC : Tendsto (fun n : ℕ => ((x n : ℝ) : ℂ)) atTop
        (nhds (1 / 2 : ℂ)) := by
      have h := (Complex.continuous_ofReal.tendsto (1 / 2 : ℝ)).comp hxR
      norm_num at h ⊢
      exact h
    have hpunc : Tendsto (fun n : ℕ => ((x n : ℝ) : ℂ)) atTop
        (nhdsWithin (1 / 2 : ℂ) {(1 / 2 : ℂ)}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hxC ?_
      exact Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have hxn : x n ≠ 1 / 2 := by
          dsimp [x]
          have hp : 0 < (1 / 4 : ℝ) * (1 / (n + 1 : ℝ)) := by positivity
          linarith
        intro heq
        apply hxn
        have hre := congrArg Complex.re heq
        norm_num at hre ⊢
        exact hre
    apply hpunc.frequently
    exact Filter.Frequently.of_forall fun n => by
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hx0 : 0 < x n := by
        dsimp [x]
        positivity
      have hx1 : x n < 1 := by
        dsimp [x]
        have hinv : 1 / (n + 1 : ℝ) ≤ 1 := by
          rw [div_le_one hn]
          norm_num
        nlinarith
      have hxi : xi ((x n : ℝ) : ℂ) ≠ 0 := by
        have hMne : fzzCigarParityMellin ((x n : ℝ) : ℂ) ≠ 0 := by
          rw [fzzCigarParityMellin_ofReal_eq_fermiMellinNormalizer]
          exact Complex.ofReal_ne_zero.mpr (fermiMellinNormalizer_pos hx0).ne'
        intro hz
        apply hMne
        rw [fzzCigarParityMellin_eq_completionUnit_mul_xi
          (show ((x n : ℝ) : ℂ) ∈ fzzD2OpenStrip by
            exact ⟨by simpa using hx0, by simpa using hx1⟩), hz, mul_zero]
      rw [show H ((x n : ℝ) : ℂ) =
          xi ((x n : ℝ) : ℂ) ^ 2 * G ((x n : ℝ) : ℂ) -
            fzzCigarParityInformationVelocityPoleCleared ((x n : ℝ) : ℂ) by rfl,
        fzzCigarParityInformationVelocityPoleCleared_eq hxi,
        hreal (x n) hx0 hx1,
        fzzCigarParityMeromorphicInformationVelocity_ofReal hx0 hx1]
      ring
  have hHzero : Set.EqOn H (fun _ => 0) fzzD2OpenStrip :=
    hH.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
      isPreconnected_fzzD2OpenStrip hhalf hfreq
  obtain ⟨ρ, hρ0, hρ1, hz⟩ := exists_xi_zero_openStrip
  have hρstrip : ρ ∈ fzzD2OpenStrip := ⟨hρ0, hρ1⟩
  have hxiPunc : ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, xi z ≠ 0 := by
    obtain ⟨R, hR, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ
    have hball : Metric.ball ρ R ∈ nhds ρ := Metric.ball_mem_nhds ρ hR
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hzball hzne
    rw [hfact z hzball]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzne)) (hh0 z hzball)
  have hGV : G =ᶠ[nhdsWithin ρ {ρ}ᶜ]
      fzzCigarParityMeromorphicInformationVelocity := by
    filter_upwards [nhdsWithin_le_nhds
        (isOpen_fzzD2OpenStrip.mem_nhds hρstrip), hxiPunc] with z hzstrip hxiz
    have hzero := hHzero hzstrip
    rw [show H z = xi z ^ 2 * G z -
        fzzCigarParityInformationVelocityPoleCleared z by rfl,
      fzzCigarParityInformationVelocityPoleCleared_eq hxiz] at hzero
    have hxi2 : xi z ^ 2 ≠ 0 := pow_ne_zero 2 hxiz
    apply mul_left_cancel₀ hxi2
    exact sub_eq_zero.mp hzero
  have horder := meromorphicOrderAt_congr hGV
  rw [meromorphicOrderAt_fzzCigarParityMeromorphicInformationVelocity_eq_neg_two
    hρstrip hz] at horder
  exact analytic_meromorphicOrderAt_ne_neg_two (hG ρ hρstrip) horder

end RHTower
