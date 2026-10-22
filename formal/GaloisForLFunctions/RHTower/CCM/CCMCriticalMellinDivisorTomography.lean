import GaloisForLFunctions.RHTower.CCM.CCMInverseTiltedCriticalMellinFactorization

/-!
# Complete divisor tomography in the critical-Mellin coordinate

The regularized polar--prime critical-Mellin defect is meromorphic on `Re u > -1`.  Its
simple poles are exactly the affine image `rho |-> rho - 1` of the complete nontrivial Xi
divisor, and the trailing coefficient at such a pole is the analytic multiplicity of `rho`.

Thus the critical-Mellin coordinate does not merely give a half-plane holomorphy criterion for
RH: it carries the complete Xi divisor with multiplicity.  RH is equivalently the assertion that
all of these poles lie on `Re u = -1/2`, or that the defect is holomorphic on the open half-plane
to the right of that line.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- Critical-Mellin pole coordinate attached to a point of the nontrivial Xi divisor. -/
def criticalMellinXiPole (rho : XiDivisorSupport) : ℂ :=
  (rho : ℂ) - 1

/-- The pole coordinate lies in the natural meromorphic continuation half-plane. -/
theorem criticalMellinXiPole_re_gt_neg_one (rho : XiDivisorSupport) :
    -1 < (criticalMellinXiPole rho).re := by
  rw [criticalMellinXiPole, Complex.sub_re]
  norm_num
  linarith [(xi_divisor_support_re_mem_open_unit rho).1]

/-- Translation from the critical-Mellin coordinate to the regularized-zeta coordinate. -/
theorem criticalMellinXiPole_add_one (rho : XiDivisorSupport) :
    criticalMellinXiPole rho + 1 = (rho : ℂ) := by
  rw [criticalMellinXiPole]
  ring

/-- The regularized critical-Mellin defect is meromorphic on its full natural half-plane. -/
theorem meromorphicOn_regularizedCriticalMellinDefect_rightNegOne :
    MeromorphicOn regularizedCriticalMellinDefect {u : ℂ | -1 < u.re} := by
  intro u hu
  change -1 < u.re at hu
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) u := by fun_prop
  have hden0 : u + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.zero_re] at hre
    norm_num at hre
    linarith
  have hrat : AnalyticAt ℂ (fun z : ℂ => 1 / (z + 1)) u :=
    analyticAt_const.div hshift hden0
  have hlog : MeromorphicAt
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z + 1)) u :=
    MeromorphicAt.comp_analyticAt
      (meromorphicAt_logDeriv_regularizedRiemannZeta (u + 1)) hshift
  simpa only [regularizedCriticalMellinDefect] using! hrat.meromorphicAt.add hlog

/-- Away from a zero of the regularized zeta, the critical-Mellin defect is holomorphic. -/
theorem analyticAt_regularizedCriticalMellinDefect_of_regularizedZeta_ne_zero
    {u : ℂ} (hu : -1 < u.re)
    (hz : regularizedRiemannZeta (u + 1) ≠ 0) :
    AnalyticAt ℂ regularizedCriticalMellinDefect u := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) u := by fun_prop
  have hden0 : u + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.zero_re] at hre
    norm_num at hre
    linarith
  have hrat : AnalyticAt ℂ (fun z : ℂ => 1 / (z + 1)) u :=
    analyticAt_const.div hshift hden0
  have hreg : AnalyticAt ℂ regularizedRiemannZeta (u + 1) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) (u + 1) (Set.mem_univ _)
  have hnum := AnalyticAt.comp (f := fun z : ℂ => z + 1) (x := u)
    hreg.deriv hshift
  have hden := AnalyticAt.comp (f := fun z : ℂ => z + 1) (x := u)
    hreg hshift
  have hlog : AnalyticAt ℂ
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z + 1)) u := by
    rw [show (fun z : ℂ => logDeriv regularizedRiemannZeta (z + 1)) =
        fun z : ℂ => deriv regularizedRiemannZeta (z + 1) /
          regularizedRiemannZeta (z + 1) by
      funext z
      rw [logDeriv_apply]]
    simpa only [Function.comp_apply] using! hnum.div hden hz
  simpa only [regularizedCriticalMellinDefect] using! hrat.add hlog

/-- The residue of the translated logarithmic derivative is the exact Xi multiplicity. -/
theorem tendsto_criticalMellin_shiftedLogDeriv_residue
    (rho : XiDivisorSupport) :
    Tendsto
      (fun u : ℂ => (u - criticalMellinXiPole rho) *
        logDeriv regularizedRiemannZeta (u + 1))
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (inverseTiltedXiMultiplicity rho : ℂ)) := by
  let p : ℂ := criticalMellinXiPole rho
  have hprho : p + 1 = (rho : ℂ) := by
    simpa only [p] using criticalMellinXiPole_add_one rho
  have hreg : AnalyticAt ℂ regularizedRiemannZeta (rho : ℂ) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) (rho : ℂ) (Set.mem_univ _)
  have hzero : regularizedRiemannZeta (rho : ℂ) = 0 := by
    have h := regularizedRiemannZeta_eq_zero_at_inverseTiltedXiPole rho
    rw [inverseTiltedXiPole] at h
    rw [show (rho : ℂ) + 1 / 2 - 1 / 2 = (rho : ℂ) by ring] at h
    exact h
  have hbase := logDeriv_iteratedDeriv_residue_of_zero
    hreg (analyticOrderAt_regularizedRiemannZeta_ne_top (rho : ℂ)) hzero 0
  have hbase' : Tendsto
      (fun t : ℂ => (t - (rho : ℂ)) * logDeriv regularizedRiemannZeta t)
      (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
      (nhds ((analyticOrderAt regularizedRiemannZeta (rho : ℂ)).toNat : ℂ)) := by
    simpa only [zero_add, pow_one, iteratedDeriv_zero, logDeriv_apply,
      pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one] using hbase
  have hshift : Tendsto (fun u : ℂ => u + 1)
      (nhdsWithin p ({p}ᶜ)) (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : ContinuousAt (fun u : ℂ => u + 1) p :=
        continuousAt_id.add_const _
      have hle : nhdsWithin p ({p}ᶜ) ≤ nhds p := inf_le_left
      simpa only [hprho] using hc.tendsto.mono_left hle
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change u + 1 ≠ (rho : ℂ)
      intro heq
      have hup : u ≠ p := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
      apply hup
      linear_combination heq - hprho
  have hcomposed := hbase'.comp hshift
  rw [analyticOrderAt_regularizedRiemannZeta_eq_xi_of_support rho] at hcomposed
  change Tendsto _ _
    (nhds ((analyticOrderAt xi (rho : ℂ)).toNat : ℂ))
  convert hcomposed using 1
  funext u
  rw [Function.comp_apply]
  congr 1
  dsimp only [p] at hprho ⊢
  rw [← hprho]
  ring

/-- The translated logarithmic derivative has an exact simple pole at every Xi divisor point. -/
theorem meromorphicOrderAt_criticalMellin_shiftedLogDeriv_eq_neg_one
    (rho : XiDivisorSupport) :
    meromorphicOrderAt
        (fun u : ℂ => logDeriv regularizedRiemannZeta (u + 1))
        (criticalMellinXiPole rho) = ((-1 : ℤ) : WithTop ℤ) := by
  let p : ℂ := criticalMellinXiPole rho
  have hprho : p + 1 = (rho : ℂ) := by
    simpa only [p] using criticalMellinXiPole_add_one rho
  have hzero : regularizedRiemannZeta (rho : ℂ) = 0 := by
    have h := regularizedRiemannZeta_eq_zero_at_inverseTiltedXiPole rho
    rw [inverseTiltedXiPole] at h
    rw [show (rho : ℂ) + 1 / 2 - 1 / 2 = (rho : ℂ) by ring] at h
    exact h
  let shift : ℂ -> ℂ := fun z => z + 1
  have hshiftAnalytic : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift p ≠ 0 := by
    dsimp only [shift]
    rw [deriv_add_const, deriv_id'']
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := logDeriv regularizedRiemannZeta) (g := shift) (x := p)
    hshiftAnalytic hshiftDeriv
  rw [show shift p = (rho : ℂ) by simpa only [shift] using hprho,
    meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hzero] at hcomp
  simpa only [shift, Function.comp_apply, p] using! hcomp

/-- Every Xi point gives a simple pole of the full regularized critical-Mellin defect. -/
theorem meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one
    (rho : XiDivisorSupport) :
    meromorphicOrderAt regularizedCriticalMellinDefect
        (criticalMellinXiPole rho) = ((-1 : ℤ) : WithTop ℤ) := by
  let p : ℂ := criticalMellinXiPole rho
  let singular : ℂ -> ℂ := fun u =>
    logDeriv regularizedRiemannZeta (u + 1)
  let correction : ℂ -> ℂ := fun u => 1 / (u + 1)
  have hp : -1 < p.re := by
    simpa only [p] using criticalMellinXiPole_re_gt_neg_one rho
  have hden : AnalyticAt ℂ (fun u : ℂ => u + 1) p := by fun_prop
  have hden0 : p + 1 ≠ 0 := by
    rw [show p + 1 = (rho : ℂ) by
      simpa only [p] using criticalMellinXiPole_add_one rho]
    intro hrho
    have hre := congrArg Complex.re hrho
    rw [Complex.zero_re] at hre
    linarith [(xi_divisor_support_re_mem_open_unit rho).1]
  have hcorrection : AnalyticAt ℂ correction p := by
    dsimp only [correction]
    exact analyticAt_const.div hden hden0
  have hsingular : MeromorphicAt singular p := by
    let shift : ℂ -> ℂ := fun u => u + 1
    have hshift : AnalyticAt ℂ shift p := by
      dsimp only [shift]
      fun_prop
    have hcomp := MeromorphicAt.comp_analyticAt
      (f := logDeriv regularizedRiemannZeta) (g := shift)
      (meromorphicAt_logDeriv_regularizedRiemannZeta (shift p)) hshift
    simpa only [singular, shift, Function.comp_apply] using! hcomp
  have hsingularOrder : meromorphicOrderAt singular p =
      ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [singular, p] using
      meromorphicOrderAt_criticalMellin_shiftedLogDeriv_eq_neg_one rho
  have hlt : meromorphicOrderAt singular p <
      meromorphicOrderAt correction p := by
    rw [hsingularOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorrection.meromorphicOrderAt_nonneg
  have hfun : regularizedCriticalMellinDefect = singular + correction := by
    funext u
    simp only [regularizedCriticalMellinDefect, singular, correction, Pi.add_apply]
    ring
  rw [hfun, meromorphicOrderAt_add_eq_left_of_lt hcorrection.meromorphicAt hlt,
    hsingularOrder]

/-- The critical-Mellin residue is the exact analytic multiplicity, with no aperture factor. -/
theorem meromorphicTrailingCoeffAt_regularizedCriticalMellinDefect
    (rho : XiDivisorSupport) :
    meromorphicTrailingCoeffAt regularizedCriticalMellinDefect
        (criticalMellinXiPole rho) =
      (inverseTiltedXiMultiplicity rho : ℂ) := by
  let p : ℂ := criticalMellinXiPole rho
  let singular : ℂ -> ℂ := fun u =>
    logDeriv regularizedRiemannZeta (u + 1)
  let correction : ℂ -> ℂ := fun u => 1 / (u + 1)
  have hden : AnalyticAt ℂ (fun u : ℂ => u + 1) p := by fun_prop
  have hden0 : p + 1 ≠ 0 := by
    rw [show p + 1 = (rho : ℂ) by
      simpa only [p] using criticalMellinXiPole_add_one rho]
    intro hrho
    have hre := congrArg Complex.re hrho
    rw [Complex.zero_re] at hre
    linarith [(xi_divisor_support_re_mem_open_unit rho).1]
  have hcorrection : AnalyticAt ℂ correction p := by
    dsimp only [correction]
    exact analyticAt_const.div hden hden0
  have hsingular : MeromorphicAt singular p := by
    let shift : ℂ -> ℂ := fun u => u + 1
    have hshift : AnalyticAt ℂ shift p := by
      dsimp only [shift]
      fun_prop
    have hcomp := MeromorphicAt.comp_analyticAt
      (f := logDeriv regularizedRiemannZeta) (g := shift)
      (meromorphicAt_logDeriv_regularizedRiemannZeta (shift p)) hshift
    simpa only [singular, shift, Function.comp_apply] using! hcomp
  have hsingularOrder : meromorphicOrderAt singular p =
      ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [singular, p] using
      meromorphicOrderAt_criticalMellin_shiftedLogDeriv_eq_neg_one rho
  have hlt : meromorphicOrderAt singular p <
      meromorphicOrderAt correction p := by
    rw [hsingularOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorrection.meromorphicOrderAt_nonneg
  have hfun : regularizedCriticalMellinDefect = singular + correction := by
    funext u
    simp only [regularizedCriticalMellinDefect, singular, correction, Pi.add_apply]
    ring
  rw [hfun]
  change meromorphicTrailingCoeffAt
      (fun u => singular u + correction u) p =
    (inverseTiltedXiMultiplicity rho : ℂ)
  rw [hcorrection.meromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt hlt]
  have htrail := hsingular.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [hsingularOrder] at htrail
  simp only [WithTop.untop₀_coe, neg_neg, zpow_one, smul_eq_mul] at htrail
  have hres := tendsto_criticalMellin_shiftedLogDeriv_residue rho
  exact tendsto_nhds_unique htrail hres

/-- Every regularized-zeta zero in the natural half-plane comes from the Xi divisor. -/
theorem exists_xiDivisorSupport_of_criticalMellin_regularizedZeta_zero
    {u : ℂ} (hu : -1 < u.re)
    (hzero : regularizedRiemannZeta (u + 1) = 0) :
    ∃ rho : XiDivisorSupport, criticalMellinXiPole rho = u := by
  let s : ℂ := u + 3 / 2
  have hs : 1 / 2 < s.re := by
    dsimp only [s]
    rw [Complex.add_re]
    norm_num
    linarith
  have hzero' : regularizedRiemannZeta (s - 1 / 2) = 0 := by
    dsimp only [s]
    rw [show u + 3 / 2 - 1 / 2 = u + 1 by ring]
    exact hzero
  obtain ⟨rho, hrho⟩ :=
    exists_xiDivisorSupport_of_inverseTilted_regularizedZeta_zero hs hzero'
  refine ⟨rho, ?_⟩
  dsimp only [inverseTiltedXiPole] at hrho
  rw [criticalMellinXiPole]
  dsimp only [s] at hrho
  linear_combination hrho

/-- In the natural half-plane, holomorphy is exactly nonvanishing of the regularized zeta. -/
theorem analyticAt_regularizedCriticalMellinDefect_iff_regularizedZeta_ne_zero
    {u : ℂ} (hu : -1 < u.re) :
    AnalyticAt ℂ regularizedCriticalMellinDefect u ↔
      regularizedRiemannZeta (u + 1) ≠ 0 := by
  constructor
  · intro han hzero
    obtain ⟨rho, hrho⟩ :=
      exists_xiDivisorSupport_of_criticalMellin_regularizedZeta_zero hu hzero
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [← hrho, meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one rho]
      at hnonneg
    have hnot : ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
    exact hnot hnonneg
  · exact analyticAt_regularizedCriticalMellinDefect_of_regularizedZeta_ne_zero hu

/-- The simple-pole support is exactly the affine image of the complete Xi divisor. -/
theorem meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one_iff
    {u : ℂ} (hu : -1 < u.re) :
    meromorphicOrderAt regularizedCriticalMellinDefect u =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ∃ rho : XiDivisorSupport, criticalMellinXiPole rho = u := by
  constructor
  · intro horder
    have hzero : regularizedRiemannZeta (u + 1) = 0 := by
      by_contra hz
      have han :=
        analyticAt_regularizedCriticalMellinDefect_of_regularizedZeta_ne_zero hu hz
      have hnonneg := han.meromorphicOrderAt_nonneg
      rw [horder] at hnonneg
      have hnot : ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
        exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
      exact hnot hnonneg
    exact exists_xiDivisorSupport_of_criticalMellin_regularizedZeta_zero hu hzero
  · rintro ⟨rho, rfl⟩
    exact meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one rho

/-- Complete simple-pole support of the regularized critical-Mellin defect. -/
def criticalMellinSimplePoleSupport : Set ℂ :=
  {u : ℂ | -1 < u.re ∧
    meromorphicOrderAt regularizedCriticalMellinDefect u =
      ((-1 : ℤ) : WithTop ℤ)}

theorem range_criticalMellinXiPole_eq_simplePoleSupport :
    Set.range criticalMellinXiPole = criticalMellinSimplePoleSupport := by
  ext u
  constructor
  · rintro ⟨rho, rfl⟩
    exact ⟨criticalMellinXiPole_re_gt_neg_one rho,
      meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one rho⟩
  · rintro ⟨hu, horder⟩
    exact (meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one_iff hu).mp
      horder

/-- The complete Xi divisor embeds in the critical-Mellin simple-pole support. -/
def criticalMellinXiPoleEmbedding
    (rho : XiDivisorSupport) : criticalMellinSimplePoleSupport :=
  ⟨criticalMellinXiPole rho,
    criticalMellinXiPole_re_gt_neg_one rho,
    meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one rho⟩

theorem criticalMellinXiPole_injective :
    Function.Injective criticalMellinXiPole := by
  intro rho sigma h
  apply Subtype.ext
  dsimp only [criticalMellinXiPole] at h
  linear_combination h

theorem criticalMellinXiPoleEmbedding_bijective :
    Function.Bijective criticalMellinXiPoleEmbedding := by
  constructor
  · intro rho sigma h
    apply criticalMellinXiPole_injective
    exact congrArg Subtype.val h
  · intro u
    have huRange : (u : ℂ) ∈ Set.range criticalMellinXiPole := by
      rw [range_criticalMellinXiPole_eq_simplePoleSupport]
      exact u.property
    obtain ⟨rho, hrho⟩ := huRange
    refine ⟨rho, ?_⟩
    apply Subtype.ext
    exact hrho

/-- Canonical equivalence between the nontrivial Xi divisor and the critical-Mellin poles. -/
noncomputable def criticalMellinXiDivisorEquivSimplePoleSupport :
    XiDivisorSupport ≃ criticalMellinSimplePoleSupport :=
  Equiv.ofBijective criticalMellinXiPoleEmbedding
    criticalMellinXiPoleEmbedding_bijective

theorem criticalMellinXiDivisorEquivSimplePoleSupport_apply
    (rho : XiDivisorSupport) :
    ((criticalMellinXiDivisorEquivSimplePoleSupport rho :
        criticalMellinSimplePoleSupport) : ℂ) = criticalMellinXiPole rho := by
  rfl

/-- RH is exactly concentration of the critical-Mellin pole divisor on its critical line. -/
theorem riemannHypothesis_iff_criticalMellin_poles_on_line :
    RiemannHypothesis ↔
      ∀ u : ℂ, -1 < u.re →
        meromorphicOrderAt regularizedCriticalMellinDefect u =
          ((-1 : ℤ) : WithTop ℤ) → u.re = -1 / 2 := by
  constructor
  · intro hRH u hu horder
    obtain ⟨rho, hrho⟩ :=
      (meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one_iff hu).mp
        horder
    have hsourceLine :=
      riemannHypothesis_iff_inverseTiltedDyadic_poles_on_line.mp hRH
        (inverseTiltedXiPole rho)
        (inverseTiltedXiPole_re_gt_half rho)
        (meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one rho)
    rw [← hrho, criticalMellinXiPole, Complex.sub_re]
    rw [inverseTiltedXiPole, Complex.add_re] at hsourceLine
    norm_num at hsourceLine ⊢
    linarith
  · intro hpoles
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    let u : ℂ := criticalMellinXiPole rho
    have hu : -1 < u.re := criticalMellinXiPole_re_gt_neg_one rho
    have horder : meromorphicOrderAt regularizedCriticalMellinDefect u =
        ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one rho
    have hline := hpoles u hu horder
    dsimp only [u, criticalMellinXiPole, rho] at hline
    rw [Complex.sub_re] at hline
    norm_num at hline
    rw [mem_rightHalf] at hz
    linarith

/-- **Complete critical-Mellin divisor tomography.**  The regularized defect carries the full Xi
divisor with exact multiplicity, and both pole-line concentration and half-plane holomorphy are
equivalent to RH. -/
theorem criticalMellinDivisorTomography_capstone :
    MeromorphicOn regularizedCriticalMellinDefect {u : ℂ | -1 < u.re} ∧
    (∀ u : ℂ, -1 < u.re →
      (AnalyticAt ℂ regularizedCriticalMellinDefect u ↔
        regularizedRiemannZeta (u + 1) ≠ 0)) ∧
    (∀ u : ℂ, -1 < u.re →
      (meromorphicOrderAt regularizedCriticalMellinDefect u =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ∃ rho : XiDivisorSupport, criticalMellinXiPole rho = u)) ∧
    (∀ rho : XiDivisorSupport,
      meromorphicTrailingCoeffAt regularizedCriticalMellinDefect
          (criticalMellinXiPole rho) =
        (inverseTiltedXiMultiplicity rho : ℂ)) ∧
    (RiemannHypothesis ↔
      ∀ u : ℂ, -1 < u.re →
        meromorphicOrderAt regularizedCriticalMellinDefect u =
          ((-1 : ℤ) : WithTop ℤ) → u.re = -1 / 2) ∧
    (RiemannHypothesis ↔
      ∀ u : ℂ, -1 / 2 < u.re →
        AnalyticAt ℂ regularizedCriticalMellinDefect u) := by
  exact ⟨meromorphicOn_regularizedCriticalMellinDefect_rightNegOne,
    fun _ hu => analyticAt_regularizedCriticalMellinDefect_iff_regularizedZeta_ne_zero hu,
    fun _ hu => meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one_iff hu,
    meromorphicTrailingCoeffAt_regularizedCriticalMellinDefect,
    riemannHypothesis_iff_criticalMellin_poles_on_line,
    riemannHypothesis_iff_regularizedCriticalMellinDefect_analytic_rightNegHalf⟩

end

end RHTower
