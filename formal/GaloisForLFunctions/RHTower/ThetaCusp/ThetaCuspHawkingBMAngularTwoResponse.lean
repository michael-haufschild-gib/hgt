import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularAssembly
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularReconstruction

/-!
# The complete squared-source angular inverse at shift two

The explicit cusp principal response and its differential cutoff leave a globally smooth modular
L² forcing. The coercive inverse on the original energy domain constructs its unique correction.
Restoring the principal field gives a modular distributional solution of `(2-Delta)U=S²` for the
literal completed-Eisenstein scalar at every Xi occurrence, without an L² premise on `S²`.

The final tested equation uses the actual full hyperbolic Laplacian, arbitrary compact chart tests,
and the entire original source. Every cutoff derivative and modular seam is retained. This leaf
establishes a distributional inverse; smooth representative and tensor-source reconstruction are
separate statements.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped MatrixGroups ContDiff ComplexConjugate
namespace RHTower.D4BMAngularTwo
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMQuadraticMixedSource D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The complete squared-cusp principal response at angular shift two. -/
def cuspResponse (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  cuspPowerResponse 2 (q.1 : ℂ)
    (d4BMCompletedEisensteinCuspConstantCoefficient (D4BMGlobalAngularResponse.center q) true)
    (d4BMCompletedEisensteinCuspConstantCoefficient (D4BMGlobalAngularResponse.center q) false) z

/-- The full principal response cut off below the original cusp transition. -/
def cutoffResponse (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  cutoff z*cuspResponse q z

/-- The original full scalar-square forcing after the exact differential cutoff subtraction. -/
def forcing (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  (1 : ℂ)*scalar (D4BMGlobalAngularResponse.center q) z^(2 : ℕ) -
    (hyperbolicLaplacian (cutoffResponse q) z - (2 : ℂ)*cutoffResponse q z)

private theorem principal_center (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q) z =
      d4BMCompletedEisensteinCuspConstantCoefficient (D4BMGlobalAngularResponse.center q) true*(z 1 : ℂ)^(q.1 : ℂ) +
      d4BMCompletedEisensteinCuspConstantCoefficient (D4BMGlobalAngularResponse.center q) false*(z 1 : ℂ)^(1-(q.1 : ℂ)) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent (D4BMGlobalAngularResponse.center q) false = 1-(q.1 : ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign, D4BMGlobalAngularResponse.center]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent (D4BMGlobalAngularResponse.center q) true = (q.1 : ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign, D4BMGlobalAngularResponse.center]
  simp only [D4BMGlobalAngularResponse.principal, d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm, d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one, hm,hp]
  exact add_comm _ _

/-- None of the three original squared cusp powers is resonant at the angular shift two. -/
private theorem cusp_two_denominators (q : XiZeroCopy) :
    (2*(q.1 : ℂ))*(2*(q.1 : ℂ)-1)-2 ≠ 0 ∧
      (2-2*(q.1 : ℂ))*(1-2*(q.1 : ℂ))-2 ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have hlinear (a b : ℝ) (ha : a ≠ 0) : (a : ℂ)*(q.1 : ℂ)+(b : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    norm_num [Complex.mul_im] at hh
    exact hi (hh.resolve_left ha)
  have hq : (q.1 : ℂ) ≠ 0 := by simpa using hlinear 1 0 (by norm_num)
  have hm : (q.1 : ℂ)-1 ≠ 0 := by simpa only [Complex.ofReal_one,one_mul,Complex.ofReal_neg,sub_eq_add_neg] using hlinear 1 (-1) (by norm_num)
  have hp : 2*(q.1 : ℂ)+1 ≠ 0 := by simpa using hlinear 2 1 (by norm_num)
  have ht : 2*(q.1 : ℂ)-3 ≠ 0 := by simpa [sub_eq_add_neg] using hlinear 2 (-3) (by norm_num)
  constructor
  · rw [show (2*(q.1 : ℂ))*(2*(q.1 : ℂ)-1)-2 =
      2*((q.1 : ℂ)-1)*(2*(q.1 : ℂ)+1) by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm) hp
  · rw [show (2-2*(q.1 : ℂ))*(1-2*(q.1 : ℂ))-2 =
      2*(q.1 : ℂ)*(2*(q.1 : ℂ)-3) by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hq) ht

/-- The explicit cusp response has exactly the original full principal-part forcing. -/
theorem cuspResponse_equation (q : XiZeroCopy)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (cuspResponse q) z -
      (2 : ℂ)*cuspResponse q z =
      (1)*D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q) z^(2 : ℕ) := by
  rw [principal_center]
  unfold cuspResponse
  obtain ⟨h0,h2⟩ := cusp_two_denominators q
  simpa only [one_mul] using cusp_response_equation 2 (q.1 : ℂ)
    (d4BMCompletedEisensteinCuspConstantCoefficient (D4BMGlobalAngularResponse.center q) true)
    (d4BMCompletedEisensteinCuspConstantCoefficient (D4BMGlobalAngularResponse.center q) false)
    z hz h0 (by norm_num) h2

private theorem cuspResponse_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (cuspResponse q) domain := by
  unfold cuspResponse cuspPowerResponse powerResponse
  exact ((contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)).add
    (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞))).add
    (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞))

private theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    (Y.contDiff.sub contDiff_const))

private theorem cutoffResponse_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (cutoffResponse q) domain :=
  cutoff_smooth.contDiffOn.mul (cuspResponse_smooth q)

private theorem laplacian_continuous {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiffOn ℝ 2 f domain) : ContinuousOn (hyperbolicLaplacian f) domain := by
  intro z hz
  have hfo : ContDiffAt ℝ 2 f z := hf.contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
  have hd (i : Fin 2) : ContDiffAt ℝ 1 (coordDeriv i f) z :=
    (hfo.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hdd (i : Fin 2) : ContinuousAt (coordDeriv i (coordDeriv i f)) z :=
    (((hd i).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  exact (((Complex.ofRealCLM.continuous.continuousAt.comp (continuous_apply 1).continuousAt).pow 2).mul
    ((hdd 0).add (hdd 1))).continuousWithinAt

/-- The full residual is continuous on the whole positive-height chart. -/
theorem forcing_continuousOn (q : XiZeroCopy) :
    ContinuousOn (forcing q) domain := by
  have hr := cutoffResponse_smooth q
  have hl := laplacian_continuous ((contDiffOn_infty.mp hr) 2)
  exact (continuousOn_const.mul ((cuspLeg_contDiffOn .scalar (D4BMGlobalAngularResponse.center q)).continuousOn.pow 2)).sub
    (hl.sub (continuousOn_const.mul hr.continuousOn))

/-- The cutoff response vanishes on a neighborhood of the entire compact modular seam. -/
theorem cutoffResponse_zero (q : XiZeroCopy)
    (z : Fin 2 → ℝ) (hz : z 1 ≤ 2) : cutoffResponse q z = 0 := by
  unfold cutoffResponse cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

/-- Above the transition region, the actual residual is precisely the full squared-source
remainder, with the physical forcing amplitude retained. -/
theorem forcing_high (q : XiZeroCopy)
    (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    forcing q z = (1)*squareRemainder (D4BMGlobalAngularResponse.center q) z := by
  have he : cutoffResponse q =ᶠ[𝓝 z] cuspResponse q := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    unfold cutoffResponse cutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  rw [forcing, hyperbolicLaplacian_congr he, he.eq_of_nhds,
    cuspResponse_equation q z (by linarith)]
  dsimp [squareRemainder]
  ring

private theorem coordinates_continuous : Continuous coordinates := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

/-- The full residual is bounded on the entire standard modular cell, including its cusp. -/
theorem forcing_bounded (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ ModularGroup.fd →
      ‖forcing q (coordinates z)‖ ≤ C := by
  obtain ⟨B,hB,hb⟩ := squareRemainder_bounded (D4BMGlobalAngularResponse.center q) (1/2) (by norm_num)
  let lo : Fin 2 → ℝ := ![-1/2,1/2]
  let hi : Fin 2 → ℝ := ![1/2,4]
  have hc : ContinuousOn (forcing q) (Icc lo hi) :=
    (forcing_continuousOn q).mono (by
      intro z hz
      have hh := hz.1 1
      change (1/2 : ℝ) ≤ z 1 at hh
      change 0 < z 1
      linarith)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C (‖(1 : ℂ)‖*B),
    le_trans (mul_nonneg (norm_nonneg _) hB) (le_max_right _ _), ?_⟩
  intro z hz
  have hre := abs_le.mp hz.2
  have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have him : (1/2 : ℝ) ≤ z.im := by nlinarith [z.im_pos]
  by_cases hh : 4 ≤ z.im
  · rw [forcing_high q (coordinates z) (by change 3 < z.im; linarith),norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb (coordinates z) him) (norm_nonneg _)).trans (le_max_right _ _)
  · apply (hC (coordinates z) ?_).trans (le_max_left _ _)
    constructor
    · intro i
      fin_cases i
      · simpa [lo, coordinates, neg_div] using hre.1
      · exact him
    · intro i
      fin_cases i
      · exact hre.2
      · exact le_of_not_ge hh

/-- The entire physical residual belongs to the actual modular hyperbolic L² space,
for every Xi occurrence, with no spectral-location hypothesis. -/
theorem forcing_memLp (q : XiZeroCopy) :
    MemLp (fun z : UpperHalfPlane => forcing q (coordinates z)) 2 angularMeasure := by
  have hc : Continuous (fun z : UpperHalfPlane => forcing q (coordinates z)) :=
    (forcing_continuousOn q).comp_continuous coordinates_continuous
      (fun z => z.im_pos)
  obtain ⟨C,_,hC⟩ := forcing_bounded q
  apply MemLp.of_bound hc.aestronglyMeasurable C
  exact (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet).mono hC

/-- The admitted full forcing as a vector in the actual angular Hilbert space. -/
def forcingVector (q : XiZeroCopy) : Lp ℂ 2 angularMeasure :=
  (forcing_memLp q).toLp (fun z => forcing q (coordinates z))

/-- The Hilbert-space vector retains the original full differential residual almost everywhere. -/
theorem forcingVector_coe (q : XiZeroCopy) :
    (forcingVector q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      (fun z => forcing q (coordinates z)) :=
  (forcing_memLp q).coeFn_toLp
private theorem cutoffResponse_chartSmooth (q : XiZeroCopy) :
    ChartSmooth (fun z => cutoffResponse q (coordinates z)) := by
  have hC : ContDiff ℝ ∞ (fun z : ℂ => ![z.re,z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have hf : ContDiffOn ℝ ∞ (fun z : ℂ => cutoffResponse q ![z.re,z.im])
      {z : ℂ | 0 < z.im} :=
    (cutoffResponse_smooth q).comp hC.contDiffOn (fun _ hz => hz)
  intro z
  apply (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw]
  rfl

private theorem cutoffResponse_cell_germ (q : XiZeroCopy) :
    CellGermCompatible (fun z => cutoffResponse q (coordinates z)) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      change cutoffResponse q (coordinates (A • w)) = cutoffResponse q (coordinates w)
      rw [hn]
      simp only [coordinates,cutoffResponse,cutoff,cuspResponse,cuspPowerResponse,powerResponse,
        Matrix.cons_val_one,ModularGroup.im_T_zpow_smul]
    · obtain ⟨hl,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hγ
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp
          (show Continuous (fun w : UpperHalfPlane => A • w) from by
            simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      rw [cutoffResponse_zero q _ hAw.le,cutoffResponse_zero q _ hw.le]

/-- The globally glued original cusp cutoff response, retaining its complete closed-cell germs. -/
def globalCuspCutoff (q : XiZeroCopy) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => cutoffResponse q (coordinates z))

/-- The original cusp cutoff extends to a globally smooth upper-half-plane field. -/
theorem globalCuspCutoff_smooth (q : XiZeroCopy) :
    ChartSmooth (globalCuspCutoff q) :=
  cellGermExtension_smooth _ (cutoffResponse_cell_germ q) (cutoffResponse_chartSmooth q)

/-- The constructed global cusp cutoff is invariant under every actual modular element. -/
theorem globalCuspCutoff_invariant (q : XiZeroCopy) (γ : PSL2Z)
    (z : UpperHalfPlane) : globalCuspCutoff q (γ • z) = globalCuspCutoff q z :=
  cellGermExtension_invariant _ (cutoffResponse_cell_germ q) γ z

/-- Full germ agreement preserves every cutoff derivative in each closed-cell chart. -/
theorem globalCuspCutoff_germ (q : XiZeroCopy) (z : UpperHalfPlane)
    (hz : z ∈ fd) : globalCuspCutoff q =ᶠ[𝓝 z]
      (fun w => cutoffResponse q (coordinates w)) :=
  cellGermExtension_germ _ (cutoffResponse_cell_germ q) z hz

/-- The global cusp cutoff equals the original full cutoff response on the closed modular cell. -/
theorem globalCuspCutoff_eq_on_fd (q : XiZeroCopy) (z : UpperHalfPlane)
    (hz : z ∈ fd) : globalCuspCutoff q z = cutoffResponse q (coordinates z) :=
  (globalCuspCutoff_germ q z hz).eq_of_nhds

/-- The native energy equation for the actual full residual at angular shift two. -/
def WeakSolution (q : XiZeroCopy) (h : energyDomain) : Prop :=
  ∀ v : energyDomain,
    (∑ i : Fin 2, inner ℂ ((v : EnergySpace) i.succ) ((h : EnergySpace) i.succ)) +
      2*inner ℂ (embedding v) (embedding h) = inner ℂ (embedding v) (forcingVector q)

/-- The complete original cusp-subtracted source has a unique native energy response. -/
theorem exists_unique_weakResponse (q : XiZeroCopy) :
    ∃! h : energyDomain, WeakSolution q h :=
  exists_unique_angular_reconstruction (forcingVector q)

/-- The unique energy response to the original complete residual. -/
def weakResponse (q : XiZeroCopy) : energyDomain :=
  (exists_unique_weakResponse q).exists.choose

theorem weakResponse_spec (q : XiZeroCopy) : WeakSolution q (weakResponse q) :=
  (exists_unique_weakResponse q).exists.choose_spec

theorem weakResponse_norm_le (q : XiZeroCopy) :
    ‖weakResponse q‖ ≤ ‖forcingVector q‖/2 :=
  angular_reconstruction_norm_le _ _ (weakResponse_spec q)

private theorem scalar_chartSmooth (q : XiZeroCopy) :
    ChartSmooth (fun z => scalar (D4BMGlobalAngularResponse.center q) (coordinates z)) := by
  have hC : ContDiff ℝ ∞ (fun z : ℂ => ![z.re,z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have hf : ContDiffOn ℝ ∞ (fun z : ℂ => scalar (D4BMGlobalAngularResponse.center q) ![z.re,z.im])
      {z : ℂ | 0 < z.im} :=
    (cuspLeg_contDiffOn .scalar (D4BMGlobalAngularResponse.center q)).comp hC.contDiffOn
      (fun _ hz => hz)
  intro z
  apply (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw]
  rfl

private theorem chartLaplacian_smooth (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f) :
    ChartSmooth (chartLaplacian f) := by
  have hl := planarLaplacian_contDiffOn hf.planar_contDiffOn
  have h : ContDiffOn ℝ ∞ (fun z : ℂ => (z.im : ℂ)^(2 : ℕ)*planarLaplacian (f ∘ ofComplex) z)
      {z : ℂ | 0 < z.im} :=
    ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow 2).contDiffOn.mul hl
  intro z
  apply (h.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [chartLaplacian,Function.comp_apply,ofComplex_apply_of_im_pos hw]
  rfl

/-- The original full forcing expressed globally, with every cusp-cutoff derivative retained. -/
def globalForcing (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  scalar (D4BMGlobalAngularResponse.center q) (coordinates z)^(2 : ℕ) -
    (chartLaplacian (globalCuspCutoff q) z-2*globalCuspCutoff q z)

/-- The global expression agrees with the admitted original residual on the entire closed cell. -/
theorem globalForcing_eq_on_fd (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    globalForcing q z = forcing q (coordinates z) := by
  rw [globalForcing,chartLaplacian_congr (globalCuspCutoff_germ q z hz),
    chartLaplacian_coordinates,globalCuspCutoff_eq_on_fd q z hz]
  simp only [forcing,one_mul]

/-- The full residual is globally smooth, including modular seams and elliptic corners. -/
theorem globalForcing_smooth (q : XiZeroCopy) : ChartSmooth (globalForcing q) := by
  intro z
  exact ((scalar_chartSmooth q z).pow 2).sub
    ((chartLaplacian_smooth _ (globalCuspCutoff_smooth q) z).sub
      (contDiffAt_const.mul (globalCuspCutoff_smooth q z)))

/-- The actual global forcing is modular invariant before its Hilbert-space interpretation. -/
theorem globalForcing_invariant (q : XiZeroCopy) (γ : PSL2Z) (z : UpperHalfPlane) :
    globalForcing q (γ • z) = globalForcing q z := by
  have hD := chartLaplacian_invariant _ (globalCuspCutoff_smooth q)
    (globalCuspCutoff_invariant q) γ z
  unfold globalForcing
  rw [hD,globalCuspCutoff_invariant]
  congr 2
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul]
    exact xi_scalar_modular q A z

/-- The smooth global residual represents the actual admitted source vector. -/
theorem globalForcing_native_ae (q : XiZeroCopy) :
    globalForcing q =ᵐ[measure] (forcingVector q : UpperHalfPlane → ℂ) := by
  filter_upwards [ae_mem_interior,forcingVector_coe q] with z hz he
  rw [globalForcing_eq_on_fd q z (fdo_subset_fd hz),he]

/-- The globally smooth source equals the original modular lift of its admitted L² vector. -/
theorem globalForcing_ae_lift (q : XiZeroCopy) :
    globalForcing q =ᵐ[(volume : Measure UpperHalfPlane)] globalLift (forcingVector q) := by
  have he : globalForcing q =ᵐ[measure] globalLift (forcingVector q) :=
    (globalForcing_native_ae q).trans (globalLift_ae_eq _).symm
  have hn : ∀ᵐ z : UpperHalfPlane ∂volume,
      z ∈ fd → globalForcing q z = globalLift (forcingVector q) z :=
    (ae_restrict_iff' isClosed_fd.measurableSet).mp he
  have ht (γ : PSL2Z) : ∀ᵐ z : UpperHalfPlane ∂volume,
      γ • z ∈ fd → globalForcing q z = globalLift (forcingVector q) z := by
    have hh := (measurePreserving_smul γ (volume : Measure UpperHalfPlane)).quasiMeasurePreserving.ae hn
    filter_upwards [hh] with z hz hmem
    simpa only [globalForcing_invariant q γ z,globalLift_invariant (forcingVector q) γ z] using hz hmem
  have hall := ae_all_iff.mpr ht
  filter_upwards [hall] with z hz
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  exact hz (QuotientGroup.mk A) (by simpa only [PSL2Z_mk_smul] using hA)

/-- The constructed shift-two correction obeys the original equation against all modular chart tests. -/
theorem weakResponse_distribution_equation (q : XiZeroCopy) (g : PlanarChartTest) :
    inner ℂ g.laplaceVector (embedding (weakResponse q)) -
      2*inner ℂ (embedding g.toChartTest.energyTest) (embedding (weakResponse q)) =
      -inner ℂ (embedding g.toChartTest.energyTest) (forcingVector q) := by
  have he := weakResponse_spec q g.toChartTest.energyTest
  rw [g.completed_green] at he
  linear_combination -he

/-- The native equation unfolds over the full half-plane with its actual original source. -/
theorem weakResponse_lifted_equation (q : XiZeroCopy) (g : PlanarChartTest) :
    (∫ z : UpperHalfPlane, conj (g.laplaceTest.field z)*globalLift (embedding (weakResponse q)) z) -
      2*(∫ z : UpperHalfPlane, conj (g.field z)*globalLift (embedding (weakResponse q)) z) =
      -(∫ z : UpperHalfPlane, conj (g.field z)*globalForcing q z) := by
  have he := weakResponse_distribution_equation q g
  rw [PlanarChartTest.laplaceVector,g.laplaceTest.lift_pairing,g.lift_pairing,g.lift_pairing] at he
  rw [he]
  congr 1
  apply integral_congr_ae
  filter_upwards [globalForcing_ae_lift q] with z hz
  rw [hz]

/-- The entire original scalar-square source is restored in the weak equation.
The native response is tested distributionally; the smooth cutoff uses its actual Laplacian. -/
theorem full_source_tested_identity (q : XiZeroCopy) (g : PlanarChartTest) :
    (∫ z : UpperHalfPlane, conj (g.laplaceTest.field z)*globalLift (embedding (weakResponse q)) z) -
      2*(∫ z : UpperHalfPlane, conj (g.field z)*globalLift (embedding (weakResponse q)) z) =
      -(∫ z : UpperHalfPlane, conj (g.field z)*
        (scalar (D4BMGlobalAngularResponse.center q) (coordinates z)^(2 : ℕ) -
          (chartLaplacian (globalCuspCutoff q) z-2*globalCuspCutoff q z))) :=
  weakResponse_lifted_equation q g

/-- The complete angular response retains the full principal field and its native correction. -/
def fullResponse (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  globalLift (embedding (weakResponse q)) z-globalCuspCutoff q z

theorem fullResponse_invariant (q : XiZeroCopy) (γ : PSL2Z) (z : UpperHalfPlane) :
    fullResponse q (γ • z) = fullResponse q z := by
  simp only [fullResponse,globalLift_invariant,globalCuspCutoff_invariant]

/-- Removing the explicit principal response recovers the actual finite-energy correction. -/
theorem fullResponse_renormalized_native (q : XiZeroCopy) :
    (fun z => fullResponse q z+globalCuspCutoff q z) =ᵐ[measure] embedding (weakResponse q) := by
  simpa only [fullResponse,sub_add_cancel] using globalLift_ae_eq (embedding (weakResponse q))

private theorem compact_pair_integrable (g : PlanarChartTest)
    (h : UpperHalfPlane → ℂ) (hh : ChartSmooth h) :
    Integrable (fun z : UpperHalfPlane => conj (g.field z)*h z) (volume : Measure UpperHalfPlane) := by
  have hc := (Complex.conjCLE.continuous.comp (ChartSmooth.continuous g.toChartTest.smooth)).mul
    (ChartSmooth.continuous hh)
  have hk : HasCompactSupport (fun z : UpperHalfPlane => conj (g.field z)) :=
    g.toChartTest.compact.comp_left (by simp)
  exact hc.integrable_of_hasCompactSupport hk.mul_right

private theorem planar_height_pairing (g : PlanarChartTest) (F : ℂ → ℂ) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*(g.field z*F z)) =
      ∫ z : ℂ, g.field z*F z := by
  rw [integral_volume_height_sq_chart (fun z : ℂ => g.field z*F z)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hn : z ∉ tsupport g.field := fun hg => hz (g.support hg)
  simp [image_eq_zero_of_notMem_tsupport hn]

private theorem chart_green (g : PlanarChartTest) (h : UpperHalfPlane → ℂ)
    (hh : ChartSmooth h) :
    (∫ z : UpperHalfPlane, conj (g.laplaceTest.field z)*h z) =
      ∫ z : UpperHalfPlane, conj (g.field z)*chartLaplacian h z := by
  have hL : (∫ z : UpperHalfPlane, conj (g.laplaceTest.field z)*h z) =
      ∫ z : ℂ, g.conjugate.laplacianTest.field z*(h ∘ ofComplex) z := by
    calc
      _ = ∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*
          (g.conjugate.laplacianTest.field z*(h ∘ ofComplex) z) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [← g.laplace_conjugate,g.conjugate.laplaceTest_field]
        simp only [Function.comp_apply,ofComplex_apply,coe_im]
        change ((z.im : ℂ)^(2 : ℕ)*g.conjugate.laplacianTest.field z)*h z = _
        ring
      _ = _ := planar_height_pairing _ _
  rw [hL,g.conjugate.laplacian_green _ hh.planar_contDiffOn]
  rw [← planar_height_pairing g.conjugate (planarLaplacian (h ∘ ofComplex))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [chartLaplacian,PlanarChartTest.conjugate]
  ring

/-- The full original angular inverse exists distributionally at shift two.
All compact test integrals are admitted, all modular seams are retained, and the full
literal squared source is restored without an L² premise on that source itself. -/
theorem fullResponse_distribution_equation (q : XiZeroCopy) (g : PlanarChartTest) :
    (∫ z : UpperHalfPlane, conj (g.laplaceTest.field z)*fullResponse q z) -
      2*(∫ z : UpperHalfPlane, conj (g.field z)*fullResponse q z) =
      -(∫ z : UpperHalfPlane, conj (g.field z)*
        scalar (D4BMGlobalAngularResponse.center q) (coordinates z)^(2 : ℕ)) := by
  have hW (a : PlanarChartTest) : Integrable (fun z : UpperHalfPlane =>
      conj (a.field z)*globalLift (embedding (weakResponse q)) z) volume :=
    compact_chart_mul_lift_integrable a.conjugate.toChartTest _
  have hK (a : PlanarChartTest) := compact_pair_integrable a _ (globalCuspCutoff_smooth q)
  have hD := compact_pair_integrable g _ (chartLaplacian_smooth _ (globalCuspCutoff_smooth q))
  have hS := compact_pair_integrable g
    (fun z => scalar (D4BMGlobalAngularResponse.center q) (coordinates z)^(2 : ℕ))
    (fun z => (scalar_chartSmooth q z).pow 2)
  have hG : (∫ z : UpperHalfPlane, conj (g.field z)*globalForcing q z) =
      (∫ z : UpperHalfPlane, conj (g.field z)*
        scalar (D4BMGlobalAngularResponse.center q) (coordinates z)^(2 : ℕ)) -
      (∫ z : UpperHalfPlane, conj (g.field z)*chartLaplacian (globalCuspCutoff q) z) +
      2*(∫ z : UpperHalfPlane, conj (g.field z)*globalCuspCutoff q z) := by
    calc
      _ = ∫ z : UpperHalfPlane,
          (conj (g.field z)*scalar (D4BMGlobalAngularResponse.center q) (coordinates z)^(2 : ℕ) -
            conj (g.field z)*chartLaplacian (globalCuspCutoff q) z) +
          2*(conj (g.field z)*globalCuspCutoff q z) := by
        apply integral_congr_ae
        filter_upwards [] with z
        unfold globalForcing
        ring
      _ = _ := by
        have hadd := integral_add (hS.sub hD) ((hK g).const_mul 2)
        simp only [Pi.sub_apply] at hadd
        rw [hadd,integral_sub hS hD,integral_const_mul]
  have he := weakResponse_lifted_equation q g
  rw [hG] at he
  simp only [fullResponse,mul_sub]
  rw [integral_sub (hW g.laplaceTest) (hK g.laplaceTest),integral_sub (hW g) (hK g),
    chart_green g _ (globalCuspCutoff_smooth q)]
  linear_combination he

end
end RHTower.D4BMAngularTwo
