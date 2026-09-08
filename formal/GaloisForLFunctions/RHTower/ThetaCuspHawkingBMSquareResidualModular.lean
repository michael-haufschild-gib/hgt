import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCellGermExtension
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPeriodization
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteAngularSourceProjection

/-! The original half-square residual has an actual smooth modular extension. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

private theorem residual_low (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z.im < 2) :
    squareResidual q (coordinates z) = fullSquarePotential q (coordinates z) := by
  unfold squareResidual cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by change z.im-2 ≤ 0; linarith)]
  simp

/-- Integer translations preserve the literal residual before modular gluing. -/
theorem squareResidual_translate (q : XiZeroCopy) (n : ℤ) (z : UpperHalfPlane) :
    squareResidual q (coordinates (T^n • z)) = squareResidual q (coordinates z) := by
  simp only [squareResidual,fullSquarePotential,xi_scalar_modular]
  congr 1
  simp only [cutoff,principalSquare,D4BMGlobalAngularResponse.principal,
    d4BMCompletedEisensteinCuspConstantPart,d4BMCompletedEisensteinCuspConstantTerm,
    d4BMCompletedEisensteinCuspConstantMaassFactor,coordinates,ModularGroup.im_T_zpow_smul]
  rfl

/-- Every closed-cell overlap preserves the full original residual germ. -/
theorem squareResidual_cell_compatible (q : XiZeroCopy) :
    CellGermCompatible (fun z => squareResidual q (coordinates z)) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      dsimp only
      rw [hn]
      exact squareResidual_translate q n w
    · obtain ⟨hl,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hγ
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp (show Continuous (fun w : UpperHalfPlane => A • w) from by
          simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      rw [residual_low q _ hAw,residual_low q _ hw]
      simp only [fullSquarePotential,xi_scalar_modular]

private theorem residual_chartSmooth (q : XiZeroCopy) :
    ChartSmooth (fun z => squareResidual q (coordinates z)) := by
  have hs := cuspLeg_contDiffOn .scalar (center q)
  have hR : ContDiffOn ℝ ∞ (squareResidual q) domain :=
    (contDiffOn_const.mul (hs.mul hs)).sub
      (sourceCutoff_smooth.contDiffOn.mul (principalSquare_smooth q))
  have hc : ContDiff ℝ ∞ (fun w : ℂ => (![w.re,w.im] : Fin 2 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  intro z
  have hf := hR.contDiffAt
    ((isOpen_lt (continuous_const : Continuous (fun _ : Fin 2 → ℝ => (0:ℝ)))
      (continuous_apply 1)).mem_nhds (show coordinates z ∈ domain from z.im_pos))
  apply (hf.comp (z:ℂ) hc.contDiffAt).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_def,coordinates,ofComplex_apply_of_im_pos hw]
  rfl

/-- The actual source extended by compatible full closed-cell germs. -/
def globalSquareResidual (q : XiZeroCopy) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => squareResidual q (coordinates z))

theorem globalSquareResidual_eq_on_fd (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    globalSquareResidual q z = squareResidual q (coordinates z) := by
  simpa only [one_smul,globalSquareResidual] using
    cellGermExtension_eq _ (squareResidual_cell_compatible q) 1 z (by simpa using hz)

theorem globalSquareResidual_invariant (q : XiZeroCopy) (γ : PSL2Z) (z : UpperHalfPlane) :
    globalSquareResidual q (γ • z) = globalSquareResidual q z :=
  cellGermExtension_invariant _ (squareResidual_cell_compatible q) γ z

theorem globalSquareResidual_smooth (q : XiZeroCopy) : ChartSmooth (globalSquareResidual q) :=
  cellGermExtension_smooth _ (squareResidual_cell_compatible q) (residual_chartSmooth q)

/-- The original noncompact height subtraction, with its literal translation partition. -/
def squareCutoffSeed (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  (cuspWindow z.re : ℂ)*(cutoff ![0,z.im]*principalSquare q ![0,z.im])

/-- The complete periodization is exactly the original subtraction on the closed cell. -/
theorem squareCutoffSeed_periodize_cell (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    periodize (squareCutoffSeed q) z = cutoff (coordinates z)*principalSquare q (coordinates z) := by
  refine periodize_cuspWindow (fun y : ℝ => cutoff ![0,y]*principalSquare q ![0,y]) ?_ z hz
  intro y hy
  unfold cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by change y-2 ≤ 0; linarith)]
  simp

/-- The source's global extension is its full scalar square minus the full cutoff orbit sum. -/
theorem globalSquareResidual_eq_periodized (q : XiZeroCopy) (z : UpperHalfPlane) :
    globalSquareResidual q z = fullSquarePotential q (coordinates z)-periodize (squareCutoffSeed q) z := by
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have hi := globalSquareResidual_invariant q (QuotientGroup.mk A) z
  have hp := periodize_invariant (squareCutoffSeed q) (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hi hp
  rw [← hi,globalSquareResidual_eq_on_fd q _ hA,squareResidual,
    ← squareCutoffSeed_periodize_cell q _ hA,hp]
  simp only [fullSquarePotential,xi_scalar_modular]

/-- The original native period equals the integral of the constructed global source. -/
theorem scalarResidualPeriod_eq_global (q : XiZeroCopy) (u : ℂ) :
    scalarResidualPeriod q u =
      ∫ z : UpperHalfPlane in fd, scalar u (coordinates z)*globalSquareResidual q z := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with z hz
  rw [globalSquareResidual_eq_on_fd q z hz]

end
end RHTower.D4BMJointSource
