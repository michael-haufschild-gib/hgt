import GaloisForLFunctions.RHTower.SelbergScatteringSourceVector
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullCoreOperator
import GaloisForLFunctions.HTGeometry.SmoothWeight
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Compact modular approximation of the complete original source

The existing smooth height cutoff is glued across all modular seams and elliptic
points. Multiplication retains the complete corrected Xi source and constructs
actual native operator-domain approximants. They converge in the original L2
norm and eventually retain the source germ at each fixed cell point. Convergence
of their operator images in Hilbert norm remains a separate obligation.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.SelbergScatteringSourceApproximation
open D4BMModularCore D4BMGlobalAngularResponse
open SelbergScatteringCuspSubtraction SelbergScatteringSourceVector
noncomputable section

def cutoffHeight (n : ℕ) : ℝ := n + 3

private theorem cutoffHeight_ge_three (n : ℕ) : 3 ≤ cutoffHeight n := by
  unfold cutoffHeight
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

private theorem cutoffHeight_pos (n : ℕ) : 0 < cutoffHeight n :=
  lt_of_lt_of_le (by norm_num) (cutoffHeight_ge_three n)

def heightWeight (n : ℕ) (y : ℝ) : ℝ := smoothWeight (cutoffHeight n) (cutoffHeight n) y

theorem heightWeight_one (n : ℕ) (y : ℝ) (hy : y ≤ cutoffHeight n) : heightWeight n y = 1 :=
  smoothWeight_eq_one (cutoffHeight_pos n) hy

theorem heightWeight_zero (n : ℕ) (y : ℝ) (hy : 2*cutoffHeight n ≤ y) : heightWeight n y = 0 := by
  apply smoothWeight_eq_zero (cutoffHeight_pos n)
  linarith

private theorem heightWeight_cell_compatible (n : ℕ) :
    CellGermCompatible (fun z => (heightWeight n z.im : ℂ)) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨j,hj⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      dsimp only
      rw [hj,ModularGroup.im_T_zpow_smul]
    · obtain ⟨hl,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hγ
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp (show Continuous (fun w : UpperHalfPlane => A • w) from by
          simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      have hn := cutoffHeight_ge_three n
      rw [heightWeight_one n _ (by linarith),heightWeight_one n _ (by linarith)]

private theorem heightWeight_chartSmooth (n : ℕ) :
    ChartSmooth (fun z => (heightWeight n z.im : ℂ)) := by
  have hs : ContDiff ℝ ∞ (fun w : ℂ => (heightWeight n w.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((smoothWeight_contDiff _ _).comp Complex.imCLM.contDiff)
  intro z
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_def,ofComplex_apply_of_im_pos hw]
  rfl

/-- The expanding height cutoff, smoothly glued on the actual modular quotient. -/
def modularCutoff (n : ℕ) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => (heightWeight n z.im : ℂ))

theorem modularCutoff_eq_on_fd (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) :
    modularCutoff n z = (heightWeight n z.im : ℂ) := by
  simpa only [one_smul,modularCutoff] using
    cellGermExtension_eq _ (heightWeight_cell_compatible n) 1 z (by simpa using hz)

theorem modularCutoff_germ (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) :
    modularCutoff n =ᶠ[𝓝 z] (fun w => (heightWeight n w.im : ℂ)) :=
  cellGermExtension_germ _ (heightWeight_cell_compatible n) z hz

theorem modularCutoff_invariant (n : ℕ) (γ : PSL2Z) (z : UpperHalfPlane) :
    modularCutoff n (γ • z) = modularCutoff n z :=
  cellGermExtension_invariant _ (heightWeight_cell_compatible n) γ z

theorem modularCutoff_smooth (n : ℕ) : ChartSmooth (modularCutoff n) :=
  cellGermExtension_smooth _ (heightWeight_cell_compatible n) (heightWeight_chartSmooth n)

theorem modularCutoff_compact (n : ℕ) : CellCompact (modularCutoff n) := by
  refine ⟨{z : UpperHalfPlane | z ∈ fd ∧ z.im ≤ 2*cutoffHeight n},truncated_cell_compact _,?_⟩
  intro z hz hn
  have hy : 2*cutoffHeight n ≤ z.im := by
    have : ¬ z.im ≤ 2*cutoffHeight n := fun h => hn ⟨hz,h⟩
    exact (lt_of_not_ge this).le
  rw [modularCutoff_eq_on_fd n z hz,heightWeight_zero n z.im hy]
  simp

theorem modularCutoff_norm_le (n : ℕ) (z : UpperHalfPlane) : ‖modularCutoff n z‖ ≤ 1 := by
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have hi := modularCutoff_invariant n (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hi
  rw [← hi,modularCutoff_eq_on_fd n (A • z) hA,Complex.norm_real,Real.norm_eq_abs]
  change |smoothWeight (cutoffHeight n) (cutoffHeight n) (A • z).im| ≤ 1
  rw [abs_of_nonneg (smoothWeight_nonneg _ _ _)]
  exact smoothWeight_le_one _ _ _

/-- The actual global modular cutoff eventually equals one at every fixed point. -/
theorem modularCutoff_eventually_one (z : UpperHalfPlane) :
    ∀ᶠ n : ℕ in atTop, modularCutoff n z = 1 := by
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  obtain ⟨N,hN⟩ := exists_nat_ge (A • z).im
  filter_upwards [eventually_ge_atTop N] with n hn
  have hi := modularCutoff_invariant n (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hi
  have hnn : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hh : (A • z).im ≤ cutoffHeight n := by
    unfold cutoffHeight
    linarith
  rw [← hi,modularCutoff_eq_on_fd n (A • z) hA,heightWeight_one n _ hh]
  norm_num

/-- At each closed-cell point the cutoff is eventually one on an entire
neighborhood, so all local derivative errors eventually vanish there. -/
theorem modularCutoff_eventually_germ_one (z : UpperHalfPlane) (hz : z ∈ fd) :
    ∀ᶠ n : ℕ in atTop, modularCutoff n =ᶠ[𝓝 z] (fun _ => (1:ℂ)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt z.im
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hh : z.im < cutoffHeight n := by
    unfold cutoffHeight
    linarith
  apply (modularCutoff_germ n z hz).trans
  have he : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < cutoffHeight n :=
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hh
  filter_upwards [he] with w hw
  rw [heightWeight_one n _ hw.le]
  norm_num

/-- The complete original corrected source cut off by the actual modular exhaustion. -/
def sourceCore (q : XiZeroCopy) (n : ℕ) : CoreField where
  field z := modularCutoff n z * globalResidual q z
  smooth := fun z => (modularCutoff_smooth n z).mul (globalResidual_smooth q z)
  invariant := by
    intro γ z
    rw [modularCutoff_invariant,globalResidual_invariant]
  compact := by
    obtain ⟨K,hK,hk⟩ := modularCutoff_compact n
    refine ⟨K,hK,?_⟩
    intro z hz hn
    dsimp only
    rw [hk z hz hn,zero_mul]

theorem sourceCore_field_on_fd (q : XiZeroCopy) (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) :
    (sourceCore q n).field z = (heightWeight n z.im : ℂ)*globalResidual q z := by
  change modularCutoff n z * globalResidual q z = _
  rw [modularCutoff_eq_on_fd n z hz]

/-- The approximants eventually retain the full original source germ at each
closed-cell point, including both derivatives of its literal operator image. -/
theorem sourceCore_eventually_germ (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    ∀ᶠ n : ℕ in atTop, (sourceCore q n).field =ᶠ[𝓝 z] globalResidual q := by
  filter_upwards [modularCutoff_eventually_germ_one z hz] with n hn
  filter_upwards [hn] with w hw
  change modularCutoff n w * globalResidual q w = globalResidual q w
  rw [hw,one_mul]

/-- The literal operator images are eventually exact at each fixed cell point.
This pointwise result does not assert convergence in the native graph norm. -/
theorem sourceCore_operator_eventually_eq (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    ∀ᶠ n : ℕ in atTop, (sourceCore q n).field z - chartLaplacian (sourceCore q n).field z =
      globalResidual q z - chartLaplacian (globalResidual q) z := by
  filter_upwards [sourceCore_eventually_germ q z hz] with n hn
  rw [hn.eq_of_nhds,chartLaplacian_congr hn]

/-- Every source approximant is admitted to the original native closed operator. -/
def sourceApproxDomain (q : XiZeroCopy) (n : ℕ) : energyOperator.domain :=
  ⟨fieldVector (sourceCore q n),(sourceCore q n).mem_energyOperator_domain⟩

/-- The admitted approximants retain the exact original differential operator image. -/
theorem sourceApproxDomain_operator_coe (q : XiZeroCopy) (n : ℕ) :
    (energyOperator (sourceApproxDomain q n) : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z => (sourceCore q n).field z - chartLaplacian (sourceCore q n).field z) :=
  (sourceCore q n).energyOperator_coe

/-- Compact modular approximants converge in the original native Hilbert norm
to the complete corrected source; no Fourier truncation is used. -/
theorem sourceApproxDomain_tendsto (q : XiZeroCopy) :
    Tendsto (fun n : ℕ => (sourceApproxDomain q n : Space)) atTop (𝓝 (sourceVector q)) := by
  have hm (n : ℕ) : Measurable (modularCutoff n) :=
    (ChartSmooth.continuous (modularCutoff_smooth n)).measurable
  have h0 : (0:ℝ) ≤ 1 := by norm_num
  have h1 (z : UpperHalfPlane) : ‖(1:ℂ)‖ ≤ (1:ℝ) := by simp
  have hpt (z : UpperHalfPlane) : Tendsto (fun n => modularCutoff n z) atTop (𝓝 (1:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [modularCutoff_eventually_one z] with n hn
    exact hn.symm
  have ht := tendsto_lpBoundedMulCLM_apply (μ := measure) hm measurable_const h0
    modularCutoff_norm_le h1 hpt (sourceVector q)
  have he (n : ℕ) : lpBoundedMulCLM (p := 2) (μ := measure) (hm n) h0
      (modularCutoff_norm_le n) (sourceVector q) = (sourceApproxDomain q n : Space) := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := measure) (hm n) h0
      (modularCutoff_norm_le n) (sourceVector q),sourceVector_coe q,
      (core_field_memLp (sourceCore q n).field (sourceCore q n).smooth (sourceCore q n).compact).coeFn_toLp]
      with z hz hr hc
    rw [hz,hr]
    exact hc.symm
  have he1 : lpBoundedMulCLM (p := 2) (μ := measure) measurable_const h0 h1 (sourceVector q) =
      sourceVector q := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := measure) measurable_const h0 h1 (sourceVector q)]
      with z hz
    rw [hz,one_mul]
  simpa only [he,he1] using ht

end
end RHTower.SelbergScatteringSourceApproximation
