import GaloisForLFunctions.RHTower.SelbergScatteringSourceApproximation
import GaloisForLFunctions.RHTower.SelbergScatteringCutoffForcing
import GaloisForLFunctions.RHTower.SelbergScatteringNativeResidual

/-!
# Original source derivatives and differential image

Uniform bounds for the complete shifted Fourier--Bessel families admit the
original weighted vertical derivative. Compact lower-cell control and full
upper-cell tails retain every mode. The original differential forcing supplies
an actual L2 operator-image target, with its literal representative proved on
the full closed modular cell. Native operator-domain admission is not assumed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped MatrixGroups ContDiff
namespace RHTower.SelbergScatteringSourceBounds
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMJointSource
open SelbergScatteringCuspSubtraction SelbergScatteringSourceVector
open SelbergScatteringNativeResidual
noncomputable section

/-- Every weighted vertical derivative of the full infinite Bessel family is
uniformly bounded on a positive-height half-strip. -/
theorem weighted_value_vertical_bounded (u nu w : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 →
      ‖(z 1 : ℂ)^w * coordDeriv 1 (value u nu a d negative) z‖ ≤ C := by
  obtain ⟨A,hA,hbA⟩ := weighted_value_bounded u nu w (a-1) d negative l hl
  obtain ⟨B,hB,hbB⟩ := weighted_value_bounded u (nu+1) w a (d+1) negative l hl
  obtain ⟨C,hC,hbC⟩ := weighted_value_bounded u (nu-1) w a (d+1) negative l hl
  refine ⟨‖(a:ℂ)‖*A+‖(Real.pi:ℂ)‖*(B+C),by positivity,?_⟩
  intro z hz
  have hy := hl.trans_le hz
  have hd : coordDeriv 1 (value u nu a d negative) z =
      (a:ℂ)*value u nu (a-1) d negative z -
        (Real.pi:ℂ)*(value u (nu+1) a (d+1) negative z+value u (nu-1) a (d+1) negative z) := by
    rw [coordDeriv,(value_hasFDerivAt u nu a d negative z hy).fderiv]
    simp [valueGradient,D4BMAngularSeries.gradient]
  have he : (z 1 : ℂ)^w * coordDeriv 1 (value u nu a d negative) z =
      (a:ℂ)*((z 1 : ℂ)^w*value u nu (a-1) d negative z) -
        (Real.pi:ℂ)*((z 1 : ℂ)^w*value u (nu+1) a (d+1) negative z+
          (z 1 : ℂ)^w*value u (nu-1) a (d+1) negative z) := by
    rw [hd]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have h := add_le_add (mul_le_mul_of_nonneg_left (hbA z hz) (norm_nonneg (a:ℂ)))
    (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hbB z hz) (hbC z hz)))
      (norm_nonneg (Real.pi:ℂ)))
  simpa only [norm_mul] using h

private theorem tail_vertical_eq (u : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 1 (tail u) z = 2*(coordDeriv 1 (value u u (1/2) 0 false) z +
      coordDeriv 1 (value u u (1/2) 0 true) z) := by
  have he : tail u =ᶠ[𝓝 z] (fun v => 2*(value u u (1/2) 0 false v+value u u (1/2) 0 true v)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
    simp only [tail,d4BMCompletedEisensteinCuspTailPart,d4BMCompletedEisensteinFullSignedZeroWord,
      signedTail_eq_value _ _ _ _ _ v hv,Nat.cast_zero,zero_add]
  have h0 := (value_hasFDerivAt u u (1/2) 0 false z hz).differentiableAt
  have h1 := (value_hasFDerivAt u u (1/2) 0 true z hz).differentiableAt
  have hsum : DifferentiableAt ℝ (fun v => value u u (1/2) 0 false v+value u u (1/2) 0 true v) z :=
    h0.add h1
  unfold coordDeriv
  rw [he.fderiv_eq,fderiv_const_mul hsum,fderiv_fun_add h0 h1]
  simp [add_apply,smul_apply,smul_eq_mul]
  ring

/-- The complete scalar Fourier tail retains uniform weighted vertical
derivative bounds, with both signed infinite families present. -/
theorem weighted_tail_vertical_bounded (u w : ℂ) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 →
      ‖(z 1 : ℂ)^w * coordDeriv 1 (tail u) z‖ ≤ C := by
  obtain ⟨A,hA,hbA⟩ := weighted_value_vertical_bounded u u w (1/2) 0 false l hl
  obtain ⟨B,hB,hbB⟩ := weighted_value_vertical_bounded u u w (1/2) 0 true l hl
  refine ⟨2*(A+B),by positivity,?_⟩
  intro z hz
  rw [tail_vertical_eq u z (hl.trans_le hz)]
  have he : (z 1 : ℂ)^w * (2*(coordDeriv 1 (value u u (1/2) 0 false) z+
      coordDeriv 1 (value u u (1/2) 0 true) z)) =
      2*((z 1 : ℂ)^w*coordDeriv 1 (value u u (1/2) 0 false) z+
        (z 1 : ℂ)^w*coordDeriv 1 (value u u (1/2) 0 true) z) := by ring
  rw [he,norm_mul]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hbA z hz) (hbB z hz)))
      (by norm_num)

private theorem weightedDeriv_congr {f g : UpperHalfPlane → ℂ} {z : UpperHalfPlane}
    (he : f =ᶠ[𝓝 z] g) (v : ℂ) : weightedDeriv v f z = weightedDeriv v g z := by
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hp : f ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] g ∘ ofComplex := by
    change ∀ᶠ w in 𝓝 (z:ℂ), f (ofComplex w) = g (ofComplex w)
    apply hc.eventually (p := fun w => f w = g w)
    rw [ofComplex_apply]
    exact he
  unfold weightedDeriv
  rw [hp.fderiv_eq]

private theorem weightedDeriv_coordinates_vertical (f : (Fin 2 → ℝ) → ℂ) (z : UpperHalfPlane) :
    weightedDeriv Complex.I (fun w => f (coordinates w)) z =
      (z.im:ℂ)*coordDeriv 1 f (coordinates z) := by
  have he : (fun w : UpperHalfPlane => f (coordinates w)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      f ∘ angularCoordinates := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw,angularCoordinates]
    rfl
  unfold weightedDeriv
  rw [he.fderiv_eq]
  have hd := angularCoordinates_derivative f 1 (z:ℂ)
  change fderiv ℝ (f ∘ angularCoordinates) (z:ℂ) Complex.I = coordDeriv 1 f (coordinates z) at hd
  rw [hd]

/-- The complete corrected source has a uniformly bounded original vertical
frame derivative on the entire closed modular cell. -/
theorem globalResidual_vertical_bounded (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ fd →
      ‖weightedDeriv Complex.I (globalResidual q) z‖ ≤ C := by
  have hc := weightedDeriv_continuous Complex.I (globalResidual q) (globalResidual_smooth q)
  obtain ⟨A,hA⟩ := (truncated_cell_compact 4).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨B,hB,hb⟩ := weighted_tail_vertical_bounded (physicalAngularParameter q) 1 3 (by norm_num)
  refine ⟨max 0 (max A B),le_max_left _ _,?_⟩
  intro z hz
  by_cases hy : z.im ≤ 4
  · exact (hA z ⟨hz,hy⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h3 : 3 < z.im := by linarith
    have hg : globalResidual q =ᶠ[𝓝 z] (fun w => tail (physicalAngularParameter q) (coordinates w)) := by
      apply (cellGermExtension_germ _ (residual_cell_compatible q) z hz).trans
      have he : ∀ᶠ w : UpperHalfPlane in 𝓝 z, 3 < w.im :=
        (isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds h3
      filter_upwards [he] with w hw
      exact residual_high q (coordinates w) hw.le
    rw [weightedDeriv_congr hg,weightedDeriv_coordinates_vertical]
    have hh := hb (coordinates z) h3.le
    rw [Complex.cpow_one] at hh
    exact hh.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The actual vertical frame derivative is admitted in the original native
Hilbert space; the complete source and both signed tails are retained. -/
theorem globalResidual_vertical_memLp (q : XiZeroCopy) :
    MemLp (weightedDeriv Complex.I (globalResidual q)) 2 measure := by
  obtain ⟨C,_,hb⟩ := globalResidual_vertical_bounded q
  apply MemLp.of_bound (weightedDeriv_continuous Complex.I (globalResidual q)
    (globalResidual_smooth q)).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with z hz
  exact hb z hz

def sourceVerticalVector (q : XiZeroCopy) : Space :=
  (globalResidual_vertical_memLp q).toLp (weightedDeriv Complex.I (globalResidual q))

theorem sourceVerticalVector_coe (q : XiZeroCopy) :
    (sourceVerticalVector q : UpperHalfPlane → ℂ) =ᵐ[measure]
      weightedDeriv Complex.I (globalResidual q) :=
  (globalResidual_vertical_memLp q).coeFn_toLp

/-- The native vertical derivative retains the original residual derivative at
every closed-cell point, including the glued seams. -/
theorem globalResidual_vertical_on_fd (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    weightedDeriv Complex.I (globalResidual q) z =
      (z.im:ℂ)*coordDeriv 1 (residual q) (coordinates z) := by
  have hg : globalResidual q =ᶠ[𝓝 z] (fun w => residual q (coordinates w)) :=
    cellGermExtension_germ _ (residual_cell_compatible q) z hz
  rw [weightedDeriv_congr hg,weightedDeriv_coordinates_vertical]

/-- The glued original source retains its full literal forced operator equation
on every point of the closed modular cell. -/
theorem globalResidual_operator_on_fd (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    globalResidual q z - chartLaplacian (globalResidual q) z =
      scatteringEnergy (q.1:ℂ)*globalResidual q z + cutoffForcing q (coordinates z) := by
  have hg : globalResidual q =ᶠ[𝓝 z] (fun w => residual q (coordinates w)) :=
    cellGermExtension_germ _ (residual_cell_compatible q) z hz
  rw [chartLaplacian_congr hg,chartLaplacian_coordinates,globalResidual_eq_on_fd q z hz]
  rw [← residual_equation q (coordinates z) z.im_pos]
  unfold scatteringEnergy
  ring

/-- The original differential operator image as an actual native L2 vector.
Domain admission of the source still requires its graph limit. -/
def sourceOperatorTarget (q : XiZeroCopy) : Space :=
  scatteringEnergy (q.1:ℂ) • sourceVector q + SelbergScatteringCutoffForcing.forcingVector q

theorem sourceOperatorTarget_coe (q : XiZeroCopy) :
    (sourceOperatorTarget q : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z => globalResidual q z - chartLaplacian (globalResidual q) z) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [Lp.coeFn_smul (scatteringEnergy (q.1:ℂ)) (sourceVector q),sourceVector_coe q,
    SelbergScatteringCutoffForcing.forcingVector_coe q,ae_restrict_mem isClosed_fd.measurableSet]
    with z hs hr hh hz
  simp only [Pi.add_apply,Pi.smul_apply] at hs ⊢
  rw [hs,hr,hh,smul_eq_mul]
  exact (globalResidual_operator_on_fd q z hz).symm

end
end RHTower.SelbergScatteringSourceBounds
