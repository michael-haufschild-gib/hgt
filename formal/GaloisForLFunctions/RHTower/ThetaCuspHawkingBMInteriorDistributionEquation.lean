import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalAngularWeakResponse

/-!
Actual smooth modular energy tests identify the complete second-order distributional equation of the full angular response.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- Compact interior tests are closed under every real directional derivative. -/
def InteriorTest.derivative (g : InteriorTest) (v : ℂ) : InteriorTest where
  field z := fderiv ℝ g.field z v
  smooth := (g.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  compact := g.compact.fderiv_apply ℝ v
  support := (tsupport_fderiv_apply_subset ℝ v).trans g.support

/-- Complex conjugation preserves the actual smooth compact interior test space. -/
def InteriorTest.conjugate (g : InteriorTest) : InteriorTest where
  field z := conj (g.field z)
  smooth := Complex.conjCLE.contDiff.comp g.smooth
  compact := g.compact.mono (by intro z hz he; exact hz (by simp [he]))
  support := (closure_mono (by intro z hz he; exact hz (by simp [he]))).trans g.support

private theorem InteriorTest.restricted_compact (g : InteriorTest) :
    HasCompactSupport (fun z : UpperHalfPlane => g.field z) := by
  have hs : tsupport g.field ⊆ Set.range UpperHalfPlane.coe :=
    g.support.trans (Set.image_subset_range _ _)
  have hK := UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage' g.compact hs
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro z hz
    exact subset_tsupport g.field hz
  · exact isClosed_closure.preimage UpperHalfPlane.continuous_coe

private theorem InteriorTest.restricted_support (g : InteriorTest) :
    Function.support (fun z : UpperHalfPlane => g.field z) ⊆ ModularGroup.fdo := by
  intro z hz
  obtain ⟨w,hw,he⟩ := g.support (subset_tsupport g.field hz)
  exact UpperHalfPlane.coe_injective he ▸ hw

private theorem InteriorTest.restricted_smooth (g : InteriorTest) :
    ChartSmooth (fun z : UpperHalfPlane => g.field z) := by
  intro z
  apply g.smooth.contDiffAt.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,UpperHalfPlane.ofComplex_apply_of_im_pos hw]

/-- Actual smooth modular extension of a compact interior test by periodization. -/
def InteriorTest.modularField (g : InteriorTest) : CoreField where
  field := periodize (fun z : UpperHalfPlane => g.field z)
  smooth := periodize_smooth _ g.restricted_compact g.restricted_smooth
  invariant := periodize_invariant _
  compact := ⟨tsupport (fun z : UpperHalfPlane => g.field z),g.restricted_compact,by
    intro z hz hn
    rw [periodize_eq_on_fd _ g.restricted_support z hz]
    exact image_eq_zero_of_notMem_tsupport (f := fun z : UpperHalfPlane => g.field z) hn⟩

/-- The constructed modular extension retains exact test values on the closed cell. -/
theorem InteriorTest.modularField_eq (g : InteriorTest) (z : UpperHalfPlane) (hz : z ∈ fd) :
    g.modularField.field z = g.field z :=
  periodize_eq_on_fd _ g.restricted_support z hz

/-- Both actual derivatives of the periodized test agree on the open cell. -/
theorem InteriorTest.modularField_deriv (g : InteriorTest) (v : ℂ) (z : UpperHalfPlane)
    (hz : z ∈ fdo) : weightedDeriv v g.modularField.field z =
      (z.im : ℂ)*fderiv ℝ g.field (z:ℂ) v := by
  have he : g.modularField.field ∘ UpperHalfPlane.ofComplex =ᶠ[𝓝 (z:ℂ)] g.field := by
    have hopen : IsOpen interiorChart := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ isOpen_fdo
    filter_upwards [hopen.mem_nhds ⟨z,hz,rfl⟩] with w hw
    obtain ⟨a,ha,rfl⟩ := hw
    simpa only [Function.comp_apply,UpperHalfPlane.ofComplex_apply] using
      g.modularField_eq a (fdo_subset_fd ha)
  unfold weightedDeriv
  rw [he.fderiv_eq]

private theorem InteriorTest.conjugate_deriv (g : InteriorTest) (v z : ℂ) :
    fderiv ℝ g.conjugate.field z v = conj (fderiv ℝ g.field z v) := by
  have hd := (Complex.conjCLE.hasFDerivAt.comp z
    (g.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
  exact congrArg (fun a : ℂ →L[ℝ] ℂ => a v) hd

/-- The conjugated test embedded in the actual completed modular energy domain. -/
def InteriorTest.energyTest (g : InteriorTest) : energyDomain :=
  ⟨frameGraph g.conjugate.modularField,frameGraph_mem _⟩

/-- The scalar component of the constructed energy test retains the conjugated local field. -/
theorem InteriorTest.energyTest_scalar (g : InteriorTest) :
    (embedding g.energyTest : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z : UpperHalfPlane => conj (g.field z)) := by
  apply (core_field_memLp _ g.conjugate.modularField.smooth g.conjugate.modularField.compact).coeFn_toLp.trans
  filter_upwards [ae_mem_interior] with z hz
  exact g.conjugate.modularField_eq z (fdo_subset_fd hz)

/-- A constructed energy test's gradient is precisely the mass test of its local derivative. -/
theorem InteriorTest.energyTest_gradient (g : InteriorTest) (i : Fin 2) :
    (g.energyTest : EnergySpace) i.succ = massTest (g.derivative (direction i)) := by
  have hi : (g.energyTest : EnergySpace) i.succ =
      derivativeVector g.conjugate.modularField (direction i) := by fin_cases i <;> rfl
  rw [hi]
  apply Lp.ext
  have hm : (massTest (g.derivative (direction i)) : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z : UpperHalfPlane => massTestFunction (g.derivative (direction i)) z) := by
    unfold massTest
    exact MemLp.coeFn_toLp _
  filter_upwards [(weightedDeriv_memLp (direction i) _ g.conjugate.modularField.smooth
    g.conjugate.modularField.compact).coeFn_toLp,hm,ae_mem_interior] with z hd hm hz
  change derivativeVector g.conjugate.modularField (direction i) z = _ at hd
  rw [hd,hm,g.conjugate.modularField_deriv _ z hz,g.conjugate_deriv]
  simp [massTestFunction,InteriorTest.derivative,map_mul]

end
end RHTower.D4BMModularCore

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- The exact dual Euclidean Laplacian, weighted by squared hyperbolic height. -/
def InteriorTest.laplaceVector (g : InteriorTest) : Space :=
  ∑ i : Fin 2, fluxTest (g.derivative (direction i)) (direction i)

/-- The two completed gradients can both be moved onto an actual compact interior test. -/
theorem InteriorTest.completed_green (g : InteriorTest) (h : energyDomain) :
    (∑ i : Fin 2, inner ℂ ((g.energyTest : EnergySpace) i.succ) ((h : EnergySpace) i.succ)) =
      -inner ℂ g.laplaceVector (embedding h) := by
  have he (i : Fin 2) :
      inner ℂ ((g.energyTest : EnergySpace) i.succ) ((h : EnergySpace) i.succ) =
        -inner ℂ (fluxTest (g.derivative (direction i)) (direction i)) (embedding h) := by
    rw [g.energyTest_gradient]
    apply eq_neg_iff_add_eq_zero.mpr
    exact energyDomain_testConstraint (g.derivative (direction i)) i h
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  congr 1
  simp only [InteriorTest.laplaceVector,sum_inner]

/-- The constructed response satisfies the full distributional angular equation,
with both derivatives transferred to the test and no regularity premise on the response. -/
theorem full_response_distribution_equation (q : XiZeroCopy) (minusBranch : Bool)
    (g : InteriorTest) :
    inner ℂ g.laplaceVector (embedding (weakResponse q minusBranch)) -
      parameter q minusBranch*inner ℂ (embedding g.energyTest) (embedding (weakResponse q minusBranch)) =
        inner ℂ (embedding g.energyTest) (forcingVector q minusBranch) := by
  have he := (weakSolution_iff_gradient q minusBranch _).mp
    (weakResponse_spec q minusBranch) g.energyTest
  rw [g.completed_green] at he
  linear_combination -he

/-- The actual scalar test pairing is its literal local integral. -/
theorem InteriorTest.scalar_pairing (g : InteriorTest) (u : Space) :
    inner ℂ (embedding g.energyTest) u = ∫ z : UpperHalfPlane, g.field z*u z ∂measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.energyTest_scalar] with z hz
  rw [hz]
  simp [mul_comm]

/-- Local scalar test moments of every angular L² vector are absolutely integrable. -/
theorem InteriorTest.integrable_scalar_pairing (g : InteriorTest) (u : Space) :
    Integrable (fun z : UpperHalfPlane => g.field z*u z) measure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (embedding g.energyTest) u).congr
  filter_upwards [g.energyTest_scalar] with z hz
  rw [hz]
  simp [mul_comm]

private theorem fluxTest_coe (g : InteriorTest) (v : ℂ) :
    (fluxTest g v : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z : UpperHalfPlane => conj ((z.im : ℂ)^2*fderiv ℝ g.field z v)) := by
  unfold fluxTest
  exact MemLp.coeFn_toLp _

private theorem integrable_flux_pairing (g : InteriorTest) (v : ℂ) (u : Space) :
    Integrable (fun z : UpperHalfPlane => ((z.im : ℂ)^2*fderiv ℝ g.field z v)*u z) measure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (fluxTest g v) u).congr
  filter_upwards [fluxTest_coe g v] with z hz
  rw [hz]
  simp [mul_comm]

/-- The literal planar Laplacian of a compact interior test. -/
def InteriorTest.planarLaplacian (g : InteriorTest) (z : ℂ) : ℂ :=
  ∑ i : Fin 2, fderiv ℝ (g.derivative (direction i)).field z (direction i)

/-- The dual Laplacian vector pairs as the native measure's height-squared differential expression. -/
theorem InteriorTest.laplace_pairing (g : InteriorTest) (u : Space) :
    inner ℂ g.laplaceVector u =
      ∫ z : UpperHalfPlane, (z.im : ℂ)^2*g.planarLaplacian z*u z ∂measure := by
  simp only [InteriorTest.laplaceVector,sum_inner,fluxTest_inner]
  rw [← integral_finsetSum _ (fun i _ => integrable_flux_pairing _ _ u)]
  congr 1
  funext z
  simp only [InteriorTest.planarLaplacian,Finset.mul_sum,Finset.sum_mul]

/-- Every actual Xi response obeys the literal second-order local distributional PDE. -/
theorem full_response_integral_equation (q : XiZeroCopy) (minusBranch : Bool)
    (g : InteriorTest) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^2*g.planarLaplacian z*
      (embedding (weakResponse q minusBranch)) z ∂measure) -
      parameter q minusBranch*(∫ z : UpperHalfPlane, g.field z*
        (embedding (weakResponse q minusBranch)) z ∂measure) =
      ∫ z : UpperHalfPlane, g.field z*forcing q minusBranch (coordinates z) ∂measure := by
  have he := full_response_distribution_equation q minusBranch g
  rw [g.laplace_pairing,g.scalar_pairing,g.scalar_pairing] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [forcingVector_coe q minusBranch] with z hz
  rw [hz]

end
end RHTower.D4BMModularCore
