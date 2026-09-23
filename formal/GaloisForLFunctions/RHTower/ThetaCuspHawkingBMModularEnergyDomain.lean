import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularWeakDerivative
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The completed graph of the full smooth modular core has a dense injective scalar projection. Local derivative identities survive completion and exclude nonzero gradients over a zero scalar vector.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- A full smooth modular field with compact quotient support. -/
structure CoreField where
  field : UpperHalfPlane → ℂ
  smooth : ChartSmooth field
  invariant : ∀ γ : PSL2Z, ∀ z, field (γ • z) = field z
  compact : CellCompact field

def fieldVector (f : CoreField) : Space :=
  (core_field_memLp f.field f.smooth f.compact).toLp f.field

def derivativeVector (f : CoreField) (v : ℂ) : Space :=
  (weightedDeriv_memLp v f.field f.smooth f.compact).toLp (weightedDeriv v f.field)

/-- Value and the two literal hyperbolic-frame derivatives, with the sum-of-squares Hilbert norm. -/
abbrev EnergySpace := PiLp 2 (fun _ : Fin 3 => Space)

def frameGraph (f : CoreField) : EnergySpace :=
  WithLp.toLp 2 ![fieldVector f,derivativeVector f 1,derivativeVector f Complex.I]

/-- Completion of the full modular differential graph, before projecting to scalar values. -/
def energyDomain : Submodule ℂ EnergySpace :=
  (Submodule.span ℂ (Set.range frameGraph)).topologicalClosure

instance : CompleteSpace energyDomain := by
  unfold energyDomain
  infer_instance

/-- The scalar-value projection of the completed actual differential graph. -/
def embedding : energyDomain →L[ℂ] Space :=
  (PiLp.proj 2 (fun _ : Fin 3 => Space) 0).comp energyDomain.subtypeL

theorem frameGraph_mem (f : CoreField) : frameGraph f ∈ energyDomain :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f,rfl⟩)

/-- The completed graph projects densely into the original angular Hilbert space. -/
theorem embedding_dense : Dense (embedding.range : Set Space) := by
  apply smoothCore_dense.mono
  rintro v ⟨f,hf,hi,hk,he⟩
  let a : CoreField := ⟨f,hf,hi,hk⟩
  refine ⟨⟨frameGraph a,frameGraph_mem a⟩,?_⟩
  change fieldVector a = v
  apply Lp.ext
  exact (core_field_memLp f hf hk).coeFn_toLp.trans he.symm

/-- Scalar L² norm is controlled by the actual value-plus-gradient energy norm. -/
theorem embedding_norm_le (x : energyDomain) : ‖embedding x‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le (x : EnergySpace) 0

/-- A smooth compact local test strictly inside the modular cell. -/
structure InteriorTest where
  field : ℂ → ℂ
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  support : tsupport field ⊆ interiorChart

private theorem test_memLp (g : ℂ → ℂ) (hg : Continuous g) (hk : HasCompactSupport g) :
    MemLp (fun z : UpperHalfPlane => g z) 2 measure := by
  have h := hg.memLp_of_hasCompactSupport (μ := Measure.map UpperHalfPlane.coe measure) (p := 2) hk
  exact UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff.mp h

def massTestFunction (g : InteriorTest) (z : ℂ) : ℂ := conj ((z.im : ℂ)*g.field z)
def fluxTestFunction (g : InteriorTest) (v z : ℂ) : ℂ :=
  conj ((z.im : ℂ)^(2 : ℕ)*fderiv ℝ g.field z v)

private theorem massTest_continuous (g : InteriorTest) : Continuous (massTestFunction g) :=
  Complex.conjCLE.continuous.comp
    ((Complex.ofRealCLM.continuous.comp Complex.continuous_im).mul g.smooth.continuous)

private theorem massTest_compact (g : InteriorTest) : HasCompactSupport (massTestFunction g) := by
  apply g.compact.mono
  intro z hz hzero
  apply hz
  simp [massTestFunction,hzero]

private theorem fluxTest_continuous (g : InteriorTest) (v : ℂ) : Continuous (fluxTestFunction g v) :=
  Complex.conjCLE.continuous.comp
    (((Complex.ofRealCLM.continuous.comp Complex.continuous_im).pow 2).mul
      ((g.smooth.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const))

private theorem fluxTest_compact (g : InteriorTest) (v : ℂ) : HasCompactSupport (fluxTestFunction g v) := by
  apply (g.compact.fderiv_apply ℝ v).mono
  intro z hz hzero
  apply hz
  simp [fluxTestFunction,hzero]

def massTest (g : InteriorTest) : Space :=
  (test_memLp _ (massTest_continuous g) (massTest_compact g)).toLp (fun z => massTestFunction g z)

def fluxTest (g : InteriorTest) (v : ℂ) : Space :=
  (test_memLp _ (fluxTest_continuous g v) (fluxTest_compact g v)).toLp
    (fun z => fluxTestFunction g v z)

theorem massTest_inner (g : InteriorTest) (u : Space) :
    inner ℂ (massTest g) u = ∫ z : UpperHalfPlane, ((z.im : ℂ)*g.field z)*u z ∂measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(test_memLp _ (massTest_continuous g) (massTest_compact g)).coeFn_toLp] with z hz
  change (massTest g) z = massTestFunction g z at hz
  rw [hz]
  simp [massTestFunction,mul_comm]

theorem fluxTest_inner (g : InteriorTest) (v : ℂ) (u : Space) :
    inner ℂ (fluxTest g v) u =
      ∫ z : UpperHalfPlane, ((z.im : ℂ)^(2 : ℕ)*fderiv ℝ g.field (z:ℂ) v)*u z ∂measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(test_memLp _ (fluxTest_continuous g v) (fluxTest_compact g v)).coeFn_toLp] with z hz
  change (fluxTest g v) z = fluxTestFunction g v z at hz
  rw [hz]
  simp [fluxTestFunction,mul_comm]

/-- The two real coordinate directions underlying the hyperbolic frame. -/
def direction (i : Fin 2) : ℂ := ![1,Complex.I] i

private theorem frameGraph_derivative (f : CoreField) (i : Fin 2) :
    frameGraph f i.succ = derivativeVector f (direction i) := by
  fin_cases i <;> rfl

/-- The continuous local integration-by-parts functional on the full differential graph. -/
def testConstraint (g : InteriorTest) (i : Fin 2) : EnergySpace →L[ℂ] ℂ :=
  (innerSL ℂ (massTest g)).comp (PiLp.proj 2 (fun _ : Fin 3 => Space) i.succ) +
  (innerSL ℂ (fluxTest g (direction i))).comp (PiLp.proj 2 (fun _ : Fin 3 => Space) 0)

private theorem testConstraint_frameGraph (g : InteriorTest) (i : Fin 2) (f : CoreField) :
    testConstraint g i (frameGraph f) = 0 := by
  change inner ℂ (massTest g) (frameGraph f i.succ) +
    inner ℂ (fluxTest g (direction i)) (fieldVector f) = 0
  rw [frameGraph_derivative,massTest_inner,fluxTest_inner]
  have hL : (∫ z : UpperHalfPlane, ((z.im : ℂ)*g.field z)*(derivativeVector f (direction i)) z ∂measure) =
      ∫ z : UpperHalfPlane, weightedDeriv (direction i) f.field z*((z.im : ℂ)*g.field z) ∂measure := by
    apply integral_congr_ae
    filter_upwards [(weightedDeriv_memLp (direction i) f.field f.smooth f.compact).coeFn_toLp] with z hz
    change (derivativeVector f (direction i)) z = weightedDeriv (direction i) f.field z at hz
    rw [hz,mul_comm]
  have hR : (∫ z : UpperHalfPlane, ((z.im : ℂ)^(2 : ℕ)*fderiv ℝ g.field (z:ℂ) (direction i))*(fieldVector f) z ∂measure) =
      ∫ z : UpperHalfPlane, f.field z*((z.im : ℂ)^(2 : ℕ)*fderiv ℝ g.field (z:ℂ) (direction i)) ∂measure := by
    apply integral_congr_ae
    filter_upwards [(core_field_memLp f.field f.smooth f.compact).coeFn_toLp] with z hz
    change (fieldVector f) z = f.field z at hz
    rw [hz,mul_comm]
  rw [hL,hR,weightedDeriv_test_identity f.field f.smooth g.field g.smooth g.compact g.support]
  exact neg_add_cancel _

/-- The literal local derivative identity survives the actual energy completion. -/
theorem energyDomain_testConstraint (g : InteriorTest) (i : Fin 2) (x : energyDomain) :
    testConstraint g i x = 0 := by
  have hsub : energyDomain ≤ (testConstraint g i).toLinearMap.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨f,rfl⟩
      exact testConstraint_frameGraph g i f
    · exact (testConstraint g i).isClosed_ker
  exact hsub x.property

end
end RHTower.D4BMModularCore

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

private theorem zero_of_massTest_annihilation (u : Space)
    (hu : ∀ g : InteriorTest, inner ℂ (massTest g) u = 0) : u = 0 := by
  let ν : Measure ℂ := Measure.map UpperHalfPlane.coe measure
  let U : ℂ → ℂ := fun z => u (UpperHalfPlane.ofComplex z)
  have hU : MemLp U 2 ν := by
    apply UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff.mpr
    simpa only [U,Function.comp_def,UpperHalfPlane.ofComplex_apply] using Lp.memLp u
  have hOpen : IsOpen interiorChart :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo
  have hY : ContinuousOn (fun z : ℂ => (z.im : ℂ)) interiorChart :=
    (Complex.ofRealCLM.continuous.comp Complex.continuous_im).continuousOn
  have hW := ((hU.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn interiorChart).continuousOn_mul hY hOpen.isLocallyClosed
  have ht : ∀ (g : ℂ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ interiorChart →
      ∫ z, g z • ((z.im : ℂ)*U z) ∂ν = 0 := by
    intro g hg hk hs
    let G : ℂ → ℂ := fun z => (g z : ℂ)
    have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hg
    have hsupport : Function.support G ⊆ Function.support g := by
      intro z hz
      simpa only [G,Function.mem_support,Complex.ofReal_ne_zero] using hz
    let t : InteriorTest := ⟨G,hG,hk.mono hsupport,(closure_mono hsupport).trans hs⟩
    have hzero := hu t
    rw [massTest_inner] at hzero
    rw [UpperHalfPlane.measurableEmbedding_coe.integral_map]
    calc
      _ = ∫ z : UpperHalfPlane, ((z.im : ℂ)*t.field z)*u z ∂measure := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [U,UpperHalfPlane.ofComplex_apply,t,G,Complex.real_smul,coe_im]
        ring
      _ = 0 := hzero
  have hz := hOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hW ht
  have hz' := UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mp hz
  apply Lp.ext
  filter_upwards [hz',ae_mem_interior,Lp.coeFn_zero ℂ 2 measure] with z hzero hz h0
  rw [h0]
  have h : (z.im : ℂ)*u z = 0 := by
    simpa only [U,UpperHalfPlane.ofComplex_apply,coe_im] using hzero ⟨z,hz,rfl⟩
  exact (mul_eq_zero.mp h).resolve_left (Complex.ofReal_ne_zero.mpr z.im_ne_zero)

private theorem embedding_eq_zero_imp (x : energyDomain) (hx : embedding x = 0) : x = 0 := by
  have hd (i : Fin 2) : (x : EnergySpace) i.succ = 0 := by
    apply zero_of_massTest_annihilation
    intro g
    have he := energyDomain_testConstraint g i x
    change inner ℂ (massTest g) ((x : EnergySpace) i.succ) +
      inner ℂ (fluxTest g (direction i)) (embedding x) = 0 at he
    rw [hx,inner_zero_right,add_zero] at he
    exact he
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hx
  · exact hd 0
  · exact hd 1

/-- The actual modular energy completion is faithful: a scalar L² value determines both
completed hyperbolic derivatives. This closes the differential graph's closability obligation. -/
theorem embedding_injective : Function.Injective embedding := by
  intro x y hxy
  have hz : embedding (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  exact sub_eq_zero.mp (embedding_eq_zero_imp (x-y) hz)

end
end RHTower.D4BMModularCore
