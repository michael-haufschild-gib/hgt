import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularEnergyDomain

/-! Totality and weak derivative identities for the actual modular tests used by the joint wave domain. -/
open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped ContDiff
namespace RHTower.D4BMJointWave
open D4BMModularCore
noncomputable section

/-- The original full modular core separates the actual angular L² space. -/
theorem angularValue_total (u : Space)
    (hu : ∀ f : CoreField, inner ℂ (fieldVector f) u = 0) : u = 0 := by
  have hclosed : IsClosed {v : Space | inner ℂ v u = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hs : (smoothCore : Set Space) ⊆ {v : Space | inner ℂ v u = 0} := by
    rintro v ⟨f,hf,hi,hk,he⟩
    let a : CoreField := ⟨f,hf,hi,hk⟩
    have ha : fieldVector a = v := Lp.ext
      ((core_field_memLp f hf hk).coeFn_toLp.trans he.symm)
    exact ha ▸ hu a
  exact inner_self_eq_zero.mp (closure_minimal hs hclosed (smoothCore_dense u))

/-- Local mass tests are total; the positive hyperbolic height cannot conceal an L² component. -/
theorem angularMass_total (u : Space)
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

/-- The joint construction uses the actual modular integration-by-parts identity. -/
theorem angularDerivative_green (f : CoreField) (g : InteriorTest) (i : Fin 2) :
    inner ℂ (massTest g) (derivativeVector f (direction i)) +
      inner ℂ (fluxTest g (direction i)) (fieldVector f) = 0 := by
  have h := energyDomain_testConstraint g i ⟨frameGraph f,frameGraph_mem f⟩
  fin_cases i <;> exact h

end
end RHTower.D4BMJointWave
