import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCutoffDomination

/-! The original noncompact physical angular Laplacian pairing is the proved limit of native core tests. -/
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem laplacian_pairing_ae (q : XiZeroCopy) (n : ℕ) (h : RadialSpace) (u : SpatialSpace) :
    (fun p => inner ℂ (l2SeparatedProduct h (fieldVector (physicalCoreCutoff q n).laplacian) p) (u p)) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure]
    fun p => conj (h p.1)*conj ((physicalCoreCutoff q n).laplacian.field p.2)*u p := by
  let g := (physicalCoreCutoff q n).laplacian
  have hg : (fun p : ℝ × UpperHalfPlane => fieldVector g p.2) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure] fun p => g.field p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (core_field_memLp g.field g.smooth g.compact).coeFn_toLp
  filter_upwards [l2SeparatedProduct_ae h (fieldVector g),hg] with p hp hq
  simp only [l2SeparatedFun] at hp
  rw [hp,hq]
  simp only [RCLike.inner_apply,map_mul]
  ring

/-- The compact angular differential term is the literal original test-first integral. -/
theorem physicalCoreCutoff_laplacian_inner (q : XiZeroCopy) (n : ℕ) (h : RadialSpace) (u : SpatialSpace) :
    inner ℂ (l2SeparatedProduct h (fieldVector (physicalCoreCutoff q n).laplacian)) u =
      ∫ p : ℝ × UpperHalfPlane, conj (h p.1)*conj ((physicalCoreCutoff q n).laplacian.field p.2)*u p
        ∂radialMeasure.prod D4BMModularCore.measure := by
  rw [L2.inner_def]
  exact integral_congr_ae (laplacian_pairing_ae q n h u)

/-- The full differentiated physical test limit is justified by the actual response's height norm and both cutoff commutators. -/
theorem physicalCoreCutoff_laplacian_inner_tendsto (q : XiZeroCopy) (h : RadialSpace) (u : SpatialSpace)
    (hu : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    Tendsto (fun n : ℕ => inner ℂ (l2SeparatedProduct h (fieldVector (physicalCoreCutoff q n).laplacian)) u)
      atTop (𝓝 ((physicalAngularParameter q^(2 : ℕ)-1/4)*inner ℂ h (physicalJointProjection q (hu.toLp _)))) := by
  rw [physicalJointProjection_height_integral q h u hu,← integral_const_mul]
  simp_rw [physicalCoreCutoff_laplacian_inner]
  obtain ⟨C,hC,hb⟩ := physicalCoreCutoff_laplacian_bound
  let L := physicalAngularParameter q^(2 : ℕ)-1/4
  let P : ℝ × UpperHalfPlane → ℂ := fun p =>
    conj (h p.1)*scalar (physicalAngularParameter q) (coordinates p.2)*u p
  let Q : ℝ × UpperHalfPlane → ℂ := fun p =>
    h p.1*coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates p.2)*((p.2.im:ℂ)*u p)
  let B : ℝ × UpperHalfPlane → ℝ := fun p => (‖L‖+C)*‖P p‖+2*C*‖Q p‖
  have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
      p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  apply tendsto_integral_of_dominated_convergence B
  · intro n
    exact (L2.integrable_inner (𝕜 := ℂ)
      (l2SeparatedProduct h (fieldVector (physicalCoreCutoff q n).laplacian)) u).aestronglyMeasurable.congr
        (laplacian_pairing_ae q n h u)
  · exact ((physical_height_pairing_integrable q h u hu).norm.const_mul (‖L‖+C)).add
      ((physical_vertical_pairing_integrable q h u hu).norm.const_mul (2*C))
  · intro n
    filter_upwards [hfd] with p hp
    simp only [norm_mul,norm_conj]
    calc
      _ ≤ ‖h p.1‖*((‖L‖+C)*‖scalar (physicalAngularParameter q) (coordinates p.2)‖+
          2*C*p.2.im*‖coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates p.2)‖)*‖u p‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb q n p.2 hp) (norm_nonneg _)) (norm_nonneg _)
      _ = B p := by
        simp only [B,P,Q,norm_mul,norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_pos p.2.im_pos]
        ring
  · filter_upwards [hfd] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [physicalCoreCutoff_eventually_laplacian q p.2 hp] with n hn
    rw [hn,physicalTestField_laplacian,starRingEnd_self_apply]
    ring

end
end RHTower.D4BMJointSource
