/-
Spectral estimates adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicExteriorCoercivity
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicVariationalLaplacian
import GaloisForLFunctions.HTGeometry.ConstitutiveCompactCofinalFusion
import GaloisForLFunctions.HTGeometry.BoundedFredholmStability

/-!
# Fredholm spectral pencil below the cusp threshold

Exterior coercivity bounds energy by the spectral residual and compact-core
mass. The corpus compact-operator theorem then gives finite-dimensional
kernel and closed range. Self-adjointness gives finite-dimensional cokernel.
This applies to the actual quotient pencil throughout `0 ≤ λ < 1`.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

section
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- A compact error estimate makes the residual operator have finite kernel and closed range. -/
lemma cofinal_of_compact_energy_estimate (T : E →L[ℂ] E) (K : E →L[ℂ] G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u, ‖u‖^2 ≤ A*‖T u‖^2+B*‖K u‖^2) :
    HTGeometry.IsCofinalTransducer T := by
  apply HTGeometry.cofinalTransducer_of_compact_jointlyBoundedBelow K T hK
  let R := 1+max A 0+max B 0
  have hR : 0<R := by dsimp only [R]; positivity
  have hs : 0<Real.sqrt R := Real.sqrt_pos.mpr hR
  refine ⟨(Real.sqrt R)⁻¹,inv_pos.mpr hs,fun u => ?_⟩
  have ht : ‖T u‖^2 ≤ ‖(K.prod T) u‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (K u,T u)) 2
  have hk : ‖K u‖^2 ≤ ‖(K.prod T) u‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (K u,T u)) 2
  have he : ‖u‖^2 ≤ R*‖(K.prod T) u‖^2 := calc
    _ ≤ A*‖T u‖^2+B*‖K u‖^2 := hest u
    _ ≤ max A 0*‖T u‖^2+max B 0*‖K u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    _ ≤ max A 0*‖(K.prod T) u‖^2+max B 0*‖(K.prod T) u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left ht (le_max_right _ _))
        (mul_le_mul_of_nonneg_left hk (le_max_right _ _))
    _ ≤ R*‖(K.prod T) u‖^2 := by
      dsimp only [R]
      nlinarith only [sq_nonneg ‖(K.prod T) u‖]
  have hn : ‖u‖ ≤ Real.sqrt R*‖(K.prod T) u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hs.le (norm_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt hR.le] using he
  calc
    _ ≤ (Real.sqrt R)⁻¹*(Real.sqrt R*‖(K.prod T) u‖) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hs.le)
    _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ hs.ne',one_mul]

lemma selfAdjoint_range_eq_ker_orthogonal (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (hrange : IsClosed (Set.range T)) : T.range=T.kerᗮ := by
  have hh := T.orthogonal_ker
  rw [hT.adjoint_eq] at hh
  rw [hrange.submodule_topologicalClosure_eq] at hh
  exact hh.symm

omit [CompleteSpace G] in
lemma selfAdjoint_fredholm_of_compact_estimate (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (K : E →L[ℂ] G) (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u, ‖u‖^2 ≤ A*‖T u‖^2+B*‖K u‖^2) : HTGeometry.IsFredholmOp T := by
  obtain ⟨hrange,hfinite⟩ := cofinal_of_compact_energy_estimate T K hK A B hest
  letI : FiniteDimensional ℂ T.ker := hfinite
  letI : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  have hquot : FiniteDimensional ℂ (E ⧸ T.kerᗮ) :=
    (T.kerᗮ.quotientEquivOfIsCompl T.ker T.ker.isCompl_orthogonal.symm).symm.finiteDimensional
  refine ⟨hfinite,hrange,?_⟩
  rw [selfAdjoint_range_eq_ker_orthogonal T hT hrange]
  exact hquot

omit [CompleteSpace E] in
lemma ker_orthogonal_restriction_injective (T : E →L[ℂ] E) :
    Function.Injective (T.domRestrict T.kerᗮ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  apply Subtype.ext
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact T.ker.inner_right_of_mem_orthogonal hu u.2

end

def kernelSpectralFormOperator (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ContinuousLinearMap.id ℂ KernelEnergyGraph-
    (z+1)•(kernelEnergyMass.adjoint.comp kernelEnergyMass)

lemma kernelSpectralFormOperator_inner (z : ℂ) (u : KernelEnergyGraph) :
    inner ℂ u (kernelSpectralFormOperator z u)=
      ((‖kernelEnergyGradient u‖^2:ℝ):ℂ)-z*((‖kernelEnergyMass u‖^2:ℝ):ℂ) := by
  change inner ℂ u (u-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass u))=_
  rw [inner_sub_right,inner_smul_right u (kernelEnergyMass.adjoint (kernelEnergyMass u)) (z + 1),kernelEnergyMass.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelEnergyGraph_norm_sq,Complex.ofReal_add]
  ring

lemma kernelSpectralFormOperator_selfAdjoint (spectralParam : ℝ) :
    IsSelfAdjoint (kernelSpectralFormOperator (spectralParam:ℂ)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
  intro u
  have hh := kernelSpectralFormOperator_inner (spectralParam:ℂ) u
  have hr : inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u=
      (((‖kernelEnergyGradient u‖^2-spectralParam*‖kernelEnergyMass u‖^2):ℝ):ℂ) := by
    rw [←inner_conj_symm (𝕜 := ℂ) (kernelSpectralFormOperator (spectralParam:ℂ) u) u,hh]
    simp only [map_sub,map_mul,Complex.conj_ofReal,Complex.ofReal_sub,Complex.ofReal_mul]
  change (starRingEnd ℂ) (inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u)=
    inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u
  rw [hr,Complex.conj_ofReal]

lemma scalar_compact_energy_estimate (m g n t k spectralParam C : ℝ)
    (hspectralParam : 0≤ spectralParam) (hspectralParamone : spectralParam<1) (hC : 0≤C)
    (hspace : n^2=m^2+g^2) (hcore : m^2≤g^2+C*k^2)
    (hform : g^2-spectralParam*m^2≤n*t) :
    n^2≤(4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2 := by
  have hd : 0<1-spectralParam := sub_pos.mpr hspectralParamone
  have hlow : (1-spectralParam)/2*n^2≤n*t+C*k^2 := by
    rw [hspace]
    nlinarith only [hform,
      mul_nonneg (show 0≤1+spectralParam by linarith) (sub_nonneg.mpr hcore),
      mul_nonneg hd.le (mul_nonneg hC (sq_nonneg k))]
  have hlow' := mul_le_mul_of_nonneg_left hlow (show 0≤4*(1-spectralParam) by positivity)
  have hsq : (1-spectralParam)^2*n^2≤4*t^2+4*(1-spectralParam)*C*k^2 := by
    nlinarith only [hlow',sq_nonneg ((1-spectralParam)*n-2*t)]
  have he : (4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2=
      (4*t^2+4*(1-spectralParam)*C*k^2)/(1-spectralParam)^2 := by
    field_simp [hd.ne']
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr (by nlinarith only [hsq])

lemma kernelSpectralFormOperator_compact_estimate
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ) (hC : 0≤C)
    (hcore : ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
      C*‖kernelEnergyMassRestriction K hK u‖^2)
    (spectralParam : ℝ) (hspectralParam : 0≤ spectralParam) (hspectralParamone : spectralParam<1) (u : KernelEnergyGraph) :
    ‖u‖^2≤(4/(1-spectralParam)^2)*‖kernelSpectralFormOperator (spectralParam:ℂ) u‖^2+
      (4*C/(1-spectralParam))*‖kernelEnergyMassRestriction K hK u‖^2 := by
  apply scalar_compact_energy_estimate ‖kernelEnergyMass u‖ ‖kernelEnergyGradient u‖
    ‖u‖ ‖kernelSpectralFormOperator (spectralParam:ℂ) u‖ ‖kernelEnergyMassRestriction K hK u‖ spectralParam C
    hspectralParam hspectralParamone hC (kernelEnergyGraph_norm_sq u) (hcore u)
  have hh := re_inner_le_norm (𝕜 := ℂ) u (kernelSpectralFormOperator (spectralParam:ℂ) u)
  rw [kernelSpectralFormOperator_inner] at hh
  simpa only [RCLike.re_to_complex,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using hh

lemma kernelSpectralFormOperator_solution_graph (z : ℂ) (F : KernelQuotientL2)
    (v : KernelEnergyGraph) (hv : kernelSpectralFormOperator z v=kernelVariationalSolution F) :
    (kernelEnergyMass v,F+z•kernelEnergyMass v)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  have hh : v-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass v)=kernelEnergyMass.adjoint F := hv
  have hv' : kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v)=v := by
    rw [map_add,map_smul]
    exact (sub_eq_iff_eq_add.mp hh).symm
  have he : kernelEnergyMass v+(F+z•kernelEnergyMass v)=F+(z+1)•kernelEnergyMass v := by
    rw [add_smul,one_smul]
    abel
  rw [he]
  change kernelEnergyMass (kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v))=kernelEnergyMass v
  rw [hv']

lemma kernelSpectralFormOperator_of_domain (z : ℂ) (u : kernelEnergyLaplacian.domain) :
    kernelSpectralFormOperator z (kernelVariationalSolution (kernelEnergyLaplacian u+u))=
      kernelVariationalSolution (kernelEnergyLaplacian u-z•(u:KernelQuotientL2)) := by
  have hu : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  change kernelVariationalSolution (kernelEnergyLaplacian u+u)-
    (z+1)•kernelVariationalSolution (kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u)))=_
  rw [hu,←map_smul,←map_sub]
  congr 1
  rw [add_smul,one_smul]
  abel

theorem kernelSpectralFormOperator_isFredholm (spectralParam : ℝ)
    (hzero : 0≤ spectralParam) (hone : spectralParam<1) :
    HTGeometry.IsFredholmOp (kernelSpectralFormOperator (spectralParam:ℂ)) := by
  obtain ⟨K,hK,C,hC,hcompact,hcoercive⟩ := kernel_global_exterior_coercivity
  exact selfAdjoint_fredholm_of_compact_estimate _
    (kernelSpectralFormOperator_selfAdjoint spectralParam)
    (kernelEnergyMassRestriction K hK.measurableSet) hcompact
    (4/(1-spectralParam)^2) (4*C/(1-spectralParam))
    (kernelSpectralFormOperator_compact_estimate K hK.measurableSet C hC hcoercive spectralParam hzero hone)

theorem kernel_theta_spectral_fredholm :
    HTGeometry.IsFredholmOp (kernelSpectralFormOperator (8/9:ℂ)) := by
  convert kernelSpectralFormOperator_isFredholm (8/9) (by norm_num) (by norm_num) using 1
  norm_num

#print axioms kernelSpectralFormOperator_isFredholm
#print axioms kernel_theta_spectral_fredholm
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
