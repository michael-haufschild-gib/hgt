/-
Initial resolvent matching adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicIncomingResidue
import GaloisForLFunctions.MetaplecticMobiusDescent.BoundedCubicRemainderGradient
import GaloisForLFunctions.MetaplecticMobiusDescent.BoundedSmoothCubicOperatorDomain

/-!
# The resolvent correction equals the actual incoming remainder

For `Re s>4`, the Eisenstein series minus its smooth incoming seed has
bounded mass and hyperbolic gradient. Its explicit coordinate equation
therefore holds in the actual operator graph. Nonreal resolvent uniqueness
identifies it with the constructed correction, giving an initial open
region where the meromorphic construction agrees with the source series.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def kernelEisensteinRemainderL2 (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) : KernelQuotientL2 :=
  (kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs).toLp
    (kernelEisensteinRemainder a b s (by linarith))

lemma kernelEisensteinRemainderL2_ae (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    kernelEisensteinRemainderL2 a b ha hab s hs=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelEisensteinRemainder a b s (by linarith) :=
  (kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs).coeFn_toLp

theorem kernelEisensteinRemainder_energy (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃u : KernelEnergyGraph,kernelEnergyMass u=kernelEisensteinRemainderL2 a b ha hab s hs := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  have hgrad' : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G := hgrad
  have hgL := kernelFunctionGradient_memLp f hf G hG hgrad'
  obtain ⟨u,hu,hgu⟩ := kernel_bounded_smooth_energy_exists f hf hfL hgL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad'
  exact ⟨u,hu⟩

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold Matrix

lemma axis_update_contDiff (p : SpatialCoordinates) (j : Fin 3) :
    ContDiff ℝ ∞ (fun t => Function.update p j t) := by
  apply contDiff_pi.mpr
  intro k
  by_cases h : k=j
  · subst k
    simpa only [Function.update_self,id_eq] using! (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t))
  · simpa only [Function.update_of_ne h] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => p k))

lemma smooth_positive_axis_regular (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice f p j) (p j) ∧
      DifferentiableAt ℝ (deriv (axisSlice f p j)) (p j) := by
  have hh : ContDiffAt ℝ ∞ (axisSlice f p j) (p j) := by
    have hfp : ContDiffAt ℝ ∞ f (Function.update p j (p j)) := by
      simpa only [Function.update_eq_self] using hf p hp
    have h := hfp.comp (p j) (axis_update_contDiff p j).contDiffAt
    simpa only [axisSlice,Function.comp_def,Function.update_eq_self] using! h
  exact ⟨hh.differentiableAt (by simp),(hh.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma axisLaplacian_sub_smooth (f g : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ ContDiffAt ℝ ∞ f p) (hg : ∀p,0<p 2→ ContDiffAt ℝ ∞ g p)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => f q-g q) p=axisLaplacian f p-axisLaplacian g p := by
  let F : Fin 2→SpatialCoordinates→ℂ:=![f,fun q => (-1:ℂ)*g q]
  have hF : ∀i : Fin 2,∀q,0<q 2→ ContDiffAt ℝ ∞ (F i) q := by
    intro i q hq
    fin_cases i
    · exact hf q hq
    · exact contDiffAt_const.mul (hg q hq)
  have hh := axisLaplacian_finset_sum Finset.univ F
    (fun i hi q hq j => smooth_positive_axis_regular (F i) (hF i) q hq j) p hp
  have he : (fun q => ∑i : Fin 2,F i q)=(fun q => f q-g q) := by
    funext q
    simp [F,Fin.sum_univ_two,sub_eq_add_neg]
  rw [he] at hh
  simp only [Fin.sum_univ_two,F,Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  rw [axisLaplacian_const_mul] at hh
  simpa only [neg_one_mul,sub_eq_add_neg] using hh

lemma eisensteinRemainder_coordinate_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (eisensteinRemainderField a b s) p=
      smoothCuspSeedDefectField a b s p+s*(2-s)*eisensteinRemainderField a b s p := by
  have hD := actual_smoothCuspSeed_laplace_defect a b s ha hab p hp
  unfold eisensteinRemainderField
  rw [axisLaplacian_sub_smooth _ _ (smoothEisenstein_contDiffAt s hs)
    (actual_smoothCuspSeed_contDiffAt a b s ha hab) p hp,smoothEisenstein_eigenfunction s hs p hp]
  linear_combination hD

lemma kernelQuotientDefect_euclidean_eq (a b : ℝ) (s : ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelQuotientDefect a b s (kernelEuclideanProjection p)=smoothCuspSeedDefectField a b s p.ofLp := by
  unfold kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp]
  change smoothCuspSeedDefect a b s _=smoothCuspSeedDefectField a b s p.ofLp
  rw [smoothCuspSeedDefectField,dif_pos hp]
  simp only [mul_comm Complex.I]

theorem kernelEisensteinRemainder_operator_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian (kernelFunctionField (kernelEisensteinRemainder a b s hs)) p=
      kernelQuotientDefect a b s (kernelEuclideanProjection p)+
        kernelEisensteinSpectralParameter s*kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p) := by
  let f := kernelFunctionField (kernelEisensteinRemainder a b s hs)
  have hf : ∀q,0<q 2→ ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s hs
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s hs (WithLp.toLp 2 q) hq
  rw [positiveEuclideanLaplacian_eq_axis f hf p hp,
    axisLaplacian_congr_positive _ _ he p.ofLp hp,
    eisensteinRemainder_coordinate_equation a b ha hab s hs p.ofLp hp,
    kernelQuotientDefect_euclidean_eq a b s p hp,kernelEisensteinRemainder_euclidean_eq a b s hs p hp]
  rfl

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

theorem kernelEisensteinRemainderL2_graph (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    (kernelEisensteinRemainderL2 a b ha hab s hs,
      kernelL2Defect a b (by linarith) hab s+kernelEisensteinSpectralParameter s •
        kernelEisensteinRemainderL2 a b ha hab s hs)∈kernelEnergyLaplacian.graph := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  let A : KernelQuotient→ℂ := fun q => kernelQuotientDefect a b s q+
    kernelEisensteinSpectralParameter s*f q
  have hD := kernelQuotientDefect_memLp a b s (by linarith) hab
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    hD.add (hfL.const_smul (kernelEisensteinSpectralParameter s))
  have hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p) := by
    intro p hp
    exact kernelEisensteinRemainder_operator_equation a b ha hab s (by linarith) p hp
  have hgraph := kernel_bounded_smooth_operator_graph f hf hfL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad A hA hEq
  have hAL : hA.toLp A=kernelL2Defect a b (by linarith) hab s+
      kernelEisensteinSpectralParameter s • kernelEisensteinRemainderL2 a b ha hab s hs := by
    exact (hD.toLp_add (hfL.const_smul (kernelEisensteinSpectralParameter s))).trans
      (congrArg (fun x => hD.toLp (kernelQuotientDefect a b s)+x)
        (hfL.toLp_const_smul (kernelEisensteinSpectralParameter s)))
  rw [hAL] at hgraph
  exact hgraph

theorem kernelEisensteinL2Correction_eq_remainder (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelEisensteinL2Correction a b (by linarith) hab s=
      kernelEisensteinRemainderL2 a b ha hab s hs := by
  exact kernelEisensteinL2Correction_unique a b (by linarith) hab s
    (kernelSpectralFormOperator_isUnit_nonreal _
      (kernelEisensteinSpectralParameter_nonreal s (by linarith) (by linarith)))
    _ (kernelEisensteinRemainderL2_graph a b ha hab s hs)

theorem kernelEisensteinL2Correction_initial_overlap (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelEisensteinL2Correction a b (by linarith) hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q := by
  rw [kernelEisensteinL2Correction_eq_remainder a b ha hab s hs hi]
  exact kernelEisensteinRemainderL2_ae a b ha hab s hs


#print axioms kernelEisensteinRemainderL2_graph
#print axioms kernelEisensteinL2Correction_initial_overlap
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
