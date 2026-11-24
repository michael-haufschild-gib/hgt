import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import GaloisForLFunctions.HTGeometry.SortedEigenbranchAnalytic

/-! # The mixed change of ordered energies across two weak couplings -/

open Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry.WeakBonds.Products
noncomputable section

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- In a neighborhood of an analytic germ, the four-corner remainder
is bounded by the product of the two displacement norms. -/
theorem local_rectangle {f : A → B} {a : A} (ha : AnalyticAt ℝ f a) :
    ∃ r > 0, ∃ C ≥ (0:ℝ), ∀ x u v : A,
      x ∈ ball a r → x+u ∈ ball a r → x+v ∈ ball a r → x+v+u ∈ ball a r →
      ‖f (x+v+u)-f (x+v)-f (x+u)+f x‖ ≤ C*‖u‖*‖v‖ := by
  obtain ⟨K,U,hU,hK⟩ := (ha.fderiv.contDiffAt : ContDiffAt ℝ 1 (fderiv ℝ f) a).exists_lipschitzOnWith
  have hb : U ∩ {z | AnalyticAt ℝ f z} ∈ 𝓝 a := inter_mem hU ha.eventually_analyticAt
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hb
  refine ⟨r,hr,K,K.coe_nonneg,?_⟩
  intro x u v h₀ hu hv huv
  have line {b : A} (hb : b∈ball a r) (hbv : b+v∈ball a r) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
      b+s•v∈ball a r := by
    simpa only [add_sub_cancel_left] using (convex_ball a r).add_smul_sub_mem hb hbv hs
  let g (s : ℝ) := f (x+s•v+u)-f (x+s•v)
  let d (s : ℝ) := (fderiv ℝ f (x+s•v+u)-fderiv ℝ f (x+s•v)) v
  have path {s : ℝ} (ht : s∈Icc (0:ℝ) 1) :
      x+s•v∈ball a r ∧ x+s•v+u∈ball a r := by
    refine ⟨line h₀ hv ht,?_⟩
    have h₁ : (x+u)+v ∈ ball a r := by rwa [add_right_comm x u]
    simpa only [add_right_comm x u] using line hu h₁ ht
  have deriv (s : ℝ) (ht : s∈Icc (0:ℝ) 1) : HasDerivAt g (d s) s := by
    obtain ⟨h₁,h₂⟩ := path ht
    have h : HasDerivAt (fun t : ℝ => x+t•v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    have he := ((hs h₂).2.differentiableAt.hasFDerivAt.comp_hasDerivAt s (h.add_const u)).sub
      ((hs h₁).2.differentiableAt.hasFDerivAt.comp_hasDerivAt s h)
    exact he
  have bound (s : ℝ) (ht : s∈Icc (0:ℝ) 1) : ‖d s‖≤K*‖u‖*‖v‖ := by
    obtain ⟨h₁,h₂⟩ := path ht
    have h := hK.dist_le_mul _ (hs h₂).1 _ (hs h₁).1
    rw [dist_eq_norm,dist_eq_norm,add_sub_cancel_left] at h
    exact (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right h (norm_nonneg v))
  have h := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s ht => (deriv s ht).hasDerivWithinAt) bound (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  simp only [g,one_smul,zero_smul,add_zero,sub_zero,norm_one,mul_one] at h
  convert h using 1
  congr 1
  abel

/-- All sorted energy levels share one neighborhood and one quadratic
remainder bound at any simple Hermitian ensemble member. -/
theorem sorted_rectangle {m D : ℕ} {P : Fin m → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ i, (P i).IsHermitian) {a : Fin m→ℝ} 
    (ha : Function.Injective (isHermitian_spectralEnsembleMatrix hP a).eigenvalues) :
    ∃ r > 0, ∃ C ≥ (0:ℝ), ∀ x u v : Fin m→ℝ,
      x ∈ ball a r → x+u ∈ ball a r → x+v ∈ ball a r → x+v+u ∈ ball a r →
      ‖sortedEnsembleSpectrum hP (x+v+u)-sortedEnsembleSpectrum hP (x+v)-
        sortedEnsembleSpectrum hP (x+u)+sortedEnsembleSpectrum hP x‖ ≤ C*‖u‖*‖v‖ :=
  local_rectangle (AnalyticAt.pi (analyticAt_sortedEnsembleSpectrum hP ha))

#print axioms sorted_rectangle
end
end GaloisForLFunctions.HTGeometry.WeakBonds.Products
