import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.EndpointForms
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.UnitaryDescent
import GaloisForLFunctions.HTGeometry.Quantum.CoefficientMassLieProduct
import GaloisForLFunctions.HTGeometry.SelfAdjointPropagator

/-! # Strict improvement by a Hermitian observable at simple arc endpoints -/
open Matrix NormedSpace Metric Real
open scoped Matrix.Norms.L2Operator InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where
local instance : NormedAlgebra ℚ (Mat I) := .restrictScalars ℚ ℂ _

/-- An observable with opposite, positive and negative endpoint
expectations after centering moves a genuine unitary gate strictly
inside the projective error bound. -/
theorem spectral_descent (u : I → ℂ) (hu : Matrix.diagonal u ∈ unitary (Mat I))
    (a b : I) (hab : a ≠ b) (hb : u b=star (u a)) (hs : 0 < (u a).im)
    {ε : ℝ} (hε : 0 < ε) (hbase : (u a).re=1-ε^2/2)
    (hint : ∀ j, j≠a → j≠b → (u a).re < (u j).re)
    (A : Mat I) (hA : A.IsHermitian) {d : ℝ} (hd : 0 < d)
    (haA : A a a=(d:ℂ)) (hbA : A b b=-(d:ℂ)) :
    ∃ t > (0:ℝ), ‖Matrix.diagonal u-exp (t • (Complex.I • A))‖ < ε := by
  let Φ := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
  let K := Complex.I • A
  let V (t : ℝ) := exp (t • K)
  have hsk : K ∈ skewAdjoint (Mat I) := by
    rw [skewAdjoint.mem_iff,show star K=star Complex.I • star A from star_smul _ _]
    rw [show star A=A from hA.eq]
    simp [K]
  have hV (t) : V t ∈ unitary (Mat I) := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hsk)
  let j := Classical.choice (inferInstance : Nonempty I)
  letI : Nonempty (sphere (0 : EuclideanSpace ℂ I) 1) :=
    ⟨⟨PiLp.single 2 j (1:ℂ),mem_sphere_zero_iff_norm.mpr (by simp)⟩⟩
  have hr (t : ℝ) : ‖Φ (V t)-ContinuousLinearMap.id ℂ _-(t:ℂ) • Φ K‖ ≤ (‖K‖^2/2)*t^2 := by
    have hh : ‖V t-(1+t • K)‖ ≤ ‖K‖^2*|t|^2/2 := by
      simpa [V,cstarExponentialTaylor_one] using norm_exp_sub_cstarExponentialTaylor_le K hsk 1 t
    have he : Φ (V t)-ContinuousLinearMap.id ℂ _-(t:ℂ) • Φ K=Φ (V t-(1+t • K)) := by
      have hone : Φ 1=ContinuousLinearMap.id ℂ _ := map_one Φ
      have hscale : Φ (t • K)=(t:ℂ) • Φ K := by
        rw [←Complex.coe_smul t K]
        exact map_smul Φ (t:ℂ) K
      rw [map_sub,map_add,hone,hscale,sub_add_eq_sub_sub]
    rw [he,Matrix.l2_opNorm_toEuclideanCLM]
    rw [sq_abs] at hh
    linarith only [hh]
  have hu' (v) : ‖Φ (Matrix.diagonal u) v‖=‖v‖ := norm_apply_of_mem_unitary (Unitary.map_mem Φ hu) v
  have hv' (t v) : ‖Φ (V t) v‖=‖v‖ := norm_apply_of_mem_unitary (Unitary.map_mem Φ (hV t)) v
  have hmin (k : I) : (u a).re ≤ (u k).re := by
    by_cases he : k=a
    · rw [he]
    by_cases he' : k=b
    · rw [he',hb]; simp
    exact (hint k he he').le
  have hm (v : EuclideanSpace ℂ I) (hv : ‖v‖=1) := endpoint_mass u v hv (u a).re hmin
  obtain ⟨t,ht,he⟩ := unitary_descent (Φ (Matrix.diagonal u)) (Φ K) (fun t => Φ (V t))
    hε (by positivity) hu' hv' hr (fun v hv => hbase ▸ (hm v hv).1) (by
      intro v hv hzero
      have hz := (hm v hv).2 (hzero.trans hbase.symm)
      apply endpoint_variation u A a b hab hb hs hd haA hbA _ v hv (fun k hka hkb => hz k (hint k hka hkb))
      exact (hA.apply b a).symm)
  refine ⟨t,ht,?_⟩
  have he' : ‖Φ (Matrix.diagonal u-V t)‖ < ε := by rwa [map_sub]
  exact he'

#print axioms spectral_descent
end
end GaloisForLFunctions.HTGeometry.FirstGate
