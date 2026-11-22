import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.EndpointForms

/-! # The spectral margin away from the two extremal phases -/
open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

def onPair (a b : I) (v : EuclideanSpace ℂ I) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun j => if j=a ∨ j=b then v j else 0)

theorem onPair_off (a b : I) (v : EuclideanSpace ℂ I) (j : I) (ha : j≠a) (hb : j≠b) :
    onPair a b v j = 0 := by simp [onPair,ha,hb]

/-- The norm lost by restricting to the endpoints is precisely the spectator mass. -/
theorem onPair_pythagoras (a b : I) (v : EuclideanSpace ℂ I) :
    ‖onPair a b v‖^2+‖v-onPair a b v‖^2=‖v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=a ∨ j=b <;> simp [onPair,h]

/-- A real-part margin γ at every spectator gives γ times its squared
mass as surplus in the real unitary overlap. -/
theorem spectator_surplus (u : I→ℂ) (a b : I) (y γ : ℝ) (hy : ∀ j, y≤(u j).re)
    (hg : ∀ j, j≠a → j≠b → y+γ≤(u j).re) (v : EuclideanSpace ℂ I) (hv : ‖v‖=1) :
    let U := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (diagonal u)
    y+γ*‖v-onPair a b v‖^2 ≤ (⟪U v,v⟫_ℂ).re := by
  intro U
  have hh (j : I) : γ*‖(v-onPair a b v) j‖^2 ≤ ((u j).re-y)*‖v j‖^2 := by
    by_cases h : j=a ∨ j=b
    · simpa [onPair,h] using mul_nonneg (sub_nonneg.mpr (hy j)) (sq_nonneg ‖v j‖)
    · obtain ⟨ha,hb⟩ := not_or.mp h
      have hm : γ≤(u j).re-y := by linarith only [hg j ha hb]
      simpa [onPair,h] using mul_le_mul_of_nonneg_right hm (sq_nonneg ‖v j‖)
  have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => hh j
  have hnorm : ∑ j, ‖v j‖^2=1 := by rw [←EuclideanSpace.norm_sq_eq,hv,one_pow]
  simp only [←Finset.mul_sum,sub_mul,Finset.sum_sub_distrib,←EuclideanSpace.norm_sq_eq (v-onPair a b v)] at hs
  rw [hnorm,mul_one] at hs
  rw [diagonal_overlap u v]
  linarith only [hs]

#print axioms spectator_surplus
end
end GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
