import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.Rounding.OptimalSign
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.MarkedMass

/-! # Exact spectral-phase feasibility for a marked subspace of any rank -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections.Rounding
open StaticLocalLaboratoryComplexityGrowthLaw
open private diagonal_overlap from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryDiagonal
open private sign_norm from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.MarkedMass
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Energy levels with more than half their weight in the marked subspace. -/
def majority (V : unitaryGroup I ℂ) (M : Finset I) := univ.filter fun i => 1/2<rowWeight V M i

private theorem mark_self (M : Finset I) : star (diagonal (markSign M))=diagonal (markSign M) := by
  ext i j
  by_cases hij : i=j
  · subst j; by_cases hi : i∈M <;> simp [markSign,hi]
  · simp [hij,Ne.symm hij]

/-- The only real sign pattern that can improve a strict fit below √2
is read from the diagonal of the target reflection. -/
theorem majority_round (V : unitaryGroup I ℂ) (M : Finset I) (f : I → ℂ)
    (hf : ∀ i, ‖f i‖=1) (hs : ‖diagonal f-reflection V M‖^2<2) :
    ‖diagonal (markSign (majority V M))-reflection V M‖≤‖diagonal f-reflection V M‖ := by
  let W := reflection V M
  have hW : W∈unitary (Mat I) := mul_mem (mul_mem V.property
    (mem_unitaryGroup_diagonal_general _ (sign_norm M))) (Unitary.star_mem V.property)
  have hself : star W=W := by simp only [W,reflection,star_mul,star_star,mark_self,mul_assoc]
  have h := round_reflection (⟨W,hW⟩:unitaryGroup I ℂ) hself f hf hs
  have he (i : I) : side (f i)=markSign (majority V M) i := by
    have hb := diagonal_overlap f hf W hW i
    rw [show W i i=((1-2*rowWeight V M i:ℝ):ℂ) from reflection_diagonal V M i,
      Complex.conj_ofReal,mul_comm (f i),Complex.re_ofReal_mul] at hb
    change ‖diagonal f-W‖^2<2 at hs
    have hprod : 0<(1-2*rowWeight V M i)*(f i).re := by linarith only [hs,hb]
    by_cases hm : 1/2<rowWeight V M i
    · have hr : ¬0≤(f i).re := fun hr => hprod.not_ge (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hm]) hr)
      simp [side,markSign,majority,hm,hr]
    · have hr : 0≤(f i).re := by
        by_contra! hn
        exact hprod.not_ge (mul_nonpos_of_nonneg_of_nonpos (by linarith only [le_of_not_gt hm]) hn.le)
      simp [side,markSign,majority,hm,hr]
  simpa only [signs,he] using h

/-- At each closed tolerance the full torus test reduces to two explicit
candidates: the imaginary scalar and the spectral-majority reflection. -/
theorem marked_phase_fit_iff (V : unitaryGroup I ℂ) (M : Finset I) (e : ℝ) :
    (∃ f : I → ℂ, (∀ i, ‖f i‖=1) ∧ ‖diagonal f-reflection V M‖≤e) ↔
      Real.sqrt 2≤e ∨ ‖diagonal (markSign (majority V M))-reflection V M‖≤e := by
  constructor
  · rintro ⟨f,hf,hfit⟩
    by_cases hh : Real.sqrt 2≤e
    · exact Or.inl hh
    have hlt := hfit.trans_lt (lt_of_not_ge hh)
    have hsq := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 2)).mpr hlt
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at hsq
    exact Or.inr ((majority_round V M f hf hsq).trans hfit)
  · rintro (h|h)
    · exact ⟨fun _ => Complex.I,fun _ => Complex.norm_I,(imaginary_distance_le V M).trans h⟩
    · exact ⟨_,sign_norm _,h⟩

#print axioms marked_phase_fit_iff
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections.Rounding
