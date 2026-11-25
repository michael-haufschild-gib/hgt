import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Rational phase functions without poles on the physical time orbit -/

open MvPolynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.SpectralCoordinates
noncomputable section
variable {F : Type*} [Field F] [Algebra F ℂ]
variable {I T : Type*} (K : IntermediateField F ℂ) (z : T → I → ℂ)

/-- Quotients of phase polynomials whose denominator never vanishes
on this orbit. Both a unit phase and its inverse lie in the ring. -/
def phaseFunctionRing : Subring (T → ℂ) where
  carrier := {f | ∃ p q : MvPolynomial I K, ∀ t,
    aeval (z t) q≠0 ∧ f t*aeval (z t) q=aeval (z t) p}
  zero_mem' := ⟨0,1,fun t => by simp⟩
  one_mem' := ⟨1,1,fun t => by simp⟩
  neg_mem' := by
    rintro f ⟨p,q,h⟩
    exact ⟨-p,q,fun t => ⟨(h t).1,by simp only [Pi.neg_apply,neg_mul,(h t).2,map_neg]⟩⟩
  add_mem' := by
    rintro f g ⟨p,q,hf⟩ ⟨r,s,hg⟩
    refine ⟨p*s+r*q,q*s,fun t => ?_⟩
    simp only [map_mul,map_add,Pi.add_apply]
    refine ⟨mul_ne_zero (hf t).1 (hg t).1,?_⟩
    linear_combination (aeval (z t) s)*(hf t).2 + (aeval (z t) q)*(hg t).2
  mul_mem' := by
    rintro f g ⟨p,q,hf⟩ ⟨r,s,hg⟩
    refine ⟨p*r,q*s,fun t => ?_⟩
    simp only [map_mul,Pi.mul_apply]
    exact ⟨mul_ne_zero (hf t).1 (hg t).1,by rw [mul_mul_mul_comm,(hf t).2,(hg t).2]⟩

theorem constant_mem_phaseFunctionRing (a : K) : (fun _ : T => (a:ℂ))∈phaseFunctionRing K z :=
  ⟨C a,1,fun t => by simp⟩

theorem coordinate_mem_phaseFunctionRing (i : I) : (fun t => z t i)∈phaseFunctionRing K z :=
  ⟨X i,1,fun t => by simp⟩

theorem invCoordinate_mem_phaseFunctionRing (i : I) (hn : ∀ t, z t i≠0) :
    (fun t => (z t i)⁻¹)∈phaseFunctionRing K z :=
  ⟨1,X i,fun t => by simpa only [aeval_X,map_one] using And.intro (hn t) (inv_mul_cancel₀ (hn t))⟩

/-- At an algebraically independent phase point, evaluation detects
every nonzero member of the orbit's rational function ring. -/
theorem eval_zero_iff {f : T → ℂ} (hf : f∈phaseFunctionRing K z) {t : T}
    (ht : AlgebraicIndependent K (z t)) : f t=0 ↔ ∀ u, f u=0 := by
  obtain ⟨p,q,h⟩ := hf
  refine ⟨fun h0 u => ?_,fun h => h t⟩
  have hp : p=0 := ht (by rw [map_zero,←(h t).2,h0,zero_mul])
  exact (mul_eq_zero.mp ((h u).2.trans (hp ▸ map_zero _))).resolve_right (h u).1

#print axioms eval_zero_iff
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.SpectralCoordinates
