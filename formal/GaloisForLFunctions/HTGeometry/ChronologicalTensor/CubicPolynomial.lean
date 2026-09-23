import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicInvariantSpace
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Faithful polynomial coordinates on the cubic physical section

The first decay eigenmode and middle gap are algebraically independent as
actual functions on the physical section. Two infinite-root arguments prove
faithfulness, using a two-parameter family of physical probes. The polynomial
variables map to the three decay modes without extra algebraic assumptions.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicTriangleProbe (t x : ℝ) : Fin 5 → ℝ :=
  ![(1-t+x)/2,0,t,0,(1-t-x)/2]

theorem cubicTriangleProbe_section : ∀ t ∈ Ioo (0:ℝ) 1,
    MapsTo (cubicTriangleProbe t) (Ioo 0 (1-t)) cubicProbeSection := by
  intro t ht x hx
  rcases ht with ⟨ht0,ht1⟩
  rcases hx with ⟨hx0,hx1⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> simp [cubicTriangleProbe] <;> linarith
  all_goals simp [cubicTriangleProbe] <;> ring

theorem cubicTriangleProbe_middle (t x : ℝ) : (cubicTriangleProbe t x) 2=t := rfl

theorem cubicTriangleProbe_mode (t x : ℝ) :
    cubicDecayMode 0 (cubicTriangleProbe t x)=t*(1-x^(2 : ℕ))/4 := by
  change t*(1-((1-t+x)/2-(1-t-x)/2)^(2 : ℕ))/4=t*(1-x^(2 : ℕ))/4
  ring

theorem cubicTriangleCoordinate_injective (t : Ioo (0:ℝ) 1) :
    InjOn (fun x => t.val*(1-x^(2 : ℕ))/4) (Ioo 0 (1-t.val)) := by
  intro x hx y hy he
  have ht : t.val ≠ 0 := ne_of_gt t.property.1
  have hprod : t.val*(x^(2 : ℕ)-y^(2 : ℕ))=0 := by linear_combination -4*he
  have hsq := (mul_eq_zero.mp hprod).resolve_left ht
  have hfac : (x-y)*(x+y)=0 := by nlinarith only [hsq]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith [hx.1,hy.1]

theorem cubicTriangleCoordinate_infinite (t : Ioo (0:ℝ) 1) :
    ((fun x => t.val*(1-x^(2 : ℕ))/4) '' Ioo 0 (1-t.val)).Infinite := by
  apply (Set.infinite_image_iff (cubicTriangleCoordinate_injective t)).mpr
  exact Set.Ioo_infinite (by linarith [t.property.2])

def cubicPolynomialObservation : Polynomial (Polynomial ℝ) →ₐ[ℝ] (cubicProbeSection → ℝ) where
  toRingHom := RingHom.pi (fun g =>
    Polynomial.eval₂RingHom (Polynomial.evalRingHom (cubicDecayMode 0 g.val)) (g.val 2))
  commutes' r := by
    ext g
    change Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 g.val)) (g.val 2)
      (Polynomial.C (Polynomial.C r))=r
    simp

theorem cubicPolynomialObservation_zero_iff (P : Polynomial (Polynomial ℝ)) :
    cubicPolynomialObservation P=0 ↔ P=0 := by
  constructor
  · intro hP
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hC : ((Polynomial.C : ℝ → Polynomial ℝ) '' Ioo 0 1).Infinite := by
      apply (Set.infinite_image_iff Polynomial.C_injective.injOn).mpr
      exact Set.Ioo_infinite zero_lt_one
    apply hC.mono
    rintro z ⟨t,ht,rfl⟩
    change Polynomial.eval (Polynomial.C t) P=0
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (cubicTriangleCoordinate_infinite ⟨t,ht⟩).mono
    rintro y ⟨x,hx,rfl⟩
    let g : cubicProbeSection := ⟨cubicTriangleProbe t x,cubicTriangleProbe_section t ht hx⟩
    have he := congrFun hP g
    change Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 (cubicTriangleProbe t x)))
      ((cubicTriangleProbe t x) 2) P=0 at he
    rw [cubicTriangleProbe_mode,cubicTriangleProbe_middle] at he
    have h := Polynomial.eval₂_hom (p := P)
      (Polynomial.evalRingHom (t*(1-x^(2 : ℕ))/4)) (Polynomial.C t)
    simp only [Polynomial.coe_evalRingHom,Polynomial.eval_C] at h
    exact h.symm.trans he
  · rintro rfl
    exact map_zero _

theorem cubicPolynomialObservation_injective : Function.Injective cubicPolynomialObservation := by
  intro P Q h
  have hz : cubicPolynomialObservation (P-Q)=0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp ((cubicPolynomialObservation_zero_iff (P-Q)).mp hz)

theorem cubicPolynomialObservation_middle :
    cubicPolynomialObservation Polynomial.X=(fun g => g.val 2) := by
  ext g
  change Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 g.val)) (g.val 2) Polynomial.X=g.val 2
  simp

theorem cubicPolynomialObservation_firstMode :
    cubicPolynomialObservation (Polynomial.C Polynomial.X)=(fun g => cubicDecayMode 0 g.val) := by
  ext g
  change Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 g.val)) (g.val 2)
    (Polynomial.C Polynomial.X)=cubicDecayMode 0 g.val
  simp

theorem cubicPolynomialObservation_secondMode :
    cubicPolynomialObservation (Polynomial.X^(2 : ℕ))=(fun g => cubicDecayMode 1 g.val) := by
  rw [map_pow,cubicPolynomialObservation_middle]
  rfl

theorem cubicPolynomialObservation_thirdMode :
    cubicPolynomialObservation (Polynomial.X^(3 : ℕ))=(fun g => cubicDecayMode 2 g.val) := by
  rw [map_pow,cubicPolynomialObservation_middle]
  rfl

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
