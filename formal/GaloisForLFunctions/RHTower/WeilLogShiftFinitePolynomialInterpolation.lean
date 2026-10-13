import GaloisForLFunctions.RHTower.WeilLogShiftFinitePolynomialQuotient

/-! Every actual finite observable has a unique polynomial representative of degree below support size. -/

open MeasureTheory
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_polynomial_representative_iff
    (r k : ℕ) (a b d : ℝ) (f : E → ℝ) (p : Polynomial ℝ) :
    (p.degree < (r + 1 : ℕ) ∧
      ∀ᵐ z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E), p.eval (z 0) = f z) ↔
        p = Lagrange.interpolate Finset.univ
          (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
          (fun i => f (finiteWeilCanonicalFluctuationPoint r k i)) := by
  rw [finiteWeilCanonicalJointQuadraticTilt_ae_iff]
  simpa using Lagrange.eq_interpolate_iff (s := Finset.univ) (f := p)
    (fun i => f (finiteWeilCanonicalFluctuationPoint r k i))
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn

theorem finiteWeilCanonicalJointQuadraticTilt_existsUnique_polynomial_representative
    (r k : ℕ) (a b d : ℝ) (f : E → ℝ) :
    ∃! p : Polynomial ℝ, p.degree < (r + 1 : ℕ) ∧
      ∀ᵐ z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E), p.eval (z 0) = f z := by
  refine ⟨Lagrange.interpolate Finset.univ
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (fun i => f (finiteWeilCanonicalFluctuationPoint r k i)), ?_, ?_⟩
  · exact (finiteWeilCanonicalJointQuadraticTilt_polynomial_representative_iff
      r k a b d f _).mpr rfl
  · intro p hp
    exact (finiteWeilCanonicalJointQuadraticTilt_polynomial_representative_iff
      r k a b d f p).mp hp

theorem finiteWeilCanonicalJointQuadraticTilt_observable_ae_eq_iff_interpolate_eq
    (r k : ℕ) (a b d : ℝ) (f g : E → ℝ) :
    (∀ᵐ z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E), f z = g z) ↔
      Lagrange.interpolate Finset.univ
        (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
        (fun i => f (finiteWeilCanonicalFluctuationPoint r k i)) =
      Lagrange.interpolate Finset.univ
        (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
        (fun i => g (finiteWeilCanonicalFluctuationPoint r k i)) := by
  rw [finiteWeilCanonicalJointQuadraticTilt_ae_iff]
  simpa using (Lagrange.interpolate_eq_iff_values_eq_on (s := Finset.univ)
    (fun i => f (finiteWeilCanonicalFluctuationPoint r k i))
    (fun i => g (finiteWeilCanonicalFluctuationPoint r k i))
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn).symm

end RHTower
