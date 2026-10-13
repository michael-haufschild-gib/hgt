import GaloisForLFunctions.RHTower.WeilLogShiftFinitePolynomialInterpolation
import GaloisForLFunctions.HTGeometry.AtomicProbabilityTilt

/-! # Polynomial tilts realize exactly positive laws on canonical finite support -/

namespace RHTower

open MeasureTheory
open GaloisForLFunctions.HTGeometry.FourierLLogL

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Canonical polynomial potential for the target-to-base log density. -/
def finiteWeilCanonicalLogDensityPolynomial (r k : ℕ) (Q : Law (Fin (r + 1))) :
    Polynomial ℝ :=
  Lagrange.interpolate Finset.univ
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (fun i => Real.log (Q i / finiteWeilCanonicalEdgeMass r k i))

theorem finiteWeilCanonicalLogDensityPolynomial_degree_lt
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    (finiteWeilCanonicalLogDensityPolynomial r k Q).degree < (r + 1 : ℕ) := by
  simpa only [finiteWeilCanonicalLogDensityPolynomial, Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ)
      (v := fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
      (fun i => Real.log (Q i / finiteWeilCanonicalEdgeMass r k i))
      (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn

theorem finiteWeilCanonicalLogDensityPolynomial_eval_at_atom
    (r k : ℕ) (Q : Law (Fin (r + 1))) (i : Fin (r + 1)) :
    (finiteWeilCanonicalLogDensityPolynomial r k Q).eval
      (finiteWeilCanonicalFluctuationPoint r k i 0) =
      Real.log (Q i / finiteWeilCanonicalEdgeMass r k i) :=
  Lagrange.eval_interpolate_at_node (s := Finset.univ)
    (v := fun j => finiteWeilCanonicalFluctuationPoint r k j 0)
    (fun j => Real.log (Q j / finiteWeilCanonicalEdgeMass r k j))
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn (Finset.mem_univ i)

theorem finiteWeilCanonicalLogDensityPolynomial_tilt_eq_atomic_of_pos
    (r k : ℕ) (Q : Law (Fin (r + 1))) (hQ : ∀ i, 0 < Q i) :
    (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
      (fun z => (finiteWeilCanonicalLogDensityPolynomial r k Q).eval (z 0)) =
      (Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E) := by
  change ((finiteWeilCanonicalEdgeLaw r k).atomicProbability
    (finiteWeilCanonicalFluctuationPoint r k) : Measure E).tilted _ = _
  apply Law.atomicProbability_tilted_eq_of_weight_exp
  intro i
  change finiteWeilCanonicalEdgeMass r k i *
    Real.exp ((finiteWeilCanonicalLogDensityPolynomial r k Q).eval
      (finiteWeilCanonicalFluctuationPoint r k i 0)) = Q i
  rw [finiteWeilCanonicalLogDensityPolynomial_eval_at_atom,
    Real.exp_log (div_pos (hQ i) (finiteWeilCanonicalEdgeMass_pos r k i)),
    mul_comm, div_mul_cancel₀ _ (finiteWeilCanonicalEdgeMass_pos r k i).ne']

/-- The exact image of bounded-degree real polynomial tilts is the positive simplex. -/
theorem finiteWeilCanonicalJointProbabilityLaw_exists_polynomial_tilt_iff
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    (∃ p : Polynomial ℝ, p.degree < (r + 1 : ℕ) ∧
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => p.eval (z 0)) =
        (Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E)) ↔
    ∀ i, 0 < Q i := by
  constructor
  · rintro ⟨p, _, heq⟩
    exact Law.pos_of_atomicProbability_tilted_eq
      (finiteWeilCanonicalEdgeLaw r k) Q (finiteWeilCanonicalFluctuationPoint r k)
      (fun i j hij => finiteWeilCanonicalFluctuationPoint_fst_injective r k
        (congrArg (fun z : E => z 0) hij))
      (fun i => finiteWeilCanonicalEdgeMass_pos r k i) (fun z : E => p.eval (z 0)) heq
  · intro hQ
    exact ⟨finiteWeilCanonicalLogDensityPolynomial r k Q,
      finiteWeilCanonicalLogDensityPolynomial_degree_lt r k Q,
      finiteWeilCanonicalLogDensityPolynomial_tilt_eq_atomic_of_pos r k Q hQ⟩

end

end RHTower
