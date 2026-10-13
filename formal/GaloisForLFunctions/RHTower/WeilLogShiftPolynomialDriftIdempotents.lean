import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialBoundaryProfile
import GaloisForLFunctions.HTGeometry.FiniteLawZeroPattern
import GaloisForLFunctions.HTGeometry.FiniteNodePolynomialIdempotents

/-! # Exact algebraic classification of canonical logarithmic drift masks -/

namespace RHTower

open Filter GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped Topology

theorem finiteWeilCanonicalZeroMassPolynomial_idempotent
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) ∣
      (finiteWeilCanonicalZeroMassPolynomial r k Q) ^ 2 -
        finiteWeilCanonicalZeroMassPolynomial r k Q := by
  apply (finite_node_polynomial_idempotent_iff_values
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k) _).mpr
  intro i
  simpa only [finiteWeilCanonicalZeroMassPolynomial_eval_at_atom] using
    Q.zeroMassIndicator_eq_zero_or_one i

theorem finiteWeilCanonicalZeroMassPolynomial_ne_one
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    finiteWeilCanonicalZeroMassPolynomial r k Q ≠ 1 := by
  obtain ⟨i, hi⟩ := Q.exists_zeroMassIndicator_eq_zero
  intro h
  have hnode : (finiteWeilCanonicalZeroMassPolynomial r k Q).eval
      (finiteWeilCanonicalFluctuationPoint r k i 0) = 0 := by
    rw [finiteWeilCanonicalZeroMassPolynomial_eval_at_atom, hi]
  rw [h, Polynomial.eval_one] at hnode
  exact one_ne_zero hnode

theorem finiteWeilCanonicalZeroMassPolynomial_exists_iff
    (r k : ℕ) (p : Polynomial ℝ) :
    (∃ Q : Law (Fin (r + 1)), finiteWeilCanonicalZeroMassPolynomial r k Q = p) ↔
      p.degree < (r + 1 : ℕ) ∧
      Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) ∣
        p ^ 2 - p ∧ p ≠ 1 := by
  classical
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨finiteWeilCanonicalZeroMassPolynomial_degree_lt r k Q,
      finiteWeilCanonicalZeroMassPolynomial_idempotent r k Q,
      finiteWeilCanonicalZeroMassPolynomial_ne_one r k Q⟩
  · rintro ⟨hdegree, hidempotent, hne⟩
    have hvalues := (finite_node_polynomial_idempotent_iff_values
      (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
      (finiteWeilCanonicalFluctuationPoint_fst_injective r k) p).mp hidempotent
    have hzero : ∃ i, p.eval (finiteWeilCanonicalFluctuationPoint r k i 0) = 0 := by
      by_contra hnone
      push_neg at hnone
      apply hne
      apply (finite_node_polynomial_eq_one_iff
        (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
        (finiteWeilCanonicalFluctuationPoint_fst_injective r k) p
        (by simpa only [Fintype.card_fin] using hdegree)).mpr
      intro i
      exact (hvalues i).resolve_left (hnone i)
    obtain ⟨Q, hQ⟩ := (Law.exists_law_zeroMassIndicator_iff
      (fun i => p.eval (finiteWeilCanonicalFluctuationPoint r k i 0))).mpr ⟨hvalues, hzero⟩
    refine ⟨Q, ?_⟩
    have hp : p = Lagrange.interpolate Finset.univ
        (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
        (fun i => p.eval (finiteWeilCanonicalFluctuationPoint r k i 0)) :=
      (Lagrange.eq_interpolate_iff (s := Finset.univ) (f := p)
        (fun i => p.eval (finiteWeilCanonicalFluctuationPoint r k i 0))
        (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn).mp
        ⟨by simpa only [Finset.card_univ, Fintype.card_fin] using hdegree, fun _ _ => rfl⟩
    rw [finiteWeilCanonicalZeroMassPolynomial, hQ]
    exact hp.symm

/-- Classifies logarithmic coefficient drifts along the canonical uniform-mixture path. -/
theorem finiteWeilCanonicalApproximationPolynomial_exists_logarithmic_drift_iff
    (r k : ℕ) (p : Polynomial ℝ) :
    (∃ Q : Law (Fin (r + 1)), ∀ j : ℕ,
      Tendsto (fun n : ℕ => (finiteWeilCanonicalApproximationPolynomial r k Q n).coeff j /
        Real.log ((n : ℝ) + 1)) atTop (𝓝 (-p.coeff j))) ↔
      p.degree < (r + 1 : ℕ) ∧
      Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) ∣
        p ^ 2 - p ∧ p ≠ 1 := by
  rw [← finiteWeilCanonicalZeroMassPolynomial_exists_iff]
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    apply Polynomial.ext
    intro j
    exact neg_injective (tendsto_nhds_unique
      (tendsto_finiteWeilCanonicalApproximationPolynomial_coeff_div_log r k Q j) (hQ j))
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun j => ?_⟩
    simpa only [hQ] using
      tendsto_finiteWeilCanonicalApproximationPolynomial_coeff_div_log r k Q j

end RHTower
