import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialTiltApproximation
import GaloisForLFunctions.HTGeometry.FiniteLawBoundaryLogProfile
import GaloisForLFunctions.HTGeometry.FinitePolynomialInterpolationLimits

/-! # The zero-weight pattern determines the logarithmic polynomial boundary direction -/

namespace RHTower

open Filter GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped Topology

noncomputable def finiteWeilCanonicalZeroMassPolynomial
    (r k : ℕ) (Q : Law (Fin (r + 1))) : Polynomial ℝ :=
  Lagrange.interpolate Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    Q.zeroMassIndicator

noncomputable def finiteWeilCanonicalBoundaryLogPolynomial
    (r k : ℕ) (Q : Law (Fin (r + 1))) : Polynomial ℝ :=
  Lagrange.interpolate Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (Q.boundaryLogValue (finiteWeilCanonicalEdgeMass r k))

theorem finiteWeilCanonicalZeroMassPolynomial_eval_at_atom
    (r k : ℕ) (Q : Law (Fin (r + 1))) (i : Fin (r + 1)) :
    (finiteWeilCanonicalZeroMassPolynomial r k Q).eval
      (finiteWeilCanonicalFluctuationPoint r k i 0) = Q.zeroMassIndicator i :=
  Lagrange.eval_interpolate_at_node (s := Finset.univ)
    (v := fun j => finiteWeilCanonicalFluctuationPoint r k j 0) Q.zeroMassIndicator
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn (Finset.mem_univ i)

theorem finiteWeilCanonicalZeroMassPolynomial_degree_lt
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    (finiteWeilCanonicalZeroMassPolynomial r k Q).degree < (r + 1 : ℕ) := by
  simpa only [finiteWeilCanonicalZeroMassPolynomial, Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ)
      (v := fun i => finiteWeilCanonicalFluctuationPoint r k i 0) Q.zeroMassIndicator
      (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn

theorem finiteWeilCanonicalBoundaryLogPolynomial_degree_lt
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    (finiteWeilCanonicalBoundaryLogPolynomial r k Q).degree < (r + 1 : ℕ) := by
  simpa only [finiteWeilCanonicalBoundaryLogPolynomial, Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ)
      (v := fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
      (Q.boundaryLogValue (finiteWeilCanonicalEdgeMass r k))
      (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn

theorem finiteWeilCanonicalZeroMassPolynomial_eq_zero_iff
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    finiteWeilCanonicalZeroMassPolynomial r k Q = 0 ↔ ∀ i, 0 < Q i := by
  classical
  constructor
  · intro hzero i
    by_contra hpos
    have hi : Q i = 0 := le_antisymm (le_of_not_gt hpos) (Q.nonneg i)
    have hnode : Q.zeroMassIndicator i = 0 := by
      rw [← finiteWeilCanonicalZeroMassPolynomial_eval_at_atom r k Q i, hzero,
        Polynomial.eval_zero]
    simp only [Law.zeroMassIndicator, hi, if_pos, one_ne_zero] at hnode
  · intro hpos
    have hzero : Q.zeroMassIndicator = (0 : Fin (r + 1) → ℝ) := by
      funext i
      simp only [Law.zeroMassIndicator, (hpos i).ne', if_false, Pi.zero_apply]
    rw [finiteWeilCanonicalZeroMassPolynomial, hzero, map_zero]

theorem finiteWeilCanonicalApproximationPolynomial_eval_atBot_iff
    (r k : ℕ) (Q : Law (Fin (r + 1))) (i : Fin (r + 1)) :
    Tendsto (fun n : ℕ => (finiteWeilCanonicalApproximationPolynomial r k Q n).eval
      (finiteWeilCanonicalFluctuationPoint r k i 0)) atTop atBot ↔ Q i = 0 := by
  simpa only [finiteWeilCanonicalApproximationPolynomial,
    finiteWeilCanonicalLogDensityPolynomial_eval_at_atom] using
      Law.tendsto_uniformApproximation_log_atBot_iff Q (finiteWeilCanonicalEdgeMass r k) i
        (finiteWeilCanonicalEdgeMass_pos r k i)

theorem tendsto_finiteWeilCanonicalApproximationPolynomial_renormalized_eval
    (r k : ℕ) (Q : Law (Fin (r + 1))) (x : ℝ) :
    Tendsto (fun n : ℕ => (finiteWeilCanonicalApproximationPolynomial r k Q n).eval x +
      Real.log ((n : ℝ) + 1) * (finiteWeilCanonicalZeroMassPolynomial r k Q).eval x)
      atTop (𝓝 ((finiteWeilCanonicalBoundaryLogPolynomial r k Q).eval x)) := by
  have h := tendsto_lagrange_interpolate_eval
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (fun n : ℕ => (fun i => Real.log (Q.uniformApproximation n i /
      finiteWeilCanonicalEdgeMass r k i)) + Real.log ((n : ℝ) + 1) • Q.zeroMassIndicator)
    (Q.boundaryLogValue (finiteWeilCanonicalEdgeMass r k))
    (fun i => Law.tendsto_uniformApproximation_renormalized_log Q
      (finiteWeilCanonicalEdgeMass r k) i (finiteWeilCanonicalEdgeMass_pos r k i)) x
  simpa only [map_add, map_smul, Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul,
    finiteWeilCanonicalApproximationPolynomial, finiteWeilCanonicalLogDensityPolynomial,
    finiteWeilCanonicalZeroMassPolynomial, finiteWeilCanonicalBoundaryLogPolynomial] using h

theorem tendsto_finiteWeilCanonicalApproximationPolynomial_renormalized_coeff
    (r k : ℕ) (Q : Law (Fin (r + 1))) (j : ℕ) :
    Tendsto (fun n : ℕ => (finiteWeilCanonicalApproximationPolynomial r k Q n).coeff j +
      Real.log ((n : ℝ) + 1) * (finiteWeilCanonicalZeroMassPolynomial r k Q).coeff j)
      atTop (𝓝 ((finiteWeilCanonicalBoundaryLogPolynomial r k Q).coeff j)) := by
  have h := tendsto_lagrange_interpolate_coeff
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (fun n : ℕ => (fun i => Real.log (Q.uniformApproximation n i /
      finiteWeilCanonicalEdgeMass r k i)) + Real.log ((n : ℝ) + 1) • Q.zeroMassIndicator)
    (Q.boundaryLogValue (finiteWeilCanonicalEdgeMass r k))
    (fun i => Law.tendsto_uniformApproximation_renormalized_log Q
      (finiteWeilCanonicalEdgeMass r k) i (finiteWeilCanonicalEdgeMass_pos r k i)) j
  simpa only [map_add, map_smul, Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul,
    finiteWeilCanonicalApproximationPolynomial, finiteWeilCanonicalLogDensityPolynomial,
    finiteWeilCanonicalZeroMassPolynomial, finiteWeilCanonicalBoundaryLogPolynomial] using h

theorem tendsto_finiteWeilCanonicalApproximationPolynomial_eval_div_log
    (r k : ℕ) (Q : Law (Fin (r + 1))) (x : ℝ) :
    Tendsto (fun n : ℕ => (finiteWeilCanonicalApproximationPolynomial r k Q n).eval x /
      Real.log ((n : ℝ) + 1)) atTop
      (𝓝 (-(finiteWeilCanonicalZeroMassPolynomial r k Q).eval x)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop := by
    have h : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hlim := ((tendsto_finiteWeilCanonicalApproximationPolynomial_renormalized_eval
    r k Q x).div_atTop hlog).sub_const ((finiteWeilCanonicalZeroMassPolynomial r k Q).eval x)
  simp only [zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [tendsto_atTop.mp hlog 1] with n hn
  have hne : Real.log ((n : ℝ) + 1) ≠ 0 := by linarith
  field_simp [hne]
  ring

theorem tendsto_finiteWeilCanonicalApproximationPolynomial_coeff_div_log
    (r k : ℕ) (Q : Law (Fin (r + 1))) (j : ℕ) :
    Tendsto (fun n : ℕ => (finiteWeilCanonicalApproximationPolynomial r k Q n).coeff j /
      Real.log ((n : ℝ) + 1)) atTop
      (𝓝 (-(finiteWeilCanonicalZeroMassPolynomial r k Q).coeff j)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop := by
    have h : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hlim := ((tendsto_finiteWeilCanonicalApproximationPolynomial_renormalized_coeff
    r k Q j).div_atTop hlog).sub_const ((finiteWeilCanonicalZeroMassPolynomial r k Q).coeff j)
  simp only [zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [tendsto_atTop.mp hlog 1] with n hn
  have hne : Real.log ((n : ℝ) + 1) ≠ 0 := by linarith
  field_simp [hne]
  ring

end RHTower
