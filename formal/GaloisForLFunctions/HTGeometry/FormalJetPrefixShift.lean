import GaloisForLFunctions.HTGeometry.JetMonomialDegreeBounds
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryMagnitudeHypertranscendence

/-!
# Adding a polynomial to a power series, formally

Adding a polynomial to a power series is an invertible triangular change of the jet coordinates.
The corresponding substitution of differential polynomials keeps the total jet degree and raises
the combined point-and-order weight by at most `deg p` per jet factor.  This makes a differential
relation for `F + p` into one for `F` with controlled degree data, which is what a gap criterion
with relation-dependent thresholds needs in order to discard a finite prefix of the series.
-/

open MvPolynomial PowerSeries Finset

namespace GaloisForLFunctions.HTGeometry

theorem iterate_derivative_add (j : ℕ) (A B : ℂ⟦X⟧) :
    (⇑(d⁄dX ℂ))^[j] (A + B) = (⇑(d⁄dX ℂ))^[j] A + (⇑(d⁄dX ℂ))^[j] B := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_add]

theorem iterate_derivative_coe (j : ℕ) (p : Polynomial ℂ) :
    (⇑(d⁄dX ℂ))^[j] (p : ℂ⟦X⟧) = ((((⇑Polynomial.derivative)^[j] p : Polynomial ℂ)) : ℂ⟦X⟧) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      PowerSeries.derivative_coe]

theorem aeval_powerSeriesX (q : Polynomial ℂ) :
    Polynomial.aeval (PowerSeries.X : ℂ⟦X⟧) q = (q : ℂ⟦X⟧) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, Polynomial.coe_add]
  | monomial k c =>
      rw [Polynomial.aeval_monomial, Polynomial.coe_monomial, PowerSeries.X_pow_eq]
      ext m
      simp [PowerSeries.coeff_monomial, PowerSeries.coeff_C_mul]

/-- Each jet coordinate of `F + p` is the corresponding shifted coordinate of `F`. -/
theorem aeval_formalJets_jetPolynomialAdd (n : ℕ) (F : ℂ⟦X⟧) (p : Polynomial ℂ)
    (i : Fin (n + 2)) :
    aeval (formalJets n F) (jetPolynomialAdd n p i) = formalJets n (F + (p : ℂ⟦X⟧)) i := by
  induction i using Fin.cases with
  | zero => simp [jetPolynomialAdd, formalJets]
  | succ j =>
      rw [jetPolynomialAdd, Fin.cases_succ, map_add, aeval_X,
        ← Polynomial.aeval_algHom_apply (MvPolynomial.aeval (formalJets n F))
          (MvPolynomial.X 0) ((⇑Polynomial.derivative)^[(j : ℕ)] p)]
      simp only [formalJets, Fin.cons_succ, Fin.cons_zero, aeval_X]
      rw [aeval_powerSeriesX, iterate_derivative_add, iterate_derivative_coe]

/-- Substituting the shifted jet coordinates transports a relation for `F + p` to one for `F`. -/
theorem aeval_formalJets_bind₁_jetPolynomialAdd (n : ℕ) (F : ℂ⟦X⟧) (p : Polynomial ℂ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    aeval (formalJets n F) (bind₁ (jetPolynomialAdd n p) Q)
      = aeval (formalJets n (F + (p : ℂ⟦X⟧))) Q := by
  rw [MvPolynomial.aeval_bind₁]
  congr 1
  congr 1
  funext i
  exact aeval_formalJets_jetPolynomialAdd n F p i

theorem bind₁_jetPolynomialSub_jetPolynomialAdd (n : ℕ) (p : Polynomial ℂ) :
    (fun i => bind₁ (jetPolynomialSub n p) (jetPolynomialAdd n p i))
      = (MvPolynomial.X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [jetPolynomialSub, jetPolynomialAdd]
  | succ j =>
      simp only [jetPolynomialSub, jetPolynomialAdd, Fin.cases_succ, map_add,
        MvPolynomial.bind₁_X_right]
      rw [← Polynomial.aeval_algHom_apply (MvPolynomial.bind₁ (jetPolynomialSub n p))
        (MvPolynomial.X 0) ((⇑Polynomial.derivative)^[(j : ℕ)] p), MvPolynomial.bind₁_X_right]
      simp [jetPolynomialSub]

theorem bind₁_jetPolynomialAdd_ne_zero {n : ℕ} (p : Polynomial ℂ)
    {Q : MvPolynomial (Fin (n + 2)) ℂ} (hQ : Q ≠ 0) : bind₁ (jetPolynomialAdd n p) Q ≠ 0 := by
  intro h0
  apply hQ
  have hback : bind₁ (jetPolynomialSub n p) (bind₁ (jetPolynomialAdd n p) Q) = Q := by
    rw [MvPolynomial.bind₁_bind₁, bind₁_jetPolynomialSub_jetPolynomialAdd,
      MvPolynomial.bind₁_X_left]
    simp
  rw [← hback, h0, map_zero]

theorem natDegree_iterate_derivative_le (j : ℕ) (p : Polynomial ℂ) :
    ((⇑Polynomial.derivative)^[j] p).natDegree ≤ p.natDegree := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have := Polynomial.natDegree_derivative_le ((⇑Polynomial.derivative)^[j] p)
      omega

/-- The substitution keeps the total jet degree and raises the weight by at most `r · deg p`. -/
theorem jetBd_bind₁_jetPolynomialAdd {n r V : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    (h : JetBd n r V Q) (p : Polynomial ℂ) :
    JetBd n r (V + p.natDegree * r) (bind₁ (jetPolynomialAdd n p) Q) := by
  classical
  set D := p.natDegree with hD
  have hexp : bind₁ (jetPolynomialAdd n p) Q
      = ∑ d ∈ Q.support, MvPolynomial.C (MvPolynomial.coeff d Q)
          * ∏ i, (jetPolynomialAdd n p i) ^ (d i) := by
    rw [bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    rfl
  rw [hexp]
  refine JetBd.finsetSum _ _ fun d hd => ?_
  have hdeg := h.deg d hd
  have hwt := h.wt d hd
  have hfactor : ∀ j : Fin (n + 1),
      JetBd n (d j.succ * 1) (d j.succ * ((j : ℕ) + D))
        ((jetPolynomialAdd n p j.succ) ^ (d j.succ)) := by
    intro j
    refine JetBd.pow ?_ _
    rw [jetPolynomialAdd, Fin.cases_succ]
    refine JetBd.add ((JetBd.X_succ j).mono le_rfl (by omega)) ?_
    exact (JetBd.polynomial_point ((⇑Polynomial.derivative)^[(j : ℕ)] p)).mono (Nat.zero_le _)
      (le_trans (natDegree_iterate_derivative_le _ _) (by omega))
  have hprod : JetBd n (∑ j : Fin (n + 1), d j.succ * 1)
      (∑ j : Fin (n + 1), d j.succ * ((j : ℕ) + D))
      (∏ j : Fin (n + 1), (jetPolynomialAdd n p j.succ) ^ (d j.succ)) :=
    JetBd.finsetProd _ _ _ _ fun j _ => hfactor j
  have hzero : JetBd n 0 (d 0) ((jetPolynomialAdd n p 0) ^ (d 0)) := by
    rw [jetPolynomialAdd, Fin.cases_zero]
    simpa using (JetBd.X_zero (n := n)).pow (d 0)
  have hsplit : ∏ i, (jetPolynomialAdd n p i) ^ (d i)
      = (jetPolynomialAdd n p 0) ^ (d 0)
        * ∏ j : Fin (n + 1), (jetPolynomialAdd n p j.succ) ^ (d j.succ) :=
    Fin.prod_univ_succ (fun i => (jetPolynomialAdd n p i) ^ (d i))
  rw [hsplit]
  refine ((JetBd.C_bd (n := n) (MvPolynomial.coeff d Q)).mul (hzero.mul hprod)).mono ?_ ?_
  · have : ∑ j : Fin (n + 1), d j.succ * 1 = ∑ j : Fin (n + 1), d j.succ := by
      exact Finset.sum_congr rfl fun j _ => by ring
    omega
  · have hsum : ∑ j : Fin (n + 1), d j.succ * ((j : ℕ) + D)
        = (∑ j : Fin (n + 1), (j : ℕ) * d j.succ) + D * ∑ j : Fin (n + 1), d j.succ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hDr : D * ∑ j : Fin (n + 1), d j.succ ≤ D * r := Nat.mul_le_mul_left _ hdeg
    omega

end GaloisForLFunctions.HTGeometry
