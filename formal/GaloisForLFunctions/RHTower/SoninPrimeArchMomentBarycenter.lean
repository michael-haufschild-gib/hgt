import GaloisForLFunctions.RHTower.SoninPrimeArchFiniteMomentTransfer

/-!
# A positive Sonin aperture barycenter to RH

The earlier Sonin transfer asks the fixed prime--archimedean moment vector to be a cluster point of
the one-parameter positive-aperture moment curve.  The Gamma source naturally carries scale-integral
data, so a weaker constraint-side producer is a positive measure on apertures whose barycenter of
Sonin energy moments is the complete prime--archimedean moment sequence.

This module proves the consumer.  Finite polynomial support permits exact interchange of the
aperture integral and the Hankel sum.  Unconditional positivity of every Sonin trace--Hankel value
then transfers to the prime--archimedean source and proves RH.  No Xi divisor, target measure, or
root-location assumption occurs in the barycenter predicate.
-/

open MeasureTheory Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A positive aperture law whose barycenter of Sonin energy moments is the complete
prime--archimedean moment sequence. -/
def SoninPrimeArchMomentBarycenter (ν : Measure ℝ) : Prop :=
  (∀ᵐ a ∂ν, 0 < a) ∧
    (∀ r, Integrable (fun a => soninAllPrimeEnergyMoment a r) ν) ∧
    ∀ r, ((normalizedPrimeArchMoment r : ℝ) : ℂ) =
      ∫ a, soninAllPrimeEnergyMoment a r ∂ν

private theorem integrable_soninMomentQuadraticSum
    {ν : Measure ℝ} (hint : ∀ r, Integrable (fun a => soninAllPrimeEnergyMoment a r) ν)
    (n : ℕ) (c : Fin n → ℝ) :
    Integrable (fun a => ∑ i : Fin n, ∑ j : Fin n,
      ((c i * c j : ℝ) : ℂ) *
        soninAllPrimeEnergyMoment a ((i : ℕ) + (j : ℕ))) ν := by
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (hint ((i : ℕ) + (j : ℕ))).const_mul _))

/-- A moment barycenter identifies the complete prime--archimedean Hankel value with the
positive aperture average of the Sonin trace--Hankel values. -/
theorem primeArchSourceTraceHankel_eq_integral_sonin_of_momentBarycenter
    {ν : Measure ℝ} (h : SoninPrimeArchMomentBarycenter ν) (p : Polynomial ℝ) :
    primeArchSourceTraceHankel p = ∫ a, soninAllPrimeTraceHankel a p ∂ν := by
  let n : ℕ := p.natDegree + 1
  let c : Fin n → ℝ := Polynomial.toFn n p
  have hp : Polynomial.ofFn n c = p := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have hsumInt := integrable_soninMomentQuadraticSum h.2.1 n c
  rw [← hp, ← xiCentralTraceHankel_eq_primeArchSourceTraceHankel,
    xiCentralTraceHankel_ofFn]
  simp_rw [← primeArchSourceMoment_eq_xiCentralReciprocalMoment]
  change (∑ i : Fin n, ∑ j : Fin n,
      ((c i * c j : ℝ) : ℂ) *
        ((normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ)) = _
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      ((c i * c j : ℝ) : ℂ) *
        ((normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ)) =
        ∑ i : Fin n, ∑ j : Fin n,
          ((c i * c j : ℝ) : ℂ) *
            ∫ a, soninAllPrimeEnergyMoment a ((i : ℕ) + (j : ℕ)) ∂ν := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [h.2.2 ((i : ℕ) + (j : ℕ))]
    _ = ∫ a, ∑ i : Fin n, ∑ j : Fin n,
          ((c i * c j : ℝ) : ℂ) *
            soninAllPrimeEnergyMoment a ((i : ℕ) + (j : ℕ)) ∂ν := by
      symm
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          rw [integral_const_mul]
        · intro j _
          exact (h.2.1 ((i : ℕ) + (j : ℕ))).const_mul _
      · intro i _
        exact integrable_finsetSum Finset.univ (fun j _ =>
          (h.2.1 ((i : ℕ) + (j : ℕ))).const_mul _)
    _ = ∫ a, soninAllPrimeTraceHankel a (Polynomial.ofFn n c) ∂ν := by
      apply integral_congr_ae
      filter_upwards [h.1] with a ha
      exact (soninAllPrimeTraceHankel_ofFn a ha n c).symm

/-- The barycenter relation transfers unconditional Sonin positivity to every integer
prime--archimedean Hankel test. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_soninMomentBarycenter
    {ν : Measure ℝ} (h : SoninPrimeArchMomentBarycenter ν) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  rw [primeArchSourceTraceHankel_eq_integral_sonin_of_momentBarycenter h q]
  let n : ℕ := q.natDegree + 1
  let c : Fin n → ℝ := Polynomial.toFn n q
  have hq : Polynomial.ofFn n c = q := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have hsumInt := integrable_soninMomentQuadraticSum h.2.1 n c
  have htraceInt : Integrable (fun a => soninAllPrimeTraceHankel a q) ν := by
    rw [← hq]
    exact hsumInt.congr (h.1.mono fun a ha =>
      (soninAllPrimeTraceHankel_ofFn a ha n c).symm)
  calc
    0 ≤ ∫ a, (soninAllPrimeTraceHankel a q).re ∂ν :=
      integral_nonneg_of_ae
        (h.1.mono fun a _ => soninAllPrimeTraceHankel_re_nonneg a q)
    _ = (∫ a, soninAllPrimeTraceHankel a q ∂ν).re := integral_re htraceInt

/-- **Aperture-barycenter chain to RH.** A positive source aperture law whose Sonin spectral
moments have the complete prime--archimedean moment sequence as barycenter proves RH. -/
theorem riemannHypothesis_of_soninPrimeArchMomentBarycenter
    {ν : Measure ℝ} (h : SoninPrimeArchMomentBarycenter ν) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_soninMomentBarycenter h)

end

end RHTower
