import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.FiniteJetConstraintSourceBoundary

/-!
# Exponential and sigmoidal observations preserve hypertranscendence

A hypertranscendental source cannot be hidden by the exact observation channels that recur in
physics, machine learning, and gene regulation:

* a logarithmic exponential phase, characterized without choosing a logarithm by
  `phase'/phase = source'`;
* nonzero differentially algebraic gains and differentially algebraic offsets;
* a fractional-linear sensor whenever its value rationally recovers the source;
* logistic and hyperbolic-tangent readouts of an exponential phase.

These are observability theorems, not existence or temporal-evolution theorems.  They complement
`PolynomialFirstOrderActivationBoundary`: that module extracts an HT input from an HT output,
whereas this module proves the forward non-collapse direction for the actual exponential,
logistic, and tanh value relations.

Parent differential algebra: R. Ait El Manssour, A.-L. Sattelberger, and B. Teguia Tabuguia,
*D-Algebraic Functions*, Journal of Symbolic Computation 125 (2025), arXiv:2301.02512.
The logistic applications include neural gates and sigmoidal gene-regulatory response laws.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

/-- Every derivative of a hypertranscendental element is hypertranscendental. -/
theorem hypertranscendentalOver_deriv
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) :
    HypertranscendentalOver F x′ := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton] at hx ⊢
  have hshift := hx.jetShift (fun _ : Unit => 1)
  simpa [differentialJet_succ] using hshift

/-- Adding a differentially algebraic observable preserves hypertranscendence exactly. -/
theorem hypertranscendentalOver_add_differentialAlgebraic_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x d : E} (hd : DifferentialAlgebraicOver F d) :
    HypertranscendentalOver F (x + d) ↔ HypertranscendentalOver F x := by
  constructor
  · intro hsum hx
    exact hsum (differentialAlgebraicOver_add hx hd)
  · intro hx hsum
    have hx' := differentialAlgebraicOver_sub hsum hd
    exact hx (by simpa using hx')

/-- Multiplication by a nonzero differentially algebraic observable preserves
hypertranscendence exactly. -/
theorem hypertranscendentalOver_mul_differentialAlgebraic_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x d : E} (hd : DifferentialAlgebraicOver F d) (hd0 : d ≠ 0) :
    HypertranscendentalOver F (x * d) ↔ HypertranscendentalOver F x := by
  constructor
  · intro hprod hx
    exact hprod (differentialAlgebraicOver_mul hx hd)
  · intro hx hprod
    have hx' := differentialAlgebraicOver_mul hprod
      (differentialAlgebraicOver_inv hd)
    exact hx (by simpa [mul_assoc, hd0] using hx')

/-- A logarithmic exponential observation cannot collapse a hypertranscendental source.  If
`phase'/phase = source'`, then an HT source forces an HT phase. -/
theorem hypertranscendentalOver_phase_of_logDeriv_eq_deriv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {source phase : E} (hsource : HypertranscendentalOver F source)
    (hlog : phase′ / phase = source′) :
    HypertranscendentalOver F phase := by
  intro hphase
  have hlogDA : DifferentialAlgebraicOver F (phase′ / phase) :=
    differentialAlgebraicOver_div
      (differentialAlgebraicOver_deriv hphase) hphase
  have hsourceDerivDA : DifferentialAlgebraicOver F source′ := by
    simpa [hlog] using hlogDA
  exact (hypertranscendentalOver_deriv hsource) hsourceDerivDA

/-- **Exponential-affine observability transfer.**  A nonzero base-field rescaling of an HT source,
followed by a logarithmic exponential channel and a nondegenerate affine readout, remains HT. -/
theorem hypertranscendentalOver_exponentialAffineObservable
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {source phase : E} {a b c : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsource : HypertranscendentalOver F source)
    (hlog : phase′ / phase = (algebraMap F E a * source)′) :
    HypertranscendentalOver F
      (algebraMap F E c * (algebraMap F E b * phase - 1)) := by
  have haE : algebraMap F E a ≠ 0 := (map_ne_zero (algebraMap F E)).2 ha
  have hbE : algebraMap F E b ≠ 0 := (map_ne_zero (algebraMap F E)).2 hb
  have hcE : algebraMap F E c ≠ 0 := (map_ne_zero (algebraMap F E)).2 hc
  have haDA : DifferentialAlgebraicOver F (algebraMap F E a) :=
    differentialAlgebraicOver_algebraMap a
  have hbDA : DifferentialAlgebraicOver F (algebraMap F E b) :=
    differentialAlgebraicOver_algebraMap b
  have hcDA : DifferentialAlgebraicOver F (algebraMap F E c) :=
    differentialAlgebraicOver_algebraMap c
  have hscaled : HypertranscendentalOver F (algebraMap F E a * source) := by
    have h := (hypertranscendentalOver_mul_differentialAlgebraic_iff
      haDA haE).2 hsource
    simpa [mul_comm] using h
  have hphase : HypertranscendentalOver F phase :=
    hypertranscendentalOver_phase_of_logDeriv_eq_deriv hscaled hlog
  have hweighted : HypertranscendentalOver F (algebraMap F E b * phase) := by
    have h := (hypertranscendentalOver_mul_differentialAlgebraic_iff
      hbDA hbE).2 hphase
    simpa [mul_comm] using h
  have hminusOne : HypertranscendentalOver F
      (algebraMap F E b * phase - 1) := by
    have hnegOne : DifferentialAlgebraicOver F (-1 : E) := by
      simpa using differentialAlgebraicOver_neg
        (differentialAlgebraicOver_algebraMap (F := F) (E := E) 1)
    simpa [sub_eq_add_neg] using
      (hypertranscendentalOver_add_differentialAlgebraic_iff hnegOne).2 hweighted
  have h := (hypertranscendentalOver_mul_differentialAlgebraic_iff
    hcDA hcE).2 hminusOne
  simpa [mul_comm] using h

/-- **Fractional-linear recovery principle.**  If an observed value rationally recovers an HT
source using only base-field coefficients, then the observation is HT.  The supplied recovery
identity is the exact nondegeneracy certificate. -/
theorem hypertranscendentalOver_fractionalLinearObservable_of_recovery
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {source observed : E} {a b c d : F}
    (hsource : HypertranscendentalOver F source)
    (hrecover : source =
      (algebraMap F E a * observed + algebraMap F E b) /
        (algebraMap F E c * observed + algebraMap F E d)) :
    HypertranscendentalOver F observed := by
  intro hobserved
  have ha := differentialAlgebraicOver_algebraMap (F := F) (E := E) a
  have hb := differentialAlgebraicOver_algebraMap (F := F) (E := E) b
  have hc := differentialAlgebraicOver_algebraMap (F := F) (E := E) c
  have hd := differentialAlgebraicOver_algebraMap (F := F) (E := E) d
  have hnum : DifferentialAlgebraicOver F
      (algebraMap F E a * observed + algebraMap F E b) :=
    differentialAlgebraicOver_add
      (differentialAlgebraicOver_mul ha hobserved) hb
  have hden : DifferentialAlgebraicOver F
      (algebraMap F E c * observed + algebraMap F E d) :=
    differentialAlgebraicOver_add
      (differentialAlgebraicOver_mul hc hobserved) hd
  exact hsource (by
    rw [hrecover]
    exact differentialAlgebraicOver_div hnum hden)

/-- A logistic sensor preserves an HT phase whenever its displayed denominator is nonzero. -/
theorem hypertranscendentalOver_logisticPhase
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero F] [CharZero E]
    {phase : E} (hphase : HypertranscendentalOver F phase)
    (hden : 1 + phase ≠ 0) :
    HypertranscendentalOver F (phase / (1 + phase)) := by
  let observed := phase / (1 + phase)
  apply hypertranscendentalOver_fractionalLinearObservable_of_recovery
    (source := phase) (observed := observed)
    (a := 1) (b := 0) (c := -1) (d := 1) hphase
  dsimp only [observed]
  norm_num [map_ofNat]
  field_simp [hden]
  ring

/-- A tanh sensor, written as the Möbius transform `(phase-1)/(phase+1)`, preserves an HT phase. -/
theorem hypertranscendentalOver_tanhPhase
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero F] [CharZero E]
    {phase : E} (hphase : HypertranscendentalOver F phase)
    (hden : phase + 1 ≠ 0) :
    HypertranscendentalOver F ((phase - 1) / (phase + 1)) := by
  let observed := (phase - 1) / (phase + 1)
  have hrecoverDen : -observed + 1 ≠ 0 := by
    dsimp only [observed]
    intro hzero
    field_simp [hden] at hzero
    have htwo : (2 : E) ≠ 0 := by norm_num
    apply htwo
    linear_combination hzero
  apply hypertranscendentalOver_fractionalLinearObservable_of_recovery
    (source := phase) (observed := observed)
    (a := 1) (b := 1) (c := -1) (d := 1) hphase
  dsimp only [observed]
  norm_num [map_ofNat]
  field_simp [hden, hrecoverDen]
  ring

/-- **Forward logistic clock transfer.**  An HT latent clock remains HT after an exponential phase
and a logistic neural/genomic sensor. -/
theorem hypertranscendentalOver_logisticObservable_of_logDeriv_eq_deriv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero F] [CharZero E]
    {source phase : E} (hsource : HypertranscendentalOver F source)
    (hlog : phase′ / phase = source′) (hden : 1 + phase ≠ 0) :
    HypertranscendentalOver F (phase / (1 + phase)) :=
  hypertranscendentalOver_logisticPhase
    (hypertranscendentalOver_phase_of_logDeriv_eq_deriv hsource hlog) hden

/-- **Forward tanh clock transfer.**  An HT latent clock remains HT after an exponential phase and
a tanh neural/genomic sensor. -/
theorem hypertranscendentalOver_tanhObservable_of_logDeriv_eq_deriv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero F] [CharZero E]
    {source phase : E} (hsource : HypertranscendentalOver F source)
    (hlog : phase′ / phase = source′) (hden : phase + 1 ≠ 0) :
    HypertranscendentalOver F ((phase - 1) / (phase + 1)) :=
  hypertranscendentalOver_tanhPhase
    (hypertranscendentalOver_phase_of_logDeriv_eq_deriv hsource hlog) hden

end

end GaloisForLFunctions.HTGeometry
