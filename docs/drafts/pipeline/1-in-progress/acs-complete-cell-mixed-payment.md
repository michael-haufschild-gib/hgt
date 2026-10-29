# Mixed payment between pair averages and balanced cells

- **ID:** acs-complete-cell-mixed-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Parent:** [complete-cell index payment](acs-complete-cell-index-payment.md)
- **Statement:** Control the original mixed Weil interaction between complete pair averages and the now-positive balanced detail directions, with a signed payment that remains valid under complete-cell refinement.

## Known input and missing step

[Balanced whole-cell effectivity](../3-formalized/acs-complete-cell-haar-effectivity.md) gives a growing logarithmic floor on every signed high-index balanced detail and exact smooth source effectivity. Arbitrary complete-cell data also have independent pair averages. Positivity of the detail block does not bound its mixed coupling or the residual after its elimination.

## Concrete source calculation underway

The coarse pair is `C_a = cellAtom (2*a) + cellAtom (2*a+1)`. For coefficients `u,v` on its two complete cells, the checked exact splitting is

`u cellAtom(2*a) + v cellAtom(2*a+1) = (haarRightCoeff a*u + haarLeftCoeff a*v) C_a + (u-v) haarAtom a`.

The average block is the actual cell system translated by `log 2`. Every integer-translated coarse pair has zero real inner product with every balanced detail. The opposite mixed orientation remains. The open task is a genuine bound for the remaining original Gamma–prime–pole coupling; no assumed positive Schur residual or unchanged-sign claim is permitted.

## Status

[Complete-cell prime triangularity](../3-formalized/acs-complete-cell-prime-triangularity.md) passed its exact final Lean check, with five clean transitive axiom audits: actual pair splitting, exact `log 2` shift identity, endpoint-jump formula, and vanishing of the entire average-to-detail prime block for every integer multiplier. The opposite mixed orientation is retained. No mixed Weil sign has been proved. No stage-2 parking.

## Checked full-source Gamma variance bound

For a finite family of disjoint nonempty intervals `I_i=(a_i,b_i)` of widths `w_i≤1`, define `mean_i=(∫ I_i f)/w_i` and `V_i=∫ I_i (f-mean_i)²`. Lean now proves:

`Σ_i log(1/w_i)*V_i ≤ levyEnergy f`

for every compact BV source, without local mean-zero restrictions. This pays local oscillation even with nonzero pair averages. Weighted variance on each exponential Gamma slice pays its minimum weight times the unweighted variance; coherent interval charges preserve coefficient one. The theorem does not retain the entire coarse Gamma energy as an additional free term.

[Gamma payment with arbitrary means](../3-formalized/acs-gamma-payment-with-arbitrary-means.md) records twelve clean exact-file/transitive audits through the full logarithmic inequality `levyEnergy_ge_sum_log_variance` and its exact complete-cell specialization.

`CompleteCellVariancePayment.lean` passed its exact final audit, including four clean transitive axiom prints. It retains independent average and detail coefficients on every pair and identifies them with arbitrary original cell coefficients. `cellPairSum_levyEnergy_ge` proves `Σ log(a)*haarMass(a)*(u(a)-v(a))² ≤ levyEnergy(Σ u(a)*rawCell(2a)+v(a)*rawCell(2a+1))` for arbitrary signed `u,v` and every finite horizon. No pair average is suppressed.

## Checked mean and exterior remainder

[Simultaneous Gamma payment](../3-formalized/acs-gamma-detail-mean-boundary-payment.md) passed exact project checks and ten clean transitive axiom audits. `IntervalVarianceRemainder.lean` proves the product-weight splitting; `GammaVarianceRemainder.lean` proves its full Gamma-series and exterior-point consequences. `GammaMeanVarianceCapacity.lean` proves the coherent finite-family bound and the real inequality

`Σ_i log(1/w_i) V_i(f) + (1/2) Σ_ij w_i*w_j*k(max(b_j-a_i,b_i-a_j))*(mean_i(f)-mean_j(f))² + Σ_i ∫_F w_i*(mean_i(f)-f(y))²*gammaFarCharge_i(y) ≤ levyEnergy f`.

The exterior sum is proved finite before conversion to real numbers. All three terms coexist in the original energy; no local mean-zero or exterior-vanishing premise appears. The explicit mean graph is not identified with the entire coarse Gamma energy.

`CompleteCellMeanGraph.lean` passed its exact project check and both transitive axiom audits. It retains arbitrary original cell coefficients, logarithmic detail payment, the full mean graph, and an explicit exterior charge depending only on the actual pair averages. Its source is proved zero almost everywhere outside the interval family.

## Checked coarse Gamma recovery

[Coarse Gamma recovery](../3-formalized/acs-coarse-gamma-recovery.md) passed all three exact project checks and thirteen standard-axiom audits. Uniform integrated row bounds, their actual-pair transfer, and exterior finiteness give

`Γ(averageSectionProfile q X) + Σ_(a=1..X) log(a)*haarMass(a)*d(a)² ≤ Γ(completePairProfile q d X) + C*∫(averageSectionProfile q X)²`

for every signed `q,d` and every horizon, with the explicit nonnegative constant `C=2*(13*exp(1/2)+2*gammaTailMass(log(3/2)))`. The integral equals the actual coefficient mass `Σ logCellWidth(a)*q(a)²`. The original independent cell coefficients `u,v` are retained in a separate exact specialization. This closes coarse Gamma recovery without using the detail reserve twice. Full signed prime and pole coupling remains unpaid.

## Joint non-first-prime payment

The [mixed square tail](../3-formalized/acs-square-mixed-source-lower-order.md)
is arbitrarily small in the original complete-profile Gamma energy, uniformly
in horizon. Together with the odd higher powers and actual Gamma coupling,
it gives the [joint source estimate](../3-formalized/acs-joint-nonfirst-mixed-payment.md)

`Γ(g+h)−Γ(h)+W(h)−B₂−Bodd ≥ (1−ε)Γ(g)+(κ/4)D+∫h²`

after one fixed detail head, where `κ=1−1/sqrt(2)` and
`D=Σ log(1/w_a)M_a d_a²`. Every mixed exponent at least two occurs once.
The entire Haar diagonal, including first primes and its pole, is retained.
This closes those mixed payments, not the exponent-one mixed source or
the coarse signed block.

The [full-pole extension](../3-formalized/acs-full-polar-nonfirst-payment.md)
replaces the detail pole with the actual complete-profile pole. It retains
`(1−ε)Γ(g)+(κ/8)D+∫h²` and the positive cosh square after a fixed head,
leaving one adverse sinh square. The original head coordinates and that
moment bound negative dimension by A+1. First-prime mixing and the coarse
signed prime/archimedean block still require joint arithmetic payment.

The [joint whole-square extension](../3-formalized/acs-joint-whole-square-polar-payment.md)
now pays the coarse even-power source from retained coarse Gamma. For
`U=R−S₂(g)`, one fixed head and c>0 give

`c Γ(g)+(γ_E/2)∫g²+(κ/8)D+∫h²+2 coshHalfMoment(F)²
 ≤ U+2 sinhHalfMoment(F)²+(1/2)(∫F)²`.

The exact source identity contains the complete `S₂(F)` once. The head and
the two original moments give uniform negative dimension at most A+2.
This jointly pays the previously missing coarse even powers without reusing
the complete Gamma reserve. The remaining coarse source has first primes,
odd higher powers and archimedean mass; first-prime mixing and the finite
index costs remain open.

## Full Haar prime source: uniform finite heads

[Full Haar prime finite heads](../3-formalized/acs-full-haar-prime-source-finite-heads.md)
now approximate the entire prime diagonal, including first powers, within
`εΓ(F)` in the original complete profile, with one head for every horizon.
The exact divisor identity makes large multipliers small; upward incidence
and reciprocal-width detail payment handle the finite remainder.

Combining this with the established mixed square and odd higher-power
estimates gives `|R−(Γ(F)+P(F))|≤εΓ(F)` after one fixed detail head,
where `R=fullPolarNonfirstSourceForm q d X`. In particular,
`R+2 sinhHalfMoment(F)²≥(1−ε)Γ(F)+2 coshHalfMoment(F)²`.
This retains the original complete Gamma coupling, strengthening the
previous coarse-Gamma share plus fixed logarithmic-detail reserve.
First-prime mixing, the coarse signed block and finite index costs remain.

## Remaining first-prime investigation

`TheOrderedWeilSourceIsACenteredChebyshevDefect` gives the exact ordered
mixed form as a centred Chebyshev derivative pairing minus the localized
Gamma tail. Prime and polar terms must remain together in this comparison;
the identity supplies no sign for arbitrary signed complete coefficients.

`BezoutValuationIncidence.CentredPrimeRowPassesTheCoherentBlockObstruction`
proves short-window cancellation for the actual row Λ−1 and a cross-scale
weighted bilinear bound using Huxley's theorem. Its stated window and row
norms differ from the complete-cell mixed source. No transfer to the
required shared Gamma/polar reserve has been proved here. This is a source
input to investigate, not a discharged first-prime estimate.

The stronger balanced-scale input is in
`ArithmeticCompensationTheory.TheBalancedRegimeAndTheOmittedResidueClassLaw`:
`exists_balanced_centredPrimeBlock_rowBilinear_le` and
`exists_balanced_centredPrimeBlock_dualNorm_le` give qualitative savings
when P≤Q≤BP, using the 17/30 window theorem. Its
`tendsto_mul_kernelStatistic_centredPrimeBlock` also proves that centring
Λ−1 retains the nonzero single-modulus limit
`−π²(p²−1)²/(144p²(p−1))`. That contribution cannot be discarded in a
source-preserving transfer. The finite-prime packet theorem
`eventually_packetCorrectedPrimeBlock_seventeenThirtieths` in
`MultiModulusKloostermanDispersionAndPrimeRowTransfer` adds explicit periodic
correctors; it therefore does not directly estimate the original ACS source.
Neither statement supplies the missing aperture-independent all-prime complete-cell norm bound.

[Uniform prime–polar cancellation](../3-formalized/acs-prime-polar-cancellation-in-gamma-norm.md)
now gives `|primeSum(f)−P(f)|≤ε exp(R)(Γ(f)+∫f²)` for all sufficiently
large R, simultaneously over every BV profile supported in [−R,R]. This
retains the original coefficients and both poles and removes the derivative
norm from the cancellation estimate. The remaining aperture factor prevents
its use as the missing uniform first-prime mixed payment.

## Log

- 2026-10-28 — Opened after the full balanced-cell floor and smooth effectivity passed exact Lean audits.
