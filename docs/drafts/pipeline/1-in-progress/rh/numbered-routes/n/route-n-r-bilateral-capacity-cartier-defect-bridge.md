# Route N/R bilateral capacity–Cartier defect bridge

- **ID:** `route-n-r-bilateral-capacity-cartier-defect-bridge`
- **Stage:** 1 — in progress
- **Type:** exact cross-route paper bridge; Lean target unverified
- **Scientific status:** `[PAPER-DERIVED] [NO RH ASSUMPTION] [NOT YET LEAN-CHECKED]`
- **Statement:** Route N's bilateral prime capacity excess is, after its fixed
  positive coefficient, exactly the squared norm of Route R's literal
  source-to-physical Cartier comparison defect.

## Exact statement

Fix an actual Xi copy `q`, an ordinary prime `p`, and write

```text
rho   = q.1,
delta = deningerHalfDensityMateGain p rho = p^(2 Re(rho)-1),
M     = xiCenteredFlowMultiplicityMass rho,
A     = routeNGammaSewnCriticalSquarefreeParityOdds p,
c     = ccmRationalAdelicPrimeXiCartierCoefficient rho,
D     = ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho,
C     = xiCenteredFlowBilateralPrimeCapacityExcess q p.
```

The proposed closed theorem is

```text
delta * Complex.normSq c * C = M * A * Complex.normSq D.       (NR-CARTIER)
```

No factor is selected from a zero. `M`, `A`, and `delta` are explicit and
strictly positive. The theorem therefore identifies the Route-N excess with
the literal source/physical comparison defect before any scalarization or
summation.

## Paper derivation

The existing exact theorems give the following identities.

1. Route P's reflected prime translation excess is

   ```text
   P(q,p) = p^(-t) + p^t - 2,
   t = primeDepthBVWoldXiCenteredRate rho = 2 Re(rho)-1.
   ```

   This follows from
   `frankensteinThetaPrimeTranslationEnergy_eq`,
   `frankensteinThetaPrimeTranslationEnergy_lineConj_eq`, and the definition
   of `frankensteinThetaPrimeTranslationPairExcess`.

2. Since `delta = p^t`, elementary field algebra gives

   ```text
   P(q,p) = delta + delta^(-1) - 2 = (delta - 1)^2 / delta.    (1)
   ```

3. Route R identifies its physical reflected phase quadrature with the same
   expression:

   ```text
   Q(p,rho) = (delta - 1)^2 / delta.
   ```

   This is
   `ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_mateGainDefect`.
   Hence `P(q,p) = Q(p,rho)`.

4. Route R retains the Cartier coefficient exactly:

   ```text
   phasePhysical - phaseSource = Q(p,rho) * Complex.normSq c,
   delta * (phasePhysical - phaseSource) = Complex.normSq D.
   ```

   These are
   `ccmRationalAdelicPrimeXiGammaPairedPhaseEnergy_sub_source_eq_quadraturePort`
   and
   `ccmRationalAdelicPrimeXiMateGain_mul_phaseEnergyExcess_eq_sourceDefectNormSq`.
   Combining them yields

   ```text
   delta * P(q,p) * Complex.normSq c = Complex.normSq D.      (2)
   ```

5. Route N is coefficient-faithful to Route P:

   ```text
   C = M * A * P(q,p).
   ```

   This is
   `xiCenteredFlowBilateralPrimeCapacityExcess_eq_translationPairExcess`.
   Multiplying (2) by `M*A` gives `(NR-CARTIER)`.

All five steps are unconditional algebraic identities. The result is stronger
than agreement of zero loci: it retains prime, divisor-copy, multiplicity,
critical-channel, and Cartier-coefficient data.

## Proof-chain consequence

The active chain is now

```text
literal CCM/Mobius source
  -> Cartier source-to-physical comparison D
  -> (NR-CARTIER) bilateral N/P/R excess
  -> zero excess on every Xi fibre
  -> critical-line landing
  -> RH.
```

This does not prove `D = 0`. It removes a false separation between Route N
capacity, Route P translation work, and Route R phase polarization: all are
the same nonnegative source defect with explicit positive gauges.

## Hard mathematical core

The sole load-bearing source statement here is a proof, from the literal
arithmetic source rather than a postulated Hilbert adjoint, that the fixed
Cartier source-to-physical defect `D` vanishes. Equivalent existing receiver
forms are source-dagger identity, reflected phase-quadrature landing,
same-fibre norm identity, and null-homology of the retained central
Bockstein class. They classify the target but do not produce it.

The graded variable-ideal source comparison and its coefficient-faithful
resolved frame already exist. The next attack is therefore not to construct
that comparison or a new capacity inequality. It is to identify its resolved
source dagger with the fixed same-fibre Cartier dagger while retaining `c` in
both reflected orientations. Any candidate must imply
`D = 0` directly and must not obtain it by inserting `P(q,p)=0`, a boundedness
assumption, or a zero-indexed quotient.

## New first-Cartier source interface

There is a sharper, one-prime formulation of the missing source statement.
For every `rho : XiDivisorSupport` and `p : Nat.Primes`, put

```text
I_rho,p = DeningerXiBidirectionalIntegralGammaReporter rho p,
D_rho,p = ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho.
```

Then the existing pointwise classifications compose to the exact interface

```text
Nonempty I_rho,p  <->  D_rho,p = 0.                         (IC-R-CARTIER)
```

The paper proof is one line of equivalences:

```text
Nonempty I_rho,p <-> Re(rho)=1/2
                  <-> D_rho,p=0.
```

The left equivalence is
`deningerXiBidirectionalIntegralGammaReporter_nonempty_iff`; the right one is
`ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_re_eq_half`
(with its unused cofinal-depth argument set to `0`).  This interface has not
yet been made into a dedicated Lean theorem or audited in a scratch import.

It is stronger than a restatement of a zero locus because it identifies the
precise missing map.  The integral source class is already unconditional:
its multiplicity-labelled orientations `F` and `R` satisfy

```text
F != 0,     F + R = 0.
```

A coefficient-faithful reporter would have to read them as the two literal
Gamma-six defects at

```text
a = log(p) * (2 Re(rho)-1).
```

Additivity would therefore force

```text
defect_forward(a) + defect_reflected(a)
  = 2 * (cosh(a) - 1) = 0,
```

which is exactly the same `D_rho,p = 0` detected by the Route-R Cartier
comparison.  Thus the proposed source producer is now concrete:

```text
canonical CCM rational source potential
  -> additive map on the literal integral first Cartier conormal
  -> the two prescribed Gamma-six coefficient readings
  -> D_rho,p = 0
  -> NR-CARTIER capacity zero.
```

This is a stricter target than a two-prime shared ghost: one fixed ordinary
prime suffices once both Cartier orientations are retained.  It still cannot
be postulated.  A targeted corpus check found no `ccmRationalAdelic` reference
in either `FrankensteinXiBidirectionalIntegralCartierSource.lean` or
`SourceHorizontalBilateralSecondCartierTopology.lean`.  Consequently the
missing work is a source-induced comparison from the CCM quotient data to the
integral Cartier physical character, not a new conormal class, a new reporter
structure, or a new capacity estimate.

## Cyclic-Kummer audit: source descent already exists

The deeper corpus search changes that diagnosis in one important way.  The
literal CCM source already has two nontrivial, coefficient-faithful boundary
descents:

```text
ordinary cyclic coinvariants (tau - 1),
signed Kummer coinvariants with degree-two Hochschild boundaries (tau + 1).
```

The first is constructed in
`RouteRPreDivisorRationalCartierCoinvariantFunctor.lean`.  Its ordinary-prime
class survives, its descended Cartier coefficient is the original Xi jet, and
its physical defect is definitionally the same `D_rho,p`:

```text
coinvariant physical defect = D_rho,p.
```

The second is constructed in `RouteRSignedKummerCyclicCartierLanding.lean`.
It retains the same jet with the nonzero prime-log regulator and gives the
independent exact readout

```text
signed-Kummer physical defect = -log(p) * D_rho,p.
```

Thus both cyclic parities and genuine degree-two Hochschild boundaries have
already been imposed without losing prime provenance, multiplicity, or the
Cartier coefficient.  They do not kill `D_rho,p`; they expose it.  The
positive conclusion is operational: do not seek another source quotient.
Seek a source theorem that makes the **actual physical prime dilation act
trivially on one of these existing quotient classes**.  That is a concrete
commuting-square/functoriality statement, with no selectable observer or
unfixed source object left.

## Second-Cartier ghost evaluation bridge

The first-Cartier interface explains why the two finite Gamma readings cannot
be additive off the line.  The exact quantity they fail to add to zero is
already present in the literal second Cartier neighbourhood.

Let `g = (q - 1)^2` in the *unquotiented* Laurent source ring and let
`chi_delta` be the physical Laurent character with `chi_delta(q)=delta`.
Do not treat `chi_delta` as a map out of the second Cartier quotient: that is
precisely the issue.  Its evaluation on the retained representative is

```text
chi_delta(g) = (delta - 1)^2.                              (G)
```

The source relation in `R / (q-1)^3` is

```text
[q-1] + [q^-1-1] = [g].                                    (S2)
```

and `[g]` is nonzero and square-zero.  Applying the physical character before
quotienting makes `(S2)` read

```text
(delta - 1) + (delta^-1 - 1) = delta^-1 * chi_delta(g).
```

That right side is the Route-P/Route-R quadrature quantity.  Consequently the
same algebra behind `NR-CARTIER` gives the coefficient-free normalization

```text
delta * C = M * A * chi_delta(g),                           (S2-N)
Complex.normSq D = Complex.normSq c * chi_delta(g).         (S2-R)
```

Here `C`, `D`, `M`, `A`, `c`, and `delta` have the meanings fixed above.
`(S2-N)` is the Route-N translation identity plus
`P=(delta-1)^2/delta`; `(S2-R)` is the explicit factorization
`D=(1-delta)c`.  These paper derivations remain unverified as a dedicated Lean
module, just as `(NR-CARTIER)` does.

This identifies the capacity excess as the physical value of the unique
nonzero second-order source escape, with no divisor summation and no discarded
coefficient.  It also gives a strict source criterion:

```text
chi_delta factors through Z[q,q^-1]/(q-1)^3
  <-> chi_delta((q-1)^3)=0
  <-> delta=1
  <-> chi_delta(g)=0
  <-> D=0 <-> C=0.
```

The first implication uses that the target complex field is reduced; the
middle equivalences use positivity of `delta` and nonvanishing of `c`, `M`,
and `A`.  Thus ordinary reduced quotient descent cannot be the producer—it
would prove the conclusion immediately and erase the first-order source
orientations.  The live mathematical task is now sharper: derive
third-order flatness of this *specific physical Laurent character* from the
literal CCM/Möbius source while retaining its coefficient line.  A solution
must explain why the physical character kills `(q-1)^3`; merely using the
second-Cartier quotient or declaring a reduced physicalization cannot do so.

## Lean target and audit boundary

Suggested module:

```text
formal/GaloisForLFunctions/RHTower/XiCenteredFlowRouteNCartierDefectBridge.lean
```

It should import only the existing Route-N bilateral-capacity bridge and the
Route-R phase-quadrature polarization module, prove the intermediate equality
`P(q,p)=Q(p,rho)`, then prove `(NR-CARTIER)`. It must be checked in a small
scratch import first and only then built as its single module. No Lean process
was started for this card; the theorem remains unverified until that audit.

## Actual-source modal transfer (CM-TRANSFER)

**Status:** `[PAPER-DERIVED] [NO RH ASSUMPTION] [NOT YET LEAN-CHECKED]`.

The completed unit-Riesz response is a literal arithmetic source current.  Its
Laplace transform and the completed source-relative CCM reporter are not merely
compatible at their zero loci: on the open half-plane `Re z > 0` they are linked
by an explicit, zero-free rational transport.

Write

```text
R(z) = integral_0^infty exp(-z t) * unitRieszCompletedSourceResponse(t) dt,
M(z) = 3 / ((z + 1) * (2 z + 3)),
S(z) = unitRieszCesaroComplexCompletedReporterSymbol(z).
```

The source weld gives

```text
R(z) = M(z) * regularizedCriticalMellinDefect(z),
```

by `unitRieszCompletedSourceResponse_laplace_eq_defect`.  The complex
source-relative normalization computes

```text
S(z) = -3 z^2 / (32 * (z + 1) * (2 z + 1))
```

from `unitRieszCesaroComplexCompletedReporterSymbol_eq`.  Eliminating the
common critical-Mellin defect gives

```text
S(z) * regularizedCriticalMellinDefect(z)
  = T(z) * R(z),

T(z) = -z^2 * (2 z + 3) / (32 * (2 z + 1)).                 (CM-TRANSFER)
```

Every factor in `T(z)`, `M(z)`, and `S(z)` is nonzero for `Re z > 0`.
Thus the coefficient-faithful reporter is a zero-free rational image of an
actual completed prime/polar/archimedean source response on that half-plane.
No source quotient, selected observer, or asymptotic/RH premise is used in
this calculation.

This isolates the next genuine producer conjecture:

```text
The CM-TRANSFER source port extends through the Xi-divisor continuation and
intertwines prime dilation with the fixed physical Cartier character.
```

If proved coefficient-faithfully, that transport supplies the previously
missing gauge-breaking map from literal source to `D_rho,p`; it would imply
`D_rho,p = 0`, then `(NR-CARTIER)`, then critical-line landing.  The current
corpus supplies the right-half-plane equality but not this continuation and
Cartier-intertwining law.  The third-grade/Cesaro convergence criteria do not
supply it: their required linear or bounded tail conditions are already
RH-bearing.
