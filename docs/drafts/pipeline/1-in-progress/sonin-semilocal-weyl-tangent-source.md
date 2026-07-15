# Sonin semilocal Weyl-tangent source

- **ID:** sonin-semilocal-weyl-tangent-source
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + analytic source problem
- **Source:** quantum-mechanical Weyl/Stone value relation applied to the existing semilocal
  logarithmic-dilation source
- **Statement:** The finite von Mangoldt central trace is exactly the finite weighted sum of
  identity tangents, or equivalently Wigner--Smith relative phase derivatives at any real
  parameter, of unit-modulus prime-power Weyl characters.  Hence the existing
  fixed-bounded-response obstruction does not exclude a bounded differentiable phase family;
  the missing task is to descend that family from the actual Sonin cutoff/scattering cyclic class.

## Goal

Replace the impossible request that one fixed bounded projection-correction response equal the
unbounded orbital length `log(p^m)` by the physically correct generator interface.  The value of a
Weyl character is bounded, while its identity tangent retains the full logarithmic charge.

The route is useful only if the phase character is tied to the existing physical dilation and its
tangent feeds an existing arithmetic consumer.  Both links are exact in the present source:

1. logarithmic-position multiplication and normalized physical dilation obey the Weyl relation;
2. the finite von Mangoldt central trace is a sum of the resulting phase-orbit tangents.

## Gates

- [x] 0 → 1 in-progress: exact physics relation, actual Sonin dilation specialization, direct
  finite-trace consumer, and a named analytic open core
- [ ] 1 → 2 fully-proven: targeted Lean audit plus proof of a source-defined cyclic phase descent
- [ ] 2 → 3 formalized: targeted Lean verification and axiom inspection
- [ ] 3 → 4 publication-ready: standalone theorem, analytic hypotheses, provenance, and Lean
  certificate

## Physics value relation

For real charge `q`, the scalar Weyl character is

```text
chi_q(t) = exp(-i q t).
```

It has the exact pair of value relations

```text
|chi_q(t)| = 1,                  t real,
i * chi_q'(0) = q.
```

Thus bounded phase values do not bound their infinitesimal generator.  The reusable general
HTGeometry implementation is
`formal/GaloisForLFunctions/HTGeometry/WeylCharacterGenerator.lean`.  It also formalizes addition
of charges and parameters, so independent source charges compose multiplicatively before their
generators add.

This is the scalar value content of the Weyl/Stone one-parameter-unitary framework.  No unbounded
operator-domain theorem or autonomous flow is imported into the hypertranscendental setting.

## Actual Sonin dilation relation

Let

```text
(M_t f)(x) = exp(i t log|x|) f(x)
```

and let `U_p` be the corpus's normalized physical dilation.  For `p>0` and `x!=0`, direct
substitution gives

```text
M_t U_p = exp(-i t log p) U_p M_t.
```

At the semilocal prime-power scale `p^m`, the phase has unit modulus for every real `t`, while its
identity tangent is `-i log(p^m)`.  Weighting this phase by the existing logarithmic Euler
coefficient `p^(-m/2)/m` gives

```text
i * d/dt|_0 [p^(-m/2)/m * exp(-i t log(p^m))]
  = log(p) p^(-m/2).
```

The right side is exactly the corpus declaration `soninSemilocalPrimeFluxCoefficient`.  The
RHTower source is
`formal/GaloisForLFunctions/RHTower/SoninSemilocalWeylGenerator.lean`.

The phase is not merely defined after reading that coefficient.  On the common pointwise core,
the same source proves the exact Heisenberg-conjugation identity

```text
M_t U_p M_{-t} = exp(-i t log p) U_p
```

and its Kubo tangent form

```text
d/dt|_0 (M_t U_p M_{-t}) = i [log|x|, U_p].
```

Thus the bounded family is constructed from the actual logarithmic-position and dilation actions.
What is still missing is its survival after the Sonin cutoff/scattering and cyclic-trace descent.

The Wigner--Smith relative derivative removes the choice of basepoint.  For the same character,

```text
i * conjugate(chi_q(t)) * chi_q'(t) = q             for every real t.
```

Consequently the finite von Mangoldt central trace has the exact representation

```text
sum_(p,m) test(p,m) * p^(-m/2)/m
  * [i * conjugate(chi_log(p^m)(t)) * chi_log(p^m)'(t)]
```

at every real `t`.  A future cyclic descent may therefore work at any parameter where its cutoff
or trace estimates are available; it need not reach a specially normalized identity point.

## Direct corpus applications

- **Positive successor to the no-go:** `SoninSemilocalTraceObstruction` excludes a fixed
  Hilbert--Schmidt projection-correction response whose value would have to grow like `log(p^m)`.
  It does not exclude the derivative at the identity of a bounded phase family.  The new theorem
  changes the value interface rather than contradicting the obstruction.
- **Existing finite consumer:** `finiteVonMangoldtCentralTrace_eq_sum_weylGenerators` rewrites the
  already formalized finite von Mangoldt central trace as a finite sum of exact Weyl generators.
- **Basepoint hypothesis removed:**
  `finiteVonMangoldtCentralTrace_eq_sum_wignerSmithCharges` gives the same trace from relative
  phase derivatives at every real parameter, so an eventual analytic descent need not assume
  access to `t=0`.
- **Existing geometric source:** `logPositionUnitary_normalizedDilation_weyl` exponentiates the
  logarithmic-position/dilation commutator already used in `SoninLogCoordinateScattering`; the
  character is not an independently fitted arithmetic scalar.
- **Existing commutator consumer:**
  `deriv_normalizedDilationWeylCharacterOrbit_zero_eq_I_mul_commutator` identifies the phase
  tangent with the existing logarithmic-position/dilation commutator, while
  `soninSemilocalWeylFluxOrbit_mul_normalizedDilation_eq_conjugation` inserts the existing Euler
  weight into that actual conjugation orbit.
- **General HTGeometry reuse:** whenever a fixed bounded detector is too small for a growing
  source charge, `scalarWeylCharacter_bounded_and_generator_exact` isolates the precise additional
  datum that can retain it: a differentiable one-parameter phase response.
- **Finite support retained:** the trace consumer remains a `Finsupp` sum over prime powers.  No
  interchange of an infinite series and a derivative is claimed.

## What is and is not discharged

The exact finite algebraic value relation is discharged at source level.  In particular, the
finite von Mangoldt coefficient no longer needs to be represented as the value of one bounded
projection response.

The relation now produces the required phase family from logarithmic position and physical
dilation on their common pointwise core.  It does **not** yet prove that the family survives the
Sonin cutoff, scattering operator, or cyclic trace.  Consequently this card does not claim a
prime--Gamma moment comparison, coupled-Gram positivity, or RH.

## Open core

`[OPEN CORE]` Descend the constructed pointwise conjugation family through the actual
cutoff/scattering cyclic class to a bounded one-parameter response `Phi_pk(t)` satisfying all of
the following without inserting `log(p^m)` by hand:

```text
|Phi_pk(t)| is uniformly controlled for real t,
Phi_pk is differentiable at t=0,
i * Phi_pk'(0) = soninSemilocalPrimeFluxCoefficient pk,
```

and prove that the derivative survives the required finite-part/cyclic descent.  The source
construction must identify the Weyl phase through the physical dilation action, control the
cutoff and conductor terms, and justify differentiation of the relevant trace or pairing.  For
an infinite prime-power limit it must additionally supply a valid dominated or trace-class
interchange theorem; the present finite result deliberately avoids that assumption.

This is a distinct source problem from the coupled vacuum-Feshbach aperture inequality.  If the
cyclic phase descent exists, it supplies the missing unsquared Euler signal that a fixed
Hilbert--Schmidt correction cannot carry.  If it does not, the bounded-response obstruction
remains decisive for that implementation class.

## Literature provenance

1. H. Weyl, *Quantenmechanik und Gruppentheorie*, Zeitschrift für Physik 46 (1927), 1--46,
   DOI [10.1007/BF02055756](https://doi.org/10.1007/BF02055756).
2. M. H. Stone, *Linear Transformations in Hilbert Space. III. Operational Methods and Group
   Theory*, Proceedings of the National Academy of Sciences 16 (1930), 172--175,
   DOI [10.1073/pnas.16.2.172](https://doi.org/10.1073/pnas.16.2.172).
3. R. Kubo, *Statistical-Mechanical Theory of Irreversible Processes. I. General Theory and
   Simple Applications to Magnetic and Conduction Problems*, Journal of the Physical Society of
   Japan 12 (1957), 570--586,
   DOI [10.1143/JPSJ.12.570](https://doi.org/10.1143/JPSJ.12.570).
4. E. P. Wigner, *Lower Limit for the Energy Derivative of the Scattering Phase Shift*, Physical
   Review 98 (1955), 145--147,
   DOI [10.1103/PhysRev.98.145](https://doi.org/10.1103/PhysRev.98.145).
5. F. T. Smith, *Lifetime Matrix in Collision Theory*, Physical Review 118 (1960), 349--356,
   DOI [10.1103/PhysRev.118.349](https://doi.org/10.1103/PhysRev.118.349).

Only the exact unitary-character and identity-generator value relation is transferred.  No claim
about uniqueness of the canonical commutation relations is needed.  The Birman--Krein
scattering-determinant/spectral-shift formula was also audited but is not promoted: the current
corpus has no source-built trace-class scattering pair or spectral-shift formalism to which its
hypotheses could be applied.

## Verification status

Source inspection only.  In accordance with the active user constraint, no Lean invocation,
scratch compilation, lint, axiom inspection, numerical check, targeted build, or full build was
run.  The declarations must not be promoted to stage 3 until a narrow validation pass is
authorized.

## Log

- 2026-07-15 — primary physics provenance checked; generic Weyl-character generator, actual Sonin
  dilation conjugation/Kubo tangent specialization, and finite von Mangoldt trace consumer written
  source-only.  No computation or build run.
