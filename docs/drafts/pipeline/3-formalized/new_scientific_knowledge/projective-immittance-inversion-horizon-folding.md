# Projective immittance charts have an exact inversion-horizon folding locus

- **ID:** `projective-immittance-inversion-horizon-folding`
- **Stage:** 3-formalized/new_scientific_knowledge
- **Type:** GENERAL HT THEOREM / PROJECTIVE CHART CLASSIFICATION / SMITH-CHART SYNTHESIS
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [CANDIDATE NEW SCIENTIFIC SYNTHESIS] [NOT RH]`
- **Novelty boundary:** the Smith impedance/admittance half-turn, conjugation of Möbius maps, and
  differential Lüroth theory are classical.  The candidate-new statement is the exact folding
  locus for the positive-order HT jet-tail flag, together with the resulting collapse of a pair of
  complementary HT horizons.  It depends on the candidate-new projective jet-horizon stabilizer
  theorem and is not claimed as an independent new mathematical core.
- **Parents:** `projective-jet-horizon-stabilizer-law.md`,
  `ProjectiveHorizonComplementarity.lean`, `ExponentialObservationHypertranscendence.lean`
- **Formal target:** `formal/GaloisForLFunctions/HTGeometry/ProjectiveImmittanceHorizon.lean`

## Exact theorem `[PROVED HERE]`

Let `K` be a differential field of characteristic zero, let `L/K` be a differential-field
extension, and let `x in L` be hypertranscendental over `K`.  For `a,b,c,d in K` with

```text
Delta = a d - b c != 0,
```

write

```text
M(t) = (a t + b)/(c t + d)
T_n(t) = K(delta^n t, delta^(n+1) t, ...).
```

Then:

1. `M(x)` and `M(x^(-1))` are hypertranscendental over `K`; no observation-side HT premise is
   required.
2. The first positive-order horizons fold together exactly on one quadratic coefficient locus:

   ```text
   T_1(M(x^(-1))) = T_1(M(x))  iff  d^2 = c^2.              (1)
   ```

3. The first horizon already detects folding of the complete flag:

   ```text
   (for every n, T_n(M(x^(-1))) = T_n(M(x)))
     iff d^2 = c^2.                                         (2)
   ```

Equivalently, in characteristic zero the folding charts are precisely those whose projective pole
`-d/c` is one of the two fixed points `+1,-1` of inversion.  The normalized Smith chart

```text
Gamma(t) = (t-1)/(t+1)
```

lies on the `d=c` component.  It therefore sends the two distinct HT horizons of impedance `x`
and admittance `x^(-1)` to the same complete jet-tail flag.  At value level this is the practical
Smith rule

```text
Gamma(x^(-1)) = -Gamma(x),                                  (3)
```

the 180-degree impedance/admittance rotation.

If additionally `T_0(x)=L`, the existing projective-horizon complementarity theorem gives

```text
T_1(x) join T_1(x^(-1)) = L,                                (4)
```

whereas (1) gives

```text
T_1(Gamma(x)) join T_1(Gamma(x^(-1))) = T_1(Gamma(x)).       (5)
```

Thus a Smith chart can fold a complete pair of raw projective horizons into one reported horizon.
This is a coordinate-information law, not a claim that the Smith chart loses the whole generated
differential field.

## Proof

Put `y=M(x)`.  Hypertranscendence makes `x` transcendental, hence the denominator `cx+d` cannot
vanish under the nondegeneracy condition.  The inverse identity

```text
x = (d y-b)/(-c y+a)
```

then shows that any differential-algebraic relation for `y` would make `x` differentially
algebraic.  Hence `y` is HT.  Inversion preserves HT, and the same argument applies to
`M(x^(-1))`.

Let `I(t)=t^(-1)`.  Direct multiplication of the projective matrices gives

```text
M I M^(-1) = [ A  B ]
              [ C  D ]

A = b d-a c,
B = a^2-b^2,
C = d^2-c^2,
D = a c-b d = -A.                                           (6)
```

The determinant of this representative is

```text
A D-B C = -(a d-b c)^2 = -Delta^2 != 0.                     (7)
```

Consequently

```text
M(x^(-1)) = (A y+B)/(C y+D).                                (8)
```

Apply the projective jet-horizon stabilizer law to the HT element `y`.  It states that the first
tail in (8) equals `T_1(y)` exactly when

```text
C=0 and delta(A/D)=0.                                       (9)
```

If (9) holds then `C=0`, which is `d^2=c^2`.  Conversely suppose `C=0`.  By (7), `A D != 0`.
Since `D=-A`, one has `A/D=-1`, so `delta(A/D)=0` without any constancy assumption on
`a,b,c,d`.  This proves (1).  The all-tail form of the same stabilizer theorem proves (2).
Equation (3) is (8) for `(a,b,c,d)=(1,-1,1,1)`.  Equations (4) and (5) follow respectively from
the existing reciprocal-horizon complementarity theorem and from equality plus idempotence of
field join.

## Hostile audit

1. **Classical Smith-chart collision.**  The 180-degree impedance/admittance rule is classical and
   is not the novelty claim.  It is the `d=c` specialization of (1).
2. **Elementary Möbius-conjugacy collision.**  Formulae (6)--(8) are elementary projective algebra.
   The new content, if the parent flag theorem survives specialist scrutiny, is the iff relation
   between the coefficient locus and equality of all positive-order differential-field horizons.
3. **Differential Lüroth collision.**  Differential Lüroth theory says that generators of one
   differential-rational function field are homographically related.  It does not classify when
   the fields generated only by their positive-order jets agree.
4. **Wrapper attack.**  The general theorem is not restricted to the Smith coefficients and does
   not merely rename the parent stabilizer: it classifies a two-chart comparison after conjugating
   inversion and proves a raw-complementarity/reported-folding fracture.
5. **Coefficient-constancy attack.**  No premise `delta a=delta b=delta c=delta d=0` is used.  On
   the folding locus the surviving affine slope is identically `-1`.
6. **Pole attack.**  HT plus `Delta != 0` forces every denominator used in the proof to be nonzero;
   the theorem does not hide a partial-function hypothesis.
7. **DA boundary.**  A DA element can have a collapsed jet flag, so HT is essential rather than an
   ornamental assumption.
8. **Characteristic-two boundary.**  The intended differential fields have characteristic zero;
   there `d^2=c^2` is the union `d=c` or `d=-c` and has the fixed-point interpretation above.
9. **RH pressure test.**  The theorem controls coordinate information only.  It neither produces
   source-resolved passivity nor discharges an RH-equivalent positivity proposition.
10. **Computation audit.**  The discovery and proof are symbolic; no numerical experiment or
    numerical pre-certification was used.

## Literature boundary

- Phillip H. Smith's 1939 *Transmission Line Calculator* introduced the classical chart.  Standard
  impedance/admittance use rotates the reflection coefficient by 180 degrees, equivalently (3).
- D'Alfonso--Jeronimo--Solerno, *Effective differential Lüroth's theorem*, Journal of Algebra 406
  (2014), DOI `10.1016/j.jalgebra.2014.02.022`, records the classical differential Lüroth parent
  and the homographic relation between generators.
- Exact-statement searches covered Smith impedance/admittance duality, Möbius conjugation of
  inversion, differential Lüroth generators, jet filtrations, derivative-tail fields, and
  projective stabilizers.  They found the classical parents but no theorem matching (1)--(5).
  This supports only a provisional candidate-new-synthesis verdict.

## Bounded law and practical-rule census

The census is exhaustive for the bounded search class used in this investigation: named laws and
standard practical rules directly governing one-port/multiport impedance, passive or contractive
scattering, positive-real/Herglotz response, projective positive metrics, and their spectral or
network consumers.  Laws with no source, hypothesis, or composition contact with the three formal
areas are outside the search class.

| Law or rule | Existing corpus contact | Tested verdict |
|---|---|---|
| Smith/Cayley impedance--reflection transform | `CayleySchur`, `ProjectiveJetHorizon` | **New exact composer:** (1)--(5); does not create passivity. |
| Schwarz--Pick / Schur contraction | `CayleySchur`, `MobiusFiniteSchurTransfer` | Preserves a proved Schur bound; cannot supply the missing prime-source sign. |
| Herglotz/Nevanlinna / positive-real law | `PrimeLogHerglotz`, CCM passivity interfaces | RH-facing instances are consumers or iff criteria; no unconditional source discharge found. |
| Foster reactance theorem | finite rational lossless synthesis | Inapplicable to the exact logarithmic prime spectrum; useful only for finite rational surrogates. |
| Brune/Cauer/Darlington synthesis | dyadic passive-network card | Requires positive-real rational input or a prior passive realization; using the continued source is circular. |
| Transmission-line / ABCD Möbius cascade | `IsingCavityRapidityAudioCascade` | Exact finite composer already formalized; the scalar normalized RH premise is not produced. |
| Redheffer star product / feedback closure | CCM and finite Schur colligations | Can preserve local contractivity and connect apertures; source-resolved passivity and convergence remain open. |
| Schur complement / Kron reduction / star--mesh | `CCMComplexMellinColligation` | Removes internal ports but preserves rather than proves the unresolved critical-defect sign. |
| Bode--Fano matching bounds | capacity and passive-response lanes | Post-passivity bandwidth consumer; cannot prove a response passive or holomorphic. |
| Kramers--Kronig dispersion | analytic response lanes | Causality/analyticity composer after boundary control; does not create the missing positive measure. |
| KYP / positive-real / bounded-real lemma | finite colligation interfaces | Converts a proved storage inequality to frequency passivity and back; not a source of that inequality. |
| Small-gain / circle / passivity interconnection | finite Schur transfer and feedback | Useful closure rule for constructed blocks; raw prime delays fail the required input class. |
| Kirchhoff matrix-tree / Rayleigh monotonicity / HPP | prime Kirchhoff matroid card | Finite positive incidence is useful; regular-only/HPP shortcuts fail and the weighted source weld is open. |
| Nyquist / argument principle / Routh--Hurwitz | exact divisor tomography | Zero/pole consumer, strictly downstream of the missing zero-free half-plane response. |
| Thevenin--Norton / impedance--admittance inversion | projective horizon modules | **Classified by (1)--(5):** inversion changes raw HT horizons, while exactly the folding charts erase that distinction. |
| Reciprocity / losslessness / J-unitarity / optical theorem | `FiniteConstraintGroupAverage`, `SoninLogCoordinateScattering` | **Hypothesis discharge:** the involutive unitary master constraint is exactly twice the complementary projection. |
| Wigner--Smith / Friedel / Birman--Krein delay laws | Wigner--Smith HT observability and matrix tomography | Operationally exposes HT phase data and finite projective rank; does not produce source passivity. |
| Birkhoff--Hilbert / Thompson projective contraction | `CapacityLoewner` | Two-sided finite Loewner comparison exists; convergence use requires an explicit positive cofinal map first. |
| OPUC Schur algorithm / paraorthogonal roots | Xi Cayley--OPUC card | Root selector and finite moment geometry are closed; source moment/Verblunsky identification remains open. |
| KMS / fluctuation--dissipation | passive KMS response card | Finite positive response is available; equality/convergence to the continued prime--arch source remains open. |

The census leaves one genuinely RH-bearing open core unchanged: construct a source-first positive
finite-aperture colligation, prove cofinal passive convergence, and identify its limit with the
continued dyadic source on an open overlap.  All other tested laws are bridges, consumers,
classifiers, or no-go mechanisms around that core.

## Gates

- [x] exact source-pure statement
- [x] bounded internal corpus audit
- [x] external parent and exact-statement search
- [x] hostile collision and falsification audit
- [x] dependency-closed paper proof
- [x] unconditional Lean formalization
- [x] isolated source check
- [x] targeted module build
- [x] generated indexes refreshed and the new module is reachable from the HTGeometry umbrella
- [x] axiom audit
- [ ] repository-wide lint green (blocked only by unrelated universal-phase and prime-radial
  umbrella debt listed below)

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ProjectiveImmittanceHorizon.lean`: passed with no
  diagnostics;
- `lake build GaloisForLFunctions.HTGeometry.ProjectiveImmittanceHorizon`: passed (`8505` jobs);
- `#print axioms` for the HT-observation theorem, both folding iff theorems, and the Smith
  complementarity theorem reports only `propext`, `Classical.choice`, and `Quot.sound`;
- the project lint/index gate was run after formalization; any remaining failures are recorded as
  unrelated pre-existing or concurrent umbrella/index debt, not silently attributed to this module:
  `UniversalPhaseCoherenceAvoidance`, `UniversalPhaseCoherenceEntropy`,
  `UniversalPhaseCoherenceMinimax`, `UniversalPhaseCoherenceTargetMeasure`,
  `FinitePrimeCoefficientDifferentialField`, `PrimeRadialFusionConductorLaw`,
  `PrimeRadialFusionFieldCorrespondence`, `PrimeRadialFusionKolchinRank`,
  `PrimeRadialFusionRankSurfaceLaw`, and `PrimeRadialFusionRankSurfaceRealization`.  Concurrent
  source edits also made `LEAN_API.md` and `LEAN_OVERVIEW.md` stale during the check-generated scan;
  the indexer was rerun after that scan.
