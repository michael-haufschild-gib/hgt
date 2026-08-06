# Route-R degree-six BV--Green physical cyclic producer

- **ID:** `route-r-degree-six-bv-green-physical-cyclic-producer`
- **Stage:** 1-in-progress
- **Type:** RH-BEARING SOURCE PRODUCER
- **Scientific status:** `[CONJECTURE] [OPEN CORE]`
- **Parent:** `../3-formalized/route-r-deninger-bv-green-positive-unit-comparison.md`
- **Canonical open-core name:** `XI_BV_GREEN_STOKES_STRICT_DESCENT`

## Exact claim

Construct before divisor specialization a completed, coefficient-faithful arithmetic cyclic
complex `C_src`, a degree-one chain `G_6`, and strict comparison maps

```text
C_src,1  --b_src-->  C_src,0
  | F_1                 | F_0
  v                     v
C_phys,1 --b_phys--> C_phys,0 --R_phys--> completed Xi conormal
```

such that:

1. `b_src G_6` is the literal ordinary-integer boundary
   `[S_6^*, Q S_6] = 6^-1 Q - P_6 Q`;
2. `F_0 (b_src G_6) = b_phys (F_1 G_6)` strictly, with ordinary-prime, depth, divisor, and
   multiplicity provenance retained;
3. the fixed physical reader is boundary-blind on this independently constructed target,
   `R_phys (b_phys y)=0`;
4. its divisor fibre is the already fixed reflected physical marginal,
   `R_phys (F_0 (b_src G_6)) = routeRDeningerBVGreenReflectedBoundary rho`;
5. none of `C_src`, `C_phys`, `F_0`, `F_1`, `b_phys`, or boundary-blindness is defined using Xi-zero
   location, the centered rate, vanishing of the physical boundary, same-fibre norm preservation,
   source-dagger preservation, cofinal equicontinuity, singular Stokes flatness, or RH.

The conclusion is

```text
forall rho : XiDivisorSupport,
  routeRDeningerBVGreenReflectedBoundary rho = 0.
```

By the formalized positive-unit comparison this implies the explicit Route-R Hodge-mate
coefficient is zero for every prime and divisor fibre and therefore proves RH.

## Known frontier

- `[CORPUS]` The operator boundary and its Hochschild primitive exist before specialization.
- `[CORPUS]` Its fixed physical reflected marginal equals the degree-six Deninger mate curvature.
- `[CORPUS]` That marginal is a strictly positive unit times Route R's explicit Hodge-mate
  coefficient.
- `[CORPUS]` Source cyclic traces kill the Hochschild boundary, but the fixed physical reader does
  not descend through that quotient off the critical line.
- `[CORPUS]` Generic mapping cones, common determinant correction, reflection-hyperbolic balance,
  KMS untwisting, and resolved chain exactness have already been falsified as producers.
- `[OPEN CORE]` Construct boundary-blindness from independently defined completed arithmetic
  source geometry while preserving the fixed physical fibre.

## Anti-circularity tests

- Specializing first and then quotienting by the physical defect is forbidden.
- A trace or target whose definition contains `rho.re`, mate gain, `K_6`, or the desired kernel is
  a consumer, not a producer.
- Replacing the fixed reader by an ordinary cyclic trace erases coefficient faithfulness.
- Boundary-blindness may not be postulated as a structure field without an independent theorem
  deriving it from source operations.
- A conditional Lean theorem packaging the diagram does not close this card.

## Internal collision audit

1. `DeningerOrdinaryIntegerBVGreenStokesRadialComparison.lean` constructs the literal source
   boundary
   \[
     B_n=[S_n^*,QS_n]=n^{-1}Q-P_nQ=b(S_n^*\otimes QS_n)
   \]
   and proves that its normalized physical value is
   `n⁻¹ (1 - mateGain(n,s)⁻¹)`.  For `n=6`, physical cyclic descent is already equivalent to
   `Re(s)=1/2`.
2. `MobiusThetaPhysicalParacyclicSourceNullHomology.lean` proves that the retained relative
   prime class is one-dimensional and nonzero.  Fixed-grade evaluation does not descend through
   the source boundary off the critical line.
3. `RouteRPreDivisorRationalCartierCoinvariantFunctor.lean` constructs the genuine cyclic
   coinvariant quotient and retains the prime atom, but its physical dilation defect remains the
   same Bockstein coefficient.
4. `DeningerCompletedXiHellingerGammaCofaceClosedSaturation.lean` proves that nonzero displacement
   makes the ordinary completed Hellinger coface span dense in the full two-channel target.
5. `DeningerCompletedXiHellingerGammaResolvedProvenanceSaturation.lean` sharpens the graph repair:
   off axis its relative quotient is *exactly* completed incidence provenance.  No additional
   Hodge marginal survives in which the BV--Green class could be cancelled.
6. `DeningerResolvedDefectHellingerGammaBalancedCofaceNoGo.lean` proves every finite balanced
   coface grade is transverse to the antidiagonal resolved Green defect.
7. `SourceDaggerCyclicMonodromyRigidity.lean` proves that a nonzero equivariant atomic landing from
   an involutive source to monodromy `delta` forces `delta=1`.  Constructing that landing, rather
   than the rigidity implication, is the open RH-bearing step.
8. Common `det₂` correction, reflection-hyperbolic balance, countercharacter untwisting, generic
   mapping cones, and the old dense-core boundary are already formalized no-gos.  They respectively
   preserve the anomaly, cancel both orientations for every rate, erase provenance, repackage
   exactness, or extend only as the zero operator.

## External mechanism audit

Primary work on twisted cyclic cohomology, modular/KMS spectral triples, and zeta-regularized
determinants confirms the structural alternatives already visible internally:

- modular weights replace ordinary cyclicity by twisted cyclicity and retain the modular defect;
- zeta/`det₂` regularization has a residue or multiplicative anomaly on non-trace-class
  commutators;
- a singular trace kills finite-rank or leading logarithmic pieces but does not identify the fixed
  same-fibre conormal with an ordinary cyclic trace.

No audited source supplies the project-specific coefficient-faithful map from the retained
rational-adelic provenance class to the fixed Xi conormal.  External literature therefore does not
close or weaken the named open core.

## Conjecture / falsification log

### C1 — ordinary or singular cyclic trace on the Wold--Green domain

`[FALSIFIED]`  If both `S_6^* QS_6` and `QS_6 S_6^*` lie in a cyclic domain, their difference has
trace zero.  The fixed physical value is nonzero at every off-line fibre.  The Dixmier/residue
coefficient can vanish because the two logarithmic densities agree; the retained finite modular
anomaly is precisely what the physical reader measures.  Calling the residue the physical reader
loses coefficient faithfulness.

### C2 — twisted/KMS cyclicity

`[FALSIFIED AS AN ORDINARY DESCENT PRODUCER]`  The half-density character turns the source reader
into a twisted trace.  Its twisted boundary is zero, but the ordinary Hochschild boundary acquires
the factor `1 - mateGain⁻¹`.  Thus twisted cyclicity calculates the Route-R obstruction rather than
annihilating it.

### C3 — paired Gamma orientations

`[FALSIFIED AS A FIXED-SAME-FIBRE PRODUCER]`  Reciprocal orientation costs permit a weighted
two-orientation cancellation for every positive gain.  The projection to either fixed physical
orientation is not cyclic and restores the explicit reflected defect.  This is the already-known
hyperbolic-balance no-go in chain language.

### C4 — resolved Hellinger provenance absorbs the boundary

`[FALSIFIED]`  Off axis, the resolved quotient is canonically the provenance carrier itself.  The
Hodge channels are saturated, not available for cancellation.  Any surviving annihilator must act
directly on the retained incidence class.

### C5 — composite-degree (`6=2·3`) factorization curvature

`[FALSIFIED]`  The exact source identity
\[
 B_{mn}=n^{-1}B_m+P_mB_n
\]
and its reversed factorization reduce under the physical character to the multiplicativity of
the mate gain.  Their square curvature is identically flat for every centered rate and therefore
cannot select rate zero.

### C6 — source integral/Cartier lattice on retained provenance

`[FALSIFIED]`  The source lattice carries a universal Laurent coordinate `t`.  Its integral unit
acts after base change by `t ↦ p^a`, with arbitrary real regulator `a log p`.  Integrality
quantizes the Laurent exponent, not the spectral base-change parameter.  This is the exact
counterexample already recorded in
`5-failed/xi-relative-torsion-integral-degree-quantization.md`.  A discrete physical line would
still need an independent source theorem forcing the specialization through its unitary locus.

### C7 — linear mixed-dagger Bianchi/null-homotopy

`[FALSIFIED BY NEW CORPUS]`  `DeningerFailureNerveMixedDaggerCoboundary.lean` proves on the actual
failure-nerve edge that source reversal minus analytic dagger is the mixed coboundary of the
constant identity cochain for *every* parameter.  The same file identifies the degree-six Gamma
term as its secondary norm transgression.  Thus linear exactness is true off line and cannot
annihilate the quadratic physical reporter.

### C8 — Hodge/Stokes on the lattice-torus or mixed `L¹/L²` completion

`[FALSIFIED WITHOUT AN INDEPENDENT CO-CLOSEDNESS LAW]`  The new lattice-torus formality and mixed
prime Banach completion provide honest source completions, but exactness plus completeness does
not kill the norm of an exact cochain.  The Stokes computation is
`‖δ1‖² = ⟨1,δ†δ1⟩`; its vanishing requires the independent co-closedness/boundary law
`δ†δ1=0`.  On the actual one-dimensional edge this condition is equivalent to unitarity of the
half-density character, hence to the critical-line condition.  Postulating it would rename the
target.

## Strongest positive survivor: normalized cyclic-reader wall

The failed cycles separate two questions that were previously conflated:

1. does a nonzero normalized cyclic reader exist on the literal degree-six Wold--Green pair?
2. does that source reader agree with the fixed same-fibre physical marginal?

The first question has a completely source-native positive answer.  For a positive-integer basis
vector `e_k`, write

\[
 d_k(T)=(Te_k)_k,
 \qquad
 \tau_6(T)=\frac56 d_1(T)+d_6(T).                         \tag{CR1}
\]

Then

\[
 \tau_6(Q)=\frac56+\frac16=1.                              \tag{CR2}
\]

Using `S_6^*QS_6=6^{-1}Q` and `S_6S_6^*=P_6`,

\[
 \tau_6(S_6^*QS_6)=\frac16,
 \qquad
 \tau_6(QS_6S_6^*)=\tau_6(P_6Q)=\frac16.                  \tag{CR3}
\]

So `tau_6` is normalized and cyclic on the exact pair defining the degree-six boundary, and

\[
 \tau_6(B_6)=0.                                             \tag{CR4}
\]

More generally, every linear reader cyclic on this pair kills `B_6`.  Therefore a normalized
pair-cyclic reader whose value on `B_6` agrees with the fixed physical marginal exists at a divisor
fibre `rho` exactly when

\[
 \operatorname{routeRDeningerBVGreenReflectedBoundary}(\rho)=0,
\]

which the positive-unit theorem identifies with `Re(rho)=1/2`.  Globally, physical cyclic descent
of `B_6` is equivalent to RH.

This result is not the requested producer.  It is a nonvacuous universal wall: source cyclic-reader
existence and normalization are solved unconditionally; the only missing datum is equality with
the fixed physical reader.  No alteration of Hochschild degree, trace normalization, completion,
or cyclic quotient can supply that equality.

### Dependency-closed proof

`(CR2)` follows because `Qe_k=k^{-1}e_k`.  The first identity in `(CR3)` follows from source Wold
scaling and `(CR2)`.  For the second, `P_6Qe_1=0` while `P_6Qe_6=6^{-1}e_6`, so `(CR1)` gives
`1/6`.  Subtracting proves `(CR4)`.  Conversely, if the physical marginal is zero, `tau_6` supplies
the normalized physical cyclic witness.  If any such witness exists, pair cyclicity makes its
boundary value zero, so agreement makes the physical marginal zero.  The already formalized
positive-unit comparison finishes the pointwise and global equivalences.

### Hostile audit

- `tau_6` is defined only from integer indices `1,6`, Wold operators, and reciprocal Green density.
- It does not mention `rho`, Xi, mate gain, the Hodge coefficient, or a zero predicate.
- Normalization rules out the zero-reader vacuity.
- Pair cyclicity is proved by direct source calculation, not stored as an assumed field.
- The theorem does not claim the physical comparison.  It proves that comparison is precisely the
  still-open RH-bearing operation.

## Gates

- [x] exact RH-bearing claim frozen
- [x] internal collision and failed-route audit complete
- [x] external primary-literature audit complete
- [x] conjecture/falsification cycles complete
- [ ] dependency-closed paper proof
- [ ] unconditional Lean proof

## 2026-08-06 formalization status

The requested physical producer remains open.  The strongest positive survivor is now formalized in
`RHTower/RouteRDegreeSixBVGreenPhysicalCyclicDescentWall.lean` and recorded at
`3-formalized/route-r-degree-six-bv-green-cyclic-reader-wall.md`.

Lean closes the literal Hochschild presentation, constructs the nonzero normalized source reader
`tau_6`, proves pair cyclicity and source boundary annihilation, and proves exact pointwise/global
classifiers for physical descent.  The remaining open premise is only the coefficient-faithful
equality between this source cyclic quotient and Route R's fixed same-fibre physical marginal.
That equality is not implied by source cyclicity; the classifier proves it is RH-equivalent.
