# Xi reciprocal Clifford-square source route to RH

- **ID:** `xi-reciprocal-clifford-square-source-rh`
- **Stage:** 5-failed
- **Type:** `FALSIFIED` in full-source Hilbert/closed-graph category; exact RH coordinate retained
- **Lean bridge:** `formal/GaloisForLFunctions/RHTower/XiReciprocalCliffordSquare.lean`
- **Source construction:** `formal/GaloisForLFunctions/RHTower/WeightOneCliffordDirac.lean`
- **Terminal input:** `formal/GaloisForLFunctions/RHTower/XiReciprocalSquareSourceCore.lean`

## Claim

The source Clifford algebra is now explicit.  With `D=t d/dt`, the weight-one inversion
`Jf(t)=t^(-1)f(t^(-1))` obeys `JDJ=-(D+1)`.  Hence the centered generator

```text
C = D + 1/2
```

anticommutes with `J`.  For every real `a`, the source Dirac expression

```text
Q_a = C + aJ
```

satisfies `Q_a^2=C^2+a^2` on smooth scale profiles.  This is proved in Lean without Xi zeros.

The remaining claim is to close `Q_a` on the source Hilbert space and construct a unitary,
resolvent, or scattering comparison to the continued-Cauchy realization of the reciprocal Xi
operator.  Under that comparison its decomposition has the form

```text
R = A + B,
A* = A,
B* = -B,
AB = -BA.
```

and the same Clifford mixed terms cancel:

```text
R^2 = A^2 + B^2 = (R^2)*.
```

The existing reciprocal-square theorem turns this weaker even symmetry into RH.  This route does
not require `R` itself to be self-adjoint: the skew sector may be nonzero, but it must anticommute
with the Hermitian sector.

## Two-ended chain

```text
completed prime--Gamma/theta Dirac object, source-defined before the Xi divisor
  -> weight-one inversion J and centered scale generator C=D+1/2
       [PROVED SOURCE + LEAN: CJ=-JC]
  -> explicit source Clifford expression Q_a=C+aJ
       [PROVED SOURCE + LEAN: Q_a^2=C^2+a^2 on smooth profiles]
  -> closed Hilbert-space realization of Q_a and Q_a^2
       [PROVED PAPER: logarithmic unitary gives d/dx+aR on H¹,
        square d²/dx²+a² self-adjoint on H²]
  -> spectral determinant / scattering comparison with completed Xi
       [OPEN CORE A: xi(rho)=0 sends a^2+(rho-1/2)^2 into spectrum(Q_a^2+V_source)]
  -> continued-Cauchy comparison with the reciprocal-square readout
       [OPTIONAL OPEN CORE B: source-to-divisor intertwiner]
  -> R_Xi^2 is self-adjoint
       [PROVED LEAN: square_isSelfAdjoint_of_self_skew_anticomm]
  -> every centered reciprocal-square Xi coordinate is real
       [PROVED LEAN: unconditional Cauchy closure and fiber readout]
  -> every Xi zero lies on Re(s)=1/2
  -> RH
       [PROVED LEAN CONDITIONAL CAPSTONE:
        riemannHypothesis_of_xiReciprocalCliffordPolarization].
```

The comparison may be weakened to quadratic reality on the algebraic continued-Cauchy source
span, because the existing closure theorem reaches every exact multiplicity fiber.  A full
all-carrier unitary equivalence is therefore sufficient but not logically necessary.

## Exact prime--Gamma boundary splice

The arithmetic scalar boundary function is already source-defined:

```text
T(z) = continuedPrimeArchSourceRelativeTrace(z),
F(z) = -T(z)/z.
```

The corpus proves that `F` is exactly the functional-equation-paired reciprocal-square resolvent.
It also proves that the sector inequality

```text
0 <= Re(z) Im(F(z)),          0 < Im(z) < 1/2,
```

is equivalent to RH.  Therefore a positive self-adjoint Weyl/resolvent realization of `F` as the
boundary function of the closed weight-one Dirac square, or of a self-adjoint prime--Gamma
perturbation of it, would complete the route.

An abstract Nevanlinna realization theorem cannot supply this step: its hypothesis that `F` is a
Herglotz/Stieltjes function is precisely the missing sector sign and hence RH-equivalent.  The
boundary triple, cyclic source vector, and perturbation must be constructed directly from the
theta--Euler--Gamma object before the scalar sign is read.  This is the exact positive residue of
the abstract-realization no-go.

## Candidate source architectures

1. **Weight-one inversion Dirac split — constructed algebraically.**  The centered dilation is
   skew-adjoint on `L²(R_+,dt)` at the formal level and the inversion is a self-adjoint involution;
   their exact anticommutation is proved on smooth profiles.  Logarithmic transport proves the
   closed square on `H²(R)`.  The missing work is the completed determinant/scattering identity,
   not the graded algebra or bulk operator closure.
2. **Tame/wild Clifford split.**  Put the finite-prime Euler sector in the Hermitian component and
   the archimedean Gamma/Stokes sector in the skew component.  A source supersymmetry would have to
   exchange them and force their anticommutator to vanish after completion.
3. **Theta parity Dirac split.**  Use the weight-one inversion and the even/odd theta-cusp sectors
   as the grading, with the quadratic scale Hamiltonian as `D^2`.  The reciprocal spectral
   parameter would then be a first-order Dirac coordinate whose square is source self-adjoint.
4. **Relative resolvent superconnection.**  Realize the continued prime--Gamma Cauchy packets as
   boundary values of two graded resolvents.  A flat superconnection could force the mixed
   anticommutator to be an exact boundary term that vanishes on the source core.

Only the first construction's smooth source algebra is established; every determinant or
continued-Cauchy comparison remains `[CONJECTURE]`.

## Exact no-go and circularity audit

Every bounded operator has the formal Hermitian/skew decomposition

```text
A = (R + R*)/2,     B = (R - R*)/2.
```

This decomposition alone gives no new information.  Its anticommutator is proportional to

```text
R^2 - (R*)^2,
```

so asking the canonical pieces to anticommute is exactly asking `R^2` to be self-adjoint.  Lean
also proves the global consumer predicate
`XiReciprocalCliffordPolarization` equivalent to RH: under RH the trivial split
`A=R_Xi, B=0` works.  Therefore a valid proof cannot obtain the decomposition by manipulating the
target operator after its divisor is known.  It must construct an independent source grading and
then prove the comparison.

## Firewalls

1. The reciprocal Xi operator is indexed by the actual divisor.  Its abstract Clifford split is a
   terminal consumer interface, not a source proof.
2. Taking `B=0` reduces the route to ordinary Hilbert--Polya self-adjointness and adds nothing.
3. Defining `A` and `B` from `R_Xi` by adjoints merely rewrites square self-adjointness.
4. Trace reality of `R_Xi^2` is unconditional under conjugate pairing and cannot orient individual
   divisor fibers.  The relation must hold on the continued Cauchy packets.
5. A Krein-self-adjoint source operator is not automatically Hilbert-self-adjoint after squaring;
   the metric comparison and domains must be proved.
6. For unbounded Dirac pieces, formal anticommutation on a core does not by itself imply
   self-adjointness of the closed square.  Here that attack is discharged on paper by logarithmic
   transport to `d/dx+aR`; it remains a firewall for any prime--Gamma perturbation.
7. The source grading must be fixed before spectral zeros are read and cannot depend on their
   orientation.
8. Declaring `F=-T/z` to be a Weyl function by an abstract realization theorem assumes the
   Nevanlinna sector property that the route is meant to prove.  A source-built boundary triple is
   required.

## Positive theorem extracted from the no-go

`[PROVED LEAN]` In any complex Hilbert space, the sum of an anticommuting self-adjoint and
skew-adjoint bounded operator has self-adjoint square.  Hence any genuine graded source
factorization immediately upgrades to an RH capstone, while any failed construction identifies
its precise defect as the mixed anticommutator `AB+BA`.  The defect is an operator-valued,
orientation-sensitive source target; it cannot disappear through scalar conjugate-pair
cancellation.

## Status

- `[PROVED LEAN]` abstract Clifford cancellation gives a self-adjoint square;
- `[PROVED LEAN SOURCE]` `C=D+1/2` anticommutes with the actual weight-one inversion and
  `(C+aJ)^2=C^2+a^2` on every smooth scale profile;
- `[PROVED PAPER SOURCE]` the logarithmic unitary closes `Q_a` on transported `H¹` and gives the
  self-adjoint square `d²/dx²+a²` on `H²`;
- `[PROVED LEAN]` the Mellin symbol `a^2+(w-1/2)^2` is a real affine transform of the existing
  quadratic-scale energy and its reality at all Xi zeros is equivalent to RH;
- `[PROVED LEAN]` a Clifford polarization of the reciprocal Xi operator implies RH;
- `[PROVED LEAN NO-GO]` the bare global polarization predicate is RH-equivalent;
- `[PROVED NO-GO]` the canonical Hermitian/skew split merely repackages the missing condition;
- `[OPEN CORE]` construct a self-adjoint prime--Gamma boundary/scattering perturbation of the
  explicit bulk square whose Weyl function is the already explicit `-T(z)/z`, and prove the
  determinant comparison with Xi; a continued-Cauchy intertwiner is a stronger optional
  realization.

## 2026-08-01 terminal full-source audit

The open-core wording above is superseded for this route.  Two unconditional source-specific
closure theorems now exhaust the proposed regular Hilbert realization.

1. `xiTheta_continuousBoundaryReporter_eq_zero` proves that a continuous full-domain reporter on
   any normed carrier with dense ordinary-`L²` source image is zero if it kills the complete
   translated theta orbit.  Its contrapositive
   `xiTheta_nonzero_continuousBoundaryReporter_forces_escape` gives the exact survivor: a nonzero
   reporter must see a source translate or ordinary `L²` must fail to embed densely.
2. `hilbertGram_l2PartialOperator_not_closable` removes the boundedness loophole.  For an arbitrary
   Hilbert target and an arbitrary partial ordinary-`L²` operator whose domain contains the full
   theta Schwartz core, every nonzero positive momentum-symmetric Hilbert-Gram realization which
   kills the completed theta source is nonclosable.  No RH, simplicity, divisor enumeration, or
   continuity of the Gram map in ordinary `L²` is assumed.

The free Clifford bulk does close, but its square is the constant-coefficient operator
`d²/dx²+a²`; it has no arithmetic determinant.  Finite-rank theta coupling produces a Cauchy
response built from `|XiC|²` and loses Xi phase.  Finite-channel scalar-principal-symbol local
couplings are pure gauge on the line or yield finitely many arithmetic lattices on an interval.
An abstract Weyl realization of `-T(z)/z` assumes the Nevanlinna sign already proved equivalent to
RH.  These are distinct failures, not one missing technical lemma.

### Exact killing mechanism

The full source orbit is Wiener-cyclic in ordinary `L²`.  Positivity and pair symmetry propagate
theta nullity to a dense radical.  A nonzero Hilbert Gram map therefore has a dense proper
ordinary-`L²` kernel image and admits an `L²`-null sequence whose Hilbert image is one fixed nonzero
vector.  Its graph closure contains `(0,y)` with `y≠0`, so no partial realization on the full source
core is closable.  A closed self-adjoint realization is therefore impossible in the specified
full-source category.

### Strongest positive survivor

The complete surviving positive source form is a singular temperate Fourier rigging supported on
the real Xi divisor.  Its ordinary-`L²` radical is dense, proper, and nonclosed.  Any future spectral
construction must consequently use a genuinely partial/discontinuous essential-boundary relation,
a carrier in which ordinary `L²` is nondense, or a source-selected domain that does not kill the
complete cyclic bulk.

The finite zero-eigenfunction span is not ruled out.  It is not a source construction: proving that
the source selects and retains every Xi conormal is exactly the conservativity/limiting-absorption
statement which forces real quadratic parameters and hence RH.  Likewise a source-built
infinite-rank determinant would be a new route, not a repair of this regular Clifford completion.

### New insight and route status

`[FORMALIZED NEW SOURCE-SPECIFIC CONSEQUENCE]` The arbitrary-Hilbert-target closed-graph obstruction
shows that singularity is forced at graph level, not merely at metric level.  The explicit Clifford
algebra remains a valid exact RH coordinate, but it is not an independent source producer.

**Status:** `RETIRED / FORMALLY CLOSED NO-GO` for the advertised full-source Hilbert/closed-graph
realization.  This does **not** claim that every conceivable Hilbert--Pólya operator is impossible.
It closes precisely the source completion, finite-rank/local coupling, and abstract-Weyl shortcuts
audited above.
