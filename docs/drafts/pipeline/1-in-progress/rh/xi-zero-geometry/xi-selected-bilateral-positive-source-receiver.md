# Xi-selected bilateral positive source receiver

## Status

In progress.  Exact positive receiver and exact obstruction frozen.  No RH claim.

## Mission

Construct a positive receiver for the genuine Meyer prime character
`chi_p(rho)` which retains the Xi divisor, prime label, forward coefficient
`chi_p(rho)`, inverse coefficient `chi_p(rho)⁻¹`, and fixed source normalization.
Such a receiver would force `‖chi_p(rho)‖ = 1` and hence the critical line.

Toeplitz-gas compression is excluded by
`not_exists_sourceHorizontalCanonicalLaurentToGasLanding`: its one-sided
isometry satisfies only one inverse relation.

## Conjecture / hostile-audit loop

### C1 — complete the algebraic Meyer reporter by Riesz representation

**Conjecture.**  The unconditional nonzero Meyer eigenfunctional extends to
the half-density Hilbert completion, so unitary centered translation forces
its eigenvalue to have modulus one.

**Failure.**  `DeningerMeyerHalfDensityL1Completion` proves that the actual Xi
evaluation is bounded on the canonical invariant completion iff the divisor
is already on the critical line.  Riesz completion therefore assumes the
desired theorem.  Label: `[REDISCOVERED] [CIRCULAR]`.

### C2 — put forward and reflected coefficients in two independent positive blocks

**Conjecture.**  Positivity of the two reciprocal blocks forces each block to
be contractive; multiplying the inequalities gives unit modulus.

**Failure.**  Separate positive completions may rescale their diagonal masses
by reciprocal factors.  Reflection exchanges the two Xi fibres but does not
identify their norms on one fixed carrier.  This is the existing
exchange-versus-fold wall.  Label: `[BRIDGE] [FAILED PRODUCER]`.

### C3 — source/Gamma naturality kills the rescaling

**Conjecture.**  A natural positive receiver cannot carry a nontrivial
Radon--Nikodym correction.

**Failure.**  For every nonzero complex character value `z`, the unique
correction

```text
Delta(z) = |z|^2
```

satisfies

```text
Delta(z) z⁻¹ = conjugate(z).
```

For the actual centered flow this correction is

```text
Delta_rho(t) = exp(2 t (Re rho - 1/2)).
```

It is positive, multiplicative in `t`, reciprocal under critical-line
reflection, and equals the already-constructed prime-tail source
countercharacter at prime time.  Therefore it is genuine source/Gamma
naturality, not a prime-local fitted ghost.  Covariant source-capacity
conservation uses exactly this correction.  Naturality alone cannot make it
trivial.  Label: `[BRIDGE] [SHARP NO-GO]`.

### C4 — fixed-star bilateral positivity

**Survivor.**  Let `z = chi_p(rho)` and define two two-orientation matrices:

```text
M_mod(z) = [[1, z], [|z|^2 z⁻¹, |z|^2]],
M_can(z) = [[1, z], [z⁻¹, 1]].
```

`M_mod(z)` is unconditionally positive semidefinite: using
`|z|^2 z⁻¹ = conjugate(z)`, it is the rank-one Gram matrix of
`(1, conjugate(z))`.  It is the exact modular-covariant positive receiver.

`M_can(z)` is coefficient-faithful in both orientations and uses one fixed
unit source normalization.  If it is positive semidefinite, Hermitian
symmetry forces `z⁻¹ = conjugate(z)`, hence `|z| = 1`.  Conversely, if
`|z| = 1`, `M_can(z) = M_mod(z)` and is positive semidefinite.  Thus

```text
M_can(chi_p(rho)) >= 0  <->  ‖chi_p(rho)‖ = 1
                          <->  Re rho = 1/2.
```

This is not a Toeplitz-gas landing: no unilateral shift, range projection,
or Gibbs state occurs.  It is the minimal two-orientation source moment
receiver.  Label: `[BRIDGE] [NOVELTY UNVERIFIED]`.

## Paper proof

Fix an Xi divisor support point `rho` and prime `p`.  Put
`z = chi_p(rho)`.  The exponential definition gives `z != 0`.  Let
`Delta = |z|^2 = z * conjugate(z)`.  Then

```text
Delta z⁻¹ = z conjugate(z) z⁻¹ = conjugate(z).
```

Consequently

```text
M_mod(z) = [1, conjugate(z)]^* [1, conjugate(z)]
```

and is positive semidefinite.

If `M_can(z)` is positive semidefinite, it is Hermitian.  Comparing its
`(1,0)` entry with the conjugate of its `(0,1)` entry gives
`z⁻¹ = conjugate(z)`.  Multiplication by `z` gives
`1 = z conjugate(z) = |z|^2`; nonnegativity of the norm gives `|z| = 1`.
Conversely `|z| = 1` makes `Delta = 1`, hence `M_can(z) = M_mod(z)` and the
canonical matrix is positive semidefinite.

The corpus identity
`norm_deningerMeyerXiPrimeGammaCharacter_eq_halfGammaClock` and positivity of
`log p` identify `|z| = 1` with
`primeDepthBVWoldXiCenteredRate rho = 0`, hence `Re rho = 1/2`.

At prime time, `Delta` is also the inverse-oriented Gamma ghost by
`norm_sq_deningerMeyerXiPrimeGammaCharacter`.  Using
`riemannReflectedSourceEntropy = -sourceCayleyTransverseRate`, it equals
`xiCenteredFlowSourceCountercharacter rho (log p)`.  This proves that the
off-line modular correction is source-derived and explains why covariant
positivity does not imply fixed-star positivity.

## Open core

Construct, from the arithmetic source rather than from an RH-equivalent
boundedness premise, a proof that `M_can(chi_p(rho))` is positive semidefinite
for every retained Xi divisor.  Equivalently: prove that the source-derived
modular countercharacter acts trivially on the selected bilateral receiver.
Global/equivariant positivity, one-sided gas compression, separate reflected
blocks, contractible ghosts, and covariant capacity conservation do not
supply this fixed-star descent.

## External novelty audit

Meyer gives a nuclear Frechet spectral realization, Paugam an unconditional
symplectic pairing, and Deninger explains why a natural real Weil/Hodge
realization is obstructed.  Connes--Consani semilocal positivity remains a
framework whose global positivity is RH-bearing.  None of these sources
constructs the fixed-star, Xi-fibre-selected receiver above.  This is only a
bounded audit, so novelty remains `[NOVELTY UNVERIFIED]`.

## Lean plan

1. Define actual Meyer modular weight `Delta_p(rho) = ‖chi_p(rho)‖^2`.
2. Prove `Delta * chi⁻¹ = star chi` and identify `Delta` with both Gamma ghost
   and prime-time source countercharacter.
3. Define modular and canonical `2 x 2` source receiver matrices.
4. Prove modular receiver positive semidefinite unconditionally.
5. Prove canonical receiver positive semidefinite iff `‖chi‖ = 1`, pointwise
   iff the critical line, globally iff RH.
6. Wire leaf module into `RHTower.lean`; run only leaf Lean check/build and
   formal lint, never umbrella build.

## Lean status — 2026-08-17

Formalized in
`formal/GaloisForLFunctions/RHTower/XiSelectedBilateralPositiveSourceReceiver.lean`
and wired into `formal/GaloisForLFunctions/RHTower.lean`.

Proved unconditionally:

- actual Meyer character is nonzero and its modular weight is positive;
- modular-star identity and uniqueness of the correction;
- correction equals inverse Gamma ghost and arithmetic source
  countercharacter at prime time;
- modular-covariant bilateral receiver is a positive semidefinite rank-one
  Gram for every retained Xi divisor;
- fixed-star canonical receiver positivity implies `‖chi_p(rho)‖ = 1`;
- canonical positivity iff norm one iff `Re rho = 1/2` iff integral Cartier
  Gamma reporter existence;
- global canonical receiver existence iff RH;
- off line, positive modular receiver is provably distinct from canonical
  receiver.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/XiSelectedBilateralPositiveSourceReceiver.lean` passed;
- exact leaf build
  `lake build GaloisForLFunctions.RHTower.XiSelectedBilateralPositiveSourceReceiver`
  passed;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- static lint found no issue in this module or its umbrella wiring, but the
  repository-wide reachability gate remains red on three unrelated pre-existing
  unimported modules:
  `FrankensteinThetaTerminalFisherEntranceWall`,
  `HedenmalmThetaDirectCayleyReflectionPortDefect`, and
  `SchanuelValueFieldInstance`.

The requested unconditional **canonical** receiver is not constructed: that
would prove RH by the formal endpoint above.  What is constructed
unconditionally is the unique source-natural modular receiver, together with
the proof that replacing it by a fixed-star receiver is exactly the remaining
RH-strength descent law.  This is a sharp fail-and-pivot result, not a proof of
RH.

## Fixed-star/unit-diagonal descent audit — 2026-08-17

### C5 — quaternionic CCM Real structure supplies the fixed star

**Conjecture.**  Compose exact CCM Real equivariance with cyclic reversal and
descend the resulting operation to the Xi-selected two-orientation receiver.

**Failure.**  The exact CCM operator Real structure is a conjugate-linear
*multiplicative* involution: it preserves product order and the rational shift
label.  Hilbert adjoint is anti-multiplicative and reverses the shift label.
Cyclic reversal supplies that label reversal, but then acts on the opposite
source orientation.  Identifying the result with the original orientation is
exactly the same-fibre source-dagger law already classified as RH-equivalent.
Thus CCM Real continuity gives cross-fibre covariance, not fixed-star descent.
Label: `[BRIDGE] [FAILED PRODUCER]`.

### C6 — endpoint charge quantizes the modular defect

**Conjecture.**  Combine the even integral horizontal collision charge with
the unconditional endpoint off-line charge bound below `93/2000`; a positive
off-line class would then violate integrality.

**Failure.**  The two charges are not coefficient-faithfully equal.  Horizontal
collision charge has an ordinate-independent quantum `2`, whereas endpoint
charge weights each copy by a reciprocal-square ordinate factor.  Corpus
identifies the latter with a *weighted* Ward index, not the integral collision
index.  At unbounded height there is no uniform positive lower comparison.
This is exactly the uniformity wall in `IntegralityAndUniformity`; the small
endpoint bound yields height gaps, not exclusion.  Label:
`[FRANKENSTEIN] [FAILED PRODUCER]`.

### C7 — remove unit diagonal rather than construct it

**Conjecture.**  Unit diagonal may be the missing normalization; allow arbitrary
diagonal masses while retaining the literal forward coefficient `chi` and
inverse coefficient `chi⁻¹`.

**Proof / strongest survivor.**  For arbitrary `d0 d1 : C`, put

```text
M(d0,d1;chi) = [[d0, chi], [chi⁻¹, d1]].
```

If this matrix is positive semidefinite, Hermitian symmetry of its `(1,0)` and
`(0,1)` entries gives `chi⁻¹ = conjugate(chi)`.  Diagonal entries never enter.
Since `chi` is nonzero, this is equivalent to `|chi| = 1`.  Conversely, when
`|chi| = 1`, choosing `d0=d1=1` gives the already-proved positive canonical
receiver.  Therefore

```text
exists d0 d1, M(d0,d1;chi_p(rho)) >= 0
  <-> conjugate(chi_p(rho)) = chi_p(rho)⁻¹
  <-> |chi_p(rho)| = 1
  <-> Re(rho) = 1/2.
```

This is a strict sharpening: **unit diagonal carries no RH burden**.  Any
positive receiver with the two literal coefficients already forces fixed-star
descent.  Changing diagonal masses cannot repair an off-line character; the
only unconditional repair is the previously classified modular change of the
inverse off-diagonal coefficient itself.  Global arbitrary-diagonal receiver
existence is still equivalent to RH, so this does not manufacture the missing
producer.  Label: `[BRIDGE] [PROVED ON PAPER] [NOVELTY UNVERIFIED]`.

### Revised open core

Construct an arithmetic source operation that identifies literal inversion
with Hilbert star on each selected Xi fibre:

```text
conjugate(chi_p(rho)) = chi_p(rho)⁻¹.
```

No diagonal normalization theorem is needed.  CCM Real equivariance, cyclic
reversal on the opposite orientation, positive modular covariance, endpoint
weighted Ward bounds, and integral collision quantization do not prove this
same-fibre identity.

## Lean status — fixed-star/unit-diagonal audit

Added to
`formal/GaloisForLFunctions/RHTower/XiSelectedBilateralPositiveSourceReceiver.lean`:

- literal fixed-star descent as a pointwise proposition;
- arbitrary-complex-diagonal receiver retaining exact `chi` and `chi⁻¹`;
- positivity of any such receiver implies `|chi|=1` without using either
  diagonal entry;
- fixed-star equality, arbitrary-diagonal positivity, unit-diagonal positivity,
  critical-line placement, and the integral Gamma reporter are pointwise
  equivalent;
- global arbitrary-diagonal receiver existence is equivalent to RH.

Verification:

- scratch proof passed with `lake env lean /tmp/XiFixedStarScratch.lean`;
- exact leaf check passed;
- exact leaf build passed; no umbrella build was run;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- static lint found no issue in the edited leaf.  Repository-wide reachability
  remains red on unrelated worktree modules:
  `FrankensteinThetaTerminalFisherEntranceWall`,
  `HedenmalmThetaDirectCayleyReflectionPortDefect`, `XiRectangleZeroCount`,
  `JetLevelThreeDescent`, `JetOrderOneSlicing`, and `QuadraticLevelThree`.
