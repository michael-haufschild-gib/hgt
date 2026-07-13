# Prime-Adams quasi-unipotent symplectic realization to RH

- **ID:** `prime-adams-quasi-unipotent-symplectic-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Lean bridge:** `formal/GaloisForLFunctions/RHTower/LocalDivisorJetAdamsMonodromy.lean`
- **Local input:** `formal/GaloisForLFunctions/RHTower/LocalDivisorJetAdamsDilation.lean`

## Claim

Construct one completed prime--Gamma object, defined before and independently of the Xi zero set,
whose localization at a spectral point has both of the following source structures:

1. a symplectic self-adjoint spectral realization, so the algebraic multiplicity of every
   hypothetical right-half Xi zero is even;
2. a regular-singular arithmetic local system whose genuine Euler Adams operation is the local
   divisor-jet dilation with weights

```text
1, n, ..., n^(m-1),  n >= 2,
```

and whose local monodromy theorem makes those weights quasi-unipotent.

For a positive-length jet, quasi-unipotence and `n >= 2` exclude the weight `n`; hence `m=1`.
The same hypothetical right-half zero would therefore have order both one and even, a
contradiction.  This would prove RH without leaving an independent multiplicity rung open.

## Two-ended chain

```text
completed prime--Gamma regular-singular object, source-defined before zeros
  -> one localization functor at a spectral parameter
       [OPEN CORE A: construct the object and local comparison]
  -> symplectic self-adjoint spectral fiber
       [OPEN CORE B: source polarization, not a zero-indexed realization]
  -> even local Xi order
       [PROVED LEAN mechanism: SymplecticMultiplicity]
  -> genuine Euler Adams action on the same local divisor fiber
       [PROVED LEAN coefficient law; OPEN source identification]
  -> weights 1,n,...,n^(m-1)
       [PROVED LEAN: LocalDivisorJetAdamsDilation]
  -> regular-singular arithmetic monodromy makes every weight a root of unity
       [OPEN CORE C: applicable geometric/quasi-unipotent monodromy theorem]
  -> m=1
       [PROVED LEAN: adamsDilation_quasiUnipotent_forces_simple]
  -> order is simultaneously one and even
  -> no right-half Xi zero
  -> RH
       [PROVED LEAN CONDITIONAL CAPSTONE:
        riemannHypothesis_of_rightSymplecticRealization_of_rightAdamsDilationQuasiUnipotent].
```

The two source conclusions must arise from one construction.  Merely assuming a zero-indexed
`SymplecticRealization` and separately assuming quasi-unipotence is the Lean consumer interface,
not yet the mathematical producer.

## Why this is not the pure-weight route

Pure weight asks all Adams eigenvalues to have one common norm.  This route instead asks the actual
local Adams representation to lie in the quasi-unipotent monodromy image of an algebraic
regular-singular connection.  It is a discrete arithmetic obstruction: the single expanding
cotangent weight `n` already contradicts finite-order semisimple monodromy.  No common-weight metric
or scalar trace identity is required.

## Source-provider attack

The most concrete target is a completed relative cohomology object with a tame finite-place
Gauss--Manin sector and an archimedean Gamma/Stokes sector.  Its local divisor filtration must
identify the Adams action before taking a determinant or trace.  The polarization must restrict
nondegenerately to the generalized eigenspace of each spectral point, while the finite-place
Adams action must be the actual prime-power substitution on the same fiber.

The construction is deliberately static: a comparison of two source constraints on one local
fiber.  It must not claim that Xi is propagated by a finite-dimensional differential flow.

## Attacks and firewalls

1. The ordinary Euler Adams semigroup is not finite monodromy.  Its weights cannot simply be
   declared roots of unity; an actual algebraic regular-singular local system and comparison map
   are required.
2. Regular-singular monodromy is not automatically quasi-unipotent for an arbitrary analytic
   connection.  The arithmetic/geometric hypotheses of the monodromy theorem must be constructed.
3. The completed Gamma sector is naturally irregular-singular.  A proof must isolate a tame local
   quotient carrying Adams while retaining the wild sector in the completed object; forcing the
   whole source to be regular-singular is likely false.
4. Functional-equation mirror pairing gives an even total dimension but is blind to the
   multiplicity of one right-half fiber.  The alternating form must restrict nondegenerately at
   that single eigenvalue.
5. Centered determinant one erases the expanding direction.  The full local spectrum, especially
   the weight `n`, must survive.
6. Defining a symplectic space or monodromy representation after reading the Xi multiplicity is
   target-fed and proves nothing about the source.
7. A finite-dimensional regular-singular object may encode a local constraint, but cannot be
   presented as a forbidden generative differential handle for Xi.

## Positive theorem extracted from the obstruction

`[PROVED LEAN]` The expanding Adams cotangent weight is a reducedness detector: for every `n >= 2`,
any positive local divisor jet on which the genuine Adams-dilation spectrum is quasi-unipotent has
length exactly one.  Thus failure of the RH route at the Gamma irregularity boundary still leaves
a source-independent theorem: any arithmetic regular-singular realization of an Euler divisor
fiber is automatically reduced.

## Status

- `[PROVED LEAN]` actual local Adams weights are `n^j`;
- `[PROVED LEAN]` quasi-unipotent actual Adams dilation forces `m=1`;
- `[PROVED LEAN]` symplectic local realization forces even multiplicity;
- `[PROVED LEAN CONDITIONAL]` the two properties at every right-half Xi zero imply RH;
- `[PROVED NO-GO]` ordinary Adams dynamics, centered determinants, and mirror pairing alone do not
  supply the source comparison;
- `[OPEN CORE]` one completed source object carrying both the pointwise symplectic polarization and
  the arithmetic regular-singular Adams localization.
