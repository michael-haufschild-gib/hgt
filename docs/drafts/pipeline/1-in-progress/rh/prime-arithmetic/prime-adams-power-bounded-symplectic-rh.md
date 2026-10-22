# Prime-Adams power-bounded symplectic realization to RH

- **ID:** `prime-adams-power-bounded-symplectic-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Lean bridge:** `formal/GaloisForLFunctions/RHTower/LocalDivisorJetAdamsMonodromy.lean`
- **Isometric bridge:** `formal/GaloisForLFunctions/RHTower/LocalDivisorJetAdamsIsometric.lean`
- **Local input:** `formal/GaloisForLFunctions/RHTower/LocalDivisorJetAdamsDilation.lean`

## Claim

Construct one completed prime--Gamma operator object, defined before and independently of the Xi
zero set, whose localization at a spectral point simultaneously supplies:

1. a symplectic self-adjoint realization, making each hypothetical right-half Xi order even;
2. the genuine Euler Adams semigroup on the corresponding local divisor jet, realized as a
   power-bounded operator semigroup in one source norm.

On an order-`m` jet the actual Adams weights are `1,n,...,n^(m-1)` for `n>=2`.  If `m>1`, the
cotangent weight `n` has unbounded iterates.  Power-boundedness therefore forces `m=1`, contradicting
the even multiplicity supplied by the same polarized source.  Hence the construction would prove
RH.

## Two-ended chain

```text
completed prime--Gamma Banach/KMS/operator object, source-defined before zeros
  -> one local spectral fiber and divisor filtration
       [OPEN CORE A: construct the object and local comparison]
  -> source symplectic self-adjointness on the fiber
       [OPEN CORE B: nondegenerate pointwise polarization]
  -> even local Xi order
       [PROVED LEAN mechanism]
  -> genuine Euler Adams semigroup on the same fiber
       [PROVED LEAN local weights; OPEN source identification]
  -> a uniform power bound for every Adams iterate on every local weight
       [OPEN CORE C: source contraction or isometric normalization]
  -> the expanding cotangent weight cannot occur, so m=1
       [PROVED LEAN: adamsDilation_powerBounded_forces_simple]
  -> order is simultaneously one and even
  -> no right-half Xi zero
  -> RH
       [PROVED LEAN CONDITIONAL CAPSTONE:
        riemannHypothesis_of_rightSymplecticRealization_of_rightAdamsDilationPowerBounded].
```

The intended theorem is not the conjunction of two unrelated zero-indexed assumptions.  The
operator norm, the Adams action, the spectral localization, and the alternating polarization must
all descend from one completed source construction.

## Correct power-map Adams host

The Bost--Connes multiplication isometry `mu_n |k> = |nk>` is **not** the Euler Adams action used
by the local jet: multiplication of the integer label is different from powering every Euler
base.  The correct counting-space source operator is instead

```text
V_n |k> = |k^n>.
```

Because `k -> k^n` is injective on positive integers, `V_n` is an isometry.  Its adjoint acts on
coefficients by pullback,

```text
(V_n^* f)(k) = f(k^n),
```

and is a contraction.  This adjoint, not `mu_n`, has the same variance as the local Adams law.

After removing the unavoidable value-amplitude from a prime derivative coefficient, its `j`-th
coordinate is

```text
f_j(k) = (-log k)^j,
```

and Lean proves the exact source covariance

```text
f_j(k^n) = n^j f_j(k).
```

For every `k,n >= 2` and `j>0`, Lean also proves `|f_j(k^n)|>|f_j(k)|`.  Thus the raw normalized
jet is a genuine generalized eigenpacket for `V_n^*`, but it lies outside the counting Hilbert
space; a nonzero Hilbert eigenvector with eigenvalue `n^j>1` would contradict contractivity.

Lean formalizes this exact consequence as
`adamsDilation_contractive_eigenpacket_forces_simple`: if a positive local packet has nonzero
vectors `v_j` and one complex-linear contraction satisfies

```text
U v_j = n^j v_j,              0 <= j < m,
```

then `m=1`.  The same-packet RH capstone is
`riemannHypothesis_of_rightPolarizedAdamsContractiveEigenpacket`.

The missing map is therefore sharper than a generic Adams intertwiner.  A completed prime--Gamma
localization must turn the generalized logarithmic jet into nonzero Hilbert vectors while
preserving the power-map pullback covariance and the alternating pairing.  An honest contraction
cannot do this for any positive jet direction.  Consequently a successful construction must
either annihilate every positive local direction globally, or place the localized vectors in a
boundary/residue space on which the contractive ambient action and finite divisor quotient are
related by a nontrivial exact sequence.  Scalar graded KMS covariance does not supply that exact
sequence.

The parity end is also placed on this same local packet.  Lean defines
`LocalAdamsSymplecticPolarization(m)` as a nondegenerate alternating form on `C^m`, proves that it
makes `m` even, and combines it directly with the isometric eigenpacket in
`riemannHypothesis_of_rightPolarizedAdamsIsometricEigenpacket`.  A separate spectral operator or
zero-indexed `SymplecticRealization` is no longer logically required.  The source localization must
carry the alternating form and the Adams intertwiner together.

## Why this is not the quasi-unipotent or pure-weight route

Power-boundedness is an analytic semigroup condition.  It neither asks the weights to be roots of
unity nor places them on a common weight circle by decree.  It could arise from a Markov dilation,
a contractive transfer operator, a unitary KMS implementation, or a bounded representation of the
prime-power semigroup.  The contradiction uses the whole forward orbit of the single weight `n`.

## Source-provider attack

A plausible provider is a completed Euler transfer operator whose prime-power endomorphisms act
contractively after a source-defined modular normalization, together with a skew polarization on
its local spectral fibers.  The normalization must preserve the relative weight between the
constant and cotangent directions.  If it divides each weight by its own growth, it has merely
erased the detector.

The operator need not generate Xi by a finite flow.  The required statement is a static
compatibility constraint: the source-defined norm says the entire Adams representation is bounded,
while the local divisor comparison computes a particular subquotient of that representation.

## Attacks and firewalls

1. The unnormalized Euler Adams semigroup is visibly expanding.  Any claimed bound must come from
   a completed source norm or dilation theorem, not from assuming the conclusion.
2. A scalar renormalization `n^{-j}` depending on the unknown local degree makes every eigenvalue
   one and is target-fed.  One source normalization must act uniformly before multiplicity is read.
3. Unitary implementation on an auxiliary GNS space does not imply boundedness on the divisor
   subquotient unless the comparison intertwines the actual Adams action.
4. Functional-equation dual weights can cancel operator growth in a product while each factor
   remains unbounded.  A determinant or total supertrace bound is insufficient.
5. Symplectic total dimension is even, but the RH contradiction needs evenness of the single
   generalized eigenspace at a right-half point.
6. A zero-indexed Banach space manufactured with a favorable norm after reading `m` is a consumer,
   not a source construction.
7. Power-boundedness may be impossible for the genuine completed Adams action.  If so, the precise
   positive residue is that every nonreduced local Euler divisor fiber forces exponential norm
   growth in every faithful finite-dimensional realization.
8. The Bost--Connes multiplication isometry uses the wrong semigroup action.  Replacing `k -> k^n`
   by `k -> nk` destroys the normalized jet eigenlaw and is not an admissible source provider.
9. The correct power-map isometry is infinite-dimensional and proper.  Its adjoint is contractive,
   so the raw expanding logarithmic eigenpacket cannot be an ordinary Hilbert subspace.  Any
   claimed localization must state the boundary/residue topology in which these generalized
   vectors become visible without silently abandoning the ambient norm.

## Positive theorem extracted from the obstruction

`[PROVED LEAN]` For every `n>=2`, a positive local divisor jet with the actual Adams-dilation
spectrum is power-bounded only when it is reduced.  Equivalently, any faithful realization of a
nonreduced Euler divisor fiber contains an explicitly expanding cotangent orbit.  This turns a
failed bounded-operator construction into a quantitative witness of nilpotent thickness.

## Status

- `[PROVED LEAN]` actual local Adams weights are `n^j`;
- `[PROVED LEAN]` power-bounded actual Adams dilation forces `m=1`;
- `[PROVED LEAN]` a faithful actual Adams eigenpacket inside one source isometry forces `m=1`;
- `[PROVED LEAN]` normalized prime-log coordinates obey `f_j(p^n)=n^j f_j(p)` and every positive
  coordinate grows strictly under a nontrivial power map;
- `[PROVED LEAN]` a faithful actual Adams eigenpacket inside one source contraction forces `m=1`;
- `[PROVED LEAN]` a nondegenerate alternating form on that same packet makes `m` even, and the
  coupled isometric or contractive same-packet capstone implies RH;
- `[PROVED LEAN]` symplectic local realization forces even multiplicity;
- `[PROVED LEAN CONDITIONAL]` the coupled properties at every right-half Xi zero imply RH;
- `[PROVED NO-GO]` determinant cancellation, auxiliary unitarity, and degree-dependent
  renormalization do not provide the needed local bound;
- `[OPEN CORE]` one completed source exact sequence carrying both pointwise symplectic polarization
  and a faithful boundary/residue realization of the generalized logarithmic Adams packet for the
  correct power-map pullback; an ordinary Hilbert eigenpacket is excluded by the proved
  contraction obstruction.
