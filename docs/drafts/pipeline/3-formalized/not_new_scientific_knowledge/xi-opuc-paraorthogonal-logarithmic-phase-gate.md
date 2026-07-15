# Xi--OPUC paraorthogonal logarithmic-phase gate

- **ID:** `xi-opuc-paraorthogonal-logarithmic-phase-gate`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM / `[PROVED IN LEAN] [CONDITIONAL RH ENDPOINT] [OPEN SOURCE IDENTITY]`
- **Parents:** `xi-taylor-theta-tail-core-density-current`, finite OPUC root location
- **Statement:** A source-defined stable polynomial with a unimodular paraorthogonal terminal whose
  value at the dyadic logarithmic phase is a multiple of `XiC` proves the Riemann hypothesis.

## Exact theorem

Put

```text
u(z)=exp(i log(2) z).
```

Let `p_z` be a nonzero complex polynomial whose roots all lie strictly in the unit disk, let
`tau_z` be unimodular, and let

```text
T_z(X)=X p_z(X)-tau_z p_z^*(X)
```

be its paraorthogonal terminal polynomial.  If there is any amplitude `A(z)` such that

```text
T_z(u(z))=A(z) XiC(z)                                      (1)
```

for every complex `z`, then RH holds.  No nonvanishing or sign condition on `A` is needed.

## Proof

The exact phase modulus is

```text
|u(z)|=exp(-log(2) Im(z)).                                 (2)
```

Every zero of a paraorthogonal terminal built from a strictly disk-stable polynomial and a
unimodular endpoint lies on the unit circle.  If `XiC(z)=0`, equation `(1)` makes `u(z)` a zero of
`T_z`, so the paraorthogonal theorem and `(2)` give

```text
1=|u(z)|=exp(-log(2) Im(z)),
```

hence `Im(z)=0`.  Thus every centered Xi zero is real.  Equivalently, every zero of `xi` lies on
`Re(s)=1/2`, which is RH.  `QED`

This is a contradiction chain with both ends closed:

```text
off-line Xi zero
  -> interior dyadic phase root of T_z
  -> paraorthogonal root has unit modulus
  -> exp(-log(2) Im(z))=1
  -> Im(z)=0
  -> contradiction.
```

## Positive boundary from the Prouhet no-go

The phase-adapted Prouhet symbol already has `u(z)` as a double root for every `z`.  Therefore,
when `Im(z)>0`, that symbol cannot itself be a stable paraorthogonal terminal.  This is not merely
a route failure: it identifies the positive form of the required producer.

The Prouhet symbol may be used as a finite annihilator inside the construction, but the terminal
in `(1)` must be a distinct source-defined stable polynomial.  A successful argument must derive
its evaluation identity from the theta--prime--Gamma source; it cannot relabel the signed Prouhet
packet as an OPUC polynomial.

The abstract exclusion is formalized independently: any polynomial with one certified strict
open-disk root differs from every stable paraorthogonal terminal.  This also rules out a generic
positive-Toeplitz realization of the phase-adapted packet throughout the open Fourier strip.

## Corpus splice audit

- The theta-tail density supplies a positive probability source and therefore canonical finite
  Toeplitz sections.  The missing edge is not positivity: it is the exact terminal evaluation
  `(1)`.
- The finite Gamma-shift Dirichlet residual exposes the first arithmetic multiplier and may
  contribute to `A(z)` or a finite coefficient formula, but its right-half-plane asymptotic gives
  neither strict OPUC stability nor `(1)` in the critical strip.
- The self-consistent Haar endpoint cancels an affine current by using that current.  Substituting
  it as the OPUC endpoint would remain circular unless `(1)` is first proved from an independent
  source recurrence.
- The positive prime--archimedean circle states are built from the Xi divisor moments and cannot
  serve as the source-pure producer.  Their OPUC machinery remains reusable after a divisor-free
  theta or completed Euler moment sequence is identified.
- Finite projective-horizon monodromy supplies no stable polynomial or terminal evaluation
  identity and does not discharge `(1)`.

## Exact open producer

Construct `p_z`, `tau_z`, and `A(z)` from the completed theta--prime--Gamma source, before selecting
zeros, and prove all three statements:

```text
p_z != 0,
every root of p_z lies in |X|<1,
T_z(exp(i log(2) z))=A(z) XiC(z).                         (3)
```

Equation `(3)` is the sole mathematical gap in this chain.  It is an evaluation identity plus
finite stability, not an RH-equivalent positivity assumption or a divisor-selected carrier.

## Lean declarations

Files:

- `formal/GaloisForLFunctions/HTGeometry/ParaorthogonalInteriorRootExclusion.lean`
- `formal/GaloisForLFunctions/RHTower/XiOPUCParaorthogonalPhaseGate.lean`

Declarations:

- `polynomial_ne_finiteParaorthogonalPolynomial_of_isRoot_norm_lt_one`
- `xiDyadicLogPhase`
- `norm_xiDyadicLogPhase`
- `im_eq_zero_of_norm_xiDyadicLogPhase_eq_one`
- `riemannHypothesis_of_paraorthogonal_dyadic_phase_XiC_value`

Targeted leaf builds pass.  The RH capstone axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] paraorthogonal interior-root exclusion formalized
- [x] dyadic phase modulus formalized
- [x] source evaluation identity converted to real centered Xi zeros
- [x] centered real-zero conclusion converted to RH
- [x] phase-adapted Prouhet terminal shortcut retired
- [x] positive successor stated as a distinct source terminal identity
- [ ] construct the divisor-free stable source polynomial family
- [ ] prove the exact terminal evaluation identity `(3)`
- [ ] discharge RH

