# Rational CDD decimation cocycles as a physical source of hypertranscendence

- **ID:** `rational-cdd-decimation-cocycle`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL QFT PROGRAM / CONSTRAINT SELECTION PRINCIPLE
- **Scientific status:** `[CONJECTURE] [EXPLICIT MODEL PROVED ON PAPER]`
  `[PARENT COLLISION IDENTIFIED] [NOVEL CORE OPEN]`
- **Scope:** general hypertranscendental physics; no RH or distinguished special function
- **Parent model:** `geometric-cdd-hypertranscendental-local-qft.md`
- **Statement:** The physical source of HT is not discrete scale invariance by itself but a
  nontrivial rational cocycle left when one complete resonance shell is removed.  A source-minimal
  derivation of that cocycle from QFT coarse-graining would turn HT from an engineered scattering
  choice into a dynamical prediction.

## Exact decimation law

For a scalar scattering germ `P(t)` and `0<q<1`, one-shell divisor decimation has the form

```text
P(t)=B(t)P(qt),                                             (1)
```

where `B` is the finite CDD factor carried by the shell crossing the cutoff.  The physical
compatibility laws are

```text
B(-t)=B(t)^(-1),
|B(t)|<=1 for Re(t)>=0,
B(0)=1.                                                     (2)
```

The minimal reality-paired seed

```text
B(t)=((1-t)/(1+t))^2                                       (3)
```

gives the unique normalized holomorphic germ

```text
P(t)=product_(k>=0) B(q^k t).                              (4)
```

Its divisor is a complete geometric orbit.  The rational-or-HT difference-Galois theorem then
gives an exact dichotomy:

```text
finite/rational divisor closure, or hypertranscendence.     (5)
```

For `(3)`, the infinite zero/pole orbit rules out the rational branch.  The parent card proves
that the corresponding regular scattering function constructs a local interacting factorizing
QFT and has an HT Wigner--Smith phase-delay reporter.

## Relation to cyclic RG

The pole rapidities of `(4)` have real parts

```text
mu_k=arcosh(Cq^(-k)),
mu_(k+1)-mu_k -> -log(q).                                  (6)
```

Their resonance masses therefore obey the asymptotic Russian-doll ratio `q^(-1/2)`.  This is the
standard UV limit-cycle signature.  It is not the novelty: cyclic RG, infinite resonance towers,
and elliptic factorized `S`-matrices are established parent physics.

The distinction is exact.  A strict cycle satisfies `S(theta-T)=S(theta)` and can be represented
by differentially algebraic elliptic functions.  A decimation cocycle satisfies `(1)` with a
nontrivial shell factor.  Its accumulated shell product is forced into the rational-or-HT
dichotomy.  Therefore

```text
discrete scale invariance does not imply HT;
nontrivial rational scale cocycle + infinite divisor does.  (7)
```

## Fields/Nobel gate

Equations `(1)`--`(7)` assemble parent theories and one explicit physical existence model.  That
is not yet new medal-level science.  The surviving claim is deliberately narrower and harder:

`[CONJECTURE -- SOURCE-MINIMAL CDD DECIMATION]` There exists a local QFT coarse-graining functor
whose action on an intrinsic, presentation-independent scalar scattering sector removes exactly
one physical resonance shell and induces `(1)` with rational `B`.  At a nontrivial fixed cocycle,
the QFT observable algebra is HT in the canonical kinematic coordinate.

The conjecture must supply all of the following:

1. a cutoff-independent definition of the shell and decimator from the QFT, not from the known
   divisor of `P`;
2. a proof that the induced cocycle is rational and respects unitarity, crossing, and locality;
3. presentation invariance under admissible field redefinitions and CDD-normalization choices;
4. a Lagrangian, operator-algebraic, or functorial construction whose reconstructed scattering
   law is the cocycle fixed point;
5. an observable reporter retaining the HT logarithmic derivative stably.

A proof would make hypertranscendence a consequence of a physical renormalization constraint.
Without it, `(4)` remains a rigorous but selected member of Lechner's broad admissible scattering
class.

## Cosmology pressure test

The cosmological analogue would replace resonance-shell decimation by horizon-shell decimation.
One e-fold would remove one geometric mode shell and leave a rational cocycle on a wavefunction
coefficient or its flat-space residue.  This is only a research criterion.  Choosing an HT initial
state, transfer function, or primordial spectrum by hand is circular and does not realize the
conjecture.

## Falsifiers

Retire or weaken the conjecture if:

1. the decimator can be defined only after the target divisor is supplied;
2. every source-natural local-QFT shell map produces a strict periodic/elliptic DA cycle instead
   of a nontrivial cocycle;
3. the rational shell factor is removable by an admissible DA normalization;
4. regularity/locality forces every nontrivial cocycle fixed point out of the physical scattering
   class;
5. the real-axis logarithmic reporter is compactly or gauge-theoretically invisible.

## Primary parent literature

- A. LeClair and G. Sierra, *Renormalization group limit-cycles and field theories for elliptic
  S-matrices*, <https://arxiv.org/abs/hep-th/0403178>.
- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.
- P. G. O. Freund and A. V. Zabrodin, *A Hierarchical Array of Integrable Models*,
  <https://arxiv.org/abs/hep-th/9208033>.
