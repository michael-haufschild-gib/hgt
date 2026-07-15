# Finite algebraic state boundary for hypertranscendental clocks

- **ID:** finite-algebraic-state-hypertranscendence-boundary
- **Stage:** 3-formalized
- **Type:** `[PROVED ELSEWHERE]` / corpus-strengthening formalization
- **Parent theory:** differential-algebraic realization and input/output elimination
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/FiniteAlgebraicStateBoundary.lean`

## Statement

Let `F ⊆ E` be differential fields of characteristic zero and let `x ∈ E`. Call `x` a finite
algebraic state observable when there is an intermediate field `S`, closed under differentiation,
such that `x ∈ S` and `trdeg_F S < aleph0`. Then

```text
FiniteAlgebraicStateObservable F x  ->  DifferentialAlgebraicOver F x.       (1)
```

Consequently,

```text
HypertranscendentalOver F x
  -> not (FiniteAlgebraicStateObservable F x).                              (2)
```

The nontrivial positive form is

```text
HypertranscendentalOver F x  and  x in S  and  derivationClosed S
  -> aleph0 <= trdeg_F S.                                                    (3)
```

In particular the ambient field of a hypertranscendental element has transcendence degree at
least `aleph0` over its coefficient field.

## Proof

Membership `x ∈ S` gives an order-zero algebraic relation for `x` over `S`, hence
`DifferentialAlgebraicOver S x`. The existing finite-transcendence descent theorem says that
differential algebraicity over a derivation-closed intermediate field of finite transcendence
degree descends to `F`. This proves `(1)`, and `(2)` is its contrapositive.

For `(3)`, if `trdeg_F S < aleph0`, `(1)` contradicts hypertranscendence. The ambient statement
also follows directly because the full derivative jet of a hypertranscendental element is an
algebraically independent sequence, so its cardinality gives the lower bound on transcendence
degree.

## Exact scope

The theorem applies after a proposed realization has been reduced to a derivation-closed field of
finite transcendence degree. This covers finite rational autonomous state-space systems and
finite algebraic differential state systems whose coefficients and inputs lie in the base. It
does not cover models with an HT coefficient, an HT oracle input, or a hidden state that already
contains the target; those violate the finite state-field premise rather than evade the theorem.

The statement is strictly broader than the corpus's finite linear boundaries:

- the state equations may be nonlinear and rational;
- no Koopman-invariant finite linear dictionary is required;
- no diagonalizable or finite-rank transfer operator is required;
- no time-evolution interpretation is used in the proof.

The field `S` is an observation budget. Differentiation orders what the clock reveals, and `(3)`
says those observations require infinitely many algebraically independent state coordinates. It
therefore implements the motif “hypertranscendence is about the observability structure of a
clock, not about temporal evolution” at the nonlinear algebraic-state level.

## Genomics, genetics, ML, and AI transfer

Rational biochemical and gene-regulatory ODE models generate a derivation-closed field from
finitely many concentration/state coordinates. Differential-algebra methods eliminate their
hidden states to obtain input/output differential invariants. Therefore an exactly HT genomic
clock signal cannot be the exact output of any fixed finite rational reaction-network state model.
The positive conclusion is that any exact algebraic-state realization must have unbounded state
transcendence degree.

Polynomial neural ODEs and recurrent neural ODEs admitting finite polynomial-system embeddings
fall under the same interface. The theorem does not challenge their approximation power. It says
that exact representation of an HT clock requires either infinite algebraic state complexity or a
non-algebraic primitive carrying HT-level information. This is a precise architecture test, not an
analogy.

## Physics transfer

Any finite rational minisuperspace, finite scalar-field ansatz, finite rational Hamiltonian
reduction, or finite algebraic effective-state closure also lands in `(1)` when its observable
field is derivation closed. An HT clock observable forces such an exact physical realization out
of every finite algebraic state budget. This is useful as a model-exclusion criterion, but it does
not assert that a concrete physical clock is hypertranscendental.

## Literature gate

- Y. Wang and E. D. Sontag, *Algebraic Differential Equations and Rational Control Systems*,
  SIAM J. Control Optim. 30 (1992), 1126--1149, DOI `10.1137/0330060`. Rational state-space
  realizability is equivalent to algebraic differential input/output equations.
- H. A. Harrington, K. L. Ho, and N. Meshkat, *Differential Algebra for Model Comparison*,
  arXiv:1603.09730. Hidden variables in biological ODE models are eliminated to measurable
  differential invariants.
- C. Fronk and L. Petzold, *Interpretable Polynomial Neural Ordinary Differential Equations*,
  Chaos 33 (2023), 043101, arXiv:2208.05072.
- M. Gonzalez, M. Petreczky, and E. Toth, *Realization Theory of Recurrent Neural ODEs Using
  Polynomial System Embeddings*, arXiv:2205.11989.

The mathematical elimination principle is established parent theory. The value of this card is
the exact Lean interface and its direct integration with the HT jet/transcendence-degree corpus;
novelty is not claimed.

## RH impact

The result does not orient prime--Gamma source incidence and does not prove RH. It strengthens
the search in three concrete ways:

1. a finite rational physical, genomic, or AI hidden-state model cannot generate an HT source;
2. finite nonlinear algebraic state models are now excluded, not only finite linear observers or
   finite Hankel-rank transfers;
3. any exact model proposed to discharge an RHTower hypothesis must expose an infinite state-rank
   mechanism or a source-specific non-algebraic primitive.

The surviving research target is positive: find a source-defined lower bound or sign law carried
by the infinite prime--Gamma state growth. Generic finite-state realization theory cannot supply
that orientation.

## Verification

The Lean module contains no `sorry`, `admit`, new axiom, `opaque`, or `unsafe` declaration. Its
capstone theorems are checked using only the standard logical axioms already present in mathlib.
