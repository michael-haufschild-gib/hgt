# Finite squarefree Euler complement rigidity

- **ID:** `finite-squarefree-euler-complement-rigidity`
- **Stage:** 3-formalized
- **Formalized companion:** `./finite-squarefree-euler-complement-rigidity-formalized.md`
- **Type:** THEOREM (paper and Lean) — `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** An exact centered functional equation for a finite product of degree-one Euler
  factors forces every local parameter to have critical modulus; equivalently, every factor zero
  lies on the symmetry line.

## Theorem

Let `P` be a finite set of distinct primes, put `Q=prod_(p in P) p`, and choose complex parameters
`a_p`. Define

```text
F_a(s)=prod_(p in P) (1-a_p p^(-s)).
```

Assume `epsilon != 0` and

```text
F_a(s)=epsilon Q^(1/2-s) F_a(1-s)                     (1)
```

for every complex `s`. Then

```text
a_p^2=p for every p in P,
epsilon=(-1)^|P| (prod_p a_p)/sqrt(Q), and epsilon^2=1.
```

Consequently every zero of `F_a` has real part `1/2`. Conversely, if `a_p^2=p` for every prime,
then (1) holds with the displayed value of `epsilon`.

## Proof `[PROVED HERE]`

For `S subset P`, write `a_S=prod_(p in S)a_p` and `n_S=prod_(p in S)p`. Expanding the left side
of (1) gives coefficient `(-1)^|S|a_S` at the distinct frequency `n_S^(-s)`. Expanding the right
side and replacing `S` by its complement gives coefficient

```text
epsilon sqrt(Q) (-1)^(|P|-|S|) a_(P\S)/n_(P\S).
```

Uniqueness of finite Dirichlet polynomials therefore gives, for every `S`,

```text
a_S=epsilon (-1)^|P| sqrt(Q) a_(P\S)/n_(P\S).        (2)
```

Taking `S=P` yields `a_P=epsilon (-1)^|P|sqrt(Q)`, so every `a_p` is nonzero. Taking
`S=P\{p}` in (2) and substituting the preceding identity gives

```text
a_P/a_p=a_P a_p/p,
```

hence `a_p^2=p`. Squaring the formula for `epsilon` now gives `epsilon^2=1`.

If `1-a_p p^(-s)=0`, taking absolute values gives `|a_p|p^(-Re s)=1`; since `|a_p|=sqrt(p)`,
`Re s=1/2`.

Conversely, `a_p^2=p` implies

```text
a_(P\S)/n_(P\S)=1/a_(P\S).
```

With `epsilon=(-1)^|P|a_P/sqrt(Q)`, the right side of (2) is
`a_P/a_(P\S)=a_S`, proving every coefficient identity and hence (1). The empty-prime case reduces
to `1=epsilon` and is included.

## Attack and exact boundary

The proof is top-coefficient rigidity. It uses `S=P` and the complements `P\{p}`; the functional
equation acts by Boolean complement only because `P` has a maximal squarefree monomial `n_P`.
For the all-prime Euler source, complements of finite prime sets are cofinite and are not Dirichlet
coefficients. There is no top coefficient from which to recover the local equations `a_p^2=p`.

Thus this theorem does not approximate an RH proof as `P` grows. Any passage through increasing
finite prime inventories would install a cutoff/limit flow and would still lack a coefficientwise
infinite complement. The completed gamma factor supplies the global functional equation, but not
an infinite Boolean top coefficient.

## Parent and novelty verdict

After erasing the Euler notation, the proof is coefficient reversal for a factored multiaffine
self-reciprocal polynomial, followed by unique factorization. This is standard reciprocal-polynomial
algebra and is an immediate finite Dirichlet-polynomial argument. It fails the parent-theory and
anti-theatre gates and is retained only as a sharp boundary theorem.

## Research consequence

The infinite completed-source problem cannot be solved by importing finite coefficient complement.
Its missing compatibility must be defined directly on the pointed infinite source--divisor
incidence object. In particular it must couple the all-prime coefficient rays to a selected pole
of the continued logarithmic flux; neither source recovery nor a finite functional-equation actor
contains that coupling.

## Gates

- [x] 0 -> 1: exact finite statement and degeneracies specified.
- [x] 1 -> 2: complete coefficient proof and converse.
- [x] 2 -> 3: literal functional equation, local-square rigidity, zero-line consequence, and
  converse formalized unconditionally.
- [ ] 3 -> 4: ineligible as a standalone new-science result.

## Lean formalization closure — 2026-08-15

- **Exact target retained:** the full finite-prime functional equation, local-square classification,
  zero-line consequence, and converse; no quotient, finite-sample, or coefficient-only surrogate is
  being promoted as the card theorem.
- **Corpus reuse audited:** `RHTower/Sieve/EulerExpansion.lean` supplies the squarefree expansion
  and injectivity of `T ↦ ∏ p∈T p`; `Hurwitz/JointPowerOrbit.lean` supplies Vandermonde recovery for
  distinct power sequences; `RHProofLab/EulerProductArithmetic.lean` supplies compatible finite
  Euler-product algebra.
- **Closed proof architecture:** specialize the functional equation at every negative integer
  `s = -m`.  Both sides become finite linear combinations of the distinct sequences
  `m ↦ (∏ p∈T p)^m`; Vandermonde recovery gives every complement-coefficient identity, from which
  the top coefficient and one-prime complements force `a_p^2 = p`.  The converse is then proved
  coefficientwise before restoring the entire functional equation.
- **Closed Lean core:**
  `RHTower/FiniteSquarefreeEulerComplementRigidity.lean` now proves both
  directions of the exact Boolean-complement coefficient algebra:
  `finiteEulerComplement_coefficients_force_localSquares` and
  `finiteEulerComplement_coefficients_of_localSquares`; it also now proves the
  literal centered epsilon formula
  `finiteEulerComplement_epsilon_formula` and its exact square consequence
  `finiteEulerComplement_epsilon_sq`.  The source type is an arbitrary finite
  prime set; no one-prime or finite-sample surrogate is used.
- **Literal wrapper closed:**
  `RHTower/FiniteSquarefreeEulerFunctionalEquation.lean` defines the exact
  product `F_a(s)` and exact complex functional equation `(1)`.  It derives
  every Boolean-complement coefficient identity from `(1)` sampled at all
  negative integers, by the distinct squarefree-product Vandermonde theorem;
  it then proves local squares, the displayed epsilon formula and square,
  every-zero real part `1/2`, and the full complex functional-equation
  converse from local squares.  No finite-sample or coefficient-only
  surrogate is promoted as the card theorem.
- **Audit:** direct
  `lake env lean GaloisForLFunctions/RHTower/FiniteSquarefreeEulerFunctionalEquation.lean`,
  focused `lake build GaloisForLFunctions.RHTower.FiniteSquarefreeEulerFunctionalEquation`,
  and `#print axioms` for all capstones passed.  Axioms are only `propext`,
  `Classical.choice`, and `Quot.sound`; source scan found no `sorry`, `admit`,
  `axiom`, `opaque`, or `unsafe` declaration.  The module is wired into
  `GaloisForLFunctions.RHTower`; no umbrella build was run.
