# One HT field carries every finite constraint geometry at every Krein index

- **ID:** `universal-constraint-krein-index-product-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / strengthening of the constraint--orientation product
- **Scientific status:** `[CONJECTURE] [PAPER CORE PROVED] [LEAN IN PROGRESS] [NOVELTY UNVERIFIED]`
- **Statement:** One fixed prime-log maximal-translation HT field realizes every finite localized
  Stanley--Reisner differential matroid at every prescribed finite Pick-kernel negative-square
  index.  The representative changes only by a finite rational Cauchy surgery.

## Exact law under construction

Let `g_*` be the fixed universal positive prime-log source and let `K_*` be its embedded
differential-translation field over `C(z)`.  For every `k >= 0`, the target is an explicit finite
real-pole rational correction `r_k` such that:

1. `g_* + r_k` generates exactly `K_*` as an embedded differential field;
2. its complete universal translated palette remains differentially algebraically independent;
3. it realizes the exact localized Stanley--Reisner differential matroid of every finite complex;
4. its Nevanlinna--Pick kernel has exactly `k` negative squares.

Thus the promoted product is

```text
all finite nonlinear differential constraint geometries x N
```

where the second coordinate is the actual Krein--Langer index, not the previously formalized
combinatorial count of negative residues.

## Paper proof

Choose `k` distinct real surgery poles away from the prime-log support.  On any finite upper-half-
plane node packet, the positive background Pick Gram is positive semidefinite and the negative
atoms contribute a rank-`k` subtraction.  Therefore every negative-definite subspace has dimension
at most `k`.

For the lower bound, choose `k` nodes so that the square Cauchy sampling matrix `V` is invertible.
If `H` is the background Gram on those nodes, then

```text
H - T V V* < 0
```

for every sufficiently large positive `T`.  Quantitatively, with `W V* = I`, the sup-operator norm
gives

```text
Re <x,Hx> <= k ||H|| ||x||^2,
||x|| <= ||W|| ||V* x||,
<x,VV*x> = ||V*x||_2^2 >= ||V*x||_infinity^2.
```

Hence

```text
T=(k ||H||+1)||W||^2
```

makes the Gram strictly negative on every nonzero vector.  This supplies a `k`-dimensional negative
subspace.  Together with the rank upper bound, the global negative-square index is exactly `k`.

Rational-gauge invariance then supplies items 1--3 without changing the source field.

## Positive selector consequence

The constraint coordinate and the actual Krein index are independently variable inside one
embedded HT field.  Therefore a faithful arithmetic positivity selector must retain a marked,
cofinally compatible coupling between finite constraint sewings and the distinguished index-zero
representative.  The positive datum is such a coupling section; neither projection alone can carry
it.

## Formalization plan

- [x] isolate an explicit large-negative-scale matrix lemma;
- [x] prove the required sup-norm coercivity estimate in a scratch Lean module;
- [ ] formalize the universal positive prime-log Pick Gram and prove it positive semidefinite;
- [ ] formalize the signed finite-atom Gram and exact global negative-square predicate;
- [ ] instantiate Cauchy nonsingularity and the explicit scale;
- [ ] compose with universal rational-gauge field invariance and the Stanley--Reisner theorem;
- [ ] build the HT geometry umbrella, lint, and inspect axioms;
- [ ] run the exact parent-literature audit before claiming new scientific knowledge;
- [ ] add the strengthened theorem to a publication-ready paper only after the Lean gate passes.

## Boundary audit

The matrix scaling and signed-atomic inertia calculations are classical bridges.  The only possible
candidate-new content is their exact compatibility with one fixed universal maximal-translation HT
field carrying all finite nonlinear constraint geometries.  Scientific novelty is not claimed until
that combined theorem is formalized and compared against generalized Nevanlinna, universal
translation, and differential-matroid literature.

