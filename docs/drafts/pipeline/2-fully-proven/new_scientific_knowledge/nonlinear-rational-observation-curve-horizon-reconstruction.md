# Nonlinear rational observation curves are visible through every HT derivative horizon

- **ID:** `nonlinear-rational-observation-curve-horizon-reconstruction`
- **Stage:** 2-fully-proven
- **Type:** GENERAL HT THEOREM / DIFFERENTIAL-RATIONAL OBSERVABILITY CLASSIFICATION
- **Scientific status:** `[PROVED ON PAPER] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `projective-horizon-building-schwarzian-complementarity`
- **Statement:** At every positive derivative depth, finitely many rational views of a free HT
  scalar reconstruct exactly the differential function field of their normalized observation
  curve if and only if that curve is not an affine line.

## Goal

Classify which finite static rational observation systems remain globally observable after deleting
every jet below an arbitrary positive depth. The result concerns simultaneous constraint fields.
Derivative depth is a filtration index, not a flow or time variable.

## Main theorem: normalization of the observation curve `[PROVED]`

Let `C` be an algebraically closed constant field of characteristic zero and let `x` be
hypertranscendental over `C`. Choose nonconstant rational functions

```text
R_1,...,R_m in C(z),   m>=1,
```

and let `T in C(x)` be an ordinary Luroth generator of their joint function field:

```text
C(R_1(x),...,R_m(x))=C(T).                                (1)
```

For `n>=1`, put

```text
L_n=C<(R_1(x))^(n),...,(R_m(x))^(n)>.
```

Then exactly one of the following holds.

1. The normalized observation curve is an affine line. Equivalently, for a generator `V` of
   `C(T)`, every `R_i` has the form `a_i V+b_i`. Then

   ```text
   L_n=C<V^(n)> < C<V>                                    (2)
   ```

   for every `n>=1`.

2. The normalized observation curve is not an affine line. Then

   ```text
   L_n=C<T>                                                (3)
   ```

   for every `n>=1`.

Thus the arbitrarily deep derivative horizons reconstruct the normalization of their joint
algebraic image and no larger finite cover above it. Affine linearity of that image, not derivative
depth, is the exact failure condition.

### Proof

Replace `x` by the differentially transcendental Luroth coordinate `T`. Differential Luroth gives
`L_n=C<u>` for some differential rational `u(T)`. Choose `R_1` nonconstant. Highest-jet coefficient
comparison, exactly as in Lemma 1 below, puts every slope ratio

```text
q_i(T)=R_i'(T)/R_1'(T)                                    (4)
```

in `L_n`.

If every `q_i` is constant, integration gives `R_i=a_iR_1+b_i`; the observation curve is a line,
`R_1` is a rational coordinate on its normalization, and `(2)` follows. Positive differential
order makes the inclusion strict.

Otherwise some `q_i` is nonconstant, so `T` is algebraic over `L_n`. Let `Z` be an `L_n`-conjugate
of `T`. Unique extension of the derivation and equality of the observed `n`-th jets give, by their
highest free jet coefficients,

```text
R_i'(Z) dZ/dT = R_i'(T)                                   (5)
```

for every `i`. Hence

```text
R_i(Z)=R_i(T)+c_i,   c_i in C.                            (6)
```

The translation vector `c=(c_i)` stabilizes the irreducible observation curve. A nonlinear
algebraic curve in affine space has trivial translation stabilizer in characteristic zero: if
`c!=0`, all integer multiples of `c` stabilize it, the Zariski closure is a one-dimensional
additive subgroup, and the curve is its affine-line coset. Therefore `c=0`. The functions `R_i`
generate `C(T)`, so `(6)` forces `Z=T`. Every conjugate is trivial and separability gives
`T in L_n`, proving `(3)`.

## Identity-view corollary: exact affine/non-affine dichotomy `[PROVED]`

Let `C` be an algebraically closed constant field of characteristic zero, let `x` be
hypertranscendental over `C`, and put `F=C<x>`. Let `R in C(z)` be nonconstant. For `n>=1`, define

```text
L_n(R)=C<x^(n),(R(x))^(n)>.
```

Then

```text
L_n(R)=F for every n>=1   iff   R is not affine.            (7)
```

If `R(z)=az+b`, then `L_n(R)=C<x^(n)>`, a proper depth-`n` jet tail. Every rational nonlinearity,
including every genuine projective denominator, has complete reconstruction power when paired
with the original horizon.

## Lemma 1: principal symbols recover the ordinary derivative

Assume `R` is non-affine and fix `n>=1`. Put `L=L_n(R)`. Differential Luroth gives `u in F` such
that `L=C<u>`. Let `m=ord_x(u)`. Both observed generators have exact differential order `n` in
`x`, and the coefficient of `x_n` in `delta^n R(x)` is `R'(x)`. Differential-order additivity
therefore gives rational differential expressions

```text
A(u,...,u_r)=x_n,
B(u,...,u_r)=delta^n R(x),
r=n-m.
```

Taking the formal partial derivative with respect to the highest jet `x_n` gives

```text
1     = A_(u_r) u_(x_m),
R'(x) = B_(u_r) u_(x_m).                                  (2)
```

The first line is nonzero, so division in `(2)` yields

```text
R'(x)=B_(u_r)/A_(u_r) in L.                                (3)
```

This is the nonlinear information injected by the second horizon. For an affine `R`, `(3)` is
only a constant and no missing jet is recovered.

## Lemma 2: one rational shadow plus one positive jet separates every branch

Let `r in C(z)` be any nonconstant rational function. Then, for every `n>=1`,

```text
C<r(x),x_n>=C<x>.                                          (4)
```

Write `K=C<r(x),x_n>`. Since `r(x) in K`, the element `x` is algebraic over `K`. Let `z` be a
`K`-conjugate of `x` in an algebraic differential closure. Derivations extend uniquely across
separable algebraic extensions, so the conjugacy commutes with `delta` and gives

```text
r(z)=r(x),
delta^n z=x_n.                                             (5)
```

The first equation makes `z` algebraic over `C(x)`. In the algebraic function field `C(x,z)`,
the coefficient of the free highest jet `x_n` in `delta^n z` is the algebraic derivative
`dz/dx`; all remaining terms use only `x_1,...,x_(n-1)`. Algebraic independence of the HT jets
and the second equation in `(5)` force

```text
dz/dx=1.                                                   (6)
```

Hence `z-x` is a constant of the algebraic function field. Algebraic closedness of `C` gives
`z=x+c` for some `c in C`. Now `(5)` says

```text
r(x+c)=r(x).                                               (7)
```

A nonconstant rational function in characteristic zero has no nonzero additive period: a
nonconstant polynomial cannot be periodic by its leading term, while a rational function with a
pole would acquire the infinite pole orbit `a+Zc`. Thus `c=0`, every conjugate equals `x`, and the
separable minimal polynomial of `x` over `K` has degree one. This proves `(4)`.

## Proof of the classification

If `R` is non-affine, `R'` is nonconstant. Lemma 1 puts `R'(x)` in `L_n(R)`, and Lemma 2 with
`r=R'` puts `x` in `L_n(R)`. Differential closure then gives `F<=L_n(R)`; the reverse inclusion
is immediate.

If `R(z)=az+b`, positive derivatives satisfy

```text
delta^k R(x)=a x_k,   k>=1.
```

Hence `L_n(R)=C<x_n>`. The strict HT jet flag proves this is proper in `F`. This proves `(7)`.

## Projective all-depth corollary

For `p in P^1(C)`, choose `M_p in PGL_2(C)` carrying `p` to infinity and put

```text
H_(p,n)=C((M_p x)^(n),(M_p x)^(n+1),...).                 (8)
```

The field is choice-independent by constant-affine jet-tail invariance. If `p!=q`, the transition
`M_q M_p^(-1)` has a genuine denominator and is therefore non-affine. Applying `(7)` gives

```text
H_(p,n) H_(q,n)=F                                         (9)
```

for every `n>=1`. Each individual horizon omits `n` independent jets; any two distinct projective
ends reconstruct all of them at every finite depth.

## Novelty and significance attack

- Differential Luroth, differential-order additivity, unique extension of derivations across
  separable algebraic fields, and ordinary no-periodicity of rational functions are classical.
- Exact-statement searches found nonlinear-system observability theory and differential-Luroth
  algorithms, but no theorem reconstructing the normalization of a rational observation curve
  from arbitrary common-order derivative horizons, or identifying affine-line images as the exact
  failures uniformly in `n`.
- The theorem is not a rank condition, a local inverse-function statement, or a renamed Schwarzian
  invariant. It is a global equality of differential function fields at arbitrary derivative
  depth, with the residual finite cover identified exactly by ordinary Luroth normalization.
- The principal-symbol step alone is insufficient: `(3)` generally makes `x` only algebraic.
  Lemma 2 is the branch-separation mechanism that upgrades algebraic observability to exact
  rational reconstruction.
- The theorem would fail for a merely differentially algebraic source because highest jets need
  not be free. Hypertranscendence is the load-bearing hypothesis, not decoration.

## Physical interpretation

`[CONJECTURAL INTERPRETATION]` Affine curvature of the joint observation image is the exact static
information threshold. A nonlinear observation curve is reconstructed together with its complete
differential function field at every depth, while an affine-line image remains one proper horizon.
The invisible information is not vague: it is precisely any finite algebraic cover above the
normalized observation curve. This is an exact algebraic analogue of depth-independent holographic
normalization, not a quantum or black-hole assertion.

## RH impact audit

`[FORMULATION CONSTRAINT; NOT RH PROGRESS]` An RH construction based on an HT source cannot claim
that deep derivative erasure is intrinsic when its rational observations trace a nonlinear curve:
their horizons reconstruct that curve's full differential function field. Any residual ambiguity
must be a genuine common algebraic cover. No canonical nonlinear source-pure zeta observation curve
is known, and the theorem does not constrain zeros or imply a critical-line statement.

## Lean realization and exact boundary

`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonComplementarity.lean` formalizes:

```text
projectiveInversion_twoJet_reconstruction
hypertranscendentalOver_sup_firstJetTail_inv_eq_top
mem_of_pow_mem_and_nonzero_differentialJet_mem
mem_of_sq_mem_and_nonzero_differentialJet_mem
```

The first two declarations certify the full depth-one inversion case. The latter two certify the
power branch-collapse mechanism at arbitrary depth: in any derivation-closed intermediate field,
visibility of any positive power `x^k` and one nonzero jet forces visibility of `x`.

The isolated source check and targeted module build pass. Formal lint passes. Axiom reports contain
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no full build was run.

The uniform principal-symbol/Luroth theorem `(2)--(3)` and general algebraic branch argument remain
paper-level because the toolchain has no differential-order or differential-Luroth interface and
no packaged algebraic function-field derivation theorem. No axiom or opaque placeholder is added.

## Gates

- [x] 0 -> 1 in-progress: exact classification, source-pure proof, parent collision, and formal
  boundary identified
- [x] 1 -> 2 fully-proven: highest-jet coefficient and algebraic-branch arguments audited
- [ ] 2 -> 3 formalized: depth-one inversion and quadratic branch collapse formalized; general
  Luroth principal symbol and rational branch separation remain
- [ ] 3 -> 4 publication-ready: independent specialist priority audit and standalone exposition

## Log

- 2026-07-15 — inversion all-depth complementarity discovered from the first-horizon projective
  building, then strengthened to the exact affine/non-affine rational classification.

## Primary references checked

- L. D'Alfonso, G. Jeronimo, P. Solerno, *Effective Differential Luroth's Theorem*, Journal of
  Algebra 406 (2014), for differential Luroth and exact-order generator control.
- Classical Hermann--Krener and modern algebraic observability literature, for the adjacent but
  flow-based local/global observability setting; no matching free-HT field classification found.
