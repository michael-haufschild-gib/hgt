# Raw noncommutative holonomy growth does not force differential innovation

- **ID:** `noncommutative-holonomy-word-growth-differential-innovation`
- **Stage:** 5-failed
- **Type:** FALSIFIED / CROSS-OPERATOR TRANSDUCTION
- **Scientific status:** `[FALSIFIED] [POSITIVE SALVAGE FORMALIZED]`
- **Statement:** Exponential word growth, a free-product splitting, or Zariski-dense noncommutative
  monodromy does not by itself force unbounded differential-jet innovation of scalar horizontal
  sections.

## The proposed implication

Programme 2 suggested a lower-bound theorem of the form

```text
noncommutative holonomy growth
  => lower differential innovation.                              (1)
```

If "growth" in `(1)` means only growth of words in the abstract or represented monodromy group,
the implication is false. The failure is not a missing estimate: the two complexities live in
different objects.

## Exact obstruction

Brav and Thomas exhibit rank-four hypergeometric monodromy groups in `Sp(4,Z)` which are Zariski
dense and split as free or amalgamated products; seven of their fourteen cases contain a free
subgroup of finite index. In particular, the Dwork-quintic quotient has monodromy

```text
Z * (Z/5Z).                                                   (2)
```

These groups are monodromy groups of generalized hypergeometric ordinary differential equations.
Every scalar coordinate of a horizontal section therefore satisfies a fixed fourth-order linear
differential equation with rational-function coefficients. Its full derivative tower is generated
over the coefficient field by four initial jets. Thus `(2)` has exponential noncommutative word
growth while the scalar differential presentation remains uniformly finite.

Consequently no lower bound which diverges with raw word growth, freeness, thinness, or Zariski
density can hold for scalar differential innovation without an additional invariant linking the
monodromy action to the chosen scalar observable.

## Representation-theoretic lesson

Monodromy complexity can be stored entirely in the matrix action relating a finite basis of local
solutions. A complicated image in `GL_r` says that analytic continuation mixes those `r`
coordinates richly; it does not say that any coordinate escapes the rank-`r` differential module.
The scalar observable forgets the group word while retaining only a coordinate of a finite linear
system.

The missing datum is therefore not a larger growth exponent. It is a **source-sensitive quotient**
which tests whether the action creates a genuinely new boundary class after passage to the scalar
observable.

## Significant positive replacement

For additive primitives under an arbitrary, possibly noncommuting automorphism family, define the
simultaneous telescoping space of a finite packet `S` by

```text
Tel_S={c in C^S : exists k in K, for every i,
                    tau_i(k)-k=sum_(s in S) c_s b_(i,s)}.    (3)
```

Under characteristic zero and equality of the common fixed fields, the correct quantitative law is

```text
trdeg_K K(x_s:s in S)=dim_C(C^S/Tel_S).                     (4)
```

The proof uses the arbitrary-family Ostrowski theorem already formalized in the project. A basis of
`C^S/Tel_S` gives algebraically independent constant-linear combinations of the primitives; every
complementary combination is a base element plus a common constant. Equation `(4)` is the numerical
rank form of the exact algebraic-matroid representation theorem
`automorphismFamily_algebraicIndependent_iff_no_constant_simultaneous_telescoping`.

This is the viable target-5 transduction principle:

```text
simultaneous observable-sensitive cocycle defect
  = algebraic innovation rank.                              (5)
```

Noncommutativity is allowed, but raw noncommutativity is not the cause. The load-bearing invariant
is the quotient by simultaneous coboundaries.

## Falsifier and reuse rule

Any future holonomy-to-HT proposal must specify:

1. the scalar or finite packet of observables;
2. the induced increment cocycles in the chosen coefficient field;
3. the simultaneous coboundary space being quotiented out; and
4. a proof that the claimed holonomy invariant injects into that quotient.

If it uses only abstract word growth, group freeness, thinness, or Zariski closure, the
Brav--Thomas rank-four examples kill it immediately.

## Lean status

No new Lean theorem is needed for the qualitative replacement: the exact arbitrary-family
algebraic and differential Ostrowski criteria are already unconditional in
`formal/GaloisForLFunctions/HTGeometry/SourceLogarithmicBoundary.lean`. Equation `(4)` is a
finite-dimensional rank corollary of that formalized matroid equivalence; packaging the cardinal
identity would add an API theorem, not a new hypothesis or a new transduction mechanism.

## References

1. C. Brav and H. Thomas, *Thin monodromy in Sp(4)*, Compositio Mathematica 150 (2014),
   333--343, `https://arxiv.org/abs/1210.0523`, doi:10.1112/S0010437X13007550.
2. F. Beukers and G. Heckman, *Monodromy for the hypergeometric function nF(n-1)*,
   Inventiones Mathematicae 95 (1989), 325--354, doi:10.1007/BF01393900.
3. C. Hardouin and M. F. Singer, *Differential Galois theory of linear difference equations*,
   Mathematische Annalen 342 (2008), 333--377, `https://arxiv.org/abs/0801.1493`.

## Log

- 2026-07-17 -- Raw holonomy-growth target falsified by fixed-rank hypergeometric systems; exact
  simultaneous-cocycle quotient retained as the significant positive transduction law.
