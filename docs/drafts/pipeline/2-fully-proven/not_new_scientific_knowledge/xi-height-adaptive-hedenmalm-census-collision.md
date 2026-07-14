# Height-adaptive Hedenmalm adjacent-census collision

- **ID:** `xi-height-adaptive-hedenmalm-census-collision`
- **Stage:** 2-fully-proven / Lean source wired, focused check deferred by the no-computation constraint
- **Type:** THEOREM / TOP-DOWN RH REDUCTION / VALUE RELATION
- **Scientific status:** `[PROVED ON PAPER] [FORMALIZATION WRITTEN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHeightAdaptiveHedenmalmCensusCollision.lean`

## Statement

Put

```text
E_Xi(z)=XiC(z)+i XiC'(z).
```

At every zero of `XiC` of order `m`, the exact Hedenmalm order-drop law gives

```text
ord_z(E_Xi)=m-1.
```

For a bounded right-half Xi box let `M(T)` be the total Xi order, let `P_E(T)` be the sum of the
orders of `E_Xi` at the corresponding centered Xi points, and let `D(T)` be the number of distinct
Xi zeros in the box.  Then

```text
M(T)=P_E(T)+D(T).
```

Let `C_Xi` be the unconditional Xi zero-count-envelope constant.  Suppose that for every integer
`n>=1` there is a `k` such that

```text
C_Xi (n+3) log(n+4) < 2^k
```

and the two finite divisor censuses satisfy

```text
M(n) = P_E(n)  mod 2^k.
```

Then `2^k` divides `D(n)`, while the zero-count envelope gives `0<=D(n)<2^k`.  Hence `D(n)=0` for
every positive integer height.  Integer-height exhaustion gives RH.

## Top-down gain

The existing Hedenmalm--Kummer chain asked for a common analytic degree-`d` root of both `XiC` and
`E_Xi`; its minimal degree-two form also required the first Xi multiplicity ladder.  The new chain
requires neither input.  It replaces both by one finite scalar congruence per integer height:

```text
height-adaptive Xi/E_Xi common-divisor census congruence
  -> no distinct right-half Xi zero in that box
  -> RH.
```

This is strictly weaker than constructing regional or global Kummer roots.  It also avoids the
analytic continuation seam of the sharp-prime adjacent-census version because both functions are
entire and source-defined from the completed theta transform.

## Open core

`[OPEN CORE]` Produce the height-adaptive congruence from a boundary value, resultant,
subresultant, or determinant relation for the entire pair `(XiC,E_Xi)`, without reading the Xi
divisor or assuming a zero-free region.  The exact finite object to seek is a dyadic common-divisor
degree reader on the bounded spectral rectangle.  A Kummer root is sufficient but unnecessarily
strong.

The paper theorem `xi-hedenmalm-local-algebra-rank-census.md` identifies the sharp finite object.
On the direct sum of the Xi local algebras in the box, multiplication by `E_Xi` has rank exactly
the number of distinct Xi zeros.  Hence the required census congruence is equivalently a dyadic
rank congruence for one canonical multiplication operator, or a congruence for the first nonzero
subresultant index of the finite Weierstrass pair `(XiC,E_Xi)`.  The same paper theorem reconstructs
this finite reader unconditionally from boundary logarithmic-derivative moments and identifies it
with the confluent-jet rank of the existing Xi Hedenmalm Bezoutian.  The only remaining input is an
extra source relation forcing the large-modulus rank congruence; construction of the reader is no
longer open.

## Literature boundary

The local identity `ord(F+iF')=ord(F)-1` at a zero of `F` is elementary analytic divisor calculus.
The bounded-box argument is the standard fact that a positive integer divisible by a larger
positive modulus must vanish.  The contribution is the project-specific reduction of the live
Hedenmalm route, not a new parent-theory theorem.

## Gates

- [x] exact local order drop available in the Lean corpus
- [x] affine Xi-to-XiC order transport written explicitly
- [x] bounded Hedenmalm common-divisor census identified with the predecessor census
- [x] height-adaptive congruence reduced to the existing adjacent-census RH capstone
- [x] new Lean module wired into the RHTower umbrella
- [x] finite local-algebra rank/subresultant target isolated on paper
- [x] finite reader reconstructed from source boundary values on paper
- [ ] focused Lean check when computation is permitted
- [ ] source-side dyadic common-divisor degree relation
