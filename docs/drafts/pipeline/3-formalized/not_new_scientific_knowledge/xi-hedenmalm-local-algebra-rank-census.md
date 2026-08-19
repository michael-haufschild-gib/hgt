# Xi--Hedenmalm local-algebra rank census

- **ID:** `xi-hedenmalm-local-algebra-rank-census`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / TOP-DOWN VALUE RELATION
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean parents:** `XiHedenmalmDeBrangesSeam.lean`, `XiHedenmalmMomentDeterminacy.lean`,
  `XiHedenmalmKummerCollision.lean`, `XiHedenmalmJordanMatrix.lean`,
  `XiHeightAdaptiveHedenmalmCensusCollision.lean`
- **Statement:** multiplication by the canonical Hedenmalm function on the finite Xi local algebra
  has one-dimensional image on every distinct zero fibre, so its total rank is exactly the number
  of distinct Xi zeros in the window.

## Theorem

Let

```text
F = XiC,
E = F + i F'.
```

Let `Omega` be a bounded spectral window whose boundary contains no zero of `F`.  For every zero
`rho` of `F` in `Omega`, write `m_rho = ord_rho(F)` and form the local Artin algebra

```text
A_rho = O_rho / (F).
```

Put

```text
A_Omega = direct_sum_{F(rho)=0, rho in Omega} A_rho
```

and let `M_E` be multiplication by the germ of `E` on `A_Omega`.  If

```text
M(Omega) = sum_rho m_rho,
D(Omega) = number of distinct zeros rho in Omega,
P_E(Omega) = sum_rho ord_rho(E),
```

then

```text
dim_C A_Omega = M(Omega),
rank_C M_E = D(Omega),
nullity_C M_E = P_E(Omega) = M(Omega) - D(Omega).
```

Thus the distinct-zero census is the rank of one canonical finite operator constructed from the
entire pair `(XiC,E)`.

## Proof

Fix a zero `rho` of order `m>=1` and use the local coordinate `t=z-rho`.  There is a holomorphic
unit `u` with

```text
F(t)=t^m u(t).
```

Modulo `(F)`,

```text
E = F + i F'
  = i t^(m-1) (m u + t u').
```

The factor `m u+t u'` is a unit because its value at `t=0` is `m u(0) != 0`.  After identifying
`A_rho` with `C{t}/(t^m)`, multiplication by `E` is therefore multiplication by `t^(m-1)` followed
by an automorphism.  The map

```text
sum_{j=0}^{m-1} a_j t^j  |->  a_0 t^(m-1)
```

has rank one and kernel `(t)`, of dimension `m-1`.  Hence

```text
rank M_E|A_rho = 1,
nullity M_E|A_rho = m-1 = ord_rho(E).
```

Taking the direct sum over the finitely many zero fibres proves all three identities.

## Polynomial and subresultant form

Let `W_Omega` be the monic finite Weierstrass polynomial carrying the Xi divisor in `Omega`, and
let `R_E` be the residue class of `E` represented by a polynomial modulo `W_Omega`.  Then

```text
deg gcd(W_Omega,R_E) = P_E(Omega) = M(Omega)-D(Omega),
rank(mul R_E on C[X]/(W_Omega)) = D(Omega).
```

Equivalently, the first nonzero subresultant index of `(W_Omega,R_E)` is
`M(Omega)-D(Omega)`; its complement in `deg W_Omega=M(Omega)` is the distinct-zero census.  This is
classical finite local algebra: subresultants do not add an RH input; they provide a finite
coefficient reader for the exact common-divisor degree.

There is also an exact reflection form.  For the Schwarz reflection `E#(z)=conj(E(conj z))`, the
reality of `F` gives

```text
E# = F - i F',
E + E# = 2F,
E - E# = 2i F'.
```

Consequently

```text
gcd(F,E) = gcd(F,F') = gcd(E,E#)
```

on every finite Weierstrass window.  The multiplication rank above is therefore also the degree of
the square-free quotient `W_Omega/gcd(W_Omega,W_Omega')`.  The Hedenmalm value and the reflection
pair read the same finite distinct-divisor charge.

The source-level reflection algebra is formalized in Lean.  Centered functional-equation
reflection exchanges the pair,

```text
E(-z)=E#(z),
E#(-z)=E(z),
```

while its even and odd projections recover the two local-algebra generators exactly:

```text
E+E#=2F,
E-E#=2i F'.
```

The corresponding two-variable de Branges commutator is odd under simultaneous reflection.  This
closes the reflection-value API needed by a future finite Weierstrass/subresultant formalization;
the finite multiplication-rank theorem itself remains paper-only.

## Bezoutian form

The classical Bezout rank formula gives

```text
rank Bez(W_Omega,W_Omega')
  = deg W_Omega - deg gcd(W_Omega,W_Omega')
  = D(Omega).
```

This is not a merely nominal collision with the existing Hedenmalm kernel.  If locally
`F=W_Omega H` with `H` zero-free, then the derivative Bezoutians satisfy

```text
B_F(z,v)
 = H(z)H(v) B_W(z,v) + W_Omega(z)W_Omega(v) B_H(z,v).
```

After passage to the finite local algebra modulo `W_Omega` in both variables, the second term
vanishes and the unit factors `H(z)H(v)` do not change rank.  Therefore the finite confluent-jet
compression of the already formalized global kernel `xiHedenmalmBezoutian` has rank exactly
`D(Omega)`.  The theta/prime--Gamma source formulas for that kernel are formulas for the correct
finite census reader, not merely for a similarly named object.

## Boundary coefficient reconstruction

The construction of the finite reader from source boundary values is unconditional.  Let `Gamma`
be the positively oriented boundary of `Omega`, disjoint from the Xi divisor, and define

```text
p_j(Omega) = (1/(2 pi i)) integral_Gamma z^j F'(z)/F(z) dz.
```

The argument principle gives

```text
p_j(Omega) = sum_rho m_rho rho^j.
```

Newton identities reconstruct every coefficient of `W_Omega` from the finite power-moment list;
polynomial differentiation and subresultants then reconstruct `D(Omega)`.  No enumeration or
choice of a zero is required.  This discharges existence of the coefficient reader, but it does
not orient the reader: the resulting number is still the actual distinct-zero census.

## Consequence for the top-down RH chain

The hypothesis in `XiHeightAdaptiveHedenmalmCensusCollision.lean`

```text
M(n) = P_E(n) mod 2^k
```

is exactly

```text
rank M_E,n = 0 mod 2^k.
```

When `2^k` is larger than the unconditional Xi zero-count envelope, this congruence forces
`rank M_E,n=0`, hence the height-`n` box contains no distinct Xi zero.  Integer-height exhaustion
then gives RH.

The live target is therefore not a Kummer root and not a multiplicity ladder.  It is a source-side
coefficient theorem forcing one height-adapted subresultant/rank congruence for the canonical pair
`(XiC,E)`.

## Exact open interface

`[OPEN CORE]` Prove an additional source value/reflection relation, beyond the generic argument
principle, which forces

```text
rank M_E,n = 0 mod 2^k
```

for some `2^k` above the zero-count envelope at every positive integer height.  The contour moments,
Newton reconstruction, reflection identity `E#=2F-E`, and Bezout rank formula are unconditional;
none by itself forces this congruence.  A theorem merely evaluating the reader as the actual Xi
census is a consumer identity and does not close the interface.

## Literature boundary

The local Artin-algebra calculation and the equality between polynomial-gcd degree and
subresultant rank defect are classical.  Relevant algebraic background includes:

- Carlos D'Andrea, Hoon Hong, Teresa Krick and Agnes Szanto, *An Elementary Proof of Sylvester's
  Double Sums for Subresultants*, <https://arxiv.org/abs/math/0604418>.
- Akira Terui, *Recursive Polynomial Remainder Sequence and its Subresultants*,
  <https://arxiv.org/abs/0806.0495>.

The project-specific gain is the exact identification of the complementary subresultant rank with
the distinct Xi-zero census through the canonical Hedenmalm value `E=XiC+i XiC'`.

## Gates

- [x] exact local-algebra rank and nullity proved
- [x] direct-sum bounded-window census proved
- [x] equivalent polynomial-gcd/subresultant formulation proved
- [x] equivalent finite Bezoutian-rank formulation proved
- [x] boundary moment/Newton reconstruction of the coefficient reader proved on paper
- [x] connected to the wired height-adaptive Hedenmalm RH capstone
- [x] centered `E`/`E#` reflection exchange and even/odd source recovery formalized in Lean
- [ ] formalize the local multiplication-rank theorem in Lean
- [ ] construct the subresultant reader directly from source boundary data

## Lean formalization (complete and unconditional)

- `formal/GaloisForLFunctions/HTGeometry/PolynomialQuotientMultiplicationRank.lean` — the rank of
  multiplication in a polynomial quotient algebra.
- `formal/GaloisForLFunctions/HTGeometry/GcdDerivativeDistinctRoots.lean` — `deg gcd(F, F')` and
  the count of distinct roots.
- `formal/GaloisForLFunctions/HTGeometry/HermiteBiehlerPairRankCensus.lean` — the de Branges value
  `F + i F'`, its gcd with `F`, and the exact rank census of multiplication by it.
- `formal/GaloisForLFunctions/HTGeometry/FiniteMomentDivisorReconstruction.lean` — a finite divisor
  is determined by finitely many power sums.
- `formal/GaloisForLFunctions/RHTower/XiHedenmalmLocalAlgebraRankCensus.lean` — the Xi packet
  divisor, its Weierstrass polynomial, the moment reconstruction, and the census congruence.
