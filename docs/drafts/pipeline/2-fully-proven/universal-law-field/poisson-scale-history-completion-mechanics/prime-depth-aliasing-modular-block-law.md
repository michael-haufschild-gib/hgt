# Prime-depth aliasing modular block law

- **ID:** ULF-PDAMB-001
- **Stage:** 2-fully-proven
- **Type:** pre-divisor source/completion fusion law
- **Parents:** ULF-SFMH-001, ULF-PBFOF-001, TwoPrimeKummerClockSeparation
- **Status:** [FULLY PROVEN] [NOT RH]

## Statement

Let `L2=log 2`, `L3=log 3`. For every `epsilon>0` there are positive integers `m,n` such that

~~~text
0 < |m L2-n L3| < epsilon.                              (PDAMB.1)
~~~

Thus fixed distinct prime labels admit arbitrarily close positive prime-depth Burnol clocks.

Let `K` be a field, let

~~~text
C = [[d,g],[g,e]] tensor I,
U = diag(P,Q),
V = diag(Pi,Qi),
Delta = d e-g^2,
~~~

where `P Pi=I`, `Q Qi=I`, and `Delta!=0`. Then the retained source-site block of
`C^(-1) U C V` is

~~~text
(d e I-g^2 Q Pi)/Delta
 = I + (g^2/Delta)(I-Q Pi).                             (PDAMB.2)
~~~

When `V=U^(-1)`, this is the retained block of source-frame modular holonomy. Therefore its
singular coefficient is the normalized Gram capacity `g^2/(d e-g^2)`, multiplying frame mismatch
`I-QP^(-1)`. This is a multiplicative source/completion law, not a quadratic-form selector.

For zero-clock cubic-Cauchy Burnol columns of rates `x,y>0`, amplitude factors cancel and

~~~text
g^2/(d e-g^2)
 = 64 x^3 y^3 / ((x+y)^6-64x^3y^3),                   (PDAMB.3)

(x+y)^6-64x^3y^3
 = (x-y)^2 ((x+y)^4+4xy(x+y)^2+16x^2y^2).            (PDAMB.4)
~~~

Hence the capacity diverges when positive rates coalesce. For the pairs in (PDAMB.1), the theta
blocks remain the fixed distinct blocks `U_2(a),U_3(a)` for every `a!=0`; their mismatch does not
coalesce with prime-power scale.

## Proof

TwoPrimeKummerClockSeparation proves arbitrarily small nonzero values of
`r log 2+s log 3` for nonzero `(r,s) in Z^2`. Choose the value below both `epsilon` and `log 2`.
Coordinates cannot have the same sign: otherwise positivity of both logarithms and nonvanishing
of the pair give absolute value at least `log 2`. Both coordinates are therefore nonzero and have
opposite signs. Taking their positive absolute values gives (PDAMB.1).

The inverse of the scalar source block is

~~~text
C^(-1)=Delta^(-1)[[e,-g],[-g,d]] tensor I.
~~~

Block multiplication gives the upper-left block of `C^(-1) U C V` as
`Delta^(-1)(de P Pi-g^2 Q Pi)`. Using `P Pi=I` proves the first equality in (PDAMB.2); adding and
subtracting `Delta I` proves the second. Substitution of diagonal and off-diagonal cubic-Cauchy
Gram entries proves (PDAMB.3). Equation (PDAMB.4) is the difference-of-cubes factorization with
`A=(x+y)^2`, `B=4xy`, since `A-B=(x-y)^2`.

## Meaning

Multiplicative source formation identifies prime powers by archimedean decay scale; theta
completion identifies them by prime label. Near-collision of the first without collision of the
second forces finite inner modular transports toward infinity. Finite determinant remains one,
so the only possible invariant is a relative cofinal boundary.

## Non-claim

This does not prove that Xi completion requires bounded/regular modular transport and does not
identify the cofinal cubic boundary with zero multiplicity. Those are the remaining RH interfaces.
