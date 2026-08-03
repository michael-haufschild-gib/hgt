# Route R graded-det2 reflection Cartier/hyperbolic classification

- **ID:** `route-r-graded-det2-reflection-cartier-hyperbolic-classification`
- **Stage:** 3 — formalised in Lean 4
- **Type:** EXACT SOURCE CLASSIFICATION / STOKES-CARTIER NO-GO / POSITIVE SURVIVOR
- **Status:** `[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parents:**
  - `route-r-graded-det2-scalar-descent-counterboundary.md`;
  - `../../5-failed/route-r-source-stokes-cartier-graded-det2-trivialization.md`.

## Frozen theorem

For the explicit source anomaly

```text
A_a(i,j,k)=exp(-a kappa(i,j,k)) > 0,
```

reflection negates the centered rate.  On the reflection double define

```text
T_a=diag(A_a,A_(-a)),
B((x,y),(u,v))=xv+yu,
d=(1,1).
```

The exact classification is:

1. `A_a A_(-a)=1` on every labelled prime/depth triangle;
2. `T_a` preserves `B` for every real rate;
3. `B(d,d)=2`, so the same-fibre diagonal is positive;
4. `T_a d` remains diagonal iff `a*kappa=0`;
5. on the same-prime depths `(2,0),(2,1),(2,2)`, diagonal descent holds iff `a=0`;
6. for an actual Xi divisor point `rho`, the reflected divisor anomaly product is one, while
   witness diagonal descent holds iff `Re(rho)=1/2`;
7. global positive diagonal descent is equivalent to triviality of the explicit graded-`det2`
   boundary on the actual leading Xi conormal, hence equivalent to RH.

## Dependency-closed proof

Write `kappa=kappa(i,j,k)`.  Since reflection sends `a` to `-a`,

```text
A_a A_(-a)
 =exp(-a kappa) exp(a kappa)
 =exp(0)
 =1.                                                        (1)
```

For `z=(x,y)` and `w=(u,v)`, equation `(1)` gives

```text
B(T_a z,T_a w)
 =(A_a x)(A_(-a) v)+(A_(-a) y)(A_a u)
 =(A_a A_(-a))(xv+yu)
 =B(z,w).                                                   (2)
```

Thus determinant-one reflection balance and hyperbolic Stokes conservation hold for every `a`.
They are not critical-line selectors.

The positive diagonal has `B(d,d)=2`.  Its transported coordinates are

```text
(exp(-a kappa), exp(a kappa)).
```

They agree iff their real exponential exponents agree, hence iff `a*kappa=0`.  On the explicit
three-depth witness, the previously proved identity

```text
kappa=-log(2)/8 != 0
```

reduces this condition to `a=0`.  At an actual Xi divisor point,
`a=2 Re(rho)-1`, so diagonal descent is exactly `Re(rho)=1/2`.

The nonselectivity is strict, not merely logical: at `a=1`, equation `(1)` and pairing preservation
still hold on the nonzero-curvature witness, while diagonal descent fails.  Finally, the existing
actual-Xi theorem identifies boundary vanishing with the same critical-line equation pointwise.
Quantifying over Xi divisor support identifies global diagonal descent with boundary triviality,
and the existing boundary theorem identifies that proposition with RH.

## Scientific delta and hostile novelty audit

The generic linear algebra of `diag(t,t⁻¹)` is classical and is not claimed as new.  New
source-specific content is the exact classification of the already constructed prime/depth
BV--Wold graded-`det2` class after its actual divisor-resolved Xi landing:

- source reflection produces an **indefinite metabolic Cartier trivialization** for every divisor
  location;
- the first coefficient-faithful positive reduction is the same-fibre diagonal;
- preservation of that diagonal is exactly the existing boundary-annihilation problem, not a
  consequence of determinant or Stokes data;
- a concrete nonzero-rate source witness separates the two notions unconditionally.

External determinant-anomaly, determinant-bundle, irregular Stokes, and arithmetic-cohomology
frameworks provide parent language but no theorem identifying this explicit source class or
producing its positive same-fibre descent.  This result therefore moves Route R's frontier while
avoiding a false RH claim.

## Exact surviving open core

Construct from literal prime/depth/divisor source data a positive same-fibre polarization not
chosen from the desired boundary vanishing, then prove its Stokes-flatness law.  Ordinary Cartier
principalness, determinant-one reflection balance, hyperbolic/Krein conservation, cyclic
exactness, and global Stokes summation are now excluded as sufficient producers.

## Lean realization

Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldGradedDet2StokesCartierTrivialization.lean`.
The module is imported by `formal/GaloisForLFunctions/RHTower.lean` and proves all seven frozen
claims, including the concrete nonzero-rate no-go and global RH-equivalence.

Verification:

- direct `lake env lean` passed;
- targeted `lake build GaloisForLFunctions.RHTower.PrimeDepthBVWoldGradedDet2StokesCartierTrivialization` passed;
- `scripts/formal_tools.py lint` passed;
- `#print axioms` on all frontier theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`;
- module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
