# Böttcher all-order parameter--spatial jet law

- **ID:** `bottcher-all-order-parameter-spatial-jet-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); third layer formalized in Lean
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every logarithmic parameter jet of the normalized quadratic Böttcher coordinate
  has an explicit dyadic transform determined by spatial derivatives of all earlier parameter jets,
  with a closed binomial coefficient kernel.

## Values and normalization

In the reciprocal coordinate `t=1/z`, put

```text
F(c,t)=t phi_c(1/t),
L(c,t)=log F(c,t),
R_c(t)=t^2/(1+c t^2).
```

The normalized Böttcher constraint is

```text
L(c,R_c(t))=2L(c,t)-log(1+c t^2),                   (1)
```

with `L(0,t)=0`. For `r>=1`, define the logarithmic parameter values

```text
J_r(t)=partial_c^r L(0,t).                          (2)
```

Write `J_a^(b)` for the `b`-th spatial derivative.

## Main theorem `[PROVED HERE]`

For every integer `r>=1`,

```text
J_r(t^2)
 =2J_r(t)+(-1)^r(r-1)! t^(2r)
  -sum_(a=1)^(r-1) sum_(b=1)^(r-a)
     [r!/(a!b!)] (-1)^(r-a) binom(r-a-1,b-1)
     t^(2(r-a+b)) J_a^(b)(t^2).                    (3)
```

Thus the new parameter value `J_r` enters linearly, while every other term is an explicitly
weighted spatial derivative of a strictly earlier parameter value.

## Proof

Set

```text
delta_c(t)=R_c(t)-t^2=-c t^4/(1+c t^2).             (4)
```

Taylor expansion of `L` at `(0,t^2)` gives

```text
L(c,R_c(t))
 =sum_(a,b>=0) J_a^(b)(t^2)c^a delta_c(t)^b/(a!b!). (5)
```

All terms with `a=0` vanish because `L(0,x)` is identically zero. The coefficient of `c^r`
with `b=0` is `J_r(t^2)/r!`. For `k>=b>=1`, the displacement power has the exact coefficient

```text
[c^k] delta_c(t)^b
 =(-1)^k binom(k-1,b-1)t^(2(k+b)).                  (6)
```

Indeed,

```text
delta_c(t)^b
 =(-1)^b c^b t^(4b)(1+c t^2)^(-b),
```

and the negative-binomial expansion gives (6). In (5), set `k=r-a`; then necessarily
`1<=a<=r-1` and `1<=b<=r-a`. Finally,

```text
r![c^r](-log(1+c t^2))=(-1)^r(r-1)!t^(2r).         (7)
```

Equating the `r`-th parameter coefficients in (1), inserting (6)--(7), and isolating
`J_r(t^2)` proves (3).

## First three exact layers

Let `theta=t d/dt`, `A=J_1`, `B=J_2`, and `C=J_3`. Formula (3) gives

```text
A(t^2)=2A(t)-t^2,                                   (8)

B(t^2)=2B(t)+2t^3 A'(t)-t^4,                        (9)

C(t^2)=2C(t)+3t^2 theta B(t)
                  +3t^4 theta A(t)
                  +(3/2)t^4 theta^2 A(t)-2t^6.     (10)
```

Before eliminating the scaled derivatives, the third identity is

```text
C(t^2)=2C(t)+3t^4B'(t^2)-6t^6A'(t^2)
                  -3t^8A''(t^2)-2t^6.              (11)
```

Equations (10) and (11) agree by differentiating (8)--(9).

## Law developed from the relation

Equation (3) is a **parameter--spatial derivative staircase law**:

```text
parameter depth r
  -> spatial derivatives J_a^(b) with a+b<=r
  -> exact coupling weight
     [r!/(a!b!)] binom(r-a-1,b-1).                  (12)
```

The binomial factor counts the ways in which the `b` spatial insertions share the remaining
`r-a` parameter differentiations through the reciprocal displacement (4). The law supplies an
all-order triangular system, not a finite list of independently differentiated identities.

For transcendence, (12) names the positive field value required at every depth: a dyadic-pullback
stable field containing the mixed values

```text
{theta^b J_a : a+b<=r}.                              (13)
```

At depth two, this stability closes the algebraic independence of `A,B`. At higher depth, (13) is
the exact value family on which an all-order independence theorem can be built.

## Novelty audit

The checked literature contains the Böttcher functional equation, formal Böttcher coordinates,
Mahler interpretations, algebraic-dependence results for fixed coordinates, and parameter-family
methods. Focused searches for higher parameter derivatives, parameter jets, second and third
parameter derivatives, and mixed parameter--spatial jet recurrences found no statement of (3),
the kernel (6), or the staircase law (12).

The candidate-new label remains provisional pending specialist review of holomorphic-motion and
parameter-variation literature. The theorem is mathematically complete and does not depend on a
transcendence conjecture.

## Lean certificate

The first two layers are formalized in

```text
formal/GaloisForLFunctions/U0/VelocityJetSeries.lean
formal/GaloisForLFunctions/U0/SecondVelocityJet.lean
```

The new module

```text
formal/GaloisForLFunctions/U0/ThirdVelocityJet.lean
```

constructs the normalized third formal jet by binary coefficient descent and proves

```text
dyadicSubst_thirdJet
dyadicSubst_thirdJet_explicit
```

with the exact coefficients in (10). The targeted module build passes. The final theorem's axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`.

The positive additional formal value for the full theorem (3) is a generic bivariate-series
coefficient extractor for substitution by `-c t^4/(1+c t^2)`.

## Gates

- [x] exact all-order relation isolated
- [x] complete paper proof
- [x] nontrivial derivative-staircase law developed
- [x] first, second, and third layers formalized
- [x] targeted Lean build and axiom audit pass
- [x] focused literature collision search
- [ ] generic all-order substitution coefficient theorem in Lean
- [ ] independent specialist novelty audit

## References checked

- J. F. Ritt, *On the Iteration of Rational Functions*, Transactions of the AMS 21 (1920),
  348--356.
- L. Di Vizio, G. Fernandes, and M. Mishna, *Inhomogeneous Order 1 Iterative Functional Equations
  with Applications to Combinatorics*, arXiv:2309.07680.
- C. Favre and T. Gauthier, *Polynomial Dynamics and Local Analysis of Orbits*, Compositio
  Mathematica 159 (2023), 930--970.
- A. Medvedev and T. Scanlon, work on invariant varieties and algebraic dependencies for polynomial
  dynamics, as background for fixed-coordinate comparison.

## Log

- 2026-07-11 -- Derived and proved the all-order coefficient law, isolated the binomial coupling
  kernel, formalized the third mixed parameter--spatial layer, and completed a focused novelty
  search.
