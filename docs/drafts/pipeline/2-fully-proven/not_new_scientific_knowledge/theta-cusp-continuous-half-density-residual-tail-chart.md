# Theta-cusp continuous half-density residual-tail chart

- **ID:** `theta-cusp-continuous-half-density-residual-tail-chart`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / `[VALUE RELATION] [REFLECTION] [SOURCE TAIL CHART]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `theta-cusp-half-density-ward-laplace-budget-transfer.md`;
  `theta-cusp-antisymmetric-half-density-turan-curvature-transfer.md`
- **Lean input:** `PrimeArchThetaAtomLikelihoodRatio.lean`, especially
  `thetaCuspSourceTerm_shift_one`
- **Statement:** Both critical half-density survival transforms of the first theta source atom are
  elementary at every real cutoff.  Consequently every residual tail has exact even and odd
  exponential moment budgets, the ordinary survival function lies in an explicit relative-width
  corridor, and the crossing windows in the live Turan route can be written using only total
  moments and residual moments governed by this continuous value chart.

## 1. First source atom

Let

```text
f(x)=thetaCuspSourceTerm x 1
    =2*pi*(2*pi*exp(2*x)-3)*exp(5*x/2)*exp(-pi*exp(2*x))
```

for `x>=0`, and put

```text
q(a)=pi*exp(2*a).
```

For every real cutoff `a>=0`, define the two half-density survival transforms

```text
T_+(a)=integral_a^infinity exp(x/2)*f(x) dx,
T_-(a)=integral_a^infinity exp(-x/2)*f(x) dx.           (1)
```

Then

```text
T_+(a)=2*pi*exp(3*a)*exp(-q(a)),
T_-(a)=(2*q(a)-1)*exp(-q(a)).                          (2)
```

### Proof

Set the right sides of `(2)` equal to `F_+(a),F_-(a)`.  Direct differentiation gives

```text
F_+'(a)=-exp(a/2)*f(a),
F_-'(a)=-exp(-a/2)*f(a).                               (3)
```

Both functions tend to zero at upper infinity, so the fundamental theorem of calculus proves
`(2)`.  At `a=0`, these are exactly the two Ward--Laplace half-density anchors.  At
`a=log n`, the formal translation theorem gives the same identities by viewing the `n`th atom as
a shifted half-density copy of the first.

Thus the natural-index anchors are samples of a continuous residual-tail constraint, not isolated
special values.

## 2. Exact residual parity budgets

Put

```text
R_k(a)=integral_a^infinity (x-a)^k*f(x) dx.             (4)
```

Multiplying `(1)` by the compensating cutoff half-density and taking the sum and difference gives

```text
2*integral_a^infinity cosh((x-a)/2)*f(x) dx
  =exp(a/2)*(4*q(a)-1)*exp(-q(a)),                     (5)

2*integral_a^infinity sinh((x-a)/2)*f(x) dx
  =exp(a/2)*exp(-q(a)).                                (6)
```

All Taylor terms are nonnegative.  Monotone convergence therefore yields, for every `a>=0`,

```text
2*sum_(j>=0) R_(2*j)(a)/(4^j*(2*j)!)
  =exp(a/2)*(4*q(a)-1)*exp(-q(a)),                     (7)

sum_(j>=0) R_(2*j+1)(a)/(4^j*(2*j+1)!)
  =exp(a/2)*exp(-q(a)).                                (8)
```

Equivalently, if `nu_a` is the residual probability measure on `[a,infinity)` with unnormalized
density `cosh((x-a)/2)*f(x)`, then

```text
E_(nu_a)[tanh((X-a)/2)]=1/(4*q(a)-1).                  (9)
```

This is an orientation value at every source cut.  It uses neither a Xi zero nor an asymptotic
selection.

## 3. Ordinary survival corridor

Let

```text
S(a)=integral_a^infinity f(x) dx.
```

For `x>=a`,

```text
exp(-x/2)<=exp(-a/2),
exp(x/2)>=exp(a/2).
```

Applying these inequalities in `(1)` and then using `(2)` gives the exact corridor

```text
exp(a/2)*(2*q(a)-1)*exp(-q(a))
  <= S(a)
  <= 2*q(a)*exp(a/2)*exp(-q(a)).                       (10)
```

The upper-minus-lower width is exactly

```text
exp(a/2)*exp(-q(a)),                                   (11)
```

and its ratio to the lower endpoint is

```text
1/(2*q(a)-1).                                          (12)
```

Hence the corridor becomes relatively sharper along the source tail without invoking any
numerical estimate.

For every integer `n>=1`, `(10)` specializes at `a=log n` to

```text
sqrt(n)*(2*pi*n^2-1)*exp(-pi*n^2)
  <= S(log n)
  <= 2*pi*n^(5/2)*exp(-pi*n^2),                        (13)
```

with exact gap `sqrt(n)*exp(-pi*n^2)`.

## 4. Moment consequences

For `k>=1`, the layer-cake identity and `(10)` give

```text
k*integral_0^infinity
    a^(k-1)*exp(a/2)*(2*q(a)-1)*exp(-q(a)) da
  <= M_k
  <= k*integral_0^infinity
    a^(k-1)*2*q(a)*exp(a/2)*exp(-q(a)) da,              (14)
```

where `M_k=integral_0^infinity x^k*f(x) dx`.  The total width of this enclosure is the single
positive Gibbs-type moment

```text
k*integral_0^infinity a^(k-1)*exp(a/2)*exp(-q(a)) da.  (15)
```

More locally, positivity of the series in `(7)`--`(8)` gives the all-order residual estimates

```text
R_(2*j)(a)
  <=4^j*(2*j)!/2*exp(a/2)*(4*q(a)-1)*exp(-q(a)),       (16)

R_(2*j+1)(a)
  <=4^j*(2*j+1)!*exp(a/2)*exp(-q(a)).                  (17)
```

These estimates preserve the cutoff and parity information lost by a global moment enclosure.

## 5. Crossing-window specialization

Let

```text
U_k(a)=integral_a^infinity x^k*f(x) dx.
```

The binomial identity gives

```text
U_k(a)=sum_(r=0)^k binom(k,r)*a^(k-r)*R_r(a).          (18)
```

For the positive crossing window of order `m`, with `p=2*m`, the parent definition

```text
K_m(a)=L_p(a)*U_(p+2)(a)-L_(p+2)(a)*U_p(a)
```

and `L_k=M_k-U_k` collapse exactly to

```text
K_m(a)=M_p*U_(p+2)(a)-M_(p+2)*U_p(a).                 (19)
```

Thus no lower incomplete moment is needed.  At the unique regular-curvature seam `c`, equations
`(7)`--`(8)`, `(16)`--`(19)` give an explicit value-relation interface for both `K_1(c)` and
`K_2(c)`.

## 6. Seam localization before the first arithmetic shift

Let `c` be the unique zero of

```text
E_reg(x)=d/dx ((V'(x)-V'(0))/x)
```

from the parent one-seam theorem.  Then

```text
0<c<log 2.                                              (20)
```

### Proof

The parent proof gives `c>0`.  Put

```text
N(x)=x*V''(x)-(V'(x)-V'(0));
```

then `E_reg=N/x^2`, and `N` changes sign only at `c`.  At `x=log 2`, the source coordinate is
`q=4*pi`.  From the exact formulas for `V',V''`,

```text
V''(log 2)>16*pi,
V'(log 2)-V'(0)<6*pi+2.                                (21)
```

The standard inequality `log 2>2/3` and `pi>3` imply

```text
N(log 2)>(2/3)*16*pi-(6*pi+2)
        =(14/3)*pi-2>0.                                (22)
```

Hence the unique zero occurs before `log 2`.

The consequence is structural: every arithmetic translate `log n` with `n>=2` lies on the
positive side of the regular-curvature seam.

## 7. Top-down consequence

The live low-degree chain can now be attacked through a continuous family of exact tail values:

```text
continuous half-density residual chart
  + one-seam crossing-window representation
  -> paired order-one/order-two window balances
  -> reflected first-atom gates
  -> degree-one prime--Gamma source Hankel cone
  -> [independent higher-degree or leading-determinant tail]
  -> RH.
```

`[OPEN CORE]` Use `(7)`--`(9)` at the seam and the exact window collapse `(19)` to prove the two
signed window balances in
`../../1-in-progress/theta-cusp-one-seam-turan-window-balance.md`.  The present theorem does not
claim those inequalities, the independent tail, or RH.

## Literature status

Residual-life transforms, exponential tilting, and moment layer-cake identities are classical.
The contribution here is a source-specific splice of those tools with the exact theta atom and its
critical half-density reflection.  Scientific novelty has not been established and is not needed
for its role in the RH chain.

