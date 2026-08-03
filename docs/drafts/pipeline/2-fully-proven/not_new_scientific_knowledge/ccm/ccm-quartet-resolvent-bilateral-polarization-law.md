# An off-line Xi quartet is a hyperbolic-odd causal/anti-causal resolvent channel

- **ID:** `ccm-quartet-resolvent-bilateral-polarization-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `ccm-infinitesimal-real-euler-ray-logderivative-index-law.md`,
  `ccm-logderivative-closed-two-channel-graph-law.md`, and
  `ccm-hankel-boundary-relative-trace-four-unit-law.md`

## Statement

Let

```text
lambda=a+i gamma,       0<a<1/2,       gamma>0,           (1)
```

be a right-half zero of the centered Xi function, and take real Euler-ray nodes `x>1/2`.  Define
the causal and anti-causal resolvent coordinates

```text
f_lambda(x)=1/(x-lambda),
g_lambda(x)=1/(x+conjugate(lambda)).                      (2)
```

Put

```text
u_lambda=(f_lambda+g_lambda)/sqrt(2),
v_lambda=(f_lambda-g_lambda)/sqrt(2).                     (3)
```

The Hermitian kernel associated with `lambda` and its functional-equation reflection
`-conjugate(lambda)` is

```text
H_lambda(x,y)
 =f_lambda(x)conjugate(g_lambda(y))
  +g_lambda(x)conjugate(f_lambda(y))
 =u_lambda(x)conjugate(u_lambda(y))
  -v_lambda(x)conjugate(v_lambda(y)).                     (4)
```

Adding `(4)` for `lambda` and `conjugate(lambda)` gives exactly the full conjugate-quartet
contribution to the infinitesimal Euler-ray kernel

```text
J(x,y)=[Q(x)+Q(y)]/(x+y).                                 (5)
```

Thus every right-half zero contributes one positive symmetric resolvent coordinate and one
negative antisymmetric resolvent coordinate.  The negative coordinate is the hyperbolic-odd
causal/anti-causal channel

```text
v_lambda(x)
 =sqrt(2) integral_0^infinity
    exp(-xt)exp(i gamma t)sinh(a t)dt.                    (6)
```

Its anti-causal half is

```text
g_lambda(x)
 =integral_0^infinity
    exp(-xt)exp(-a t)exp(i gamma t)dt.                    (7)
```

Consequently the negative index of `J` and the four-unit boundary trace slope are the quantized
and metric readings of the same bilateral graph coordinate.

## Resolvent factorization

For the paired zero parameter `lambda`, the logarithmic-derivative contribution is

```text
q_lambda(z)=1/(z-lambda)+1/(z+lambda).                    (8)
```

Its contribution to `(5)` is

```text
[q_lambda(x)+q_lambda(y)]/(x+y)
 =1/((x-lambda)(y+lambda))
  +1/((x+lambda)(y-lambda)).                              (9)
```

The conjugate parameter contributes the conjugate pair of fractions.  Grouping the first fraction
in `(9)` with the reflected fraction from the conjugate parameter gives

```text
1/((x-lambda)(y+lambda))
 +1/((x+conjugate(lambda))(y-conjugate(lambda)))
 =H_lambda(x,y).                                         (10)
```

The remaining two fractions give `H_(conjugate(lambda))`.  This proves the quartet decomposition.
Finally, substituting `(3)` gives `(4)` by direct expansion.

## Paley--Wiener graph form

Since `x>a`, both resolvents have convergent Laplace representations:

```text
f_lambda(x)
 =integral_0^infinity exp(-xt)exp(a t)exp(i gamma t)dt,

g_lambda(x)
 =integral_0^infinity exp(-xt)exp(-a t)exp(i gamma t)dt.  (11)
```

Their symmetric and antisymmetric combinations are therefore

```text
u_lambda(x)
 =sqrt(2) integral_0^infinity
    exp(-xt)exp(i gamma t)cosh(a t)dt,

v_lambda(x)
 =sqrt(2) integral_0^infinity
    exp(-xt)exp(i gamma t)sinh(a t)dt.                    (12)
```

These are precisely the two light-cone polarizations of the closed completed-source graph.  The
anti-causal coordinate `(7)` is the Paley--Wiener image of the upper-half-plane Cauchy residue;
the causal coordinate is its functional-equation-reflected companion.  Horizontal displacement
`a` is therefore carried by the odd hyperbolic mode `sinh(a t)`, not by the ordinate phase.

In the critical-line limit `a->0`, the odd mode vanishes and the two positive conjugate coordinates
merge into the usual critical-line packet.  Off the line, `v_lambda` is nonzero and rational
partial-fraction uniqueness makes the negative coordinates for distinct zeros independent.

## Exact index--slope dictionary

Repeat `(4)` according to the zero multiplicity `m_lambda`.  Then

```text
number of independent v_lambda coordinates
 =sum_(Re lambda>0)m_lambda
 =ind_-(J).                                               (13)
```

The closed logarithmic-source graph carries the anti-causal time mode with residue amplitude
`2m_lambda`:

```text
ell_lambda(t)=2m_lambda exp(-a t)exp(i gamma t).           (14)
```

Its squared norm is

```text
||ell_lambda||_2^2
 =4m_lambda^2 integral_0^infinity exp(-2a t)dt
 =2m_lambda^2/a.                                         (15)
```

Equation `(15)` is the diagonal term in the initial boundary relative-trace slope.  Since
`0<a<1/2`, it is strictly larger than `4m_lambda`; the full Cauchy Gram has positive cross terms.
Thus one and the same bilateral coordinate has

```text
quantized reading: one negative square per multiplicity unit;
metric reading:    strictly more than four trace units per unit. (16)
```

## Positive CCM carrier law

The two surviving RH endpoints are now linked at the level of individual source coordinates:

```text
diagonal Fock / Euler-ray test
  reads the antisymmetric mode v_lambda and its negative index;

boundary relative trace
  reads the anti-causal mode ell_lambda and its inverse-horizontal cost. (17)
```

A successful CCM construction is therefore forced to transport the complete bilateral pair, not
only its anti-causal residue or only its Euler-ray index.  The distinguished Sonin compression must
be a source-pointed colligation which

```text
preserves the causal/anti-causal reflection incidence,
does not increase the incoming four-unit boundary budget,
and preserves the rank of every hyperbolic-odd channel.   (18)
```

Under `(18)`, an off-line channel is impossible: its metric cost exceeds the source budget while
its integer rank cannot disappear in the cofinal limit.

This reformulates the open theorem positively.  It does not prove the nonexpansive source budget.

## Scope and classification

Equations `(4)` and `(9)`--`(12)` are partial-fraction algebra and the elementary Laplace transform
of a resolvent.  Equations `(13)`--`(16)` combine already proved Krein--Langer index and Hankel
trace-slope laws.  The result is an exact operator dictionary, but it is parent-theory bridge work,
not new scientific knowledge.

The Lean tree does not contain the analytic Xi logarithmic kernel, half-plane Hardy graph, or
Krein--Langer minimality needed for the unconditional specialization.  Formalizing only the
two-by-two algebra would be a wrapper, so no Lean file is added.

## Gates

- [x] quartet kernel split into one positive and one negative coordinate per right-half zero
- [x] negative coordinate identified as the hyperbolic-odd bilateral mode
- [x] anti-causal half identified with the boundary-trace residue mode
- [x] index and trace slope proved to read the same graph coordinate
- [x] diagonal Fock and four-unit endpoints linked source-by-source
- [ ] construct the distinguished Sonin bilateral colligation
- [ ] prove its nonexpansive four-unit budget and cofinal rank preservation
- [ ] RH
