# Theta-cusp half-density Ward--Laplace budget transfer

- **ID:** `theta-cusp-half-density-ward-laplace-budget-transfer`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / `[VALUE RELATION] [REFLECTION] [TOP-DOWN HYPOTHESIS DISCHARGE]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `../../1-in-progress/theta-cusp-dominant-first-atom-ratio-certificate.md`;
  `theta-cusp-likelihood-ordered-tail-single-loss-transfer.md`
- **Lean inputs:** `PrimeArchThetaLiouvilleWard.lean`;
  `PrimeArchThetaGibbsEquipartition.lean`; `PrimeArchThetaAtomLikelihoodRatio.lean`;
  `ThetaCuspReflection.lean`; `ThetaCuspFourierLaplace.lean`;
  `XiEndpointCompletedValue.lean`
- **Statement:** The Liouville--Gibbs Ward equation has an exact two-step Laplace shift and two
  closed half-density values.  Reflection converts these values into an exact exponential
  generating budget for every theta source atom.  For the first/higher decomposition this budget,
  combined with the formal likelihood-ratio order, replaces the uniform tail factor
  `3005/2997` in both open low-degree transfers by explicit finite expressions involving only the
  first-atom moments and one closed elementary constant.

## 1. Ward--Laplace shift and half-density anchors

For `n>=1`, put

```text
b_n(x)=thetaCuspLiouvilleGibbsAtom n x,
f_n(x)=thetaCuspSourceTerm x n,
B_n(z)=integral_(0,infinity) exp(z*x)*b_n(x) dx,
A_n(z)=integral_(0,infinity) exp(z*x)*f_n(x) dx.
```

The formal score and Ward identities are

```text
b_n'(x)=(5/2-2*pi*n^2*exp(2*x))*b_n(x),
f_n(x)=-2*pi*(b_n'(x)+(1/2)*b_n(x)).                    (1)
```

The Gaussian tail makes every real exponential tilt integrable.  Integrating `(1)` by parts gives,
for every real `z`,

```text
2*pi*n^2*B_n(z+2)=b_n(0)+(z+5/2)*B_n(z),               (2)
A_n(z)=2*pi*(b_n(0)+(z-1/2)*B_n(z)).                   (3)
```

Since `b_n(0)=n^2*exp(-pi*n^2)`, equation `(2)` at `z=-5/2` and equation `(3)` at the two reflected
half-density points give

```text
B_n(-1/2)=exp(-pi*n^2)/(2*pi),                          (4)
A_n( 1/2)=2*pi*n^2*exp(-pi*n^2),                       (5)
A_n(-1/2)=(2*pi*n^2-1)*exp(-pi*n^2).                   (6)
```

These are values of the actual source atom, not estimates and not consequences of any zero
location statement.

## 2. Exact atom budgets

Let

```text
a_(j,n)=2*integral_(0,infinity) x^(2*j)*f_n(x) dx.
```

All terms are nonnegative.  Expanding the sum of the reflected values `(5)`--`(6)` therefore gives
the exact monotone identity

```text
sum_(j>=0) a_(j,n)/(4^j*(2*j)!)
  =(4*pi*n^2-1)*exp(-pi*n^2).                           (7)
```

For the first atom write `a_j=a_(j,1)` and set

```text
K_1=(4*pi-1)*exp(-pi).                                  (8)
```

Then

```text
sum_(j>=0) a_j/(4^j*(2*j)!)=K_1.                       (9)
```

For the completed source let `m_j` be the formal raw even moment.  The strip identity

```text
thetaCuspFourierLaplace(w)=XiC(w)
```

at `w=I/2`, the formal endpoint value `XiC(I/2)=1/2`, and evenness of the full source give

```text
sum_(j>=0) m_j/(4^j*(2*j)!)=1/2.                       (10)
```

Consequently, if `m_j=a_j+r_j` is the first/higher atom split, the complete higher-atom budget is
the closed constant

```text
H=sum_(j>=0) r_j/(4^j*(2*j)!)
  =1/2-(4*pi-1)*exp(-pi).                               (11)
```

In particular, `(7)` summed over `n>=1` recovers the theta-reflection value relation

```text
sum_(n>=1) (4*pi*n^2-1)*exp(-pi*n^2)=1/2.              (12)
```

## 3. Likelihood order converts the global budget to local tail bounds

Put

```text
w_j=a_j/(4^j*(2*j)!),
t_j=r_j/a_j,
W_k=sum_(j=0)^k w_j.
```

The formal cross-moment theorem

```text
r_(k+ell)*a_k <= a_(k+ell)*r_k                         (13)
```

and positivity of every `a_k` say exactly that `t_j` is nonincreasing.  Equation `(11)` becomes

```text
H=sum_(j>=0) w_j*t_j.                                  (14)
```

For `j<=k`, monotonicity gives `t_j>=t_k`; hence

```text
H>=W_k*t_k,
t_k<=H/W_k.                                             (15)
```

This is an all-order source-specific tail estimate.  Unlike the uniform pointwise domination
constant, its denominator grows with the moment order and its limiting budget is the exact
reflected half-density mass.

The two cases needed by the open low block are

```text
r_0<=H,
t_1<=H/(a_0+a_1/8).                                    (16)
```

The first statement is the `j=0` term of `(14)`; the second uses
`W_1=a_0+a_1/8`.

## 4. Exact-budget transfers with no uniform tail factor

Let

```text
W=a_0+a_1/8.
```

The likelihood cross-moment relation also gives

```text
m_2*a_1<=a_2*m_1.                                      (17)
```

### Lower susceptibility gate

Assume the finite first-atom inequality

```text
14*(W+H)*a_2^2 <= 9*W*a_1*a_3.                         (18)
```

By `(15)`,

```text
m_1<=a_1*(W+H)/W.
```

Combining this with `(17)` and `m_3>=a_3` gives

```text
14*m_2^2
 <=14*a_2^2*m_1^2/a_1^2
 <=9*a_3*m_1
 <=9*m_1*m_3.                                          (19)
```

Thus `(18)` implies the full-source lower susceptibility gate.  It replaces the previous
sufficient condition `14*(3005/2997)*a_2^2<=9*a_1*a_3` by a condition using the exact reflected
tail budget.

### Upper susceptibility gate

Assume instead

```text
16*(a_0+H)*a_2 <= 45*a_1^2.                            (20)
```

Equation `(16)` gives `m_0<=a_0+H`; equation `(17)` gives
`m_2<=a_2*m_1/a_1`.  Therefore

```text
16*m_0*m_2
 <=16*(a_0+H)*a_2*m_1/a_1
 <=45*a_1*m_1
 <=45*m_1^2.                                            (21)
```

Thus `(20)` implies the full-source upper susceptibility gate.  Again no coordinatewise tail
constant occurs.

### Intersection with the formal uniform bound

The formal pointwise atom domination independently gives

```text
q=8/2997,
r_j<=q*a_j.                                             (21a)
```

The budget and uniform bounds may be intersected without estimating either one.  Define

```text
D_0=min(q*a_0,H),
D_1=min(q,H/W).                                         (21b)
```

Then `(15)`, `(16)`, and `(21a)` give the sharper simultaneous bounds

```text
m_0<=a_0+D_0,
m_1<=a_1*(1+D_1).                                      (21c)
```

Repeating the two transfer proofs shows that the full-source gates follow from

```text
14*(1+D_1)*a_2^2 <= 9*a_1*a_3,                         (21d)
16*(a_0+D_0)*a_2 <= 45*a_1^2.                          (21e)
```

These are pointwise no stronger than the previous single-loss hypotheses: `D_1<=q` and
`D_0<=q*a_0` imply

```text
1+D_1<=3005/2997,
a_0+D_0<=(3005/2997)*a_0.                              (21f)
```

Thus the reflected value relation produces a genuine top-down weakening even before deciding
which branch of each minimum is active for the actual theta values.  No numerical comparison is
needed.

### Damped-atom successor activates the reflected branches

The successor card `theta-cusp-half-density-damped-tail-domination.md` retains the Gaussian factor
discarded by the uniform pointwise atom estimate.  It proves

```text
H<q*a_0<q*W.                                             (21g)
```

Consequently

```text
D_0=H,
D_1=H/W.                                                 (21h)
```

The optimal conditions `(21d)`--`(21e)` therefore reduce unconditionally to `(18)` and `(20)`,
and both are strictly weaker than their single-loss predecessors.  The comparison is analytic
and uses no evaluated theta value.

## 5. Finite Taylor constraints for the remaining value problem

Let `L_(k,n)=integral x^k*b_n(x) dx`.  Differentiating `(2)` at `z=0` and expanding the positive
exponential gives, for every `k>=0`,

```text
2*pi*n^2*sum_(r>=0) 2^r*L_(k+r,n)/r!
 = [k=0]*n^2*exp(-pi*n^2)+k*L_(k-1,n)+(5/2)*L_(k,n).   (22)
```

Every finite truncation of the sum on the left is an unconditional lower bound for the right-hand
side.  The other anchor `(4)` gives the alternating Taylor brackets

```text
sum_(r=0)^(2N+1) (-1/2)^r*L_(r,n)/r!
 <= exp(-pi*n^2)/(2*pi)
 <=sum_(r=0)^(2N)   (-1/2)^r*L_(r,n)/r!.               (23)
```

The remainder signs in `(23)` are the ordinary integral Taylor remainders of `exp(-x/2)` against
the positive density `b_n`.  Equations `(22)`--`(23)` show that the first nine Gibbs values in the
existing certificate are not independent enclosures: they lie in a nested family of exact
positive-shift and alternating-anchor constraints.

## Top-down consequence

The low-degree RH chain is now

```text
(18) and (20)
 -> the two completed theta moment-ratio gates
 -> every constant and linear prime--Gamma trace-Hankel test is nonnegative
 -> [degree-at-least-two source cone, or leading determinants from size three]
 -> RH.                                                  (24)
```

The open analytic problem is now a different, more source-specific finite value problem:

1. prove the two finite first-atom inequalities `(18)` and `(20)`;
2. use the Ward--Laplace constraints `(22)`--`(23)`, the exact first-atom budget `(9)`, and the
   existing moment/Stein relations to produce a symbolic certificate;
3. close the independent degree-at-least-two or leading-determinant tail.

This card does not claim `(18)`, `(20)`, the higher-degree tail, or RH.  Under the no-computation
restriction in force when the theorem was derived, no numerical comparison between the new exact
budgets and the older rational sufficient conditions was used.  The formal comparison `(21f)` is
purely order-theoretic; whether either minimum is strictly below its uniform branch for the actual
theta values remains open here.

## Literature placement

The shift `(2)` is the upper-incomplete-Gamma recurrence in Laplace coordinates, and the Taylor
brackets are classical complete-monotonicity consequences.  General log-concave moment comparison
does not supply `(18)` or `(20)`: it controls normalized moment shapes but does not encode the
source-specific reflected mass `(11)`.  The contribution here is the splice of the classical
shift with the formal Xi endpoint value and the formal all-atom likelihood order.

Relevant comparison sources are Eskenazis--Nayar--Tkocz, *Sharp comparison of moments and the
log-concave moment problem* (Adv. Math. 2018, arXiv:1801.07597), and Pinelis, *Exact lower and upper
bounds on the incomplete gamma function* (arXiv:2005.06384).  Neither states the theta-source
budget transfer `(15)`--`(21)`.

## Gates

- [x] exact Ward--Laplace shift proved on paper from formal source identities
- [x] two reflected half-density atom values proved on paper
- [x] exact first-atom and complete higher-tail exponential budgets proved on paper
- [x] all-order likelihood-budget tail estimate proved on paper
- [x] two uniform-factor-free low-degree transfers proved on paper
- [x] intersect with the formal uniform tail bound to obtain pointwise no-stronger hypotheses
- [x] reflected-budget branches activated by the damped-atom successor
- [x] formalize the Ward--Laplace values, completed/higher exact budgets, and first two positive
  budget truncations in Lean (`PrimeArchThetaWardLaplaceHalfDensity.lean`)
- [x] formalize the antisymmetric endpoint value and opposite-channel fidelity deficit in Lean
  (`HTGeometry.ObservationFidelity` and `PrimeArchThetaWardLaplaceHalfDensity.lean`)
- [ ] formalize the likelihood-budget transfers in Lean
- [ ] prove finite first-atom inequalities `(18)` and `(20)`
- [ ] prove the independent degree-at-least-two or leading-determinant tail

## Antisymmetric successor

The difference of the two half-density anchors, not only their sum, is useful.  It supplies the
exact odd-moment budget and exposes the two open gates as the first two Turan defects of one
half-line source.  The endpoint difference, its `sinh` integral, and the fidelity square deficit
are now formalized.  In particular Lean proves

```text
a_(0,n)^2 + exp(-pi n^2)^2
  <= ((4 pi n^2 - 1) exp(-pi n^2))^2,
exp(-pi n^2) < 2 pi L_(0,n),
```

where `L_(0,n)` is the existing zeroth Liouville--Gibbs moment.  The successor
`theta-cusp-antisymmetric-half-density-turan-curvature-transfer.md` proves the boundary-pole split,
the source floor `V''>=19`, the one-sign-change law for the regular slope curvature, and the positive
unimodal crossing-window representation.  Its remaining problem is the paired order-one/order-two
window inequality; the independent higher-degree Hankel tail remains unchanged.  The further
successor `theta-cusp-continuous-half-density-residual-tail-chart.md` promotes the two endpoint
anchors to exact even/odd residual budgets at every real cutoff.
