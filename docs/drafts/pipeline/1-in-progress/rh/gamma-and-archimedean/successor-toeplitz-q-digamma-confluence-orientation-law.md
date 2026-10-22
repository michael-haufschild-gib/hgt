# Successor Toeplitz countertrace q-digamma confluence and orientation law

- **ID:** `successor-toeplitz-q-digamma-confluence-orientation-law`
- **Stage:** 1 — in progress
- **Type:** SOURCE-SPECIFIC q-DIFFERENCE/GAMMA CONFLUENCE THEOREM
- **Scientific status:** `[PAPER PROOF] [NOVELTY PROVISIONAL] [SIGNIFICANCE AUDIT OPEN]`
- **RH used:** no
- **Computation used:** no
- **Lean:** forbidden until paper, novelty, and significance audits pass
- **Parents:**
  - `von-mangoldt-weighted-density-boundary-anomaly`;
  - `von-mangoldt-toeplitz-countertrace-analytic-radius-capacity-escape`;
  - `reflected-digamma-anomaly-reality-selector`;
  - `reflected-digamma-anomaly-orientation-universality-law`.

## Frontier statement

The universal Toeplitz opening recurrence can be solved exactly on one oriented successor edge.
Its coefficient symbol is a basic hypergeometric/q-logarithmic germ. After logarithmic boundary
blow-up, it is exactly a q-digamma germ. The cofinal limit is not merely Gamma-like: after one
universal logarithmic subtraction it is the classical digamma function, and reflection recovers
the corpus's strict critical-line selector.

Finite q-stages do **not** have the classical selector globally. They have periodic off-line
reality resonances. Those counterfeit selector zeros escape to infinite height as `q -> 1`.
Consequently the strict critical-line orientation is a genuine confluence boundary phenomenon,
not a property visible at one finite successor clock.

This theorem does not prove that a Xi zero makes the boundary value real. That is the remaining
zero-specific creator problem.

## 1. One-edge opening recurrence

Fix

```text
0 < x < y,       q=x/y in (0,1),       w != 0,
m(k)=w*(y^k-x^k).
```

Let `c_0=1` and require

```text
sum_(r=0)^N c_r m(2N-r+2)=0,             N>=1.          (1)
```

Normalize

```text
e_r=c_r/y^r,
S_N=sum_(r=0)^N e_r,
E_q(u)=sum_(r>=0)e_r u^r.                                (2)
```

The scalar `w` cancels from `(1)`. Directly at `N=1`,

```text
e_1=-(1-q^4)/(1-q^3),
S_1=-q^3*(1-q)/(1-q^3)
   =-q^3/(1+q+q^2).                                    (3)
```

For `N>=2`, the equations at `N` and `N-1` give

```text
S_N/S_(N-1)=q^2*(1-q^N)/(1-q^(N+2)).                    (4)
```

Indeed `(1)`, after division by `w*y^(2N+2)`, is

```text
S_N=q^(2N+2)*sum_(r=0)^N e_r q^(-r).                    (5)
```

Use the corresponding equation at `N-1`, together with
`e_N=S_N-S_(N-1)`, to obtain

```text
S_N*(1-q^(N+2))=q^2*S_(N-1)*(1-q^N),
```

which is `(4)`.

Telescoping `(3)`--`(4)` yields, for every `N>=1`,

```text
S_N
 =-q^(2N+1)*(1-q)*(1-q^2)
    /((1-q^(N+1))*(1-q^(N+2)))
 =-q^(2N+1)*(q;q)_N/(q^3;q)_N.                          (6)
```

Since `e_N=S_N-S_(N-1)` after setting `S_0=1`,

```text
E_q(u)=(1-u)*sum_(N>=0)S_N u^N.                         (7)
```

## 2. Exact basic-hypergeometric and q-logarithmic forms

For `|q^2 u|<1`, equation `(6)` gives

```text
E_q(u)
 =(1-u)*
   [1+q-q*{}_2 phi_1(q,q;q^3;q,q^2 u)].                (8)
```

Let

```text
ell_q(z)=sum_(k>=1) z^k/(1-q^k).                        (9)
```

The coefficient identity

```text
(q;q)_N/(q^3;q)_N
 =(1-q)*(1-q^2)
   /((1-q^(N+1))*(1-q^(N+2)))
```

and elementary partial fractions give the equivalent exact formula

```text
E_q(u)
 = (1-u)*(1-q^2)*(1-q*u)/(q^2*u^2) * ell_q(q^2*u)
   -(1+q)*(1-u)^2/u.                                  (10)
```

The removable values at `u=0` are understood through `(8)`.

## 3. Exact q-digamma boundary chart

For `0<q<1`, use the standard normalization

```text
psi_q(z)
 =-log(1-q)
   +log(q)*sum_(n>=0) q^(n+z)/(1-q^(n+z)).              (11)
```

If `Re(z)>0`, expansion of `1/(1-q^k)` and interchange of absolutely convergent sums prove

```text
ell_q(q^z)
 =[psi_q(z)+log(1-q)]/log(q).                           (12)
```

Put `u=q^(-z)`. In the critical strip `0<Re(z)<1`, equation `(12)` applies at `2-z`, so `(10)`
is an exact q-digamma presentation of the successor countertrace boundary.

Write `h=log(q)<0` and define

```text
B_q(z)
 =-E_q(q^(-z))/(2*h^2)-z*(z-1)*log(1-q).               (13)
```

Classical locally uniform convergence `psi_q -> psi` on compact subsets of the positive
half-plane, together with

```text
1-q^(-z)       = z*h+o(h),
1-q^2          =-2*h+o(h),
1-q^(1-z)      = (z-1)*h+o(h),
```

gives, locally uniformly on compact subsets of `0<Re(z)<1`,

```text
B_q(z) -> B(z):=z*(z-1)*psi(2-z)+z^2.                  (14)
```

No pole continuation is needed for this limit: both `2-z` and `1+z` remain in the positive
half-plane.

## 4. Reflection recovers the classical digamma anomaly

The digamma recurrence

```text
psi(v+1)=psi(v)+1/v
```

gives

```text
B(z)+B(1-z)
 =z*(z-1)*(psi(z)+psi(1-z)+2).                         (15)
```

Therefore

```text
[B(z)+B(1-z)]/[z*(z-1)]-2
 =psi(z)+psi(1-z).                                     (16)
```

The rational normalization is harmless throughout the open strip. Equation `(16)` identifies
the reflected confluence boundary with the exact anomaly already proved in the corpus.

For `z=sigma+i*t`, `0<sigma<1`, `t>0`, the corpus proves

```text
Im(psi(z)+psi(1-z)) > 0   iff sigma<1/2,
Im(psi(z)+psi(1-z)) = 0   iff sigma=1/2,
Im(psi(z)+psi(1-z)) < 0   iff sigma>1/2.                (17)
```

Thus the limiting boundary mode has a strict, height-independent horizontal orientation.

## 5. Finite-q counterfeit realities and their escape

Define the reflected q-anomaly

```text
A_q(z)=psi_q(z)+psi_q(1-z).                             (18)
```

Let `a=-log(q)>0`, `theta=a*t`, and

```text
v_(q,t)(sigma)=Im psi_q(sigma+i*t).
```

Taking imaginary parts in `(11)` gives the exact positive-kernel formula

```text
v_(q,t)(sigma)
 =a*sin(theta) *
  sum_(n>=0)
    q^(n+sigma)
    /(1-2*q^(n+sigma)*cos(theta)+q^(2*(n+sigma))).      (19)
```

For fixed `theta` with `sin(theta)>0`, every summand in `(19)` is strictly decreasing in
`sigma`: the function

```text
r |-> r/(1-2*r*cos(theta)+r^2)
```

has derivative

```text
(1-r^2)/(1-2*r*cos(theta)+r^2)^2 > 0
```

on `0<r<1`, while `q^(n+sigma)` strictly decreases with `sigma`. Hence, whenever

```text
2*k*pi < a*t < (2*k+1)*pi,
```

the reflected anomaly has the classical orientation `(17)`. On the following half-period the
orientation reverses. At every resonance

```text
t=k*pi/a,                                               (20)
```

all terms in `(11)` are real, so

```text
Im A_q(sigma+i*t)=0
```

for **every** `sigma` in the strip. A finite q-stage therefore cannot be a global critical-line
selector.

If `q_j -> 1`, then `a_j=-log(q_j)->0`. For every fixed `t>0`, eventually

```text
0<a_j*t<pi.
```

Thus on every fixed compact height window the false-real resonances `(20)` escape, finite-q
orientation eventually agrees with `(17)`, and the renormalized boundary converges to the strict
classical selector `(16)`.

## 6. Arithmetic source specialization and scope

For one actual von Mangoldt successor edge `n -> n+1`,

```text
x=log(n),       y=log(n+1),
q_n=log(n)/log(n+1) -> 1.                               (21)
```

Its isolated relative moment is exactly `w*(y^k-x^k)`, so Sections 1--5 apply literally.
The first false-real height is

```text
pi/(-log(q_n)),
```

which tends to infinity.

This does **not** imply that the full finite-aperture von Mangoldt counterweight factors into the
edge symbols `E_(q_n)`. The counterweight recurrence is nonlinear in the sum of edge moments.
Only an edge-indexed connector that retains the source coordinate before contraction may use the
individual q-digamma laws.

The q-digamma scale also does not equal the existing odd Gamma--Jacobi scale:

```text
1-q_n                  is asymptotic to 1/(n*log n),
1-tanh(log n)          is asymptotic to 2/n^2.
```

No identification with the coherent odd Gamma--Jacobi residual is claimed.

## 7. Exact RH-bearing open core

Equation `(17)` is a faithful line selector but not a zero-location theorem. To turn this
confluence law into an RH proof, one still needs an unconditional source theorem of the form

```text
Xi(rho)=0
  ->
the reflected cofinal countertrace boundary at rho is real.       (22)
```

The boundary in `(22)` must arise from a source-fixed, edge-retaining completion before Xi is
read. Defining it to be real, making its norm reflection-unitary, or selecting a counterterm from
`rho` would insert RH at the seam.

If `(22)` were proved and the boundary were identified with `(16)`, then `(17)` would immediately
give

```text
Re(rho)=1/2.
```

At present `(22)` is open. Hypertranscendence, q-difference type, and the real coefficient
symmetry alone do not imply it. Summing a full Schwarz/functional-equation quartet makes the
boundary real for every quartet and therefore destroys the orientation.

## 8. Novelty and anti-theatre audit

Already known and excluded from novelty:

- basic hypergeometric notation and q-Pochhammer cancellation;
- q-logarithm/q-digamma identity `(12)`;
- classical convergence `psi_q -> psi`;
- classical digamma recurrence;
- the corpus's strict classical reflected-anomaly orientation;
- routine q-difference hypertranscendence classifications.

Provisional new content is restricted to the exact composition

```text
successor opening countertrace
 -> {}_2 phi_1 symbol
 -> q-logarithmic boundary
 -> renormalized q-digamma confluence
 -> reflected classical digamma orientation,
```

together with the finite-q resonance/escape theorem and the literal arithmetic specialization
`(21)`.

Targeted searches found q-digamma inequalities on positive real arguments, standard q-Gamma
convergence, q-logarithm identities, and general q-difference hypertranscendence. No hit stated the
successor countertrace composition, reflected complex-argument orientation sectors, or escape of
the false-real resonance lattice in this source setting. This is an absence-of-hit result, not a
priority certificate.

The user-supplied `arXiv:1707.06610` is *Quark matter may not be strange*, a high-energy
phenomenology paper with no mathematical interface to this theorem or RH.

## 9. Hostile falsifiers

1. The normalization in `(2)` does not convert the opening law to `(5)`.
2. Formula `(6)` fails at `N=1`.
3. Formula `(10)` differs from `(8)` by a nonremovable term.
4. The sign or logarithmic subtraction in `(13)` is wrong.
5. The reflected limit in `(15)` retains an uncancelled rational term.
6. The finite-q anomaly has additional reality zeros inside the first sector.
7. The full source counterweight is treated as a product or sum of isolated-edge symbols.
8. Boundary reality at a Xi zero is inferred from real coefficients or quartet symmetry.
9. Literature contains the exact source-specific composition and orientation-escape theorem.

Falsifiers 1--6 are rejected by the paper algebra above. Falsifiers 7--8 are enforced as scope
restrictions. Falsifier 9 remains under external audit.

## 10. Formalization plan after audit

1. Formalize the scalar recurrence `(3)`--`(6)`.
2. Formalize the generating-series identity `(8)` algebraically.
3. Formalize the elementary finite-q imaginary-part formula `(19)` and first-sector orientation.
4. Reuse the existing classical reflected-digamma selector for the limit endpoint.
5. Keep q-Gamma convergence on paper unless the exact analytic API is already present.
6. Do not formalize an RH wrapper until the source implication `(22)` is actually proved.

