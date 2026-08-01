# Suzuki completed eigenmodes are bounded by atomic-jump coercivity

- **ID:** `suzuki-completed-eigenmode-atomic-jump-boundedness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / COMPLETION-TO-FUNCTION REGULARITY
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki's completed operator
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, especially (2.2), (2.5), (2.8), and (2.11)
- **Regularity source:** B. Dyda, S. Jarohs, and F. Sk,
  *The Dirichlet Problem for the Logarithmic \(p\)-Laplacian*,
  arXiv:2411.11181v3, Theorem `bounded1`
- **Statement:** Every eigenfunction of Suzuki's self-adjoint restricted-Weil operator
  \(A_a\), including every completed square-Evans zero mode, has a bounded representative.
  The proof does not assume that the eigenfunction lies in \(H^1_0(-a,a)\).  Its essential
  source-specific input is that every von-Mangoldt translation pair is a positive atomic
  Dirichlet jump minus a scalar potential.

## 1. Exact theorem

Fix \(a>0\), put \(I_a=(-a,a)\), and extend functions on \(I_a\) by zero to
\(\mathbb R\).  Let \(A_a\) be Suzuki's Friedrichs operator associated with the
restricted Weil form \(Q_W^a\).

`[PROVED]` If

```text
u in Dom(A_a),       A_a u=lambda u,
```

then

```text
u in L-infinity(R).
```

More quantitatively, for every fixed \(a\) and \(\lambda\) there is a finite
\(C_{a,\lambda}\), depending only on the displayed source coefficients at aperture
\(a\), such that

```text
||u||_infinity <= C_(a,lambda) ||u||_2.                  (1)
```

The theorem applies to every spectral level and every multiplicity.  Since \(A_a\)
has real coefficients and is self-adjoint, a complex eigenfunction is handled by
applying the real theorem to its real and imaginary parts.

## 2. The completed form domain is the logarithmic Dirichlet space

Let \(X^2_0(I_a)\) be the zero-exterior logarithmic energy space

```text
u in L2(R),
u=0 off I_a,
integral_R integral_(|x-y|<1)
  |u(x)-u(y)|^2/|x-y| dy dx < infinity.                  (2)
```

Suzuki's Fourier formula has the form

```text
Q_W^a(u)
 =(1/(2pi)) integral_R
   [log|xi| + b_a(xi)] |uhat(xi)|^2 dxi,                 (3)
```

where \(b_a\) is bounded.  Indeed, its prime part is a finite sum

```text
-2 sum_(n<=exp(2a)) Lambda(n)/sqrt(n) cos(xi log n),
```

and the polar--Gamma remainder in Suzuki's (2.7) is bounded at fixed aperture.
For a zero-extended \(u\in L^2(I_a)\),

```text
|uhat(xi)| <= sqrt(2a)||u||_2,
```

so the negative low-frequency integral

```text
integral_(|xi|<1) |log|xi|| |uhat(xi)|^2 dxi
```

is bounded by a constant times \(a\|u\|_2^2\).  Consequently finiteness of
the closed form is equivalent to

```text
integral_R log^+|xi| |uhat(xi)|^2 dxi < infinity.        (4)
```

The standard Fourier characterization of the zero-exterior logarithmic energy
identifies `(4)` with `(2)`.  Hence

```text
Dom(Q_W^a)=X^2_0(I_a).                                   (5)
```

This step is load-bearing.  It puts completed eigenfunctions, not merely
\(H^1_0\) test functions, in the weak space on which logarithmic truncations are
legal.

## 3. Positive atomic decomposition of the prime operator

For \(h>0\), define the symmetric finite-jump form

```text
J_h(u,phi)
 =integral_R [u(x+h)-u(x)][phi(x+h)-phi(x)] dx.           (6)
```

Translation invariance of Lebesgue measure gives the exact identity

```text
J_h(u,phi)
 =2<u,phi>-<u(.+h),phi>-<u(.-h),phi>.                    (7)
```

Therefore Suzuki's literal prime pair satisfies

```text
-c_h[<u(.+h),phi>+<u(.-h),phi>]
 =c_h J_h(u,phi)-2c_h<u,phi>,                            (8)

c_h=Lambda(n)/sqrt(n)>=0,    h=log n.
```

Thus the prime term is not arbitrary translated forcing.  It is a positive
atomic Dirichlet form plus a bounded scalar potential.

Let \(T_t(s)=(s-t)^+\).  Since \(T_t\) is increasing and one-Lipschitz,

```text
(r-s)[T_t(r)-T_t(s)] >= |T_t(r)-T_t(s)|^2 >=0.           (9)
```

For \(v_t=T_t(u)\), integration of `(9)` gives

```text
J_h(u,v_t)>=J_h(v_t,v_t)>=0.                             (10)
```

This favorable sign is exactly what is lost if the prime translations are
incorrectly treated as an arbitrary bounded \(L^2\) operator.

## 4. Exact weak eigenfunction equation

Write

```text
S_a=sum_(2<=n<=exp(2a)) Lambda(n)/sqrt(n).
```

Let \(\mathcal E_L\) be the one-dimensional logarithmic-Laplacian form normalized
so that its Fourier symbol is \(2\log|\xi|\).  Suzuki's (2.5) and

```text
2A+1=log(2pi)+EulerGamma
```

give, first on \(C^\infty_c(I_a)\) and then on the completed form domain by
continuity,

```text
Q_W^a(u,phi)
 =(1/2) E_L(u,phi)
  +sum_(n<=exp(2a)) c_n J_(log n)(u,phi)
  -[log(2pi)+2S_a]<u,phi>
  -<K_a u,phi>,                                          (11)
```

where

```text
(K_a u)(x)=integral_(-a)^a r''(x-y)u(y)dy.               (12)
```

The remainder \(r\) in Suzuki's (2.2) is \(C^2\).  On the compact difference
interval \([-2a,2a]\), \(r''\) is bounded, and therefore

```text
||K_a u||_infinity
 <=sqrt(2a) ||r''||_(L-infinity(-2a,2a)) ||u||_2.         (13)
```

If \(A_a u=\lambda u\), `(11)` becomes

```text
(1/2) E_L(u,phi)+sum_n c_n J_(log n)(u,phi)
 =[lambda+log(2pi)+2S_a]<u,phi>+<K_a u,phi>              (14)
```

for every \(\phi\in X^2_0(I_a)\).

## 5. Atomic-jump logarithmic truncation lemma

`[PROVED]` Let \(\Omega\) be a bounded interval.  Suppose that a real
\(u\in X^2_0(\Omega)\) satisfies

```text
(1/2) E_L(u,phi)+sum_(j=1)^m c_j J_(h_j)(u,phi)
 =integral_Omega [b u+f]phi                              (15)
```

for every \(\phi\in X^2_0(\Omega)\), where \(c_j\ge0\), \(b\in\mathbb R\),
and \(f\in L^\infty(\Omega)\).  Then \(u\in L^\infty(\Omega)\), with

```text
||u||_infinity
 <=C_(Omega,|b|)
   [||f||_infinity+||u||_2+||u||_(L^1_0)].               (16)
```

Here \(L^1_0\) is the standard logarithmic tail space.  For a compactly
supported \(L^2\) function its norm is bounded by a constant times
\(\|u\|_2\).

### Proof

For \(t\ge0\), the truncation \(v_t=(u-t)^+\) belongs to
\(X^2_0(\Omega)\).  Test `(15)` with \(v_t\).  Equations `(9)`--`(10)` allow
all atomic terms to be discarded from the left, yielding

```text
E_L(u,v_t)
 <=2 integral_Omega [||f||_infinity+|b||u|]v_t.          (17)
```

Case \(p=2\) of the logarithmic \(p\)-Laplacian truncation proof
(Dyda--Jarohs--Sk, Theorem `bounded1`) now applies verbatim.  That proof uses
the assumed subsolution inequality only after inserting this same truncation:
it splits the positive unit-range kernel at a radius \(\delta\), chooses the
annular mass larger than the coefficient \(2|b|\), and absorbs the potential
term.  Its resulting threshold is exactly `(16)`.  Applying the same argument
to \(-u\) bounds \(u^-\).  Therefore \(u\in L^\infty\).  `QED`

Apply the lemma to `(14)` with

```text
b=lambda+log(2pi)+2S_a,
f=K_a u.
```

Equation `(13)` and compact support absorb both \(\|f\|_\infty\) and the tail
norm into \(C_{a,\lambda}\|u\|_2\), proving `(1)`.

## 6. Immediate weak-source and boundary consequences

Returning to the untranslated form of `(11)`, every eigenfunction satisfies
weakly

```text
L_Delta u
 =2[lambda+log(2pi)]u
  +2 sum_(n<=exp(2a)) c_n
      [u(.-log n)+u(.+log n)]
  +2K_a u.                                               (18)
```

After `(1)`, every term on the right of `(18)` is bounded.  Hence every
completed eigenfunction is a bounded weak solution of the ordinary
logarithmic Dirichlet problem with bounded source.  The optimal boundary
theorem of Hernandez-Santamaria--Lopez Rios--Saldana therefore gives

```text
u in C(R),
|u(x)| <= C [log(1/dist(x,{ -a,a }))]^(-1/2).             (19)
```

In particular, the previously live escape

```text
unbounded completed square-Evans zero mode
```

does not exist.

Equation `(19)` does not by itself prove pointwise classical regularity at the
dense translated seam orbit.  Atomic translations propagate the endpoint
half-log germ to interior germs, so generic compact-perturbation Schauder
theory cannot be invoked without checking its target space.  The exact
remaining pre-trace issue is therefore no longer boundedness:

```text
SUZUKI-WEAK-SIGNED-TRACE:
extend the exact half-log signed-trace theorem from pointwise Dini solutions
to bounded continuous weak solutions of (18), or prove the needed
source-specific Dini control in an endpoint collar.                       (20)
```

## 7. Hostile audit

### No \(H^1_0\) smuggling

Only `(5)` is used.  Truncations are taken in \(X^2_0(I_a)\), the completed
form domain.  No endpoint value, derivative, or pointwise distributional
formula is assumed before boundedness is proved.

### No arbitrary-operator absorption

An \(L^2\)-bounded translation operator does not map \(L^2\) to
\(L^\infty\), so treating the prime block as a generic lower-order forcing
would not prove the theorem.  The proof uses the exact sign decomposition
`(8)` and fails for negative atomic weights.

### Resonant shifts do not matter

The argument is per jump length and uses only `(10)`.  Coincident seams,
rational relations among shift lengths, and aperture resonances cannot
change the sign.

### Sign changes and multiplicity are allowed

No ground-state positivity or simplicity is used.  Positive and negative
truncations are independent, and real and imaginary parts are handled
separately.

### Fixed aperture is essential

The constant in `(1)` may grow with

```text
S_a=sum_(n<=exp(2a)) Lambda(n)/sqrt(n)
```

and with the compact-interval norm of \(r''\).  No cofinal uniform estimate is
claimed.

## 8. Novelty boundary

Dyda--Jarohs--Sk prove boundedness for logarithmic \(p\)-Laplacian equations
with bounded multiplication potential and bounded forcing.  Suzuki proves
the exact completed restricted-Weil operator and its finite prime
translations, but does not prove boundedness of its completed eigenfunctions.
A targeted search through 1 August 2026 found no application that rewrites
Suzuki's von-Mangoldt translation block as positive atomic jump energy and
uses it to lift every completed eigenfunction to \(L^\infty\).

The generic monotone-truncation inequality `(9)` is standard.  Novelty is
claimed only for its exact conjunction with Suzuki's completed form-domain
identity, positive von-Mangoldt coefficients, and the resulting elimination
of the unbounded completed-zero-mode escape.  Specialist priority review
remains required.

## 9. Formalization decision

This theorem has a precise unconditional formal core:

1. the shift-pair/atomic-jump identity `(7)`--`(8)`;
2. truncation monotonicity `(9)`--`(10)`;
3. the finite positive weighted sum;
4. the source specialization \(c_n=\Lambda(n)/\sqrt n\ge0\).

Formalizing only these algebraic and order-theoretic claims is useful because
they certify the load-bearing source sign.  The analytic logarithmic
truncation theorem and Suzuki form-domain identification remain imported
paper mathematics until the relevant measure and Fourier infrastructure is
available in Lean.

## Gates

- [x] completed form domain identified with zero-exterior logarithmic energy
- [x] exact prime shift pair rewritten as positive atomic jump minus potential
- [x] truncation sign proved for every visible prime atom
- [x] \(L^2\to L^\infty\) control of the polar--Gamma remainder proved
- [x] every completed eigenfunction proved bounded
- [x] bounded weak source equation and optimal half-log boundary bound obtained
- [x] unbounded completed square-Evans escape eliminated
- [ ] extend signed trace to bounded continuous weak solutions
- [ ] prove trace-zero completed zero modes enter \(H^1_0\)
- [ ] prove two-ended corona no-return
- [ ] prove raw Evans positivity
- [ ] RH
