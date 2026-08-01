# Forced Gamma transport: trace zero is exact upper-strip gluing

- **ID:** `suzuki-forced-gamma-upper-strip-gluing`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FORCED HARDY-SEAM CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes
- **Input:** `suzuki-gamma-homogeneous-half-log-scattering-classification.md`

## 1. Forced equation and propagator

Let \(X\) be a complex Hilbert space, \(T=T^*\in\mathcal B(X)\), and

```text
r(z)=psi(1+i z)+psi(1-i z)+2 EulerGamma.                (1)
```

On the strip

```text
S_1={z:0<Im z<1},                                       (2)
```

choose the branches equal to one on the positive real boundary and put

```text
Q(z)=exp(i EulerGamma z)
     [Gamma(1+i z)/Gamma(1-i z)]^(1/2)
     exp(-i z T/2),
H(z)=z^(-1/2)Q(z).                                      (3)
```

Then

```text
H'=[-1/(2z)+(i/2)(r(z)I-T)]H.                           (4)
```

Let \(b:S_1\to X\) be holomorphic and have polynomial growth on every closed substrip.  Consider

```text
f'=[-1/(2z)+(i/2)(r(z)I-T)]f+b.                         (5)
```

For the differentiated Suzuki equation with right side \(G'\), one has

```text
b(z)=-(i/2) Ghat(z).                                    (6)
```

No regularity of \(G\) beyond what is explicitly used below is assumed.

## 2. The particular solution has no half-log branch

### Theorem 1

`[PROVED]` The function

```text
p(z)=H(z) integral_0^z H(w)^(-1)b(w)dw                  (7)
```

is single-valued and holomorphic through \(z=0\) from the upper side, with

```text
p(z)=O_X(z).                                            (8)
```

Every boundary solution of `(5)` has unique constants \(c_+,c_-\in X\) such that

```text
f(eta)=H(eta)c_+ +p(eta),     eta>0,
f(eta)=H_-(eta)c_-+p(eta),    eta<0,                    (9)
```

where \(H_-(\eta)=(-\eta)^{-1/2}Q(\eta)\).  Its regular-singular half-log coefficient is

```text
beta
 =1/(2 sqrt(pi))
   [exp(i pi/4)c_+ +exp(-i pi/4)c_-].                   (10)
```

For inverse Fourier solutions in the bounded Suzuki source class, whose signed physical half-log
trace is already known to exist, `(10)` equals that physical trace.  The forcing contributes no
regular-singular term to `(10)`.

### Proof

Near zero, the digamma expansion gives \(Q(z)=I+O(z)\).  Hence

```text
H(z)^(-1)b(z)=z^(1/2)[b(0)+O(z)].
```

Termwise integration gives

```text
integral_0^z H(w)^(-1)b(w)dw
 =(2/3)z^(3/2)b(0)+O(z^(5/2)).
```

Multiplication by \(H(z)=z^{-1/2}[I+O(z)]\) proves `(8)`.  More generally every
\(w^{n+1/2}\) term becomes a \(z^{n+1}\) term, so all branch monodromy cancels and \(p\) is
holomorphic at zero.

Variation of constants proves `(9)`.  The particular solution is analytic at frequency zero, so
it has no \(|\eta|^{-1/2}\) coefficient.  The Fourier--Watson calculation from the homogeneous
classification gives `(10)` for the two terms \(Hc_\pm\).

To identify it with the already existing physical trace, apply the standard Abelian direction to
the source asymptotic

```text
F(L)=beta_phys L^(-1/2)+o(L^(-1/2)).
```

Its positive-tail Fourier contribution has coefficients
\(\sqrt\pi e^{-i\pi/4}\beta_{\rm phys}\) at \(\eta\downarrow0\) and
\(\sqrt\pi e^{i\pi/4}\beta_{\rm phys}\) at \(\eta\uparrow0\).  Substitution into `(10)` returns
\(\beta_{\rm phys}\).  Terms with zero physical trace have no additional critical coefficient.
`QED`

## 3. Exact forced gluing theorem

### Theorem 2

`[PROVED]` The following are equivalent:

```text
beta=0;
c_-=-i c_+;
the two boundary solutions (9) glue to one holomorphic
solution of (5) on S_1.                                 (11)
```

That holomorphic solution has polynomial growth on every closed substrip.

### Proof

Equation `(10)` gives the first equivalence.  The upper boundary value of \(z^{-1/2}\) on the
negative real axis is \(-i(-z)^{-1/2}\), while \(Q\) has one common holomorphic branch on
\(S_1\).  Hence the homogeneous terms glue exactly when \(c_-=-ic_+\).  The particular solution
`(7)` already glues by Theorem 1.  This proves `(11)`.

For growth, Stirling gives, uniformly on each closed substrip,

```text
||H(x+i sigma)||=O((1+|x|)^(-1/2-sigma)),
||H(x+i sigma)^(-1)||=O((1+|x|)^(1/2+sigma)).           (12)
```

A straight-line path in `(7)` and polynomial growth of \(b\) therefore give polynomial growth of
\(p\), and hence of \(f\). `QED`

### Distributional consequence

The strip Paley--Wiener theorem applied to the polynomially bounded holomorphic solution gives,
for every \(0<\sigma<1\),

```text
e^(sigma L)F(L) is tempered,                            (13)
```

where \(F\) is the inverse Fourier distribution of the real boundary value.  Thus after trace
zero there is no singularity of the exact forced transport between the critical branch at zero
and the Gamma wall at \(z=i\).

Statement `(13)` is deliberately distributional.  Polynomial strip growth alone is not an
\(L^2\) Hardy estimate.

## 4. Exact quantitative Hardy criterion

### Theorem 3

`[PROVED]` Fix \(0<\sigma<1\).  If

```text
integral_R (1+|x|)^(1/2+sigma)
  ||b(x+i sigma)|| dx < infinity,                       (14)
```

then every zero-trace solution in Theorem 2 satisfies

```text
f(.+i sigma) in L2(R;X),                                (15)
e^(sigma L)F(L) in L2(R;X).                             (16)
```

### Proof

By `(12)`, the Bochner integrals

```text
C_+=integral_0^infinity H(x+i sigma)^(-1)b(x+i sigma)dx,
C_-=integral_(-infinity)^0 H(x+i sigma)^(-1)b(x+i sigma)dx
```

converge absolutely under `(14)`.  Rebase variation of constants at the two infinities.  On each
frequency tail, the bracket in `(7)` is a constant plus an absolutely convergent tail bounded by
the corresponding tail of the integrand.  Multiplication by `(12)` gives

```text
||f(x+i sigma)||
 <=C(1+|x|)^(-1/2-sigma)
   [1+tail_(|t|>=|x|)
      (1+|t|)^(1/2+sigma)||b(t+i sigma)||].             (17)
```

The bracket is bounded and the power in `(17)` has square exponent \(1+2\sigma>1\).
This proves `(15)`.  Fourier translation and Plancherel give `(16)`. `QED`

Condition `(14)` is sufficient, not claimed necessary.  It is the first exact non-circular
source norm found for the forced Gamma seam.

## 5. Suzuki consequence and new open core

For a logarithmic tail cutoff, finite prime translations produce compactly supported commutator
forcing.  The literal Gamma jump commutator has physical tails \(O(e^{-|L|})\), because a point at
distance \(L\) from the cutoff can interact with it only through

```text
1/(exp(s)-1),  s>=L-O(1).                               (18)
```

Therefore its Fourier transform is holomorphic for \(|\operatorname{Im}z|<1\), and Theorem 2
applies once the completed seam state and cutoff equation are constructed.  This closes the
**analytic-continuation** part of the forced Gamma-strip problem.

It does not yet prove `(14)`.  Exponential physical localization gives an \(L^2\) shifted Fourier
line, but `(14)` asks for the additional weighted frequency moment needed by the first-order
variation operator.  In source variables this is a precise finite regularity statement for the
cutoff commutator, not a vague “smooth forcing” premise:

```text
SUZUKI-FORCED-HARDY-MOMENT:
for some sigma in (1/2,1), the completed cutoff forcing obeys (14). (19)
```

If `(19)` holds, Theorem 3 gives physical \(e^{-\sigma L}\) decay.  Since

```text
u_r(exp(-L))=-exp(L)F'(L),
```

the exponent \(\sigma>1/2\) is exactly what puts the original derivative in \(L^2(dr)\), closing
the trace-zero \(H^1_0\) connector.

## 6. Hostile audit

1. **No Hardy theatre.**  Holomorphy with polynomial growth yields `(13)`, not `(16)`.
   The weighted moment `(14)` is stated and retained.
2. **No endpoint-source deletion.**  Forcing enters through the explicit particular integral
   `(7)`.  Its branch cancellation is proved, not assumed.
3. **No guessed exponent.**  Strip endpoint one is the first pole of the exact Gamma quotient.
4. **No generic ellipticity shortcut.**  The half-log scattering map `(10)` and upper boundary
   factor \(-i\) come from the regular singularity of the literal Gamma equation.
5. **No completed-domain smuggling.**  Source must still construct its carrier-valued cutoff
   forcing and prove `(19)`.
6. **No RH claim.**  Even after trace-zero \(H^1_0\), raw Evans positivity and nonzero-trace
   corona no-return remain.

## 7. Novelty and Lean decision

Corpus and targeted external searches found no prior forced Gamma half-log gluing law of
`(7)`--`(19)` for Suzuki's restricted-Weil boundary equation.  The ingredients are standard;
their exact source conjunction appears new, with priority unverified.

Formalization must include the branch-cancelling particular solution and weighted Bochner-tail
estimate.  A Lean theorem assuming `(15)` would be circular.  Current formal tree has Bochner
integration and half-line integration by parts, but lacks the required Gamma-ratio strip modulus
and vector-valued Paley--Wiener translation package.  Those are now precise infrastructure targets.
