# The leading CCM endpoint layer has an exact cofinal all-prime incidence

- **ID:** `ccm-cofinal-prime-sawtooth-incidence-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Fourier series of the periodic sawtooth, periodic averaging, and the Euler
  logarithmic derivative
- **Statement:** Integer multiplicative translates of the leading CCM endpoint sawtooth retain an
  exact rational resonance. Uniformly through the cofinal prime-power cutoff, their von Mangoldt
  incidence converges to the scalar `-(pi^2/12) zeta'(2)/zeta(2)`.

## Sawtooth normalization

Let

```text
S(x)=sum_(k>=1) sin(kx)/k
```

in `L2(R/(2*pi*Z))`, with the midpoint value at jumps. Thus, for `0<x<2*pi`,

```text
S(x)=(pi-x)/2,                  |S(x)|<=pi/2.           (1)
```

For an integer `n>=1`, put

```text
F_n(x)=S(x)S(nx).
```

## Integer-dilation resonance theorem

`[PROVED HERE]` The mean of `F_n` is

```text
mu_n=(1/(2*pi)) integral_0^(2*pi) F_n(x)dx
    =pi^2/(12n).                                      (2)
```

Moreover, there is an absolute constant `C_0` such that every zero-mean primitive

```text
A_n(x)=integral_0^x (F_n(t)-mu_n)dt                   (3)
```

extended `2*pi`-periodically satisfies

```text
sup_(n>=1) ||A_n||_infinity <= C_0.                   (4)
```

Consequently, for every `V in C_c^1(R)` and `L>0`,

```text
integral_R V(s)F_n(L e^s)ds
 =pi^2/(12n) integral_R V(s)ds + R_(n,L)(V),           (5)
```

where the error is uniform in `n`:

```text
|R_(n,L)(V)|
 <=(C_0/L) integral_R e^(-s)(|V'(s)|+|V(s)|)ds.       (6)
```

### Proof

Parseval applied first to finite sine sums and then in `L2` gives

```text
mu_n
 =1/2 sum_(k,l>=1; k=ln) 1/(kl)
 =1/(2n) sum_(l>=1)1/l^2
 =pi^2/(12n),                                         (7)
```

which proves `(2)`. The function `F_n-mu_n` is `2*pi`-periodic, has mean zero, and is bounded
uniformly in `n` by `(1)` and `(2)`. Its primitive is therefore periodic and satisfies `(4)`, for
example with

```text
C_0=2*pi*(pi^2/4+pi^2/12)=2*pi^3/3.                   (8)
```

Almost everywhere,

```text
F_n(L e^s)-mu_n
 =(1/(L e^s)) d/ds A_n(L e^s).                        (9)
```

Insert `(9)` in the left side of `(5)` and integrate by parts. The boundary term vanishes because
`V` is compactly supported, and `(4)` gives exactly `(6)`.

## Cofinal von Mangoldt incidence theorem

Define the normalized leading endpoint profile

```text
T_L(s)=e^(-s/2)S(L e^s).                              (10)
```

For `W in C_c^1(R)` and integers `N>=2`, put

```text
P_(L,N)(W)
 =sum_(2<=n<=N) Lambda(n)n^(-1/2)
    integral_R W(s)T_L(s)T_L(s+log n)ds.              (11)
```

Then

```text
P_(L,N)(W)
 =pi^2/12 * sum_(2<=n<=N) Lambda(n)/n^2
    *integral_R W(s)e^(-s)ds
  +O_W((1+log^2 N)/L).                                (12)
```

In particular, if `L->infinity`, `N=N(L)->infinity`, and

```text
log^2 N(L)=o(L),                                      (13)
```

then

```text
P_(L,N(L))(W)
 ->-pi^2/12 * zeta'(2)/zeta(2)
      *integral_R W(s)e^(-s)ds.                       (14)
```

### Proof

Translation in `(10)` gives

```text
T_L(s)T_L(s+log n)
 =n^(-1/2)e^(-s)F_n(L e^s).                           (15)
```

Apply `(5)`--`(6)` with `V(s)=W(s)e^(-s)` and multiply by the coefficient
`Lambda(n)n^(-1/2)`. Summing the main terms gives the first line of `(12)`. The total error is at
most a constant depending only on `W`, times

```text
(1/L) sum_(2<=n<=N) Lambda(n)/n
 <=(1/L) sum_(2<=n<=N) log(n)/n
 =O((1+log^2 N)/L).                                   (16)
```

This proves `(12)`. Finally, the absolutely convergent Euler logarithmic derivative identity

```text
sum_(n>=2) Lambda(n)/n^2=-zeta'(2)/zeta(2)             (17)
```

and `(13)` prove `(14)`.

The compact-support hypothesis on `W` is not needed for the unweighted lower half-line that occurs
in the CCM tail. Directly integrating `(9)` on `[0,infinity)` with `V(s)=e^(-s)` gives

```text
integral_0^infinity e^(-s)F_n(L e^s)ds
 =pi^2/(12n)+O(1/L),                                  (18)
```

uniformly in `n`; the endpoint term `A_n(L)/L` is absorbed by `(4)`. Therefore

```text
sum_(2<=n<=N) Lambda(n)n^(-1/2)
  integral_0^infinity T_L(s)T_L(s+log n)ds
 =pi^2/12 sum_(2<=n<=N) Lambda(n)/n^2
  +O((1+log^2 N)/L).                                  (19)
```

Under `(13)`, this converges to `-(pi^2/12)zeta'(2)/zeta(2)`.

## Exact CCM specialization

For an even `C2` source supported on `[-lambda,lambda]`, the endpoint theorem in
`ccm-endpoint-oscillation-poisson-tail-bound.md` identifies the leading lower exterior tail at
`v=lambda e^s` as

```text
f(lambda)/(pi*sqrt(lambda))
  *e^(-s/2)S(2*pi*lambda^2 e^s).                      (20)
```

Thus `(10)` has

```text
L=2*pi*lambda^2,
N<lambda^2.                                           (21)
```

The actual cofinal cutoff satisfies `(13)`. Hence the entire prime-power incidence of the leading
endpoint layer has the universal limit `(14)`, multiplied by the squared endpoint amplitude
`|f(lambda)|^2/(pi^2 lambda)` and by the form's fixed normalization.

The positive structural conclusion is sharp:

```text
the leading endpoint layer carries the weighted all-prime tail
through the single moment  sum Lambda(n)/n^2.          (22)
```

Therefore a CCM proof of the full pointed incidence transfer must combine this universal scalar
with at least one additional cofinal carrier: the subleading endpoint jets, a nontrivial
two-scale envelope, the interior radial-prolate autocorrelation, or the reduced-resolvent response
of `ccm-prime-source-ground-incidence-response.md`. Those additional carriers are what can retain
more than the one Euler moment in `(20)` and couple the source to the distinguished divisor/trace
moments.

## Route consequence

This theorem resolves one ambiguity in the exterior-tail gate. The leading oscillatory tail is not
lost under the growing prime cutoff, and it is not governed by the ambient coherent-growth norm.
It has a finite, explicit, all-prime limit. The remaining radial-prolate comparison can therefore
be organized as

```text
explicit leading Euler scalar
  + quantitatively smaller or richer endpoint/interior remainder
  + archimedean term
  -> true Weil Rayleigh excess and parity margin.       (23)
```

To turn `(21)` into the cofinal Weil-floor theorem, one still needs endpoint asymptotics for the
actual constrained prolate source and a bilinear remainder estimate relative to the true even
spectral gap. Neither is asserted here.

## Novelty and significance verdict

After erasing the CCM vocabulary, `(2)`--`(14)` are periodic Fourier orthogonality, a bounded
primitive estimate, and the classical Euler logarithmic derivative. The growing-cutoff synthesis
is useful for the route but does not clear the parent-theory gate. It is classified as a bridge,
not new scientific knowledge.

## References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- A. Connes, C. Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715.
- M. Th. Rassias, L. Toth, *Trigonometric representations of generalized Dedekind and Hardy sums
  via the discrete Fourier transform*, arXiv:1512.01466.

## Lean decision

The formal tree contains related Euler--Maclaurin sawtooth lemmas but no periodic `L2` Fourier
series interface or von Mangoldt Euler logarithmic derivative. Formalizing only the bounded
primitive calculation would not certify the radial-prolate remainder. No Lean file is added.

## Gates

- [x] integer-dilation sawtooth mean computed
- [x] averaging error uniform in the dilation proved
- [x] growing von Mangoldt cutoff summed
- [x] exact Euler scalar identified
- [ ] actual constrained-prolate endpoint amplitude asymptotics
- [ ] subleading/interior incidence estimate beyond the one-moment leading layer
- [ ] true Weil Rayleigh-excess or parity-margin transfer
