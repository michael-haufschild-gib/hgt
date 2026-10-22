# The leading CCM endpoint layer has a universal archimedean logarithmic mass

- **ID:** `ccm-leading-endpoint-archimedean-log-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** logarithmic Fourier multipliers, semiclassical defect measures, and the
  sawtooth Fourier series
- **Statement:** The archimedean Weil form of the normalized leading lower endpoint profile
  `T_L(s)=1_(s>=0)e^(-s/2)S(Le^s)` is asymptotic to `(pi^2/12)log L`. For the constrained CCM
  source this is `(8*pi/33)d_1(lambda)log lambda`.

## Archimedean form

Use Suzuki's Fourier convention

```text
hat(u)(xi)=integral_R u(s)exp(i*xi*s)ds.
```

The archimedean part of the global Weil form is the logarithmic Fourier-multiplier form

```text
A(u)
 =1/(2*pi) integral_R m(xi)|hat(u)(xi)|^2 dxi,

m(xi)=Re psi(1/4+i*xi/2)-log pi.                                  (1)
```

The classical digamma expansion gives

```text
m(xi)=log|xi|-log(2*pi)+O(|xi|^(-2))                              (2)
```

as `|xi|->infinity`. The exact symbol is smooth and bounded below on `R`.

Let

```text
S(theta)=sum_(k>=1)sin(k*theta)/k,
T_L(s)=1_(s>=0)e^(-s/2)S(L e^s),   L>=1.                          (3)
```

The midpoint value at the sawtooth jumps is immaterial.

## Logarithmic chirp lemma

Let `P` be a mean-zero `2*pi`-periodic function with Fourier coefficients `p_k` satisfying

```text
sum_(k!=0) (1+log(1+|k|))|p_k|^2<infinity,                        (4)
```

and let `a in C_c^1(R)`. Put

```text
u_L(s)=a(s)P(L e^s).
```

For every real Fourier multiplier `M` which is bounded below and satisfies

```text
M(xi)=log|xi|+O(1),   |xi|->infinity,                              (5)
```

one has

```text
1/(2*pi*log L) integral_R M(xi)|hat(u_L)(xi)|^2 dxi
 ->||a||_2^2 sum_(k!=0)|p_k|^2.                                  (6)
```

### Proof

First take a trigonometric polynomial

```text
P_N(theta)=sum_(0<|k|<=N)p_k exp(i*k*theta).
```

Each summand of `u_(L,N)` is the oscillatory function

```text
p_k a(s)exp(i*k*L*e^s)                                            (7)
```

with nonvanishing local frequency `k*L*e^s`. For a compactly supported Fourier test symbol
`q(s,eta)`, integration by parts in the cross phases

```text
(k-l)L e^s,   k!=l,
```

and ordinary stationary phase on the diagonal give the semiclassical measure

```text
sum_(0<|k|<=N)|p_k|^2 |a(s)|^2 ds delta_(k*e^s)(deta).             (8)
```

This is also obtained directly by inserting `(7)` in the Fourier pairing: every off-diagonal
integral has derivative bounded below by `|k-l|L` on the support of `a`, while the diagonal term is
Plancherel after conjugation by its phase.

On the support in `(8)`, `eta` is bounded away from zero. Hence `(5)` implies

```text
M(L*eta)/log L ->1                                                (9)
```

uniformly there. A smooth truncation of `M(L*eta)/log L`, followed by `(8)` and then removal of the
truncation using `(5)`, proves `(6)` for `P_N`.

For completeness, the removal of the Fourier cutoff uses the logarithmic energy estimate

```text
limsup_(L->infinity) 1/log L
  *||a(P-P_N)(L e^.)||_(M+C)^2
 <=C_a sum_(|k|>N)(1+log(1+|k|))|p_k|^2,                           (10)
```

where `C` is chosen so that `M+C>=1`. To prove `(10)`, split the Fourier variable of each phase in
`(7)` into

```text
|xi| comparable to |k|L,
|xi| below that range,
|xi| above that range.
```

On the comparable range, `(5)` is bounded by
`C(log L+log(1+|k|))`; on both complementary ranges, repeated integration by parts in `s` gives a
summable geometric bound. Applying the same integration by parts to distinct phases gives the
corresponding almost-orthogonality estimate, so the squared form norm is bounded by the right side
of `(10)`, not by the square of an `l1` sum. Condition `(4)` makes that right side tend to zero.
Taking `N->infinity` after `L->infinity` proves `(6)`.

## Sawtooth archimedean law

The sawtooth has coefficients

```text
p_k=1/(2*i*k)  for k>0,
p_k=-1/(2*i*|k|) for k<0,
```

so `(4)` holds and

```text
sum_(k!=0)|p_k|^2=1/2 sum_(k>=1)1/k^2=pi^2/12.                     (11)
```

To pass from compact amplitude to `(3)`, choose cutoffs `a_(eps,M)` equal to `e^(-s/2)` on
`[eps,M]`. The omitted `L2` mass is at most `C(eps+e^(-M))`, uniformly in `L`; the logarithmic
energy version follows from `(10)` applied on the two omitted regions. Letting first `L->infinity`,
then `eps->0` and `M->infinity`, gives

```text
||T_L||_2^2 ->pi^2/12,
A(T_L)/log L ->pi^2/12.                                           (12)
```

The jump at `s=0` changes only the `O(1)` part of the logarithmic energy and therefore does not
affect `(12)`.

## Constrained CCM constant

For the normalized constrained source `g_lambda`, put

```text
a_lambda=g_lambda(lambda)/(pi*sqrt(lambda)),
L_lambda=2*pi*lambda^2,
b_lambda^0(s)=a_lambda T_(L_lambda)(s).                             (13)
```

`ccm-constrained-endpoint-euler-response-constant.md` proves

```text
|a_lambda|^2/d_1(lambda)->16/(11*pi).                              (14)
```

Since `log L_lambda~2log lambda`, equations `(12)`--`(14)` yield

```text
A(b_lambda^0)/(d_1(lambda)log lambda)->8*pi/33.                     (15)
```

This is the exact leading archimedean scale of the endpoint layer.

## Combined leading-layer law

The signed prime theorem gives

```text
Q_prime(b_lambda^0,b_lambda^0)
 =-(8*pi/33)(-zeta'(2)/zeta(2))d_1(lambda)+o(d_1(lambda)).          (16)
```

Therefore

```text
[A+Q_prime](b_lambda^0,b_lambda^0)
 /(d_1(lambda)log lambda)->8*pi/33>0.                              (17)
```

The prime response is one logarithmic order below the archimedean response on the isolated leading
layer.

## Positive requirement for completing the CCM comparison

Let `b_lambda` be the exact lower exterior tail of `E(g_lambda)` and put

```text
r_lambda=b_lambda-b_lambda^0.                                     (18)
```

The source is in the global zeta-multiplier graph domain, but its Poisson endpoint terms are not
separately in the prime form domain. The next valid comparison object is therefore the single
renormalized remainder expression

```text
2 Re QW(b_lambda^0,r_lambda)+QW(r_lambda,r_lambda),                 (19)
```

not a termwise sum of central and derivative corrections.

Equation `(17)` makes the positive obligation quantitative. If the exact source Rayleigh value is
of order `d_1` rather than `d_1 log lambda`, then `(19)` must cancel the universal archimedean term
to relative precision `1/log lambda`. If no such cancellation is needed, `(17)` itself gives the
correct `d_1 log lambda` leading scale. In either case, a successful theorem must determine `(19)`
in the closed Weil topology and then compare the resulting Rayleigh excess with the true even gap.

## Novelty and significance verdict

The logarithmic chirp lemma is standard semiclassical Fourier-multiplier theory, and the sawtooth
coefficient `(11)` is Parseval. The CCM specialization identifies an exact route scale, but after
vocabulary erasure it is a direct instance of parent theory. It is classified as a bridge. The
candidate-new residue remains the arithmetic endpoint constant in
`ccm-constrained-endpoint-euler-response-constant.md`.

## References

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, Section 2.4.
- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.

## Lean decision

The formal tree has no digamma Fourier multiplier, semiclassical measure, or PSWF endpoint
interface. Formalizing Parseval for a finite chirp would not certify `(15)`. No Lean file is added.

## Gates

- [x] logarithmic chirp lemma proved
- [x] sawtooth logarithmic mass computed
- [x] constrained archimedean scale computed
- [x] signed prime scale compared
- [ ] renormalized exact-tail remainder `(19)`
- [ ] true Weil Rayleigh-excess comparison
- [ ] cofinal floor or determinant transfer

## Lean status

`[FORMALIZED]` — supersedes the "No Lean file is added" decision recorded above, which is stale.
That decision judged that Parseval for a finite chirp alone would not certify `(15)`; the module
below instead formalizes the three exact steps the card's own proof turns on — the sawtooth mass,
the logarithmic rescaling `(9)`, and the exact constant arithmetic of `(12)`–`(15)`/`(17)` — and
leaves the digamma multiplier and the semiclassical measure explicitly as cited parents.

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMEndpointArchimedeanLog.lean`
(7 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `sawtoothCoeffSq`, `hasSum_sawtoothEnergy`, `tsum_sawtoothEnergy` — **equation (11)**: the
  sawtooth Fourier coefficients have `|p_k|² = 1/(4k²)`, and counting both signs of the frequency
  the total energy is exactly `π²/12` (Basel).
- `tendsto_logMultiplier_ratio` — **equation (9)**: for any multiplier with
  `|M(ξ) − log|ξ|| ≤ C` beyond a fixed radius and any fixed `η > 0`, `M(Lη)/log L → 1` as `L → ∞`.
  This is the step that converts the semiclassical measure into a pure logarithmic scale; the
  proof isolates `log(Lη) = log L + log η` and squeezes the bounded error against `log L`.
- `endpoint_constant_eq` — the exact constant arithmetic of `(15)`:
  `(16/(11π)) · (π²/12) · 2 = 8π/33`.
- `endpoint_scale_factorization`, `tendsto_endpoint_archimedean_scale` — **equations (12)–(15)**:
  from the sawtooth mass `π²/12`, the constrained response constant `16/(11π)` of
  `ccm-constrained-endpoint-euler-response-constant.md`, and the doubling
  `log L_λ / log λ → 2`, the archimedean endpoint scale is exactly `8π/33`.
- `tendsto_lowerOrder_response` — **equation (17)**: a response whose ratio to `d₁(λ)` converges is
  one logarithmic order below, so it contributes `0` to the leading scale; the combined limit is
  still `8π/33 > 0`.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the digamma Fourier multiplier `(1)` and its expansion `(2)`;
- the semiclassical/stationary-phase measure `(8)` for the logarithmic chirp;
- the logarithmic energy estimate `(10)` and the removal of the Fourier and amplitude cutoffs;
- the PSWF endpoint interface and the signed prime theorem `(16)`.
