# Critical prime sampling forces logarithmic kernel microlocalization

- **ID:** `critical-prime-sampling-microlocalization-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / HILBERT--POLYA CARRIER LAW / BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** If the critical prime evaluations are a Bessel family of normalized evaluation
  vectors in an RKHS, then every fixed positive normalized-kernel coherence radius at logarithmic
  location `x` is `O(1/x)`.  At cutoff `N`, a bounded Hilbert carrier must therefore resolve the
  prime source on the same `1/log N` scale as the finite-prime horizontal boundary layer.  For a
  locally regular de Branges phase this forces `phi'(x) >> x`.

## Setup

Let `H` be an RKHS of complex-valued functions on a real tail, with reproducing kernel `K`.  Assume

```text
K(x,x)>0
```

throughout that tail, and write

```text
k_x=K(.,x),
e_x=k_x/sqrt(K(x,x)),
C_K(x,y)=|K(x,y)|^2/(K(x,x)K(y,y))=|<e_x,e_y>|^2.          (1)
```

The quantity `C_K` is the squared normalized kernel coherence.  It is unchanged by a nonvanishing
real entire gauge `K(x,y) -> H(x)conj(H(y))K(x,y)`.

Put

```text
w_p=(log p)^2/p.                                           (2)
```

The normalized critical prime sampling operator is

```text
(S f)_p=sqrt(w_p) f(log p)/sqrt(K(log p,log p)).            (3)
```

Assume that it is bounded:

```text
sum_p w_p |f(log p)|^2/K(log p,log p)
  <= B^2 ||f||_H^2.                                        (4)
```

No lower frame bound or reconstruction theorem is assumed.

## Kernel testing law `[PROVED]`

Insert `f=e_x` into `(4)`.  Since `||e_x||=1`, one obtains the exact necessary condition

```text
sum_p w_p C_K(x,log p) <= B^2.                             (5)
```

Fix `0<c<=1`.  Let `r(x)` be any function with `0<r(x)<=1` such that

```text
C_K(x,log p)>=c
whenever |log p-x|<=r(x).                                  (6)
```

Then `(5)` gives

```text
c sum_(|log p-x|<=r(x)) (log p)^2/p <= B^2.                (7)
```

This is the exact Hilbert-space input.  It is valid in every RKHS and is invariant under the
zero-free de Branges gauges which preserve the normalized kernel geometry.

## Prime mass at logarithmic scale `[PROVED]`

Uniformly for `0<r<=1`,

```text
sum_(|log p-x|<=r) (log p)^2/p = 2xr+o(1)                 (8)
```

as `x->infinity`.  The `o(1)` is uniform in `r`.

To prove `(8)`, let

```text
theta(X)=sum_(p<=X) log p,
A(X)=sum_(p<=X) (log p)^2/p.
```

The classical zero-free-region form of the prime number theorem gives

```text
theta(X)=X+O(X exp(-a sqrt(log X)))                         (9)
```

for some `a>0`.  Partial summation with `g(t)=log(t)/t` yields

```text
A(X)=int_(2-)^X g(t) d theta(t)
    =(1/2)(log X)^2+C+o(1),                                (10)
```

where the remainder tends to zero: after writing `theta(t)=t+E(t)`, the error integral is governed
by

```text
int^infinity exp(-a sqrt(u)) u du<infinity,
u=log t.
```

Apply `(10)` at `X=exp(x+r)` and `X=exp(x-r)`.  Both remainders tend to zero uniformly for
`0<r<=1`, the constant cancels, and

```text
((x+r)^2-(x-r)^2)/2=2xr,
```

which proves `(8)`.

## Logarithmic microlocalization theorem `[PROVED]`

Combining `(7)` and `(8)` gives

```text
limsup_(x->infinity) x r(x) <= B^2/(2c).                   (11)
```

In particular, a fixed positive coherence level cannot persist on any radius asymptotically wider
than `1/x`.  At a prime cutoff `N`, where `x=log N`,

```text
r(log N)=O(1/log N).                                       (12)
```

The positive implementation law is therefore:

> A Hilbert carrier which receives the critical prime source by bounded normalized evaluation must
> develop intrinsic kernel resolution at the logarithmic boundary scale.  It cannot remain a
> fixed-resolution translation-invariant or fixed-bandwidth geometry.

This does not say that prime sampling is impossible.  It says what the carrier geometry must do in
order for sampling to be bounded.

## De Branges phase-speed corollary `[PROVED]`

Let `H=H(E)` be a de Branges space, let `phi` be the increasing phase of `E` on the real axis, and
assume `phi'(x)>0`.  The real kernel formula gives

```text
C_E(x,y)
 = sin(phi(x)-phi(y))^2
   / ((x-y)^2 phi'(x) phi'(y)).                            (13)
```

This formula is gauge invariant.  Assume that for some fixed `M>=1` and every sufficiently large
`x`,

```text
M^(-1) phi'(x) <= phi'(t) <= M phi'(x)
whenever |t-x| <= 1/(2M phi'(x)).                          (14)
```

For `|y-x|<=1/(2M phi'(x))`, the phase increment has absolute value at most `1/2`.  Using
`|sin u|>=(2/pi)|u|` for `|u|<=pi/2`, the lower bound in `(14)`, and the upper bound for `phi'(y)`,
equation `(13)` gives

```text
C_E(x,y) >= 4/(pi^2 M^3).                                 (15)
```

Apply `(11)` with

```text
r(x)=min(1,1/(2M phi'(x))),
c=4/(pi^2 M^3).
```

The alternative `r(x)=1` cannot persist because `(11)` makes `x r(x)` bounded.  Hence eventually
`r(x)=1/(2M phi'(x))`, and it follows that

```text
liminf_(x->infinity) phi'(x)/x
  >= 4/(pi^2 M^4 B^2).                                    (16)
```

Thus a locally regular de Branges carrier which admits bounded normalized critical-prime sampling
must have phase speed at least linear in the prime-log coordinate.  Equivalently, it must allocate
at least quadratic phase volume up to logarithmic radius `x`.

The hypothesis `(14)` is load-bearing.  Without local phase regularity, the general coherence law
`(11)`, rather than the pointwise derivative bound `(16)`, is the canonical statement.

## Hilbert--Polya consequence

The corpus now imposes three independent positive obligations on a finite-prime Hilbert--Polya or
de Branges construction.

1. The finite archimedean Gamma product contributes only one projective valuation direction.  The
   construction must separately retain the prime-log character module, of cutoff rank at least
   `pi(N)`.
2. If that arithmetic carrier enters a Hilbert space by bounded normalized critical-prime
   evaluation, its kernel coherence radius at cutoff `N` must be `O(1/log N)` by `(12)`.
3. Its characteristic entire functions must carry the actual completed divisor locally uniformly
   and zero-preservingly through the cofinal limit; finite self-adjointness or finite positivity
   alone does not supply this transfer.

The rank requirement and the microlocalization requirement are different.  The first counts
independent arithmetic phases.  The second controls how sharply a Hilbert carrier must distinguish
their increasingly dense logarithmic sampling sites.  A viable architecture must satisfy both and
then prove the global determinant/divisor transfer.

## Attacks and exact boundary

1. **Gauge attack.** Normalizing every evaluation vector makes `(5)`--`(16)` invariant under the
   zero-free real gauges which leave a de Branges spectral class unchanged.
2. **Ambient `L2` attack.** The theorem does not use point values on an `L2` equivalence class.  It
   begins only after a genuine point-evaluable RKHS has been source-selected.
3. **Uniqueness-versus-stability attack.** Prime logarithms may be a uniqueness set while `(4)`
   fails.  The theorem concerns the Bessel/upper-frame half of stable synthesis, not uniqueness.
4. **Weight attack.** The conclusion is for the critical explicit-formula weights `(2)`.  A weaker
   weight may be Bessel at larger coherence radius, but then a separate theorem must show that it
   still transports the completed prime distribution.
5. **Coordinate attack.** The variable `x` is the prime-log sampling coordinate.  Identifying it
   with a spectral-height coordinate requires an explicit source-to-spectrum transform and is not
   assumed here.
6. **RH attack.** No zero location, Weil positivity, Herglotz property, or RH-equivalent
   de Branges identification enters the proof.

## Scientific verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  Equation `(5)` is the standard normalized-kernel test
for a Carleson/Bessel embedding.  Equations `(13)`--`(16)` are a direct de Branges phase-metric
specialization.  The prime asymptotic `(8)` is a partial-summation consequence of the classical
prime number theorem.  Their combination isolates the exact `1/log N` law needed by this project,
but introduces no new parent mechanism.

Relevant parent literature includes:

- J. Marzo, S. Nitzan, and J.-F. Olsen, *Sampling and interpolation in de Branges spaces with
  doubling phase*, Journal d'Analyse Mathematique 117 (2012), 79--123,
  `https://arxiv.org/abs/1103.0566`;
- A. Hartmann, P. Jaming, and K. Kellay, *Quantitative estimates of sampling constants in model
  spaces*, Journal of Mathematical Analysis and Applications 456 (2017), 1362--1384,
  `https://arxiv.org/abs/1707.07880`;
- the classical prime number theorem with a zero-free-region error term.

## Lean status (SUPERSEDED)

The original status read:

> The current tree already proves divergence of the global critical prime profile in
> `PrimeLogSamplingWeightObstruction.lean`.  It does not contain RKHS/de Branges normalized
> kernels, the short logarithmic-window asymptotic `(8)`, or the phase formula `(13)`.  Adding only
> the scalar inequality `(7)` would be wrapper bloat rather than a formalization of the theorem.
> No Lean formalization is claimed.

Two of the three obstacles were already gone.  The short-window asymptotic `(8)` is the
second-order Mertens theorem, which the corpus proves unconditionally in
`RHTower/PrimeHigherMertens` from the de la Vallée Poussin error term; and the phase formula `(13)`
is an elementary polar-form computation, not de Branges space theory.  The normalized-kernel layer
is three definitions.  The card is now formalized; see below.

## Lean formalization — COMPLETE

Module `RHTower/PrimeSamplingMicrolocalization`.  Every capstone audits to
`propext, Classical.choice, Quot.sound`.

| Card | Lean |
|---|---|
| `(1)` squared normalized kernel coherence `C_K` | `RHTower.kernelCoherence`, `RHTower.unitCoherence` |
| `C_K` is gauge invariant under `K ↦ H(x) conj(H(y)) K` | `RHTower.kernelCoherence_gauge` |
| `C_K` of a Gram kernel; normalization of evaluation vectors | `RHTower.kernelCoherence_gram`, `RHTower.norm_normalized`, `RHTower.unitCoherence_normalized` |
| `(2)`–`(3)` critical prime weights `w_p = (log p)²/p` | `RHTower.primeLogPowWeight` (corpus, at `k = 2`) |
| `(4)` boundedness of the normalized sampling operator | `RHTower.PrimeSamplingBessel` |
| `(5)` kernel testing law | `RHTower.primeSampling_kernel_test` |
| `(6)`–`(7)` coherence floor bounds the window prime mass | `RHTower.primeLogWindowMass_le` |
| `(8)` uniform logarithmic-window prime mass `2 x r + o(1)` | `RHTower.primeLogWindowMass`, `RHTower.primeLogWindowMass_eq_sum`, `RHTower.primeLogWindowMass_uniform_asymptotic` |
| `(9)`–`(10)` PNT error term and `∑_{p≤X}(log p)²/p = (log X)²/2 + C + o(1)` | corpus: `RHTower.Sieve.chebyshevTheta_sub_id_isBigO`, `RHTower.tendsto_primeLogPowSum_sub` |
| `(11)` microlocalization law `limsup x r(x) ≤ B²/(2c)` | `RHTower.prime_coherence_radius_bound` |
| `(12)` `r(log N) = O(1/log N)` | `RHTower.prime_coherence_radius_cutoff` |
| `(13)` de Branges phase kernel formula | `RHTower.deBrangesKernelOffDiag`, `RHTower.deBrangesKernelOffDiag_polar`, `RHTower.deBrangesRealKernel`, `RHTower.phaseCoherence`, `RHTower.kernelCoherence_deBranges` |
| `(14)`–`(15)` local phase regularity gives a coherence floor | `RHTower.phaseCoherence_ge` (with `RHTower.abs_sin_ge_of_abs_le`, `RHTower.sq_sin_ge_of_abs_le`, `RHTower.exists_mvt_between`) |
| `(16)` phase-speed bound | `RHTower.phase_speed_ge`, `RHTower.phase_speed_liminf` |

`(11)` is stated in the sharp `∀ ε > 0, ∀ᶠ x, x r(x) ≤ B²/(2c) + ε` form, which is exactly
`limsup_{x→∞} x r(x) ≤ B²/(2c)` and avoids the junk value of `Filter.limsup` on an unbounded
family.  `(16)` is given both in the quantitative `D`-parametrized form
(`∀ᶠ x, 1/(2 M D) ≤ φ'(x)/x` for every `D > π² M³ B²/8`) and in the card's limit form
(`∀ ε > 0, ∀ᶠ x, 4/(π² M⁴ B²) − ε ≤ φ'(x)/x`).

The hypotheses of the Lean statements are exactly the hypotheses of the card: the Bessel bound
`(4)`, the coherence radius `(6)`, and the local phase regularity `(14)`.  Nothing else is assumed.

### What is *not* formalized

- The construction of a de Branges space `H(E)` and the derivation of its reproducing kernel from
  `E`.  The corpus has no general de Branges space theory.  `(13)` is proved for the real-axis
  kernel *written in the de Branges form* `K(x,y) = (B(y)A(x) − A(y)B(x))/(π(y−x))` with the polar
  data `A = m cos φ`, `B = m sin φ`, and diagonal value `m² φ'/π` — that is, from exactly the two
  structural inputs the card quotes.  Which entire functions `E` produce such data is not addressed.
- The Hilbert--Pólya consequence section, which is a discussion of three separate obligations rather
  than a theorem.


## Gates

- [x] normalized-kernel Bessel test proved
- [x] uniform logarithmic-window prime-mass asymptotic proved
- [x] sharp `O(1/log N)` coherence law proved
- [x] locally regular de Branges phase-speed corollary proved
- [x] RH-free and gauge-invariant formulation checked
- [x] parent-theory novelty claim rejected
- [x] complete unconditional Lean formalization

## Log

- 2026-08-20 — Stage 2 → 3.  The "no Lean formalization is claimed" status was overturned: `(8)` is
  the corpus's own second-order Mertens theorem and `(13)` is a polar-form computation.  New module
  `RHTower/PrimeSamplingMicrolocalization`, wired into `GaloisForLFunctions.RHTower`; every capstone
  audits to `propext, Classical.choice, Quot.sound`.
