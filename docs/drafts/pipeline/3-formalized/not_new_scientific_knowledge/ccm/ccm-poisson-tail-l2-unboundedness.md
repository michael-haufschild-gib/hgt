# CCM Poisson-tail control must use source-structured arithmetic cancellation

- **ID:** `ccm-poisson-tail-l2-unboundedness`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper), `[BRIDGE] [NECESSITY THEOREM]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent theories:** Mellin diagonalization of dilations; Dirichlet-polynomial multipliers;
  Connes--Consani's summation map `E`
- **Statement:** A cofinal CCM tail estimate must use structure beyond the scalar prolate deficit.
  The ambient arithmetic dilation sum has `N`-term norm at least of order `sqrt(N)`, so the required
  boundedness must arise on the radial-prolate sequence through oscillation, endpoint jets, a
  zeta-weighted graph norm, or an exact summation identity.

## Route object

For `a>0` and a positive integer `N`, define

```text
(S_(a,N)q)(v)=v^(1/2) sum_(1<=n<=N) q(nv),   v>=a.
```

View it as an operator

```text
S_(a,N):L2([a,infinity),dv) -> L2([a,infinity),dv/v).
```

This is the finite arithmetic-summation operator occurring in the CCM lower-tail mechanism. If
`q` is the positive-frequency part of the Fourier leakage of a source `f`, then Poisson inversion
expresses the lower tail of `E(f)` through the limit of these dilation sums applied to `q`.

## Theorem

`[PROVED HERE]` For every `a>0` and `N>=2`,

```text
||S_(a,N)|| >= 2^(-1/2) sum_(n=1)^N n^(-1/2)
             >= sqrt(2)*(sqrt(N)-1).                    (1)
```

Consequently,

```text
sup_N ||S_(a,N)||=infinity.                              (2)
```

In particular, the infinite arithmetic sum has no bounded extension from the source `L2(dv)`
leakage space to the target `L2(dv/v)` tail space.

## Proof

The logarithmic change of variables gives a unitary map

```text
U:L2([a,infinity),dv) -> L2([log a,infinity),dt),
(Uq)(t)=e^(t/2)q(e^t).
```

For `F=Uq`, direct substitution gives

```text
(S_(a,N)q)(e^t)
 =sum_(n=1)^N n^(-1/2)F(t+log n).                       (3)
```

The target measure `dv/v` becomes `dt`.

Put `T=log a`, `L=2 log N`, and take

```text
F(t)=L^(-1/2) 1_[T,T+L](t).
```

Then `||F||_2=1`. For

```text
t in [T,T+L-log N],
```

one has `t+log n in [T,T+L]` for every `1<=n<=N`. Equation (3) is therefore constant on this
interval with value

```text
L^(-1/2) sum_(n=1)^N n^(-1/2).
```

The interval has length `L-log N=L/2`, so

```text
||S_(a,N)q||_(L2(dv/v))
 >=2^(-1/2) sum_(n=1)^N n^(-1/2).
```

Finally,

```text
sum_(n=1)^N n^(-1/2) >= integral_1^N x^(-1/2)dx=2(sqrt(N)-1),
```

which proves (1)--(2).

## Mellin interpretation

After the same logarithmic unitary, the finite sum is a translation polynomial

```text
sum_(n<=N)n^(-1/2) tau_(log n).
```

On the full line its Fourier multiplier is the Dirichlet polynomial

```text
sum_(n<=N)n^(-1/2-it).
```

The growth in (1) is its coherent value at frequency zero. Thus the positive CCM estimate must
cancel the critical-line zeta multiplier's coherent mode in the one-sided tail geometry.

## Positive requirement for the CCM transfer

For a time-limited unit vector `f`, the prolate angle controls only

```text
||(1-P_lambda)Fourier(f)||_2^2.
```

The theorem shows that the successful estimate must be source-restricted, with cancellation beyond
an ambient operator bound of the form

```text
||1_[lambda,infinity) E((1-P_lambda)Fourier(f))||_(L2(dv/v))
 <=C_lambda ||(1-P_lambda)Fourier(f)||_2               (4)
```


The scalar concentration eigenvalue must be supplemented by cancellation data describing the
actual radial-prolate leakage vector.

For finite CCM determinants whose zeros are
real in the spectral variable, the prime-clock energy defect is exactly zero. Their unresolved
terminal gate is therefore locally uniform, zero-preserving convergence to `Xi`, not an additional
horizontal-energy estimate. The actual leakage vector is a special radial-prolate tail with strong
oscillatory and endpoint structure. A viable proof must use that structure to obtain the weighted or
projective control required by the Mellin determinants—through endpoint jets, weighted variation, a
Mellin Hardy space, an exact radial-prolate summation identity, or a different direct normal-family
argument. Such information is absent from the scalar concentration eigenvalue.

`ccm-endpoint-oscillation-poisson-tail-bound.md` supplies the first source-specific exception. For
an even compact `C2` source, the leading exterior Fourier term generates the bounded sawtooth
series `sum sin(n theta)/n`, not the coherent packet used in `(1)`. The arithmetic lower tail is
therefore controlled by endpoint jets. For the normalized CCM zero-integral two-mode source, its
Poisson zero-mode correction is moreover asymptotic to an explicit constant times the concentration
deficit. The generic theorem here remains valid, but its bad vectors are now proved not to model the
leading endpoint tail of the CCM source.

## Lean status

**Formalized unconditionally, 2026-08-04**, in
`formal/GaloisForLFunctions/RHTower/CCM/CCMArithmeticTailUnbounded.lean`.

The route taken is the card's proof with the logarithmic unitary **removed**.  The card passes to
`L²(dt)` in order to write the operator as a translation polynomial, but the extremal vector can be
written directly in the `v` variable as the pullback of the card's indicator,

```text
q(v) = L^(-1/2) v^(-1/2) on [a, a e^L],   L = 2 log N,
```

and then every step is an elementary `dv/v` computation.  Nothing is lost: the unitary is needed only
to *see* the coherence, not to prove it.

- **`arithDilationSum`** — the operator `(S_(a,N) q)(v) = sqrt v sum_(n<=N) q(nv)` of the route object.
- **`coherentPacket`**, `coherentPacket_apply`, `coherentPacket_eq_zero`, `measurable_coherentPacket`,
  **`abs_coherentPacket_le`** — the extremal vector and its uniform bound on `[a, ∞)`, which is where
  `v >= a > 0` enters.
- **`integral_Ioi_coherentPacket_sq`** — `‖q‖_(L²(dv)) = 1`.  The whole computation is
  `int_a^(a e^L) dv/v = L`, so the normalisation `L^(-1/2)` is exactly right.
- `arithDilationSum_sq_div` — the target integrand `|S q|²/v` is the square of the *plain* dilation
  sum, with the `sqrt v` cancelled.  This is what makes the `dv/v` measure invisible in the estimates.
- `exp_two_mul_log`, **`arithDilationSum_coherentPacket_window`** — the **coherent step**, equation
  `(3)` of the card: for `v in [a, aN]` every one of the `N` dilates `nv` lands in `[a, a N²]`, which
  is the support because `L = 2 log N`, and the `v`-dependence cancels exactly:

  ```text
  (S q)(v) = L^(-1/2) sum_(n=1)^N n^(-1/2),   constant on the window.
  ```

  This is the only place the choice of `L` is used, and it is the entire mechanism: the `N` dilates add
  with the same sign.
- `arithDilationSum_coherentPacket_eq_zero`, **`integrableOn_arithDilationSum_sq_div`** — the image
  lies in `L²(dv/v)`: it vanishes beyond `a e^L` and is bounded by `(N L^(-1/2) a^(-1/2))²`, so the
  window bound extends to the whole ray.  Without this the comparison with a sub-window would not be a
  statement about the norm at all.
- **`half_mul_sq_sum_le_integral`** — the squared-norm bound `(1/2)(sum_(n<=N) n^(-1/2))²`.  The
  factor `1/2` is `log N / L`, i.e. the fraction of the packet's logarithmic length on which coherence
  holds.
- `two_mul_sqrt_succ_sub_one_le_sum`, **`two_mul_sqrt_sub_one_le_sum`** — the comparison
  `sum_(n<=N) n^(-1/2) >= 2(sqrt(N+1) - 1) >= 2(sqrt N - 1)`.  Proved by induction rather than by an
  integral comparison; note that the naive induction on `2(sqrt N - 1)` **fails** (the step inequality
  is false), and shifting the target to `sqrt(N+1)` is what makes each step an instance of
  `2 sqrt(N+1) <= sqrt(N+1) + sqrt(N+2)`.
- **`two_mul_sq_sub_one_le_integral`**, `sum_inv_sqrt_nonneg`,
  **`inv_sqrt_two_mul_sum_le_sqrt_integral`**, **`sqrt_two_mul_sqrt_sub_one_le_sqrt_integral`** —
  equation `(1)` in both of its stated forms,

  ```text
  ||S_(a,N)|| >= 2^(-1/2) sum_(n=1)^N n^(-1/2) >= sqrt 2 (sqrt N - 1).
  ```

- **`exists_unit_arithDilationSum_ge`** — equation `(2)`: for every constant `C` there are `N >= 2` and
  a unit vector whose image has tail energy at least `C`.  The witness is explicit,
  `N = max 2 ceil((1 + sqrt(max C 0 / 2))²)`, so no compactness or filter argument is used.

The Mellin interpretation and the positive requirement are commentary on this bound, not additional
claims, and the source-specific exception they point to is itself formalized: the sawtooth sine series
of `SawtoothFourierSeries.lean` and the endpoint jets of `CCMEndpointFourierJet.lean` bound the
leading exterior tail of a compact `C²` source, and `CCMTwoModeDeficitScale.lean` puts the two-mode
zero-mode correction at concentration-deficit order.

## Gates

- [x] `sqrt N` lower bound for the finite arithmetic dilation sum proved
- [x] unboundedness of the infinite sum proved
- [x] Lean: coherent packet constructed and normalised
- [x] Lean: coherence on the window (the constancy identity)
- [x] Lean: image integrability, so the bound is a statement about the norm
- [x] Lean: half-power harmonic sum comparison
- [x] Lean: equation `(1)` in both stated forms, unconditional
- [x] Lean: equation `(2)`, with an explicit witness
- [ ] the positive object: the arithmetic tail map restricted to the two-dimensional low-mode
      radial-prolate family

## Novelty verdict

The theorem is an exact and useful topology classifier, but its mechanism is standard
Mellin/dilation theory. It is therefore `[BRIDGE]`, not new scientific knowledge. The positive
unresolved mathematical object is the arithmetic tail map restricted to the two-dimensional
low-mode radial-prolate family.
