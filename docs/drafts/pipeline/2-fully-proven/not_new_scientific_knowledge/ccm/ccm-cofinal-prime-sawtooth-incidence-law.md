# The leading CCM endpoint layer has an exact cofinal all-prime incidence

- **ID:** `ccm-cofinal-prime-sawtooth-incidence-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Fourier series of the periodic sawtooth, periodic averaging, and the Euler
  logarithmic derivative
- **Statement:** Integer multiplicative translates of the leading CCM endpoint sawtooth retain an
  exact rational resonance. Their full exterior von Mangoldt incidence is absolutely summable,
  uniformly in the aperture, and converges to `-(pi^2/12) zeta'(2)/zeta(2)`.

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

### Full exterior all-prime theorem

The cutoff in `(19)` can be removed. Put

```text
J_n(L)=integral_0^infinity e^(-s)F_n(L e^s)ds
      =L integral_L^infinity S(x)S(nx)/x^2 dx.         (20)
```

`[PROVED HERE]` There is an absolute constant `C_1` such that, for every `L>=1` and `n>=1`,

```text
|J_n(L)|<=C_1/n.                                      (21)
```

Consequently, for every `L>=1`, the full prime response

```text
P_L^full
 =sum_(n>=2) Lambda(n)n^(-1/2)
    integral_0^infinity T_L(s)T_L(s+log n)ds           (22)
```

converges absolutely, and

```text
P_L^full ->-pi^2/12 * zeta'(2)/zeta(2)                (23)
```

as `L->infinity`.

#### Proof

Since `S` has mean zero, the primitive

```text
B_n(x)=integral_0^x S(nt)dt
```

is periodic and satisfies

```text
||B_n||_infinity=||B_1||_infinity/n.                  (24)
```

On `[L,infinity)`, put `u_L(x)=L x^(-2)S(x)`. The sawtooth is a function of bounded
variation on compact intervals, with absolutely continuous derivative `-1/2` and jumps of size
`pi` at `2*pi*Z`. Therefore

```text
Var_[L,infinity)(u_L)
 <=integral_L^infinity 2L x^(-3)|S(x)|dx
   +(1/2)integral_L^infinity L x^(-2)dx
   +pi sum_(2*pi*k>=L) L/(2*pi*k)^2
 <=C_2                                                     (25)
```

uniformly for `L>=1`. Also `u_L(x)->0` as `x->infinity` and `|u_L(L)|=O(1/L)`.
Stieltjes integration by parts in `(20)` now gives

```text
|J_n(L)|
 <=||B_n||_infinity
    *(|u_L(L)|+Var_[L,infinity)(u_L))
 <=C_1/n,
```

which proves `(21)`. By `(15)` the `n`-th summand of `(22)` is

```text
Lambda(n)/n * J_n(L).
```

Equation `(21)` dominates it by `C_1 Lambda(n)/n^2`, an absolutely summable sequence. For each
fixed `n`, `(18)` gives `J_n(L)->pi^2/(12n)`. Dominated convergence and `(17)` prove `(23)`.

## Exact CCM specialization

For an even `C2` source supported on `[-lambda,lambda]`, the endpoint theorem in
`ccm-endpoint-oscillation-poisson-tail-bound.md` identifies the leading lower exterior tail at
`v=lambda e^s` as

```text
f(lambda)/(pi*sqrt(lambda))
  *e^(-s/2)S(2*pi*lambda^2 e^s).                      (26)
```

Thus `(10)` has

```text
L=2*pi*lambda^2,
N<lambda^2.                                           (27)
```

The finite-aperture cutoff satisfies `(13)`, so `(14)` controls the matching finite prime carrier.
More strongly, `(23)` controls the complete lower-exterior prime-dilation response. Both have the
same universal limit, multiplied by the squared endpoint amplitude
`|f(lambda)|^2/(pi^2 lambda)` and by the form's fixed normalization.

The positive structural conclusion is sharp:

```text
the leading endpoint layer carries the weighted all-prime tail
through the single moment  sum Lambda(n)/n^2.          (28)
```

Therefore a CCM proof of the full pointed incidence transfer must combine this universal scalar
with at least one additional cofinal carrier: the subleading endpoint jets, a nontrivial
two-scale envelope, the interior radial-prolate autocorrelation, or the reduced-resolvent response
of `ccm-prime-source-ground-incidence-response.md`. Those additional carriers are what can retain
more than the one Euler moment in `(28)` and couple the source to the distinguished divisor/trace
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
  -> true Weil Rayleigh excess and parity margin.       (29)
```

To turn `(29)` into the cofinal Weil-floor theorem, one still needs endpoint asymptotics for the
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

## Lean status

**Superseded, 2026-08-04.**  Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMSawtoothDilationMean.lean` (the sawtooth, the mean, the bounded
primitive and the integration by parts),
`formal/GaloisForLFunctions/RHTower/CCMSawtoothDilationIncidence.lean` (the arithmetic weight, the
coordinate change, the synthesis and the limit) and
`formal/GaloisForLFunctions/RHTower/CCMSawtoothExteriorTail.lean` (the exterior half-line and the full
prime series).  Every theorem the card marks `[PROVED HERE]` is now proved in Lean.  The previous decision said no
periodic `L²` Fourier interface exists in the tree, so nothing could be certified.  That was the wrong
frame: `S` is the `2π`-periodic extension of a linear ramp, so taking

```text
S(x) = pi * (1/2 - {x/(2 pi)})
```

as the definition makes `(1)` immediate and the whole mean computation `(2)` an exact interval
integral, with no Parseval and no `L²` Fourier basis.  What the card derives from Parseval is derived
here from one change of variables and `n` polynomial integrals.

Proved so far, all unconditional (`#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`):

- `sawUnit`, `sawWave`, **`sawWave_eq_of_mem_Ioo`**, **`abs_sawWave_le`**, `sawWave_add_two_pi` —
  equation `(1)`, in closed form, with the sup bound and the period.  The closed form is no longer only
  a definitional choice: `RHTower/SawtoothFourierSeries.lean` proves
  **`tendsto_sum_sawtoothSine`**, that the card's series `∑_{k ≥ 1} sin(kθ)/k` really does converge to
  `sawWave θ` on `(0, 2π)`, so the two definitions of `S` agree.
- **`integral_sawUnit_dilate_piece`**, **`integral_sawUnit_dilate`**, **`integral_sawWave_dilate`** —
  equation `(2)`.  The `j`-th period of the fast factor contributes exactly `1/(12 n²)`, uniformly in
  `j`, and there are `n` of them.  The card's `(7)` uses Parseval on the sine series; the Lean proof
  instead pushes the dilation out of the integrand, translates each period to the origin, and
  integrates a quadratic — the mean is elementary, not spectral.
- `integral_quadratic`, `integral_congr_of_Ioo`, `intervalIntegrable_sawUnit`,
  `intervalIntegrable_sawUnit_dilate` — the integration infrastructure.  Interval integrals do not see
  the endpoint where the periodic closed form breaks, which is why the discontinuity of `S` costs
  nothing.
- **`periodic_sawUnitDilate`**, `sawDilatePrimitive`, **`sawDilatePrimitive_periodic`**,
  **`abs_sawDilatePrimitive_le`** — equations `(3)`--`(4)`.  The centered product has period one and
  mean zero, hence a periodic primitive, and `1/3` is an admissible uniform constant in unit
  normalization (the card's `C₀ = 2π³/3` is the same statement in the `2π` normalization and is not
  sharp).
- **`integral_sawUnit_comp_mul`**, **`abs_integral_sawUnit_le`** — equation `(24)`: dilation divides
  the sawtooth primitive by the dilation, and the undilated primitive is bounded by `1/8` on the whole
  line.  The card asserts the sup norm identity; the Lean version proves the scaling identity plus the
  explicit bound `1/8`, which is what the estimate consumes.
- `endpointProfile`, **`endpointProfile_mul_shift`** — equations `(10)` and `(15)`.
- **`sum_one_div_Icc_le_log`**, **`sum_vonMangoldt_div_le_log_sq`** — equation `(16)`, sharpened to an
  inequality with no error term: `∑_{2 ≤ n ≤ N} 1/n ≤ log N` follows from
  `log(N/(N+1)) ≤ -1/(N+1)`, so the visible weight is at most `log² N` exactly.
- **`lseriesSummable_vonMangoldt_two`**, **`lseries_vonMangoldt_two`** — equation `(17)`, absolute
  summability and the value `-ζ'(2)/ζ(2)`, from mathlib's von Mangoldt L-series identity.

- `intervalIntegrable_of_bound`, `integral_eq_integral_indicator`,
  **`integral_deriv_mul_primitive`** — the missing infrastructure, built here.  The card's `(9)` holds
  only almost everywhere, because `S` jumps, so the card's integration by parts differentiates a
  function that is nowhere differentiable in the classical sense.  The Lean route replaces it by a
  distributional integration by parts proved by Fubini on the triangle `{a ≤ t ≤ u ≤ b}`:

  ```text
  int_a^b phi'(u) int_a^u g = phi(b) int_a^b g - int_a^b phi g,
  ```

  valid for every bounded measurable `g`.  Only the smooth factor is ever differentiated, so no
  almost-everywhere derivative and no absolute continuity argument is needed.
- `continuous_sawDilatePrimitive`, `integral_sawDilateCentered_eq`,
  **`abs_integral_weight_mul_sawDilateCentered_le`** — equations `(5)`--`(6)`.  Against a `C¹` weight
  vanishing at both ends of the window, the dilated product agrees with its own mean up to `1/3` times
  the total variation of the weight, uniformly in the dilation.  The integration by parts is performed
  in the multiplicative variable, where the relevant primitive is exactly the bounded periodic `A_n`
  of `(3)`--`(4)`; both boundary conditions are used, which is what keeps the constant at `1/3` rather
  than `2/3`.
- **`abs_primeResponse_sub_main_le`** — equations `(12)`--`(13)` and `(19)`: the growing-cutoff
  synthesis.  The visible weight produces the exact Euler main term `(1/12) ∑_{2 ≤ n ≤ N} Λ(n) n^{-2}`
  with total error at most `(1/3) log² N` times the total variation of the weight.  The card's `(13)`
  is exactly the condition that this product tends to zero.

- `image_Ioo_exp_scale`, **`integral_comp_exp_scale`** — the change of variables `x = L e^s`.  Because
  the sawtooth factor is discontinuous this uses the measurable change of variables
  `integral_image_eq_integral_abs_deriv_smul`; the continuous substitution rule does not apply.
- `additiveWeight`, `hasDerivAt_additiveWeight`, `integral_additiveWeight_mul_comp`,
  `integral_abs_deriv_comp_exp_scale`,
  **`abs_integral_additiveWeight_mul_sawDilateCentered_le`** — `(5)`--`(6)` in the card's own additive
  coordinates.  The identity `(L e^s)² G'(L e^s) = V'(s) - V(s)` is what turns the multiplicative total
  variation into the card's `(1/L) ∫ e^{-s}(|V'| + |V|)`, so the bound is reproduced exactly, with
  `C₀ = 1/3` in unit normalization.
- `multiplicativeWeight`, `multiplicativeWeightDeriv`, `additiveWeight_multiplicativeWeight`,
  `multiplicativeWeight_eq_zero_of_lt`, **`hasDerivAt_multiplicativeWeight`**,
  **`continuous_multiplicativeWeightDeriv`**, `abs_multiplicativeWeightDeriv_le`,
  `integral_abs_multiplicativeWeightDeriv_le` — the inverse construction.  The multiplicative weight
  `V(log(x/L))/x` is singular at the origin for a general `V`, but it is globally `C¹` exactly when `V`
  has compact support: the weight then vanishes on a whole neighbourhood of `0`.  This is the technical
  content of the card's `C_c^1` hypothesis.
- **`abs_integral_weight_mul_dilate_le`** — `(5)`--`(6)` exactly as the card states them, for a `C¹`
  additive weight vanishing outside the window.
- **`abs_primeResponse_additive_sub_main_le`** — `(12)`--`(13)` and `(19)` in the card's variables:
  the error is `log² N / (3L)` times the fixed additive integral `∫ e^{-s}(|V'| + |V|)`, so the card's
  `log² N = o(L)` is exactly the statement that the bound vanishes.

- **`summable_vonMangoldt_div_sq`**, **`tendsto_sum_vonMangoldt_div_sq`**,
  **`tendsto_primeResponse_additive`** — equation `(14)`.  The real series `Λ(n) n^{-2}` is absolutely
  summable, obtained from the complex L-series statement `(17)` through `summable_norm_iff`, and its
  partial sums converge; combined with the error term of `(12)` this gives the limit along any schedule
  with `log² N(L) = o(L)`, which is the card's `(13)`.  Nothing else about the schedule is used.
- `invSqWeight`, `invSqWeightDeriv`, `hasDerivAt_invSqWeight`, `integral_abs_invSqWeightDeriv`,
  `integral_invSqWeight`, **`abs_integral_invSqWeight_mul_sawDilate_sub_mean_le`**,
  `additiveWeight_invSqWeight`, `integral_expWeight_eq_invSqWeight`,
  **`abs_integral_expWeight_sawDilate_sub_mean_le`** — equation `(18)` on every finite window, with the
  card's `O(1/L)` made explicit as `4/(3L)`, uniformly in the dilation *and* in the outer endpoint.
  The estimate is the same distributional integration by parts, now against the exterior weight
  `L x^{-2}`, whose total variation on the window is exactly `1/L - L/T²`.  The card's `A_n(L)/L`
  boundary term is the `invSqWeight L T · (A_n(T) - A_n(L))` term here.

- `sawUnit_eq_of_mem_Ico_int`, `abs_integral_sawUnit_comp_mul_le` — equation `(24)` in the form the
  tail bound needs: the sawtooth is affine on each period, and the primitive of its `n`-fold dilate is
  bounded by `1/(4n)` on the whole line, over all base points.
- `exteriorPiece`, `exteriorPieceDeriv`, `hasDerivAt_exteriorPiece`,
  `invSqWeight_mul_sawDilate_eq_exteriorPiece`, **`abs_integral_exteriorPiece_mul_le`**,
  `hasDerivAt_invPowPrimitive`, `integral_invPow`, **`abs_integral_exteriorPiece_period_le`**,
  **`abs_integral_invSqWeight_mul_sawDilate_int_window_le`** — equation `(21)` over any whole number of
  periods beyond `L`, with the absolute constant `5/8`:

  ```text
  | int_m^M L x^(-2) S(x) S(nx) dx | <= 5/(8n),   1 <= m <= M,  L <= m.
  ```

  The card obtains `(21)` from Stieltjes integration by parts against the bounded variation `(25)` of
  `L x^{-2} S(x)`.  No bounded-variation theory is needed here: on each period the slow factor
  `L x^{-2}(k + 1/2 - x)` is smooth, so the same distributional integration by parts applies, paired
  against the dilated primitive of `(24)`.  The boundary term of each period is absorbed by widening
  the comparison weight from `L x^{-3} + L x^{-2}` to `L x^{-3} + 2 L x^{-2}`, because over a full
  period `∫ L x^{-2} = L/(k(k+1))` already dominates `L/(2(k+1)²)`; the whole estimate then telescopes
  into a single explicit integral, so no harmonic-sum tail bound is needed either.

- `abs_integral_invSqWeight_mul_sawDilate_partial_le`,
  **`abs_integral_invSqWeight_mul_sawDilate_window_le`** — `(21)` for an arbitrary window: the two
  partial end periods are one application each of the per-period estimate, and the interior is the
  integer-window bound, giving the absolute constant `13/8`.
- `integrableOn_invSqWeight_mul_sawDilate`, `tendsto_integral_invSqWeight_mul_sawDilate`,
  **`abs_integral_Ioi_invSqWeight_mul_sawDilate_le`**,
  **`abs_integral_Ioi_invSqWeight_mul_sawDilate_sub_mean_le`** — both estimates on the half-line
  `(0, ∞)`.  Integrability comes from the uniform bound `∫_L^T ‖·‖ ≤ 1/4`, and the two estimates pass to
  the limit because they were already uniform in the outer endpoint.
- `image_Ioi_exp_scale`, `integral_comp_exp_scale_Ioi`,
  **`integral_expWeight_Ioi_eq_invSqWeight`** — equation `(20)`: the additive and multiplicative
  readings of the full exterior integral agree.
- **`summable_fullPrimeResponse`**, `tendsto_integral_Ioi_invSqWeight_mul_sawDilate`,
  **`tendsto_fullPrimeResponse`** — equations `(22)`--`(23)`.  The series converges absolutely,
  uniformly in `L ≥ 1`, dominated by `(13/8) Λ(n) n^{-2}`; the termwise limit is `(18)`; and Tannery's
  theorem gives `P_L^full → (1/12) ∑ Λ(n) n^{-2}`, which by `(17)` is `-(π²/12) ζ'(2)/ζ(2)` in the
  card's normalization.

Nothing the card proves is left unformalized.  The remaining open gates below are the card's own
research items, which it does not claim.

## Gates

- [x] integer-dilation sawtooth mean computed
- [x] averaging error uniform in the dilation proved
- [x] growing von Mangoldt cutoff summed
- [x] full exterior von Mangoldt series dominated and summed
- [x] exact Euler scalar identified
- [x] Lean: closed form, sup bound and period of the sawtooth `(1)` unconditional
- [x] Lean: exact integer-dilation mean `(2)` unconditional, without Parseval
- [x] Lean: bounded zero-mean periodic primitive `(3)`--`(4)` unconditional
- [x] Lean: dilated primitive scaling and bound `(24)` unconditional
- [x] Lean: endpoint profile shift identity `(10)`, `(15)` unconditional
- [x] Lean: visible arithmetic weight bound `(16)` unconditional, with no error term
- [x] Lean: Euler logarithmic-derivative moment `(17)` unconditional
- [x] Lean: distributional integration by parts against a bounded primitive
- [x] Lean: averaging estimate `(5)`--`(6)` unconditional
- [x] Lean: growing-cutoff synthesis `(12)`--`(13)`, `(19)` unconditional
- [x] Lean: additive/multiplicative change of variables unconditional
- [x] Lean: averaging estimate and synthesis in the card's own coordinates `(5)`--`(6)`, `(12)`--`(13)`
- [x] Lean: the limit form `(14)` unconditional
- [x] Lean: exterior finite-window estimate `(18)` unconditional, with an explicit constant
- [x] Lean: exterior `O(1/n)` bound `(21)` unconditional, without bounded-variation theory
- [x] Lean: improper-integral forms of `(18)` and `(20)` unconditional
- [x] Lean: full exterior series and limit `(22)`--`(23)` unconditional
- [ ] actual constrained-prolate endpoint amplitude asymptotics
- [ ] subleading/interior incidence estimate beyond the one-moment leading layer
- [ ] true Weil Rayleigh-excess or parity-margin transfer
