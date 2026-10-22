# Suzuki critical affine-Cauchy residual divergence

- **ID:** `suzuki-critical-affine-cauchy-residual-divergence`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-critical-affine-cauchy-residual-divergence-formalized.md`
- **Type:** SOURCE NO-GO / REPRESENTATION CLASSIFICATION
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`
- **Parent:** `suzuki-rooted-midpoint-compound-gram.md`

## Corpus collision

Two independent corpus theorems contain same midpoint polynomial:

```text
(w-alpha)(w-beta)=(w-m)^2-d^2,   alpha=m-d, beta=m+d.  (1)
```

`SuzukiMarkedSecantMidpointLorentzCompletion` reads right side as marked symmetric Lorentz debt.
`VonMangoldtGammaAffineBoundaryBalance` reads left side, at symmetric endpoints, as numerator of
unique affine two-boundary Cauchy residual.  This suggests tempting repair of critical rooted
Bianchi divergence: annihilate two boundary Cauchy values before taking critical cofinal limit.

## Exact candidate under hostile attack

At canonical endpoints `alpha=-1/2`, `beta=1/2`, center `w=0`, and prime rate `L_p=log p`, existing
affine residual is

```text
C(p)=twoBoundaryCauchyAffineResidual(1/2,0,L_p)
    =-1/[4 L_p(L_p+1/2)(L_p-1/2)].                    (2)
```

Weight it by actual critical rooted mass:

```text
M_aff(p)=Lambda(p)/sqrt(p) * C(p)^2.                  (3)
```

## Theorem `SUZUKI-CRITICAL-AFFINE-CAUCHY-RESIDUAL-DIVERGENCE`

`[PAPER-PROVED]`: `p |-> M_aff(p)` is not summable over primes.

If true, fixed two-boundary divided difference cannot repair critical rooted Hilbert no-go.  It
would force power-scale cancellation of inverse-quarter Euler amplitude, rather than any fixed
number of prime-log resolvent factors.

## Proof

For every prime, `L_p>=log 2>1/2`.  Thus all factors in `(2)` are positive in magnitude and

```text
L_p+1/2 <= 2L_p,   L_p-1/2 <= L_p,
C(p)^2 >= 1/(64 L_p^6).                               (4)
```

Since `Lambda(p)=L_p`,

```text
M_aff(p) >= 1/(64 sqrt(p) L_p^5).                     (5)
```

The elementary logarithm bound `log x <= 10 x^(1/10)` gives

```text
L_p^5 <= 10^5 sqrt(p),
M_aff(p) >= 1/(64*10^5*p).                            (6)
```

Euler prime-harmonic divergence finishes proof by comparison.  Every inequality is global for
`p>=2`; no
PNT, asymptotic estimate, numerical experiment, RH premise, or zero data is used.

Details: `L_p>=log 2>1/2` makes every denominator factor in `(2)` nonzero and positive.  Product
bound

```text
0<L_p(L_p+1/2)(L_p-1/2)<=2L_p^3
```

implies `(4)` after inversion and squaring.  Multiplying by positive critical mass and using
`Lambda(p)=L_p` gives `(5)`.  For `x>=0`, standard inequality
`log x<=x^epsilon/epsilon` at `epsilon=1/10` gives
`L_p<=10p^(1/10)`; fifth powers preserve order and real-power multiplication gives
`L_p^5<=10^5sqrt(p)`.  Since `sqrt(p)^2=p`, inversion yields `(6)`.  If `(3)` were summable, fixed
positive multiple of prime harmonic series would be summable, contradiction.  Square.

## Hostile falsifiers

- Sign or denominator error in exact residual `(2)`.
- Critical source mass is not `Lambda(p)/sqrt(p)` on actual Gamma-conormal connector.
- One inequality in `(4)--(6)` fails for prime `2`.
- Existing corpus already proves exact statement or stronger fixed-log-filter classification.
- External literature already states this Suzuki-specific critical residual no-go.

## Hostile verdict

`FALSE` for proposed affine-Cauchy repair; divergence theorem `SURVIVES PRELIMINARY ATTACK`.
Classical divided-difference algebra is `[BRIDGE]`; Suzuki-specific collision and no-go are
`[NOVELTY UNVERIFIED]`.

## Representation lesson

Midpoint polynomial coincidence `(1)` is real but does not solve critical topology.  Canonical
affine boundary divided difference adds only three inverse powers of `log p`; inverse critical
translation loses power `p^(1/2)` in mass.  Therefore strongest existing two-boundary Cauchy
candidate cannot be missing `L_M`.  Extension to every fixed rational prime-log filter is natural
classification conjecture, not used in theorem above.

Strongest positive survivor: exact classification saying any viable completed residual
must contain non-Hilbert prime coordinate with leading amplitude `p^(1/4) B_0(p)` and cancel that
power coefficient before entering Hilbert space.  Neumann holonomy may carry marked/alternating
sector, but it cannot replace power-scale symmetric cancellation.

## Audit state

- `[LOCAL-RESEARCH]`: symmetric affine residual and triple denominator are Lean-proved in
  `VonMangoldtGammaAffineBoundaryBalance.lean`.
- `[LOCAL-RESEARCH]`: exact critical mass and Gamma-conormal connector are Lean-proved in
  `SuzukiCriticalRootedBianchiCofinalNoGo.lean`.
- `[LITERATURE]`: Suzuki's screw source contains coefficient `Lambda(n)/sqrt(n)`
  (https://arxiv.org/abs/2206.03682); his 2026 finite-interval construction is unconditional
  (https://arxiv.org/abs/2606.09096) but source/TeX audit found no statement `(2)--(6)`.
- Classical affine interpolation/divided differences are parent mathematics; only collision with
  Suzuki midpoint debt and critical cofinal obstruction is claimed as possible new connection.

## Formalization

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalAffineCauchyResidualDivergence.lean` proves:

- `suzukiCriticalAffineCauchyResidual_eq_twoBoundary`;
- `scaled_primeHarmonic_le_suzukiCriticalAffineCauchyResidualMass`;
- `not_summable_suzukiCriticalAffineCauchyResidualMass`.

Exact positive survivor is now realized by source's aperture innovation rather than logarithmic
filter; see `suzuki-critical-aperture-quarter-shift-current.md`.
