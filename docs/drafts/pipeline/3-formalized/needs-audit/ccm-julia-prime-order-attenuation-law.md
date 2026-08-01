# CCM Julia prime-order attenuation law

- **ID:** `ccm-julia-prime-order-attenuation-law`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM / source-transport law
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY SEARCH NONCOLLISION] [NOT RH]`
- **Origin:** whole-corpus audit of the canonical Gamma-sewn Julia normal coordinate against the
  reduced CCM first-clock tower obstruction

## Why this route survives the corpus no-gos

Every scalar Gamma sewing, common-aperture Pick mixing, exponential tilt, and Dirichlet-convolution
functional already audited in the corpus either preserves the bad outer/aligned odds or worsens
them.  The canonical Julia lift is different: it is source-defined, two-channel, isometric before
scalarization, retains the prime-log environment coordinate, and is singular at the lossless
boundary.  Its squared critical environment mass nevertheless has an exact scalar attenuation.
The question is whether that attenuation has the strict prime order needed by the reduced
first-clock obstruction.

## Frozen conjecture JPOA-1 — resolved

For `y > 0`, define the universal Gamma-sewn Julia compression and defect by

```text
C(y)^2 = cosh(y/2)^2 / sqrt(cosh(2y)),
D(y)   = 1-C(y)^2,
R(y)   = 4 D(y)/(3 y^2).
```

Extend `R` continuously by `R(0)=1`.  Then:

1. `R` is strictly decreasing on `(0,infinity)`;
2. the arithmetic attenuation is positive and tends coefficientwise to `1` as `x->0+`;
3. for every prime `p`, exponent `e>=1`, and Julia aperture `x>0`, the critical hard mass is

   ```text
   J_x(p^e) = R(x log p) * Lambda(p^e)/sqrt(p^e);
   ```

4. the same factor multiplies every exponent in one `p`-tower, so Julia regularization preserves
   each complete tower's sign while strictly favoring every smaller prime over every larger prime;
5. at the first clock, every admitted multi-mode tower prime is strictly smaller than every
   one-mode outer tower prime. Hence canonical Julia regularization gives a strict pairwise
   good/bad budget gain. Aggregate domination, including `p=2,3`, remains open.

## Paper attack

Put `t=tanh(y/2)` and `P=1+6t^2+t^4`.  Hyperbolic duplication gives

```text
C(y)^2 = 1/sqrt(P),
D'(y)  = C(y)^2 * (tanh(2y)-tanh(y/2)),
tanh(2y)-tanh(y/2)
       = t(1-t^2)(t^2+3)/P.
```

The sign of `R'` is the sign of `y D'(y)-2D(y)`.  Since `y=2 artanh(t)`, it is enough to prove

```text
artanh(t) * t(1-t^2)(t^2+3)/P < sqrt(P)-1.                 (E)
```

For `0<t<1`, strict `z<sinh z` at `z=2 artanh(t)` gives

```text
artanh(t) < t/(1-t^2).
```

Thus the left side of `(E)` is less than `t^2(t^2+3)/P`.  Rationalizing the right side reduces
the remaining inequality to

```text
P(t^2+6) > (sqrt(P)+1)(t^2+3).
```

Because `1<sqrt(P)<P` and

```text
3P-(t^2+3)=17t^2+3t^4>0,
```

this is strict.  Therefore `yD'(y)<2D(y)` and `R'(y)<0`.

## Hostile tests and no-go closure

- **Boundary circularity:** if the literal first-clock source is negative at some `L`,
  coefficientwise convergence `R(x log p)->1` preserves that negativity for all sufficiently
  small `x`.  Positivity for every positive Julia aperture is therefore RH-level, not an
  unconditional consequence of dilation theory.
- **Tower-local repair:** impossible.  One `p`-tower receives one positive scalar, so its sign is
  unchanged.  The gain is cross-prime order, not local cancellation.
- **Small-square exception:** a negative `p=2` or `p=3` two-mode tower is emphasized rather than
  suppressed.  It must remain explicit in every aggregate theorem.
- **Source-faithful boundary layer:** for schedules `x=x(L)`, the useful order gap is governed by
  `alpha_L=x(L)L`.  If `alpha_L->0`, regularization becomes source-faithful but the strict
  outer/inner attenuation gap collapses.  If `alpha_L` stays positive, a nonzero gap survives but
  the boundary source is not recovered uniformly at scale `L`.  This is the exact seam to audit,
  not a claim of positivity.

## Novelty protocol

Exact corpus searches found Julia source transport, coefficientwise Mellin-boundary recovery,
prime-face convolution rigidity, worsening exponential-tilt odds, and first-clock tower collapse,
but no monotonicity theorem for the Julia critical attenuation profile and no outer/inner
first-clock order consequence.  Primary-source search will be completed before promotion.

## Lean plan

1. formalize the universal profile, exact hyperbolic normal form, and strict elasticity inequality;
2. prove strict antitonicity on `(0,infinity)` without numerical computation;
3. prove exact critical-mass factorization and towerwise scalarity;
4. instantiate the ordered signed-packet comparison at the reduced CCM first clock;
5. wire new modules into `HTGeometry`/`RHTower`, then run one foreground final audit.

## Resolution and formal audit — 2026-08-01

JPOA-1 is proved in the exact form required by the reduced first-clock obstruction. New modules:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaDefectAttenuation.lean
formal/GaloisForLFunctions/RHTower/GammaSewnMobiusJuliaPrimeOrderAttenuation.lean
```

Formal capstones:

```text
HTGeometry.strictAntiOn_juliaDefectAttenuationProfile
RHTower.gammaSewnMobiusValuationContractionMultiplier_sq_eq_hyperbolic
RHTower.gammaSewnMobiusJuliaPrimeAttenuation_eq_profile
RHTower.gammaSewnMobiusJuliaPrimeAttenuation_strictAnti
RHTower.ccmFirstClockJuliaAttenuation_outer_lt_multimode
RHTower.ccmFirstClockJuliaAttenuation_relative_budget_gain
RHTower.ccmFirstClockJuliaAttenuatedPrimePowerTowerMass_nonpos_iff
RHTower.gammaSewnMobiusJuliaHardHalfWeightTransport_sq_eq_attenuated
```

The exact arithmetic law is

```text
hard_x(u,p^e)^2 = R(x log p) * boundary(u,p^e)^2.
```

Thus every exponent in a `p`-tower receives the same positive scalar. Tower sign is preserved.
For an admitted multi-mode prime `p` and one-mode outer prime `q`, Lean proves `p<q`, hence
`R(x log q)<R(x log p)` for every `x>0`. For `G>0`, the exact budget improvement is

```text
R_q (G-B) < R_p G - R_q B.
```

This is genuine favorable source transport, but not positivity: negative one-prime towers remain
negative and `R(x log p)->1` as `x->0+`. Remaining mathematical core is aggregate lower control
showing cross-prime gain pays for all outer mass plus the explicit `p=2,3` two-mode residual while
retaining enough boundary fidelity.

Primary-source/corpus novelty search found generic Julia/Halmos dilation theory and the CCM zeta
spectral-triple framework, but no occurrence of the exact quartic profile
`1+6 tanh(y/2)^2+tanh(y/2)^4`, its strict attenuation theorem, or its first-clock prime-order
consequence. This records noncollision, not a priority claim.

Verification:

- direct `lake env lean` checks: green;
- final builds: `2787/2787` and `9525/9525`;
- eight capstone axiom reports: exactly `[propext, Classical.choice, Quot.sound]`;
- formal lint: no forbidden declaration or reachability failure in new modules; nonzero only for
  five unrelated pre-existing umbrella gaps.
