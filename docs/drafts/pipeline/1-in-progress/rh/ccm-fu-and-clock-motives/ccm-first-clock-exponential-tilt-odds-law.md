# First-clock exponential tilt increases counter-phase odds

- **ID:** `ccm-first-clock-exponential-tilt-odds-law`
- **Stage:** 1-in-progress
- **Lane:** CCM / published first-clock source
- **Type:** THEOREM / source-specific no-go with positive survivor
- **Status:** `[PAPER PROOF CLOSED] [CORE LAW LEAN-FORMALIZED] [TARGET BUILD PASSED]`
  `[STRICT FORM OPEN] [NOT RH]`
- **Depends on:** `ccm-first-clock-landau-completeness-law`,
  `ccm-euler-essential-boundary-layer-correspondence`

## Frontier attacked

The actual Euler current has positive limiting first-clock phase for safe weights
`Λ(n)n^(-σ)`, `σ > 1`.  The RH-complete source uses the hard first-aperture weights
`Λ(n)/sqrt(n)`.  On a fixed aperture, passing from exponent `σ` to exponent `1/2` is positive
exponential tilting in the log coordinate.  Question:

> Can positivity on the safe Euler side cross the half-weight seam by a positive diagonal
> reweighting of the same prime-power atoms?

## Theorem C41

Let a finite positive source be supported in a first sine period `[0,L]`.  Split it into aligned
support `[0,L/2]` and counter-phased support `[L/2,L]`.  For exponential tilt parameter `θ`, let

```text
A(θ)=sum aligned_weight(h) exp(θ h),
C(θ)=sum counter_weight(h) exp(θ h).
```

Then for `θ₁ <= θ₂`,

```text
C(θ₂) A(θ₁) >= C(θ₁) A(θ₂).                 (C41.1)
```

Division-free form covers vanishing chambers.  When both chambers carry positive mass and
`θ₁ < θ₂`, inequality is strict.  Equivalently, counter/aligned odds are monotone increasing
under outward exponential tilt.

For the literal CCM prime source, take base exponent `σ > 1` and
`θ₂=σ-1/2`.  Equation `(C41.1)` then says that hard critical reweighting can only increase
counter-phase odds relative to the safe truncated Euler window.

## Paper proof plan

Expand both cross-products as a double sum over counter atom `x` and aligned atom `y`.  Their
common nonnegative coefficient factors out.  Since `x >= L/2 >= y` and `θ₂ >= θ₁`,

```text
θ₂ x + θ₁ y >= θ₁ x + θ₂ y.
```

Monotonicity of `exp` proves every double-sum term.  Strictness follows from one positive pair.

## Scientific consequence

Safe Euler positivity cannot be pushed to the hard CCM first clock by any positive diagonal
half-weight reweighting.  Such reweighting moves mass in the wrong direction: toward the outer
negative half-wave.  Surviving RH attack must use Gamma budget or a genuinely non-diagonal,
phase-bearing source coupling.  This does not prove RH or kill all CCM transports.

## Gates

- [x] corpus audit: positive-transport divergence already known and not being repeated
- [x] generic finite total-positivity theorem
- [x] literal CCM prime-power specialization
- [ ] strict nondegenerate form
- [x] Lean direct check
- [x] targeted module build
- [x] axiom audit and lint

## Lean theorem

`formal/GaloisForLFunctions/RHTower/CCMFirstClockExponentialTiltOdds.lean` proves:

```text
finiteExponentialTilt_separatedOdds_mono
ccmFirstClockPrimeTilt_counterAligned_cross_mono
criticalMellinAtomWeight_mul_halfWeightTilt
ccmFirstClockPrime_critical_counterAlignedOdds_ge_safe
```

The literal capstone is

```text
P_counter(1/2,L) P_aligned(σ,L)
  >= P_counter(σ,L) P_aligned(1/2,L),   σ>=1/2.           (C41.2)
```

Thus the conclusion applies in particular to every safe Euler exponent `σ>1`.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/CCMFirstClockExponentialTiltOdds.lean` — pass
- `lake build GaloisForLFunctions.RHTower.CCMFirstClockExponentialTiltOdds` — pass
  (`9076/9076`)
- capstones use only `propext`, `Classical.choice`, and `Quot.sound`
- `scripts/formal_tools.py lint` — pass
