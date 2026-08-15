# The exact high radial first row is summable by bounded variation

- **ID:** `ccm-exact-high-radial-first-row-bv-bound`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's pole-uniform Bessel and exterior Liouville--Green expansions,
  exact interaction-picture transport, and nonstationary integration by parts
- **Statement:** For the actual constrained prolate source and every
  `k>=lambda^2=c/(2*pi)`, the exact radial Gram entry satisfies
  `|G_lambda(1,k)|<=C*d_1(lambda)/k^2`. Consequently the truncated-divisor weighted high first row
  is `o(d_1)`.

## Setup

Put

```text
U_(lambda,r)(x)=sqrt(lambda*x)q_lambda(lambda*r*x),

G_lambda(1,k)
 =integral_1^infinity U_(lambda,1)(x)U_(lambda,k)(x)dx/x,

c=2*pi*lambda^2.                                                (1)
```

The constrained `m=4` exterior mode carries the `sqrt(d_1)` scale. The `m=0` mode and its cross
term are smaller and obey the same estimates after their deficit factor is inserted.

## Exterior phase for the high factor

For `k>=lambda^2` and `x>=1`, one has `k*x>=lambda^2>2` for large `lambda`. Dunster's Section 2
Liouville--Green expansion therefore gives the exact phase-preserving representation

```text
U_(lambda,k)(x)
 =sqrt(d_1)/k sum_(epsilon in {+1,-1})
   exp(i*epsilon*c*xi_c(k*x))a_(epsilon,c,k)(x),                 (2)
```

where

```text
|a_(epsilon,c,k)(x)|<=C*x^(-1/2),
|d/dx a_(epsilon,c,k)(x)|<=C*x^(-3/2).                           (3)
```

The differentiated bounds include the exact remainder by
`radial-pswf-interaction-picture-transport.md`: the Liouville-transformed equation gives exact
amplitude derivatives proportional to `psi/c`, and Dunster's exterior potential is uniformly
short-range. This avoids the unjustified step of treating an additive Olver remainder as a
relative oscillatory remainder. The phase satisfies

```text
Phi_(epsilon,k)'(x)
 =epsilon*c*k*sqrt((k^2*x^2-sigma_4(c)^2)/(k^2*x^2-1)),

|Phi_(epsilon,k)'(x)|>=c_0*c*k,                                 (4)
```

and

```text
|d/dx[1/Phi_(epsilon,k)'(x)]|<=C/(c*k*x^2).                     (5)
```

## Bounded-variation lemma for the pole factor

For either amplitude in `(2)`, define

```text
V_(epsilon,c,k)(x)
 =U_(lambda,1)(x)a_(epsilon,c,k)(x)/x.                           (6)
```

`[PROVED HERE]` Dunster's Section 3 pole-uniform Bessel formula and its differentiated Olver bound
give

```text
|V_(epsilon,c,k)(1)|
 +integral_1^infinity |V_(epsilon,c,k)'(x)|dx
 <=C*sqrt(d_1)*c.                                               (7)
```

To verify `(7)`, write the normalized first factor as

```text
U_(lambda,1)(x)/sqrt(d_1)
 =A_c(x){J_0(c*xi_c(x))+c^(-1)E_c(x)},                           (8)
```

where `A_c(x)=O(x^(-1/2))`, `A_c'(x)=O(x^(-3/2))`, and the error and its derivative obey the
corresponding Bessel-envelope bounds in the analytic endpoint coordinate `eta=xi_c^2`.

On the endpoint interval `c^2*(x-1)<=1`, the analytic coordinate gives total variation `O(1)`.
On its complement, use the Bessel symbol estimates

```text
|J_0(u)|<=C*u^(-1/2),
|J_0'(u)|<=C*u^(-1/2),                                         (9)
```

and `xi_c'(x)=O(x/sqrt(x^2-1))`. After multiplication by the factor
`a_(epsilon,c,k)(x)/x=O(x^(-3/2))`, the phase derivative term is bounded by an integrable envelope
whose integral is `O(c)`. The differentiated Olver error has an extra `c^(-1)` and is smaller.
The far boundary is zero. This proves `(7)`.

## High-index integration by parts

Insert `(2)` into `(1).` For each sign, integration by parts gives

```text
integral_1^infinity V_(epsilon,c,k)(x)
  exp(i*Phi_(epsilon,k)(x))dx

 =-[V_(epsilon,c,k)(1)exp(i*Phi_(epsilon,k)(1))]
     /(i*Phi_(epsilon,k)'(1))
   -integral_1^infinity exp(i*Phi_(epsilon,k)(x))
      d/dx[V_(epsilon,c,k)(x)/(i*Phi_(epsilon,k)'(x))]dx.        (10)
```

Equations `(4)`--`(7)` bound `(10)` by

```text
C*sqrt(d_1)/k.                                                  (11)
```

The outside factor `sqrt(d_1)/k` in `(2)` therefore proves

```text
|G_lambda(1,k)|<=C*d_1/k^2,
k>=lambda^2.                                                    (12)
```

## Truncated-divisor tail

Let

```text
a_lambda(k)=sum_(q|k; q<=lambda^2)Lambda(q).
```

The divisor identity gives `0<=a_lambda(k)<=log k`. Hence `(12)` implies

```text
sum_(k>lambda^2)a_lambda(k)|G_lambda(1,k)|
 <=C*d_1 sum_(k>lambda^2)log(k)/k^2
 =O(d_1*log(lambda)/lambda^2)
 =o(d_1).                                                       (13)
```

Together with `ccm-exact-finite-aperture-first-row-vanishing.md`, equation `(13)` closes the full
truncated-divisor weighted first row.

## Route consequence

The exact prime-shift cutoff and infinite radial multiplier are now both respected:

```text
low radial row k<=lambda^2: pole-uniform stationary estimate,
high radial row k>lambda^2: exterior phase + BV estimate.        (14)
```

Thus the high radial divisor tail identified in
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-prime-shift-radial-index-separation-law.md`
vanishes at the leakage scale.

## Novelty and significance verdict

The theorem is a source-specific but standard nonstationary-phase argument using Dunster's
published expansions. It repairs the CCM route but does not clear the parent-theory novelty gate;
it is classified as a bridge.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699, Sections 2
  and 3.
- F. W. J. Olver, *Asymptotics and Special Functions*, the Liouville--Green and Bessel error
  theorems used by Dunster.
- `radial-pswf-interaction-picture-transport.md`, exact ODE transport and Lean formalization.

## Lean decision (superseded)

At the time this card was written the formal tree had no Bessel-envelope bounded-variation or
nonstationary integration interface, so no Lean file was added.  Both interfaces now exist; see the
Lean progress section at the end of this card.

## Gates

- [x] high radial factor placed in the exterior oscillatory regime
- [x] pole-factor weighted BV bound proved
- [x] exact `k^(-2)` high first-row estimate proved
- [x] truncated-divisor weighted high tail summed

## Lean progress — the whole estimate is formal

The "Lean decision" above is stale.  The formal tree now has both interfaces it said were missing:
the nonstationary integration interface (`HTGeometry/NonstationaryPhaseLowerBound.lean`,
`HTGeometry/TwoPhaseOscillatoryProduct.lean`) and the exterior dilated-phase layer
(`RHTower/RadialDilatedPhaseSeparation.lean`, `RHTower/RadialTwoIndexOscillatoryBound.lean`).

`GaloisForLFunctions/RHTower/CCMHighRadialFirstRowBV.lean` (wired, axiom-clean) proves the card end
to end, with every constant absolute:

```text
BVWeight a b B V V'
    the card's `(7)`: a weight with endpoint-plus-total-variation budget
      |V a| + |V b| + ∫_a^b |V′| ≤ B

integral_one_div_mul_sqrt_le          ∫_a^b x^{-3/2} ≤ 2/√a
integral_one_div_sq_le'               ∫_a^b x^{-2}   ≤ 1/a
    the two exterior power integrals, by explicit antiderivatives

bvWeight_of_symbol   (1 ≤ a ≤ b)
    |V| ≤ P/(x√x)  and  |V′| ≤ P′/x²   ⟹   BVWeight a b (2P + P′) V V'  and  ∫|V| ≤ 2P

firstRowWeight_symbol_bounds   (1 ≤ x)
    the card's `(6)` and `(3)`: for `V = U·A/x` with
      |U| ≤ Q/√x, |U′| ≤ Q′/√x,  |A| ≤ R/√x, |A′| ≤ R′/(x√x)
    one has
      |V| ≤ QR/(x√x)   and   |V′| ≤ (Q′R + QR′ + QR)/x²
    so the first-row weight is exactly in the symbol class of `bvWeight_of_symbol`;
    `Q′` is where the bandwidth of the first factor's own oscillation enters, and it is the
    only place a power of `c` appears

integral_abs_mul_dilatedRadialPhaseAccel_le   (0 ≤ s ≤ 1/2, 2 ≤ r, 1 ≤ a ≤ b)
    ∫_a^b |V| |ξ″| ≤ 16 B₁/(9 r)      from |ξ″| ≤ (16/9)/(r x³) ≤ (16/9)/r

abs_integral_highRadial_firstRow_le   (0 ≤ s ≤ 1/2, 2 ≤ r, 0 < c, 1 ≤ a ≤ b)
    |∫_a^b V(x) cos(c ξ_s(r x) + φ) dx| ≤ (B/r + 16 B₁/(9 r³))/c        -- `(10)`,`(4)`,`(5)`

abs_setIntegral_Ioi_highRadial_firstRow_le
    the same on the exterior ray `(1,∞)`, because the bound is uniform in the right endpoint

summable_highRadial_logMajorant       Σ log(k+2)/(k+2)² converges
tsum_weighted_highRadial_le           Σ_{k ≥ N} a(k)|G(1,k)| ≤ C d Σ_{k ≥ N} log k/k²
tendsto_tsum_log_shift_div_sq_tail    those tails tend to zero                     -- `(13)`
```

The mechanism is the card's own: the exterior phase `c ξ_s(r x)` has speed at least `c r`
(`le_dilatedPhaseSpeed`) and curvature at most `(16/9)/(r x³)`
(`abs_dilatedRadialPhaseAccel_le`), so one integration by parts against the oscillation costs a
factor `1/(c r)` and returns the endpoint-plus-variation budget of the weight, exactly `(10)`.
With `B = O(√d₁ c)` from `(7)` — the composition bound above with `Q′ = O(c)` — the entry is
`O(√d₁/r)`, and the outer `√d₁/r` normalization of the exterior expansion `(2)` turns it into
`(12)`: `|G_λ(1,k)| ≤ C d₁/k²`.  Summing against `0 ≤ a_λ(k) ≤ log k` gives `(13)`.

`#print axioms` on every declaration of the module returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Gates — Lean

- [x] the bounded-variation budget `(7)` as an interface, with its half-power symbol discharge
- [x] the two-factor composition `(3)`/`(6)` of the first-row weight
- [x] the integration by parts `(10)` with the phase lower bound `(4)` and curvature `(5)`
- [x] the exterior-ray form of the estimate
- [x] the truncated-divisor weighted high tail `(13)` and its vanishing
- [ ] the endpoint layer of `(7)` for the *actual* first factor: on `c²(x−1) ≤ 1` the Bessel
  amplitude has the `(x−1)^{-1/4}` singularity, so the half-power symbol bound
  `|U| ≤ Q/√x` used by `firstRowWeight_symbol_bounds` does not hold there and the analytic
  coordinate `η = ξ_c²` must be used instead.  Everything on the complement is discharged.

### Residue

What the module does **not** yet do is name the corpus's concrete first-row factor as the `U` of
`firstRowWeight_symbol_bounds`.  Away from the endpoint layer the two inputs it needs are already
corpus-owned — the Liouville–Green amplitude bounds `abs_xiAmplitude_le_four`,
`abs_xiAmplitudeDeriv_le` (`RHTower/XiAmplitudeDecay.lean`) and the exterior symbol record
`symbolTwoBranch_radialPSWF` (`RHTower/RadialSymbolTwoBranchBound.lean`) — so the missing step is
exactly the endpoint layer, where `RHTower/CCMRadialProlateEndpointLayer.lean` and
`RHTower/CCMFirstRowEnvelopeTail.lean` already carry the `(x−1)^{-1/4}` analysis used by the *low*
first row.
