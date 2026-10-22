# CCM first-clock apex-superlevel majorization

- **ID:** `ccm-first-clock-apex-superlevel-majorization`
- **Stage:** 5-failed
- **Type:** RETIRED STRONG RH PREDECESSOR / ATOMIC-APEX NO-GO
- **Scientific status:** `[FORMALLY FALSIFIED] [KNOWN CORPUS SPECIALIZATION] [NO COMPUTATION]`
- **Parent:** `../3-formalized/not_new_scientific_knowledge/ccm-first-clock-prime-power-tower-collapse.md`
- **Endpoint:** `CCMFirstClockReducedTowerDominance`

## Frontier

Prime-power tower collapse proves all local composite interference nonnegative except finite
two-mode anomalies at `p=2,3`. Cofinal negative mass is exactly exponent-one outer primes.
Dirichlet-convolution, diagonal tilt, and one-prime power-dilation mechanisms cannot mix this face.

Need genuinely cross-prime or prime--Gamma order.

## Apex amplitude distributions

For `L>0`, define first-half-wave amplitude

```text
a_L(h)=max(sin(2*pi*h/L),0).
```

Put continuous Gamma--polar reflection density on `0<h<=L/2`:

```text
d nu_L(h)
 =1_(0,L/2](h)
  [rho_cont(h)-rho_cont(h+L/2)] dh.
```

Put finite prime amplitude measures

```text
alpha_L
 =sum_(2<=k<=exp L) w_k delta_(max(sin(2*pi*log k/L),0)),

beta_L
 =sum_(2<=k<=exp L) w_k delta_(max(-sin(2*pi*log k/L),0)),

w_k=Lambda(k)/sqrt(k).
```

Push `nu_L` forward by `a_L` and set

```text
Good_L=(a_L)_*nu_L+alpha_L,
Bad_L=beta_L.
```

Their first moments are exactly

```text
int x d Good_L
 =continuousHalfWaveBudget(L)+primeAlignedMass(L),

int x d Bad_L
 =primeCounterMass(L).
```

Tower collapse gives an equivalent reduced form whose only cofinal bad source is outer primes.

## Strong predecessor

Define closed apex-superlevel majorization:

```text
for every L>=pi/2 and every t>0,
  Bad_L([t,infinity)) <= Good_L([t,infinity)).           (ASM)
```

By layer-cake,

```text
int x d Bad_L
 =int_(t>0) Bad_L((t,infinity)) dt
 <=int_(t>0) Good_L((t,infinity)) dt
 =int x d Good_L.
```

Therefore

```text
(ASM) -> CCMFirstClockPrimeHalfWaveDominance -> RH.
```

Since `a_L` is symmetric and strictly decreases with distance from `L/4`, `(ASM)` says that at
every amplitude level the completed good source has at least as much mass in the centered
first-half-wave window as the counter-prime source. This is a transport/concentration order, not
the scalar RH-equivalent moment inequality.

## Why route was worth testing

1. It replaces one oscillatory integral by nested positive superlevel inequalities.
2. Superlevels form one centered interval family; no arbitrary test class is required.
3. It is stable under adding any positive source component.
4. It is genuinely cross-prime--Gamma: outer prime atoms are compared to one continuous completed
   source plus all aligned towers at same amplitude threshold.
5. It is strictly stronger than RH unless source geometry forces tail-order saturation.

## Exact falsification

Set

```text
L_*=(8/3) log 2.
```

Then `L_*>=pi/2`, the prime power `k=4` lies inside the aperture, and

```text
(2*pi/L_*) log 4 = 3*pi/2.
```

Thus `Bad_(L_*)` has a strictly positive atom at amplitude `1`, with weight
`Lambda(4)/sqrt(4)>0`.

The good side has zero mass at amplitude `1`:

1. the continuous amplitude map reaches `1` only at `h=L_*/4`, a Lebesgue-null singleton;
2. an aligned integer atom at amplitude `1` would force
   `log k=(2/3)log 2`, hence `k^3=4`, impossible for integer `k>=2`.

Therefore

```text
0 < Bad_(L_*)({1})  and  Good_(L_*)({1})=0,
```

so `(ASM)` is false.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockApexSuperlevelMajorization.lean`.

Key declarations:

- `ccmFirstClockApexSuperlevelMajorization_implies_rh`;
- `ccmFirstClockBadApexMeasure_closedApex_pos`;
- `ccmFirstClockGoodApexMeasure_closedApex_eq_zero`;
- `not_ccmFirstClockApexSuperlevelMajorization`.

Direct check:

```text
lake env lean GaloisForLFunctions/RHTower/CCM/CCMFirstClockApexSuperlevelMajorization.lean
```

passes.

## Hostile audit

- [x] no scalar/Dirichlet convolution transport
- [x] no diagonal exponential de-Abelization
- [x] no discarded prime powers
- [x] no numerical evidence
- [x] define exact source measures in Lean
- [x] prove first-moment identities
- [x] prove `(ASM) -> RH` by layer-cake
- [x] determine whether `(ASM)` is already false from exact source structure
- [x] formalize exact atomic counterexample
- [ ] determine whether an atom-aware replacement law survives

## Falsifiers

Falsifier occurred exactly at `(L_*,t) = ((8/3)log 2,1)`.

## Strongest positive survivor

`ATOMIC-APEX OBSTRUCTION`: any universal source law demanding raw closed-superlevel domination
from an atomless continuous good component fails whenever a counter-phased prime power lands at
amplitude `1` and no aligned integer atom shares that apex.  Viable replacements must expose and
absorb discrete counter-apex atoms explicitly; smoothing or renaming the scalar first moment is
not enough.

## Corpus-collision audit

This obstruction is **not new scientific knowledge**.  The earlier
`SuzukiMangoldtApexLock.lean` development and
`suzuki-mangoldt-apex-lock-rigidity.md` card already prove the same stronger mechanism:
cofinal powers of two lock to unique Suzuki apices, the dominating continuous superlevel is null,
and the Mangoldt atom is positive.  The CCM theorem above is only a first-clock specialization and
an exact connector to the reduced half-wave endpoint.

No novelty claim survives.  Any successor must start beyond the existing Suzuki apex-lock theorem,
not repackage its atomic/null-set obstruction.
