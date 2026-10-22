# HB: elementary fundamental modes and complete radial source moment

Status: formalized and individually audited. RH remains unproved.

For both original fundamental frequencies `w=-3/2 ± i chi`, with nonzero
imaginary part, the actual horizon and normalizable modes coincide:

```text
H(z)=N(z)=Psi_w(z)=z^(w/2) sqrt(1-z),  0<z<1.
```

The equality includes the original normalization. One outer Gauss
parameter is zero, so every positive-degree series coefficient vanishes.
The existing original horizon-basis representation gives `N=A H+B H_opposite`.
Its actual opposite coefficient is `B=connection/(2w)=0`. Canceling the
nonzero horizon power and taking the endpoint limit of the remaining
Gauss multiplier gives `A=1`. No normalization coefficient is assigned.

## Elementary full source

At these frequencies the original unit-source gradient is

```text
K=(w+1)(w+2)/2-(s+1)(s+2).
```

Define the elementary core, using the original source amplitude a,

```text
F(z)=sqrt(1-z) (1+sqrt(1-z))^(2s-w) a^2
     [(5s^2+15s+4)/4
      +(1-z)s(s-1)/4 ((s+2)^2+(s+1)(s+2)-(w+1)(w+2)/2)].
```

Lean's `fundamentalSourceCore` uses the existing literal
`sourceRemainder` with this derived K. The native horizon Mellin core
equals F on `0<=z<1`. The original outer source integrand equals `z^w F(z)`
through its endpoint z=1.

For `Re(w)>-2`, the source has one absolutely convergent subtracted moment:

```text
M(w,s,a)=F(0)/(w+1)+integral_0^1 z^w [F(z)-F(0)] dz.
```

Nonreal w excludes `w=-1`. The near-horizon absolute bound comes from
the original source's first-remainder estimate. Continuity of F and of
the power on the positive compact interval admits the remaining tail.
This is the first-subtracted Mellin finite part; it is not identified
with a divergent unsubtracted Lebesgue integral.

The definition initially splits at z=1/2, retaining the native Mellin
subtraction and outer integral. Exact integration of the constant-core
power on [1/2,1] joins those pieces into the displayed full-endpoint
formula. `physicalFundamentalSourceMoment_integral` gives both absolute
admission and that formula for every actual Xi copy and both source and
frequency branches, without supplied strip or endpoint premises.

## Complete response and observation independence

The original moving horizon moment has derivative `z^w F(z)`; the
original outer integral has the negative of the same derivative. Their
sum is therefore independent of its interior splitting point.

With `b=horizonCoordinate(t)`, t<0, and the original onset factor
`S(s,w)=clearedOnset s w`, Lean proves

```text
clearedReducedGreen(w,chi,s,a,t)=Psi_w(b) M(w,s,a) S(s,w).

physicalSelfResidueCoefficient(t)
  =Psi_w(b) A_eff M(w,s,a) S(s,w)/E'(w).
```

Both factors of Psi are nonzero at every interior point. The denominator
slope was already proved nonzero. Thus an actual fundamental pole is
present at every interior detector exactly when it is present at one.
Its precise source criterion is `A_eff!=0`, `M!=0`, and `S!=0`.

On strict-right Xi copies, the already evaluated angular coefficient
replaces its first condition by nonvanishing of
`xi(5rho/2-1)`, `xi(rho/2)`, and `xi(3rho/2)`. The radial moment and the
literal temporal onset factor remain separate obligations. Neither is
declared nonzero. These are pointwise interior residue statements for
the continuation of the original response; no Hilbert-class QNM
continuation or physical retarded/advanced adjoint identification is added.

## Modules and validation

Five leaves under `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBM`:

- `FundamentalRadialModes`: original elementary modes and exact normalization.
- `FundamentalSourceMoment`: original-to-elementary source identities.
- `FundamentalGreenFactor`: exact spatial factorization and zero criterion.
- `FundamentalMomentEndpoint`: absolute admission and full-endpoint formula.
- `PhysicalFundamentalMoment`: actual Xi residue and detector-independent pole criteria.

The leaves contain 25 public theorems and two definitions in 460 lines;
the largest leaf has 119 lines. Each scratch check used `lake env lean`.
Each final audit used `lake build` with exactly one of the five listed
leaf modules; all five passed without warnings. Only the 27 new public
declarations were checked with `#print axioms` in a scratch file. Their
axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

All 15 installed source, object, and interface artifacts matched their
audited hashes. Each leaf has one umbrella import. Index generation,
`scripts/formal_tools.py lint --check-generated`, and `git diff --check`
passed; lint retained the 141 existing large-file warnings. No full or
umbrella build and no numerical experiment was run. The frontier map's
hash remained unchanged during this work.

Remaining: evaluate or control this literal finite-part moment and onset
factor together with the angular incidences; identify the physical
adjoint residue; complete spin-two/AIME reconstruction; prove independent
Hawking-clock extinction. None of those obligations is discharged by
the mode factorization.
