# HB: source-time integrated characteristic radial flux

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual signed direct-minus-image radial characteristic face,
  integrated over its original causal source-time interval, is bounded by
  `C exp(-T)`, uniformly over nonpositive target tortoise coordinates.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source
→ physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
The full-current target `2 Omega(B(p,p)/2,B(m,m)/2)=0` remains unproved.

## Exact result

Let `s=physicalRate(q,branch)`, `Q=fullSquarePotential q`,
`R=-Delta(Delta-2)`, `K=(7lambda-2-2Delta)/8`, and

```
A=exp(-k) a² thetaAngularCoupling(q,X,k),
thetaAngularCoupling=(KQ)(RQ),
H_s(v)=timeOnset(2s)(v),
u(y)=-tanh(y),
W_s(y)=u(y)⁴(1+u(y))(1+u(y))^(2s).
```

The [previous radial transfer](hb-source-characteristic-radial-flux.md) evaluates
the original four radial faces, with their actual direct-minus-image signs, as

```
F(v,h,x)=A H_s(v) [W_s(-h/2)-W_s(x-h/2)].
```

Define the source-time integral directly from those four original currents:

```
I(T,x)=integral(v=0..T) F(v,T-v,x) dv.
C=|A| 4(4+|2s+5|).
```

For every actual Xi copy, either branch, arbitrary original amplitude and angular
point, `T≥0` and `x≤0`,

```
|I(T,x)| ≤ C exp(-T).
```

The coefficient `C` is independent of `T` and `x`. Consequently
`I(T,x(T))→0` for **every** path `x: real → (-infinity,0]`; no continuity,
boundedness or endpoint condition on the target-radius path is assumed. The
full angular coupling and original smooth onset remain in both the definition
and the bound. Finite-interval integrability is proved separately, so the
theorem does not rely on the zero default of a nonintegrable Bochner integral.

## Closed analytical proof

The first candidate was to integrate the already proved fixed-source-time
limit. A quantitative estimate supplies the missing uniform control instead.
For `w_s(u)=u⁴(1+u)(1+u)^(2s)`, exact differentiation gives

```
w'_s(u)=u³[4+(2s+5)u](1+u)^(2s).
```

The actual source rates satisfy `Re(2s)<-2`. On `[0,1]`, the positive-real-base
complex power therefore has norm at most one, and
`|w'_s(u)|≤4+|2s+5|`. The convex mean-value estimate bounds differences of `w_s`.
The exact corpus identity

```
1-u(y)=exp(2y)(1+u(y))
```

gives `|u(y)-1|≤2 exp(2y)` for `y≤0`. At the two actual characteristics,
`y=-h/2` and `y=x-h/2`, this yields

```
|W_s(-h/2)-W_s(x-h/2)| ≤ 4(4+|2s+5|) exp(-h).
```

The actual smooth cutoff obeys `0≤chi≤1`, so
`|H_s(v)|≤exp(-2v)` for `v≥0`. Substituting `h=T-v` gives
`|F(v,T-v,x)|≤C exp(-T)exp(-v)`. Its integral is at most
`C exp(-T)(1-exp(-T))≤C exp(-T)`.

## Lean scope and validation

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceTimeFlux`.
Namespace: `RHTower.D4BMSourceTimeFlux`.

- `sourceCharacteristicWeight_exp_bound`: uniform exponential delay bound.
- `sourceTimeRadialFlux_integrable`: actual finite source-time integrability.
- `sourceTimeRadialFlux_eq`: exact convolution retaining the angular coupling.
- `sourceTimeRadialFlux_exp_bound`: quantitative source-time integral bound.
- `sourceTimeRadialFlux_tendsto_zero`: decay along any exterior radius path.

Scratch verification used foreground `lake env lean`, including a narrowed
derivative check. The final audit built only this exact leaf in an isolated
path-only environment with 4134 existing own-corpus imports frozen. It passed
without warnings in 145 seconds, reporting three jobs. No dependency, full or
umbrella build ran. The installed source and five olean/ilean/hash/trace
artifacts are byte-identical to the audited files; the new umbrella import is
wired without building it.

Only these five new public theorems were axiom-audited. Each reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. Index refresh and whole-corpus
static lint passed; lint reported existing large-file warnings. No numerical
experiment or computational result was used.

## Search evidence and next direct attack

Broad searches used independently chosen `washout`, `reciprocity`, and
`dominated convergence`; deep queries examined causal convolution, uniform
derivative bounds, and compact boundary traces. Declarations, candidate lemmas,
source proof methods and proposed ingredient sets were inspected. Results were
partial, with stale source entries and mostly source-only compiler metadata.
Generated ingredient sets were not accepted as proofs. The applicable method
here is the convex derivative estimate, checked against the installed Lean
toolchain. The convolution/Laplace and abstract reciprocity hits do not supply
the required full physical cancellation.

A broad `relaxation` search found the August 2026
[Jin–Xin relaxation paper](https://arxiv.org/html/2608.22493v1). Its use of
parameter-uniform stability suggests checking uniformity before taking a limit;
its PDE assumptions do not establish a result for this source. No external
paper is a proof premise here.

The [source-time/radial interchange](hb-source-time-radial-interchange.md) is now
formalized using fractional cutoffs `(1-epsilon)e` on the actual characteristic
intervals. Joint trace continuity includes the zero-delay corner. The exact
time-integrated truncated source transfer converges to this face integral, so
its admitted limit inherits this bound. The single source-time endpoint is not
used to discard a separate temporal contact current.

The complete physical action still requires angular/cusp integration, the
remaining transverse and temporal currents, the actual transposed kernel
action, and independent SS/SV/VV cancellation. This is decay of one retained
current term; fixed Hawking-clock extinction and RH remain unproved. The
frontier map remains read only.
