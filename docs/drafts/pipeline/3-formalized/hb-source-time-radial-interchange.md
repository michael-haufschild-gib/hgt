# HB: source-time and radial characteristic interchange

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The source-time integral of the actual truncated radial Green
  transfer converges to the original signed characteristic face integral.
  Its admitted limit has the uniform `C exp(-T)` bound.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source
→ physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Complete physical-current cancellation `2 Omega(B(p,p)/2,B(m,m)/2)=0` and RH
remain unproved.

## Original-source limit theorem

Fix an actual Xi copy, either branch, the original amplitude, angular point
`(X,k)`, target ingoing time `T≥0` and target tortoise coordinate `x<0`.
At source time `v`, let `h=T-v` and

```
e_d=x-h/2,       e_i=-h/2,
cut_d=(1-epsilon)e_d,   cut_i=(1-epsilon)e_i.
```

Use the original `radialTransferDensity` from the
[full source Green transfer](hb-common-source-green-transfer.md):

```
D = mu[(P F)G-F(P_dagger G)]-partial_X J_X-partial_k J_k.
```

Both angular divergences remain. `F` is the literal theta seed with its actual
onset and physical branch rate; `G` is the native kernel with the full retained
spin-two weight. Define

```
A_epsilon(T,x) = integral(v=0..T) [
  integral(y=cut_d..0) D_direct(v,T-v,x,y) dy
 -integral(y=cut_i..0) D_image(v,T-v,x,y) dy ] dv.
```

The exact formal result is

```
lim(epsilon→0+) A_epsilon(T,x) = sourceTimeRadialFlux(T,x).
```

The right side is defined from the original four radial current faces. Its
[previously proved bound](hb-source-time-radial-flux.md) therefore controls the
admitted original radial transfer:

```
|lim(epsilon→0+) A_epsilon(T,x)| ≤ C exp(-T),
C = |exp(-k) a² thetaAngularCoupling(q,X,k)|
      *4*(4+|2 physicalRate(q,branch)+5|).
```

This limit tends to zero along every path `x: real → (-infinity,0)` as `T→infinity`.
The constant is independent of target radius and target time. The order is
radial admission at each fixed time, followed by the late-time limit; no
uniform-in-time cutoff-error estimate is asserted.

## Closed proof

The successful conjecture scales each characteristic interval by its own length.
For `v<T` and `0<epsilon<1/2`, the fractional cutoff is strictly between `e` and
zero. The already formalized radial fundamental theorem identifies each inner
integral with minus the original radial trace at that cutoff.

On the closed rectangle `v in [0,T], epsilon in [0,1/2]`, the causal invariant is
at least one. The native spin-two trace equals the actual smooth circle
spin-two field evaluated at `arcosh(invariant)`. Continuity of this composition
includes invariant one and the zero-delay corner. The actual seed factorizes
into its smooth radial amplitude, original smooth onset and fixed angular
coefficient. These facts prove joint continuity of the original cutoff current;
no trace regularity is assumed.

Clamping the two parameters to that rectangle supplies a continuous extension
on the full parameter plane. Its fixed-interval source-time integral is
continuous by the installed parametric-integral theorem. For every interior
source time, the extension equals the original radial transfer after the exact
radial Green integration. Equality on the open source-time interval proves
finite-interval integrability and equality of the integrals. At cutoff zero,
the extension integrates to the original signed radial face. Thus continuity
gives the stated right-hand limit.

The source-time endpoint `v=T` is excluded only from the almost-everywhere
interior identity. Its trace is retained in the joint continuity proof. This
argument makes no claim that a separate temporal contact current vanishes.
The quantitative bound and moving-radius limit follow from the previously
proved source-time face theorem. Every use of `limUnder` is justified by the
newly proved limit, rather than by its default value.

## Exact Lean scope

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonSourceGreen` adds
`RHTower.D4BMCommonSourceGreen.sourceCutoffTrace_continuousOn`, with the actual
fractional cutoff and original trace as public definitions. Every previously
audited declaration is byte-for-byte unchanged.

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceTimeInterchange` provides,
in namespace `RHTower.D4BMSourceTimeInterchange`:

- `sourceTimeTruncatedTransfer_integrable`: genuine source-time integrability
  for each interior fractional cutoff.
- `sourceTimeTruncatedTransfer_tendsto`: exact original-source interchange.
- `sourceTimeTruncatedTransfer_limit_bound`: uniform `C exp(-T)` estimate.
- `sourceTimeTruncatedTransfer_limit_tendsto_zero`: decay of the admitted
  transfer along every exterior target-radius path.

Scratch checks passed with foreground `lake env lean`. Final audits built only
the two exact changed leaves, sequentially: the common-source extension passed
in 25 seconds and the new interchange leaf in 20 seconds, three jobs each,
without warnings. Existing imports were frozen in a path-only audit environment;
no old dependency, full or umbrella build ran. Both installed sources and ten
olean/ilean/hash/trace artifacts are byte-identical to the audited files.
The new leaf is wired into the umbrella without building it.

Only these five new public theorems were axiom-audited. All report exactly
`propext`, `Classical.choice`, and `Quot.sound`. Index refresh and whole-corpus
static lint passed, with existing large-file warnings. No computation or
external paper premise was used.

## Search evidence and remaining physical target

Broad `uniformity` and `parametric` searches and mechanism-directed deep searches
covered joint traces and clamped rectangle extensions. Candidate lemmas,
source proof methods and proposed ingredient sets were inspected. Results were
partial, with 330–333 stale source entries and mostly source-only compiler
metadata. The `parametric` search located the exact installed
`intervalIntegral.continuous_parametric_primitive_of_continuous` theorem and
existing clamped-integral proof methods; applicability was checked in Lean.
Generated ingredient groups were not treated as proofs. A broad `gluing`
literature search also examined the August 2026
[graph causal transport paper](https://arxiv.org/html/2608.13716v1); it supplies
no premise for this native-kernel argument.

The remaining hard task is the complete physical-current pairing: angular/cusp
integration of the retained currents, temporal and transverse current transport,
the actual transposed kernel action and independent SS/SV/VV coefficients.
The radial/source-time interchange is closed; full fixed Hawking-clock
extinction is not. Frontier map remains read only.
