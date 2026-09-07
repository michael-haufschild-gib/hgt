# HB smooth interior response

Stage: formalized in Lean 4; final leaf and axiom audits passed. Type: `[BRIDGE]`. RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

The actual response to the complete original cusp-subtracted forcing now has a
constructed smooth representative throughout the open modular cell. It equals the
original response in the native modular L² measure. Both original completed
gradients also have smooth interior representatives. No smoothness, source
regularity, Fourier reconstruction, or compatibility hypothesis is supplied to
the final actual-response theorems.

## Literal forcing and every localized order

Write h for the previously constructed weak response, J for its scalar projection,
D_i h for its original two completed frame derivatives, and F for the full original
forcing. The prior actual equation and complete cutoff commutator are proved in
[interior elliptic regularity](hb-interior-elliptic-regularity.md).

The literal cusp-power response, smooth height cutoff, and retained full scalar
square make F smooth on the positive-height chart. This includes both derivatives
of the cutoff response; no forcing term is discarded. For every smooth compact
interior test g, gF has a smooth compact zero extension to the plane. Exact native
measure transport identifies g times the original L² forcing vector with this
field almost everywhere. Hence its actual localized distribution is represented
by a Schwartz function and has every real Sobolev order.

## Bootstrap through height-weighted tests

Let T(g,u) denote the actual planar distribution represented by g times u.
The completed first-derivative identity applied to the actual compact test yg gives

`T(g,D_i h) = partial_i T(yg,Jh) - T(partial_i(yg),Jh)`.

Cancellation of y is justified by positive height on the test support, with zero
extension elsewhere. Therefore all scalar localizations in H^s give all original
gradient localizations in H^(s-1). Every coefficient on the right of the full
cutoff equation is itself an admissible interior test:

```
Delta_E T(g,Jh)
  = sum_i T(partial_i² g,Jh)
    + 2*sum_i T((partial_i g)/y,D_i h)
    + L*T(g/y²,Jh) + T(g/y²,F).
```

Thus its entire right side lies in H^(s-1). The proved planar two-derivative gain
yields scalar order s+1. Induction from the actual H² theorem proves every
nonnegative integer order for every scalar localization. The height-weighted
identity then gives every integer order for the original completed gradients.
This proof requires no additional general Sobolev multiplication theorem.

## Smooth Fourier reconstruction

A planar tempered distribution u in every integer Sobolev order has a single
Fourier representative v in L¹. For each integer m, the Bessel potential B_(2m)u
also has Sobolev order two, so its Fourier transform has an L¹ representative w_m.
The exact Bessel multiplier identity gives

`distribution(w_m) = (1+|xi|²)^m * distribution(v)`.

The weighted density on the right is locally integrable. Pairing this identity
against compact smooth tests proves actual almost-everywhere equality of the
densities. Consequently `(1+|xi|²)^m*v` is integrable. The elementary domination
`|xi|^n <= (1+|xi|²)^n` supplies every integrable polynomial moment of v.

The actual inverse Fourier integral f of v is smooth to every order. Fourier
inversion in distributions and the L¹ Fourier duality formula identify f with the
original L² class by smooth-test separation. No pointwise Fourier inversion or
pre-existing smooth representative is assumed.

## Gluing and native identification

For each compact interior test g, choose the constructed smooth representative R_g
of T(g,Jh). Almost-everywhere equality and continuity give the pointwise overlap law

`g*R_k = k*R_g`.

Actual compact smooth tests are nonzero at every point of the open cell. Their
local quotients R_g/g therefore define one smooth field there. A countable open
subcover proves its almost-everywhere planar equality to the original response.
The native measure's exact planar density transports this equality back to the
original Hilbert space. The modular seams have proved zero native measure, so the
field represents the full original angular L² class. Zero measure of seams does
not prove smooth matching across them.

## Lean surface and validation

| Module | New public theorems | Exact surface |
|---|---:|---|
| `RHTower.ThetaCuspHawkingBMForcingRegularity` | 5 | Literal full forcing C∞, exact localized source identification, every Sobolev order |
| `RHTower.ThetaCuspHawkingBMInteriorSobolevBootstrap` | 5 | Original gradient recovery, actual scalar and gradient regularity at every integer order |
| `HTGeometry.PlanarSobolevSmoothRepresentative` | 2 | Every Fourier moment and smooth reconstruction of the original planar L² class |
| `RHTower.ThetaCuspHawkingBMInteriorSmoothResponse` | 8 | Actual local representatives, pointwise overlap gluing, interior smoothness and native a.e. identification |

All four development scratch modules passed `lake env lean`. The four canonical
leaves passed individual `lake build <module>` audits in a cache-only package:
13s, 4.9s, 2.9s and 18s in table order. Only the four new leaves compiled; cached
dependencies have no source-library targets in the audit package. Audited source
bytes match the canonical files. Exactly eight new olean/ilean artifacts are
installed, and each new leaf is wired once into its theorem-area umbrella.
No umbrella or full build ran.

One scratch `lake env lean` audit checked exactly these 20 new public theorem
axiom sets, once. All contain only `propext`, `Classical.choice` and `Quot.sound`;
there were no diagnostics. Earlier theorem batches were not re-audited. No added
axioms, proof gaps, numerical certificates or numerical experiments are used.
Scoped source whitespace checks passed.

The generated source index was refreshed once. The final global
`lint --check-generated` reports an unrelated missing umbrella import for
`RHTower.PNTTailLogMoment` and stale `LEAN_API.md`, `LEAN_GAPS.md`, and
`LEAN_OVERVIEW.md` during concurrent source edits. It reports no errors in these
four new leaves. Global lint is therefore not claimed to pass.

## Remaining bridge

Extend the actual differential equation and smooth response across modular side
identifications and stabilizer charts. Construct the global cusp-cutoff extension
and assemble the full angular field. Then prove physical causal admission,
horizon and radial boundary conditions, gauge conditions, and the original
left-QNM pairing. The SS/VV sectors and independent fixed Hawking-clock extinction
remain open. Interior smoothness establishes none of these remaining physical
conclusions and does not close RH.
