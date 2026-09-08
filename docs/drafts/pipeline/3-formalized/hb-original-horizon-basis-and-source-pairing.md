# HB: original horizon basis and physical radial source pairing

- **Stage:** formalized in Lean 4 after the audit recorded below.
- **RH:** unproved. The full original joint outgoing inverse and physical advanced/adjoint source projection remain open.
- **Result:** the actual original horizon solutions form a basis at every nonreal frequency; the fixed horizon domain classifies every homogeneous solution; the normalizable solution meets that domain exactly at zeros of its original connection coefficient; actual forced boundary phases obey the original source integral.

## Exact operator and normalization

Write `L_w U` for the original normalized BM radial operator, with actual derivatives:

```text
L_w U = b(1-b) U'' + (1-3b/2) U'
        + [-w²/(4b) - (1/4+chi²)/4] U.
p(b) = b sqrt(1-b).
B(U,V) = p(b) [U V' - U' V].
rho(b) = sqrt(1-b)/(1-b).
```

The full metric-wave normalization and this radial normalization are distinct;
`rho` is derived from the displayed `L_w`, rather than assigned as a source
weight. All statements below concern the interval `0<b<1`. Jet hypotheses in
the general theorems are `HasDerivAt` statements, so their jets are actual
spatial derivatives.

## Dependency-closed proof

1. Differentiate the physical bracket with the actual product rule. The
   potential terms cancel in `U L_w V-V L_w U`. The remaining second- and
   first-derivative coefficients give exactly
   `B(U,V)'=rho*(U L_w V-V L_w U)`. Neither an endpoint condition nor a supplied
   adjoint pairing is used. When both actual equations vanish, this derivative
   is zero. Connectedness of the interior interval makes the bracket constant.
2. Both `H(w)` and `H(-w)` solve the same original radial equation: its
   frequency dependence is through `w²`. Their actual derivatives are already
   proved throughout the radial disk. Cancel the two opposite physical powers
   in their bracket. If `F_w` is the undressed Gauss factor, the result is
   `sqrt(1-b)[-w F_w F_-w+b(F_w F'_-w-F'_w F_-w)]`.
   The actual Gauss factors and their derivatives are continuous at zero and
   `F_w(0)=F_-w(0)=1`. Thus the bracket tends to `-w` at the horizon; Abel
   constancy proves `B(H(w),H(-w))=-w` throughout the interior.
3. Nonreal frequency implies `w!=0`. For any actual homogeneous solution U,
   define its coefficients from the actual jets at the fixed point `b=1/2`:
   `A=B(U,H(-w))/(-w)` and `B=B(H(w),U)/(-w)`.
   Both brackets are constant by step 1. At every interior point the determinant
   from step 2 gives exactly `U=A H(w)+B H(-w)` and the corresponding derivative
   formula. This proves representation for every actual homogeneous solution;
   it is no longer an assumption that U belongs to the two-branch family.
4. The previously proved C² positive-germ criterion excludes the stripped
   opposite power `b^(-w)` for nonreal `w` with `Re w>-2`. Equality on the whole
   interior interval supplies equality of positive-side germs after stripping.
   Hence `OriginalHorizonC2 w U` is exactly `B=0` for every actual homogeneous U.
5. For the actual normalizable solution N, the previously proved continued
   physical Wronskian is `B(H(w),N)=-connection(w,chi)/2`. Its opposite coefficient
   is therefore exactly `connection(w,chi)/(2w)`. Step 4 gives
   `OriginalHorizonC2 w N iff connection(w,chi)=0` throughout the same strip.
   At the two literal fundamental frequencies `w=-3/2 +/- i chi`, one of the
   actual Gamma denominator arguments is zero. The totalized original
   connection coefficient is consequently zero. The strict Xi strip supplies
   the frequency domain at both fundamental QNMs of every Xi copy, with the
   correct physical angular parameter `chi=z/2+i/4`.
6. If `L_w U=F`, step 1 with first solution `H(w)` gives
   `B(H(w),U)'=rho H(w) F`. On any compact interior interval `[a,b]`, continuity
   of the actual forcing and the already differentiated horizon solution makes
   this integrand integrable. The Bochner fundamental theorem then proves
   `integral_a^b rho H(w) F = B(H(w),U)(b)-B(H(w),U)(a)`.
   Both boundary terms and the actual forcing remain present.

## Correct physical Xi specialization

`ThetaCuspHawkingBMFundamentalHorizonDomain` is corrected to use
`thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)` in
its radial solution and radial operator, matching the parameter used by its
QNM frequency formula. Its prior substitution of the Xi coordinate itself
still gave a true arbitrary-parameter branch statement, but did not identify
that physical fundamental specialization. The corrected capstone is audited
again because its statement and proof changed. The strict frequency-band
argument is exposed once and reused by the new normalizable-domain capstone.

## Formal modules

Six new leaves:

- `RHTower.ThetaCuspHawkingBMOriginalRadialBracket`
- `RHTower.ThetaCuspHawkingBMOriginalHorizonWronskian`
- `RHTower.ThetaCuspHawkingBMOriginalHorizonBasis`
- `RHTower.ThetaCuspHawkingBMOriginalForcedBoundaryPairing`
- `RHTower.ThetaCuspHawkingBMOriginalNormalizableHorizonDomain`
- `RHTower.ThetaCuspHawkingBMFundamentalNormalizableDomain`

Corrected leaf: `RHTower.ThetaCuspHawkingBMFundamentalHorizonDomain`.

## Validation

Seven targeted canonical leaves (416 source lines) passed individual foreground
`lake build <module>` audits, reusing 4082 existing dependency oleans and
producing exactly seven target oleans. Six leaves are new; one is the corrected
physical capstone. All seven installed sources and fourteen installed
olean/ilean artifacts were byte-verified against the isolated audit.

A scratch-only audit of 16 new or changed public declarations (15 new, one
corrected) reported only `propext`, `Classical.choice`, and `Quot.sound`.
All leaf audits were warning-free. The RHTower umbrella is wired without being
built. No full build, umbrella build, numerical experiment, or computational
proof certificate was used.

The corpus index is refreshed. The current global `lint --check-generated`
failure concerns the concurrently added unrelated module
`RHTower.SelbergPositiveEisenstein`, which is not yet wired into its umbrella,
and generated-file freshness. No HB leaf failure was reported; the global
gate awaits completion of those independent edits.

## Remaining hard step

These are actual radial identities and an exact horizon-domain classification.
The [native radial horizon finite part](hb-original-horizon-finite-part.md)
now has its exact cutoff limit and identification with the original response
bracket, including all fundamental Xi QNMs as frequency germs.
The interval source-pairing theorem has not yet been extended to the full joint
modular source with its infinite cusp and endpoint limits. A complete forced
joint inverse, agreement with the original causal transform, and its physical
advanced/adjoint left projection remain unproved. No arbitrary left covector,
normalized scalar residue, or opposite-half-plane energy inverse is substituted
for that construction. Spin-two reconstruction, the independent Hawking-clock
extinction law, and RH remain open.

## Broad horizon search

The requested corpus-tool query `horizon` returned 11008 declarations in 1715
modules with default prefix expansion; this includes `horizontal`. The
exact-token query returned 5959 declarations in 824 modules. The full default
result set was retrieved; the figures are search counts, not claims that every
proof body was inspected.

Inspected cross-family statements give concrete boundaries for further work:

- `HTGeometry.HawkingMassLossClock` differentiates an explicit positive
  cube-root evaporation curve and proves its terminal limit. This does not
  identify the original BM response with that curve.
- `HTGeometry.VaidyaEvaporationFZZHorizonScale` identifies its universal scale
  sign condition with the frequency wall and constructs blind points at a
  fixed scale. The sign condition still needs a producer.
- `ThetaCuspHawkingHorizonRedshiftWindingLadder` retains all actual redshift
  derivatives as shifted Xi values; its observability law is explicitly open.
- `ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer` identifies the exact
  missing dynamical inputs: retarded-minus-advanced source response, cyclic
  Einstein--Green reciprocity, and simultaneous physical solvability. Its
  critical-line theorem takes these as hypotheses. The current original
  boundary-pairing construction addresses the same physical identification,
  without treating those hypotheses as established.
