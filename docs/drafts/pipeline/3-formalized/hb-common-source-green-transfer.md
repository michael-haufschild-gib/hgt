# HB: common-source Green transfer with every spatial face

Stage: 3-formalized for the four local results listed below. The [radial characteristic transfer](hb-source-characteristic-radial-flux.md) also proves the improper direct-minus-image radial integral and its signed face's late-delay cancellation at fixed source time. The third-order kernel evaluation, full physical cancellation, fixed Hawking-clock extinction and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target is the complete physical pairing `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes. Native/physical causal time-class equality is now [formalized](../3-formalized/hb-native-causal-equality.md). The present attack moves the actual common source producer across the native kernel, retaining its radial and angular faces. It does not assume that the resulting pairing vanishes.

## Exact Lean scope

Module `ThetaCuspHawkingBMNativeAngularGreen` supplies `RHTower.D4BMNativeResponse.nativeMean_joint_smooth`, exposing the existing proof of joint smoothness of the literal theta circle mean in radius and both base coordinates.

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonSourceGreen` proves three unconditional public statements:

- `kernel_invariant_affine`: the fixed-ingoing-delay invariant is affine in compact source radius for both direct and AdS-image terms.
- `thetaSeed_nativeSpinTwoKernel_green`: the original theta seed and either actual native kernel term, retaining `-Delta(Delta-2)`, satisfy the complete local spatial Green identity in the original measure. All regularity is discharged internally. `SourceInterior` contains only geometric source/cone conditions.
- `thetaSeed_producer_original`: this producer is exactly the original physical forcing on either branch, including the complete theta half-square's actual Laplacian and the fixed smooth onset.

The principal namespace for the three new source-transfer theorems is `RHTower.D4BMCommonSourceGreen`; the smoothness theorem is in `RHTower.D4BMNativeResponse`. These statements prove a local source-kernel transfer. They do not establish the complete Einstein four-divergence, finite-domain Stokes identity, characteristic admission, horizon/cusp limits, independent SS/VV coefficients or extinction.

## Exact producer and transpose

Use compact radius `u=1/r`, horizontal coordinate `X`, height `y>0`, and the original complex bilinear pairing. Write

```
Delta=y²(partial_XX+partial_yy), D=(1+u)partial_u+3,
A0=(5lambda-6)/4,
C=((4lambda+1)(lambda+2)-(lambda+4)Delta)/8,
K=(7lambda-2-2Delta)/8,
P=A0+u²C-u²KD.
```

The actual master measure is `u² du dX dy/y²`. The formal transpose, without coefficient conjugation, is

```
Pdagger=A0+u²C+(4u-u²)K+u²KD.
```

This is the same producer already [identified with both original sources](../3-formalized/hb-complete-mixed-current-common-source.md). The actual seed contains the original smooth onset, amplitude, ingoing exponential and full theta half-square.

## Complete local Green identity

Set `b=u^4(1+u)`, `a=-u³-u^4(lambda+8)/8`, `c=-b/4`, and
`W_i(F,G)=(partial_i F)G-F(partial_i G)`. For smooth fields on a finite exterior chart define

```
J_u=-b (K F)G/y²,
J_X=a W_X(F,G)+c W_X(F,partial_u G),
J_y=a W_y(F,G)+c W_y(F,partial_u G).
```

Then

```
u²[(P F)G-F(Pdagger G)]/y²
 =partial_u J_u+partial_X J_X+partial_y J_y.          (1)
```

Proof: differentiate `J_u`, using `b'=4u³+5u^4`. The remaining terms are

```
u^4[(C F)G-F(C G)]
 +(4u³+2u^4)[(K F)G-F(K G)]
 +b[(K F)partial_u G-F K(partial_u G)].
```

The multiplication terms in `C` and `K` cancel. Their Laplacian coefficients are `-(lambda+4)/8` and `-1/4`. Dividing by `y²` and applying the ordinary two-dimensional product rule gives exactly `J_X,J_y`. Radial/angular derivatives commute on the smooth interior chart. No boundary term or source equation is used in this calculation.

Integrating (1) over any finite rectangular chart gives all six oriented faces. General finite angular domains give the corresponding angular normal current. Passing to a cusp limit, a horizon limit or a causal characteristic requires separate estimates and contact terms.

## Original tortoise and logarithmic-height chart

For formal comparison with the existing native kernel, use `x<0`, `u=-tanh x`, `k=log y`, and `L=exp(2k)partial_XX+partial_kk-partial_k`. Replace `D` by `partial_x/(u-1)+3`. Put `m=1-u²`. The density and three currents become

```
u² m exp(-k)[(P F)G-F(Pdagger G)]
 =partial_x I_x+partial_X I_X+partial_k I_k,
I_x=b exp(-k)(K F)G,
I_X=exp(k)[m a W_X(F,G)+(b/4)W_X(F,partial_x G)],
I_k=exp(-k)[m a W_k(F,G)+(b/4)W_k(F,partial_x G)].     (2)
```

The radial sign follows from `du/dx=-m`. The positive `b/4` coefficient in the mixed angular currents follows from the same coordinate change; retaining the compact-coordinate sign there would be incorrect.

## Fixed ingoing delay and both causal terms

The seed's radial derivative holds its ingoing time `v` fixed. Thus its paired kernel is

```
G_epsilon(x,X,k)=R M_(Z_epsilon)Q,
Z_epsilon=invariant(H-x_target+x, x_target, epsilon*x),
R=-Delta(Delta-2), epsilon=+1 (direct), -1 (AdS image).
```

In particular, `partial_x G` contains both the static-time and source-radius derivatives. The actual reflected term changes only the kernel's spatial source argument; its static-time separation still contains `+x`.

At fixed ingoing delay `H`, put

```
A=cosh(H-x_target)/cosh(x_target),
B_epsilon=[sinh(H-x_target)+epsilon*sinh(x_target)]/cosh(x_target).
```

Then the exact invariant is affine in the original compact source radius:

```
Z_epsilon=A-B_epsilon*u.                              (3)
```

Proof: expand `cosh(H-x_target+x)`, use the parity of `sinh` and `cosh` for the image, and substitute `tanh(x)=-u`. This applies separately on each smooth forward cone. The physical direct-minus-image assembly still retains the two distinct characteristic faces.

For `H>0` and `x_target<0`, the source-coordinate intervals are exactly

```
direct: [x_target-H/2, 0],
image:  [-H/2, 0].
```

Indeed, substitute the static separation `H-x_target+x` into the respective causal inequalities `time>=|x_target-x|` and `time>=|x_target+x|`. Thus finite ingoing delay retains finite, distinct lower faces; it does not create a source-horizon boundary at `x=-infinity`.

The upper radial current at source coordinate zero vanishes through its factor `b=u^4(1+u)`. At either lower characteristic, the actual native kernel equals `Q`, so its spin-two weighted value equals `R Q`. Therefore the radial part of the signed direct-minus-image transfer is

```
exp(-k) a_s² chi(v)exp(2s v) (K Q)(R Q)
  *[b(u_image)(1+u_image)^(2s)
     -b(u_direct)(1+u_direct)^(2s)],                  (3a)
u_image=-tanh(-H/2), u_direct=-tanh(x_target-H/2).
```

The two angular face integrals remain. Formula (3a), truncated radial integration and its improper characteristic limit are [formalized](hb-source-characteristic-radial-flux.md). The angular spin-two trace is defined at fixed source radius and proved to be the limit of the interior current. One-sided transverse derivatives of the other current components and subsequent physical limits remain separate. This is not a statement about the target-horizon limit or the full Einstein response current.

## One-variable kernel action exposed by the transfer

Let `N(Z)=R M_Z Q` and `p(Z)=Z²-1`. Joint smoothness and the native Darboux identity give `Delta N=p N''+2Z N'` on `Z>1`; the angular polynomial `R` commutes with this identity. Define

```
d=u+u²(lambda+8)/8,
e=u²(1+u)B_epsilon,
c0=(5lambda-6)/4+u²(4lambda+1)(lambda+2)/8
       +(4u+2u²)(7lambda-2)/8.
```

Equations (1)–(3) reduce the actual transposed kernel producer to

```
Pdagger N = e p/4 N'''
          +(e Z-d p)N''
          +[e(6-7lambda)/8-2d Z]N'
          +c0 N.                                    (4)
```

Proof: `D N=-(1+u)B_epsilon N'+3N`; substitute this in `Pdagger`, then substitute the Darboux identity and its derivative `partial_Z(Delta N)=p N'''+4Z N''+2N'`. Formula (4) is an analytical interior identity, not yet a Lean theorem. It retains the full source-circle function and replaces no angular field by an eigenvalue. The next source-specific evaluation is now a third-order differential expression in the actual invariant, together with the three currents in (2).

## Conjecture loop and remaining test

The first candidate was that the common producer could be moved through the inverse without a remainder. Its exact transpose calculation instead supplies (1), including angular currents absent from a purely radial integration by parts. Applying this at the source's fixed ingoing time exposes the affine invariant (3) and the explicit third-order action (4). The revised candidate is to evaluate (4) on finite domains and combine all faces in (2) with the already derived source-contact and lift currents. No cancellation is inferred from reciprocity alone.

The broad corpus searches `transgression`, `reciprocity`, native smoothness, and mechanism-directed deep current/intertwiner searches were inspected through declarations, candidate lemmas and source arguments. Useful source-level ingredients include `ThetaCuspHawkingBMNativeAngularGreen`, `ThetaCuspHawkingBMCommonRadialSource`, and the coordinate derivative calculus. Search coverage is partial and most candidates are source-only; generated ingredient groups were not accepted as proofs.

An independent broad literature search found [Röntgen et al., August 2026](https://arxiv.org/abs/2608.26562). Their scattering symmetries require a common commuting operator and compatible coupling. This suggests testing an actual intertwining relation for the source producer; the paper supplies no such relation for the present operator. No result from that paper is a premise of (1) or (2).

## Validation

The complete source-transfer module passed foreground `lake env lean` scratch validation without warnings. Final audits ran only the two exact module targets: the native-smoothness extension completed in 66 seconds (three reported jobs); the new source-transfer leaf completed in 69 seconds (four reported jobs). Existing import artifacts were frozen, and the second audit reused the already audited native extension. No old dependency, full or umbrella build ran.

Only the four new public theorems were axiom-audited in a scratch file. Each reports exactly `propext`, `Classical.choice` and `Quot.sound`. Both installed sources and their ten olean/ilean/hash/trace artifacts are byte-identical to the audited files. The new module is wired into RHTower without building the umbrella. No mathematical computation was used.

Whole-corpus static lint passed, with existing large-file warnings only. All eight local links across the three updated reports and scoped whitespace checks passed.

The [actual source cusp-jet admission](hb-angular-cusp-jet-admission.md) proves every complex-weighted coordinate-derivative bound and arbitrary-horizontal-path cusp limit for the literal square remainder and its retained `-Delta(Delta-2)` image. These estimates supply the differentiated source side of the angular boundary argument. [Transport through the native circle kernel](hb-native-cusp-jet-transport.md) is formalized; evaluation of its principal angular flux remains open.

The [native cusp-jet transport](hb-native-cusp-jet-transport.md) now identifies every radius/base-coordinate derivative with the original differentiated angle integral and proves arbitrary-order decay uniformly in horizontal position and compact radius. This closes the remainder estimate needed for the angular cusp analysis. All principal powers, their angular Green flux and invariant-coordinate characteristic admission remain explicit obligations.

The [original Darboux primitive and source derivative](hb-native-darboux-primitive.md) now identify the full native invariant derivative with a nonsingular angular-action integral. Both physical source-radius branches have their actual closed derivative, characteristic contact, interior derivative limit and source-integral reconstruction, including zero delay. Transferring the retained spin-two angular operator through this derivative and evaluating the principal angular currents remain open.
