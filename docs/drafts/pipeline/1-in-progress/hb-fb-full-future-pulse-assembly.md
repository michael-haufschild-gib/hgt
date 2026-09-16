# Full future pulse assembly

Target: full temporal/metric/QNM matching. The scalar bridge is closed (DN77),
and the upper direct corner is regular (DN78). The entire original future
pulse A_P now equals a single smooth compact formula (DN82).

Fix `w=r-p>0`. Let `T(r)=1+exp(-r)`, so `r+T(r)>=2` by
`Real.add_one_le_exp (-r)`. The original pulse is zero for ingoing time `v>1`.
Its direct and image compact domains are therefore

```
lower direct: p<=v<=r, 0<=z<=exp(v-r);
upper direct: r<=v<=r+T(r), 0<=z<=1;
upper image:  r<=v<=r+T(r), 0<=z<=1.
```

The unchanged pulse has an exact `exp(2*y)` factor; setting `z=exp(2*y)`
cancels it against `dy=dz/(2*z)`. The causal kernel contributes the other
factor `1/2`. The integrand is therefore the full compact pulse averaged
on the original source circle, divided by four. Image enters with minus sign.

For lower direct use `v=r-w+w*alpha`, `z=exp(-w*(1-alpha))*beta`.
Its Jacobian is `w*exp(-w*(1-alpha))` and its invariant factors as
`I-1=2*alpha*(1-beta)*Hlower`, with Hlower strictly positive on the closed square.
For image use `v=r+T*alpha`, `z=beta`, Jacobian T; its invariant is
`I-1=2*alpha*Himage`, with Himage strictly positive for w,T>0.
These permit smooth signed radii with sine/cosine square parameters exactly
as in DN78, but require no triangle subdivision.

Proof obligations: verify these two exact invariant/radius charts; retain
both actual angular fields and the original transition derivative; prove
the resulting full compact action is smooth; identify it with A_P in the
original source-event coordinates, retaining both causal indicators and
all Jacobians. Smoothness of a compact candidate alone is insufficient.

For the last obligation, the proved outgoing-cut null-coordinate argument
in FutureSourceBridge supplies the existing mechanism. On each finite cut,
`integral_source_coordinate` changes `w_source` to `z=exp(v-w_source)`.
Pulse support then fixes the outer v domain, and the continuous compact
integrand permits the outgoing cutoff to tend to infinity, sending its
lower z endpoint to zero. This must be attached to the already admitted
`FuturePulseAdmission.truncatedResponse_limit`; no matching premise is allowed.

Lean-verified leaf: `ThetaCuspHawkingBMFuturePulseAssembly` (560 lines).
`compactInvariant_edge`, `edgeFactor_pos`, and `edgeRadius_eq` verify both
remaining characteristic charts. `edgeAction_eq_integral` and
`upperDirectAction_eq_integral` retain the exact affine Jacobians and the
source radial reversal. `compactFutureAction_eq_charts` identifies the whole
three-region compact integral with its smooth charts;
`compactFutureAction_smooth` proves its joint smoothness. `compactSample_original`
identifies both original source circles and the unchanged pulse density.
`pulseSpan_covers` verifies the single cutoff. `compactMean_cut_tail` proves
the actual omitted-strip limit below. Scratch passed in 32.21 seconds with
default heartbeats and no warnings; exact leaf audit passed in 101.52 seconds,
two jobs, no warnings. Audited source bytes and installed olean verified.
Umbrella wired without a build. Repository lint retains the pre-existing
unreachable `ThetaCuspHawkingBMOnsetTransgressionHorizon` module.

`ThetaCuspHawkingBMFuturePulseIdentity` (339 lines) closes the original
source-event equality. `response_eq_compactFutureAction` identifies the
admitted response at `tau=r-exp(W)/2,x=-exp(W)/2` with the full compact
action; `original_response_smooth` transfers joint smoothness in r,W,X,k.
Scratch passed in 41.29 seconds; exact leaf audit passed in 104.41 seconds,
two jobs, no warnings, default heartbeats. Audited source and installed
olean verified; umbrella wired without a build. Full matching and RH
remain open: horizon-cap regularity, differentiated metric/current
identification, and noncompact QNM admission still require proofs.

## Exact source-event closure mechanism

For the actual compact mean M, its extension `M(v,max(0,z))` is globally
continuous in `(v,z)` for fixed target variables. This follows from the
complete angular fields at positive-height source circles and the positive
compact radial base `1+max(0,z)`. The extension equals M everywhere used
in the physical integrals.

The omitted outgoing-cut strip is

```
Tail(L;a,b)=integral_(v=a..b) integral_(z=0..exp(v-L)) M(v,z).
```

Set `epsilon=exp(-L)`. Continuity of parameter-dependent interval primitives
and one finite outer integral prove that Tail is a continuous function of
epsilon at zero, where it is zero. Hence Tail tends to zero as L tends to
infinity. No new angular-growth or differentiated-tail premise is needed.

Once the original pulse cut is changed to compact null coordinates, and
`L>=r+T(r)`, exact pulse support gives

```
original pulse cut
 = compactFutureAction
   - Tail_direct(L;r-w,r)
   - Tail_direct(L;r,r+T(r))
   + Tail_image(L;r,r+T(r)).
```

All three tails then vanish. Uniqueness with the already proved
`FuturePulseAdmission.truncatedResponse_limit` gives equality with A_P,
and the checked compact smoothness transfers to the admitted original
field. The displayed finite-cut equality and limit identification are
formalised in `FuturePulseIdentity`, using the original gated integrals.

The continuous closed source arm can be written directly from the now
verified compact mean, avoiding a second angular regularity argument:

```
ClosedArm_image(h,y)
 = 2*exp(2*y)*M_image(tau+h+y,exp(2*y)),
tau=r-w/2, x=-w/2.
```

`compactSample_original` and the inspected definition of `onsetAngularMean`
show that this is the original ungated half-kernel, with `max(1,I)` outside
the causal cone. On either cone, `invariant_causal` removes that max. The
original pulse density is therefore its gated direct-minus-image difference.
Under `h=(v+u)/2-tau,y=(v-u)/2`, the arm divided by the null Jacobian factor
two is exactly `exp(v-u)*M_image(v,exp(v-u))`. Applying the existing finite
cone coordinate theorem and the exponential interval substitution gives
the displayed compact-cut formula. New public wrappers
`FutureSourceBridge.future_cone_cut_integrable` and
`future_cone_cut_coordinates` expose the already proved generic cone
argument; their scratch check passed in 29.92 seconds and exact leaf audit
passed in 107.68 seconds, two jobs, no warnings. The actual pulse
specialization is verified in `FuturePulseIdentity`.

Broad literature search: primary arXiv:2606.17762v3 (August 2026) proves
uniform Green estimates for discrete Pontryagin systems under hyperbolicity
and endpoint transversality; arXiv:2609.04084 studies differential boundary
conditions and adjoint transversality. Neither directly supplies the
physical source/cap matching hypotheses here. No external theorem is used.
