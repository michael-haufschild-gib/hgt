# The positive theta half is a canonical unit-radius Perron source

- **ID:** xi-theta-unit-radius-perron-source
- **Stage:** 2-fully-proven
- **Type:** THEOREM / NATIVE SEAM ALIGNMENT, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `xi-theta-critical-trace.md`, `xi-theta-reader-superexponential-conditioning.md`,
  `perron-mellin-seam-residue.md`, `canonical-perron-mellin-seam.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiThetaPositiveL2Perron.lean`

## The question a field expert asks

The completed logarithmic theta source is

`h(u) = exp(u/4) F(exp u)`

and satisfies `h(-u)=h(u)`.  Its positive half

`h_+(u) = 1_(0,infinity)(u) h(u)`

already determines the completed critical trace as a cosine transform.  Before constructing a new
reader or assigning an extra Perron charge to the reflected half, ask:

> Does the actual `h_+` itself inhabit the lower-supported `L2` source space on which the existing
> Perron--Mellin seam theorem acts?

If yes, reflection has already been quotiented by the critical cosine trace.  The meaningful
Perron question is the charge of `h_+`, not a second independently chosen reflected charge.

## Theorem A `[PROVED]`: exact exponential envelope

Put

`C_theta = evenKernel(0,1)-1 = 2 sum_(m>=1) exp(-pi m^2) > 0`.

Then, for every real `u`,

`|h_+(u)| <= C_theta exp(-2u)`,                                  (1)

and in particular

`|h_+(u)| <= C_theta`.                                           (2)

### Proof

For `u<=0`, `h_+(u)=0`.  For `u>0`, the ordinary positive theta expansion gives

`h_+(u) = sum_(m>=1) 2 exp(u/4) exp(-pi m^2 exp u)`.

For every `m>=1` and `u>=0`, the already-proved square-atom estimate is

`2 exp(u/4) exp(-pi m^2 exp u)
 <= 2 exp(-pi m^2) exp(-2u)`.

Both series are summable and have nonnegative terms, so termwise comparison and summation give
(1).  Since `exp(-2u)<=1` on the positive half-line, (2) follows.  Strict positivity of `C_theta`
comes from strict positivity of every theta-square term.

## Theorem B `[PROVED]`: the actual positive theta source is in `L2`

The function `h_+` belongs to `L2(R)`.  Hence it defines a canonical class

`g_theta = [h_+] in SoninL2`

which vanishes almost everywhere below threshold zero.

### Proof

Mellin convergence of the completed theta kernel at the critical normalization already gives
`h in L1(R)`, hence `h_+ in L1(R)`.  By (2),

`|h_+(u)|^2 <= C_theta |h_+(u)|`.

The right-hand side is integrable, so `h_+ in L2(R)`.  Passing to its `L2` equivalence class
preserves the explicit representative almost everywhere.  The strict positive truncation gives
the lower-support condition at threshold zero directly.

The step `L1 intersect L-infinity subset L2` is a `[BRIDGE]`; the substantive point is that (1)
discharges both hypotheses for the actual completed-theta half-source with an explicit intrinsic
constant.

## Theorem C `[PROVED]`: unit-radius theta-source charge decay

Let `0<delta<n`, `n>=1`, and put `D=n-delta`.  If `D>1`, then the normalized negative-line Perron
charge of `g_theta` satisfies

`Src_(M,n,delta)(g_theta) -> 0` as `M -> infinity`.                (3)

More precisely, for `M>=2`,

`|Src_(M,n,delta)(g_theta)|
 <= kappa ||g_theta||_2 D^(1-M)`,                                 (4)

where `kappa=2 sqrt(pi)/pi` is the existing Perron flank constant.

### Proof

The general lower-support estimate at threshold `tau` is

`|Src_M(g)| <= kappa exp(-M tau) ||g||_2 D^(1-M)`.

Theorem B supplies `g=g_theta` and `tau=0`, so the source radius is exactly the support radius
`exp(-tau)=1`.  Equation (4) follows.  When `D>1`, its right-hand side is a fixed constant times a
geometric sequence of ratio `D^(-1)<1`, proving (3).

## Theorem D `[PROVED BRIDGE / FLOW DIAGNOSTIC]`: canonical theta seam recovers coefficients

Let `F` be an entire carrier agreeing on `Re(s)>=c>0` with the absolutely convergent Dirichlet
series `sum a_m m^(-s)`.  Assume the existing coefficient-independent horizontal Perron mass and
completed vertical `L2` flank-energy conditions for `F`.  Define, without any defect-existence
hypothesis,

`Delta_M^theta = [t |-> F(-M+it)] - T_M(g_theta)`.

For every admissible `(n,delta)` with `n-delta>1`,

`A_(M,n,delta)(Delta^theta) -> a_n`.                               (5)

### Proof

Vertical `L2` energy constructs the line class `[F(-M+i·)]` eventually in `M`; subtraction therefore
constructs `Delta_M^theta` canonically and proves the cross-line defect identity almost everywhere.
Horizontal Perron mass supplies boundary escape eventually.  Exact Perron charge splitting then
gives

`delta a_n = Src_(M,n,delta)(g_theta)
             + Res_(M,n,delta)(Delta^theta)`.

Theorem C kills the source term.  Thus the residue tends to `delta a_n`; division by the fixed
nonzero `delta` proves (5).  No abstract source witness and no cross-line-defect Prop remain.

This theorem is a correct coefficient identity, but it is not the RH-bearing constraint.  The
`M`-indexed carrier lines transport right-edge data through a contour.  The subsequent
`xi-theta-boundary-coboundary-no-go.md` proves that the theta moving boundary feeding this picture is
an exact flat translation coboundary.  The carrier recovery is therefore retained as a `[BRIDGE]`
and a diagnostic, not as the route forward.

## Reflection audit

The competing interpretations were:

1. `[FALSIFIED]` Treat `h_+(-u)` as a second lower-supported Perron source.  It is upper-supported,
   and negative Mellin weights amplify rather than suppress it.  More importantly, this assigns
   independent data to a term already fixed by reflection.
2. `[UNNECESSARY HERE]` Invert the critical trace, pass to heat coordinates, and apply the Hardy
   square-rate reader before entering the Perron seam.  That reader is valid for coefficient
   extraction, but it adds a superexponentially conditioned analytic layer without resolving the
   completed/raw carrier mismatch, and the boundary it transports is cohomologically exact.
3. `[SURVIVES]` Use the critical cosine identity first.  Since `h_+` is real,

   `Fourier(h_+ reflected)(w) = conjugate(Fourier(h_+)(w))`,

   and the completed critical trace is `Re Fourier(h_+)`.  Reflection is therefore the conjugate
   half of one cosine datum, not an additional Perron charge.  Theorems B--C apply directly to the
   one-sided source that remains; Theorem D records only its coefficient transport.

## What fails before what works

- The new theorem does **not** produce an unconditional proof of RH.
- Building such a carrier is a flow construction in disguise: it organizes transported vertical
  lines rather than extracting a static non-exact constraint from the fixed completed object.
- It does prove that the theta-source side is no longer responsible for the obstruction: the
  positive source exists canonically in the correct Hilbert space and its source charge dies beyond
  radius one.

The route-closing coboundary theorem sharpens the actual open core:

> `[OPEN CORE]` Map the fixed completed-theta/prime weld to a nonzero carrier-free obstruction class
> which survives quotienting by affine translation/scaling coboundaries, and connect that class to
> FE polarization without an evolving carrier or contour-depth family.

Scalar decompletion, non-diagonal coefficient transport, and the moving-boundary reader all remain
on the flow side unless they produce such a non-exact class.

## Novelty and significance gates

- **NOVEL:** The boundedness and `L2` promotion alone are standard analytic bridges.  The new
  knowledge is their exact alignment with the project-native Perron source: the actual positive
  completed-theta half has intrinsic radius one and leaves no independent reflected charge.  This
  composition is not a literature lookup or a renamed generic source theorem.
- **SIGNIFICANT:** The abstract source-existence interface is removed for the actual theta object.
  Together with `xi-theta-boundary-coboundary-no-go.md`, the result separates valid analytic source
  infrastructure from the exact flow defect that cannot carry the RH obstruction.

## Gates

- [x] 0 -> 1: competing reflected-charge interpretations attacked; direct source route selected.
- [x] 1 -> 2: quantitative source bound, `L2` realization, unit-radius decay, and the carrier
  recovery bridge proved on paper.
- [x] 2 -> 3: theorem family formalized in Lean without `sorry`, `axiom`, or source/defect Props.
- [ ] 3 -> 4: publication promotion requires the fixed non-exact weld class and its polarization.
