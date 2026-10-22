# HB: physical-clock balance of the tested incoming cusp current

- **ID:** HB-QTCC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Predecessors:** [full response cusp period](hb-full-scalar-tested-response-cusp-period.md), [incoming source work](hb-incoming-radial-response-work.md)
- **Active attack:** [source-contact/current balance](../1-in-progress/hb-source-contact-spin-two-balance.md)

Proof chain: literal theta cusp → Xi occurrence → retained spin two → physical
causal radial/left-QNM action → fixed common Hawking-clock extinction → RH.

## Actual source current and physical test

Fix an original Xi occurrence q and arbitrary complex amplitudes a,b. Write
s=physicalRate q true, t=physicalRate q false, alpha=parameter q true,
beta=parameter q false. These are the original fundamental rates in
D4BMModularCore (s=rho-2 and t=-rho-1). Let H and K be the two constructed
full angular responses, Q the literal theta half-square, and psi the original
physical scalar test. The original currents are

```
J_G = beta (K+Q) grad H - alpha (H+Q) grad K,
J_S = Q [w_0 grad H + w_1 grad K + (2 w_2/3) grad Q],
J   = -(s t/3) J_G + J_S,
```

where w_i are the unchanged sourceWorkWeights. The original work is

```
W = w_0 alpha Q H + w_1 beta Q K + squareWorkCoefficient Q^2.
```

Both response corrections and all source-contact factors Q in these formulas
are retained. Define C=clockCoefficients q a b (x,y) 1 0 and k=a^2 b^2/16.
The established source equation is exactly

```
y^2 C = k [y^2 div J-W].
```

Every field in the new theorem is this constructed field. The theorem does
not accept an external solution, current, conservation premise or boundary
vanishing hypothesis.

## Differentiated physical test

Product differentiation of the entire current gives

```
div(psi J)=grad psi dot J+psi div J,
psi C=k [div(psi J)-grad psi dot J-psi W/y^2].
```

This retains the actual metric factor y^-2 on the source work. Equivalently,
the left planar integral is the native hyperbolic integral of psi*y^2*C on
any strip that lies in the fundamental cusp. No metric weight was frozen or
discarded in passing to the planar chart.

Smoothness is discharged from the literal scalar's joint smoothness and the
two constructed responses' smoothness. Coordinate derivatives preserve the
required smoothness. Complex reciprocals are differentiated over the original
real coordinates only at positive height.

## Source-derived side matching and finite Stokes

The literal scalar is horizontally periodic. Modular invariance of the full
responses gives their same unit translation identity. Coordinate derivatives
commute with this translation; products and the original sums preserve it.
Consequently the complete tested current psi*J matches across the horizontal
period's two sides, including all its response/source corrections.

Let mean denote integration in x from -1/2 to 1/2. Put

```
B(y)=mean_x(psi J_y),
D(y)=mean_x(div(psi J)),
W_tested(y)=mean_x(grad psi dot J+psi W/y^2),
R_ab(y)=mean_x(psi C).
```

Horizontal FTC cancels the full x-derivative using the proved side matching.
Differentiation under the native width-one average then gives B'=D. All
finite height integrals are admitted by the proved smoothness. For every
positive l,r, oriented interval integration proves

```
integral_l^r D(y)dy=B(r)-B(l),
integral_l^r R_ab(y)dy=k [B(r)-B(l)-integral_l^r W_tested(y)dy].
```

These are identities on the positive-height width-one strip. With l,r>3 they
apply directly to the original fundamental cusp used by the predecessor's
finite-part theorems. The upper and lower vertical contributions both remain.
Horizontal periodicity supplies no removal of grad(psi) dot J.

## Original finite physical clock

Let T_h(y) be the same horizontal scalar pairing of
`clockMoment (-6) h (fun u => incomingCurrent q a b 1 u (x,y) 1)`.
The original horizon-current translation law gives, for every h:NNReal,

```
T_h(y)=h exp(-6h) R_ab(y),
integral_l^r T_h(y)dy
 =h exp(-6h) (a^2 b^2/16)
    [B(r)-B(l)-integral_l^r W_tested(y)dy].
```

The rate -6 is the existing common horizon-clock normalization and is
independent of q. This proves the finite-clock cusp balance of the actual
incoming radial component, including the original horizon-current moment.
No frequency correction, fitted constant or source-dependent clock is used.

## Remaining extinction obligation

The source independently supplies the field equations, complete side matching,
all finite-height admissions, exact product rule, and original clock moment
law above. It has not yet supplied vanishing of the bracket. Passing to the
complete physical action still requires the original finite-part boundary
restoration and cancellation with every remaining scalar/scalar,
scalar/vector, vector/vector, retained spin-two, horizon, characteristic and
source-contact contribution. This incoming radial sector theorem does not
assert those cancellations or identify the whole left-QNM projection.

The immediately exposed analytic target is the original upper-cusp finite part
of B together with the complete derivative-test work, matched to the already
restored response-source periods and the local Q^2 contribution. Defining that
balance to be zero would assume the missing producer. No such definition or
assumption is made. HB and RH remain open.

## Verification

Scratch `lake env lean /tmp/hb-tested-angular-current.lean` passed with both
original and trimmed imports at default limits. The isolated final
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticTestedCurrentCusp`
passed in 16 seconds using cached imports. Source SHA256:
`ce13833079844dd9a71392bdfbcd65ed72cf5bbef7c67636bab0d8557e730c5d`.
The module has nine public theorems and eight public definitions and is wired
once into the umbrella. No heartbeat, recursion-depth or transparency override
was added.

Index generation initially refreshed 8 changed files. The first lint detected
that RHTower.lean and MaassLadderL2.lean had changed concurrently after that
refresh. A second refresh covered those 2 verified changes; subsequent
`scripts/formal_tools.py lint --check-generated` passed (exit 0). All 17 public
API entries, the single umbrella import and the unchanged audited source hash
were verified. All owned Lean, audit, search, index and lint processes completed;
the temporary audit directory was removed. No full or umbrella build was run.
