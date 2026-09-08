# HB native energy selection and full frequency transport

- **ID:** hb-native-energy-selection-and-frequency-transport
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** [cusp spectrum and causal continuation](../1-in-progress/hb-cusp-spectrum-and-causal-continuation.md)
- **Statement:** The original native norm eliminates the actual growing cusp coefficient. The full original Einstein stream has an exact frequency-transfer defect when its radial and angular profiles are held fixed.

RH remains open. Chain: literal theta cusp → Xi occurrence → retained spin-two
source → original causal response and left-QNM pairing → independent
Hawking-clock extinction → RH.

## Actual native coefficient selection

Let h be the constructed smooth representative of the original modular energy
response, and m its width-one cusp mean. The established almost-everywhere
identification with the original L2 vector proves integrability of `||h||²` in
the original modular measure. Transport through the upper-half-plane chart
preserves that measure with density `1/y²`. The full rectangle
`[-1/2,1/2] x (2,infinity)` lies in the actual modular cell. Restriction and
Fubini therefore prove

`integral_(y>2) (integral_(-1/2,1/2] ||h(x+i*y)||² dx)/y² dy < infinity`.

Width-one Cauchy–Schwarz bounds `||m(y)||²` by the inner integral. The actual
mean is continuous, so domination gives
`integral_(y>2) ||m(y)||²/y² dy < infinity`.
No norm-transfer or response-domain assumption is supplied.

Use the actual indicial roots `a=v+2`, `b=-v-1`, with doubled physical rate
`v=2s`, and the already constructed coefficients `A=-ell_b/(b-a)` and
`B=ell_a/(b-a)`. The physical strip gives `Re(b)>1`, without RH. The actual
asymptotic law is `m(y)/y^b -> B`.

If B were nonzero, put `c=||B||/2>0`. On a sufficiently large tail,
`||m(y)/y^b||>=c`. For y>=1, `||y^b||=y^Re(b)>=y`, so
`||m(y)||²/y²>=c²`. Integrability would then make the positive constant c²
integrable on an infinite half-line, a contradiction. Thus B=0 and ell_a=0
for every actual Xi occurrence and both branches.

The resulting boundary law and exact reconstruction retain the full source:

`J_a(y)=-integral_y^infinity g_a`,

`m(y)=A*y^a+(y^a*integral_y^infinity g_b-y^b*integral_y^infinity g_a)/(b-a)`.

This is selection by the original native energy domain. A still contains the
global boundary jet, compact modular geometry and cutoff contribution. Its
value or nonvanishing has not been determined. The result imposes no further
restriction on Xi zero locations and does not identify a retarded response.

## Full original frequency transfer

The original vector master has independent time frequency and radial jets:

`M_w(H,A,D)=[r²*f*H''+2*r*H'-(w²*r²/f+2)*H]*A+H*D`,

where `f=r²-1`. Its radial derivative is the existing `masterFirst`. Holding
the radial jets and angular slots fixed gives exactly

`M_w-M_v=-(w²-v²)*r²/f*H*A`,

`M'_w-M'_v=-(w²-v²)*(r²/f*H'-2*r/f²*H)*A`.

At the physical rate `v=2s`, retain both original radial factors and put
`c=s*(s-1)/4`. Write P for the mixed stream value
`H_v*A-c*(H_v/r²)*J`, and P' for its full radial derivative. Here A and J are
the actual constructed angular-response and squared-source covectors, and C
is the original retained mixed current, including its gradient-source term.
The previously proved source equation at v gives, at arbitrary w,

`mixed M_w=2*C-(w²-v²)*r²/f*P`,

`mixed M'_w=2*C'-(w²-v²)*(r²/f*P'-2*r/f²*P)`.

The temporal Einstein block multiplies M' by `-f/(2*r²)`; the radial block
multiplies M by `-w/(2*r²*f)`. Therefore, adding the original literal source
to the frozen-profile Einstein expression leaves the explicit correction

`D_t=f/(2*r²)*(w²-v²)*(r²/f*P'-2*r/f²*P)`,

`D_r=-(w-v)/(r²*f)*C+w/(2*r²*f)*(w²-v²)*r²/f*P`.

The first term in D_r is essential: it comes from the unsquared frequency in
the original tensor reconstruction. Both angular components and their
symmetric partners are included; all other components vanish. Lean identifies
this complete tensor with the original cosmological Einstein contraction on
the metric-jet pencil, using actual angular derivatives and original radial
profile derivatives. No substitute wave operator is used.

This is an exact comparison of the original operator at independent frequency
and radial-profile parameters. It does not construct an off-frequency causal
field, identify the transformed source after switching, or justify keeping
the original source tensor fixed under a causal transform. Those obligations
remain explicit. The diagonal angular polynomial `(v+1)*(v+2)` alone does not
specify this full frequency problem.

## Remaining mathematical obstacle

Derive the original causal convergence chamber with a compatible transformed
source and its initial terms, then continue the full radial/angular response
with its physical boundary domain. Determine its source-dependent cusp
coefficient and any change from the native coefficient B=0. The full continued
response must enter the original left-QNM pairing before an independent
Hawking-clock extinction argument. Gauge, other response sectors and RH remain
open. No numerical experiment was needed.

## Lean surface and audit

Module prefix: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBM`.

| Module suffix | Namespace | New public theorems |
|---|---|---:|
| `CuspNativeMeanSquare` | `RHTower.D4BMCuspResponse` | 2 |
| `CuspMeanEnergy` | `RHTower.D4BMCuspResponse` | 2 |
| `CuspGrowingCoefficient` | `RHTower.D4BMCuspResponse` | 4 |
| `StreamFrequencyTransport` | `RHTower.D4BMModularCore` | 2 |
| `StreamFrequencyTensor` | `RHTower.D4BMModularCore` | 2 |

All five development leaves passed `lake env lean` in scratch. Each exact
canonical module then passed its final `lake build <module>` audit through an
isolated package using existing import caches. Only the requested new leaf
compiled in each build; no dependency, full or umbrella build ran. All ten
new olean/ilean artifacts were installed and byte-checked against the audited
copies, and all five imports are wired exactly once into the umbrella.

One scratch axiom audit checked precisely the twelve new public theorems:
`propext`, `Classical.choice` and `Quot.sound` only. No previous theorem was
re-audited. No added axiom, placeholder, computational certificate or numerical
experiment was used. The source index was refreshed; scoped whitespace and
import checks passed.

`scripts/formal_tools.py lint --check-generated` reported two unrelated
concurrent modules unreachable from the RHTower umbrella:
`RHTower.DivisorSourceEntire` and `RHTower.MontgomeryIsolatedDensityConditional`,
plus 141 existing large-file warnings. Neither module was edited by this work.
Owned scratch and audit files were removed; no owned Lean/Lake process remains.
The frontier map was not edited.
