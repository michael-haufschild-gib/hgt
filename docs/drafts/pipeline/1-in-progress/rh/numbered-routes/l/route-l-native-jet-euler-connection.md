# Route L: native internal-jet Euler connection

- **ID:** RH-L-C67
- **Stage:** 1-in-progress
- **Target:** Full-source fixed Gamma/BV reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.
C66 proved both original collars and their exact finite-prefix distribution
transgression. The missing map to the fixed physical reader remains open.

## Current source attack

Write `h_k=h_(k,m)`, `A_(k,p)(x)=Σ_(n≥p) μ(n)H_(h_k)(nx)` for `x>0`.
The actual internal jet obeys `h_(k+1)(t)=i m t h_k(t)`. Therefore

```
A_(k+1,p)(x)=i m [log(x) A_(k,p)(x)
  - Σ_r Λ(r) M(h_k)(rx) - Σ_(n<p) μ(n)log(n)H_(h_k)(nx)].
```

Here `M` is the existing complete Möbius preimage, not a newly chosen
primitive. This follows from the existing complete ray connection
`Σ_r Λ(r)M(h)(rx)=-Σ_n μ(n)log(n)H_h(nx)` and the unchanged finite prefix.
Absolute admission of the logarithmic series can be obtained directly from
admission of successive original jets, instead of increasing a proof limit
or introducing a new decay hypothesis.

For the actual exchanged source `Jh_k`, jet raising has coefficient `-i m t`.
The opposite sign must survive in the second connection. This pair of
source-derived recurrences is the paper target. Its Gamma/Fourier pairing
must retain both full Euler currents and both prefix terms; discarding them
would not prove the requested comparison. Neither recurrence is a claim
that the fixed reader is cyclic or annihilates these currents.

The next test is whether the existing source connection and its Fourier
partner identify the two fixed readings, with their original normalization,
rather than merely reproduce a formal reflection or a zero-jet cancellation.

## Verified endpoint mass attack

The recurrences and critical scalar-pairing admission now pass Lean; the named
leaf build passed. Critical scalar admission does not justify exchanging an
integral with the reconstructed Euler series. The next paper target uses the
already admitted positive-damping family instead:

`integral_R M_a(h) = 2 P(h) invZeta(1+a)` for `a>0`.

Apply the continuous L1 integral to the existing L1 parameter derivative.
Differentiate this established identity on the open positive half-line to get
`integral_R E_a(h) = 2 P(h) invZeta'(1+a)`. The residue normalization gives
`invZeta'(1)=1`, so these masses tend to `2 P(h)` as `a` decreases to zero.
For the original first collar, `P(h_k)=Xi^(k)(i(1/2-1/m))/m`.
For its actual exchange, the original exponential factor cancels the ray
Jacobian before reflection, giving `P(Jh_k)=Xi^(k)(i/2)/m`.
Both complete Euler mass limits and this second source mass now pass Lean
in `/tmp/MobiusThetaNativeEulerMass.lean`. This identifies native scalar
mass corrections without claiming a weak distributional limit, an
integral/sum interchange at zero damping, or the fixed degree-six Gamma/BV
reader comparison. The installed leaf passed its final named-module audit.

The proof differentiates an established equality on the open positive
half-line. It does not infer an endpoint derivative from continuity of the
preimage. Dilation and absolute L1 summability justify the mass identity;
the existing L1 parameter-derivative theorem then justifies applying the
continuous integral to the derivative. Only afterward does continuity of
the analytic reciprocal-zeta derivative at its removable pole determine
the limit. All original internal orders and positive depths remain free.

## Verified source results

`MobiusThetaNativeJetEulerConnection.lean` proves both displayed recurrences,
the opposite sign on the actual exchanged source, and absolute summability
of both original logarithmic ray series for every internal order and positive
native depth. The proof obtains the extra logarithm from successive admitted
native jets. It uses the existing fully summed Möbius/von Mangoldt connection
and then removes exactly the unchanged finite prefix.

For each of the two complete all-integer preimages and every Schwartz test,
the critical causal series of scalar pairings is summable. The preimage's
proved zero mass removes the constant test value; its proved first moment
bounds the remainder by the Schwartz derivative seminorm times displacement.
This discharges source admission, not the equality between this series and
an integral of the pointwise Euler sum. No damping-limit identification,
Gamma/BV normalization, or conormal vanishing follows yet.

## Whole-corpus and method audits

Eight direct deep searches were run with `--any --budget-seconds 120
--no-refresh --json`. All 20 candidate statements and all 20 source-method
records from each result were inspected, including actual hypotheses and
the proposed ingredient groups. Every search reports partial retrieval and
source-only candidates; complete inventory is not compiler verification.
All returned zero proof ideas. Each has one unverified ingredient group
except the quadratic-source search, which has none.

| Search artifact | Index; snapshot/current | Files / Lean / declarations | Compiler pending |
|---|---|---|---|
| [native jet connection](../../../route-l-native-jet-connection-search.json) | 881818; 881825/881827 | 57137 / 47502 / 736578 | 44662 |
| [Fourier Euler Gamma pairing](../../../route-l-fourier-euler-gamma-pairing-search.json) | 881829; 881847/881848 | 57138 / 47502 / 736578 | 44662 |
| [critical source admission](../../../route-l-native-euler-current-admission-search.json) | 881913; 881935/881935 | 57145 / 47509 / 736853 | 44669 |
| [positive quadratic source](../../../route-l-hidden-quadratic-source-search.json) | 881925; 881936/881937 | 57145 / 47509 / 736853 | 44669 |
| [critical Euler contact](../../../route-l-critical-euler-contact-search.json) | 881945; 881962/881970 | 57145 / 47509 / 736853 | 44669 |
| [logarithmic mass](../../../route-l-logarithmic-mass-contact-search.json) | 881971; 881973/881975 | 57148 / 47512 / 737125 | 44672 |
| [adiabatic native mass](../../../route-l-adiabatic-native-mass-search.json) | 882053; 882054/882063 | 57158 / 47522 / 737205 | 44682 |
| [critical logarithmic moment](../../../route-l-native-critical-log-moment-search.json) | 882198; 882249/882251 | 57193 / 47556 / 737993 | 44716 |

The useful source arguments are the complete Möbius connection, causal
renormalization with zero mass and first moment, admitted L1 adiabatic
derivative, and the normalized reciprocal-zeta derivative at its removable
pole. Their precise domains matter: the Fourier Euler distribution and L1
parameter derivative theorems require strictly positive damping. A group
mixing the PW Gamma profile with a generic all-exponential Meyer source does
not establish their identification. The PW profile is outside that source
class. Its separately proved logarithmic current has nonzero reconstructed
mass despite zero mass of every Euler dilation; its Gamma value cannot be
transferred to our theta source.

The logarithmic normalization search supplies actual convergence of partial
sums of `-mu(n) log(n)/n` to one and stronger logarithmic error estimates.
The private weighted derivative theorem was source-read, not invoked by a
mangled private name. The current mass attack instead uses the public L1
derivative and differentiates the complete admitted mass identity. Arithmetic
ring identities, source definitions, positivity conditional on contractions,
and finite determinant nonvanishing do not establish the fixed reader map.
No inference of absence is made from these partial search results.

The last search's source-method metadata are all null; the declarations'
actual premises were inspected directly. Its proposed group uses the
definition of the Euler L1 sum together with the undifferentiated Abel
majorant, leaving uniform damping as an obligation. The polynomial-moment
endpoint continuity theorem does not supply a logarithmic moment or an
endpoint derivative. Positive energy lower bounds and ordinary Dirichlet
bounds do not fill that gap. The relevant Abel and moment source files
were read; no unverified method record was treated as a proof.

## Recent broad-paper tests

The single-word arXiv search **intertwining**, sorted by newest announcement,
was screened beyond the immediate RH literature. The following papers were
read at the stated scope; neither supplies a verified Lean ingredient.

- [Shimazaki, 2609.11233v1, September 10](https://arxiv.org/html/2609.11233v1):
  read the sign-reversing involution proof (Proposition 3.1), fixed-maximum
  weighted generating function (Theorem 3.3), single-coordinate toggle,
  crystal intertwining proof (Theorem 6.9), and the ordinary/exceptional-color
  distinction in Section 7.2. The weighted Boolean fibre retains a product
  of factors depending on the weights; sign reversal alone is not weighted
  cancellation. Toggling an original prime changes its logarithmic weight.
  The native jet recurrence therefore keeps the resulting Euler term.
  The full exceptional-color proof and all prerequisite crystal lemmas were
  not independently audited.
- [Caputo–Quattropani–Sau, 2609.10450v1, September 9](https://arxiv.org/html/2609.10450v1):
  read the spectral-gap statements, hidden stochastic matrix model,
  forward/backward intertwiners, quadratic variance argument, and positive
  quadratic Perron mode construction outline. Their transfer requires actual
  nonnegative stochastic updates, positive weights, reversibility and, for
  the L2 conclusion, polynomial density. Strong positivity uses connectivity
  and propagation spanning the update orbits. A positive quadratic mode is
  not supplied by merely calling our signed Möbius source a hidden process.
  The quadratic-source corpus search did not construct these premises on
  the unchanged native source. The full strong-positivity proof and external
  Perron references were not independently audited.

## Verification

The 206-line scratch proof passed `lake env lean` with no warnings. Its
documented leaf passed final `lake build
GaloisForLFunctions.RHTower.MobiusThetaNativeJetEulerConnection`; the log
records the new leaf built in 152 seconds. It is wired immediately after
`MobiusThetaNativeSecondCollar` in `RHTower.lean`. No umbrella build, numerical
experiment, heartbeat increase, or axiom-report command was used.

The subsequent global `scripts/formal_tools.py lint` exited 1 for concurrent
unreachable modules: `MaassCircleKernel`, `MaassCircleTransfer`,
`HTGeometry.CompactSmoothParameterIntegral`, and `HTGeometry.InversePowerCancellation`.
Those files are outside this write scope. The new jet leaf was not among
the reported errors. The later 171-line mass scratch passed with no
warnings; final `lake build
GaloisForLFunctions.RHTower.MobiusThetaNativeEulerMass` also passed, with the
new leaf built in 181 seconds. The documented leaf has 191 lines and is
wired beside the jet connection in `RHTower.lean`. Its subsequent lint
also exited 1: the same four concurrent unreachable modules remained, with
`ThetaCuspHawkingBMSourceEndpointPolynomial` additionally reported. Neither
new native-source leaf was reported as an error.

Both owned Lean checks/builds are terminal; no owned Lean process remains.
Only named leaf builds were run. Logs are
`/tmp/route-l-native-jet-euler-build.log`,
`/tmp/route-l-native-euler-mass-build.log`, and the corresponding `-lint.log`
files. No shared unrelated process or file was modified.

## Next hard comparison, with unproved steps explicit

The next conjecture is L1 convergence of the complete pointwise native
Euler currents as damping decreases to zero. The positive-damping norm
series bound is not uniform at zero, so it cannot prove this. A surviving
approach is Abel assembly of the signed logarithmic atoms, using the
corpus's stronger Mertens logarithmic rates to control the entire near-origin
contribution uniformly. This must be proved for the native source, not
transferred from the PW Gamma example.

Even that L1 limit would not by itself identify the critical scalar-pairing
series. A second comparison must establish their equality away from the
origin, bound the order of the supported difference, and determine its
coefficient from the original mass. Only after those steps could an origin
contact term be carried through the Fourier collar with a justified sign
and normalization. No delta distribution formula is currently claimed.
The fixed degree-six Gamma/BV reader and the original finite-prefix
horizontal boundary must then be compared on their actual shared domain.

The route-neutral ledger already states the relevant integral/reconstruction
constraint and is unchanged. Full-source fixed reader agreement and RH
remain **UNPROVED**.
