# TG C9.11u — exact native cumulative ground energy

- **ID:** tg-prime-polar-cumulative-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1 `tg-principal-polar-operator-cancellation`; route TG
- **Statement:** The original physical one-direction ground source has exactly the critical square energy of its literal cumulative prime–polar discrepancy, including the terminal square.
- **Status:** production leaf and all five public axiom checks pass; wired and indexed; global lint reports thirteen unrelated unwired leaves, no finding in this leaf.

## Result and hard question

Write K(P,b,R) for the original positive-logarithmic dilation source,
f_a for the physical indicator of [-a,a], and

`C(t) = sum_(p in P) 1_(log p <= t) - integral_[b,R] 1_(u<=t) (exp(u)+1)/u du`.

For a>0 and b>0 the new result is

`||K(P,b,R) f_a||² = 2a integral_0^infinity exp(-t) C(t)² dt`.

The integral is proved integrable for every finite native source. If R>=0
and all log p<=R, this equals

`2a (integral_(0,R] exp(-t) C(t)² dt + exp(-R) C(R)²)`.

These are exact identities for the actual source, with no arithmetic
admission assumption. They neither bound the energy uniformly nor establish
cofinal Cauchy decay. Those remain the hard arithmetic problem. The full
symmetric source also retains the nonnegative signed-moment square already
proved in `SoninPrimePolarSignedEnergy`.

## Dependency-closed paper proof

1. Finite-measure indicator functions test every L2 vector by its local
   scalar integral. For a strongly integrable L2-valued field with jointly
   measurable representatives bounded by an integrable scalar envelope,
   scalar Fubini identifies the strong integral's representative. Apply this
   only to the original finite polar interval; continuity supplies the
   required domination and integrability.
2. On f_a, normalized dilation by exp(u) is
   `exp(u/2) 1_[-a,a](exp(u)x)`. Multiplication by the literal polar density
   `2 cosh(u/2)/u` gives `(exp(u)+1)/u`. At a prime, the original inverse
   square root cancels the dilation normalization exactly. Thus the actual
   source has the finite prime-minus-polar indicator representative.
3. Substitute x=a exp(-t). Indicator membership is exactly u<=t. The corpus's
   proved quasi-measure-preserving head chart transports the a.e. identity,
   giving the actual source value C(t) in logarithmic coordinates.
4. The source is even and vanishes outside (-a,a). The even half-line mass
   identity and exact head-chart change of variables give the displayed
   critical energy. The L2 head chart separately proves scalar integrability,
   so this identity does not exploit a default value of an undefined integral.
5. Above the synchronized upper endpoint R every prime indicator is one and
   the entire polar interval has entered. Therefore C(t)=C(R) for t>=R.
   Split the genuine integrable energy at R and integrate exp(-t) on its
   infinite tail. This yields precisely exp(-R) C(R)², with no discarded
   boundary term.

## What advanced

C9.11t made actual ground convergence necessary for physical time-band
nuclear admission. This result now identifies that ground norm with the
literal arithmetic discrepancy and its boundary square. The representation
and finite-energy bridge are closed in Lean. No bound on the actual signed
arithmetic cross work has been obtained. The version expressed through raw
prime counting at x=exp(t) remains paper-only.

Next attack: chronological blocks have a covariance that factors into the
earlier counting discrepancy and the later harmonic prime–polar discrepancy.
Derive the actual source identity, then control its signed accumulated work.
Generic positivity or the bounded coprime balance does not supply that bound.
Gamma completion, full-response transport, Hardy cubic compatibility and
the strict sub-unit law remain open. RH is neither proved nor falsified.

## Lean evidence

Leaf: `formal/GaloisForLFunctions/RHTower/SoninPrimePolarCumulativeEnergy.lean`.
Five public declarations: the cumulative function, actual logarithmic
representative, critical energy, its integrability, and endpoint energy.
Wired into `formal/GaloisForLFunctions/RHTower.lean`.

Scratch audit: `/tmp/tg-c911u-energy.log` (exit 0, empty diagnostics).
Final production audit: `/tmp/tg-c911u-final.log` (exit 0, empty diagnostics),
using `lake --old env lean GaloisForLFunctions/RHTower/SoninPrimePolarCumulativeEnergy.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninPrimePolarCumulativeEnergy.olean`.

Public axiom audit `/tmp/tg-c911u-axioms.lean` passed with exit 0. All five
public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Evidence: `/tmp/tg-c911u-axioms.log`. No added axioms, proof holes, numerical
experiments, heartbeat changes, full builds or umbrella builds were used.

Index refresh passed; all five public names occur in `formal/LEAN_API.md`.
Global lint exited 1 with thirteen unrelated modules unreachable from their
umbrella and no finding in this leaf. Logs: `/tmp/tg-c911u-index.log` and
`/tmp/tg-c911u-lint.log`. All owned processes exited. Obsolete proof drafts
and failed probe logs were removed; final audit and search evidence retained.
