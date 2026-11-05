# Even cosh-credit gauges with retained variance

- **ID:** even-cosh-credit-gauges
- **Stage:** 3-formalized
- **Type:** EXISTING RESULT AUDIT
- **Source:** review-0411 §2.1, A8.

## Exact result

For every aperture `c>0`, a signed three-translate theta gauge has profile
`M_{b,α}(x)=(2 cosh(b/2)+α)Φ(x)−Φ(x−b)−Φ(x+b)` strictly positive on
`[−c−1,c+1]` for every `α≥0`. Its cosh charge satisfies

`C_c(M_{b,α})−α/2=C_c(M_{b,0})−αΔ_Φ(c)`,

where `Δ_Φ(c)>0`. Thus the pole coefficient is positive for
`0≤α<α*=C_c(M_{b,0})/Δ_Φ(c)` and zero at `α*`. For every even smooth
compact test `u`, the exact complete Weil form is

`Q(Mu)=J_M(u)−2 V_{M cosh}^{(−c,c)}(u)
        +2(C_c(M)−α/2)∫u²M cosh`.

Every even test supported in `[−c,c]` has this representation: divide by a
smooth positive extension of `M`. The retained variance is essential;
nonnegative pole charge alone does not establish positivity of the signed
jump form. Global window positivity remains an independent sign obligation.

## Proof and Lean

Existing source:
`SignedWindowCriticality/CollectiveSliverPaymentAndSignedThetaGauges.lean`.
Compact positivity follows from the positive minimum of `Φ` and
`Φ(x±b)≤Φ(0)`. The theta-translate source identity gives the exact form;
the positive outside cosh deficit gives the parameter interval.

Exports:
- `exists_signedEvenThetaGauge_pos_and_nonneg_poleCharge`
- `fullZeroForm_signedEvenTheta_window`
- `even_nonneg_iff_signedEvenThetaGauge`
- `reflectionPair_signedThetaGauge_representation`

The source also proves that one globally nonsingular even theta gauge
cannot have nonnegative pole charge on every window. Window adaptation
and signed coefficients supply the positive survivor.

Direct `lake --old env lean` source check passed. Eight transitive axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`. Import
closure is acyclic, with no owning umbrella dependency or forbidden proof
tokens. The existing umbrella import is verified. No new theorem is claimed.
