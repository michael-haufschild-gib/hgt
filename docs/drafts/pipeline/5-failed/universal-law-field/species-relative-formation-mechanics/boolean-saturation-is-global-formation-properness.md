# Failed overclaim: Boolean saturation is global formation properness

**Status:** `[FAILED] [EXACT COUNTERTHEOREM] [POSITIVE SURVIVOR PROMOTED] [NOT RH]`

## Conjecture

> Repeated source formation makes Boolean occupancy observer proper; therefore convergence of
> Boolean packet should force equality of underlying source rates.

## Exact failure

For every \(\alpha,\beta>0\), repeated independent Poisson superposition gives

\[
 q_m=1-e^{-m\alpha}\to1,
 \qquad r_m=1-e^{-m\beta}\to1.
\]

More strongly,

\[
 J(\operatorname{Bern}(q_m),\operatorname{Bern}(r_m))\to0
\]

even when \(\alpha\ne\beta\). Observer does not become proper; it becomes maximally saturated.
Every positive rate pair reaches same completion-boundary point.

## Positive survivor

Exact Boolean--history conservation gives

\[
 m(\alpha-\beta)\log(\alpha/\beta)=B_m+H_m.
\]

Since \(B_m\to0\),

\[
 H_m/m\to(\alpha-\beta)\log(\alpha/\beta).
\]

Hidden excess-count history, not saturated observer, carries source-generated properness. Bounded
vertical action along any unbounded superposition-depth sequence forces \(\alpha=\beta\). Survivor
is promoted to

`../../../2-fully-proven/universal-law-field/species-relative-formation-mechanics/superposition-saturation-hidden-history-action-density-and-global-properness-law.md`.

## No-go closure

- **Killing mechanism:** compact observer saturation erases rate separation.
- **Survivor:** vertical conditional information has exact linear density and global properness.
- **Selection boundary:** future source theorem must bound recovered vertical action, not merely
  close or recur Boolean observer.
- **Lean status:** no Lean written during paper-proof research pass.
