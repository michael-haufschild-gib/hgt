# Failed producer: reflected zero mass and bounded variation conserve hidden history

**Status:** `[FAILED] [EXACT COUNTERMODEL] [MODULAR SURVIVOR PROMOTED] [NOT RH]`

## Conjecture

> If a source packet has zero total mass, is odd under functional reflection, and has uniformly
> bounded signed variation at every formation depth, then its positive formed histories have
> uniformly bounded information action.

## Countermodel

Take any distinct positive Poisson rates \(\alpha,\beta\), and at depth \(m\) put

\[
 \Sigma_m=P_m-Q_m,
 \qquad P_m=\operatorname{Pois}(m\alpha),
 \quad Q_m=\operatorname{Pois}(m\beta).
\]

Then

\[
 \Sigma_m(\Omega)=0,
 \qquad \|\Sigma_m\|_{\rm TV}\le2
\]

for every \(m\). In reflected prime family, \(t\mapsto-t\) exchanges the rates and makes
\(\Sigma_m\) reflection odd. Yet exact Boolean--history conservation gives

\[
 H_m/m\to(\alpha-\beta)\log(\alpha/\beta)>0.
\]

Thus hidden-history action diverges linearly.

## Positive survivor

Bounded normalized quantities cannot be the producer. The logarithmic Radon--Nikodym cocycle can:

\[
 J(P,Q)=\int\log(dP/dQ)d(P-Q)
 \le\int|\log(dP/dQ)|d(P+Q).
\]

Uniform source control of that modular integral, or of centered modular oscillation, uniformly
bounds history action and therefore forces equal rates by global properness. Full theorem is
promoted to

`../../../2-fully-proven/universal-law-field/species-relative-formation-mechanics/bounded-positive-conservation-blindness-and-modular-producer-criterion-law.md`.

## Closure

- zero total mass: insufficient;
- reflection oddness: insufficient;
- bounded total variation/Hellinger/Jensen--Shannon: insufficient;
- surviving producer type: unbounded logarithmic likelihood/modular control;
- Lean: not written during read-only audit.
