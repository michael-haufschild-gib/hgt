# Nodal source mass forces strict modulus contraction

Let ψ be any continuous compactly supported real source and q any physical L²
velocity. Set f(x)=c+∫₀^{exp x}q, B=multiplierSourceRadius ψ>0, and

    P=∫ψ² max(f,0),    N=∫ψ² max(−f,0),    C=sinh(2B).

Use the existing compact mixture: diffuse positive-lag kernel
w(h)=exp(h/2)/sinh h multiplied by ψ(u)²ψ(u+h)², plus the complete family of
nonnegative arithmetic lag lines log(n+2), with arbitrary nonnegative weights.
All energies below are finite by compact-source admission. J is jump energy,
L is nodal energy, and q_abs is the constructed velocity of |c+primitive q|.

The connected result is

    Vψ(f)−Vψ(|f|)=4PN ≤ C L = C [J(q)−J(q_abs)],

and

    J(q_abs)=J(q)
      iff f≥0 everywhere ψ≠0 or f≤0 everywhere ψ≠0.

Consequently contraction is strict exactly when both signs occur at nonzero
source points. This requires neither connected support nor positive source
mass, and imposes no summability or energy-admission premise. It classifies
zero modulus loss; zero jump energy instead requires sourcewise constancy.

## Dependency-closed proof

For any continuous f, every ψ²f^k and each weighted positive/negative part is
continuous with compact support, hence integrable. Write M=∫ψ², A=∫ψ²f,
Q=∫ψ²f² and Vψ(f)=MQ−A². Pointwise f=f⁺−f⁻ and |f|=f⁺+f⁻, so
A=P−N, ∫ψ²|f|=P+N, and Q is unchanged by modulus. Expansion gives the
exact variance defect 4PN. Both masses are nonnegative.

The squared-distance defect is, for all real a,b,

    (b−a)²−(|b|−|a|)²=4[b⁺a⁻+b⁻a⁺]≥0.

Multiply by ψ(u)²ψ(u+h)² to define D(h,u). It is the difference of two
integrable compact pair-gap functions. Existing exact positive-lag variance
transport gives ∫_{h>0}∫D=Vψ(f)−Vψ(|f|)=4PN. No subtraction of independent
inequalities is used. When D≠0 both source endpoints lie in [−B,B], so
0<h≤2B. Thus sinh h≤C and exp(h/2)≥1, whence 1≤Cw(h).
Nonnegativity gives D≤CwD, including zero source pairs. Integration bounds
4PN by C times the diffuse nodal energy; the nonnegative arithmetic part can
only increase this energy. The prior actual modulus decomposition gives
J(q)−J(q_abs)=L, without replacing the actual L² state by a formal symbol.

A nonnegative continuous integrable function has zero integral iff it vanishes
everywhere: zero integral implies vanishing a.e., then continuity and full
support of Lebesgue measure give pointwise vanishing. Applied to ψ²f⁺,
P=0 iff f≤0 wherever ψ≠0; similarly N=0 iff f≥0 there. Hence L=0 implies
PN=0 by the lower bound, giving one of the sign alternatives. Conversely,
either alternative kills every opposite-sign source pair. Both diffuse and
every arithmetic density then have zero nodal integrand, proving L=0.
Finite-energy cancellation in J(q)=J(q_abs)+L proves the equality classifier.
Its negation gives the strict classifier because J(q_abs)≤J(q).

## Scope and parent theory

Positive-kernel comparison and modulus contraction belong to classical jump
form theory. Barlow–Bass–Chen–Kassmann's
[Non-local Dirichlet Forms and Symmetric Jump Processes](https://arxiv.org/abs/math/0609842)
states the squared-difference kernel setting in its abstract; it is background,
not a source for the theorem above. This proof uses the corpus's actual compact
mixture, rough primitive and modulus construction. No external novelty or
closed-operator identification is claimed. Two attempted textbook PDF fetches
failed and supply no evidence.

Focused corpus search returned the existing upper bounds, finite admission,
variance coercivity and exact modulus loss, but no matching nodal mass floor.
All returned candidate lemmas and source arguments were inspected; semantic
coverage was unmeasured and source/compiler freshness incomplete. This is
limited corpus evidence, not an exhaustive prior-art result.

## Formal status

`CompactSourceNodalVariance.lean` proves the exact finite lobe/variance identities
and positive-lag nodal integral (13 public theorems, 4 definitions).
`CompactNodalMassCoercivity.lean` proves the actual graph lower bound and complete
zero-loss/strictness classification (9 public theorems).
Both final serial direct `lake --old env lean -o <normal-output> <leaf>` checks
passed without diagnostics; output timestamps postdate final sources. No
umbrella/full build, numerical experiment, heartbeat increase or added axiom.
All 26 public declarations passed the axiom audit with only `propext`,
`Classical.choice`, `Quot.sound`. Exact declaration coverage was checked; seven
main signatures were inspected and have no extra analytic premises. Both
imports and all public theorem names are indexed. Global lint reports five
unrelated concurrent unreachable modules, listed in the fact ledger; neither
new leaf has an error. This connected package is contribution **7/100**.

Evidence: `/tmp/compact-nodal-variance-build.log`, `/tmp/compact-nodal-mass-build.log`,
`/tmp/compact_nodal_mass_axioms.lean`, `/tmp/compact-nodal-mass-axioms.log`,
`/tmp/compact-nodal-mass-index.log`, `/tmp/compact-nodal-mass-lint.log`.
