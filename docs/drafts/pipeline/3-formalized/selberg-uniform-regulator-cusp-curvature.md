# Uniform cusp control and exact total orbit curvature

- Stage: 3-formalized; complete source, targeted build, axiom, index, and lint audits passed.
- Parent: [Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 38.
- Previous goal turn: progress; exact cell unfolding and the signed finite quotient-functional budget completed and audited.

## Paper proof

Write a=sqrt(D), rho_e=sqrt(D+e^2), with the original finite congruence-trace density D. The checked square-root estimates give 0<=rho_e-e<=a and D/rho_e<=a for every positive e. The actual retained-curvature identity and its nonnegativity imply Delta rho_e>=-|lambda|a/y^2. This strengthens the initial proposed lower bound using rho_e: the new forcing is independent of the regulator. Consequently the following argument applies to every positive regulator, not only e<=1.

Original uniform cusp decay of D implies uniform cusp decay of a. Unit horizontal averaging therefore gives e<=u_e(y)<=e+delta beyond one height independent of e, for every positive delta. Averaging the source Laplacian identity gives u_e''>=-|lambda|/y^2 beyond a fixed height where a<=1. The existing source theorems identify u_e' with the actual averaged vertical current and u_e'' with the averaged planar Laplacian.

For a function u with derivative v and v'>=-C/y^2, the checked corrected derivative v-C/y is monotone. Its forward and backward unit secants give

v(y)<=u(y+1)-u(y)+C/y,
u(y)-u(y-1)-C/(y-1)<=v(y).

If L<=u<=L+delta at these three heights, then |v(y)|<=delta+C/(y-1). Apply this with L=e, C=|lambda|, and the uniform source mean bounds. Choosing the height so that both delta and C/(y-1) are small proves uniform decay of the original averaged current over all positive regulators. Its checked equality with the centered Stokes top current gives the same uniform decay for that literal boundary term.

In the exceptional interval, subtract the actual truncated curvature identity from the proved full-domain identity. The resulting curvature outside the truncation is lambda times the corresponding regularized amplitude tail minus the actual top current. All functions are genuinely integrable from the previous source results, so subtraction of set integrals is justified. Since 0<=D/rho_e<=sqrt(D), the regularized amplitude tail is bounded by the fixed integrable original amplitude tail. That tail tends to zero by the actual domain exhaustion. The uniform current estimate therefore forces curvature tails uniformly to zero over all positive regulators.

## Exact total mass from compact orbit tests

Let K_Y be the literal closed modular cell below height Y. The original chart identities identify its complement with the planar tail exactly. The established compactness of K_Y and actual normalized-weight construction provide a nonnegative compact w with 0<=P(w)<=1 everywhere and P(w)=1 on K_Y. The original regularized hyperbolic curvature q_e is nonnegative and integrable over the full cell. Hence P(w)*q_e is also integrable, and

0<=integral_fd q_e - integral_fd P(w)*q_e <= integral_tail q_e.

Choose Y using the newly proved uniform tail bound before choosing w. The actual regulator limits are integral_fd q_e -> lambda*M and integral_fd P(w)*q_e -> 2*Q(P(w)), where M is the positive original amplitude mass. Passing the uniform inequality to the limit proves that, for every eps>0, such a nonnegative compact w satisfies

0<=lambda*M-2*Q(P(w))<eps.

Define the total orbit curvature as the supremum of Q(P(g)) over literal compact tests whose full orbit fields lie between zero and one. The earlier upper bound gives total<=lambda*M/2. The weights just constructed approach that upper bound arbitrarily closely, so total=lambda*M/2. This is the total of the compact-orbit functional, not the total measure of the full universal cover. The factor two is the previously proved full SL(2,Z) periodization multiplicity. Taking eps<lambda*M gives a nonnegative compact g with integral g dmu>0; thus the actual constructed curvatureMeasure is nonzero.

## Scope

Uniform tails, exact total orbit-functional mass, and nonzero limiting curvature are proved for every original Maass source in the exceptional interval. Mean/current uniformity itself holds for every real eigenvalue and every positive regulator. These theorems quantify over the existing MaassCuspEigenform structure; they do not construct an exceptional form or prove such forms impossible. Generic secant and cutoff comparison auxiliaries state their analytic premises explicitly, and the actual-source capstones discharge them. The spectral quarter lower comparison remains unproved. No entropy bound, physical evaporation law, pointwise limiting curvature density, or seam-null hypothesis is substituted for the original Maass identities.

## Corpus mechanisms

The explicit --any uniform-secant/one-sided-curvature/uniform-derivative/cusp-tail/uniform-tightness/tail-mass query reached 737 declarations in 176 modules. Coverage counts do not mean every source was read. Inspected source mechanisms: SelbergOneSidedCurvatureDecay's corrected derivative and two unit secants, SelbergSquareRootRegularizationError's original-amplitude domination, SelbergMaassRegularizedCusp's exact horizontal derivative identifications, and SelbergMaassFullCurvatureBudget's actual exhaustion and full-integrability results. The previous evaporation/entropy searches require any proposed tail law to be derived from the actual source; this proof does so through these checked Maass identities.

The explicit --any mass-supremum/total-mass/compact-cutoff/dual-norm/cofinal-mass query reached 540 declarations in 364 modules. WindowTotalSqueeze supplies the bounded-window plus uniform-tail mechanism; its source estimates must be established before transfer. RadialLeakageArcsineMeasure instead uses an explicit known density and antiderivative, so its density identification was not imported into the Maass argument. Actual compact orbit weights, chart transport, positivity, and the new source tails discharge the needed cutoff estimates here.

## Audit

All four complete scratch proofs and needed source olean checks passed without warnings. The modules are wired into RHTower exactly once each; no umbrella or full build ran. Serialized final audits each rebuilt only the requested module:

- SelbergOneSidedSecants: 3 public declarations, final build 1.6s; /tmp/selberg_secants38_build.log.
- SelbergMaassUniformCusp: 8 public declarations and 2 private helpers, final build 32s; /tmp/selberg_uniform_cusp38_build.log.
- SelbergMaassUniformCurvatureTail: 8 public declarations, final build 14s; /tmp/selberg_uniform_tail38_build.log.
- SelbergMaassQuotientMass: 14 public declarations, final build 12s; /tmp/selberg_quotient_mass38_build.log.

The last three builds replayed an existing EvenL2LogUnitary informational tactic suggestion; all four completed successfully without new module warnings. A /tmp-only #print axioms audit covered every public declaration: all 33 depend only on propext, Classical.choice, and Quot.sound. The four capstone signatures were also printed to check their actual Maass-source quantifiers. Audit: /tmp/selberg_uniform_mass38_axioms.log.

The refreshed corpus index contains all 33 public declarations and both private helpers; /tmp/selberg_uniform_mass38_corpus_audit.json records complete coverage. Repository formal lint passed with existing large-file warnings; /tmp/selberg_uniform_mass38_lint.log. Source/card/umbrella whitespace and exact umbrella import counts passed. Every task-owned handle is terminal; final process inspection found no Lean or Lake process. No task commit or push. Selberg's quarter conjecture remains unproved and active.
