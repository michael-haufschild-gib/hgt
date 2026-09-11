# PW-B source orientation attack

- **ID:** PW-B-SOURCE-2026-09-10
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** rh-current-frontier-map.md, PW-B; universal-law-field/STATUS.md
- **Statement:** Derive fixed-grade PW partner balance from the original source before specializing to Xi divisor copies.

## Proof chain and unresolved input

The existing first-winding PW imbalance is a positive multiple of horizontal
displacement and the negative of a positive multiple of the Deninger Ward charge.
Universal balance at one fixed grade is equivalent to RH. The missing theorem is
source-forced balance, not this equivalence. Singular source-adapted energy is
conserved off the wall; it does not supply balance.

## Current attack plan

1. Audit original complete-evaporation and reflection-orbit source identities.
2. Test a global balance conjecture; if reflected cancellation is nonselective,
   test nonlinear entropy production with every source term retained.
3. Search the whole indexed Lean corpus, proof methods, and broad recent arXiv
   literature for an independently justified source orientation or rigidity law.
4. Formalize only dependency-closed mathematical progress. Check scratch files
   with foreground `lake env lean`; one Lean process at a time. Audit finished
   leaf modules only, wire umbrellas without building them, and run formal lint.

No numerical experiments, added axioms, or unproved source premises are allowed.
The available tools do not expose `update_plan` or `multi_tool_use.parallel`;
this card persists the plan, and independent reads use `Promise.allSettled`.

## Evidence and iterations

- 2026-09-10: Read PW-B frontier, route-independent constraints and singular
  carrier/connection memories. Source balance remains open. Deep corpus query
  `recoil source orientation singular conservation` requested with 300-second
  budget. Broad arXiv searches started with entropy, holonomy, rigidity, and
  fluctuation; no applicable recent source theorem identified yet.

## Status

The two-orientation source-forcing audit is now closed in Lean. Positive-gain
reflection retains the nonzero Gamma forcing mismatch at every shift. The
inverse-gain companion fixes the source and has matching complete forcing at
every shift, but even its zero-shift forcing is nonzero. The full arithmetic
current transports with inverse dilations and the complete Möbius-log source;
the Gamma profile's exclusion from exponentially decreasing Schwartz sources
is proved. All 18 public theorems passed scratch/direct checking, the targeted
leaf build and axiom audit with only the three standard foundational axioms.
Formal lint, generated indices and source-name collision checks passed; the
umbrella is wired without building it, and all owned Lean processes finished.
See the [reflected-forcing audit](../3-formalized/pw-b-reflected-source-forcing.md).
The missing RH producer remains a full-source law eliminating the actual forcing.

The arithmetic-current follow-up is now closed in Lean: one prime-power term
test excludes every nonzero homogeneous shifted mode and gives uniqueness for
the complete forced response. The original Gamma source passes every such
test, while its singular reflection fails every one. All 15 public theorems
passed scratch/direct checking, the targeted leaf build and the axiom audit,
with only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint passed,
the umbrella is wired without building it, and generated indices were refreshed.
See the [arithmetic-current audit](../3-formalized/pw-b-euler-current-domain-uniqueness.md).
RH remains unproved; full-source reflected forcing and its arithmetic admission
or boundary correction remain open.

RH unproved. The original-source-square horizontal-energy counterexample and
exact density classification passed scratch and direct Lean checking, the
targeted final build, and an axiom audit of all 14 new theorems. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Formal lint passed; existing
repository size warnings remain. No conditional RH theorem was introduced.
The completed proof and exact scope are in
[the stage-3 card](../3-formalized/pw-b-source-square-horizontal-energy.md).

The subsequent all-complex-shift classification is also closed in Lean. Its
11 public theorems passed the scratch/direct checks, targeted leaf build, and
axiom audit with the same three foundational axioms. Formal lint passed again.
The source-square norm admits every shifted mode and its connection image;
reflection pairs opposite shifts with equal finite positive energy. See the
[shifted-mode audit](../3-formalized/pw-b-source-square-shifted-modes.md).

## Earlier conjecture tests

1. **Complete reflection-orbit balance forces individual balance:** rejected by
   `schwarzschildParikhWilczekBorelLinearOrbitAggregate_equalWeights`, which
   vanishes for every spectral parameter, independently of critical-line
   membership. Positive quadratic energy survives, but its universal vanishing
   remains RH-equivalent.
2. **Full self-similar evaporation dissipates the imbalance:** rejected by the
   exact complete-evaporation formula, which is only the positive lifetime
   `1/(3*alpha)` times the unchanged phase. Genuine source mixing would need
   its own equation.
3. **The reflected-Fermi gradient transports zeros of the unchanged source to
   the critical line:** rejected by the existing same-source divisor theorem.
   Such continuous divisor families are constant; universal gradient
   realizability is already RH-equivalent. Constructing an inward ambient
   gradient does not prove its realization on the divisor.

The PW balance equivalence and these existing obstructions were independently
checked in `/tmp/pwb-source-audit.lean`; their axiom lists contained only
`propext`, `Classical.choice`, and `Quot.sound`. These are validations of prior
results, not new proofs of the missing source law.

## Search coverage and next mathematical step

Four deep queries and two targeted lexical queries were executed. Deep queries
returned both proof-source and stored method matches. The proposed ingredient
sets were rejected where they assumed orientation, exchangeability or zero
entropy production rather than deriving it. Saved evidence:
`pw-b-source-orientation-searches.json`. Semantic coverage was incomplete, and
two deep searches reached their deadlines; absence from those responses does
not establish absence from the corpus.

The remaining proof chain is unchanged: original-source global law -> fixed-grade
partner balance -> zero Deninger Ward charge -> RH. A further weak-flux attack
must construct the current from the actual arithmetic source, prove its endpoint
fluxes, and exclude the nonzero homogeneous profile in that exact current/domain.
The source-square norm alone cannot provide that exclusion. Iteration 6 supplies
an exclusion for the literal arithmetic current, while exposing a new failure
of reflection to preserve its necessary admission condition.

## Iteration 4: averaged singular-energy rigidity

The August 2026 paper [Critical Morrey Rigidity and Removable Singularities for
Five-Dimensional Stationary Navier--Stokes Flows](https://arxiv.org/html/2608.29664v1)
separates averaged flux control from a theorem excluding nonzero zero-defect
tangents. Test the analogous proposed PW inference: a horizontal section with
bounded adapted mean energy must vanish.

**Paper refutation and positive survivor.** Write
`phi(t)=sinh(t)-t/2`, `g(t)=exp(phi(t))`, and `a(t)=g(t)^2`.
The corpus proves `g'=(cosh(t)-1/2)g` and classifies all horizontal sections
as `f=c*g`. For every even positive density core `h`, the reflection-unitary
weight is `w=a^(-1)*h`. Consequently `w*f^2=c^2*h` exactly. For `h=1`,
every interval has weighted energy `c^2*(b-a)`, so bounded mean energy admits
nonzero zero-defect profiles. For `h=exp(-t^2)`, the same strictly positive
horizontal section has finite total adapted energy `sqrt(pi)`, although its
unweighted square is not integrable. It is also fixed by weighted reflection.

The survivor is an exact energy-density classification, not merely a failed
inequality. An arbitrary positive reflection-unitary density cannot provide a
Liouville theorem for this connection. This does not contradict the existing
neutral-L2 exclusion and does not establish a Fredholm index in a changed norm.
The physical source still must specify its norm and exclude its actual nonzero
zero-defect profiles. The strengthened source-square version below is verified
in Lean; the intermediate Gaussian witness was not added to the tree.

**Source-specific strengthening, paper proof.** The Gaussian core was only an
intermediate test. Use the existing original Gamma log profile itself,
`q(t)=exp(t/2-exp(t))`, and choose its square `w(t)=q(t)^2`. Its exact even core
is `a(t)w(t)=q(t)q(-t)=exp(-2 cosh(t))`. Thus this source-derived density is
reflection-unitary and gives `w(t)(c*g(t))^2=c^2 exp(-2 cosh(t))`.
The core is integrable without numerical estimates: `exp(-2 cosh(t))` is bounded
by `exp(t-exp(t))`, whose integral is already proved finite in the corpus;
the comparison follows from `exp(-t) >= 1-t`. The nonzero section `g` is fixed
by exact weighted reflection and solves the horizontal equation. Therefore
even this literal source-square choice admits a nonzero finite-energy
zero-defect section. The source-normalized *vanishing* theorem still fails for
this candidate norm. This is not an identification of the physical Hilbert
space, a statement about its adjoint, or a proof of a nonzero Fredholm index.

The final Lean candidate retains the general density classification and flat-core
interval law, and strengthens the Gaussian witness to this original-source-square
witness. The intermediate Gaussian construction will not be added to the tree.

## Iteration 5: source-square spectral admission and adjoint test

The unshifted counterexample raises a sharper conjecture: finite energy might
still exclude non-neutral connection shifts. The explicit solution
`f_z=exp(phi+z*t)` refutes this on paper for every `z in C`, since its source
weighted squared norm is `exp(-2*cosh(t)+2*Re(z)*t)` and has finite positive
integral. Reflection takes `f_z` to `f_(-z)` with equal total energy. The exact
solution space is the complex line generated by `f_z`. The proof and completed
Lean audit are recorded in
[the shifted-mode card](../3-formalized/pw-b-source-square-shifted-modes.md).

The adjoint corpus search found actual Hedenmalm closed-derivative and translated
cokernel theorems. Their reciprocal-theta measure and source domain differ from
the present Gamma-source-square connection; there is no proved identification.
Transferring their kernel/index statements would therefore insert an assumption.
Broad arXiv supersymmetry search found Kapranov's August 2026 theta DOI paper.
Its discrete exponential fixed-point equations do not say the infinitesimal
generators annihilate theta, and no exact Mellin/PW transmutation has been found.
The four new deep searches also inspected stored proof methods; coverage remains
partial. Full declarations, stored methods, proposed ingredient sets and coverage
are saved in `pw-b-shifted-source-searches.json`. No reported ingredient set
independently produces the required balance.

The arithmetic follow-up read the exact Möbius--von Mangoldt connection, the
Möbius--Fourier commutator and its complete kernel classification. They already
retain the full arithmetic source: the current is a Möbius logarithmic derivative,
and the commutator vanishes exactly on Poisson boundaries. Selecting such a
boundary does not identify the original PW response or derive its individual
partner balance. A surviving attack must prove that exact source identification
and retain any boundary/prime terms in the transmutation. Neither Fourier
covariance nor the existence of a large known kernel supplies the identification.

## Iteration 6: literal arithmetic current and forced uniqueness

**Conjecture:** the arithmetic current's necessary term test can exclude the
all-shift homogeneous survivors. **Paper proof:** on any one prime-power ray,
the exact coefficient is the positive constant `log(p)` and the sampled
log-coordinate tends to infinity. Every nonzero shifted homogeneous mode grows
there. Thus even that restricted term-decay test forces a homogeneous response
to vanish. Subtracting two complete forced equations gives uniqueness when both
responses satisfy this arithmetic admission. The original Gamma profile does
satisfy every such test, so this is a nontrivial domain.

**Next conjecture:** use uniqueness to identify a response with its reflected
partner. **Refutation:** the singular reflection of that same Gamma profile has
norm tending to infinity. Its arithmetic current fails every prime-power term
test. The domain required for uniqueness is not preserved by reflection.
The exact survivor is forced-response uniqueness with its admission obligations
retained. This domain also excludes critical-line homogeneous shifts, so it
cannot be declared a Xi occurrence domain.

Paper proof and current verification status:
[arithmetic current card](../3-formalized/pw-b-euler-current-domain-uniqueness.md).
Four additional deep searches inspected declarations, source arguments and
stored methods; partial coverage and candidate ingredient sets are saved in
`pw-b-arithmetic-current-searches.json`. Broad arXiv searches found a July 2026
exterior-comparison method retaining full forcing and circulation. The comparison
motivates a homogeneous difference, but its nonlinear elliptic hypotheses are
not identified with this source.

The remaining hard step is the source-derived reflected forcing and its correct
admission or boundary correction. It must produce individual partner balance;
the new uniqueness result alone does not remove that forcing or correction.

For the next source-level test, differentiation of the explicit Gamma profile
suggests the forcing `r_z(u)=(1-exp(u)-cosh(u)-z)*q(u)`. Transporting the full
forced connection through singular reflection should give
`L_(-z)(Tq)=-T(r_z)`. At a common shift, an extra `-2*z*Tq` remains. This must
be checked against the literal source derivatives and full arithmetic current;
neither equality of forcing nor cancellation of its source terms is assumed.
The literal current also changes dilation direction under reflection. For
`D_n f(t)=f(t+log(n))` with `n>0`, direct substitution gives
`T(D_n f)(t)=a(t)/a(t-log(n))*D_(1/n)(Tf)(t)`. A full-current successor must
retain these inverse dilations and gain ratios and identify the canonical
Möbius preimage; the termwise identity alone supplies no balance law.

## Iteration 7: full reflected forcing and inverse-dilation current

**Conjecture:** a shift or exact reflection covariance might make the original
Gamma source and its reflection solve the same complete forced equation.
**Paper refutation:** the transformed equation is `L_(-z)(Tf)=-T(L_z f)`;
at the same shift it retains an additional `-2*z*Tf`. For the original Gamma
profile the forcing is `(1-exp(t)-cosh(t)-z)*q(t)`. At `t=0`, its difference
from the reflected same-shift forcing is `-2*exp(-1)` at every complex shift.

**Stronger positive companion:** the exact carrier identity is `a*q=q(-t)`.
Consequently the inverse-gain reflection `R f=a^(-1)*f(-t)` fixes `q`.
For the inverse connection its forcing is `(-sinh(t)-z)*q(t)`, and the complete
same-shift forcing covariance holds for every complex `z`. Source fixation is
therefore restored without selecting a shift. At `z=0`, the forcing remains
the nonzero function `-sinh(t)*q(t)`. The no-go for positive-gain `T` is not
transferred to this different companion `R`.

**Positive survivor:** the complete arithmetic conjugation preserves all
coefficients and changes outgoing dilation into inverse dilation with ratio
`a(t)/a(t-log(n))`. The two term families differ by one nonzero constant at a
fixed base point, so their summability is equivalent. Transport of the existing
canonical Möbius connection keeps its full Möbius-log derivative source.
This identifies the correct transformed current, without asserting that the
outgoing current of the reflected function is summable or that forcing vanishes.

**Source-domain check:** the Gamma profile's unit-exponent weighted negative
tail is unbounded, so it is not an exponentially decreasing Schwartz source.
The existing Deninger connection theorem cannot be specialized to it through
that source class. Four deep searches and one lexical search inspected source
arguments and stored methods; a fifth deep search audited inverse-gain source
fixation. Partial coverage is saved in
`pw-b-reflected-forcing-searches.json`. Broadening a no-hit lexical query found
`TwistedMobiusMellin.lean` and `MobiusLaplaceLandauOscillation.lean`. Their
ordinary Möbius--Laplace source has Mellin transform `Gamma(s)/zeta(s)` on its
absolute-convergence half-plane. It differs from the canonical Möbius dilation
of the half-density Gamma profile, whose coefficients include `sqrt(n)`.
These sources must not be identified by notation alone.

The old forced-response uniqueness theorem concerns `L_z=deriv-p-z` and its
outgoing arithmetic term test. It is not automatically a theorem about the
companion connection `deriv+p-z`. Its homogeneous candidate
`exp(-phi(t)+z*t)` decays at the outgoing end at every complex shift, so that
admission question must be checked afresh before invoking uniqueness for `R`.

Paper proof and current Lean audit:
[reflected-forcing card](../3-formalized/pw-b-reflected-source-forcing.md).
The next mathematical obligation is an exact one-sided Gamma/Möbius source
extension, including its half-density factors, followed by a source-derived
boundary correction or balance law. Known Mellin identities and transport
alone do not produce the missing Ward cancellation.

## Iteration 8: the actual half-density Gamma/Möbius current

**Conjecture:** the canonical Gamma source has a well-defined Möbius preimage
and full Euler current even though its negative log-tail fails the old
exponentially decreasing Schwartz admission. The needed product-fibre proof
uses only a bound on the positive ray, so that stronger source class can be
removed for this explicit source.

**Paper mechanism:** write `Q(y)=exp(log(y)/2-y)` for `y>0`. The tangent
inequality for the exponential gives, for any `c>0`,
`c*u-exp(u) <= c*log(c)-c`. At `c=5/2`, this yields
`Q(y) <= C/y^2`, with explicit positive
`C=exp((5/2)*log(5/2)-5/2)`. Hence the double family
`b(m)*mu(n)*Q(m*n*x)` is absolutely summable for `x>0` whenever `b(0)=0`
and `sum |b(m)|/m^2` converges. Apply this to the positive-integer unit
weights and to `vonMangoldt`. Product fibres then give both the exact
Möbius right inverse and its full Möbius-log Euler connection. No reflection
or spectral premise enters the bounds or divisor identities.

The source is `sqrt(x)*sum mu(n)*sqrt(n)*exp(-n*x)`, not the ordinary
Möbius--Laplace transform. The right inverse will certify that it is nonzero;
absolute convergence alone must not be presented as the missing balance law.

**Execution:** formalize the explicit bound in scratch, prove the shared
two-variable majorant, close both divisor identities and nontriviality,
then audit the inverse-connection homogeneous modes. The companion domain
question remains distinct from the already proved positive-connection
uniqueness theorem. The source extension, complete current and actual reflected
transport are now verified in Lean: 15 public theorems, scratch and direct
checks, targeted final build, standard-axiom audit and lint passed.
[Paper proof and audit](../3-formalized/pw-b-gamma-mobius-current.md).
The arithmetic current is not identified here with the differential forcing
of the Gamma profile or its Möbius preimage.

Broad searches on polymers, resetting, coercivity and pinning were followed
to primary July/August 2026 arXiv abstracts. Ishizaka's
[memory coercivity paper](https://arxiv.org/abs/2607.12482) distinguishes
dissipation from frequency-uniform coercivity; Li and Wu's
[ENO parity paper](https://arxiv.org/abs/2607.19283) retains polynomial-kernel
obstructions when deriving positive estimates. Wang and Ye's
[pinning paper](https://arxiv.org/abs/2607.19732) separates translational
covariance from a bulk barrier. These suggest auditing a retained kernel
before claiming shift selection. Their hypotheses have not been identified
with the PW source; no external theorem is used as a Lean premise.

Three further corpus/deep searches inspected declarations, source arguments,
stored methods and proposed ingredient sets. Coverage remains partial and is
saved in `pw-b-gamma-current-searches.json`. The gapped pseudo-inverse method
requires symmetry, a specified kernel and a transverse coercivity bound; none
of those operator-domain hypotheses is supplied here. Polynomial-growth
classification likewise requires an entire-function growth bound. Neither
method is a source of the missing Ward cancellation.

## Next attack: inverse-connection admission and the actual boundary class

**Candidate to test:** perhaps the outgoing Euler-current domain supplies the
inverse connection with the uniqueness already proved for the positive
connection. **Paper failure:** for every complex `z`,
`fminus_z(u)=exp(-phi(u)+z*u)` is a nonzero inverse homogeneous solution,
and its complete outgoing Euler current converges. This is stronger than
passing a single prime-power term test, but still requires Lean verification.

For a fixed base `t`, put `A=Re(z)+1/2`, `c=|A+2|+1` and `kappa=exp(t)/2`.
For every integer `n>=1`, direct substitution gives

`n^2*|fminus_z(t+log(n))|`
`= exp(A*t+(A+2)*log(n)-kappa*n+exp(-t)/(2*n))`.

The same exponential tangent bound used in iteration 8 bounds this by
`exp(A*t+exp(-t)/2+c*log(c)-c-c*log(kappa))`, uniformly in `n`.
The known convergent series `sum Lambda(n)/n^2` therefore admits every shift.
This must not be declared a closed-domain spectrum or Xi occurrence theorem.

**Positive successor:** the actual Möbius source has additional boundary
information which this outgoing admission forgets. Its explicit positive-ray
majorant can give a uniform inverse-square bound toward zero; inverse
homogeneous modes instead grow faster than any inverse power there. Thus a
source-derived condition at that second end may restore forced uniqueness.
The proof must then derive the reflected complete forcing and retain any
boundary correction. Even such uniqueness would not by itself force that
forcing or a Ward charge to vanish. Next Lean work should first audit the
all-shift outgoing counterfamily, then derive the actual source's second-end
bound before making any comparison of reflected forced responses.

There is also a direct test of the retained **actual arithmetic forcing**.
Put `Z F(x)=sum_(m>=1) F(m*x)` and `J F(x)=sum_n Lambda(n)*F(n*x)`.
The new identities are `Z M=Q` and `J M=E`. A uniform bound
`|M(x)| <= (C*sum_n 1/n^2)/x^2` follows by summing the explicit source
majorant. It would justify the double-current interchange `Z(J M)=J(Z M)`.
Hence the proposed next exact survivor is
`Z E=J Q`, whose right side is strictly positive for every `x>0` because
`Q` is positive and any prime contributes a positive von Mangoldt term.
This would prove that the complete Möbius-log forcing is not identically
zero, without assuming any sign for `E` at individual points. The uniform bound, interchange, strict positivity and nontriviality are now
verified in the successor
[positive-reconstruction leaf](../3-formalized/pw-b-gamma-forcing-positive-reconstruction.md). A positive
aggregate must not be substituted for the required individual PW balance.

## Iteration 9: actual forcing reconstruction and its positive aggregate

**Active conjecture:** the complete arithmetic forcing might vanish after
correct source admission. **Paper refutation to formalize:** prove the uniform
bound on `M`, use it to commute `Z` and `J` as absolutely convergent double
currents, and obtain `Z E=J Q`. The right side is strictly positive at every
positive base point. Hence `E` cannot vanish on a whole dilation ray; indeed,
it has a positive real value arbitrarily far along the positive ray. This
strengthening must retain summability and the complete prime weights.

**Plan:** check current corpus methods and source bounds; prove the uniform
inverse-square majorant in scratch; prove double-current admission and exact
commutation; prove strict positivity and the strongest forced nonvanishing
statement; perform leaf, axiom and lint audits. Do not identify this arithmetic
forcing with a differential forcing, and do not replace individual PW balance
by positivity of its dilation sum. The next boundary comparison must carry
the surviving nonzero source contribution.

The quantitative positive survivor includes every prime lower bound
`Re(Z E(x)) >= log(p)*Q(p*x) > 0`, not merely nontriviality of one sum.
The proof now closes this identity, uniform admission and positive values
on every dilation ray in Lean. All 12 public theorems passed scratch and
direct checking, the targeted final build, the standard-axiom audit and
formal lint. The module is umbrella-wired and indexed; owned Lean processes
finished. [Paper and verification](../3-formalized/pw-b-gamma-forcing-positive-reconstruction.md).

**Next source comparison:** determine the leading prime in the forcing
itself, before proposing a cancelling reflected contribution. The candidate
limit is `E(x)/Q(2*x) -> log(2)` as `x -> infinity`. For `n>=2`, the
normalized term is `-mu(n)*log(n)*sqrt(n/2)*exp(-(n-2)*x)`; the first two
arithmetic indices vanish and the index-two term is exactly `log(2)`.
For `x>=1`, all remaining terms are dominated by
`exp(2)/sqrt(2)` times the absolute summands of the already convergent
series `E(1)`. Each index above two tends to zero. The current mathlib
`tendsto_tsum_of_dominated_convergence` in
`Analysis/Normed/Group/Tannery.lean` and the source argument in
`NumberTheory/LSeries/Injectivity.lean` expose this mechanism with the
uniform majorant retained. This limit and the implied eventual positivity
of `E` are paper candidates, not yet Lean claims of the current leaf.
Matching this outgoing term against a reflected source still requires
control at the opposite end; neither the prime floor nor the proposed
limit provides that control or individual PW balance.

## Iteration 10: leading-prime forcing and endpoint comparison

The active target is the exact outgoing limit `E(x)/Q(2*x) -> log(2)`.
Normalize each summand at the already admitted base `x=1`: its coefficient
is `-mu(n)*log(n)*Q(n)/Q(2)`, multiplied by
`exp(-(n-2)*(x-1))`. Indices zero and one vanish; the multiplier has norm at
most one for every other index and `x>=1`. This gives one fixed summable
majorant and exposes the prime-two coefficient. The proof will use current
mathlib Tannery and verify the exact Gamma scaling identity in scratch.
After the limit, derive eventual positivity and the necessary leading term
of any cancellation. Separately test the reflected endpoint; outgoing
dominance alone does not control the small positive ray. The missing link
remains a source-derived complete balance law, including this forcing.

The conjectured limit, eventual positivity and `E(x)/Q(x) -> 0` now pass
scratch and direct Lean checking. The raw differential-forcing
identification was then tested and fails for every complex shift: in scale
`exp(t)*q(t)`, `E(exp(t))-rminus_z(t)` tends to coefficient `1/2`, and
`E(exp(t))-rplus_z(t)` to `3/2`. These exact nonzero defects are the positive
survivor; a correction negligible in that scale cannot repair the equality.
For inverse gain, `R f(t)/q(t)=f(-t)/q(-t)`, so the reflected arithmetic
quotient tends to zero at the opposite end. This is not a bound on the
unreflected current at zero. The
[new leaf](../3-formalized/pw-b-gamma-leading-forcing.md) has 12 public
statements. Final targeted build, all 12 axiom checks, formal lint,
index, name-collision and diff audits passed. Only the standard three
axioms occur; all owned Lean and search processes finished. The leaf is
umbrella-wired; no umbrella/full build ran. Five deep searches and their
partial-coverage/method audit are retained in
`pw-b-gamma-leading-searches.json`.

## Next attack: the arithmetic current's own parameter generator

The spatial Gamma connection and the arithmetic Möbius-log derivative
are distinct operations. The current `DeningerMobiusConnection.lean`
defines its derivative by the full coefficients `-mu(n)*log(n)`, and its
connection proof is arithmetic convolution, not a spatial derivative.
The next candidate is an actual coefficient deformation

`M_b(x)=sum_n mu(n)*exp(-b*log(n))*Q(n*x)`.

At `b=0`, this is the canonical source `M`, and termwise differentiation
gives precisely `E`. To turn that calculation into a proof, use a fixed
neighborhood `|b|<1` and an admitted derivative majorant. For `n>=1`,
`|exp(-b*log(n))|<=n` and `log(n)<=n`, so the derivative is bounded by
`n^2*Q(n*x)`. The factor `n^2*exp(-n*x/2)` is uniformly bounded by the
exponential tangent inequality, while `Q(n*x/2)` is summable. This supplies
a concrete path to the needed uniform bound without assuming an analytic
interchange. Current mathlib
`hasDerivAt_tsum_of_isPreconnected` exposes precisely convergence at one
point, term derivatives and a common summable derivative bound.

This successor is a paper candidate, not an established selective law.
The full tilted convolution would give `J_b M_b = partial_b M_b`, with
weights `Lambda(m)*m^(-b)`. Any later connection to the spectral Ward
parameter must derive that parameter identification and the complete
reflected source law. Merely naming `b` a spectral parameter cannot force
balance or select the critical line.

The follow-up deep search found a prior analytic realization:
`DeningerAdiabaticGreenStokes.lean:428` proves
`hasDerivAt_deningerAdiabaticEvenPreimageLpExt` for `DeningerMeyerSource`
and `a>0`. Its derivative majorant requires `b>=d>0` and sums
`log(n)/n^(d+1)`; the associated almost-everywhere Euler identification is
at line 477. Thus the parameter-generator mechanism already exists, but
the zero-parameter actual Gamma specialization is not licensed. The next
attack should transfer the uniform-derivative argument to the explicit
Gamma series near zero, keeping pointwise and `L¹` admission distinct.

## Iteration 11: actual Gamma parameter derivative across zero

Current mathlib supplies `Real.summable_pow_mul_exp_neg_nat_mul`, so the
polynomial moments of the Gamma ray source can be admitted directly.
The strengthened candidate is complex differentiability at every coefficient
parameter `b`, not only a one-sided real collar: define the exact tilt by
`exp(-b*log(n))`, prove a polynomial majorant on each bounded complex
parameter ball, and differentiate the full series there. At zero the
derivative must be the already nonzero forcing `E`. This attacks the missing
generator identification while testing whether analytic admission itself
selects a parameter. The actual spectral Ward identification and complete
source balance remain separate open obligations.

The strengthened actual-source theorem now passes scratch and direct Lean
checking: every complex coefficient parameter is admitted at each fixed
positive scale, and the full series is complex differentiable everywhere.
At zero its derivative is exactly `E=J M`, with the original source
`M_0=M` and full convergent Euler current retained. The derivative has
positive real part for sufficiently large ray scales, so the family is
nonconstant there. The positive survivor is the exact generator identity
and its nonstationarity, not a restriction on admissible parameters.
The [parameter-generator leaf](../3-formalized/pw-b-gamma-parameter-generator.md)
contains 14 public theorems and two definitions; final targeted build,
all 14 axiom checks, formal lint, index, name-collision and diff audits
passed. Only the standard three axioms occur; all owned Lean and search
processes finished. Umbrella wired; no umbrella/full build ran.

## Next attack: global endpoint of the actual tilted source

Current corpus evidence makes the remaining global obligation explicit.
`MobiusLaplaceCriterionFrontier.lean:45` defines the ordinary source
`sum mu(n)*exp(-n*x)`; its Mellin identity at line 1235 assumes `Re(s)>1`.
`MobiusLaplaceMellinPlancherelBridge.lean:709` extends a denominator-free
identity only from a proved `MemLp` base-energy premise. The zero-exclusion
theorem at line 751 retains that premise. None can be invoked from
pointwise entire parameter admission alone.

The next exact candidates are
`M_(1/2)(x)=sqrt(x)*mobiusDiscreteLaplaceTransform(x)` and
`Mellin(M_b)(s)=Gamma(s+1/2)/zeta(s+b)` when
`Re(s)>-1/2` and `Re(s+b)>1`. The half-density shift and both convergence
conditions must be proved, not suppressed. The Mellin series/integral
interchange needs an integrable common bound over the entire positive ray.
Moving that global source class toward the zero-bearing region requires
new signed arithmetic cancellation, not a renamed conditional RH endpoint.

Five partial-coverage deep searches and the prior-method audit are saved in
`pw-b-gamma-parameter-searches.json`. A broad entrainment search found
arXiv:2607.25435 (July 28): its weighted telescoping and periodic quadratic
energy method has a sharp zero-deficit classification, but requires positive
chain states, specific flow equations and periodic endpoint matching.
Those hypotheses have not been derived from the signed arithmetic source;
discarding the Möbius signs to obtain them would change the problem.

**First global candidate to test:** the sum of the termwise `L¹(dx)` norms
has an exact admission boundary `Re(b)>0`. With
`C=integral_(x>0)|Q(x)| dx>0`, its terms are
`C*|mu(n)|/n^(Re(b)+1)`; derivative terms have the additional `log(n)`.
The sufficiency bounds are p-series/log-p-series; necessity for `Re(b)<=0`
uses prime coefficients `|mu(p)|=1`, `log(p)>=log(2)>0`, and divergence
of `sum_p 1/p`. The current corpus uses `Nat.Primes.not_summable_one_div`
in `Sieve/FullPrimeCofactorBoundary.lean:292`; the underlying mathlib module
is `NumberTheory/SumPrimeReciprocals.lean`.
This is still a paper candidate. Failure of the absolute sum of term norms
must not be promoted to failure of `L¹` for the signed summed source.
The sharp boundary would identify exactly where absolute admission stops
and a new signed global estimate is required, before attempting Mellin
continuation or an RH consequence.


## Iteration 12 — exact global absolute admission (audited)

Conjecture: for the actual atoms `mu(n)*exp(-b*log(n))*Q(n*x)`,
the sum of their `L¹(dx)` norms on `x>0` converges iff `Re(b)>0`.
The same classification should hold for the full logarithmic derivative
atoms. Plan: evaluate the Gamma norm mass and dilation exactly; prove
sufficiency with p-series and the existing logarithmic p-series estimate;
restrict necessity to primes, where `|mu(p)|=1` and `log(p)>=log(2)>0`.
Then audit the resulting positive admission region and exact endpoint
failure in Lean. A separate signed-cancellation search tests whether the
summed source itself can cross this absolute boundary. Failure of the
sum of atom norms does not decide the integrability of the signed sum.


### Signed successor exposed by the absolute boundary

The exhaustive source-text pass located a concrete positive successor:
`DeningerMertensInvSquare.lean:131` proves unconditionally
`sum |Mertens(n)|/n^2 < infinity`, and
`Sieve/MoebiusHarmonicArbitraryLogRate.lean:61` proves every fixed
inverse-logarithmic saving. These are current corpus statements, not
assumed square-root cancellation.

For the literal Gamma ray, `Q'(y)=(1/(2*y)-1)*Q(y)` on `y>0`, hence
`integral y*|Q'(y)| dy <= Gamma(3/2)/2+Gamma(5/2) < infinity`.
The adjacent dilation window has the exact mass bound
`integral |Q((n+1)*x)-Q(n*x)| dx <= C1/(n*(n+1))` for `n>=1`.
Finite Abel summation gives
`M(x)=sum Mertens(n)*(Q(n*x)-Q((n+1)*x))` after checking the terminal
term; the existing inverse-square Gamma bound and linear Mertens bound
make that pointwise terminal term tend to zero. The reassembled series
then has summable termwise L1 norms, even though the original atoms do not.
This is the next exact formalization target. Its integral should be zero
by the existing harmonic Möbius limit, with the terminal term retained.
The window estimate is already available for Schwartz log sources, but
its literal Gamma admission or a direct C1 version must be checked in Lean.
No signed Gamma endpoint theorem is claimed completed by the current leaf.


The successor must keep its strength explicit. Extending the absolute
region to the signed boundary `Re(b)=0` would use the corpus's existing
PNT-strength cancellation. It would not supply any fixed negative-power
gain. The proposed Mellin identity remains
`Mellin(M_b)(s)=Gamma(s+1/2)/zeta(s+b)` in its initial absolute region.
After a justified continuation, global `L¹(dx)` admission at a negative
real `b` would put the corresponding Mellin line at `Re(s)=1`, exposing
zero exclusion to the right of `1+b`. Approaching `b=-1/2` would therefore
require substantially stronger signed cancellation. This is a mechanism
audit and next target, not a proved continuation or RH consequence.


**Iteration 12 result:** the exact conjectured boundary is now closed in
`ThetaCuspHawkingParikhWilczekGammaMobiusGlobalAdmission.lean`, with
15 public theorems and two definitions. The positive survivor includes
integrability and exact series/integral interchange for both complete
sources throughout `Re(b)>0`; the closed capstone has no unproved premise.
Scratch, direct file, targeted final build, all 15 axiom audits, formal
lint, index, all-name and task-scoped whitespace audits passed. Only the
standard three axioms occur. Umbrella wired; no full/umbrella build ran.
All owned Lean and research processes finished. RH remains unproved.
The next hard source-specific task is the signed Gamma Abel assembly at
zero, with its derivative window, terminal term and actual source equality.


## Iteration 13 — signed Gamma endpoint assembly (audited)

Attack the actual zero-parameter source, not an assumed stronger class.
A direct factorization of the square-root and exponential increments gives
`|Q((n+1)*x)-Q(n*x)| <= (1/n+x)*Q(n*x)` for `n>=1,x>0`.
Its integrated cost is `(Gamma(3/2)+Gamma(5/2))/n^2`, sufficient for the
already-proved unconditional inverse-square Möbius summability.
Plan: check this literal bound and its Gamma moments; construct all Abel
atoms with zero index handled; prove the exact finite identity and vanishing
terminal term; identify the full sum, global L1 admission and zero mass.
The source is known nonzero, so zero mass must remain a signed statement.


The signed admission argument also exposes an exact reconstruction test.
If the actual preimage is integrable with zero mass, every positive dilation
has zero mass by the same Jacobian law. But the complete admitted arithmetic
reconstruction `Z M=Q` has mass `Gamma(3/2)>0`. Thus its source-level
series/integral defect is exactly `Gamma(3/2)`; the sum of the reconstruction
term norms cannot be integrable. Both source and reconstructed output can
be globally integrable while that interchange fails. This complete defect
is being checked with the signed endpoint, not discarded as a formal zero.

The next derivative-current candidate is simpler than introducing a new
logarithmic summatory function. Apply finite Abel summation to
`F_n(x)=-log(n)*Q(n*x)` with the original Möbius partial sums. The new atom
is `Mertens(n)*(log(n+1)*Q((n+1)*x)-log(n)*Q(n*x))`.
Split it into `log(n)` times the Gamma difference and the log increment
times the adjacent Gamma dilation. Its norm integral is bounded by
`|Mertens(n)|*(C*log(n)+Gamma(3/2))/n^2`, using
`log(n+1)-log(n)<=1/n`. The required logarithmically weighted inverse-square
summability should follow from the current inverse-log Mertens rate.
The corpus theorem `Sieve.tendsto_moebiusLogHarmonicPartial_one`
(`Sieve/MoebiusLogarithmicNormalization.lean:346`) supplies the candidate
integrated value `Gamma(3/2)` after all terminal and interchange checks.
No global theorem for the actual derivative current is claimed yet.


**Iteration 13 mathematical result:** the literal endpoint is now proved
in `ThetaCuspHawkingParikhWilczekGammaMobiusSignedEndpoint.lean`.
The direct pointwise Gamma increment estimate and both Gamma moments
supply the complete norm majorant. The finite Abel identity and terminal
decay identify the original source with its integrable signed assembly.
Its mass is zero, its L1 norm is strictly positive, and its complete
arithmetic reconstruction is integrable with mass `Gamma(3/2)`.
All positive source dilations have zero mass. The exact reconstruction
series/integral defect is therefore `Gamma(3/2)`, and its term norm
integrals cannot be summable. This is a complete source contribution,
not an RH balance law. The source and its arithmetic operator must be
admitted separately. Scratch, direct check and targeted build passed;
all 22 public axiom audits, formal lint, index, all-name and task-scoped
file audits passed. Only the standard three axioms occur. Umbrella wired;
no full/umbrella build ran. All owned Lean and research processes finished.
RH remains unproved. The next source-specific target is the full
logarithmic-current Abel assembly, its global admission and integrated
value, before attempting spectral Ward identification.

## Iteration 14 — literal logarithmic-current global mass (audited)

Conjecture from the current corpus: the complete actual logarithmic current
`E(x)=sum -mu(n)*log(n)*Q(n*x)` is globally L1 and has integral Gamma(3/2).
Use the original Mertens partial sums and the difference of
`log(n)*Q(n*x)`. Four inverse logarithmic powers absorb the added logarithm;
the remaining inverse-cubic logarithmic tail is summable. Keep two terminal
checks separate: the pointwise Gamma terminal and the integrated scalar
terminal `Mertens(N)*log(N)/N`. Identify the latter limit from the same
unconditional saving and the existing logarithmic Möbius normalization.
Then test the full Euler-current interchange, whose individual source
terms still have zero integral. This attacks global source admission and
the complete boundary contribution, not the still-missing spectral Ward
identification or RH balance.

Two deep method searches completed with partial coverage (723052 indexed
declarations; 706108 ready methods). They retrieved the usable four-log
Mertens saving and logarithmic normalization; unrelated prime estimates
and generic log derivatives do not discharge the actual source obligations.
Broad wetting searches yielded arXiv:2607.13606 (July15) and 2609.01444
(September1), whose primary abstracts were read. Dynamic contact-line
reconstruction and precursor-film replacement are numerical fluid methods;
no transferable arithmetic estimate or Ward theorem was established.

**Iteration 14 mathematical result:** the literal logarithmic current is
now proved globally L1 with integral Gamma(3/2). The new log-weighted
inverse-square Mertens summability, scalar terminal, pointwise Gamma
terminal, finite Abel identity, all atom admissions and exact integrated
logarithmic harmonic limit are retained. The actual full Euler current
has this same positive mass, while each individual current term has zero
mass; its exact series/integral defect is Gamma(3/2), and term norm
integrals are not summable. The complete difference E-Q is integrable
with zero total mass. Scratch, direct check and targeted leaf build passed;
all 23 public axiom audits, formal lint, index regeneration and all-name
checks passed. Only the standard three axioms occur. Umbrella wired;
no full or umbrella build ran. All owned Lean and research processes
finished. The one definition and 23 theorem declarations are indexed.
RH remains unproved and the goal remains active.

A third deep method search found generic dilation identities and abstract
adjoints, but no source-specific spectral matching. Broad anomaly and
reciprocity searches read arXiv:2609.06632 (September6, including primary
HTML) and 2608.30778 (August31). The first retains a complex correction
in its fluctuation identity; the second requires adjoint matching beyond
conservation for its response classification. These provide no arithmetic
or spectral theorem here; preserve the complete correction and explicitly
prove matching rather than importing a formal stationarity analogy.

**Iteration 15 target (now audited below):** compare the
actual current's mass to the two already-defined raw differential
forcings, keeping dx and x=exp(t). The source formulas become
`rminus_z(log x)=((1/x-x)/2-z)*Q(x)` and
`rplus_z(log x)=(1-3*x/2-1/(2*x)-z)*Q(x)`.
The existing Gamma moments plus the still-needed inverse first moment
suggest exact masses `(1/4-z)*Gamma(3/2)` and
`(-9/4-z)*Gamma(3/2)`. Thus their mass defects from E should be
`(z+3/4)*Gamma(3/2)` and `(z+13/4)*Gamma(3/2)`, selecting different
shifts even at this weak single test. Check the inverse moment,
coordinate identities, all global admissions and Gamma recurrence in
Lean before using these values. Neither raw forcing equals E pointwise
for any z, as the existing leading-forcing theorem already proves.
This test attacks the missing measure/parameter/complete-forcing match;
it must not rename a selected integral shift as the RH spectral coordinate.

## Iteration 15 — actual differential-forcing mass comparison (audited)

Revalidated the literal source formulas and the audited current integral.
Attack the proposed dx-pairing directly: prove the inverse Gamma moment,
express both existing log-coordinate forcings as admitted combinations of
Q, xQ and Q/x, evaluate their complete integrals and classify their
zero-defect shifts. Retain the separate existing proof that neither raw
forcing equals the arithmetic current at any shift. The positive survivor
must be the exact full mass law, not merely a rejected identification.

**Iteration 15 mathematical result (audited):** both actual raw
forcings have the predicted admitted dx masses. Their exact current mass
defects vanish only at -3/4 and -13/4 respectively. The stronger log-domain
check gives exp(t/2)-normalized negative-tail limits +1/2 and -1/2,
independent of z. Neither forcing nor either potential term is separately
L1(dt). Both complete connection sums equal the actual Gamma derivative,
which is integrable and has zero dt integral for every z. This is the
nontrivial positive survivor; splitting its pieces is inadmissible and
its all-shift validity supplies no selector. The same full derivative in
ray coordinates is Q/2-xQ, admitted with mass -Gamma(3/2). Its complete
mass defect from E is 2*Gamma(3/2). An arithmetic transmutation must retain
this contribution rather than only repair a raw-force coefficient.

Three deep method searches completed with partial coverage (723179
indexed declarations). Retrieved source/method metadata includes Gamma
identities, finite-measure transfer and tail estimates. The actual proof
uses the current Gamma derivative family, the positive-ray moments, exact
normalized lower tails and the existing half-line nonintegrability lemma.
Finite-measure and generic upper-tail methods did not solve the literal
domain problem. Broad primary arXiv abstracts read: 2609.06534 (September6,
p-torsion barriers and differing function/gradient convergence) and
2609.02192 (September2, equivariant holomorphic torsion asymptotics).
No arithmetic parameter or source-domain transfer was established.

**Next candidate, not proved:** use the actual coefficient family rather
than prescribing a new forcing for each spectral shift. Its literal
coefficients suggest the differential-difference identity
`partial_t M_b(exp t) = M_b(exp t)/2 - exp(t)*M_(b-1)(exp t)`, alongside
already-proved `partial_b M_b=E_b`. First prove local uniform source
summability for the coordinate derivative and retain the shifted family
and its global domain. The minus-one coefficient shift is a real new
domain obligation; pointwise entireness cannot discharge it. This is a
candidate actual source dynamics, not a spectral Ward identification.


**Iteration 15 final audit:** 31 public theorems in the 422-line leaf
`ThetaCuspHawkingParikhWilczekGammaForcingMeasureClassification.lean`.
Scratch and direct Lean checks, targeted leaf build, all-public axiom
audit, formal lint, index regeneration and all-name/file checks passed.
Only standard foundations occur; umbrella wired, no full/umbrella build
or numerical experiment. All owned Lean and research processes finished.
RH remains unproved; the next actual-family coordinate-generator target
is recorded above, with its shifted-parameter admission obligation.

## Iteration 16 — actual Möbius coordinate dynamics (audited below)

Attack the arithmetic family itself. Derive the exact atom shift
`A_(b-1)(n,x)=n*A_b(n,x)`, including zero index, and its real coordinate
derivative `partial_x A_b=A_b/(2*x)-A_(b-1)`. On each positive compact
interval, compare the Gamma atom with its value at the left endpoint;
polynomial coefficient bounds give a common summable derivative majorant.
Then differentiate the complete sum and transport through x=exp(t).
The full shifted family must remain in the equation. A global admission
claim for that family requires its own weighted source estimate.


**Iteration 16 mathematical result:** the actual atom shift and full
coordinate derivative are closed in Lean for every complex coefficient
parameter. Positive-interval Gamma comparisons and polynomial moments
supply the common summable derivative majorant. Thus the complete
log-coordinate equation is exactly the proposed equation above, including
its shifted family. The accompanying ray weight changes the global test:
`integral norm(x*A_(b-1))=3/2*integral norm(A_b)` for every atom. The complete
weighted shifted source therefore has the same exact absolute admission
boundary `Re(b)>0`. Its complex integral is `3/2*integral M_b`, and the
admitted weighted coordinate derivative has integral `-integral M_b`.
The shift alone must not be tested after dropping its weight. At zero the
new coordinate identity is pointwise; no signed global shifted admission
has been assumed. The full coefficient generator remains `partial_b M_b=E_b`.
Neither equation forces independent spectral stationarity.

Four deep method searches completed with partial coverage of 723219
indexed declarations. Candidate, source-argument and ingredient metadata
are retained in `pw-b-gamma-coordinate-searches.json`. The derivative
interchange search identifies the applicable common-summable-bound method;
its actual Gamma majorant is proved here. The Mertens search identifies
source decay relevant to the next signed endpoint, not its missing
weighted atom admission. Broad primary arXiv abstracts read: 2609.08746
(September8, nonexpansive wavelet dilations), 2609.06661 (September6, sparse
Mellin recovery), and 2608.13021 (August13, Shilnikov-Hopf bifurcation).
Their hypotheses do not identify this arithmetic source or its spectral
parameter. No external transfer theorem or Lean premise was introduced.

**Next candidate, not yet proved:** signed global admission of
`F_0(x)=x*M_(-1)(x)` and `integral F_0=0`. Use `R(x)=x*Q(x)` and the actual
Abel atoms `S(n)*(R(n*x)-R((n+1)*x))`. The exact decomposition of the
adjacent difference gives the bound
`x*norm Q((n+1)*x)+(x+n*x^2)*norm Q(n*x)` for positive n and x. The first
and second Gamma moments should give integrated cost at most
`(2*Gamma(5/2)+Gamma(7/2))/n^2`. Existing inverse-square Mertens summability
then supplies the proposed global norm estimate. Prove the second moment,
complete finite Abel identity and terminal decay. The original polynomial
Gamma summability bounds both `n^2*Q(n*x)` and `n*Q(n*x)`, which should kill
the terminal after `|S(n)|<=n+1`. Each new Abel atom's complex integral
should be `3/2` times the original Abel atom's integral, allowing the
already-audited zero mass to pass without a fresh formal series exchange.
None of these new endpoint obligations is claimed closed yet.

If this candidate closes, the admitted weighted coordinate derivative at
zero has zero mass, while `E=partial_b M_b|0` has mass `Gamma(3/2)`.
The exact nonzero difference would rule out identifying the two complete
responses, or representing E as a constant linear combination of M and
its weighted coordinate derivative. Retain that positive mass survivor;
the physical transmutation and independently source-forced balance remain
the RH obstacle.


**Iteration 16 final audit:** the 338-line coordinate-generator leaf has
21 public theorems and one definition. Scratch and direct Lean checks,
targeted leaf build, all 22 public axiom audits, formal lint, index
regeneration, all-name uniqueness and generated API coverage passed.
Only the standard foundations occur. Umbrella wired; no full/umbrella
build or numerical experiment ran. All owned Lean and research processes
finished. The actual coordinate generator and weighted absolute admission
are closed; the signed endpoint, arithmetic/spectral transmutation and
independent fixed-grade balance remain open. RH is unproved, goal active.

## Iteration 17 — signed coordinate endpoint and generator mass (audited below)

Revalidated the complete coordinate leaf, the existing signed Abel source,
and its exact mass law. Attack the recorded endpoint candidate directly:
prove the second Gamma moment, the weighted adjacent-source estimate,
complete signed Abel admission and terminal decay. Identify the result
with the literal `x*M_(-1)`, then compare the globally admitted coordinate
and coefficient generators. Preserve the exact nonzero mass difference
if their proposed identification fails. RH still requires an independent
source-forced spectral balance after this comparison.


**Iteration 17 mathematical result:** the complete signed endpoint is
closed in Lean. The second Gamma moment and exact adjacent-source
estimate give the stated inverse-square integrated cost for R=xQ.
Polynomial moment summability gives a stronger terminal result: the
entire sequence S(n)R(nx) is summable at every positive x. Exact finite
Abel summation, both complete pointwise sums and the terminal limit
identify the admitted assembly with literal x*M_(-1). Each integrated
new Abel atom is 3/2 times the original atom; both global norm series are
summable, so the signed endpoint has zero mass. The actual weighted
coordinate derivative D=xM' is also L1 with zero mass. Consequently
E-aM-cD has mass Gamma(3/2) and L1 norm at least Gamma(3/2), for every
complex a,c. This excludes constant local mixing and retains an exact
positive survivor; it supplies no independent spectral balance.

Four deep method searches completed with partial coverage; all metadata
is saved in pw-b-gamma-coordinate-endpoint-searches.json. Exact finite
Abel summation, convergent moments and norm-of-integral separation apply.
Broad web entrainment/elasticity queries initially returned old or
irrelevant results; direct arXiv elasticity search ordered by date found
September2026 papers. Read 2609.04169v2 (September3, revised September6),
including the primary HTML Theorem2 and separation proof, and the abstract
of 2609.04856 (September4). The first derives a response-error floor from
an inaccessible component, a useful comparison with the actual integral
functional used here. Its mechanical symmetry is not an arithmetic
premise. The second uses different ensembles and a weak-bending
approximation, with no admitted transfer found. No numerical experiment
or external proof premise was introduced.

**Next candidate, not yet formalized:** retain a nonlocal actual source
response through T_h f(x)=sqrt(x)/sqrt(x+h)*f(x+h), x>0,h>=0. On the literal
Gamma dilation atom this should multiply by exp(-n*h). The corpus file
HTGeometry/FrullaniIntegral.lean has proved positive-ray integrability and
integral (exp(-a*h)-exp(-b*h))/h = log b-log a when both real parts are
positive. Taking a=n,b=1 suggests
E(x)=integral_{h>0}(T_h M(x)-exp(-h)*M(x))/h dh. For n>=1 the difference
has fixed sign and absolute integral log n; polynomial Gamma moments
should make the full atom-integral majorant summable at each fixed x.
Prove the exact weighted translation action, finite-to-full interchange
and source admission before using this generator. This would identify
an actual nonlocal arithmetic response after the local span failed;
it would not by itself establish a joint global integral, self-adjoint
physical realization, spectral parameter matching or the required Ward
balance. Those distinctions remain essential to the RH chain.


**Iteration 17 final audit:** 384-line coordinate-endpoint leaf, 25 public
theorems and two definitions. Scratch and direct Lean checks, targeted
leaf build, all 27 public axiom audits, formal lint, index regeneration,
all-name uniqueness and generated API coverage passed. Only standard
foundations occur. Umbrella wired; no full/umbrella build or numerical
experiment ran. All owned Lean and research processes finished. The signed
coordinate endpoint, complete mass separation and positive norm gap are
closed. RH remains unproved and the goal active; the nonlocal actual-source
transmutation candidate and its unsolved spectral obligations are recorded.

## Iteration 18 — actual weighted-translation Frullani current (in progress)

Revalidated the signed coordinate endpoint and its nonzero arithmetic
mass gap. Attack the recorded nonlocal candidate: retain the exact
half-density translation, prove its action on each actual Gamma atom,
evaluate the admitted Frullani kernel and its absolute integral, then
justify the complete arithmetic series/integral interchange. Keep fixed-x
and joint global admission separate. An exact source representation must
not be mistaken for the independently forced spectral Ward balance.

**Iteration 18 joint-domain attack (candidate, not yet proved):** the
kernel calculation suggests a signed Abel assembly on the product ray.
Let K_n(h)=(exp(-n*h)-exp(-h))/h and retain
B_n(h,x)=S(n)*(K_n(h)*Q(n*x)-K_(n+1)(h)*Q((n+1)*x)). Its exact split is
K_n(h)*B_Q(n,x)+S(n)*(K_n(h)-K_(n+1)(h))*Q((n+1)*x).
For n>=1 the first kernel has absolute integral log n; the increment
has absolute integral log(n+1)-log n<=1/n. Product-integral norm bounds
should therefore be the same summable log-Mertens/inverse-square costs
as the admitted logarithmic-current Abel assembly. Prove joint atom
admission, the norm series, exact finite identity, pointwise source
identification and terminal decay. This would admit the full signed
Frullani response on both positive rays and justify Fubini at zero,
where its original separate atom norm sums diverge. Do not replace this
obligation by the easier already-paired iterated integral.


**Iteration 18 mathematical result:** both candidates close in Lean.
The literal half-density translations act on every actual Gamma atom,
obey the semigroup law and give the coefficient current as the complete
Frullani integral for every complex coefficient and positive source x.
Kernel sign gives norm integral log n; the actual current's summability
justifies the entire series exchange. Original global atom norms retain
the exact Re(b)>0 boundary. At zero, the proposed signed product Abel
estimate is proved with both complete summable Mertens costs. Exact finite
summation and terminal decay identify it with the literal two-variable
response. Thus joint L1(dh dx) admission and Fubini hold there despite the
original atomwise failure. Both iterated integrals and the product integral
are Gamma(3/2), and the product norm is strictly positive. This closes an
actual nonlocal source/domain gap without supplying independent balance.

Four deep method searches are saved in pw-b-gamma-frullani-searches.json;
all report partial coverage (723356, 723356, 723371 and 723387 indexed
declarations). The Frullani formula, product norm control and exact Abel
summation apply. The fourth proposes a commutator-trace/positive-integrand
argument. Reading its actual candidates exposes missing hypotheses:
the trace theorem requires a nuclear operator and a bounded partner,
and the positive heat kernel concerns a different prescribed pair of
squared distances. Neither identifies the actual source product integral
with that trace. Its asserted zero would contradict the exact retained
Gamma mass unless a compensating source or different proved pairing is
supplied. No trace cyclicity, positivity transfer or spectral selector is
assumed from this search output.

Broad relaxation, mixing and damping searches and direct arXiv attempts
were made; primary abstracts 2609.06139 (September5, Georgi-Machacek thermal
phase transition) and 2608.04038 (August3, empirical art/video uncertainty)
were read. Neither provides a source-faithful arithmetic operator transfer.
The first primary abstract also corrects an unrelated search snippet.
Further broad subordination and renewal searches returned older or
irrelevant material. No numerical experiments or external premises enter.

**Next candidate, not yet formalized:** derive the exact source-fixed
reflection of the now admitted nonlocal generator before trying to impose
balance. Existing inverse-gain reflection fixes Q and, on the positive ray,
should be R f(x)=Q(x)*f(1/x)/Q(1/x). Writing f=Q*u, the original weighted
translation satisfies T_h f(x)=exp(-h)*Q(x)*u(x+h). Its reflected companion
should be R T_h R f(x)=exp(-h)*Q(x)*u(x/(1+h*x)). Thus the two complete
Frullani responses should compare additive and reciprocal source motion,
with every weight and subtraction retained. Prove this exact identity from
the existing reflection, its actual arithmetic specialization and global
admission; do not infer self-adjointness or a physical pairing from the
formal conjugation. Test whether the resulting full forcing has any
independent balance law. The coefficient parameter is still not identified
with the Xi spectral label, and source fixation alone previously failed
to supply stationarity. This candidate attacks that missing operator
comparison rather than treating the nonzero current as zero.

**Process correction:** a joint scratch check was prematurely started
while the core leaf build was still running; it failed immediately on the
missing core olean. The overlap was acknowledged, the core build was allowed
to finish, and the successful scratch/direct/leaf/axiom sequence thereafter
was serialized. No numerical or full/umbrella build ran. Final audit below
records completion rather than claiming perfect process discipline.


**Iteration 18 final audit:** source leaf 250 lines, 24 public theorems
and four definitions; joint leaf 284 lines, 21 public theorems and two
definitions. Successful scratch checks, both warning-free direct leaf
checks, both targeted leaf builds and all 51 public axiom audits passed.
The builds replayed existing upstream style warnings. Only standard
foundations occur. Both umbrella imports, source-name uniqueness,
generated API coverage, index regeneration, local documentation links,
conflict/whitespace checks and task-scoped git diff checks passed.
Formal lint was run and failed on the unrelated shared-worktree module
FokasLenellsCausalFrequencyBessel being unreachable from RHTower; no
PW-B leaf lint error was reported, and that unrelated file was not changed.
All owned Lean, research and index processes completed, confirmed by
terminal statuses and a process check. The earlier corrected process
overlap remains recorded above. No full/umbrella build or numerical
experiment ran. The actual nonlocal current and signed product domain
are closed; the independent source balance and Xi spectral identification
remain unproved. RH is unproved; goal active.


## Iteration 19 — reflected nonlocal source and exact domain (in progress)

Previous turn is verified progress: actual Frullani representation and
signed product admission closed. Revalidated the current sources and the
existing inverse-gain reflection. Derive its ray formula and exact
conjugation of weighted translation. Specialize to the complete reflected
arithmetic family and retain its Frullani current. Test global admission
in the actual ray measure, rather than assuming reflection preserves it.
The reflected Gamma atom suggests Q(x)*sqrt(n)*exp(-(n-1)/x), so the
reciprocal exponential may improve the original absolute-admission
boundary. Prove any such bound before treating it as physical selection.
A spectral Ward balance still requires an independent complete source law.


**Iteration 19 mathematical result:** the reflected source and its
conjugated nonlocal generator close in Lean. The exact inverse-gain ray
formula Rf=Qf(1/x)/Q(1/x) identifies the original reflection, proves its
involution and Q fixation, and gives the explicit reciprocal translation
S_h=R T_h R with flow x/(1+h*x). The actual response on R M_b is R F_b;
its admitted fixed-x integral is R E_b, also the coefficient derivative
of R M_b. This statement preserves which source is reflected.

The proposed global estimate is stronger than initially required. The
actual reflected atom is sqrt(n)*Q(x)*exp(-(n-1)/x) times its unchanged
arithmetic coefficient. Exponential factorial bounds and the admitted
moment integral Gamma(p+3/2) show every polynomially weighted atom norm
mass series summable at every complex b. The precise common bound for
index n+2, norm(b)<=N and weight (n+2)^k has coefficient
2^(N+k+1)*(N+k+3)!/(n+1)^2 and source x^(N+k+3)*norm Q(x).
Thus full reflected family/current global admission, their series/integral
exchanges and the joint reflected Frullani integral are all proved.
Fubini holds for every b. No value or sign is asserted for its unweighted
reflected mass. At zero the current is still not identically zero on the
positive ray: involution would contradict integral E=Gamma(3/2).

Three deep method searches, each partial with 723426 indexed declarations,
are saved in pw-b-gamma-reflected-frullani-searches.json. They provided
weighted-reflection and moment comparisons, not the literal all-parameter
bound. The used factorial/Gamma names were located by corpus text search
and verified in the actual scratch proof. Broad arXiv renewal search
ordered by date yielded September9 papers 2609.09738 and 2609.10399.
The former's actual model and stationary-state section retain competing
waiting laws and a nonzero reset probability; no such source-derived law
is available here. The latter's initiator-label identifiability concerns
a different statistical model. No external premise or numerical experiment
was introduced.

**Next candidate, not yet proved:** compare the original Frullani operator
H with its conjugate on the same actual reflected arithmetic input.
The proved identity S_h(R M_b)=R(T_h M_b) supplies no equality
S_h M_b=T_h M_b. On the positive reflected atom Q(x)*sqrt(n)*exp(-(n-1)/x),
the normalized additive increment has sign opposite to that of the
original atom when n>1. Derive its complete h integral and the full
H(R M_b)-R(E_b) forcing, with joint absolute admission or an exact signed
assembly. Test a source-derived balancing contribution rather than
assuming covariance from Q fixation. The previously proved all-parameter
admission cannot itself identify the Xi spectrum or force the RH Ward
charge to vanish. PW-B remains active and RH unproved.


**Concrete next estimate (paper candidate, not Lean-closed):** for n>=2,
a=n-1 and positive x,h, the normalized original-translation increment of
the reflected Gamma atom is
L_n(x,h)=sqrt(n)*Q(x)*exp(-h)*
(exp(-a/(x+h))-exp(-a/x))/h. The exponential difference is nonnegative.
Keeping the exact reciprocal difference, rather than replacing x+h by x,
suggests the majorant
sqrt(n)*a*x^(-1/2)*exp(-x)*exp(-h)*
exp(-a/(x+h))/(x+h).
The bound 1-exp(-v)<=v gives this expression with v=a*h/(x*(x+h)).
For every positive integer p, the already verified factorial estimate
then bounds it by
sqrt(n)*p!*a^(1-p)*x^(-1/2)*exp(-x)*exp(-h)*(x+h)^(p-1).
A finite binomial expansion separates admitted Gamma moments in x and h.
Choosing p above the coefficient's polynomial degree should give a
summable inverse-square index cost for the complete original operator
on R M_b. The unit atom has zero increment. This retains both the source
endpoint and h=0 cancellation and directly attacks the same-input
comparison; it does not assert that the resulting arithmetic signed
commutator vanishes.


**Iteration 19 final audit:** 447-line reflected-Frullani leaf, 38 public
theorems and six definitions. Scratch and direct Lean checks, targeted
leaf build and all 44 public axiom audits passed. The accepted proof
emits an informational ring-normalization suggestion, and the build
replays existing upstream style warnings; no open proof goal remains.
Only standard foundations occur. Formal lint, index regeneration,
all-name uniqueness and generated API coverage passed. Both the current
umbrella import and the previously unrelated missing import are present.
Scoped whitespace, conflict and Markdown-link checks passed after fixing
a mathematical expression that had rendered as an unintended local link.
All owned Lean/research/index processes completed; a final process scan
found no owned Lean process. All Lean checks were serialized in the
foreground. No full/umbrella build, numerical experiment, commit or push
ran. The complete reflected nonlocal source is admitted at every complex
coefficient parameter, with its nonzero forcing retained. Same-source
operator balance and Xi spectral identification remain open. RH is
unproved; goal active.


## Iteration 20 — original operator on the reflected arithmetic source (Lean closed; repository lint limitation)

Previous turn is verified progress: exact reciprocal conjugation and
all-parameter global admission closed. Revalidated those source formulas
and the next kernel estimate. Attack the actual original-translation
increment on R M_b, retaining its positive scalar kernel and every signed
arithmetic coefficient. Prove the endpoint-sensitive bound, complete
product admission, full-source identity and forcing difference from R E_b.
A positive atom kernel does not imply positivity of its Möbius assembly;
independent complete balance and Xi spectral identification remain open.

**Iteration 20 paper calculation (Lean audit in progress):** the original
translation on the same reflected atom has scalar kernel
`K(a,x,h)=exp(-h)*(exp(-a/(x+h))-exp(-a/x))/h`, with a=n-1.
For a,x,h>0 this is strictly positive. Writing
`v=a*h/(x*(x+h))` factors the difference as
`exp(-a/(x+h))*(1-exp(-v))`. The inequality `1-exp(-v)<=v`
and the exponential factorial bound give, for every natural k,
`K <= (k+1)!/a^k * exp(-h)*(x+h)^k/x`.
This preserves the cancellation at h=0 and the integrable x=0 source
weight; replacing x+h by x too early loses that joint estimate.

The positive majorant
`J_k(h,x)=exp(-h)*norm(Q(x))/x*(x^k+h^k)`
splits into two products of admitted Gamma moments. Its x moments have
exact values Gamma(k+1/2), while its h moments are Gamma(k+1).
For norm(b)<=N, the complete atom with index n+2 is bounded in norm by
`2^(N+1)*(N+4)!*2^(N+2)/(n+1)^2 * J_(N+3)(h,x)`.
This supplies both joint norm summability and fixed-positive-x h norm
summability, with the zero and unit increments handled exactly.

The intended complete consequence is a globally admitted original
Frullani current on R M_b, with valid series/integral exchange and Fubini.
Its difference from R E_b has scalar weight
`W_n(x)=sqrt(n)*(integral K(n-1,x,h) dh+log(n)*exp(-(n-1)/x))`.
The zero and unit weights vanish; every n>1 weight is strictly positive.
The full defect nevertheless retains mu(n)*exp(-b*log(n))*Q(x) in its
convergent series. No sign or vanishing is inferred for that complete
signed assembly. The next source-balance test must control this exact
forcing and identify the spectral parameter; operator conjugacy alone
supplies neither assertion.

**Iteration 20 stronger candidate (not yet Lean-closed):** the exact
forcing coefficients `c_n(x)=mu(n)*Q(x)*W_n(x)` define an L-series
convergent at every complex coefficient parameter. The head c_0=c_1=0
and the prime coefficient c_2=-Q(x)*W_2(x) is nonzero. The corpus theorem
`LSeries.tendsto_cpow_mul_atTop` therefore predicts
`2^r*(H(R M_r)(x)-R(E_r)(x)) -> -Q(x)*W_2(x)` as real r tends to infinity.
This would give eventual nonvanishing of the actual full forcing at
every positive x, not just an isolated-atom sign. It tests and rejects a
family-wide source-balance conjecture while preserving the exact leading
law. It does not rule out balance at particular spectral parameters.

**Next source-balance test after the pointwise audit:** carry the literal
same-source forcing through the global x pairing. Its coefficient
`c_n(x)=mu(n)*Q(x)*W_n(x)` is the admitted difference of an integrated
original-response atom and the reflected current atom. The sum of its
norm integrals is controlled by the already proposed joint atom norm
sum plus the reflected-current norm sum. This should justify the exact
mass L-series with coefficients `d_n=integral c_n(x) dx`. The first two
vanish and `d_2=-integral Q(x)*W_2(x) dx` should be strictly negative,
using the full positive-ray integral and its proved admission. A leading
coefficient limit would then test a globally integrated family-wide
balance, not only pointwise equality. This remains a candidate: it does
not determine the zero-parameter mass, identify a physical spectral
pairing, or establish any Xi occurrence law.

**Iteration 20 mathematical result:** the full same-source candidate and
its stronger leading law close in Lean. Both the original and conjugated
nonlocal generators act on the literal reflected arithmetic family on a
proved common domain. The endpoint-sensitive reciprocal kernel estimate
and its inverse-square complete atom bound admit the original response
jointly and on every fixed-positive-x section, at every complex b.
Its complete h current and its difference from R E_b are globally L1;
Fubini and all used arithmetic sum/integral interchanges are justified.
The exact full signed defect is the series with weights W_n stated above.
W_0=W_1=0 and W_n>0 for n>1, with all Möbius signs retained.

The L-series identification is literal. Its first two coefficients
vanish; the prime-two coefficient is exactly -Q(x)*W_2(x), nonzero for
every positive x. The corpus's first-coefficient limit theorem proves
`2^r*D_r(x) -> -Q(x)*W_2(x)` along real r to infinity. Thus the actual
complete forcing is eventually nonzero and cannot be identically zero
across b. This rejects the family-wide same-input balance conjecture and
retains a quantitative leading law as its positive survivor. It does
not determine D_0, its global mass, or balance at Xi occurrences. The
spatial pairing candidate above remains the next mathematical test.

Four deep searches, all partial, are saved in the same-source search
record. Available inventories contain 723442, 723502 and 723510
declarations; the domain search's coverage was pending and had no count.
Generic positivity/leading-coefficient suggestions did not furnish the
literal theorem. Direct corpus search found and scratch-verified the
Gamma, product-integral and L-series leading-coefficient APIs. Broad
arXiv bistability search found September5 threshold-network and
September10 localized-cubic papers. The former's actual row-stochastic
nonnegative feedback and contraction hypothesis are not established for
this signed arithmetic source; the latter's primary abstract supplied
no verified transfer. No external premise or numerical experiment was
introduced.


**Iteration 20 Lean audit:** two leaves, 312 and 319 lines, with 44 public
theorems and eight definitions. Complete scratch checks and both targeted
final builds passed. Build logs show only the two new leaves rebuilt;
dependencies were reused. All 52 public axiom audits passed with only
standard foundations. All names are unique, both umbrella imports are
wired, and new-file/scoped whitespace, conflict and local-link checks
passed. The accepted current proof emits an informational ring suggestion
at line 200, and builds replay existing upstream style warnings.

The authoritative repository lint gate did not pass. Its five errors
are missing imports for Sieve.MenonHarmonicRamareBlockSwapped,
Sieve.MenonHarmonicRamareLadderSwapped,
Sieve.MenonHarmonicRamareLadderSwappedVolume,
HTGeometry.WeightedMinimax.Basic and HTGeometry.WeightedMinimax.SignRealization.
Neither new PW-B leaf is flagged. Confirmed those unrelated imports are
absent and preserved the separate active work. This is a repository-audit
limitation, not a Lean proof failure and not a claim that the full gate
passed. No full/umbrella build ran.

Index regeneration passed and refreshed LEAN_API, LEAN_GAPS and
LEAN_OVERVIEW. Every one of the 52 public names is present in the API;
both imports occur exactly once. All owned Lean, research, lint and
index sessions completed; no owned Lean process remains. Lean work was
serialized in the foreground, with no full/umbrella build, numerical
experiment, commit or push. RH remains unproved; the goal is active.
The next attack is the complete spatial mass pairing and its retained
prime leading coefficient, followed by the still-unpaid source/spectral
identification and independent fixed-grade balance.

## Iteration 21 — complete spatial pairing of the same-source forcing (Lean-closed)

Previous turn is verified progress: actual common operator admission,
full signed forcing and its nonzero pointwise leading coefficient are
Lean-closed and audited. Revalidated the current sources and route ledger.
Now test the actual positive-ray spatial pairing. Prove global coefficient
norm summability before integrating the L-series, retain the full prime
two coefficient, and derive its leading mass law. Pointwise nonvanishing
alone cannot justify a nonzero total mass. The physical measure and Xi
spectral identification, and independently source-forced balance at Xi
occurrences, remain the hard RH gap.


**Iteration 21 proof result:** complete scratch and all 31 public axiom
prints passed. The exact original spatial mass is the L-series of the
integrated signed coefficients, admitted at every complex parameter.
The zero/unit coefficients vanish and the prime-two coefficient is -A
with A finite and strictly positive. Thus 2^r B(r) tends to -A; the
complete mass is eventually nonzero, universal integrated balance is
false, and the scaled original L1 norm eventually exceeds A/2. This
closes the previously unpaid spatial-cancellation test. B(0), the
physical pairing and spectral occurrence balance remain undetermined.
See the new formalized mass card for the dependency-closed paper proof.
Its targeted final build passed (new leaf only, 239s); no full or umbrella
build ran. All 31 scratch axiom records contain only standard foundations.
Repository lint reports six unrelated missing umbrella paths: EulerDeletionSignatureWordExpansion,
Sieve.MenonHarmonicRamareLadderSwapped, Sieve.MenonHarmonicRamareLadderSwappedVolume,
and WeightedMinimax.Alternation, Coefficient and Perturbation. The new
PW-B leaf is not flagged; separate active work was preserved.

Research retained three partial deep results with pending coverage, one
partial hybrid inventory (723510 declarations), the failed Ward deep
backend and its eight-hit lexical fallback. Pure coefficient Mellin gauges
are not an analytic Mellin transform. Broad entrainment/echo arXiv searches
provided no established source transfer. The exact full mass calculation,
not a generic adjoint or Bessel model, supplies the positive survivor.

Iteration 21 final checks: index regeneration passed (two changed index
entries, zero removed); all 31 public declarations occur uniquely and are
present in LEAN_API. Card links, new-source whitespace/conflict checks and
scoped git diff checks passed. All iteration21 Lean/research/lint/index
sessions are terminal. The six-error repository lint limitation remains
recorded; no full build was run. The active scratch now belongs only to
iteration22. Memory: rh/pw_gamma_same_source_spatial_mass_2026_09_11.

## Iteration 22 — actual source Mellin identification (Lean-closed)

Conjecture from the literal atoms and freshly read corpus
Mathlib.NumberTheory.LSeries.MellinEqDirichlet and Gamma.Basic:
Mellin(M_z)(s)=Gamma(s+1/2)/zeta(z+s), initially for Re(s)>-1/2
and Re(z+s)>1. Prove the original source Mellin integral, each weighted
arithmetic atom's admission and value, full norm-sum admission and
interchange. This identifies the combined analytic parameter z+s;
coefficient-family entireness alone did not do so. Attempting absolute
coefficient admission below Re(z+s)=1 must fail by the existing sharp
Mobius L-series boundary. The positive survivor is the actual transform
identity in its proved domain; a critical-strip extension requires new
signed source estimates and cannot be assumed from reflected admission.
A scratch for the source and atom identities is prepared; no proof result
for this new Mellin bridge is claimed yet.


Iteration22 source audits: the corpus's actual Mobius–Laplace transform
has Gamma/zeta on Re(s)>1. Its critical continuation wall is proved
EQUIVALENT to RH; the source half-decay bridge retains its decay premise.
All located direct half-decay producers retain a critical-profile,
additive-correlation or mixed-convolution bound. One occurrence inside
an unconditional theorem is under a contradiction hypothesis proving
that the critical profile does not tend to zero, not an unconditional
decay producer. Generic Suzuki energy bounds retain coercivity,
accretivity and the source equation; the proposed bilateral cancellation
uses deliberately complementary character halves. No matching to the
literal arithmetic operators was found. The RapidDecayRay candidate is
a condition, not a proof of source decay. These candidates do not close
the missing source law.

The broad arXiv duality query found the September9 second-grade-fluid
boundary-control paper. Read its actual weak adjoint and section8.1
duality proof: cancellation uses common admitted tests and retains the
terminal/source terms. A strong boundary operator needs additional
regularity. No arithmetic transfer was established. The current
Mellin scratch has only an exponent-normalization repair outstanding
from its preceding check; the corrected full proof plus all nine public
axiom checks is running serially in the foreground.

Next candidate from the literal atoms and Mathlib Tannery: for Re(z)>3/2,
M_z(x)/sqrt(x) tends to 1/zeta(z-1/2) as x approaches zero from above.
Summability at z-1/2 controls each damped term by its original Dirichlet
coefficient norm. A nonzero limit would give the actual small-coordinate
Mellin boundary and prevent an unjustified large-coefficient/fixed-spectrum
transfer. No endpoint result is claimed before checking the full proof.


**Iteration22 Lean result:** complete corrected scratch and all nine
public axiom audits passed (only propext, Classical.choice, Quot.sound).
The original Q Mellin integral, full weighted atom integral and norm
integral, sharp coefficientwise admission and complete source interchange
are closed. Exact identity: Mellin(M_z)(s)=Gamma(s+1/2)/zeta(z+s) for
Re(s)>-1/2 and Re(z+s)>1. The norm-integral series converges exactly
when Re(z+s)>1 under the source exponent condition. No claim of signed
nonintegrability beyond that boundary was made. Eight theorems and one
definition were promoted with identical proof bodies and an umbrella
import. Targeted final leaf build is running; no other owned Lean runs.
Search records retain four deep method outputs: three partial inventories
report723510 declarations; the Abel-boundary query reports pending
coverage without a count. All suggested critical continuations retained
an unproved source bound or concerned a different actual source.


Iteration22 audit so far: the complete scratch and nine axiom checks
passed without errors or warnings. The new leaf is 162 lines; all nine
public names are unique, its umbrella import occurs once, local card
links and scoped whitespace/conflict checks pass. Repository-wide lint
now reports three unrelated active missing umbrella paths:
HTGeometry.WeightedMinimax.Alternation, Coefficient and PolyRoots.
The new PW-B leaf is not flagged. The targeted final build is still
running; its output so far replays existing upstream warnings.

The next endpoint argument now has a paper proof in its absolute
coefficient region: for Re(z)>3/2,
M_z(x)/sqrt(x)=sum_n term(mu,z-1/2,n)*exp(-n*x) on x>0.
The full coefficient norm series converges. Each damping factor has
modulus at most one and tends to one as x approaches zero from above.
Tannery therefore gives the literal limit 1/zeta(z-1/2), nonzero in
that region. A positive lower bound on the normalized source near zero
then forces divergence of its Mellin norm integral when Re(s)<=-1/2.
Together with the proved Mellin admission above -1/2, this would give an
exact FULL SOURCE boundary in the region Re(z)>3/2. This paper proof is
not yet Lean-checked; it does not claim the original z=0 signed critical
estimate. The next turn must verify the normalized-series identity,
dominated limit and actual nonintegrability before claiming that result.


Iteration22 final target build passed: only the new leaf rebuilt, in370s;
existing dependencies were reused. No full or umbrella build was run.
All nine complete-source declaration axiom audits are standard-foundation
only. Both this build and the axiom scratch are terminal; index regeneration
is now running. Repository lint retains the three unrelated WeightedMinimax
umbrella failures listed above. Critical continuation and independently
source-forced Ward balance remain unproved; RH and the goal remain open.


Iteration22 final audit complete: index regeneration passed and refreshed
LEAN_API, LEAN_GAPS and LEAN_OVERVIEW (zero changed/removed search entries
reported by this run). All nine new names and all31 iteration21 names
are present in the API. Completed-card links and whitespace, new-source
name uniqueness and one-copy umbrella wiring, and scoped diff checks
passed. Final process inspection found no owned Lean/lake process.
Every owned Lean, research, lint and index session is terminal. The
three unrelated WeightedMinimax lint failures remain explicitly recorded;
the repository-wide gate is not claimed passed. No full/umbrella build,
added axiom, numerical experiment, commit or push occurred.

Next goal turn starts from the literal small-coordinate endpoint argument
above, checks all actual source/domain identities in scratch, and then
returns to signed critical source control and independent PW-B Ward
balance. Neither a large-coefficient asymptotic nor the existing
RH-equivalent analytic continuation wall is an unconditional producer.

## Iteration 23 — actual source endpoint and fixed spectral argument (Lean-closed)

Previous goal turn is verified progress: the complete same-source spatial
mass and literal original Mellin bridge were built and axiom-audited.
Revalidated the current source and ledgers. The hard RH gap is still
signed critical source control plus physical occurrence-level Ward balance.
Now test the actual domain of the proposed fixed-spectral-argument transfer.
The preceding paper argument predicts a nonzero normalized endpoint for
Re(z)>3/2, hence a sharp full-source Mellin boundary at Re(s)=-1/2.
Prove the original normalized series, dominated limit, nonzero coefficient
and actual norm-integral obstruction in scratch. Retain the positive
survivor: exact endpoint coefficient and complete admitted region. Do not
replace a signed-source proof by failure of an atomwise majorant.


Iteration23 paper proof: for Re(z)>3/2, divide the literal full source by
sqrt(x). Every positive-index atom becomes
`LSeries.term(mu,z-1/2,n)*exp(-n*x)`; the zero atom vanishes. Its coefficient
norm series is summable, and the damping is bounded by one for x>0.
Dominated convergence gives the exact right endpoint `1/zeta(z-1/2)`,
which is nonzero in this region. Half its norm is therefore an eventual
positive lower bound. The actual Mellin integrand norm is exactly
`x^(Re(s)-1/2)*norm(M_z(x)/sqrt(x))`. Local power integrability now forces
Re(s)>-1/2. The prior complete Mellin bridge gives the converse, so this
is a sharp domain for the signed source itself. Keeping u=z+s fixed
fails actual admission whenever Re(u)<=Re(z)-1/2. Scratch verification
and the full public axiom audit are running; no endpoint Lean result is
claimed before that run finishes.

Three deep method searches finished with partial coverage of723510
indexed declarations. Candidate statements, source arguments and every
proposed ingredient set were inspected. The Einasto normalized-limit
proof retains a nonzero source coefficient, but the actual series here
requires Tannery. The proposed finite weighted Cauchy--Schwarz lemma
proves no local nonintegrability; power-series uniqueness also does not
supply this source's endpoint. The fold search's Klein--Gordon lemma
assumes its balance equation, and complete analytic resolution retains
an independently supplied conservative map. Neither establishes the
missing source balance. Deadline/reranking errors, a decomposition
transport failure and deferred refresh remain in the saved raw records;
model sufficiency labels are not evidence of applicable premises.

The broad date-ordered arXiv search `trapping` led to
[Universal Structure of Horizon Formation in Generic Binary Black Hole Mergers](https://arxiv.org/html/2609.11819v1)
(September10,2026). Its analytic mechanism combines past isolation,
outermost stability, a positive principal eigenfunction and a complementary
inverse, then retains nonzero linear-time and quadratic-amplitude
coefficients in a fold reduction. Those requirements are not established
for the actual Gamma/Möbius source. In particular, its known nontrivial
zero-mass signed endpoint cannot be declared a positive principal mode.
No physical stability, elliptic realization or new Lean premise was
imported, and no numerical work was used.

Next candidate, after the full-source domain audit: subtract the forced
endpoint contribution itself, rather than assign a value to a divergent
integral. With C_z=1/zeta(z-1/2), test the exact complete source
`S_z=M_z-C_z*Q`. For Re(z)>5/2, its proposed normalized first remainder
is `(M_z/sqrt(x)-C_z*exp(-x))/x`, with candidate limit
`C_z-C_(z-1)`. This follows on paper from the complete difference series
and the summable first coefficient moment, not from a formal Taylor
replacement. A new domain, integral identity, and correction to the
source dynamics would all have to be proved. No signed critical estimate
or occurrence-level Ward balance follows merely from this subtraction.


Iteration23 scratch and all ten public axiom audits passed. The nonzero
full-source endpoint, actual norm identity, sharp Mellin domain and fixed
spectral-argument exclusion are Lean-closed with standard foundations
only. Proof bodies were promoted unchanged into
ThetaCuspHawkingParikhWilczekGammaMobiusSourceEndpoint, with one umbrella
import. Only that leaf's targeted final build is running.

A fourth deep method query tested explicit subtraction and reciprocal-zeta
differences. Its partial723510-declaration output and disconnected-worker
error are saved alongside the prior three records. The proposed mixed
finite-prefix detector and arithmetic zeta_apply statement were checked:
the former concerns finite deletion paths, and the latter is the arithmetic
function equal to one on positive integers, not a monotonicity theorem for
analytic zeta. Neither proves the candidate remainder coefficient's sign.
All four research sessions are terminal. The full-source subtraction
candidate and remaining critical/Ward obstacles above remain open.


Iteration23 repository formal lint passed; the earlier unrelated
WeightedMinimax umbrella failures are absent in the current result.
The promoted public proofs match the passing scratch exactly after
comment/whitespace normalization. All ten source declarations, local card
links and scoped whitespace checks passed. Targeted build and final
index audit are still pending.


Subtraction paper analysis for the next attack: retain a_n(z)=
LSeries.term(mu,z-1/2,n). For x>0 the complete normalized remainder is
`sum a_n(z)*(exp(-n*x)-exp(-x))/x`. For n>=1 its damping quotient equals
`-integral_1^n exp(-t*x) dt`, is bounded in absolute value by n-1,
and tends to1-n. The first absolute coefficient moment is summable when
Re(z)>5/2. Dominated convergence therefore predicts the exact coefficient
C_z-C_(z-1). For real z>5/2 this coefficient is positive: the positive
Dirichlet series for zeta is strictly decreasing on the real region>1
(the n=2 term is strict), hence its reciprocal is strictly increasing.
This sign proof still needs verification against actual corpus APIs.

The same complete difference bound gives O(x^(3/2)) at zero; the admitted
coefficient norm sum gives exponential decay at infinity. Thus the proposed
subtracted source should be Mellin-convergent for Re(s)>-3/2, with the
nonzero first remainder forcing the converse for real z>5/2. One fixed
subtraction would only move the fixed-u admission boundary by one; it would
not permit an unbounded rightward coefficient shift at fixed u.

On the common admitted region Re(s)>-1/2, linearity would give the exact
transform Gamma(s+1/2)*(1/zeta(z+s)-C_z). At s=-1/2 this written product
contains a removable Gamma pole and must not be evaluated through Lean's
totalized factors. The actual complete integral has the Frullani candidate
`-sum a_n(z)*log(n)`, namely the coefficient derivative of C_z, with its
own absolute-admission proof required. Retaining this value and the full
source correction is necessary before any continuation or Ward comparison.
No new subtracted-source theorem, critical bound or balance is claimed yet.


Iteration23 final targeted build passed in161s. Its only newly built
module was ThetaCuspHawkingParikhWilczekGammaMobiusSourceEndpoint;
all dependency jobs were reused. The build session is terminal, and
index regeneration is running. No full or umbrella build was run.


Iteration23 final audit complete. Index regeneration passed with one
changed search entry and zero removals; LEAN_API, LEAN_GAPS and
LEAN_OVERVIEW were refreshed. All ten public declarations occur once in
the source corpus and API, with one umbrella import. The API uses
unqualified display names: an initial namespaced-string audit was repaired
to match actual rows, then passed without rerunning the index. All owned
Lean, research, lint and index sessions are terminal; final process
inspection found no owned Lean/lake process. Scoped source/doc whitespace
and links passed. No full/umbrella build, numerical experiment, added
axiom, commit or push occurred. RH and the goal remain open.

Next goal turn starts from the completed endpoint module and the explicit
subtraction paper analysis above. Attack complete remainder admission,
its exact transform and the retained Gamma-pole value, while testing
whether any source-derived relation can force the actual critical balance.
Do not treat the new domain theorem, a zero assigned to an unadmitted
integral, or a continued quotient as an unconditional PW-B producer.


## Iteration 24 — explicit complete endpoint correction (in progress)

Previous turn is verified progress: the literal normalized endpoint and
sharp actual Mellin domain are Lean-closed; all ten axiom audits,
targeted leaf build, lint and index checks passed. Rechecked the current
module and process state. No owned Lean process remains from that turn.
The same-source physical pairing, critical control and independently
source-forced occurrence-level Ward balance remain unproved.

Now attack the domain repair exposed by the endpoint obstruction. Construct
S_z=M_z-C_z Q as the literal complete source, retain its full difference
series and prove the first normalized remainder. The existing actual
pwGammaFrullaniKernel is exactly the required exponential difference
quotient and already has integral -log(n) and norm integral log(n) for
n>0. Use this complete kernel to derive the subtracted source's finite
Gamma-pole value, rather than substitute into a totalized singular product.
The coefficient bound, source identity and integral interchange must all
be proved before drawing any Ward conclusion.


Iteration24 paper identity and scratch status: the complete normalized
remainder is `sum a_n(z)*pwGammaFrullaniKernel n x`. Each atom is
integrable for n>0, and its exact norm integral is
`norm(LSeries.term(logMul(mu),z-1/2,n))`; the zero atom vanishes.
The entire norm-integral series is summable already for Re(z)>3/2,
without the stronger first-moment region. This admits the actual corrected
Mellin integral at s=-1/2 and identifies its value with
`-LSeries(logMul(mu),z-1/2)`, the derivative of C_z. Current scratch has
closed the full series identity, first-moment summability, logarithmic
norm-integral summability and coefficient derivative; local kernel-limit
and integral/coercion repairs are being rechecked together. No complete
subtraction module has yet been promoted or declared audited.

The first-prime audit is also being tested: since logMul(mu) has zero
coefficients at0 and1 and coefficient -log(2) at2, the exact candidate
`2^r * integral R_(r+1/2) -> log(2)` follows from the corpus L-series
leading-coefficient theorem. It would give eventual positive real part
of the retained pole value, ruling out its automatic universal vanishing.
It would not identify a fixed physical spectral parameter or establish
critical-source balance.

Two deep method searches finished with partial inventories of723712
declarations and their complete raw records are saved. The Frullani
candidate is applicable and already supported by the literal kernel.
The pole search's proposed ingredient set incorrectly labels a cocycle
formula and a Sonin missing-vector theorem as a route to strip nonvanishing.
Their actual statements were read: reflCocycle_zeta assumes zeta nonzero,
while exists_nonzero_zeta_dvd_of_aperture_lt_one constructs a vector whose
Mellin function retains the zeta divisor. Neither proves nonvanishing.
The latter search's decomposition deadline remains recorded. A third
contact/source-method search is running.

Broad arXiv searches used `compensation` and `dissipation`; a cached
compensation listing stopped in July, so current indexed search hits
were also checked. No experiment or numerical calculation was performed.
The analytic discussion in
[Dissipation Enables Strongly Detuning-Dependent Interference in Pulsed Dynamical Decoupling](https://arxiv.org/html/2607.25176v1)
(July28) retains the coherent response after a decay event; a reset does
not automatically erase the subsequent detuning signal. Its driven
qubit dynamics have not been identified with this arithmetic source.
[Dissipation-enhanced scrambling in the SYK model coupled to a lossy cavity](https://arxiv.org/html/2608.19310v1)
(August19) retains an attractive contact term when differentiating its
ladder equation, and explicitly requires large-parameter approximations.
No exact finite-parameter PW-B transmutation follows from that calculation;
its contact term cannot be silently discarded or imported as a premise.


Iteration24 new pairing attack, derived from the actual transport identities:
write g=f/Q. The normalized forward and reflected complete generators are
A g(x)=integral_0^infinity exp(-h)*(g(x+h)-g(x))/h dh and
B g(x)=integral_0^infinity exp(-h)*(g(x/(1+h*x))-g(x))/h dh.
For 0<x<y their opposite jump densities are
k_plus(x,y)=exp(-(y-x))/(y-x) and
k_minus(y,x)=(y/x)*exp(-(1/x-1/y))/(y-x).
Direct algebra gives detailed balance with w(x)=exp(-x-1/x)/x:
both w(x)*k_plus(x,y) and w(y)*k_minus(y,x) equal
exp(-y-1/x)/(x*(y-x)). Any density satisfying all these pair balances
has constant ratio to w, by comparison with one fixed positive point.
Also w(1/x)/x^2=w(x). In original f coordinates the candidate density
is eta(x)=x^(-2)*exp(x-1/x); eta(x)*|Q(x)|^2=w(x).
Its log-coordinate density is the existing singular gain.

This is a paper candidate for a pairing forced by the two actual kernels,
not yet a Lean theorem or a physical Hilbert-domain identification.
The sum A+B should have a negative difference-square form after complete
paired integration. Individual rates diverge at h=0; they cannot be
split into separately admitted gain/loss terms. In particular, conjugating
a finite forward h-cutoff changes the reflected small-h cutoff by a factor
asymptotic to x^(-2). Paper analysis predicts a retained 2*log(x) diagonal
term in the adjoint of A, with the opposite term for B. An uncorrected
claim A*=B therefore needs testing, not acceptance. Complete increments,
cutoff changes, actual arithmetic source admission, and Xi occurrence
remain unpaid. These are the next hard mathematical targets.

All four endpoint-subtraction deep searches are terminal and preserved
in the raw record, with partial inventories of723712 declarations.
The contact search supplies generic phase-integral identities, not a
source Ward producer. The reversible search's suggested finite-fibre
stationarity and row-zero ingredient set does not identify these singular
ray generators. Actual RouteEPhysicalFibreCoarea and JumpFormAdjointness
proofs were read: the former uses a supplied finite physical fibre mass,
and the latter proves translation adjointness on admitted compact-support
products. Neither discharges this ray's inversion Jacobian, cutoff term
or physical source domain. No balance conclusion is imported from them.


Iteration24 endpoint scratch now passes with all23 public declarations
using only standard foundational axioms. The complete proof was promoted
to GammaMobiusEndpointSubtraction and wired once in RHTower. Targeted leaf
build is running. Lint currently fails solely on the unrelated unreachable
HTGeometry.ChronologicalTensor.CubicCuspPresentation module. No PW-B lint
violation was reported; this is not an all-repository passing audit.

Additional broad arXiv searches used reciprocity and equilibration. The
reciprocity date-ordered endpoint returned429; the equilibration listing
was cached through August18. Read the actual primary texts of
[On the kinetic Fokker--Planck equation in curved geometry](https://arxiv.org/html/2608.14904v1)
(August14), including its source-relative density, invariant weighted
measure, symmetric diffusion and skew transport decomposition in equations
2.14--2.16. Its compact-manifold kinetic generator is not this nonlocal
ray generator, so no symmetry, closure or coercivity result transfers
without identification. The decomposition motivates checking both the
full pairing and the retained adjoint correction separately.
[Aperiodicity is sufficient for macroscopic thermalization](https://arxiv.org/html/2608.13462v1)
(August13), Theorem2.4, uses actual return probabilities of a finite-dimensional
initial subspace to bound occupied dimensions and typical equilibration.
No such independently proved return bound, finite physical realization or
Xi occurrence map has been supplied here. These source requirements cannot
be replaced by a nominal equilibrium label. No numerical experiment or
calculation was performed or imported as proof.


Iteration24 targeted endpoint-subtraction build passed in255s. The log
records only this leaf as newly built; dependencies were reused.
Its session is terminal. All23 public source declarations, one-copy
umbrella wiring, local card links and exact equality with the passing
scratch proof bodies were checked. Index regeneration is now running.
A separate scratch tests the source-derived reversible density, its
uniqueness up to scale, inversion identity, actual source-square weight,
log-coordinate singular-gain identity and integrability. No individual
adjoint or complete source form-domain result is claimed from that scratch.


The exhaustive iteration24 API audit found one actual declaration-name
collision: the older FrullaniJointAdmission bound already uses
pwGammaFrullaniKernel_norm_le for a different bound. Renamed this leaf's
stronger bound to pwGammaFrullaniKernel_norm_le_nat and changed its one
use. All other22 public names are unique. The next scratch co-imports
FrullaniJointAdmission explicitly before rechecking all23 axiom reports;
then the final targeted rebuild and regenerated API will be audited again.
This is a source integration correction; no mathematical statement changed.


Paper cutoff calculation for the pairing attack: the forward displacement
cutoff y-x>delta becomes, at the target x, reflected displacement
h>delta/(x*(x-delta)), for 0<delta<x. The difference between that cutoff
and the native reflected cutoff is the literal interval integral
integral_[delta/(x*(x-delta)),delta] exp(-h)/h dh.
Write its integrand as 1/h+(exp(-h)-1)/h. The first integral is
log(x*(x-delta)), tending to2*log(x). The second tends to zero because
its complete integrand is bounded near0 and both endpoints tend to0.
This supplies an explicit candidate for the retained adjoint contact;
its sign reverses under inversion. A full operator adjoint still requires
admitted paired products and the transformed cutoff comparison. The next
Lean target is this actual contact limit, not an assumed adjoint relation.

The contact deep search is terminal; all candidate and source-argument
names and the proposed ingredient set were inspected. Actual source checks
show log_criticalCutoff is only log(exp(...)), cutoffLogPower_first is an
ordinary composed derivative, and criticalLogJumpAtom is a power-log mode.
They do not establish the moving-cutoff integral limit or this pairing's
adjoint. The all-parameter weighted-domain deep search is still running.


The first reversible-pairing scratch completed with verified pointwise
balance, inversion and the exact singular-gain log-coordinate identity.
It also reported local elaboration errors in source-square simplification,
continuity, and the ratio proof. Those have been repaired in the scratch
but are not yet rechecked. The full pairing leaf is not promoted or
claimed complete. Its two new deep searches are terminal and saved in
pw-b-gamma-reversible-pairing-searches.json. Both have partial coverage
of723712 declarations. The all-parameter search's proposed cusp-eigenform
decay theorem requires an actual Maass eigenform; generic bounded-weight
comparison requires uniform bounds unavailable for the singular source
weight. Their actual statements were read. Neither establishes this
arithmetic family's form domain or spectral realization.


Further paper attack using the existing complete reflected-atom bound:
for each z choose integer N>=norm(z). The proved inverse-square index
majorant bounds the full normalized reflected source by 1+C*x^(N+3).
Involution then bounds the original g_z=M_z/Q by 1+C*x^(-(N+3)).
Every integer moment of w is finite: for positive powers use
x^k*w(x)<=x^k*exp(-x); for negative powers use the exact inversion
identity w(1/x)/x^2=w(x). Thus the forced pairing should admit g_z
in L2(w dx) for every complex coefficient parameter. This deduction
still needs full Lean interchange and measure-change proofs; it is
not a verified critical spectral domain or a selector.

An exact source test targets the uncorrected individual adjoint claim:
phi_1=Q(x)/Q(x)=1 and phi_2=Q(2*x)/Q(x)=sqrt(2)*exp(-x).
The actual forward Frullani generator has A phi_1=0 and
A phi_2=-log(2)*phi_2, while B phi_1=0 by source fixation.
The pairing integral integral w*phi_2 is finite and strictly positive.
Therefore <phi_1,A phi_2> differs from <B phi_1,phi_2> by the
strictly negative value -log(2)*integral w*phi_2. This is a concrete
candidate refutation of A*=B on a domain containing these source modes,
with a positive nonzero cross-pairing as survivor. Formalize the actual
admission, positivity and generator values before claiming that no-go.
The corrected individual adjoint and symmetry of A+B remain live.


The proposed contact sign is consistent with a second exact source
identity. The positive cross-density w*phi_n is proportional to
exp(-n*x-1/x)/x and is invariant under x ->1/(n*x), with its Jacobian
retained. Thus its logarithmic moment, once admitted, is
integral log(x)*w*phi_n = -(log(n)/2)*integral w*phi_n.
At n=2 this makes the proposed 2*log(x) contact exactly account for the
nonzero ground-to-mode adjoint defect above. Both the value identity and
logarithmic admission are new paper conjectures pending Lean, not a
spectral balance law. They provide a source-level check on the cutoff
calculation without a numerical test or a special-function continuation.


The renamed endpoint-subtraction scratch now passes while explicitly
co-importing FrullaniJointAdmission. All23 axiom reports contain only
propext, Classical.choice and Quot.sound. This closes the actual namespace
collision; no statement or proof mechanism changed. Final targeted leaf
rebuild, regenerated index and final lint are running. Only one owned
Lean build process is active.


Iteration24 endpoint-subtraction final audit complete. Final targeted
leaf build passed in70s, rebuilding only this leaf. Final co-import
scratch passed all23 standard-only axiom audits. Index regeneration
passed (seven changed entries, zero removals in the shared tree), and
all23 public names are unique in API and source corpus. One umbrella
import, exact scratch proof-body agreement, local links and scoped
whitespace were checked. The final lint still reports only the unrelated
unreachable HTGeometry.ChronologicalTensor.CubicCuspPresentation module;
this is not a repository-wide passing lint result. All endpoint build,
research, index and lint sessions are terminal. No full or umbrella
build, numerical experiment, added axiom, commit or push occurred.

The next live target is now recorded in pw-b-gamma-reversible-pairing.md.
Its repaired16-declaration scratch is being checked as the sole owned
Lean process. RH, actual Xi occurrence, critical source control and
independently source-forced Ward balance remain open.


Iteration25 pairing progress: the repaired16-declaration scratch passed
with only standard foundational axioms. It proves uniqueness up to scale,
source-square identification, exact existing singular gain, inversion and
integrability of the explicit weight, along with weighted rate balance.
The sole owned Lean process now checks two additional declarations: the
actual reciprocal-displacement derivative and the exact rate with its
Jacobian retained. No operator adjoint or Xi realization follows merely
from these pointwise identities; the contact and actual source-domain
attacks remain as recorded in the dedicated card.


The displacement derivative and backward rate/Jacobian proof both
produced standard-only proof terms. The combined18-declaration run
reported only one trailing redundant ring tactic (No goals to be solved),
which was removed. The exact final scratch is being rechecked before
promotion. This establishes a density-level change-of-variables identity,
not a full integral substitution or operator adjoint.


Iteration25 reversible-density final audit complete. All18 public
declarations pass with only standard foundational axioms, including the
actual reciprocal derivative and rate/Jacobian identity. The new leaf
ThetaCuspHawkingParikhWilczekGammaReversibleDensity was promoted with
identical proof bodies and wired once in RHTower. Targeted build passed
in12s, building only this leaf. Index passed (eleven changed entries,
zero removals in the shared tree); all18 public names are unique in
API and source corpus. Final repository lint passed: the earlier unrelated
CubicCuspPresentation import failure is absent. Build, scratch, index,
research and lint sessions are terminal. No full or umbrella build,
numerical experiment, added axiom, commit or push occurred.

The next turn must begin with the verified chain: first-winding PW
response -> FE signed defect -> positive source-derived pairing and
complete Ward transmutation -> independently forced fixed-grade balance
at actual Xi occurrences -> RH. The density/Jacobian is now verified
within the pairwise-balance class; imposing that class physically, the
actual adjoints, arithmetic form domain, Xi occurrence and source-forced
balance remain unproved. Attack the explicit moving-cutoff contact limit
and finite positive Gamma-mode cross-pairing in
pw-b-gamma-reversible-pairing.md; then test the complete arithmetic source.
Do not claim RH, operator symmetry or a physical Xi spectrum from density
uniqueness. PW-B and the goal remain active.


## Iteration26 — literal adjoint contact and actual source cross-test

The preceding goal turn was verified progress: endpoint subtraction and
reversible density are promoted, all41 public axiom audits and targeted
builds pass, umbrellas are wired, final index checks and repository lint
pass. Current source and logs were rechecked. RH remains unproved.
Now attack the actual adjoint gap, not a new density choice. The contact
is the literal interval integral from delta/(x*(x-delta)) to delta of
exp(-h)/h. On positive h, |(exp(-h)-1)/h|<=1, so subtracting the admitted
1/h integral leaves an error bounded by the distance between the two
endpoints. Both endpoints tend to zero. This proves the proposed2log(x)
limit without requiring a continuous value at h=0 or evaluating a
singular totalized product. In parallel, inspect source-ground/second-mode
pairing admission, positivity and actual generator values, to test the
uncorrected adjoint against concrete source data. Two new deep method
searches are running; broad arXiv transport/defect searches have begun.


Iteration26 source cross-test now has an explicit scratch construction.
The normalized positive Gamma mode is Q(n*x)/Q(x), with its actual
source-ratio proof retained. The original forward response uses literal
weighted translation before division by Q; its whole h integral should
be -log(n) times that same mode. The backward response uses the actual
reflected translation of Q and should vanish by source fixation. The
proposed weighted cross-mass is finite and strictly positive for every
positive n, and every such mode has finite weighted squared norm. Thus
for n>1 the fully admitted paired responses should differ by the strict
negative value -log(n) times the cross-mass. This tests the uncorrected
adjoint on actual source data; it is not a claim of an already constructed
closed operator. The28-declaration scratch is written but not yet run;
the contact scratch remains the sole owned Lean process.

Both initial deep searches are terminal and their raw records saved in
pw-b-gamma-adjoint-contact-searches.json, partial coverage723712.
All candidate/source-argument names and ingredient sets were inspected.
The generic metric-adjoint decomposition assumes bounded operators and
an already repaired adjoint relation; it cannot produce this singular
source correction. The finite Gamma boundary vector/range theorem is a
factorial rank-one construction, not these ray modes. The parametric
primitive continuity lemma requires an actually continuous integrand;
using the direct complete remainder bound avoids silently extending the
singular written integrand at0. A third boundary-rigidity method search
is running.

Broad arXiv queries used transport and defect; transport's date-ordered
listing was cached in July, while defect yielded September10 papers.
[Optimal feedback control under stepwise equilibration and partial observation](https://arxiv.org/html/2607.21523v1)
(July23), SectionsII--III.1, obtains its work decomposition after assuming
complete equilibration between interventions and accounting separately
for observation-conditioned updates. Its reset and finite-cycle law have
not been established for this source, so no stationarity transfers.
[Electrovacuum Black Hole Uniqueness](https://arxiv.org/html/2609.11140v1)
(September10), Theorem1.1 and Section3, retains a nonlinear differential
inequality, exhaustion boundary estimates and axis analyticity in its
rigidity argument. No such harmonic-map equations, asymptotic class or
axis analyticity have been identified for the arithmetic source. The
paper motivates testing an actual signed forcing and boundary law before
using a maximum principle; its geometric hypotheses are not adopted as
premises. The SYM one-point paper2609.09303 was also opened, but no
applicable cutoff identity has been identified. No experimental or
numerical result was used as mathematical proof.


The third boundary-rigidity search is terminal and saved beside the first
two records. Its source-reflection rigidity theorem assumes the exact
reflected quadratic source equals the conjugate source at a Xi copy;
it does not produce that equality. The finite conservative/dissipative
master generator uses a finite jump matrix. The causal-generator
dissipation theorem requires its already constructed contraction orbit
and generator domain. None identifies the current singular arithmetic
operator or discharges its full adjoint/domain gap.

The primary text of
[One-point functions of the Lagrangian in N=4 SYM with boundaries, defects and interfaces](https://arxiv.org/html/2609.09303v1)
(September8), Section2, was inspected further. Its integrated insertion
retains boundary contributions and a regulated finite part; its matrix
model relation retains identity mixing. Coupling differentiation is not
a stationarity law. This motivates retaining the complete insertion and
contact here, but no supersymmetric localization or interface action has
been identified for PW-B. No theorem is transferred from that model.

A fourth deep method search now targets the admitted logarithmic moment
under scaled reciprocal substitution. The exact source cross-density
has a candidate involution x -> 1/(n*x). An integral substitution and
logarithmic admission would test whether the literal cutoff contact
accounts for the whole ground-to-mode adjoint defect. They would still
not prove the operator identity on the full arithmetic domain.


The logarithmic-moment method search is terminal, partial coverage723712,
and its raw result is saved under log_moment in the contact search record.
All20 candidate statements,20 source-argument statements and the complete
proposed ingredient set were reviewed. The suggested eval_recipSub is
an algebraic evaluation law for reciprocal derivative jets, not an
integral change of variables. The inverse-scaled atomic-moment theorem
assumes an existing atomic representation and rescales its nodes. Neither
applies to this continuous reciprocal source measure. The actual mathlib
one-dimensional Jacobian theorem was read directly: it requires the
derivative, injectivity and measurable source set, all of which can be
proved for x ->1/(n*x). The separate logarithmic exponential majorant
will justify linearity of the two resulting finite integrals.

The third cutoff scratch failed only at pointwise-function simplification;
all integral estimates and the positive-cutoff identities already have
standard-only proof terms. Pi.div_apply did not rewrite an unapplied
function. The source-verified Pi.div_def rewrite is now being checked
in the sole owned Lean process. No cutoff-limit success is claimed yet.


The final cutoff scratch passed: all nine public declarations report
only propext, Classical.choice and Quot.sound. The literal contact limit
is now proved. Identical proof bodies are promoted in
ThetaCuspHawkingParikhWilczekGammaAdjointCutoffContact and wired once in
RHTower. Its targeted leaf build is the sole owned Lean process; final
index/name/lint audits remain pending. The formalized contact card,
frontier and route-independent cutoff constraint now record exactly this
result. Source-mode and logarithmic-pairing claims remain pending.

The logarithmic moment proof has been written as an unrun body in
/tmp/pwb-gamma-adjoint-log-moment-body.txt. It derives positivity,
involution, image and actual derivative of x ->1/(n*x); the exact
cross-density/Jacobian identity; an exponential logarithmic majorant;
the admitted moment equation; and equality of the contact pairing with
the existing source-mode defect. Do not import or claim these pending
proofs before checking the actual source-test module and this body.
The cutoff limit still does not justify exchange of its limit with the
whole source integral or an arbitrary-domain adjoint identity.


Cutoff-contact final audit complete: target build passed in193s, building
only the new leaf. All nine public names are unique in source and API;
proof bodies exactly match the passing scratch. Index passed (four
changed entries, zero removals), and repository formal lint passed.
All cutoff scratch/build/index/lint sessions are terminal.

The first source-mode scratch produced standard-only axiom reports for
all28 declarations, including the exact strictly negative paired defect
for every n>1 and its admitted strictly positive cross-mass. The overall
file reported only one redundant ring after a solved field_simp goal.
That tactic was removed and the exact final source scratch is being
checked as the sole owned Lean process. Promotion and its final audits
remain pending; the wider route is not retired.


Source-test final audit complete. All28 public declarations pass with
standard-only axioms, and their exact proof bodies are promoted in
ThetaCuspHawkingParikhWilczekGammaAdjointSourceTest. One umbrella import
is wired. Targeted build passed in230s, building only this leaf; index
passed (five changed entries, zero removals), all28 public-name/API
uniqueness checks passed, and repository formal lint passed. All
source-test scratch/build/index/lint sessions are terminal. The source
test card and frontier record the exact negative defect and positive
finite cross-mass. PW-B and RH remain open.

The11-public-declaration logarithmic-moment scratch now runs as the sole
owned Lean process. It co-imports both finished leaves and uses the
actual one-dimensional Jacobian theorem. Its names had no prior source
collisions. No moment identity is claimed before this verification.

The flat-endpoint method search is terminal, partial coverage723712,
and saved under flat_endpoint in the contact search record. All20
candidate statements,20 source-argument statements and the proposed
ingredient set were reviewed. The suggested uniform-difference theorem
already assumes uniform derivative convergence. The suggested complex
Gronwall theorem assumes an entire function and a global derivative
bound. Neither supplies the positive-ray flat reciprocal derivative
bound; this must be derived from the explicit exponential source as
recorded in the pairing card.


The first logarithmic-moment scratch stopped at local Lean issues:
normalization of reciprocal multiplication and its derivative, an
absolute-value parser spacing issue, a redundant ring, and beta-reduction
before rewriting the pulled-back scalar product. The actual cross-density
Jacobian formula already produced a standard-only proof term. These
issues were repaired in the actual scratch and a second check is running
as the sole owned Lean process. The moment and complete contact-pairing
identity remain unverified until this check succeeds. The original body
text is now stale; use /tmp/pwb-gamma-adjoint-log-moment.lean.


The second logarithmic-moment scratch proves the cross-density formula,
positive reciprocal involution/image, exact cross-Jacobian identity and
actual logarithmic integrability with standard-only proof terms. Its
remaining failure is normalization of the derivative's unapplied
function, plus one redundant ring in the majorant proof. The actual
reciprocal derivative formula is unchanged; an explicit function target
and restricted Pi.inv_def simplification are now being checked in the
sole owned Lean process. The final log is
/tmp/pwb-gamma-adjoint-log-moment-scratch-final.txt. Do not claim the
integrated moment or contact identity before a terminal passing result.


The final logarithmic-moment scratch passed all11 public declarations
with standard-only axioms. Identical proof bodies are promoted in
ThetaCuspHawkingParikhWilczekGammaAdjointLogMoment, wired once, and the
targeted build passed in168s, building only this leaf. Index passed
(four changed entries, zero removals), and all11 source/API names and
exact scratch proof bodies were checked. The three new leaves therefore
close48 public declarations, including the actual admitted contact
pairing. All owned Lean scratch/build processes are terminal.

The first final repository lint failed solely because the concurrently
added unrelated Sieve.MenonHarmonicSieveSwappedReceiver was unreachable.
Its umbrella import is now present in the shared tree; a final lint
rerun is checking that changed state. No unrelated source was edited
or built. The moment card and predecessor cards now separate the proved
mode-level identity from the still-open full cutoff transposition and
source/domain/Xi/Ward obligations.


Iteration26 final audit complete. Final repository lint passed after the
concurrent Sieve umbrella change appeared; no unrelated file was edited
or built here. All48 public declarations across the three new leaves
pass their standard-only axiom audits and targeted builds (contact193s,
source test230s, logarithmic moment168s). Every public name is unique
in source and API; every promoted proof body matches its passing scratch;
each leaf is wired once. All four result/continuation cards have valid
relative links and scoped whitespace checks pass. All owned scratch,
build, research, index and lint sessions are terminal; a process check
found no remaining owned adjoint Lean/lake process. No full or umbrella
build, numerical experiment, added axiom, commit or push occurred.

This is verified progress, not RH closure: the literal2log(x) contact is
proved and its admitted pairing accounts exactly for the complete
ground-to-mode source defect. The next turn must state the chain
PW first-winding response -> FE signed defect -> complete source adjoint
and arithmetic domain -> independently source-forced fixed-grade Ward
balance at actual Xi occurrences -> RH. Full original cutoff
transposition must retain the empty incoming region and both remaining
regions. The sharper flat reciprocal derivative bound attacks the
unpaid complete arithmetic endpoint and any proposed scalar occurrence
of the unmodified source. Those proofs, physical necessity of the
pairing, actual Xi occurrence and independent balance remain open.
Use the continuing pairing card for the exact paper bounds and next
proof obligations; do not assert that a mode-level correction proves
a closed operator or a Ward selector. PW-B and the goal remain active.


## Iteration27 — uniform reciprocal derivative and actual arithmetic endpoint

The prior turn is verified progress: all48 new public declarations,
three targeted leaf builds and final lint are complete. Current cards,
source kernel, build log and final lint were rechecked. RH is not proved.
The next hard target is the v->0+ limit of the complete reciprocal
generator. The old bound retains1/v, so it cannot justify that limit.
Conjecture: derive the exact derivative a/v^2*exp(-a/v), bound it by
(k+2)!/a^(k+1)*v^k, and use the mean-value theorem on[v,v+h]. This
removes1/v from the whole difference quotient. An admitted common
Gamma majorant should then allow the actual endpoint integral and
complete arithmetic sum, rather than the value of the totalized kernel
atv=0. Two new deep method searches are running; broad single-word
relaxation/dilation searches have begun. The general search returned
mostly old papers despite its recent filter; the date-ordered arXiv
dilation listing supplies September2026 candidates.

The first corrected flat-endpoint scratch passed all seven public
declarations with only propext, Classical.choice and Quot.sound. It
derives the reciprocal exponential's actual derivative, its arbitrary
polynomial flat bound, the complete mean-value kernel bound, the positive
endpoint kernel exp(-h-a/h)/h and pointwise right-limit convergence.
The original formula evaluated at v=0 is not that limit: totalized
division gives exp(-a/0)=1. The proof instead establishes exp(-a/v)->0
on v->0+. The bound at k=0 is 2!*exp(-h)/a, uniformly for every v>0.
An extended scratch now tests L1 convergence and the actual integral
limit. This passage, and subsequent full arithmetic summation, are
required before asserting any source endpoint or spectral exclusion.

The two new deep searches are terminal and preserved in
[flat-endpoint search records](pw-b-gamma-reciprocal-flat-endpoint-searches.json).
The derivative search reports partial coverage of723739 declarations.
The integral search reports pending coverage generation823353, without
a declaration count, and local-model JSON/runtime, Qdrant timeout and
BrokenPipe errors. All20 candidate and20 source-argument statements per
search, and all available ingredient sets, were examined despite this
incomplete coverage. No service was restarted. Suggested Hankel-head
flat-face and reciprocal Gauss-node polynomial results assume unrelated
positivity/root data. Entire-function Gronwall and uniform derivative
convergence results assume the missing estimate. The actual mathlib
mean-value theorem supplies the derivative-to-kernel step. The actual
GaussianWindowMomentRescaling.tendsto_gaussianCooledMoment proof and
mathlib's filter dominated-convergence theorem supply the integral
method, with a new explicit source majorant proved here. A third deep
method search now targets uniform convergence of the complete series.

Broad single-word relaxation/dilation searches were followed by the
date-ordered arXiv dilation listing; the relaxation listing timed out.
Two September9 primary papers were read beyond their abstracts.
[When Finite Free Curves Split](https://arxiv.org/html/2609.10367v1)
starts with real-rooted finite-free inputs and obtains a definite
symmetric pencil from hyperbolicity. Its Jacobian defect is an
off-diagonal squared norm; vanishing forces commuting matrices and
splitting. Input incidence and simplicity still matter. No corresponding
hyperbolic source pencil has been derived for PW-B, so those premises
cannot be imported. The transferable question is whether the complete
source defect has an independently justified positive representation.

[A Separation between Full-Rank PVM and Assumption-free Self-Testing](https://arxiv.org/html/2609.10013v1)
classifies an optimal face by tracial states of C plus M2. Requiring
supported projectivity removes the matrix summand. Restricted-class
closure does not commute with selecting the exact optimal face;
near-optimal projective strategies need not approach the reference
under the required dilation. No Bell-game realization of the PW source
was identified. This supplies a precise warning for the open physical
selection step: a dense admitted class alone does not determine the
exact zero-defect states. Neither paper supplies Ward balance or RH.

The extended scratch then passed all eleven public declarations,
including actual endpoint integrability, strictly positive finite mass,
L1 convergence of the original kernels and convergence of their
integrals. The polynomial extension proves the integrability of
exp(-h)*(1+h)^k and the uniform original integral bound on0<v<=1.
Its endpoint-bound proof had one remaining tactic mismatch (positivity
was applied to h<=1+h); that is repaired and the final scratch is
running alone. The immediately preceding run has thirteen standard-only
declarations, not a fully passing file. No leaf has yet been promoted.

The third deep method search is terminal, saved under series in the
flat-endpoint record. It reports partial/pending generation823353 and
semantic-worker disconnection and reranking deadline errors. All20
candidate statements,20 source-argument statements and the complete
proposed ingredient set were reviewed. The Dirichlet and exponential
series candidates assume uniform or normal summability; positive moment
form candidates additionally assume positivity and bounded kernel roots.
The integral-sum theorem requires a summable bound and admitted sum.
The local SuzukiWeilAppendixDerivative.tendsto_tsum_suzukiVerticalLerchTerm
proof and mathlib Tannery theorem were read directly. They provide the
applicable eventual-uniform-majorant method. The source-specific bound
is derived from the new flat derivative estimate, not supplied by the
search result.

The next scratch, /tmp/pwb-gamma-arithmetic-endpoint.lean, is written but
has not been run. It retains the actual signed coefficients and uses
the existing complete source-current integral-to-series identity. The
first two response terms vanish. For n>=2 and |z|<=N, the coefficient
norm is at most n^(N+1), and k=N+2 gives a common inverse-square tail.
Tannery should give an absolutely summable finite endpoint for every
complex z. The scratch also connects this limit to the literal original
current divided by Q(v), rather than merely a new coefficient series.
Neither the full arithmetic endpoint nor any spectral exclusion is
claimed until this check succeeds. The active proof chain still lacks
full adjoints, independent physical selection of the pairing, actual Xi
occurrence and independently forced Ward balance.

The final repaired endpoint scratch passed all14 public declarations
with standard-only axioms. Exact bodies are promoted in
ThetaCuspHawkingParikhWilczekGammaReciprocalEndpoint and wired once.
The targeted leaf audit passed, building only that leaf in15s; the
other dependencies were replayed. Index passed with two changed entries
and zero removals. Final source/API uniqueness and repository lint are
being checked. The complete arithmetic endpoint scratch is now running
as the sole owned Lean process, importing the audited endpoint leaf.

New broad single-word dissipation/resolvent web searches again returned
mostly older papers despite their recent filter. The date-ordered arXiv
dissipation listing yielded September10 papers; the resolvent listing
returned an internal error. The primary
[Quantitative Diffusive Limits for Singular Nonlocal Transport](https://arxiv.org/html/2609.11837v1)
was inspected through its available abstract and introduction; its HTML
stops at the model equation. It assumes smooth strictly positive data
on a compact connected boundaryless manifold and states uniform
approximation through a resolvent energy. These hypotheses have not
been identified for the noncompact signed PW source. No proof or
theorem transfer is claimed from the truncated HTML.

The primary
[An Anisotropic Onsager Criterion](https://arxiv.org/html/2609.11488v1)
was read through its theorem discussion, commutator decomposition and
horizontal-dissipation argument. It derives horizontal energy
regularity for existing weak PDE solutions assuming space-time L4 and
critical vertical Besov regularity. A doubly truncated balance absorbs
horizontal commutator flux; the vertical flux needs separate control.
An additional vanishing high-frequency Besov tail gives energy
equality. The transferable method is to derive domain control from the
original truncated balance and bound each remaining flux. PW-B still
lacks the corresponding complete source balance and independently
proved domain hypotheses. Neither positivity of its rate density nor
the new arithmetic endpoint supplies these premises.

The complete arithmetic endpoint is now verified. All11 public
declarations in ThetaCuspHawkingParikhWilczekGammaMobiusReciprocalEndpoint
pass standard-only axiom audits, the targeted40s leaf build, exact
scratch-body comparison, all-name source/API uniqueness, single umbrella
import and final repository lint. Index passed with two changed entries
and zero removals. Together the two endpoint leaves close25 public
declarations. Their scratch/build/index/lint processes are terminal.

The next skew-occurrence deep search is terminal and saved under
skew_occurrence in the same search record. It has no reported errors,
but partial coverage of730452 declarations and substantial stale/pending
compiler and method metadata. All20 candidate statements,20 source
argument statements and the complete ingredient set were examined.
Many source-argument hits are definitions with no extracted method.
The proposed Sonin translation/Mellin ingredients require an identified
L2/strong-log carrier. The finite chiral metric-adjoint result is a
matrix identity; the finite Euler adjoint assumes an existing bounded
operator source. None constructs the current nonlocal operator domain
or an actual Xi eigenvector. Bare transform covariance cannot replace
those missing premises.

A direct source test now attacks the proposed corrected skew formula.
The scratch /tmp/pwb-gamma-skew-source-endpoint.lean proves, with
standard-only terms, M_z(x)/Q(x)->1 and E_z(x)/Q(x)->0 at infinity for
every complex z. It uses the full admitted coefficient series at x=1
as its common summable majorant. Actual inverse-gain reflection of the
new complete reciprocal endpoint gives the finite limit of
R(H(R M_z))(x)/Q(x). Hence the literal corrected source expression

`K_z(x)=E_z(x)-R(H(R M_z))(x)-2*log(x)*M_z(x)`

has exact leading quotient K_z(x)/(Q(x)*log(x))->-2. These five public
declarations have standard-only proof terms, but the file is not yet
promoted: its scalar-exclusion proof initially used a nonexistent
Complex.ofNat_re name. The contradiction is now expressed directly as
nonvanishing of -2 in C. The final scratch is running as the sole owned
Lean process.

The positive-survivor extension is being checked in that same scratch.
Adding the explicit logarithmic ground correction 2*c*log(x)*Q(x)
changes the leading quotient to2*c-2. A scalar identity with the
ground-subtracted field M_z-c*Q therefore forces c=1. This is an exact
necessary correction coefficient, not existence of a corrected scalar
mode or a full-domain adjoint. It cancels the leading obstruction for
every z and cannot alone select Xi zeros. Full transposition, physical
necessity of the pairing, actual Xi occurrence and an independently
forced Ward law remain open. PW-B is not being retired.

Iteration27 final audit complete. The full skew-source scratch passed
all8 public declarations, including the scalar exclusion, exact
correction limit and unique ground coefficient. Exact bodies are
promoted in ThetaCuspHawkingParikhWilczekGammaSkewSourceEndpoint,
wired once, and its targeted leaf build passed in211s. Index passed
with two changed entries and zero removals. All8 source/API names are
unique, promoted bodies exactly match the passing scratch, and final
repository formal lint passed. This leaf has only redundant-tactic
style warnings. The three new leaves close33 public declarations with
standard-only axioms; their targeted builds took15s,40s and211s and
built only their respective leaves. All owned scratch, build, research,
index and lint sessions are terminal; a process check found no remaining
owned PW Gamma Lean/lake or research process.

The next goal turn must retain the full chain: PW response -> FE signed
defect -> complete source adjoints/domain and positive Ward transmutation
-> independently source-forced fixed-grade balance at actual Xi
occurrences -> RH. The previous turn is verified progress: it closes
the complete arithmetic endpoint, excludes the unchanged-source scalar
ansatz and proves the unique leading ground correction. PW-B and RH
remain open. The continuing pairing card records a concrete next
conjecture/proof target: prove exponential decay of the complete
ground-subtracted normalized source, then identify the next retained
skew boundary value as minus the complete endpoint B_z. This would
give B_z=0 as a necessary condition for a corrected scalar equation,
not produce that equation or identify its parameters with Xi zeros.
Full original cutoff transposition, physical necessity of the chosen
pairing, corrected source incidence and independent Ward balance must
still be attacked. No full or umbrella build, numerical experiment,
added axiom, subagent, commit or push occurred.


### Iteration28: retained boundary after the forced ground correction

The target is the complete signed tail, not a finite approximation. For
d_n=GlobalAtom(z,n,1)/Q(1), absolute summability and the exact mode shift
give |M_z/Q-1| <= (sum_n |d_(n+2)|) exp(-(x-1)) for x>=1. This should
force log(x)(M_z/Q-1)->0 and identify the corrected residual divided by
Q as -B_z. A corrected scalar equation must then satisfy B_z=0. The
vanishing condition is a boundary test, not an established Xi incidence
or a sufficient occurrence theorem. Full cutoff adjoints, physical
necessity of the pairing and independent Ward balance remain open.
The previous33 public declarations and final lint remain verified.


Three deep searches are terminal and saved in
pw-b-gamma-ground-boundary-searches.json. All20 candidates and20 source
arguments in each, plus their complete ingredient sets, were reviewed.
Coverage is partial730597 declarations. The ground-tail and incidence
queries report no errors; the moment query reports a semantic runtime
deadline. Compiler metadata remains largely pending. Method freshness
improved across snapshots but does not certify applicability. The
proposed finite ladder separation cannot establish continuous moment
uniqueness; Laplace-boundary linearity and angular inversion do not
construct this reciprocal source's boundary expansion. An exhaustive
source search identified the directly relevant local exponential-window
complex-density uniqueness theorem in HTGeometry.LocalExponentialTestClosure.
Its actual finite-measure, exponential-window and L2 premises were read.
A focused mechanism search is now running to audit related proof ideas.

Broad single-word arXiv searches used memory, elasticity and friction.
General web results returned older papers; the date-ordered memory and
friction listings returned September2026, while elasticity listings
failed to fetch. Most memory hits were AI/hardware work with no useful
analytic transfer. Two primary friction-search papers were inspected:
Boundary control for optimal mixing by two-dimensional second-grade
fluids, arXiv2609.09946v1, September9, especially Remark8.1 and Lemma8.3;
and Well-posedness and exponential stability for abstract evolution
equations with delay in the nonlinear source: frictional and viscoelastic
cases, arXiv2609.08986v1, especially Theorem3.2 and its explicit stability
and small-Lipschitz premises. The former derives weak adjoint duality
through common Galerkin limits and does not infer strong boundary traces
from insufficient regularity. The latter requires an existing stable
semigroup, delay bounds and independently justified small-data control.
Neither supplies PW-B's source incidence or Ward law.
Sources: https://arxiv.org/html/2609.09946v1 and
https://arxiv.org/html/2609.08986v1.

First scratch failed at an infinite-sum rewrite: rewriting division
selected the shifted tail rather than the complete sum. It is corrected
with an explicitly typed full-sum identity. An expanded sole foreground
scratch now also checks all polynomially weighted source/current tails
and the rapid reciprocal-current decay required by the corrected scalar
equation. All moment extraction and uniqueness remain unformalized;
the pairing card records their explicit quantitative proof candidate.


The fourth deep search is terminal, saved as local_window: partial
coverage730613 declarations and a decomposition runtime deadline.
All20 candidate statements,20 source arguments and the full proposed
ingredient set were examined. Its proposed AllZero monomial theorem
concerns exponent lists, not vanishing integral moments; the Stokes
germ isomorphism likewise does not identify this density. The actual
local exponential-window density theorem found by source inspection
remains the relevant method. No search-generated implication was used
as a proof.

The all-moment proof candidate can avoid differentiating the complete
source: the already verified per-mode reciprocal flat-kernel bound,
summed with a sufficiently high inverse-power coefficient majorant,
makes the original0<h<v integral flat at each fixed order. Elementary
exp-series bounds and Gamma integrability similarly admit each moment
and control its removed0<t<2v piece. This identifies exact next Lean
obligations without assuming a complete source derivative theorem.


A stronger preferred positive survivor emerged from the actual corpus
Schlaefli/Gamma coefficient mechanism (BesselK1RayCoefficients, read in
full): J_j(z)/Gamma(j) should tend to the nonzero n=2 arithmetic
coefficient as j->infinity. Inverting each positive endpoint integral
and using1-a/u<=exp(-a/u)<=1 gives an explicit Gamma squeeze. A single
large fixed inverse-power majorant controls every n>=3 contribution
for all later j. This avoids the separate L2 density construction and
all-z leading source theorem. The exact bounds and next formal steps
are recorded in the pairing card. The original full cutoff expansion
is still needed before this candidate can exclude the corrected ansatz.


Iteration28 final audit complete. All10 public declarations are promoted
in ThetaCuspHawkingParikhWilczekGammaGroundBoundary with exact passing
scratch bodies and standard-only logical axioms. One umbrella import
is wired. Only the targeted leaf was built, in482s; its dependencies
were replayed. Index passed with zero changed entries and zero removals
(the shared search index already contained the source). All10 public
source and API names are unique. Repository formal lint and scoped
tracked-file whitespace checks passed. Remaining Lean diagnostics are
redundant-tactic style warnings. No full/umbrella build, added axiom,
numerical experiment, subagent, commit or push occurred.

The fifth deep query is terminal and saved as high_order. Its coverage
reports only pending generation872787, with rerank/semantic runtime
deadlines and a filter/worker disconnect. All20 candidates and20 source
arguments were examined; there is no ingredient set. The reciprocal
Gamma-function inverse lemmas are not the needed inverse change of
variables in the endpoint integral. Existing original-source kernel
bounds and the Gamma recurrence remain the verified starting points.

The preferred next attack is the quantitative high-order endpoint
moment detector. For fixed admitted p, the candidate error is
|J_j/Gamma(j)-a_2| <= |a_2|/(j-1)+C_z,p*2^(p-j). First prove the
reciprocal integral substitution and Gamma squeeze, then this full
signed-series bound. Next derive the all-order expansion from the
original cutoff integral using the already verified kernel flat bound,
and extract moments from the all-power current flatness now proved.
This could exclude the unit-corrected scalar ansatz while yielding
nonzero high-order moments as its positive survivor. Neither statement
is being claimed formalized yet; PW-B is not retired and RH is unproved.

The complete goal chain remains PW response -> FE signed defect ->
complete source adjoints/domain and positive Ward transmutation ->
independently forced fixed-grade balance at actual Xi occurrences -> RH.
The source-tail and necessary boundary results are verified progress;
full original cutoff transposition, physical necessity of the pairing,
actual Xi occurrence and independent Ward balance remain hard gaps.


### Iteration29: normalized high-order endpoint moment

Previous turn is verified progress: the actual482s leaf build and final
lint logs were revalidated. This turn attacks the reciprocal integral
substitution and Gamma squeeze, then the complete signed moment
coefficient recovery. A new deep inversion-method search is running.
User now explicitly forbids further #print axioms checks; comply.
Continue kernel checking with lake env lean scratch files, targeted
leaf build and the existing no-added-axiom/source lint discipline.


Iteration29 mathematical target is now closed in scratch. The reciprocal
positive kernel substitution, Gamma squeeze, main-mode error bound,
main-mode limit, later-mode limit and arbitrary inverse-mode bounds
are proved in GammaReciprocalMoments; its targeted leaf build passed
in61s. The complete signed source moment is absolutely admitted at
every order, with exact source/series integral equality. A single
inverse-square majorant independent of every later moment order
recovers the actual nonzero n=2 coefficient. Every sufficiently high
actual moment is nonzero for each complex z. GammaMobiusMomentDetector
scratch passed; its targeted leaf build is running. No numerical
experiments or axiom-print checks were used.

The remaining immediate mathematical obstacle is original-cutoff
extraction: split h<v and h>=v, use the already proved kernel flat
bound on the near part, and a finite geometric expansion of1/(t-v)
after t=h+v on the far part. The complete source controls removed
small-t moment pieces and the logarithmic loss. This should derive
each moment from the already proved all-power current flatness, but
that extraction is not yet a Lean proof. The corrected scalar ansatz
is not retired. Full adjoints, actual Xi occurrence and independent
Ward balance remain open, so RH remains unproved.


Iteration29 final mathematical and build status: all three new leaves
passed scratch and targeted leaf builds (61s,175s,76s); final formal
lint passed. Each has one umbrella import. The complete actual-source
high-order moment detector is closed. A new conjecture loop tested
using a convergent-power-series API for the remaining extraction:
the actual moment terms fail to tend to zero at every nonzero complex
argument, proved in GammaMomentDivergence. The strongest positive
survivor is the admitted full signed moment family and its nonzero
Gamma-normalized first-coefficient limit, already closed in Lean.
The narrow failed-series card records both statements; PW-B remains
live. Finite asymptotic extraction, not an assumed convergent series,
is the next attack.

All three deep/method searches are terminal and saved in the moment
search JSON. Each set of20 candidates and20 source arguments was
inspected. The third has partial coverage730859 and no reported
errors; its analytic approximation requires an unavailable series
premise, and its generated finite-geometric/cutoff plan does not
retain the actual moving-boundary terms. The actual corpus factorial
decay proof and mathlib source yielded the new divergence theorem.
Broad recent curvature/drift searches and primary Thorpe-pairing
reading supplied an exact-annihilator correction idea only; no PW
annihilator, Xi occurrence or Ward orientation follows from it.

The user instruction to stop axiom-print checks is saved separately
in Serena memory rh/pw_b_user_no_axiom_prints_2026_09_11 and remains
in force. No further such checks, full builds, numerical experiments,
subagents, commits or pushes occurred.

### Iteration30: original cutoff coefficient extraction

Previous turn classified as verified progress: the actual moment-divergence
leaf build and final lint logs were revalidated, the current source-integral
and eventual nonvanishing declarations were read, and no owned Lean process
was live. This turn attacks the original near/far cutoff decomposition,
source-flat bounds uniform enough for the removed moment pieces, and the
finite geometric remainder. A new deep/method search is running. No
convergent-series premise will replace the missing finite asymptotics.
The existing exact full-source moment detector is the contradiction target;
full adjoints, Xi occurrence and independent Ward balance remain open.

Iteration30 source checkpoint: the complete reciprocal tail has an arbitrary-order
flat bound and a global polynomial bound. The normalized response is proved equal
to the original admitted same-source response divided by Q(v), so its integral is
the original current/Q(v). The near-diagonal integral is flat to every order.
Every endpoint integrand exp(-t)S_z(t)/t^(j+1), including j=0,1, is absolutely
admitted. Its removed initial integral is flat at every requested order, and
B_(k+2) is exactly the already nonzero high-order moment. Eighteen public theorems
in GammaReciprocalCutoffSource passed a foreground scratch check with no
diagnostics; its targeted leaf build is running. Full current extraction is not
yet claimed.

The loss estimate was sharpened in proof strategy: h>v implies 1/h<=1/v, hence
its norm is at most norm(S_z(v))*exp(-v)/v. Arbitrary source flatness absorbs
this bound. No separate logarithmic estimate is necessary. The next scratch
retains this loss, the near response, the removed moments and the finite far
resolvent remainder in one exact original-current identity.

Both iteration30 deep/method records are saved in
[pw-b-gamma-reciprocal-cutoff-searches.json](pw-b-gamma-reciprocal-cutoff-searches.json).
All twenty candidates and twenty source arguments from each were inspected.
The first has partial coverage731004; the second has partial coverage731102
and local reranking deadline/disconnection errors. The attempted --mode method
flag is unsupported; mechanism retrieval was run through the documented deep
mode. The Frullani set-splitting proof and the original half-line translation
proof in EulerHedenmalmMobiusStokesInverse provide applicable mechanisms. The
suggested half-plane decay ingredient plan does not supply this cutoff estimate.

Broad recent arXiv searches used gelation and bifurcation. Primary reading:
[Jencks–Kaper–Vo, 2609.08969v1](https://arxiv.org/html/2609.08969v1), sections1,
4.3 and4.4. Their singular reaction-diffusion proof retains separate rescaling
and entry/exit charts and an explicit transition map. Persistence then needs
transversality of center-manifold intersections. Transfer here is methodological:
retain both cutoff regions and their exact coordinate conversion. Their fold,
small-parameter and transversality hypotheses supply no PW source adjoint,
Xi occurrence or Ward balance. No result from that paper is imported as a premise.

The source leaf's targeted build completed successfully in43s. The first
finite-expansion scratch pass exposed five formalization errors (measurability
of the totalized quotient, an unnecessary closed-goal tactic, an inferred
IntegrableOn type, exponential cast placement and a triangle-inequality
association). These have been corrected in scratch. The original checker handle
then disappeared without a terminal exit report; process inspection confirmed
it was no longer live. No success was inferred from its empty log. The same
corrected scratch is being checked again, now retaining an explicit exit file.

The third deep/method query has partial coverage731153; semantic retrieval
reported a local Qdrant timeout. All twenty candidate and twenty source-argument
statements were inspected and the record was added to the cutoff search JSON.
Actual corpus source in PowerExpansionAlongRay and AsymptoticExpansionAlgebra
uses finite Poincare remainders and coefficient peeling, without a convergent
series premise. The least-nonzero-moment mechanism in HierarchicalResonanceBreaking
supplies a sharper survivor: existence of a finite first nonzero moment and
an exact normalized current limit. The corresponding current-valuation scratch
is drafted but cannot run until the expansion leaf is verified and built.

Finite expansion checkpoint: the final explicit-exit scratch passed without
diagnostics, and GammaReciprocalCutoffExpansion passed its targeted build in76s.
Ten public theorems retain all four original cutoff errors and prove
norm(exp(-v)C_z(v)-sum_(j<q)v^j B_j)<=C_z,q*v^q on0<v<=1/2.
The current-valuation and corrected-scalar contradiction scratch is now running.

A further broad recent arXiv search used resurgence. Primary reading of
[de Mello Koch–Raj–Rudra, 2609.04664v1](https://arxiv.org/html/2609.04664v1)
covered the introduction, section5 and the full-versus-reduced incidence part
of section6.4. Their Borel–Leroy angular representation retains the radial
Gamma normalization. Reduced kernel trajectories need not represent distinct
full trajectories; the full matrix variables and physical contour determine
incidence. The paper uses numerical integration for that incidence example,
which is not an unconditional Lean premise here. Transfer is limited to
retaining original variables, normalization and physical occurrence separately.
No resummation or saddle claim proves PW Xi occurrence or Ward balance.

Iteration30 final proof checkpoint: all31 public theorems in the three new leaves
passed foreground scratch checks and targeted leaf builds (source43s,
expansion76s, valuation6.3s). Exact scratch/promoted source equality and one
umbrella import per leaf were verified. The index refreshed all three leaves.
The final formal lint run failed on the unrelated unwired working-tree module
ThetaCuspHawkingBMRetardedPulseClock; no PW-B wiring error was reported.
No full/umbrella build or axiom-print check was run.

The original current now has a finite first nonzero endpoint coefficient at
every complex parameter, with its exact nonzero rescaled limit. This excludes
the precise unit-ground-corrected Gamma scalar equation everywhere. The
[narrow failed-route card](../5-failed/pw-b-corrected-gamma-scalar-occurrence.md)
records both the obstruction and this strongest positive survivor. PW-B stays
live; the next attack is complete original-cutoff transposition and its common
signed source domain, followed by a different justified Xi occurrence and an
independently forced fixed-grade Ward law. No RH proof is claimed.

### Iteration31: complete adjoint cutoff passage

Conjecture: the actual finite-cutoff transposition has the retained logarithmic
contact on the complete signed arithmetic pairing, including the moving endpoint
layer and the region with empty incoming interval. The pointwise cutoff limit
and single-mode contact are already proved; neither permits dropping those
regions. A new whole-corpus deep/method query targets transposition, reciprocal
Jacobian and moving-boundary estimates. This attack must establish an actual
paired identity, not merely all-parameter square-integrability.

Iteration31 mechanism pivot: translate x=u+delta in the whole contact region,
retaining its entire moving layer on the fixed positive u ray. The complete
signed two-parameter density has the paper bound C*x*exp(-x), deduced from
reciprocal polynomial source bounds and exponential factorial inequalities.
It gives the integrable majorant C*exp(-u)*(2|log u|+3u^2+2u+3), and an
O(delta) bound for the separate empty incoming loss. The full paired contact
limit is now under Lean scratch verification; finite-cutoff gain transposition
and the remaining difference term are not yet proved.

Both new deep/method queries have no reported execution errors, with partial
coverage731355 and731449 and incomplete semantic/source-refresh coverage.
Records are saved in [full adjoint searches](pw-b-gamma-full-adjoint-searches.json).
The first generated ingredient plan incorrectly proposed matrix transpose
and an elliptic-curve variable-change invariant for the jump integral; neither
supplies this proof. Actual reciprocal substitution source was inspected in
BVPrimeWindowReciprocalReflection. The applicable logarithmic majorant proof
comes from the corpus LogExpTailIntegral, and actual additive Haar translation
transports the original contact integral. The second generated logarithmic
squared-tail plan has a different weight and is not a substitute for the
moving-layer estimate.

Broad recent arXiv search used fragmentation and scattering. Search-engine
results were old and the fragmentation listing timed out; the scattering
latest listing produced [Belishev–Vakulenko,2609.03536v1](https://arxiv.org/html/2609.03536v1).
Primary reading covered the control/connecting operators and AppendixLemma1.
Their identity C=W*W=I+R connects positivity to an actual input-to-state map;
unreachable states require a density argument using supported delayed waves.
Real bounded compactly supported potential and absence of zero bound or
semibound states are explicit premises. Transfer is methodological: original
source occurrence and boundary-free transposition need their own proofs.
Neither this scattering model nor abstract positive connecting operators
supplies a PW Xi occurrence or the missing Ward balance.

Iteration31 final checkpoint: all14 public declarations in
GammaAdjointPairedContact passed the final foreground scratch without
diagnostics. Its targeted leaf build passed in26s. Exact scratch/promoted
source equality, one umbrella import and all14 indexed public names were
verified. All local links in the four new proof cards resolve; scoped
whitespace checks passed. Final index and repository formal lint passed.
The earlier unrelated HB wiring error is resolved in the current working
tree; no other task's source was modified. All owned Lean and research
processes are terminal. No axiom-print check or full/umbrella build was run.

The [paired-contact proof](../3-formalized/pw-b-gamma-adjoint-paired-contact.md)
closes both complete signed moving-layer passage and the empty incoming
constant loss. It is not a full adjoint theorem. The next exact quantities
are the changing-source mismatch E_delta and omitted initial backward
response, followed by original finite-cutoff gain transposition. Their
complete response majorant is already available in GammaReciprocalCutoffSource.
The third deep/method query retained in the full-adjoint JSON has partial
coverage731543 and no execution errors; its proposed bounded-cutoff
ingredient plan does not establish the moving-response limit. Actual
mathlib integrable primitive continuity and dominated convergence are the
applicable source mechanisms.

A subsequent Xi-occurrence audit must also respect the actual corpus
GammaMobiusMellinBridge: the original Mellin integral is
Gamma(s+1/2)/zeta(z+s) only on its proved overlap Re(s)>-1/2 and
Re(z+s)>1. The full sum of atom norm integrals has exactly the latter
admission threshold. This gives an original source/transform identity,
not a residue in the proposed operator domain or a scalar Gamma mode.
Any continuation or different occurrence realization needs its own proof.
Full common-domain adjoints, actual Xi occurrence and independent fixed-grade
Ward balance remain open. PW-B and the overall RH goal remain active.

### Iteration32: complete paired response passage

Conjecture: the original paired backward response is jointly absolutely
integrable on both positive rays. Its complete signed kernel is
J_zv(x,h)=w(x)g_v(x) conjugate(H_z(1/x,h)). The proposed bound is
C*x*exp(-x)*exp(-h)*(1+h)^r. The existing complete response bound and
inverse polynomial source bound reduce this to exponential factorial
inequalities. If proved, dominated convergence on the product space retains
both the moving mismatch interval and the omitted initial response region.
Original iterated integrals still require Fubini identities and admission;
this is not yet a full gain transposition or operator domain theorem.

Deep/method search returned partial coverage731591, with complete file
inventory but incomplete compiler/semantic coverage. Its generated
cancellation-plus-moving-parts plan requires separate admission of both
parts; the existing full response estimate instead supports one joint
absolute majorant. No generated proposal is treated as a verified lemma.

Broad recent arXiv search used dilation and dispersal. Primary reading of
[Bickel–Pascoe–Tully-Doyle,2607.14372v1](https://arxiv.org/html/2607.14372v1)
covered the Nelson construction and its minimality proof. A strict finite
matrix contraction is compressed from multiplication by a matrix inner
function, with equality for every power and density supplied by its defect
vectors. The transfer requirement is exact source compression and minimality;
an available positive dilation alone selects no PW source or Xi occurrence.
The minimum-dilation-tree result2609.08990 was inspected only at abstract
level; its approximation algorithm supplies no exact source identity here.

Iteration32 proof pivot is now explicit: use two product-space indicators,
x>delta with h>a_delta(x), and x>delta with h>delta. Both are dominated
by the complete jointly integrable response and converge to that response.
Exact Fubini and difference-of-tail identities recover the original oriented
mismatch. This avoids an unproved uniform bound on a changing primitive.
The final scratch is checking all original source formulas and admissions.
The second deep/method query returned partial coverage731623, no execution
errors and no generated proof ideas. Its compact smooth interval majorants
and probability-product transport results have different premises; neither
replaces the original signed kernel estimate.

The next gain-transposition attack can use the actual coordinate identity
M_z'=(1/(2x))*M_z-M_(z-1). Dividing by the literal Q should give
(g_z)'=g_z-g_(z-1), so complete source polynomial bounds and the convex
mean-value estimate can admit the forward difference jointly without an
atomwise sign assumption. This normalized derivative and its paired estimate
are not yet Lean theorems. Actual corpus reciprocal substitution uses
intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos on compact positive
intervals; moving to the full jump triangle still requires the exact endpoint
limits and absolute admission. Pointwise detailed balance alone does not
complete this step.


Iteration32 final checkpoint: all nineteen public theorems in
GammaAdjointPairedResponse passed the final foreground scratch without
diagnostics. Its targeted leaf build passed in125s; only this leaf was newly
built. Exact scratch/promoted source equality, one umbrella import, all
nineteen public API entries and the new proof-card links were verified.
Final index and repository formal lint passed. All owned Lean and research
processes are terminal. No axiom-print check, numerical experiment or
full/umbrella build was run.

The [complete paired-response proof](../3-formalized/pw-b-gamma-adjoint-paired-response.md)
closes joint absolute admission, original moving mismatch and simultaneous
native cutoff passage. This is verified progress beyond the previous contact
limit, not a full adjoint theorem. The remaining chain is original finite-cutoff
gain transposition, full common physical signed domain and source-forced
pairing, a different justified Xi occurrence, independent fixed-grade Ward
balance, and RH. The next exact attack is the normalized derivative and paired
forward response bound, followed by the retained triangular reciprocal integral
identity. The scalar Gamma ansatz excluded by the current valuation remains
excluded. PW-B and the RH goal remain active; RH is not proved.

The third deep/method query, retained in the response search JSON, has partial
coverage731749 and no execution errors. Its triangle substitution candidate
is a natural-number parameter encoding, not a change of integration variables.
The useful reciprocal-integral candidate still needs its precise hypotheses
checked for this jump triangle; no transfer theorem is assumed.

### Iteration33: original forward response and triangular transpose

The previous turn is verified progress: the complete paired response leaf,
original-source mismatch and native cutoff limits passed scratch, targeted
leaf build and formal lint. The finite-cutoff gain identity remains open.
The new conjecture uses the actual coordinate source equation to prove
(g_z)'=g_z-g_(z-1). Complete inverse-polynomial bounds should then control
forward increments on every x>0,h>0 by h times a fixed inverse-polynomial
in x. This supplies the original forward paired response admission needed
before transposing the full source on the translated jump triangle.
The investigation starts from the corpus derivative and complete source
bounds, with a new deep/method query; no atom sign or Xi-mode assumption
is introduced. Full physical domain, justified Xi occurrence and independent
Ward balance remain distinct RH obstacles.

Iteration33 pivot: the installed additive shear (x,y)->(x,y-x) preserves
Lebesgue product measure. Composing the original absolutely admitted cutoff
gain with this exact shear retains its whole triangular support; Fubini then
produces the recipient interval0<x<y-delta. A direct injective Jacobian theorem
maps that interval to the reciprocal ray h>a_delta(y). This avoids separately
estimating a transformed triangle by a surrogate source. The normalized
derivative, complete forward bound and source-level current pairing are
checking in the same scratch as these exact gain identities.

The first deep query finished with partial coverage731780 and interrupted
text retrieval/disconnected semantic-worker errors. Its returned source
coordinate derivative is usable; the unrelated exponential cascade and
projective regulator candidates do not provide the required estimate.
A second deep query targets the actual image, Jacobian and product shear.

Broad recent arXiv searches used transport and symmetrization. The general
search engine returned mostly old or unrelated results; the latest arXiv
transport listing supplied two September9 preprints. Primary reading of
[Bothe,2609.10393v1](https://arxiv.org/html/2609.10393v1) covered the explicit
balance-anchoring axiom and Sections11–13: nonnegative mechanism production
is a constitutive restriction after reversible exchanges cancel; matching
weights test a stated model package. No new physical axiom or entropy sign
is imported into PW-B. Primary reading of
[Hashemi–Hyun,2609.10367v1](https://arxiv.org/html/2609.10367v1) covered the
finite-free matrix defect proof: real-rooted input hyperbolicity supplies a
definite symmetric pencil, and mean/variance identities turn the Jacobian
loss into an off-diagonal squared norm. The real-rooted premise cannot
supply an unconditional Xi producer. Exact transport and source identities,
not an assumed positive representation, are the relevant methodological test.

Iteration33 gain checkpoint: all33 public declarations in
GammaAdjointGainTransposition passed the final foreground scratch without
diagnostics. Exact source was promoted and wired once; targeted leaf build
passed in46s. The complete reciprocal and triangular gain identities now
have every original inner section and both outer integrals admitted. The
forward cutoff converges to the actual coefficient-current pairing.
The full paired adjoint is now under Lean verification through the exact
identity F_delta=R_delta+E_delta+(C_delta-L_delta). This retains the separate
empty incoming constant loss and applies the previous response/contact
limits only after the finite-cutoff algebra has been established.

The second and third deep/method queries have partial coverage731829 and
731881 and no reported execution errors. The second returned positivity
and unrelated injectivity lemmas rather than the actual change of variables;
the installed additive shear and one-dimensional Jacobian source supplied
that proof. The third's proposed cutoff-subtraction transfer only preserves
an already stated literal piece; it does not prove the paired adjoint.
Actual admitted tail subtraction and retained source-interval splitting
provide the finite identity being checked.

Iteration33 full-current checkpoint: the final scratch for all four
GammaFullPairedAdjoint public theorems exited0 without diagnostics. The exact
source has been promoted and wired once; its targeted leaf audit is running.
The finite-cutoff identity, full-source adjoint formula and absolute admission
of all three original-current pairings are proved in that checked source.

The fourth deep/method query finished with partial coverage731960 and no
execution errors. The actual DeningerSkewAdjointGraphCore source gives
numerical-range and off-axis lower bounds only after skew symmetry on a
specified inner-product domain. The generated exponential-density ingredient
set does not establish density, closure or physical incidence. The raw result
is retained with the three preceding queries. This leaves common-domain
construction and original Xi incidence as mathematical obligations; it does
not promote an abstract operator premise to a source theorem.

Iteration33 final audit: both exact checked leaves are promoted and wired once.
The gain leaf has33 public theorems and passed its46-second targeted build;
the full paired-adjoint leaf has four public theorems and passed its124-second
targeted build. All37 names are indexed. Final formal lint passed, with only
existing repository size warnings. No full/umbrella build, numerical experiment
or axiom-print check was used. The complete source formula retains2log(x),
and all three displayed original-current integrals are absolutely admitted.
RH is not proved: physical domain/closure, different justified Xi occurrence,
and independently forced fixed-grade balance remain open.

### Iteration34: Mellin reader and the paired source norm

The source adjoint is now checked and audited. The next incidence conjecture
asks whether its weighted norm controls the literal Mellin reader at any
complex argument. The original source and density give the exact candidate
dual weight D_a(x)=x^(2a)*exp(-x+1/x), a=Re(s). Paper comparison with
exp(-1)/n!*x^(2a-n), n>2a+1, defeats global dual admission for every a.
The positive survivor includes compact-away-from-zero dual admission and
weighted square admission of every complete arithmetic source, obtainable
from the proved self-pairing. Scratch verification is running; no new result
is promoted yet. The [dual-domain proof](../3-formalized/pw-b-gamma-mellin-dual-domain.md)
records the exact scope, including the additional work needed for an actual
unbounded-reader theorem.

Two new deep/method queries returned partial coverage732050 and732074 with
no execution errors. Their [raw records](pw-b-gamma-mellin-dual-searches.json)
retain all candidates and method premises. A proposed residue transfer mixes
dual-number algebra with a separate contour source and supplies no PW
incidence. Mellin inversion still needs original admission and vertical
integrability; Sonin versions additionally require band and decay hypotheses.
None supplies the missing global weighted reader. The direct source formula,
exponential factorial bound and local power-integrability criterion are the
proof ingredients being tested.

Broad recent intertwining reading inspected
[Elber–Lheem,2608.01485](https://arxiv.org/html/2608.01485v1): multiplicity-free
finite-group induction uses explicit character restrictions and a compatible
anti-involution or a separate reduction. Its exact intertwiner acts on a
specified induced representation. No such representation or character
identification has been derived for the PW source. The
[Jiang–Wang–Wu abstract,2606.04383](https://arxiv.org/abs/2606.04383) concerns
GNS/KMS-symmetric quantum Markov semigroups; its HTML body was unavailable,
so no detailed proof transfer is asserted. These readings do not replace
the original-source domain check.

Iteration34 scratch closure: all seven public theorems passed without
diagnostics. The exact source has been promoted and wired once; the targeted
leaf audit is running. Lean proves the literal squared Mellin dual-weight
identity, nonintegrability near zero for every complex argument, compact
admission away from zero, and weighted squared-norm admission of every
complete arithmetic source. The narrow failed global-dual estimate preserves
these positive survivors. No theorem about arbitrary continuous Mellin
extensions is claimed; endpoint control and actual Xi incidence remain open.

Iteration34 final audit: exact checked GammaMellinDualDomain source and its
unique umbrella import are verified. All seven public names are indexed.
The targeted leaf build passed in57s and final formal lint passed with only
existing size warnings. All owned Lean, index and research processes have
finished. No full/umbrella build, numerical experiment or axiom-print check
was used. The complete paired-current identity remains intact. The next
incidence attack must retain explicit endpoint control or construct a
justified stronger/weak reader domain; abstract weighted source admission
cannot supply the missing Mellin estimate. Physical operator closure,
actual Xi occurrence and independent fixed-grade balance remain unproved.

### Iteration35: retain the fixed-argument mixed source current

Revalidated iteration34 source and passing build/lint evidence. Its dual-norm
obstruction changes the next action: use the original coefficient and spatial
logarithms together. At fixed u=z+s the source derivative is M'_z-log(x)M_z.
Its full atom contains -log(n*x), so scaling t=n*x retains a single logarithmic
Gamma kernel with the original arithmetic norm weight n^(-u). This is the
new [fixed-Mellin current proof](../3-formalized/pw-b-gamma-fixed-mellin-current.md), before
any continuation or Xi specialization. A deep/method search and direct corpus
Gamma/Mellin derivative audit are running; no new current identity is claimed
yet. Physical domain/closure, Xi incidence and independent Ward balance remain
unproved.

Iteration35 first checkpoint: the logarithmic Gamma-source admission and its
literal Mellin integral, plus the exact full mixed-current weighted-source
identity, passed scratch without diagnostics. The final assembly now applies
the actual ChronologicalWeightedMellin theorem, whose admitted source theorem
retains the complete norm-integral sum. Its general weight is
W_z(t)=t^(-z)*[-log(t)*Q(t)], and the existing cpow-Mellin transport changes
its argument from z+s to s. The resulting full mixed-current admission,
Gamma derivative value, pointwise fixed-argument derivative and zero integral
of the explicitly Gamma-normalized current are under verification.

Deep/method search had partial coverage732156 and no execution errors. Its
Mellin derivative candidate is applicable only with its endpoint bounds; the
proposed abstract transport symmetries do not supply those. Hybrid logarithmic
Gamma search returned useful actual GammaIntegral derivatives, with partial
coverage and a local-Qdrant timeout. No service was launched. Both raw results
are in [the search record](pw-b-gamma-fixed-mellin-searches.json). The installed
general weighted Möbius source provides the direct full-series passage.

Broad recent deformation and transmutation searches included primary reading
of [Adarsha–Chakraborty–Bhattacharyya,2608.10594v1](https://arxiv.org/html/2608.10594v1),
SectionV: its signed accretion/evaporation rate defines a stagnation threshold,
but the stated closed-form timescale uses a specified rate regime; it does
not enforce stagnation. No rate balance is imported as a Ward law. Primary
reading of [Xu,2609.10454v1](https://arxiv.org/html/2609.10454v1), Theorem2.10
and its proof, uses a chosen compactification and prior metric results. It
supplies no original Mellin endpoint or physical source comparison here.

Iteration35 final scratch: all six public theorems passed without diagnostics.
The exact source was promoted and wired once; targeted leaf audit is running.
The theorem identifies the actual fixed-argument derivative, admits the full
mixed current, evaluates its Mellin integral as -Gamma'(s+1/2)/zeta(z+s), and
proves the explicit Gamma-normalized current has zero integral in the same
open convergence region. It adds no critical-strip continuation or physical
Ward premise. The missing source endpoint/reader comparison and actual Xi
incidence are now separate from this proved parameter-transport identity.

Iteration35 final audit: the six public declarations in
GammaFixedMellinCurrent passed final scratch without diagnostics and the
28-second targeted leaf build. Exact scratch/promoted-source equality and
one umbrella import are verified. All six public names are indexed; final
formal lint passed with only existing repository size warnings. Proof-card
links and scoped whitespace checks passed. All owned Lean/index/research/lint
processes have finished. No full/umbrella build, numerical experiment or
axiom-print check was used. RH remains unproved. The next current-source
attack must retain endpoint flux while testing continuation and physical
Xi incidence, rather than treating the normalized zero integral as the
independent fixed-grade Ward producer.
