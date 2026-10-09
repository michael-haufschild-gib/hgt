# Fixed-probe positivity forces uniform expanding-panel positivity

Status: [PAPER PROVED; LEAN VERIFIED]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Claim and plan

Under nonnegative coefficients and summable normalized excess, exchange the
order of the probe and cutoff quantifiers in asymptotic log-shift positivity.
Each fixed integer-log probe may have its own cutoff, yet the entire expanding
panel acquires a common cutoff. If uniform positivity fails, one fixed probe
stays below a fixed negative margin in every sufficiently late window.

1. Extract potential convergence from local summability alone, removing the
   existing asymptotic-positivity premise from the fixed-probe limit argument.
2. Prove the quantifier-exchange criterion under finite excess and convergent
   origin/sample potentials; discharge convergence for nonnegative coefficients.
3. Prove the persistent fixed negative witness when uniform positivity fails.
4. Compile affected leaves at default heartbeats; audit changed/new public results.
5. Wire/index, authoritative lint, promote this card, clean owned scratch.

## Dependency-closed paper proof

Write P_y(n)=K(y+log n)+K(y-log n), a=normalized deviation, and psi(y)=sum aP_y.
The truncated kernels are nonnegative, bounded above by K, and tend to K.
If sum aP_y converges, its term norms form a summable majorant for every
truncated potential term: |a(n) P_{L,y}(n)| <= |a(n) P_y(n)|. Dominated
convergence therefore gives psi_L(y)->psi(y), without a coefficient-growth
or test-positivity premise.

The existing fixed-probe identity uses only summability of the two truncated
potentials at 0 and log m. Extract that exact premise from its proof. The
zero-side term tends to zero independently of lam. Consequently convergence
of the two untruncated potentials gives the exact probe limit

`f(k,m) -> d(m)=2(psi(log m)-psi(0))`.

For a convergent real sequence f(k,m), the condition
`forall eps>0, exists N, forall k>=N, -eps<=f(k,m)` is equivalent to d(m)>=0.
Forward: pass each eventual lower bound to the limit and let eps decrease to
zero. Reverse: convergence eventually places f(k,m) above d(m)-eps>=-eps.

Thus pointwise approximate positivity for all m>=2 is exactly the sampled
potential inequalities. With summable excess and sample convergence, the
existing sampled-potential characterization recovers uniform expanding-panel
positivity. For nonnegative lam, the previous increment supplies convergence
at all real shifts before any positivity is imposed.

If uniform positivity fails on that domain, the potential characterization
gives a fixed m>=2 with d(m)<0. Set eta=-d(m)/2>0. Convergence gives
f(k,m)<=-eta for every sufficiently large k; increasing the cutoff also places
the fixed m inside each expanding panel.

## Corpus audit and boundaries

Inspected `WeilLogShiftExcessControl.lean`: current fixed-probe limit assumes
asymptotic positivity only to obtain potential summability and its dominated
convergence bound. Its private exact identity also assumes more than it uses.
`WeilLogShiftSampledPotentialCone.lean` supplies the sampled characterization;
`WeilLogShiftNonnegativePotential.lean` supplies unconditional convergence on
the nonnegative, finite-excess coefficient domain.

Initial local search found the existing whole-panel criterion, sparse
convergence theorem, and persistent-gap theorem under absolute summability.
The targeted local lexical search `pointwise logShift uniform` found zero hits.
The broader OR search returned 224 declarations across 42 modules and located
the ingredients above. No matching quantifier-exchange theorem appeared in
those returned declarations. No claim of exhaustive semantic coverage is made.

No claim that convergence or finite excess can be omitted on arbitrary signed
coefficients. No external novelty claim, RH claim, new axiom, numerical
experiment, or heartbeat increase. No mixed-sign rigidity claim.

## Exact new insight

The origin and single-probe potential series are sufficient for the fixed-probe
limit. Extracting this local summability argument removes the previous
positivity premise and avoids circularity when deriving positivity from limits.

With finite excess, sampled convergence plus pointwise approximate positivity
then recovers the common expanding-panel cutoff through the corpus's potential
criterion. Nonnegative coefficients discharge the convergence premises. Thus
a failure on that domain cannot occur only at probes escaping to infinity:
one fixed integer-log probe has a fixed negative margin in all late panels.

## Lean artifacts and validation

Updated `formal/GaloisForLFunctions/RHTower/WeilLogShiftExcessControl.lean`:

- `tendsto_truncatedPotential_of_summable_potential` is new.
- `tendsto_logShift_probe_of_summable_potential` is new.
- The two existing positivity-based limit theorems retain their signatures and
  delegate to the stronger results. The private identity now takes exactly the
  two truncated summability facts used in its proof.

New `formal/GaloisForLFunctions/RHTower/WeilLogShiftPointwiseCriterion.lean`:

- `weilLogShiftAsymptoticPositive_iff_pointwise_of_summable_potential`
- `weilLogShiftAsymptoticPositive_iff_pointwise_of_nonneg_coefficients`
- `exists_persistent_fixed_logShift_negative_of_not_asymptoticPositive`

Both final leaves passed `lake --old env lean <leaf> -o <local olean>` at default
heartbeats with no diagnostics. All seven new/changed public theorem axiom
audits passed with exactly `[propext, Classical.choice, Quot.sound]`. Public
signatures were checked from the exported module. The initial witness proof
needed explicit normalization of a composed natural-number cast before
`linarith`; the paper argument and statement were unchanged.

The new module is wired into `RHTower.lean`. Index refresh passed; all seven
new/changed API rows were verified. Authoritative lint exited 1 with five
unrelated unreachable HTGeometry modules: `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
and `BoundaryCoronaCStarAlgebra`. Neither affected leaf has a reported lint error.

All owned jobs exited. Scoped whitespace checks passed. All ten owned scratch
files were removed and their absence verified. Both exported artifacts are
present and newer than their final source files.

## Remaining frontier

This exchanges approximate positivity quantifiers, not exact nonnegativity
with epsilon zero. It does not remove finite excess or arbitrary signed-tail
convergence. General mixed-sign rigidity remains open.
