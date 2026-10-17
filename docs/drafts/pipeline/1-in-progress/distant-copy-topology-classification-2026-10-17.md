# Distant-copy amplitudes, compactness and polar continuity

- **ID:** distant-copy-topology-classification-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; independent BiScaleUncertainty.
- **Status:** Dependency-closed paper proof complete; Lean certificate pending, uncounted.
- **Paper:** `docs/reports/BiScaleUncertainty/DistantCopyTopologyClassification.md`
- **Guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).
- **Plan:** Audit copy and polar-moment APIs; complete exact paper classification;
  formalize the norm and moment laws, convergence/compactness consequences and
  actual sharpness witnesses; run leaf/axiom/index/lint checks. `update_plan` is unavailable.

## Gates

- [x] Corpus audit: deep discovery completed in 64.92 seconds; source-only candidates.
  Direct reads verified the actual source moment multipliers and full-line cosh product.
- [x] Dependency-closed paper proof of exact norm, energy, compactness and polar laws,
  including actual smooth witnesses and positive replacement criteria.
- [ ] Formalize the scalar/correlation and energy bounds.
  `DistantCopyCorrelationTopology.lean` passes without diagnostics: the sharp
  global error is attained at the copy center, and uniform convergence is
  equivalent to mixing-coefficient decay. The amplitude-uniform energy leaf is checking.
- [ ] Formalize compactness equivalences, polar moment classification and both witnesses.
- [ ] Direct leaf checks, axiom audit, umbrella/API wiring, formal lint, ledger update.

## Candidate classification

Fix an actual compact C² positive-mass source f, with correlation radius D>0.
For T>D and arbitrary real a, let g=f-a f(.-T), H=h_f/h_f(0), and b=a/(1+a²).
The existing exact expansion and mass law give

    H_g(x)-H(x) = -b (H(x-T)+H(x+T)).

The two shifted correlation supports are disjoint. Since |H|<=1 and H(0)=1,
conjecture the exact global norm identity

    ||H_g-H||_infinity = |b|, and H_g(T)=-b.

For any T_n->infinity and arbitrary amplitudes a_n, local correlations eventually
agree exactly with H on each fixed bounded window. Existing separated-copy energy
and exponential-tail estimates should give E(g_n)->E(f), uniformly in amplitudes,
because |a|/(1+a²)<=1/2. The exact norm identity predicts global uniform correlation
convergence iff |a_n|/(1+a_n²)->0. The signed-grid compactness criterion should then
show compact closure of the sequence's correlations iff this same scalar condition.

## Sharpness and positive survivor to audit

Taking a_n=1 and a seed with correlation radius below log 2 should yield actual
smooth bounded-energy sources whose every fixed grid sample is eventually zero,
and whose energies converge, but whose correlations are not relatively compact.
The surviving positive statement is the exact amplitude criterion above: pointwise
grid vanishing and energy convergence cannot replace uniform signed trace decay.

For polar attenuation a=exp(-T/2), b->0, but the factor b cosh(T/2) does not tend
to zero. Investigate the exact normalized polar-moment law

    P(H_g) = (1-2b cosh(T/2)) P(H),
    P(H)=integral_(0,infinity) H(x) cosh(x/2) dx.

If established, this separates global correlation compactness from polar continuity:
for P(H) nonzero, the missing scalar control is b cosh(T/2)->0. Audit a concrete
smooth seed with P(H) nonzero and every analytic integral; do not assume them.
Full-grid exact blindness remains a distinct constraint and is not asserted here.

## Corpus evidence

Searches `/tmp/signed-grid-pointwise-frontier.txt` and
`/tmp/signed-grid-copy-frontier.txt` found the exact local copy laws and existing
pointwise energy infrastructure, not this classification. Relevant inspected inputs:
`autocorr_subtractCopy`, `normalized_autocorr_subtractCopy_local`,
`normalizedArchEnergy_subtractCopy_sub`, `abs_integral_shifted_autocorr_arch_le`,
and `normalizedArchEnergy_abs_sub_le_of_local`. Reuse them; do not count their
already-certified algebra or energy estimates anew. Search specifically for the
polar-moment identity before proving that portion.
