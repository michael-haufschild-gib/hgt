# CHMD: primitive nodal source contraction

Status: stopped when the user cleared the goal. Route selected for this goal turn: CHMD, previously unworked in this root goal. No qualifying CHMD result is claimed.

## Objective

Remove a hard source-level obstruction to excluding sign-changing odd CHMD bound states above the critical resolvent threshold. A new receiver, improved bound, abstract encoding, or another conditional sign statement does not count. Qualifying progress starts at 2/44 (PM, SZ); CHMD has no credit.

## Plan

1. Inspect current Lean source definitions, stationary/nodal decomposition, parity bound-state obstruction, and the complete signed prime-shift form. Search the whole Lean corpus for existing source transformations and stronger results.
2. State and attack an exact transformation of the original source that preserves the primitive/parity requirements while changing the full signed energy. Reject sign-blind replacements or omitted prime/collar terms.
3. Complete any surviving paper proof before Lean. Formalize the exact positive survivor, verify all new declarations and axioms, wire finished modules, and run scoped final checks plus formal lint.

## Constraints

Current Lean corpus only; no web, external novelty audit, numerical computations, extra axioms, unproved analytic premises, full builds, or heartbeat increases. One owned foreground Lean build at a time. Frontier map is read-only. Preserve unrelated worktree changes. Workflow/card metadata are not mathematical evidence.

## Initial question

Can an operation on the actual odd primitive source remove nodal sign changes without increasing the complete source energy? Stationary absolute-value contraction alone is insufficient: the exact signed prime-shift term and the primitive/parity constraints must be paid. The operation and its domain will be specified from current Lean definitions before making a mathematical conjecture.

## Evidence and progress

- The current frontier map describes sign-changing odd bound states above 1/2 as open. Its statement is navigation only; inspect and check the cited Lean source.
- Whole-corpus deep discovery launched for the primitive absolute-value/nodal contraction mechanism. No mathematical conclusion yet.
- First deep search completed without partial results or runtime errors, but compiler coverage is mostly pending/stale; source inspection remains authoritative. Most candidate lemmas were unrelated. Useful source arguments led to `CHMDReflectedPrimeSingularPart.lean`.
- Initial local-modulus/gauge idea is already excluded in the corpus: the entire negative reflected-prime measure is mutually singular with the positive jump measure; strictly positive scalar gauges plus absolutely continuous or diagonal corrections cannot remove even the first-prime component. The existing positive survivor is exact collar compensation and its strict positive crossing energy. Do not reprove this no-go or count it as new.
- Ordinary `absGraph` moves odd vectors into the even sector; the cost of `primGraph (absGraph p)` is already represented by exact ground-square/nodal identities and conditional Rayleigh inequalities in current source. They do not produce the missing sign.

## Next conjecture to audit

The explicit normalized theta-shift differences may generate the entire odd threshold radical in the native source graph topology. This would identify the actual arithmetic radical quotient rather than introduce another sign receiver. First inspect the current Riesz–resolvent dictionary and all existing closure/spectral-synthesis results; then state exact topology and generators. No completeness claim is assumed.

## No-go closure

Do not retire a failed contraction conjecture without identifying and auditing its strongest nontrivial positive survivor. Any stronger theorem exposed by formalization returns to the paper-proof audit.

## Revised exact target: native Jordan layers in the arithmetic radical

Further current-source audit found that reciprocal-weight theta translation admission and derivative-history equality are already proved. Whole Gaussian-regularized Meyer cohomology already has faithful full CHMD graph admission in `PaperThetaOriginalArithmeticRealization.lean`. Repeating either construction adds no new result.

The remaining concrete question is which original native Jordan layers the CHMD quotient retains. Write `a = xiSpectralPointSupport rho`, `m = xiSupportMultiplicity rho`, and let `f_j = nativeThetaDivisorJet rho j` for `0 <= j < m`. Let `M_w(f)` be `boundedThetaMomentCLM w f`.

### Dependency-closed paper proof

1. The existing literal spatial equations and actual endpoint traces give
   `(w-a) M_w(f_0) = -w XiC(w)/thetaSource.mass` and
   `(w-a) M_w(f_(j+1)) = (j+1) M_w(f_j)`.
   Apply `boundedThetaMoment_source_equation` with the actual bounded native profiles. No formal eigenvector replacement occurs.
2. Induction yields the exact entire identity
   `(w-a)^(j+1) M_w(f_j) = -j! w XiC(w)/thetaSource.mass`.
3. At every other Xi zero, cancellation gives zero. At `w=a`, the successor equation gives `M_a(f_j)=0` whenever `j+1<m`.
4. At the terminal layer `j=m-1`, factor the actual entire Xi locally as `(w-a)^m G(w)`, with `G(a) != 0`, using its proved exact divisor multiplicity. Away from `a`, cancel to obtain `M_w(f_(m-1)) = -(m-1)! w G(w)/thetaSource.mass`. Continuity gives the same identity at `a`, which is nonzero because `a != 0` and the theta mass is positive. This closes the positive half of the classification; merely showing lower layers vanish would be insufficient.
5. Thus every finite packet has exactly one nonzero Xi-sample coordinate per root, namely its terminal coefficient times the nonzero terminal sample. Distinct roots cannot cancel these coordinates. The joint Xi-sample kernel is exactly the sum of the lower Jordan layers.
6. The existing BV admission gives real and imaginary graph vectors for every native packet. The normalized native moment is its literal Fourier readout divided by theta mass. Xi conjugation/reflection gives vanishing samples for both scalar components. Removing their two polar coordinates places exactly the sample-silent packets in the actual `signedRadical`; their full signed energy and pairing vanish. This identifies the actual invisible Jordan layers, retaining every prime and polar term before projection.

### Attacks and scope

- This is a source classification, not an RH proof or a new positivity receiver. It must not receive qualifying RH credit merely for identifying an arithmetic quotient.
- The terminal nonvanishing uses exact multiplicity, not a simple-zero assumption. All chain slots and every finite root packet must be covered.
- Pole subtraction is explicit; uncorrected source energy need not vanish.
- The original theta-shift completeness conjecture remains unresolved. Multiple-zero lower layers expose why sample vanishing cannot silently be strengthened to full-order divisibility.
- Third corpus deep search completed with `partial=false`, no errors, and predominantly pending/stale compiler coverage. The checked definitions above, not search ranking, support the proof.

## Stop state

- User cleared the goal during implementation; research stopped.
- Draft `formal/GaloisForLFunctions/RHTower/CHMDNativeJordanSamples.lean` contains the proposed exact native-chain transform and finite-packet sample classification. It has not been compiled, audited, or wired. Treat every new theorem there as unverified.
- `PaperThetaCutTransform.lean` changes only the visibility of the existing `differentiable_bounded_thetaTransform` helper from private to public. Its narrow Lean compilation completed successfully.
- Initial `/tmp` API probe found universe-inference errors in unspecialized `have := @...` lines, not unknown names. The revised probe completed successfully before cancellation cleanup reached it (exit 0); no owned Lean process remains. This verifies API names only, not the draft. No CHMD radical-bridge module was created.
- No final lint, index regeneration, axiom audit, or RH contribution credit. Qualifying progress remains 2/44 (PM, SZ).
