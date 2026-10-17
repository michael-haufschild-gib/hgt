# CHMD: exact native Jordan radical classification

Status: the dependency-closed paper proof and both Lean modules are complete. Individual compilation and the full scoped axiom audit passed; the formal index was refreshed. Global lint failed on unrelated modules listed below. The user requested completion of this existing work followed by stopping, with no new route. This result receives no qualifying RH-route credit.

## Original research objective (unresolved)

Remove a hard source-level obstruction to excluding sign-changing odd CHMD bound states above the critical resolvent threshold. A new receiver, improved bound, abstract encoding, or another conditional sign statement does not count. That obstruction remains open. The completed positive result below classifies finite native packets in the actual arithmetic radical; it does not prove positivity or exclude these bound states.

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

## Deferred conjecture (not pursued)

The explicit normalized theta-shift differences may generate the entire odd threshold radical in the native source graph topology. This would identify the actual arithmetic radical quotient rather than introduce another sign receiver. No completeness claim is assumed or proved. The user's stopping instruction leaves this conjecture deferred.

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

## Completed formal result

- `CHMDNativeJordanSamples.lean` proves the exact entire chain transform, vanishing at other Xi roots and at lower layers, nonvanishing of every terminal sample without a simple-zero assumption, and the finite-packet equivalence between Xi-sample silence and zero terminal coefficients.
- `CHMDNativeJordanRadical.lean` identifies the literal real and imaginary BV graph Fourier readouts with the normalized native transform. Reflection/conjugation separates the two scalar components. Its main theorem, `nativeFinite_polarResidual_radical_iff_terminal_zero`, proves that both polar-corrected components belong to the full signed arithmetic radical exactly when every terminal coefficient vanishes.
- The same module proves all mixed pairings and energies of these polar-corrected lower-layer packets vanish. `nativeFinite_lower_source_energy` retains the original archimedean energy, every prime jump, mass term, and both polar contributions before projection.
- `PaperThetaCutTransform.lean` only exposes the already-proved `differentiable_bounded_thetaTransform` helper publicly. Both new modules are imported by `RHTower.lean`.
- The hardest positive step, terminal nonvanishing at arbitrary exact multiplicity, is proved in Lean. No infinite-packet completion, theta-shift density, positivity, simplicity of zeros, or RH conclusion is claimed. Corpus searches preceded implementation; external novelty was not audited under the current-corpus-only constraint.

## Verification

- Individual `lake --old env lean` compilation passed for the exposed-helper module and both new modules. Each new module produced its local `.olean`; no full or umbrella build was run.
- The `/tmp` axiom audit imported the completed radical module and checked all 29 new public declarations plus the exposed helper. Coverage matched all 30 declarations exactly. Every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py lint` ran and exited 1 on unrelated worktree failures: unreachable `PrimeBurnolLevySymbol`, `LevyFiniteJumpMeasure`, `LevyLaplaceExponent`, `LevyLaplaceKernel`, and `LevyLaplaceTruncation` modules, plus a `sorry` in `RuelleZetaNuclearZeroFree.lean:285` (`fredholmD_eq`). No failure named either new CHMD module or the exposed helper. These independent changes were preserved.
- `scripts/formal_tools.py index` exited 0, regenerating `LEAN_API.md`, `LEAN_GAPS.md`, `LEAN_OVERVIEW.md`, and refreshing the search index (15 changed files, 0 removed).
- Scoped whitespace checks passed. Owned API/axiom scratch files were removed after successful checks. No owned Lean process remains.

## Stop instruction

The user first cleared the all-routes goal, then explicitly requested finishing this already-started work and stopping. No new route is authorized. The original RH obstruction remains unresolved and no CHMD qualifying contribution is claimed.
