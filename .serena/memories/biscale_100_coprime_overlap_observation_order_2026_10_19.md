# BiScale 100 programme: coprime overlap, 2026-10-19

Accepted count **3/100**, active unbudgeted goal100, 97 remaining. Do not mark complete. Canonical tracker: `docs/drafts/pipeline/1-in-progress/biscale-100-contribution-programme-2026-10-18.md`. New stage-3 card: `docs/drafts/pipeline/3-formalized/biscale-prime-overlap-observation-order-2026-10-19.md`; stage-1 card moved, not duplicated. Prior package links updated. Read alongside `mem:biscale_100_arithmetic_translation_anchoring_2026_10_19`.

## Exact result
For pairwise coprime odd integers p,q,r>1, cutoff max(2pq,2pr,2qr)+n, actual Ramanujan inverse weights with arbitrary real coordinates a on the three orders, all labelled affine quadratic data plus translated degrees <=m recover the actual signal modulo integer translation against **arbitrary competing real sieve weights** iff:
`AtMostOne a ∨ (Full a ∧ 4 ≤ m) ∨ 6 ≤ m`.
Thus full support requires exactly 4, exactly two modes require exactly 6, support <=1 requires no extra translated degree. All zeros included. Common sign equals actual translation by pqr. No support premise on competitors: affine data force their signal into this family.

Quartic Fourier readout is P^4*a*b*c^2; permutations compare all signs when abc nonzero. Any zero-sum quartet on two incomparable orders has even multiplicities, so independent flips preserve full fourth arrays. Odd moments vanish by actual antiperiod; existing sixth valuation recovery gives sharp upper bound. Single-coordinate flips give actual nontranslation lower witnesses.

Count one substantive native support-dependent degree jump. Fourier inversion, CRT, inverse realization and sign algebra are not separate contributions. Broader literature priority is not claimed.

## Files and verification
New leaves under formal/GaloisForLFunctions/BiScaleUncertainty:
- CoprimeOverlapQuarticReadout.lean
- IncomparableSieveQuartic.lean
- CoprimeOverlapSieveFamily.lean
- CoprimeOverlapObservationOrder.lean

Capstone namespace `GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CoprimeOverlap.Triangle`, theorem `sharp_observation_order`. Four named-source/export checks via `lake --old env lean -o ... <named source>` passed without diagnostics. Final capstone process 39573 exit0. Final imported audit process 97794 exit0.
All **60 explicit public declarations** #checked and #print axioms inspected; closures subset of propext, Classical.choice, Quot.sound. Printed Triangle and observation definitions confirm only arithmetic domain assumptions.
Audit source `/tmp/bsu_100_overlap_final_audit.lean`; log `/tmp/bsu-100-overlap-final-audit.log`.
Source logs: `/tmp/bsu-100-overlap-readout-leaf.log`, `/tmp/bsu-100-incomparable-leaf.log`, `/tmp/bsu-100-overlap-family-leaf.log`, `/tmp/bsu-100-overlap-order-leaf.log`.
All leaves wired exactly once. Index passed (88035), lint --check-generated passed (67424), 381 existing large-file warnings only. Logs `/tmp/bsu-100-overlap-index.log`, `/tmp/bsu-100-overlap-lint.log`.
Whitespace clean. README unchanged SHA256 95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275.
Extracted temporary drafts removed; final audit/logs/search evidence retained. No owned running jobs.

## Search and priority boundaries
User explicitly steered: use Lean corpus search; do not miss existing work. Continue running `scripts/formal_tools.py research` directly before any new topic/code; not just rg. Do not inspect search help/source as preparation.
All inventories inspected for deep CRT, realization, native quartic prior, moment injectivity, quadratic affine bridge, incomparable-orders queries. See card for exact JSON files. Two requests partial, semantic completeness unmeasured, background refresh incomplete. Own new sources appeared in latest query and excluded from prior evidence. Lexical quartic/bridge query fully paginated: all 48 unique hits.
Reused existing moment Fourier identity, prime-family through-five obstruction, sixth valuation recovery, affine comparable-product theorem, RHTower Ramanujan inverse and BVI actual-coefficient injectivity.
Primary comparisons: Jaming–Kolountzakis 2003 §3.4, Grünbaum–Moore publisher abstract (full text inaccessible), full Putinar 2005 pp11–18. Classical 4/6 deck and invariant-ring mechanisms excluded from novelty credit. This bounded comparison is not exhaustive absence evidence.
Existing mixed-stability-strata-1810 card concerns changing valuation ambiguity/stability; inspected, distinct, untouched.

## Continuation constraints
No hgtl7, subagents, numerical experiments, heartbeat increases, full/umbrella builds, commits/pushes or README edits. Preserve concurrent APT/BVI/THIM work. One owned foreground Lean at a time. #print axioms in /tmp only. Use guarded finite-time Python scratch jobs. update_plan unavailable; programme card tracks work.
No next conjecture started. Possible future question: exact quartic phase constraints for edge-supported coprime-block graphs (triangles and four-cycles); MUST search prior work and create card before research/formalization. Do not treat as proved/new/counted.

## Lean interface lessons
sieveSeq lives in BVI; open BVI when using it. TrueTranslationPredictionAndExactCompression direct import provides sieve_active_coefficients_eq_iff.
Fin literal eta after fin_cases can require explicit change before rewriting zero assumptions.
For readout coordinate rewrites, rw exact coordinate lemmas before normalizing Nat multiplication association.
Empty-Fin Fourier inversion sum: avoid Unique/default definitional mismatch; use explicit Finset.sum_eq_single with Subsingleton.elim.
Equiv.addRight translation-index target is (x+t)+h, not h+(x+t); change exact form then ring.
