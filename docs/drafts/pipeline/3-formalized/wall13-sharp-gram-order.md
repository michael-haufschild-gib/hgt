# Wall 13: sharp Gram-determinant detection order

- **ID:** BSU-W13-SHARP-GRAM
- **Stage:** 3-formalized
- **Type:** THEOREM — dependency-closed paper proof and Lean proof complete
- **Scope:** BiScaleUncertainty; Wall 13 remains open.

## Exact theorem

Use the concrete smooth compact seed b from the [sharp closed-product package](wall13-minimal-cycle-order.md). Its correlation h is positive exactly on (-1,1) and vanishes outside that interval. For T>2 and a real amplitude a, put

    f_a(u) = b(u) - a*b(u-T).

For every natural n, some real sample configuration of size n distinguishes the Gram determinants of f_-a and f_a exactly when

    a != 0 and T < n.

The least detecting order for every nonzero amplitude is therefore floor(T)+1. Every smaller order agrees at every configuration. Zero amplitude never detects. At an integer gap T=m, size m still agrees and size m+1 detects.

The theorem also constructs actual smooth compact sources of equal positive correlation mass with normalized polar moments zero and strictly positive, respectively, whose Gram determinants have this exact detection threshold. The sources are the literal pair at amplitude exp(-T/2).

## Proof

Let q=floor(T)+1 and s=T/q. Then q>=3, 0<s<1 and 2s>1. At the samples 0,s,...,(q-1)s, the correlation matrix has diagonal R=(1+a^2)h(0), nearest-neighbor entries c=(1+a^2)h(s), closing-edge entry z=-a*h(s), and every other off-diagonal entry zero. These are actual correlation values: the support bounds eliminate all other seed packets.

Start from the tridiagonal path matrix and add the closing edge to the two endpoint rows. Row multilinearity gives det(A(z))=det(A)+z(B+C)+z^2 D. Symmetry gives B=C. The endpoint cofactor is (-1)^(q-1)c^(q-1): deleting the first row and final column leaves an upper-triangular minor with diagonal c. Subtraction cancels the constant and quadratic terms, giving the exact identity

    det Gram(f_-a) - det Gram(f_a)
      = 4*a*h(s)*(-1)^(q-1)*((1+a^2)*h(s))^(q-1).

Every factor except a is nonzero. This proves detection at q without a rank hypothesis or an assumed realization.

For n<=T, each determinant permutation summand is a closed correlation product of length n. The already verified strict packet-charge bound forces equality of those products, hence equality of the determinants at every configuration.

For every larger size, prepend the explicit point sum_i |t_i|+T+2 to any detecting configuration. Its cross-correlations with the old points vanish. Expansion in that row multiplies each determinant by the same positive mass R, preserving detection. Induction covers every n>=q. Equal sources settle a=0. The previously verified polar formulas supply the concrete polar-neutral/positive pair.

## Lean artifacts and audit

| Module | Public declarations | Role |
|---|---:|---|
| [EndpointCycleDeterminant](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/EndpointCycleDeterminant.lean) | 7 | Cycle matrices, endpoint cofactor, exact odd determinant term |
| [SharpCycleGramRealization](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SharpCycleGramRealization.lean) | 9 | Explicit samples, actual Gram matrix, exact difference and nonzero-amplitude criterion |
| [SharpGramDetectionOrder](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SharpGramDetectionOrder.lean) | 10 | Lower bound, explicit padding, complete iff, concrete polar pair |

All 26 explicit public declarations, comprising 8 definitions and 18 theorems, received signature and axiom inspection. Every axiom list is exactly `propext`, `Classical.choice`, `Quot.sound`. No added axioms or analytic premises. All three leaves have clean successful checks; the final named-leaf check also exited 0 with an empty log. Matrix, analytic, and common-helper API probes passed against the installed toolchain.

The shared compiled cache changed repeatedly during this work. Checks therefore selected an isolated snapshot of the required compiled project dependencies. The three previously audited parent sources and their selected compiled artifacts match their earlier SHA256 fingerprints exactly. No dependency source was edited. The final audit ran from `formal/` through the same installed compiler and Lake environment:

```sh
lake --old env /bin/sh -c \
  'LEAN_PATH="/tmp/bsu-wall13-gram-cache:$LEAN_PATH" exec lean "$@"' \
  lean -j 1 GaloisForLFunctions/BiScaleUncertainty/SharpGramDetectionOrder.lean
```

Audit artifacts:

- `/tmp/bsu-wall13-gram-manifest.json`: checked source/artifact hashes, every public declaration, parent fingerprints and audit records.
- `/tmp/bsu_wall13_gram_axioms.lean` and `/tmp/bsu-wall13-gram-check-axioms.log`: complete public signature/axiom audit.
- `/tmp/bsu-wall13-endpoint-cycle-r6.log`, `/tmp/bsu-wall13-gram-check-grid.log`, `/tmp/bsu-wall13-gram-check-order.log`: clean leaf checks.
- `/tmp/bsu-wall13-gram-check-final.log`: clean final named-leaf audit.
- `/tmp/bsu-wall13-gram-basic-api.log`: clean common-helper API probe.

All three modules are imported exactly once by the BiScale umbrella. No umbrella or full build was run. Index refresh passed (`/tmp/bsu-wall13-gram-index.log`). Three documented lexical queries returned all 26 public declarations, with no missing declarations or result markers; the complete comparison is `/tmp/bsu-wall13-gram-discovery-check.json`. This verifies discoverability of this package, not completeness of the wider research corpus.

Global `scripts/formal_tools.py lint` exited 1: 381 large-file warnings and six unrelated modules unreachable from the BiScale umbrella: `CentralBinomialRatioGrowth`, `FactorialPolarGramScaleSeparation`, `FactorialPolarLossAsymptotic`, `FactorialPolarLossLowerBound`, `MertensValuationBudget`, and `StationaryResolventMarkovPositivityAndNodalDefectProducer`. None of the three modules in this package was reported. These concurrent files were left untouched. Full log: `/tmp/bsu-wall13-gram-lint.log`.

## Frontier evidence and limits

Before formalization, all 20 candidate and 20 source statements returned in `/tmp/bsu-wall13-gram-threshold-frontier.json` were inspected. No applicable exact determinant threshold was supplied. Semantic coverage was unmeasured, compiler statuses source-only, and background refresh incomplete. The follow-up `/tmp/bsu-wall13-gram-cofactor-search.json` was partial because semantic retrieval timed out; all 40 returned candidate/source statements were inspected. Source inspection and scratch probes verified the matrix APIs actually used. These bounded searches do not establish exhaustive absence or external novelty.

The new result closes the determinant-cancellation gap left by the sharp closed-product theorem. Spatial separation determines the first Gram order capable of exposing the relative copy sign in this explicit family. The exact nonzero determinant formula is the positive structural statement behind the finite-order obstruction.

This does not establish full-Gram recovery for arbitrary compact sources, stable recovery, a coercive energy bound, or a transfer between pointwise and Bochner cones. **Wall 13 remains open; the all-walls goal remains active.** The [failed fixed-order recovery route](../5-failed/wall13-fixed-order-polar-recovery.md) retains its negative conclusion and now has this sharp formalized survivor.

After this bounded package, reassess a different wall or mechanism from the current ledger rather than automatically extending the copy-orientation hierarchy. Preserve the concurrent Bézout and factorial-family work. The field READMEs and walls ledger remain read-only for this task.
