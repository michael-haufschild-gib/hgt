# Mass-shifted centered-source degree capital

- **ID:** `mass-shifted-centered-source-degree-capital`
- **Stage:** 3-formalized
- **Route:** U, signed completed-source degree renewal
- **Type:** THEOREM / quantitative positive survivor
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Depends on:** `mass-shifted-apex-centered-source-log-derivative`,
  `mass-shifted-super-apex-degree-persistence`, finite outer Gauss-node interlacing

## Frozen claim

Fix one positive finite moment block and one positive hard mass `y`. If all current Gauss nodes
are positive, outer interlacing selects a next-degree node `z` above every current node `x` and

```text
(y*x)^2 - 1 < (y*z)^2 - 1.
```

For canonical shifted-Xi admission at fixed `w > 1/2`, these quantities are exactly the literal
de-resisted, moving-apex-centered completed-source residues. Therefore every positive current
source atom has a strictly larger positive next-degree source atom. Degree renewal cannot shrink
centered source residue at fixed mass.

## Conjecture -> proof/fail loop

1. **Positive null flag persists across degree.** Already formalized; qualitative and therefore
   insufficient for a cumulative source budget.
2. **The full Poisson null-flag value is monotone.** False as a generic inference: its aperture
   denominator depends on node location and may outweigh residue growth for fixed center.
3. **The pre-reporting source residue itself is strict degree capital.** Survives. Outer
   interlacing gives `x < z`; positivity of `x`, `z`, and `y` makes squaring strictly monotone.
   De-resistance identifies both literal source coefficients with one before centering, so no
   admission resistance or aggregation weight remains.
4. **Fixed-mass capital closes Route U.** False. Shifted-Xi mass transport changes both measure
   and nodes; theorem isolates all possible loss to continuous mass motion. It supplies no
   cross-mass lower bound and does not prove RH.

## Dependency-closed paper proof `[PROVED HERE]`

Let current Gauss nodes be roots of monic orthogonal polynomial `P_(m+1)`. Finite positive moment
admission gives outer interlacing: there is a root `z` of `P_(m+2)` such that `x < z` for every
current node `x`. Current node set has cardinality `m+1`, hence is nonempty. If all current nodes
are positive, select one to get `z > 0`.

For arbitrary current node `x`, positivity gives

```text
0 < y*x < y*z.
```

Strict monotonicity of the square on the positive ray yields

```text
(y*x)^2 - 1 < (y*z)^2 - 1.
```

For shifted-Xi canonical admission, exact de-resistance theorem states at every nonzero admitted
root

```text
CenteredCompletedSourceResidue(w,n,x) = (w^2*x)^2 - 1.
```

Apply it to current degree `n=m+1` and next degree `n+1=m+2`. Since `z>0`, all required nonzero
conditions hold. Substitution proves literal source inequality. If current residue is positive,
transitivity makes next residue positive and strictly larger.

No limit, numerical computation, representing measure, RH premise, post-aggregation orientation,
or chosen reporter enters.

## Novelty and hostile audit

Classical interlacing explains existence of the outer node. Classical monotonicity of `u^2-1` on
the positive ray is bridge algebra. Corpus searches found no theorem identifying this strict
outer-node gain with the literal de-resisted completed prime--Gamma/von-Mangoldt source at two
adjacent canonical admissions. Candidate novelty is that source-specific splice and its exact
localization of remaining loss to mass transport. No priority claim is made pending specialist
review.

## Exact residual

Prove a mixed mass--degree balance for this capital. Correct target must compare residue after
continuous shifted-Xi mass transport with the strictly larger fixed-mass successor supplied here.
A scalar Poisson flag at fixed aperture is not sufficient because its denominator can change.

## Lean target

- generic module: `HTGeometry/FiniteExtremeSourceCapital.lean`;
- shifted-Xi module:
  `RHTower/XiShiftedCanonicalAdmissionCenteredSourceDegreeCapital.lean`;
- direct Lean, targeted builds, umbrella wiring, and axiom audit required before promotion.

## Lean certificate

- `HTGeometry.exists_gaussNode_apexCenteredResidue_above_all_below`;
- `RHTower.exists_xiShiftedCanonicalAdmissionCenteredSourceResidue_above_all_succ`;
- `RHTower.exists_xiShiftedCanonicalAdmissionCenteredSourceResidue_succ_gt_of_pos`.

Both modules are wired into `HTGeometry.lean` and `RHTower.lean`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/FiniteExtremeSourceCapital.lean` — PASS;
- `lake build GaloisForLFunctions.HTGeometry.FiniteExtremeSourceCapital` — PASS;
- `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionCenteredSourceDegreeCapital.lean` — PASS;
- `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCenteredSourceDegreeCapital` — PASS;
- `/tmp` `#print axioms` audit for all three capstones — only `propext`,
  `Classical.choice`, and `Quot.sound`;
- `git diff --check` on all changed files — PASS;
- repository lint reaches both new modules. Its nonzero exit is pre-existing/concurrent unreachable
  module debt in unrelated CCM, Deninger, Sieve, and HTGeometry modules; neither new module appears
  in lint errors.

## Log

- 2026-08-13 — conjecture isolated after rejecting monotonicity of posterior Poisson flag;
  dependency-closed proof completed.
- 2026-08-13 — generic and literal source-capital theorems formalized, built, umbrella-wired, and
  axiom-audited; promoted to Stage 3.
