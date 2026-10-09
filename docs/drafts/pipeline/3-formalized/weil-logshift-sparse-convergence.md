# Sparse convergence and covering probes recover Cauchy control

Status: [PAPER PROVED; LEAN VERIFIED]
Date: 2026-10-09
Source policy: our Lean corpus only; no web searches or external papers.

## Exact claims and plan

1. Expose the already-proved bounds for the explicit probe
   `m_j=floor(exp j)+1`: `m_j>=2` and `j<=log m_j<=j+1`.
2. Generalize the sampled deficit block argument to real probe centers y_j:
   every log n in block j is within a fixed finite radius R of y_j; the signed potential
   series converges at each y_j; and their values share a real lower bound b.
   Together with summable excess, these conditions imply uniform deficit
   block mass and Cauchy control of absolute normalized deviation.
3. Prove the exact log-shift criterion using convergence only at the explicit
   m_j, while retaining the potential inequalities at every integer m>=2.
4. Audit both changed leaves, all affected public results, index, lint, and
   existing umbrella wiring; clean owned scratch files.

## Dependency-closed paper proof

Write a for normalized deviation, e for its excess, v for deficit, E=sum e,
K for riemannAutocorr, and psi for the signed potential.

The corpus already bounds the excess potential by `2 K(0) E` at every real
shift. At each convergent sample y_j, the signed/excess decomposition proves
deficit convergence and

`0<=potential_v(y_j)<=S:=2 K(0) E-b`.

Thus S>=0. The corpus provides continuity and strict positivity of K. Its
minimum on the compact interval [-|R|,|R|] gives kappa>0; any distance at most
R is also at most |R|, so this bounds K at every covered difference. For every
finite subset F of block j, the covering condition and nonnegative terms give

`kappa sum_F v <= potential_v(y_j) <= S`.

Hence deficit block mass is uniformly at most S/kappa. Adding total excess
and using |a|<=e+v bounds absolute block mass. The existing generic
block-to-Cauchy theorem finishes. No unit-radius restriction, integer-valued-probe restriction, origin
convergence, coefficient growth premise, or comparison with psi(0) is needed
for this covering-probe result.

For m_j=floor(exp j)+1, exp j>=1 and exp 1>=2 imply
`exp j<=m_j<=exp j+1<=exp(j+1)`. Thus m_j>=2 and log m_j is in [j,j+1],
within distance one of every logarithm in block j. This is already the
witness used by the existing existential probe lemma; expose its bounds.

For the sparse criterion, use y_j=log m_j and b=psi(0). The retained
integer-log potential inequalities supply the common lower bound at these
probes. Cauchy control and the previous Cauchy/potential equivalence give
asymptotic positivity. Conversely, asymptotic positivity plus summable excess
already gives convergence at every real shift and all sampled inequalities.

## Scope and boundary

Preserve all existing public statements. Generalize their shared proofs and
keep old results as corollaries. No new module is needed; existing umbrella
imports must remain present. The sparse criterion removes convergence tests
at all intermediate integers, but does not remove their potential inequalities.
No claim of mixed-sign rigidity, deficit summability, or external novelty.
No new axioms, numerical experiments, or heartbeat increases.

## Lean artifacts and validation

In `formal/GaloisForLFunctions/RHTower/WeilLogShiftDeficitTranslation.lean`:

- `integer_log_probe_bounds`
- `integer_log_probe_covers_block`

The existing existential probe theorem now follows from these explicit bounds.
In `formal/GaloisForLFunctions/RHTower/WeilLogShiftSampledPotentialCone.lean`:

- `exists_deficit_logBlock_bound_of_potential_cover`
- `exists_cauchyBounded_absDeviation_of_potential_cover`
- `weilLogShiftAsymptoticPositive_iff_sparse_potential`

The covering results allow any fixed real radius R and any real common lower
bound b. The compact-kernel minimum proof uses [-|R|,|R|], so no separate
nonnegative-radius premise is introduced. Existing sampled statements and
their public signatures are preserved as corollaries.

Both changed leaves passed final `lake --old env lean ... -o ...` checks,
with default heartbeats and no diagnostics. Scratch checks verified compactness
APIs against this toolchain. Signature and axiom audit passed for all eight
public results in DeficitTranslation, all six in SampledPotentialCone, and
all five dependent Cauchy results: nineteen total, each using exactly
`[propext, Classical.choice, Quot.sound]`.

Existing umbrella imports verified. Index refresh passed and all five new
API rows were checked. Scoped whitespace checks passed. Authoritative lint
exited 1 with eight unrelated unreachable modules: RHTower's
`SquareResidueQuadraticCompletion`, `SquareResidueQuadraticInterval`,
`StretchedBoseNonDensity`; HTGeometry's `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
and `BoundaryCoronaCStarAlgebra`. No reported lint error concerns these leaves.

The exact local lexical query found no match. Broader local search returned
727 declarations across 318 modules; ranked hits and relevant source proofs
identified the needed dependencies. This supports a corpus dependency
reduction, not external novelty or exhaustive semantic coverage.

## Exact insight and remaining frontier

Local convergence need only be checked on probes covering the logarithmic
line within a fixed radius, provided their signed potential values have a
uniform lower bound and total excess is finite. This recovers uniform local
mass and Cauchy control without origin convergence or coefficient growth.
The exact log-shift criterion can therefore use the explicit sparse sequence
floor(exp j)+1 for convergence while keeping all integer-log potential inequalities.

The unrestricted convergence-free criterion is now disproved in
`../5-failed/weil-logshift-convergence-free-potential-no-go.md`: a zero-excess
minorant has every sampled partial sum tending to minus infinity while all
totalized potentials vanish. This sparse-convergence criterion is the audited
positive survivor. Genuine mixed-sign rigidity remains open.
