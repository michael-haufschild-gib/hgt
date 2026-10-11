# Fluctuation scale of canonical logarithmic transport

Status: formalized and natively audited.
Sources: local Lean corpus only. No external novelty claim.

## Target

For n=r+1 and k=2n^2+t(r), prove H/n ->1/4 and nR ->1/4, where H is
the canonical edge second moment about r/2 and R is the mass-weighted
local logarithmic correction squared error about 1/2. Offsets t(r) are
arbitrary natural numbers; no analytic hypotheses at the roots.

## Paper route

Write q for the arithmetic absolute profile, G=sum q, f for the canonical
central-rescaled profile, F=sum f, x_i=i-n/2, d_i=i-floor(n/2), and
S=sqrt((n+1)/2). Existing local distortion gives |f_i-q_i|<=q_i|d_i|/n.
The reverse ratio modulus and |i-j|<=n give f_i>=q_i/2, hence F>=G/2.

Prove the binomial centered fourth moment by Pascal induction:
sum choose(n,i)(2i-n)^4=(3n^2-2n)2^n. Therefore sum q_i x_i^4<=n^2 G.
Existing sum q_i d_i^2<=S^2 G and weighted Cauchy give
sum q_i |d_i|x_i^2<=G n S. Thus the weighted profile error against x^2
is <=G S, while |F-G|<=G S/n is already proved in the corpus.
With B=sum f_i x_i^2 and arithmetic second moment nG/4,
|B-nF/4|<=G S+(n/4)|F-G|<=2G S<=4F S.
Normalize: |sum M_i x_i^2-n/4|<=4S. The exact midpoint-edge identity
sum M_i x_i^2=H+1/4 gives |H-r/4|<=4S. Dividing by n proves H/n->1/4.

For the transport correction T_i, put z_i=nT_i-i-1/2. Existing indexed
bound gives |z_i|<=3/2. Consequently
|n^2 R-H|<=3 sum m_i|i-r/2|+9/4.
Weighted Cauchy bounds the first moment by sqrt(H). The new H estimate
and S<=n give sqrt(H)<=4S, so this difference is <=16S.
Divide by n and combine with H/n->1/4: nR->1/4.
The exact mixture-plan dispersion identity delta R transfers the
fluctuation law uniformly to arbitrary varying endpoints, as a vanishing
error n*plan_dispersion-delta/4.

## Plan and audit

- Prior edge-correction closure metadata revalidated, no issues.
- Search corpus for fourth-moment and weighted-normalization ingredients.
- Formalize fourth moments, weighted profile error, lower normalization.
- Prove sharp edge second-moment estimate and unconditional limit.
- Prove transport fluctuation comparison and full-mixture limit.
- Native leaf/API/axiom audit, imports and freshness, unique names,
  local root index, formal lint. No umbrella/full builds.

## Verification log

- Corpus-wide lexical AND search for binomial fourth moment returned no hit;
  exhaustive targeted Lean text search found no matching moment theorem.
- Exact binomial fourth moments passed native Lean without diagnostics.
- Arithmetic fourth moment, its quadratic bound, and the mixed third-moment
  Cauchy estimate passed native Lean without diagnostics.
- Profile lower normalization passed native Lean without diagnostics.
- Weighted profile second error, centered normalization error, and sharp
  midpoint second-moment estimate passed native Lean without diagnostics.
  A polymorphic absolute-square simp step needed explicit finite-sum
  congruence with the index supplied; repaired before the successful check.
- Sharp edge bound |H-r/4|<=4S, normalized error <=6S/n, and unconditional
  H/n->1/4 root passed native Lean without diagnostics.
- Edge centered absolute moment <=4S, raw comparison |n^2R-H|<=16S,
  and scaled comparison |nR-H/n|<=16S/n passed native Lean without
  diagnostics. Formal scalar remainder uses 3|x|+4; this retains the same
  final constant. Removed a redundant ring tactic after field_simp closed
  the normalization identity.
- Transport fluctuation error <=22S/n and unconditional nR->1/4 passed
  native Lean without diagnostics.
- Full-mixture fluctuation error <=22S/n and vanishing-error root passed
  native Lean without diagnostics, for arbitrary varying endpoint sequences.
- Metadata audit: eight leaves, 21 public theorems, globally unique; all
  15 incoming imports inspected. Own/direct artifacts fresh, leaf logs
  empty, whitespace clean; each leaf wired once in RHTower umbrella.
- All three roots found by local indexed search, no markers. Scoped diff
  check passed.
- Final native scratch audit passed: all 21 public theorems use only
  propext, Classical.choice, and Quot.sound. Eight API references also
  type-checked. All owned native jobs are terminal.
- Repository lint: 367 size warnings and seven unrelated errors. Missing
  umbrella imports: RHTower.CCMParityTopLayerAlternation,
  CCMParityTopLayerEvenModel, CCMParityTopLayerOddFloor,
  CCMPolarOddPrimeJumps, XiGaussianHeatHankelWindowCeiling;
  HTGeometry.QKrawtchoukCompanionTriangular. Proof debt:
  CCMPolarOddPrimeJumps.lean:104, sorry in ccmPolarOddSource_eq_core_add_atoms.
  No lint issue belongs to this closure.

## Formal roots

- `WeilLogShiftEdgeVarianceScale.lean:60`:
  `tendsto_finiteWeilCanonicalEdgeCenteredSecondMoment_quarter`.
- `WeilLogShiftTransportFluctuationLimit.lean:29`:
  `tendsto_finiteWeilCanonicalEdgeLogCorrectionSecondMoment_fluctuation_quarter`.
- `WeilLogShiftMixtureFluctuationLimit.lean:32`:
  `tendsto_finiteWeilMixtureCoupling_log_correction_fluctuation_error_zero`.

All three quantify structural data only, with no unproved analytic premises.
H is centered at r/2, not at the actual edge mean; R is centered at 1/2.
No claim about variance around the actual means is made here.

## Audit artifacts

- `/tmp/hgt-fluctuation-metadata.py`
- `/tmp/hgt-fluctuation-declarations.json`
- `/tmp/hgt-fluctuation-incoming-imports.txt`
- `/tmp/hgt-fluctuation-final-audit.lean` and `.log`
- `/tmp/hgt-fluctuation-edge-root-search.json`
- `/tmp/hgt-fluctuation-transport-root-search.json`
- `/tmp/hgt-fluctuation-lint.log`
- Eight `/tmp/hgt-<Leaf>.log` native leaf logs.
