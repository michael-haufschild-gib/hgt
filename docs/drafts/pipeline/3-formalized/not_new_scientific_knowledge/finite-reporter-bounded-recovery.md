# Bounded recovery and conditional-information condition control

- **ID:** `finite-reporter-bounded-recovery`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, quantitative observation recovery
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.FiniteReporterBoundedRecovery`
  - `GaloisForLFunctions.RHTower.XiLogDerivReporterBoundedRecovery`

## General value law

Let `R` be a source reporter, `D` a bounded postprocessor, and `Q` a bounded exact left recovery
on the reporter image:

```text
Q o D o R = R.
```

For the conditional Gram/Fisher information `I_N` contributed by the `N`-th derivative-clock
reading, forward data processing and recovered data processing give the two-sided inequality

```text
I_N(D o R) <= ||D||^2 I_N(R),
I_N(R)     <= ||Q||^2 I_N(D o R).                         (1)
```

If `||Q|| <= C` with `C > 0`, equation `(1)` yields the explicit lower transport bound

```text
I_N(R) / C^2 <= I_N(D o R).                               (2)
```

If both `D` and `Q` are contractions, the two bounds meet and conditional information is exactly
preserved.  This derives the equality case from recoverability and norms; the encoder need not be
presented as a separately packaged linear isometry.

## Positive content and no-go

The existing data-processing theorem supplied only an upper information bound.  Equations `(1)`
and `(2)` add the missing quantitative lower bound for any exactly recoverable observation
channel.  Hence surviving clock innovations cannot be arbitrarily attenuated by a well-conditioned
recoding.

The corresponding no-go is also exact: recovery returns only what the original reporter retained.
If the source direction was erased before `D`, neither `D` nor `Q` recreates it.  The significant
positive replacement is quantitative transport of all non-erased values.

## Direct Xi application

For the Xi logarithmic-derivative reporter, the decoder/recovery norm sandwich holds uniformly at
every derivative order.  Thus any exact holographic, quantum-error-correcting, learned, or inverse
measurement recoding of the Xi reporter has explicit condition-number control throughout the
conditional-information tower.

This strengthens the earlier isometric Xi result, but it does not remove the unconditional
finite-dimensional reporter collapse.  That collapse occurs in the original observer algebra;
bounded recovery faithfully transports the same zero.

## Cross-domain scope

The value law applies to:

- exact quantum error-correcting and holographic reconstruction maps;
- quantum reference-frame recodings;
- sensor fusion and inverse measurement systems;
- learned encoders with an explicit bounded decoder;
- genomic or biochemical reporters with bounded reconstruction;
- any finite derivative-clock observation panel in `HTGeometry`.

Recovery/data-processing provenance: Gao--Li--Marvian--Rouze, arXiv:2302.02341, and
Beny--Oreshkov, arXiv:0907.5391.

## Lean surface

- `finiteDerivativeReporterConditionalInformation_le_recovery_norm_sq_mul`
- `finiteDerivativeReporterConditionalInformation_boundedRecovery_sandwich`
- `finiteDerivativeReporterConditionalInformation_div_recovery_bound_le`
- `finiteDerivativeReporterConditionalInformation_eq_of_contractive_recovery`
- `xiLogDerivReporter_boundedRecovery_sandwich`
- `xiLogDerivReporter_div_recovery_bound_le`

## RH impact and boundary

This discharges the missing lower information bound whenever an RH-facing reporter construction
comes with a bounded exact recovery.  It allows estimates to be moved through a recoding without
reproving every conditional-information inequality in the new representation.

It is not a source producer and cannot prove RH by itself.  In particular, it neither prevents the
finite-reporter Xi collapse nor supplies the missing prime--archimedean positive spectral measure.

## Verification

- [x] exact HT module target built and cached
- [x] exact Xi specialization target built and cached
- [x] both touched Lean files check directly
- [x] no full or concurrent build used
- [x] no numerical computation used
