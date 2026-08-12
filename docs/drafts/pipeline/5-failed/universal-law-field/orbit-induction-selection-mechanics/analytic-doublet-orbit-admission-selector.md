# Analytic-doublet orbit-admission selector

- **ID:** ULF-OISM-FAIL-1
- **Stage:** 5-failed
- **Type:** FAILED LITERAL SELECTION APPLICATION / POSITIVE SURVIVOR
- **Parent:** ULF-OISM-1 and ULF-OISM-2
- **Verdict:** The moving-horizon analytic prime doublet realizes the weighted orbit mechanism and
  has a neutral-only Hilbert-admission locus, but global admission is already equivalent to RH.
  Orbit induction therefore reorganizes the receiver and strengthens the completion no-go; it does
  not supply the missing unconditional source theorem.
- **Status:** [FAILED AS RH PRODUCER] [EXACT RECEIVER] [LEAN-PROVED INPUT]
  [RECOVERY--REGULARIZATION SURVIVOR] [NOT RETIRED SOURCE]

## 1. Candidate

For a centered grade `t` and prime `p`, the literal analytic reflection doublet after the physical
half-density connection has amplitudes

```text
stable:   s_t(p) = t p^(-1/2-|t|),
unstable: u_t(p) = t p^(-1/2+|t|).
```

Its positive local energy is

```text
e_t(p)=t^2 p^(-1-2|t|)+t^2 p^(-1+2|t|).
```

These are pre-completion coefficient formulas.  Functional reflection exchanges the two analytic
branches.  The connection supplies the neutral-only factor `t`.

## 2. Exact weighted-orbit classification

For `t != 0`:

1. `sum_p |s_t(p)|^2 < infinity`, because the exponent is strictly below `-1`;
2. `sum_p |u_t(p)|^2 = infinity`, because the exponent is at least `-1`;
3. the full doublet is not in the ordinary all-prime Hilbert carrier.

At `t=0`, both channels vanish.  Hence

```text
full analytic doublet is square summable  <->  t=0.
```

This is already formally proved by
`summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_iff` in
`HedenmalmThetaMovingHorizonAnalyticDoubletNoGo.lean`.

Under ULF-OISM-2 this is the essential/nonsummable phase of a weighted prime orbit.  The stable
projection is a summable one-sided formation; the full reflection packet is not.

## 3. Why it does not prove RH

For a Xi-zero copy `q`, the same Lean module proves

```text
doublet admission at q  <->  theta boundary flux at q is zero,
all-copy doublet admission  <->  RH.
```

Therefore the missing premise

> every literal analytic doublet belongs to the ordinary all-prime Hilbert carrier

is not an unconditional consequence of entireness, reflection, or source formation.  It is an
RH-equivalent receiver condition.  Invoking it as “global orbit admission” would be circular.

The orbit-induction theorem does not change this logical status.  It says what admission would
force; it does not manufacture admission.

## 4. Completion repairs fail under bounded recovery

One can force off-wall summability by inserting a decaying prime weight `a_p`.  However, any such
regularization requires `inf_p |a_p|=0`.  ULF-OISM-2, Theorem 11.1, then gives:

```text
regularized bounded target history
    => decoder norms diverge on the cofinal source history.
```

For a diagonal completion, bounded coefficient recovery is equivalent to
`inf_p |a_p| > 0`, which leaves the unstable prime sum divergent.  Thus:

```text
off-wall regularization  and  bounded coefficient-faithful recovery
cannot coexist.
```

Functional equation does not help: it exchanges the stable and unstable legs and preserves their
combined divergence.

## 5. Failed conjecture loops

1. **Infinite orbit plus neutral-only local factor proves selection. -- False.** Global admission
   is still a separate source theorem and is RH-equivalent here.
2. **Entireness admits both analytic legs in one positive Hilbert completion. -- False.** The
   unstable leg is prime-harmonic-or-worse for every nonzero grade.
3. **A decaying diagonal completion repairs admission without information loss. -- False.** It has
   no bounded coefficient decoder.
4. **Functional-equation exchange cancels stable and unstable energy. -- False.** Positive
   completion adds the two energies.
5. **The stable projection is source-canonical because it is finite. -- False.** Choosing the
   decaying branch depends on the sign of the unknown grade unless an independent Hardy/polar
   source operation constructs it.

## 6. Strongest positive survivor

The failed application leaves a precise universal law:

> A positive completion may either retain both functional-equation branches and lose off-neutral
> admission, or regularize/select one branch and lose bounded common recovery.  It cannot do both
> by a diagonal, coefficient-faithful formation.

The remaining literal producer is therefore not another summability proof.  It must construct a
non-diagonal source-native stable/Hardy projection or an off-diagonal cancellation before positive
completion, and then prove its global source identity without reading zero grade.

## 7. Lean status

Read-only audit only.  Existing unconditional Lean support:

- `thetaMovingHorizonAnalyticCovariantDoubletEnergy_eq_stable_add_unstable`;
- `not_summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy`;
- `summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_iff`;
- `all_summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_iff_riemannHypothesis`.

The new generic recovery--regularization theorem is paper-proved in ULF-OISM-2 and Lean-pending.

