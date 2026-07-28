# Free de Sitter curvature commutator does not retain Gamma hypertranscendence

- **ID:** `de-sitter-free-curvature-commutator-ht`
- **Stage:** 5-failed
- **Type:** FALSIFIED PHYSICAL CARRIER / POSITIVE DIFFERENTIAL-CLASS SURVIVOR
- **Source:** Mora--Woodard tree-level de Sitter Weyl correlator; de Sitter Bogoliubov HT corpus
- **Statement:** In four-dimensional de Sitter space, the gauge-invariant tree-level
  Weyl--Weyl correlator is rational in invariant separation, so its antisymmetric commutator
  cannot carry the Gamma hypertranscendence of the global-to-static Bogoliubov phase.

## Failed conjecture

The proposed curvature-echo protocol measures a smeared Pauli--Jordan/Peierls kernel of
gauge-invariant linearized curvature. The first attempted HT bridge was:

```text
de Sitter global-to-static Gamma HT phase
  survives in the free gauge-invariant curvature commutator
  and therefore in the echoed two-clock entangling phase.                   (1)
```

This would have placed classical curvature, quantum noncommutativity, and HT in one two-loop
observable.

## Exact killing mechanism

Mora and Woodard compute the noncoincident tree-level linearized Weyl--Weyl correlator on a
four-dimensional de Sitter background. Its scalar coefficient reduces to

```text
A''(y) = H^2/(16 pi^2) * (8/y^3 + 2/y^2),                   (2)
```

where `y` is de Sitter invariant separation. Tensor factors are built from the metric and
derivatives of `y`. Thus the scalar coefficient is rational, hence differentially algebraic.
Taking the antisymmetric boundary-value difference to obtain the commutator cannot restore the
separate global-mode Gamma phase that curvature differentiation has already removed.

The paper explicitly identifies why: derivatives converting the graviton field to linearized
Weyl curvature remove the logarithmic infrared contribution and leave a simple de Sitter-invariant
result. Equation `(1)` is therefore false at tree level in free four-dimensional de Sitter gravity.

## Strongest positive survivor

The failure sharply separates two layers of quantum spacetime:

```text
local free curvature causal algebra
  = gauge-invariant, infrared-safe, finite differential class;

global clock/mode orientation phase
  = capable of retaining Gamma hypertranscendence.                          (3)
```

Consequently the chronodromy program must not demand that one two-point commutator carry every
kind of information. The curvature commutator remains the correct candidate for a classical-null
quantum-gravity echo, while HT must be sought in:

1. a higher connected chronodromy cumulant from gravitational interactions;
2. a genuinely global/projective closed clock-frame cycle;
3. a black-hole or extremal scattering reporter whose mode-gauge quotient does not remove its
   coupled special-function dependence.

This is a positive architecture theorem: local quantum causal structure and global clock-atlas
complexity are independent axes even when they belong to one complete chronodromy probability
law.

## No-go closure

- **Exact killing theorem/mechanism:** equation `(2)` makes the free four-dimensional de Sitter
  Weyl reporter rational in invariant separation; antisymmetrization cannot recover the removed
  Gamma mode phase.
- **Strongest positive survivor:** separation law `(3)` and the three surviving HT loci above.
- **New insight:** an HT Bogoliubov phase can be physical relative to a global clock split while
  remaining absent from local gauge-invariant curvature two-point data. “Quantum,” “curved,” and
  “HT” are distinct information axes.
- **Status:** physical formula and inference paper-audited; exact rational differential-algebra
  survivor not yet Lean-formalized, so closure is not complete.

## Primary source

- P. J. Mora and R. P. Woodard, *Linearized Weyl-Weyl Correlator in a de Sitter Breaking Gauge*,
  <https://arxiv.org/abs/1202.0999>, especially the four-dimensional reduction of `A''(y)`.
- A. Higuchi, *Equivalence between the Weyl-tensor and gauge-invariant graviton two-point
  functions in Minkowski and de Sitter spaces*, <https://arxiv.org/abs/1204.1684>.

## Log

- 2026-07-28 — route falsified by the exact four-dimensional tree-level Weyl correlator.
  Preserved local/global differential-class separation as positive survivor; Lean closure remains.
