# Thermodynamic affinity as clock holonomy

- **ID:** thermodynamic-affinity-clock-holonomy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Physics sources:** stochastic thermodynamics, chemical reaction-network cycle affinities,
  molecular motors and Brownian clocks
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy`,
  `GaloisForLFunctions.RHTower.PrimeArchEntropyProductionResponseRH`
- **Statement:** Positive forward/reverse observable values have nonnegative current-affinity
  product; their rate ratio is a reversible clock calibration, nonunit loop holonomy forces a
  strictly positive entropy-production edge on that loop, and finite KMS entropy production equals inverse
  temperature times the existing dissipative intensity.

## Goal

Transfer an orientation-sensitive value relation shared by nonequilibrium physics, chemistry and
biology into the static observable geometry of hypertranscendental functions. The transfer must
not install a time evolution. It should strengthen the Weyl clock-calibration theorem, discharge a
reversibility hypothesis for rate-ratio calibrations, and leave a positive witness when global
scalar calibration fails.

## Gates

- [x] 0 → 1 in-progress: exact parent identity and corpus consumer identified
- [x] 1 → 2 fully-proven: paper proof reduces to order-monotonicity of `log`, telescoping ratios,
  and the existing connected-graph clock-integrability theorem
- [x] 2 → 3 formalized: Lean module, targeted build, direct file check and axiom audit
- [ ] 3 → 4 publication-ready: not promoted; this is established parent mathematics formalized as
  a project bridge

## Parent identity

For `f,r>0`, define

```text
J(f,r) = f-r,
A(f,r) = log(f/r),
Σ(f,r) = J(f,r) A(f,r).
```

Monotonicity of the logarithm gives

```text
Σ(f,r) ≥ 0,
Σ(f,r) > 0  iff  f ≠ r,
Σ(r,f) = Σ(f,r),
A(r,f) = -A(f,r).
```

Thus entropy production detects failure of local detailed balance but forgets its orientation.
This is the positive residue of the no-go: passivity or entropy production alone cannot choose the
directed prime--archimedean sign.

For a positive directed rate field `k(u,v)`, the multiplicative edge calibration

```text
c(u,v) = k(u,v) / k(v,u)
```

is automatically reversible. On a connected observable graph, the existing static clock theorem
therefore becomes the Kolmogorov/Wegscheider criterion:

```text
one global multiplicative detailed-balance potential exists
  iff
every closed rate-ratio holonomy is one.
```

If one closed holonomy is nonunit, some edge used by that loop satisfies
`Σ(k(u,v),k(v,u))>0`.

## KMS application

For finite Gibbs populations `p_a`, Hermitian transition amplitude `M_ab`, energy gap
`ΔE=E_a-E_b`, and inverse temperature `β`, Lean proves

```text
log(p_b/p_a) = β ΔE,
Σ_KMS(a,b) = (p_b-p_a)|M_ab|² log(p_b/p_a),
Σ_KMS(a,b) = β D_KMS(a,b),
Σ_KMS(a,b) ≥ 0,
Σ_KMS(a,b) = Σ_KMS(b,a).
```

Here `D_KMS` is the already formalized finite dissipative transition intensity. This identifies its
physical normalization and proves that entropy production is orientation-blind even though its
current and affinity factors are separately oriented.

## Direct corpus effect

- `ClockCalibrationReversible` is automatic for every nonzero rate-ratio field.
- `clockCalibrationExact_iff_flat` now supplies the full graph detailed-balance cycle criterion.
- `FiniteKMSFluctuationDissipation` gains an exact entropy-production interpretation and a
  nonnegative value at arbitrary inverse temperature.
- The `RHTower` passive-response limit and RH capstone lose the hypothesis `β ≥ 0` when the
  response is formulated with entropy-production intensity.
- A nontrivial clock holonomy now has a positive local witness rather than only the negative
  conclusion that no global scalar clock exists.

For `RHTower`, this is a route discriminator rather than an RH proof. A passive/KMS construction
can certify nonnegative dissipation, but the formal reversal symmetry proves that it cannot select
the orientation of the prime--archimedean mirror defect. Any successful consumer must retain one
oriented factor—current, affinity, branch, puncture or source divisor—before their product erases
the sign.

## Literature gate

The bridge is standard parent mathematics, not claimed as new scientific knowledge.

- U. Seifert, *Stochastic thermodynamics, fluctuation theorems and molecular machines*,
  arXiv:1205.4176.
- R. Rao and M. Esposito, *Nonequilibrium Thermodynamics of Chemical Reaction Networks: Wisdom
  from Stochastic Thermodynamics*, arXiv:1602.07257.
- M. Polettini and M. Esposito, *Irreversible thermodynamics of open chemical networks I: Emergent
  cycles and broken conservation laws*, arXiv:1404.1181.
- A. C. Barato and U. Seifert, *Cost and Precision of Brownian Clocks*, arXiv:1610.07960.

## Lean certificate

The modules export the elementary affinity and entropy-production laws, the rate-ratio calibration
and automatic reversibility theorem, the connected graph exactness/flatness criterion, the
positive holonomy witness, the finite KMS specialization, and the arbitrary-temperature
prime--archimedean passive-response consumers. No new axiom, `sorry`, `admit`, `opaque`, or
`unsafe` declaration is introduced.
