# TG C9.11p.1 — exact recovery of complete complex sources

- **Stage:** 3-formalized
- **Route:** TG, joint prime–Gamma relative admission
- **Status:** final leaf audit and all sixteen public axiom queries pass
- **Open parent:** ../1-in-progress/tg-principal-polar-operator-cancellation.md

## Hard question and contribution

Can the complete correction response acquire trace-norm cancellation that is
absent from its actual unsquared prime–polar source? No: the complete response
pair and the literal time-band source pair admit bounded real-linear
reconstruction in both directions. This identifies exactly where signed
arithmetic cancellation must occur, without an assumed admission theorem.
Actual prime–polar convergence, Gamma completion, Hardy cubic compatibility,
the strict sub-unit law and RH remain unproved.

## Corpus basis

The actual projections are A (physical forbidden), B (Fourier forbidden),
Q (Sonin), with Q0=1−A−B and J=Q−Q0. Existing leaves prove J trace class,
J self-adjoint, QJ=JQ=0, J²+J=AB+BA and

`C(D)=(1−Q)DJ−JDQ0`, `C(D)Q=−JDQ`.

The current deep searches `/tmp/tg-c911p-{kernel,nuclear-continuity,recovery}-search.json`
were partial, with snapshot coverage and incomplete background refresh.
Candidate lemmas and source arguments were inspected against source. No
claim of novelty or applicability relies on search completeness.

## Dependency-closed paper proof

Put F=1−Q. The operator 1+J equals Q+A+B. If (1+J)x=0,
taking the real inner product with x gives

`‖Qx‖²+‖Ax‖²+‖Bx‖²=0`.

Thus Ax=Bx=0, so x is Sonin, while Qx=0. Hence x=0. Since J is compact,
the compact Fredholm alternative implies that 1+J is boundedly invertible.
Write U=(1+J)⁻¹. This constructs the actual inverse; no spectral-gap premise
is introduced.

Projection algebra gives

`C(D)F=(1+J)F DJ`, `(C(D*)Q)*=−QDJ`.

Consequently, for every bounded complex source D,

`DJ=U C(D)F−(C(D*)Q)*`.

The reverse map is `C(D)=F(DJ)−(D*J)*Q0`. Applying both identities to D
and D* supplies bounded real-linear maps between the pairs

`(C(D),C(D*))` and `(DJ,D*J)`.

All entries belong to the genuine Schatten-one Banach carrier. Bounded
left/right multiplication and adjoint act continuously in its trace norm.
The maps therefore carry sums and arbitrary-filter limits in both directions.
There is no self-adjointness premise on D.

The polynomial identity further gives

`J=(AB+BA)U`, `AB+BA=J(1+J)`.

Thus bounded right multiplication reconstructs both ways between the left
source pair and the literal pair `(D(AB+BA),D*(AB+BA))`. Summability and
existence of an arbitrary-filter trace-norm limit are equivalent for the
complete response pair and this actual two-leg time-band source pair.
Both time-band terms and both adjoint-source directions remain present.

## Lean result

`formal/GaloisForLFunctions/RHTower/SoninCorrectionResponseRecovery.lean`
contains the inverse, operator recovery, genuine nuclear pairs, bounded
reconstruction maps and both summability/cofinal-limit equivalences.

Final check, 2026-10-02:

```
lake --old env lean GaloisForLFunctions/RHTower/SoninCorrectionResponseRecovery.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninCorrectionResponseRecovery.olean
lake --old env lean /tmp/tg-c911p-recovery-axioms.lean
```

Both exit 0. Final leaf diagnostics are empty. All sixteen public declarations
depend only on `propext`, `Classical.choice`, `Quot.sound`; no new axiom,
proof hole, numerical experiment or heartbeat override. The leaf is wired
into `RHTower.lean`; no full or umbrella build was run. Formal lint reports
eleven unrelated unwired leaves and no finding in this leaf.
The index command completed successfully; all sixteen public declarations
appear in `formal/LEAN_API.md`.

## Next hard conjecture

Construct the native signed prime–polar cutoff on the full Sonin carrier,
with the density `2 cosh(u/2)/u` and original symmetric dilation source.
Use the recovered literal time-band pair to prove a signed nuclear-tail
law, or extract its exact obstruction. The recovery equivalence proves
neither Cauchy control nor a critical-scale prime-error estimate.
