# TG C9.22a: actual Hardy commutator continuity in trace norm

- **Stage:** 3-formalized
- **Route:** TG, source-to-Hardy operator-ideal admission
- **Parent:** tg-gamma-clock-nuclear-phase-admission.md
- **Production:** formal/GaloisForLFunctions/RHTower/CCM/CCMArchimedeanNuclearContinuity.lean

## Exact statement

The existing positive Hankel operator and literal Hardy quantized differential
have continuous lifts from Schwartz space into SchattenOneOperator SoninL2,
with its genuine trace norm. The latter lift is exactly [H,M_g], retaining
both actual Hardy crossblocks. No operator-norm limit is relabeled trace-norm
convergence, and no trace-class or continuity premise is assumed.

## Dependency-closed proof

The corpus's literal positive Hankel factorization is H_g=S_g V. Its fixed
Volterra observer V is Hilbert–Schmidt. Its derivative synthesis S_g has
Hilbert–Schmidt norm equal to the L2 norm of its Bochner field. Integrating
the existing derivative-slice majorant gives

 ||field(g)|| <= pi * C(g),

where C(g) is the existing finite sixth-order Schwartz seminorm of g'.
The exact field and Hankel difference laws retain linear dependence on g.
Schatten Holder bounds ||H_g||_1 by ||V||_2*pi*C(g). The finite seminorm is
continuous and vanishes at zero, so this proves trace-norm continuity.

The literal upper time crossblock is H_(FourierInv g) followed by reflection.
The lower crossblock is the adjoint of the upper block for conjugate g.
Continuous left/right ideal actions, isometric adjoint, Schwartz Fourier
continuity, and the existing exact Fourier crossblock identities give the
continuous nuclear lift of 2(upper-lower), namely the original [H,M_g].

## Verification and contribution

2026-10-04: final foreground `lake --old env lean
GaloisForLFunctions/RHTower/CCM/CCMArchimedeanNuclearContinuity.lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/CCM/CCMArchimedeanNuclearContinuity.olean`
exits 0, empty diagnostics. Separate /tmp audit of all five public declarations
exits 0: exactly propext, Classical.choice, Quot.sound. Umbrella wired; no full
or umbrella build. Index0 records all five. Lint1 reports sixteen unrelated
unreachable modules, no finding in this leaf. Default heartbeats throughout.
Logs: `/tmp/tg-c922-nuclear-{final,axioms,index,lint}.log`.

This closes the ideal-topology step of C9.22. The original Gamma cutoff symbol
convergence and its varying products still need proof. This analytic ingredient
alone supplies no arithmetic energy, completed relative cubic comparison,
strict contraction, or RH conclusion.
