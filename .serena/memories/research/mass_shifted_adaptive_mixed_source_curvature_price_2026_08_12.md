# Mass-shifted adaptive-mixed source curvature price (2026-08-12)

New module: formal/GaloisForLFunctions/RHTower/XiShiftedAdaptiveMixedFrontierPrice.lean, umbrella-wired in RHTower.lean.

Finding: on any higher odd shifted-Xi null contact, existing nondegenerate admission-sensitive arithmetic source S is formed before rational--Gamma/von-Mangoldt aggregation and equals twice first odd Pade defect delta. Therefore source magnitude squared is exactly parity-complete curvature numerator: price Pi=((S/2)^2*(2*(|a|+1)-a)/( |a|+1)^2)/W(A), with adaptive null-pair A. If delta != 0, Pi>0 using actual integral Lipschitz denominator and w^2+Pi<=terminalFrontier(n+m).

Capstones:
- xiShiftedAdaptiveMixedOddContactFrontierPrice
- xiShiftedAdaptiveMixedOddContactFrontierPrice_eq_firstOddDefect
- xiShiftedAdaptiveMixedOddContactFrontierPrice_pos
- add_xiShiftedAdaptiveMixedOddContactFrontierPrice_le_terminalFrontier
- xiShiftedAdaptiveMixedOddContactFrontierPrice_pos_and_le_terminalFrontier

Heavy-loop failures: source sign alone gives no uniform frontier increment; Riccati U'<-U^2 does not bound positive chamber lifetime because positive hyperbolic decay can persist forever. Survivor/higher principle: source-capacity renewal. Remaining exact RH burden is non-summable/cofinal lower control of Pi, equivalently prevent source magnitude, transverse conditioning, and Lipschitz transport efficiency from becoming summably negligible.

Verification: direct lake env lean pass; target lake build pass; axioms only propext, Classical.choice, Quot.sound. formal_tools lint fails only on unrelated pre-existing/concurrent unreachable modules; new module is indexed and umbrella-reachable. Report equations (9.3.615)-(9.3.617); Stage3 card mass-shifted-adaptive-mixed-source-curvature-price.md.