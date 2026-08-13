# Mass-shifted vacuum-free nondegenerate source action (2026-08-13)

Modules:
- `RHTower.XiShiftedCanonicalAdmissionAdjacentEdgeArithmeticAction`
- `RHTower.XiShiftedCanonicalAdmissionNondegenerateSourceEffectivity`
- `RHTower.XiShiftedCanonicalAdmissionVacuumFreeSourceRecession`

New unconditional laws:
1. Full nondegenerate two-amplitude null-flag source pays effectivity but has normalized unit floor; cannot be finite outgoing budget.
2. Subtract `P_n^2` inside source polynomial. Vacuum-free history is `H°_n = sum_{j<n} alpha_j^2 + 2 sum_{j<n} beta_j + 2 a_n^2 + alpha_n^2 >= 0` and `R_n^2 <= ((2n+1)^2+2) H°_n`.
3. Literal completed source `S°_n = 2 N_n H°_n`; hence division-free `2N_n R_n^2 <= K_n S°_n`.
4. Unit subtraction preserves exact odd-to-even null landing: at lifted null flag with first odd Pade defect delta, `A^sharp_circ(A,B)=2 delta` for arbitrary adjacent B, because moment of `A^2` is zero. This is source-first, not reporter.
5. Sharp recession: `y^2 S°_n(y)/(2N_n(y)) -> C_n`, with `C_1=1`, `C_n=(4n^2+3n+2)/8` for n>=2. Literal square-mass source has same law.
6. Actual integral action: `(log N_n(b)-log N_n(a))^2 <= (b-a) K_n integral S°_n/(2N_n)` on positive chamber.
7. Exact adjacent edge: `(log beta_n)'=R_(n-1)-R_n`; symmetric adjacent literal sources pay squared shared-edge velocity division-free.

Honest frontier:
- RH not proved.
- Mass recession is now proper at each fixed degree, sharp order y^-2.
- Leading coefficient grows quadratically in n; false-RH renewal may escape through degree. Remaining core is degree-proper common arithmetic budget. Summable degree weights are insufficient unless compensated by event growth.

Verification:
- direct Lean checks pass;
- targeted build of vacuum-free recession module passes;
- capstones use only propext, Classical.choice, Quot.sound;
- lint new modules clean/reachable, whole gate fails on unrelated concurrent unreachable Maynard/Sieve, Deninger, Suzuki modules;
- no computations or forbidden declarations.
