# CCM-FU: exact transverse compensation for a reversed head

- **Type:** [BRIDGE], THEOREM (Lean).
- **Parent:** [complete reserve-extension induction](../1-in-progress/ccm-fu-reserve-extension-induction.md).
- **Scope:** Exact local source criterion with stated orientation hypotheses. Choice of a suitable prime, complete ordering, the uniform signed bound and RH remain open.

Write `A_R` for the literal retained fibre after removing its Möbius parity.
Assume `h=A_empty<=0` and every nonempty retained coordinate is nonnegative.
For an active prime q, retain every nonempty q-free label R and put

`a=A_{q}`, `x_R=A_R`, `y_R=A_(R+q)`,

`T=sum_R (x_R-y_R)^2`, `C=sum_R x_R*y_R`.

Assume also `y_R<=x_R` for every one of those labels. The actual merger
preserves the nonpositive head and all nonempty orientations. Its complete
good/defect energy decomposition is

`G_before=a^2+T+2C`, `D_before=h^2`,

`G_after=T`, `D_after=(h-a)^2`.

Consequently the geometric certificate `Phi=Q+2sqrt(G)sqrt(D)` contracts
exactly when

`a*sqrt(T)<=C`.

Indeed its nonnegative square root changes from
`-h+sqrt(a^2+T+2C)` to `-h+a+sqrt(T)`. Cancel `-h` and square the remaining
nonnegative sides. This retains every transverse label and shows that the
negative head's magnitude does not enter this local comparison.

The five-coordinate paper comparison exposed by the logarithmic-slack
diagnostic is a special case: its transverse residual is
`T=(b-c)^2+z^2` and overlap is `C=b*c`. No numerical coordinate value was
used in this formal proof. The numerical cutoff-17 witness itself has not
been promoted to a Lean certificate.

The hypotheses are not proved for an exhaustive sequence of source states.
In particular, this contraction criterion cannot replace the original
reserve-extension claim, which permits local increases paid by unused
budget. It identifies one exact compensation mechanism inside that problem.

The module is `RHTower/MobiusDivisorHeadDefectCompensation.lean`. Its public
theorems are `mobiusDivisorParityRadius_sq`,
`mobiusDivisorHeadDefect_insert_preserves`, and
`mobiusDivisorHeadDefect_compensation_iff`.

Scratch and exact-file `lake env lean` checks pass. Only the new module's
olean was emitted. Its seven new public declarations were axiom-audited
once: only `propext`, `Classical.choice`, and `Quot.sound`. The module is
wired into `RHTower.lean`; the index was refreshed and formal lint passed.
Lake's module-only `--no-build` preflight rejected stale dependency traces
without compiling anything; a dependency-rebuilding Lake audit was not run.
No full or umbrella build was run.
