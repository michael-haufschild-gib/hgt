# FZZ-P/Deninger information--Ward transmutation (HC38, 2026-08-28)

Formalized
`GaloisForLFunctions.RHTower.FZZCigarParityDeningerInformationWardTransmutation`.

HC37's nonlinear Fermi information force factors as `(2 sigma-1) C(sigma)` with a strictly
positive piecewise source multiplier `C` throughout the open strip. For every Xi divisor copy,
the cup-traced Deninger reflect-gauge commutator is exactly `1-2 Re(q)`. Each divisor-flow
eigenvalue is also a literal source-first FZZ parity-Mellin mode, and on that mode the FZZ force is
exactly `-C` times the Deninger Ward charge. Per-copy information equilibrium is therefore
equivalent to reflect-gauge equivariance; universal equilibrium is equivalent to RH.

New bounded-audit route knowledge: FZZ nonlinear source orientation and Deninger displacement Ward
mechanics have one shared oriented RH charge, not two independent gaps. Strict positivity proves
translation loses neither sign nor zeros. Remaining open core is actual source/dynamical
cancellation of this shared charge; changing detector language cannot supply it.

Verification: direct Lean check passed; targeted module build passed (8823 jobs); all 11 public
theorems audited with only `propext`, `Classical.choice`, `Quot.sound`; lint had no HC38 finding;
module wired into RHTower umbrella without full umbrella build. Frontier map remained read-only.
