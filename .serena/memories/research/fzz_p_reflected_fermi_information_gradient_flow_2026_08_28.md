# FZZ-P reflected Fermi information gradient flow (HC37, 2026-08-28)

Formalized
`GaloisForLFunctions.RHTower.FZZCigarParityReflectedFermiInformationGradientFlow`.

For literal Fermi--Mellin log mean `m` and variance `V`, define reflected work
`W(sigma)=(2*sigma-1)*(m(sigma)-m(1-sigma))` and force
`F(sigma)=2*(m(sigma)-m(1-sigma))+(2*sigma-1)*(V(sigma)+V(1-sigma))`.
The module proves `W'=F`; work is reflected Jeffreys divergence; `F` is negative left of `1/2`,
positive right, and zero exactly at center; velocity `-F` is strictly inward; and work dissipation is
strictly negative away from center. A source-first FZZ Mellin mode is stationary exactly on the
critical line. Universal mode stationarity is equivalent to FZZ Mellin completeness and RH.

New bounded-audit route knowledge: literal nonlinear/nonlocal source geometry supplies global
center orientation without reporter tuning. Remaining RH core is not orientation but a genuine
source/physical Ward law forcing divisor modes to be stationary (or an equivalent landing theorem).
Do not confuse the defined stationarity endpoint with proof of that Ward law.

Verification: direct Lean check passed; targeted module build passed (8797 jobs); all 12 audited
public endpoints use only `propext`, `Classical.choice`, `Quot.sound`; lint had no HC37 finding;
module wired into RHTower umbrella without building full umbrella. Frontier map remained read-only.
