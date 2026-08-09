# Mass-shifted spectral face: Krein/Volterra structure and exact no-gos (2026-08-09)

## Narrow use of docs/notes.md
Two ideas were productive: (1) a tied moment-null relation is a hidden affine extension class, whose decisive datum lives one rung above the constrained moment block; (2) sign must be source-conditioned joint realizability, not a scalar inequality on marginal moment data. Tate-fracture/CLG language currently has no typed connector to the Xi kernel and supplies no sign theorem.

## Formalized structural theorem
For a tied-power polynomial P with coefficients c_0..c_n and signed Hankel form [u,v]_s, the null relations say [P,X^r]_s=0 for r=0..n. In particular [P,P]_s=0. The endpoint remainder/crossing is [P,XP]_s, i.e. the first Krein crossing of the null vector. In the Xi carrier model, factorial-normalized Volterra primitives F_r satisfy the analogous flag: integrals of F_0..F_n vanish and the crossing is c_n^{-1} times the integral of F_{n+1}. This identifies the missing theorem as positive Krein crossing type / next-rung incidence for the actual Euler–Gamma source, not generic moment positivity.

Lean:
- formal/GaloisForLFunctions/HTGeometry/FiniteHankelBoundaryKreinCrossing.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryKreinCrossing.lean
Capstone: RHTower.xiShiftedHankelBoundary_kreinVolterraFlag

## Exact no-gos
1. Sector/radius tied-power clouds:
Z+={11,9,10+i,10-i}, Z-={11+i,9+i,9-i,11-i}; same (s0,s1,s2)=(40,400,4000), kernel (-10,1), crossings +4 and -16. Scaling preserves sector/radius and opposite signs.
2. Positive carrier factorial moments:
mu+=(16/17)delta_(3/4)+(1/17)delta_5 and mu-=(4/5)delta_(1/2)+(1/5)delta_3; same factorial-normalized s0=s1=s2=1; crossings 7/24 and -1/12.
3. Global scalar budget no-go:
Three copies of each cloud scaled by 1/2880 have common s0=1/24, s1=1/6912, s2=1/1990656 and null polynomial X-1/288; energies E+=1/1382400 and E-=1/691200, both <1/150000; exact Xi scalar windows 1/25<s0<29/625 and s1<1/5000; crossings +1/5733089280000 and -1/1433272320000. Exact conjugation, sector/radius and Möbius transport also hold. Therefore all current scalar mass/first-moment/energy budgets plus geometry do not determine orientation.

Lean:
- HTGeometry/TiedPowerSectorOrientationNoGo.lean
- HTGeometry/TiedPowerEndpointOrientationNoGo.lean
- HTGeometry/FactorialPositiveCarrierOrientationNoGo.lean
- HTGeometry/TiedPowerGlobalBudgetOrientationNoGo.lean

## Route implication
Any successful §9.3 theorem must use a mixed Euler–Gamma/null-flag incidence invariant capable of distinguishing source-conditioned joint realizability. More scalar budgets cannot close the route. RH remains open.