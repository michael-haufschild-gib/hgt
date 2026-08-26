# BM nonlinear radiation kernel and helicity admission (2026-08-26)

Formalized in `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNonlinearRadiationKernel.lean`, imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Exact result at first nonlinear (quadratic/second-harmonic) order

For BM mode q, complete gauge-fixed horizon-plus-normalizable-boundary radiation is
[
R_q(d,m)=(G_q d,T_qG_qd,G_qm,T_qG_qm).
]
The existing corpus proves (G_q\ne0). Hence (R_q) is injective and (ker R_q=\bot).

For the full-Einstein second-harmonic source ((C_qA^2,m)), the exact zero fibre is
[
R_q(C_qA^2,m)=0 \iff A=0\land m=0.
]
Therefore actual opposite-helicity radiation and its squared-norm flux vanish iff the opposite-helicity source coordinate itself vanishes. Critical-line placement does not kill a nonzero actual opposite-helicity channel.

Full tagged reflected/conjugated FE--Schwarz radiation also has trivial zero fibre.

## Untagged fold classification

Define folded orthogonal radiation by subtracting reflected and conjugated records:
[
F_q^\perp(m_r,m_s)=R_r(0,m_r)-R_s(0,m_s).
]
A nonzero dark kernel exists iff (T_r=T_s). Folded direct radiation has the identical criterion. Thus
[
\mathrm{Dark}^\perp(q)\iff T_r=T_s\iff\mathrm{Dark}^{\parallel}(q).
]
Critical-line copy coincidence implies both dark kernels, but the converse is the open transfer-collision rigidity problem (T_r=T_s\Rightarrow\Re\rho(q)=1/2). Even if proved, it is not orthogonal-helicity-specific.

## Hostile result

Falsified conjecture: actual orthogonal helicity is a hidden/lost channel supplying its own nonlocal critical-line admission law. Horizon coordinate (G_qm) detects every (m\ne0). Existing corpus “orthogonal helicity flux” ((\Im\lambda_q)^2\|\psi\|^2) is a tilt-weighted total norm, not the norm of the actual opposite-helicity radiation channel.

## Scope

This is the exact kernel at the constructed first nonlinear Einstein--Teukolsky order. Literature/corpus do not construct a fully all-order nonlinear Einstein scattering map, so no all-order kernel claim was made.

## Verification

Targeted compile passed:
`lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNonlinearRadiationKernel.lean`.

Every new declaration's `#print axioms` output was only `[propext, Classical.choice, Quot.sound]`.

Formal lint remained red only on pre-existing/concurrent unreachable modules; this module is reachable through the umbrella import. No endpoint ledger, route ledger, pipeline card, or git state was touched.