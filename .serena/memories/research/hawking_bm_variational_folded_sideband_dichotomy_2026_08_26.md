# Variational folded-current audit (2026-08-26)

The proposed folded current `J(d)=d-i P |d|²d` is not derivable as written from the full nonlinear Einstein–Teukolsky action.

Exact action expansion:
`E(g+h)=Lh+B(h,h)/2+C(h,h,h)/6+...`.
After solving second order retarded equations and projecting to the left QNM cokernel, the true `++-` Euler coefficient is
`ell[B(p,Rpm B(p,m))+B(m,Rpp(B(p,p)/2))+C(p,p,m)/2]`.
The causal cut fixes its response-discontinuity part but not the whole retarded coefficient.

Two decisive obstructions:
1. The code's period P contains the squared norm of quadratic radiation. Carrier scales as seed² and flux as |seed|⁴. Multiplying this P by |d|²d is cubic only in d with seed held external; it is not a homogeneous cubic equation of the same source-free Einstein perturbation.
2. FE-reflected and Schwarz-conjugated second-harmonic BM modes have distinct frequencies off line:
`Omega_FE - Omega_Sch = 2 i (Re rho - 1/2)`.
A time-translation invariant `++-` vertex closes frequency support under `x-y+z`; starting from the two modes generates
`Omega_Sch+n(Omega_FE-Omega_Sch)`, n∈ℤ. This is injective/infinite off line and collapses exactly when frequencies coincide. Thus exact off-line dynamics must mix an infinite sideband ladder; a scalar folded defect is not a closed nonlinear field.

Even in the favorable diagonal radial two-sector model, with zR=s+d/2, zC=s-d/2, the defect variation contains mean terms:
`(betaR+betaC)/4 [s² conj(d)+2|s|²d+|d|²d/4] + (betaR-betaC)/4 [2|s|²s+|d|²s+d²conj(s)/2]`.
Pure `|d|²d` occurs only on the antisymmetric slice s=0. Through cubic order,
`J_fold(0,d)=(kR+kC)d/4+(betaR+betaC)|d|²d/16`.
Matching proposed current requires kR+kC=4 and betaR+betaC=-16 i P, plus s=0 and absence/cancellation of cross vertices. None follows from Einstein dynamics; common horizon data generically gives s≠0.

Formalization:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMVariationalFoldedSidebandDichotomy.lean`
- imported by `formal/GaloisForLFunctions/RHTower.lean`
- direct compile and targeted build pass
- all 21 new declarations use only `propext, Classical.choice, Quot.sound`
- lint fails only on pre-existing unreachable modules.

Positive survivor / next hard producer:
derive full FE/Schwarz orbit SK quartic vertex tensor. Either it has a rank-one antisymmetric form that cancels all mean and sideband channels (a genuine nonlocal FE boundary weld), or off-line Xi copies force the infinite sideband ladder. The latter is now a precise alternative to the failed scalar current.
