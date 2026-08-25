# Exact theta-mirror Teukolsky scattering (2026-08-25)

New module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyThetaMirrorScattering.lean`, imported by `formal/GaloisForLFunctions/RHTower.lean`.

Let `R q` be Xi functional reflection, `a = Re q`, `delta = a-1/2`, `OmegaF = -i(4n+5/2)`, and use the reflected-real-pair BM spectral point `z_q`.

New exact results:
- Joint BM channel `(Omega_q,Q_q)` has reflection defects `Omega_q-Omega_Rq=2i delta` and `Q_q-Q_Rq=4 delta`; joint labels coincide iff `a=1/2`.
- Cross-lacing: `Omega_q = QNMPlus(2n,z_q)` and `Omega_Rq = QNMMinus(2n+1,z_q)`.
- Exact reflected radial shifts: `A_R=B+1`, `B_R=A-1`.
- Fix physical minus-Jost denominator `D_q=1/Gamma(B_q)`. Gamma recurrence forces numerator `N_q=(A_q-1)/Gamma(A_q)`, with exact swap `N_R=D_q`, `D_R=N_q`.
- Therefore `S_q=N_q/D_q` obeys `S_R=S_q^{-1}` and Cayley `C_q=(N_q-D_q)/(N_q+D_q)` is reflection odd.
- Tilted incidence is a projective scattering zero/pole pair: at `Omega_q`, `N=0,D!=0`; at `Omega_Rq`, `D=0,N!=0`. Cayley values are `-1,+1`.
- On line, `N=D` for all frequency, hence `C=0`; specifically `C_q(Omega_q)=0 iff Re q=1/2`.
- Exact local node: `(A+2n)(B+2n+1)=-(1/4)(w^2+delta^2)` at `omega=OmegaF+w`.

Interpretation:
- This realizes a theta-specific equivariant scattering/family-index object. Off-line reflection forces two distinct joint angular-frequency labels and swaps zero/pole helicities.
- It does not eliminate off-line fibers. A scalar determinant descends and paired edge modes are allowed. To force RH, nonlinear Einstein-Teukolsky horizon dynamics must prove a gauge-invariant nonzero adjoint cubic projection or strict absorption law that prevents the perfect `C=±1` pair without mixing.
- The full open amplitude is `A_12->M=<Psi_M^dagger,-delta^2 G[h1,h2]>_sympl`; generic KMS/passivity/CCR cannot prove its sign/nonvanishing.

Verification:
- Target module passes `lake env lean`.
- All new declarations use only `[propext, Classical.choice, Quot.sound]`.
- Lint reports only pre-existing unreachable modules `SuzukiShiftedXiBoundaryFactorization` and `HTGeometry.SecondOrderConstraintDescent`; new module is reachable.
- Generated scratch files and module oleans cleaned. No git used.

Related prior memory: `mem:research/hawking_teukolsky_mediator_pole_multiplicity_2026_08_25`.