# HC43 HB phase-sensitive chiral Ward amplitude (2026-08-28)

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude.lean`.
Formal card: `docs/drafts/pipeline/3-formalized/hb-phase-sensitive-chiral-ward-amplitude.md`.

Corpus-led discovery: the BM orthogonal-helicity coefficient has exact complex factorization
`mix(q) = I * Im(rho_q) * D(q)`, where `D(q)` is the Deninger reflect-gauge Ward charge `1 - 2 Re(rho_q)`.
The actual nonlinear mixed-horizon projection is therefore
`projection = K_HB(amplitude,q) * D(q)`, with
`K_HB = I*Im(rho)*Green(q)*carrier(amplitude,xiSpectralPoint q)`.
For nonzero amplitude, every factor is nonzero. Calibration by `K_HB` recovers the signed real Ward coordinate exactly, including strict left/right orientation. Exact complex ratios connect the same projection to FZZ information force, every PW-B recoil-grade imbalance, and actual RBH multiplicity-leading imbalance.

Universal cancellation for fixed seed `(amplitude,orthogonalMixing)=(1,0)` is equivalent to `RiemannHypothesis`. This closes HC42's phase/orientation loss but is a receiver, not a producer. Next hard core: derive source-native zero-amplitude conservation/solvability, or prove a sharp obstruction and extract its strongest positive survivor.

Audit: direct `lake env lean` passed; target-only `lake build` passed (12,003 jobs); all 16 public theorem axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`; wired into `RHTower.lean`; global lint had only pre-existing unrelated unreachable modules. Frontier map remained read-only.

Bounded literature audit through 2026-08-28 found neighboring BM topological-black-hole QNM/stability, black-hole Riemann-zero, Connes scaling-Hamiltonian, nonlinear mode-excitation, and complex-bilinear Teukolsky-current work, but no exact BM/Deninger signed-amplitude identity or FZZ/PW/RBH amplitude transmutation.