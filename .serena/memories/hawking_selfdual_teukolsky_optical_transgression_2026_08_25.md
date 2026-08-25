New module `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingSelfDualTeukolskyOpticalTransgression.lean`, imported by `RHTower.lean`; HRTV endpoint updated in `docs/reports/endpoints.md`.

Novel exact bridge: for Xi divisor q, selfdual response defect D and susceptibility S satisfy `Im(lambda_quad) * S = -64 * Im(rho) * D`, where `lambda_quad = rho(1-rho)` is de-aliased quadratic Teukolsky angular Casimir. Conjugate scalar/vector parity responses split in helicity basis into direct coefficient `Re(lambda)` and off-diagonal coefficient `i Im(lambda)`. Its norm-square is `Im(lambda)^2`.

Gauge-fixed angular optical Pythagoras: for symmetric angular operator A, `||(A-lambda)psi||^2 = ||(A-Re lambda)psi||^2 + E_mix`. Division-free incidence: `S^2 E_mix = 4096 Im(rho)^2 D^2 ||psi||^2`; for nonzero psi, `E_mix=0 iff Re(rho)=1/2`.

Global theorem: for any linear radiation map R into horizon-plus-boundary flux Hilbert space satisfying optical angular symmetry `<R psi,R A psi>=<R A psi,R psi>`, same decomposition holds after R. No isometry/losslessness or fixed greybody normalization is needed. Global mixing flux nonnegative and vanishes iff critical line when `R psi != 0`.

Exact BM radial incidence: second harmonic frequency `2 omega_0`; radial hypergeometric A equals `-(rho+2)/4`, whose real part lies in (-3/4,-1/2) on Xi strip, so reciprocal-Gamma Jost factor is never zero. Nonzero selfdual principal carrier therefore gives nonzero exact chiral boundary response in every Xi sector.

Failed conjectures: complex QNM residue is not positive flux; half-decay resonant pump requires external/off-shell driving; bare Green/Jost amplitude has nontrivial Gamma transfer; completed Eisenstein FE identifies partner global profile, so local mismatch cannot simply be declared physical flux. Surviving open core: classify full non-selfdual same-grade second-order Einstein/Teukolsky source on gauge quotient and prove actual radiation map's optical Gram preserves angular grading; exclude remaining gauge/mass/spin/threshold kernels beyond principal chiral BM response.

Verification: direct Lean check passed; all created theorem axiom audits only `[propext, Classical.choice, Quot.sound]`; lint reports only pre-existing unreachable owned modules. No git. Scratch files removed.