# Static local complexity master goal

- Goal: unconditionally prove Brown–Susskind growth–plateau–recurrence law for ordinary time-independent fixed-local Hamiltonians, plus permanent non-Haar locality witness.
- Master card: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.
- O4 robust state no-shortcuts remains central open core; no Lean until paper proof closes. User forbids subagents.
- Exact O4 target: aggregate annular shortcut-locus bound (O4.3i), equivalently quenched (O4.3). Fixed circuit, moment, design, spreading, and simulator lower bounds do not count.
- Primary-source correction 2026-08-02: Brown–Freedman–Lin–Susskind Nature 2023 conjectures emergent long-distance metric universality and an approximately exponential critical penalty schedule. It does NOT state a numbered conjecture that typical fixed-local H directions avoid directional cut loci exponentially long. O4 is a new directional strengthening motivated by that programme; master card attribution corrected in four places.
- 2026 Zlokapa–Allen–Harrow simulation lower bound does not cross O4: all-input channel; late-time factor uses fresh disjoint blocks, or a static system whose size/description grows with time.
- Hostile reset 2026-08-02: replica/cut-rank/cavity identities (O4.12q–z16) lose at Hamiltonian-dependent circuit selector. Planar-renormalized conjecture has no positive selector-aware inequality and is retired as evidence of O4 progress.
- Paper-proved quantized-witness bridge (O4.3j–n): any positive-probability robust O4 lower bound at time t yields rational fixed-q H with O(log(Btm/epsilon)) coefficient bits and same gate lower bound at half resolution. At t=exp(alpha n), this is polynomial-bit local H with robust exponential nonuniform endpoint complexity.
- RH orientation–transgression transfer audit (O4.3o–r): useful only as a no-go. Product projectors |0>,|1>,|+>,|+i> prepared in O(n) gates span Hermitian space; their differences span traceless operators. Any linear observable insensitive to adaptive choice among them factors through trace and is constant on all density matrices. Thus labels must survive a nonlinear/relative construction before scalarization. RH Green primitive does not supply circuit-boundary calibration or O4.
- SOTA audit of fixed-q eigenvector-universality route: no rigorous fixed-q Pauli/SYK theorem was found at strength needed for Haar-scale fixed-target anti-concentration. Wigner/band eigenvector universality does not transfer because fixed-q Pauli/SYK ensembles have only poly(n) Gaussian coefficients and strongly correlated matrix entries. Eigenvector universality alone would also be insufficient without joint phase nonresonance.
- Actual missing knowledge: natural robust exponential quantum state/unitary circuit lower bound for one finitely described static local Hamiltonian endpoint, then positive-density/quenched upgrade. Static ensemble entropy is O(m log t); ballistic complexity requires deterministic logical-depth/seed expansion.
- Target-independent recurrence-removal route is impossible: if `F_t` is
  `L_t`-Lipschitz and a shortcut centre maps exactly to a permitted target,
  its radius `epsilon/(2L_t)` parameter ball lies in that target cap.  Any
  common exceptional set leaving fixed-target mass `h_t` must absorb at least
  `rho_0 v_m r^m-h_t` per disjoint shortcut ball.  With `L_t=O(t)`, this is
  `Omega(t^-m)`, far above Haar cap mass.  Thus “common recurrence mass”
  equals the aggregate shortcut-locus problem and a circuit union is circular.
- Correct selector-aware invariant: fixed-radius annular packing number of the
  complete radial shortcut locus.  Across small error/budget margins,
  Duhamel robustness makes packing deficit and O4 annular volume deficit
  equivalent.  Direct packing bound (O4.3t), not fixed-target Haar
  anti-concentration, is the irreducible frontier.
- Hellinger-Hodge-Green audit: an `m`-parameter locally Lipschitz endpoint
  law on `CP^(D-1)` is supported on Hausdorff dimension at most `m`; when
  `m<2D-2` it is mutually singular with Haar, has Hellinger affinity zero,
  and TV distance one at every fixed time.  Thus no positive-mass Haar-bulk
  decomposition can exist for fixed-q static ensembles.  The Riemann paper
  only reinforces labels-before-scalarization; its linear Green/Hodge maps
  do not control the nonlinear selector.  Its “Quantum recurrence” entry is
  a two-state Gibbs purity limit, not an orbit recurrence theorem.
- O3 semantic correction: the existing `Omega(2^n/poly)` Choi lower bound is
  on 2n qubits, hence not near-maximal unrestricted state complexity there.
  New paper proof repairs this.  Stabilizer 2-design averaging selects one
  fixed poly-preparable n-qubit input with spectral collision `<=K/D` outside
  Hamiltonian mass `2/K`.  Heavy/light truncation plus an 8-direction
  Steinhaus-Hoeffding bound gives every fixed target cap mass
  `<=8 exp(-(1-eps^2)^2 D/(64K))`, surviving the circuit union to
  `Omega(D/(K log M))`.
- Stronger explicit-product repair: abstract compact orbit-frame law says a
  conjugation-invariant D-dimensional Hamiltonian ensemble has expected
  spectral collision `<=D/R` at fixed `psi0` when
  `span{(g psi0)^tensor2}` is an irreducible carrier of dimension R.  For the
  Fock vacuum in half-spin `Spin(2m)`, `D=2^(m-1)` and
  `R=binom(2m,m)/2`, so `D^2/R<=sqrt(m)`.  The isotropic SYK-q plus quadratic
  ensemble is Spin-invariant and has simple spectrum a.s. via a quadratic
  nonzero-discriminant witness.  It therefore has an explicit product-vacuum
  plateau `Omega(D/(L sqrt(m) log M))` with probability `1-1/L`, avoiding
  eigenvector universality and Choi dimension loss.
- Fermionic O2 is paper-closed for isotropic two-plus-four-Majorana H.  In a
  parity basis, degree<=2 diagonal Ising energies isolate any chosen
  Hamming-two edge; a quadratic Majorana flip and transverse diagonal
  parameter produce a square-root loop swapping exactly that edge.  The
  parity Hamming-two graph is connected, so edge loops give full
  `S_(2^(m-1))` monodromy.  Symmetric standard-representation rigidity then
  makes all projective rational gap relations measure-zero for the
  full-density Gaussian law.  Thus the Spin product-vacuum cap bound transfers
  to completed physical time.
- No Lean processes were started in this route.
