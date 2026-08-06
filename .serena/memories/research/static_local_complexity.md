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
- Hellinger-Hodge-Green audit: homogeneity makes the all-time theorem
  stronger without adding a time dimension.  Since `tH(x)=H(tx)`, the full
  all-time set equals `{[exp(-iH(y)) psi0] : y in R^m}` and has Hausdorff
  dimension at most `m`; if `m<2D-2`, it is Haar-null yet supports every
  coefficient/time law.  Hence one time-independent measurable separator
  gives Hellinger affinity zero and TV distance one against Haar for every
  static-local endpoint.  The same holds in `PU(D)` when `m<D^2-1`.  This closes
  permanent non-Haar distinguishability only measure-theoretically: the
  indicator need not be efficient or physically measurable.  The Riemann
  paper still supplies no nonlinear selector/shortcut packing bound; its
  “Quantum recurrence” entry is a two-state Gibbs purity limit, not an orbit
  recurrence theorem.
- Updated Hellinger-Hodge-Green re-audit: its uniform-capacity selector uses
  real Cartan growth `exp(c(Re rho-1/2))`; Hermitian quantum evolution has
  only unit-modulus compact characters, so this mechanism cannot detect
  shortcuts.  Its strict-reduction law does transfer as a quantum no-go: for
  any bounded `L : ell^1(W) -> Hilbert` on `N` circuit labels, some signed
  packet has input norm `N` and output norm at most `sqrt(N)||L||`; hence any
  lower modulus is at most `||L||/sqrt(N)`.  Existing Lean theorems:
  `exists_lpOne_signed_packet_hilbert_bound` and
  `lpOne_to_innerProduct_not_boundedBelow`.  Common linear reporting cannot
  replace O4's nonlinear aggregate shortcut-packing bound.
- Lean-proved Hellinger survivor: retain `H` as resolved base label.  For
  endpoint density `p_H`, circuit density `q_(H,C)`, and positive `f_H`, a
  fibrewise bound `int q_(H,C)/f_H <= r(H)` for every circuit plus selected
  affinity `>=alpha` on event `A` implies
  `P(A) <= (E int f_H p_H + E r)/(2 alpha)`.  Exact continuum theorem:
  `resolvedHellinger_selectorRemoval` in
  `formal/GaloisForLFunctions/HTGeometry/ResolvedHellingerSelectorRemoval.lean`;
  standard axioms only, wired into `HTGeometry`.  It absorbs selector without
  circuit union or `sup`/expectation swap and permits `f(H,z)` from a
  transported-parent energy barrier.  It does not prove O4; missing knowledge
  remains an independently controlled exponential-rate barrier.  Card:
  `docs/drafts/pipeline/3-formalized/resolved-hellinger-selector-removal-law.md`.
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
- New paper-proved exact-complexity boundary:
  `docs/drafts/pipeline/2-fully-proven/algebraic-two-local-instant-exact-complexity.md`.
  Full two-local monodromy plus Hilbert irreducibility yields a rational
  two-local H with `S_D` Galois group and cyclic product input.  Its spectral
  Q-rank is `D-1`; the already Lean-proved finite Lindemann--Weierstrass
  theorem and Jia--Wolf's trdeg circuit bound give exact state complexity
  at least `(D-1)/16` at every nonzero algebraic time.  Semialgebraicity of
  bounded-gate states plus one-dimensional `R_an` implies subthreshold exact
  times are locally finite.  This proves exact complexity jumps instantly
  and is physically invalid as Brown growth.  It sharpens O4 to quantitative,
  fixed-radius separation from low-gate semialgebraic sets; qualitative
  transcendence cannot supply that radius.
- No Lean processes were started in this route.
- Finite Hellinger minimax wall (paper-proved, Lean pending): for positive endpoint probability `p` and finite shortcut observation laws `q_c`, the optimal common reciprocal certificate satisfies `inf_(f>0) [sum p_i f_i + max_c sum q_(c,i)/f_i] = 2 max_(lambda in Delta(C)) Aff(p, sum_c lambda_c q_c)`. Therefore the certificate is useful only against the convex hull of all shortcut laws. If that convex hull contains `p`—in particular for one projective measurement once basis-state targets are within budget—the bound is trivial. Any viable route needs coherent/replica observations with a quantitative shortcut-convex-hull deficit at the full growth rate. Recorded as (O4.H7)–(O4.H8) in master card.
- July-2026 SOTA audit: Al-Ghattas--Gamarnik arXiv:2607.14384 controls a Gaussian residual uniformly after the ancilla-assisted shallow-circuit supremum, using marginal subtraction and pruned backward cones. It does not transfer to autonomous growth: `Tr(H rho_t)=Tr(H rho_0)`, every `f(H)` witness is conserved, a fixed commutator current is a bounded signed coboundary, and backward-support variance reduction ends at depth `Theta(log n)`. Master card records (O4.G1)--(O4.G4). Positive survivor: any Gaussian-supremum O4 route needs a disorder-linear, nonconserved, non-coboundary endpoint witness whose residual keeps contracting after light-cone saturation.
- Finite Liouvillian Hodge--Green bridge: every transition vector is its zero-gap stationary part plus an exact spectral-Liouvillian coboundary. Lean capstone `transitionGap_hodgeGreen_decomposition` in `formal/GaloisForLFunctions/HTGeometry/FiniteLiouvillianHodgeGreenLaw.lean`, wired and axiom-audited. For observables this gives `W=Pi_H W+i[H,A]`; hence every fixed linear autonomous signal is conserved plus a time coboundary. This closes fixed linear witnesses only; `||A||` may blow up with inverse gaps, and O4 still needs time-dependent/nonlinear/replica shortcut control.
- Two-replica local-singlet synchronization is paper-closed.  For one edge,
  the nine two-body Pauli collective commutators have Casimir spectrum
  `{0,0,48,80}` on the local invariant basis and kernel `span{uu,ff}`.  On a
  connected graph, the global local-singlet kernel is exactly identity/global
  swap.  This does not imply pencil fullness: the Hermitian matrices
  `E13+E31,E23+E32` have positive Casimir and common kernel zero but shrink a
  plane to a line.  Exact next gate is Pauli Hall expansion for every subspace
  on the global-permutation quotient.  Card:
  `docs/drafts/pipeline/3-formalized/two-replica-local-singlet-synchronization-law.md`.
- Hellinger--Hodge--Green cross-audit against sharpened O4: its recurrence
  section is genuinely useful for the required target-independent split.
  `finiteSpectralSurvivalFidelityMean_eq_collisionMass_add_remainder` isolates
  exact replica collision mass, and
  `norm_fidelityReplicaFiniteWindowRemainder_le` bounds the complement by
  `min(1,(T delta)^(-1))` with constant one independent of dimension/order.
  Then `resolvedHellinger_selectorRemoval` can absorb the adaptive best
  short-circuit target on the complement, so recurrence mass is paid once.
  Missing input remains a target-uniform reciprocal certificate at the full
  growth rate.  Hodge--Green/common-kernel control cannot prove Hall expansion,
  an all-subspaces/exterior-degree property.  Promising exact algebraic route:
  combine `tightOperatorFamily_subspace_finrank` with a bi-tight replica-Pauli
  scaling; Parseval--Bessel then implies Hall immediately.  One-replica
  scaling already realizes this.  Growing-replica scaling/rank-nondecrease is
  still open.
- 2026-08-04 two-replica synchronization is fully formalized and moved to Stage 3.  The wired module `formal/GaloisForLFunctions/HTGeometry/TwoReplicaLocalSingletSynchronization.lean` now proves the physical identity/swap change of coordinates, exact intertwining with the nine-generator edge double-commutator Casimir, slice-wise tensor edge action, mismatch kernel, and the finite positive master-constraint capstone `physicalState_twoReplicaGraphMasterConstraint_iff`: on every finite nonempty preconnected graph only all-identity/all-swap Hilbert coefficient modes survive.  The module passes `lake env lean` without warnings, contains no forbidden declarations, and all three new capstones use only `propext/Classical.choice/Quot.sound`.  Synchronization is closed; growing-replica Pauli Hall expansion/bi-tight scaling remains the first algebraic frontier.
- 2026-08-06 direct-net adaptive static-Choi shortcut law fully formalized. Direct target overlap removes anchor loss, permits every radius `<1`, and under maximal projective rank gives uniform order-r collision `<= r! d^-r` for arbitrary full `d^2` Choi targets. Gaussian/uniform windows cover finite padded circuit dictionaries and arbitrary uncountable adaptive target classes via any finite metric net; selector measurability is unnecessary. Modules: `HTGeometry/SubprobabilityPhaseTwistedReplicaShortcutActionLaw.lean`, `RHTower/DirectAdaptiveStaticChoiShortcutActionLaw.lean`. Module build green; axioms standard. This closes finite-window selector/continuous-family resolution only. O4 remains fixed-time quenched coefficient-space anti-concentration; intrinsic action resolution may collapse.
