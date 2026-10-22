# Graded self-dual completed Bost--Connes system: the functional equation as an operator-algebra duality

- **ID:** `self-dual-completed-bost-connes-system`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** collapse theorem and dihedral correction of
  `../../../3-formalized/not_new_scientific_knowledge/born-temperature-kms-factor-type-duality.md` §8;
  corpus review 2026-07-12
- **Statement:** `[CONJECTURE]` There exists a **graded** C*-dynamical system whose signed
  partition function is the half-dilated completed zeta
  `Z(beta) = Lambda(beta/2) = pi^(-beta/4) Gamma(beta/4) zeta(beta/2)` — discrete prime modes with
  Hamiltonian `log sqrt(n)` welded to one continuous archimedean scale mode — such that
  `beta -> 2-beta` is a duality of the system itself (an operation on its algebra/dynamics), not an
  identity of analytically continued scalars, with fixed locus `beta = 1`.

## Goal

The parent card proved that the ordinary Bost--Connes system cannot carry the functional equation
(symmetry group `R_+ x Zhat*` has no `beta -> 2-beta` element; the Gamma-completion is
Born-invisible; the reflected-sector duality at `xi` zeros collapses to RH verbatim). The residue
is exact: a native FE needs a *different* system in which the reflection acts on the off-diagonal
algebra. Constructing it would make the completed functional equation a Kramers--Wannier-type
operator duality, with the critical line as the self-dual locus of a genuine statistical system
rather than a label. Non-circularity transfers unchanged: `xi`, its divisor, and
square-summability assumptions must not enter the construction.

## Constraints inherited from the corpus (review 2026-07-12)

1. **Dihedral no-go `[PROVED + Lean]`.** `Lambda(beta)` itself is NOT the target partition
   function: its scalar FE reflects about `1/2`, the Born reflection acts about `1`, and carrying
   both forces `1`-periodicity — excluded by the pole at `0` against regularity at `2`
   (`completedRiemannZeta_no_born_reflection`, `doubly_reflected_periodic`,
   `formal/GaloisForLFunctions/RHTower/CompletedBornReflectionNoGo.lean`). The unique Born-self-dual
   gauge is `Z(beta)=Lambda(beta/2)` (`completedRiemannZeta_half_dilated_born_reflection`), i.e.
   prime Hamiltonian `log sqrt(n)`.
2. **Grading is forced `[PROVED + Lean]`.** `Z(1) = Lambda(1/2) = -8 xi(1/2) < 0` real
   (`completedRiemannZeta_half_eq`, `completedRiemannZeta_half_neg`): the self-dual value is
   negative, so `Z` is a supertrace datum, never an ungraded Gibbs trace. The system must carry a
   `Z/2` grading; the duality is a duality of graded KMS structures.
3. **Pole geometry.** `Z(beta)=Lambda(beta/2)` has simple poles at both temperature ends
   `beta=0` and `beta=2` and is regular on `(0,2)`: the phase diagram to construct is
   pole--regular--pole, symmetric about the regular negative self-dual point `beta=1` — unlike bare
   Bost--Connes, whose single pole sits at the transition. What thermodynamic role a *boundary*
   pole pair plays (two ends of a temperature interval, exchanged by the duality) is part of the
   construction problem.
4. **Archimedean-only duality content `[PROVED in tree]`.** The reflection cocycle of `zeta` is
   the pure Gamma quotient `h(s)=Gammaℝ(s)/Gammaℝ(1-s)` with ZERO rate-lattice content
   (`ReflectionCocycleClass.lean`): the FE datum lives entirely in the archimedean cell, and the
   prime rate lattice is weld-inert under it. Together with the parent card's Born-invisibility,
   the demanded duality must act on the **archimedean off-diagonal** structure; it cannot be
   carried by the prime lattice or by any diagonal channel.
5. **III_1 robustness `[PROVED in tree, spectral face]`.** The rate group `<log p>` is dense in
   `R` (`SeamSpectrumDensity.lean`); any extension containing the prime rates keeps a gapless
   modular spectrum, so the high-temperature type `III_1` cannot be deformed away by adding the
   archimedean mode (also the R17/R32 no-gos: no discrete Frobenius; the archimedean component of
   the symmetry group is the connected flow `R_+`). The duality therefore relates a type-`III_1`
   phase to a type-I phase and **cannot be normal** off the fixed locus: the first deliverable is
   the categorical home of a non-normal (graded, possibly antilinear) exchange functor.
6. **Clock selection `[PROVED in tree]`.** In the seam framework (`SeamClockSelection.lean`) the
   Born reflection is the affine constraint with linear part `-1` on the temperature line — the
   `feObject` pattern, unique fixed clock at `1` — while the composition of the two reflections of
   the dihedral no-go is the unit shift, the `shiftObject` with NO clock. The conjectured system
   sits at the reflection vertex of this dihedral pair; the shift face is the classical
   `s -> s+1` difference structure of `Gamma`.
7. **Hypertranscendence status.** `zeta` is hypertranscendental in-tree
   (`hypertranscendental_riemannZeta`); `Gamma`'s Hölder theorem is the named in-tree frontier
   (`GammaDifferentialFE.lean` machinery). `[OPEN CORE]` Hypertranscendence of `Lambda` (equiv. of
   `xi`) is NOT decided by differential-field closure rules — `log Lambda' = psi`-part `+`
   `zeta'/zeta` is a sum of two HT elements — and is the missing certificate that the conjectured
   system's partition function has no finite algebraic-differential handle. Candidate machinery:
   the `HTGeometry` universal prime-log palettes (differential independence under arbitrary
   rational gauges, `UniversalConstraintOrientation.lean`) to force joint independence of the
   prime-log and digamma jets.
8. **Square-root gauge echoes `[BRIDGE, explore]`.** The forced Hamiltonian `log sqrt(n)` is the
   `m=2` rung of the formalized dilation tower (`mPart`, `MFreeTower.lean`;
   `dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt`, `SqrtCarrierCertificate.lean`: the square-dilated
   carrier IS the carrier at doubled argument), and RH-ladder level `1` is exactly the existence of
   an analytic `sqrt(xi)` on the half-plane (`rhLadder_one_iff_sqrt_rightHalf`). The graded
   self-dual system is conjecturally the thermal face of the `sqrt(xi)` Kummer rung: its grading
   operator should square to the trivial one the way `sqrt(xi)^2 = xi`.
9. **Archimedean mode realization `[CONJECTURE, concrete]`.** `Gammaℝ(beta) = 2 * integral over
   x>0 of x^beta e^(-pi x^2) dx/x`: the archimedean mode is the half-line scale variable with
   Gaussian weight and Hamiltonian `-log x`. The Gaussian is the unique Fourier-self-dual weight —
   the natural microscopic carrier of the reflection — and the tree's theta-cusp modules
   (`ThetaCuspReflection.lean`, `XiThetaSourceSeam.lean`) already formalize the reflected theta
   source this mode's second quantization would produce.

## Gates

- [x] 0 → 1 in-progress: the graded algebra carrying the archimedean mode is fixed (the ungraded
  Gaussian scale mode welded to the parity-graded `log sqrt(n)` system; the twisted module lives
  inside the same system — Approach step 3); the candidate duality map is written on generators
  (weight-one inversion on scale profiles, signed sector swap on the two-adic pair; scalar shadow
  and seed-level dynamics proven); kill tests re-run (the map is source-derived from the Gaussian
  and inversion, no `xi` input; it acts on profiles, not the Born diagonal); the exchange functor's
  shape is named (grading-odd involution on the doubled system) — its KMS-categorical realization
  is the open core below.
- [ ] 1 → 2 fully-proven: existence of the system, its graded KMS_beta classification, and the
  duality with fixed locus `beta=1` proved on paper; `[OPEN CORE]` `Lambda` hypertranscendence
  settled or explicitly bypassed.
- [ ] 2 → 3 formalized: partition-function weld and duality skeleton in Lean; operator content as
  explicit hypotheses (no axioms), extending `CompletedBornReflectionNoGo.lean`.
- [ ] 3 → 4 publication-ready: novelty audit against Connes--Consani archimedean/adelic
  constructions, graded/super KMS literature (Kastler, Jaffe--Lesniewski--Osterwalder chains), and
  lattice Kramers--Wannier duality.

## Approach

1. **Archimedean mode first — EXECUTED 2026-07-12, grading identified `[PROVED HERE + FORMALIZED]`**
   (`formal/GaloisForLFunctions/RHTower/BornEtaGrading.lean`, axiom-clean, lint green). The answer
   corrects the expectation: **the grading is not archimedean.** Findings:
   - The archimedean mode is **ungraded**: `Gammaℝ(beta/2)` is a strictly positive real on the
     whole strip (`Gammaℝ_real_strip_pos`, derived in-tree as `Lambda/zeta`, quotient of two
     negative reals), so its supertrace is its trace and carries no sign.
   - The grading lives on the prime side and is the **parity grading** `n -> (-1)^(n-1)` — in
     Bost--Connes terms the range-projection grading `1 - 2 mu_2 mu_2*` of the `2`-isometry. It is
     canonical: the Euler deletion at `q` has unimodular (`±1`) coefficients iff `q = 2`
     (`eulerDeletionCoefficient_unimodular_iff`).
   - The graded doublets `{2n+1, 2n+2}` of the `log sqrt(n)` Hamiltonian have absolutely
     convergent, strictly positive supertrace on the whole strip (`bornSupertrace_pos`) — where
     the ungraded trace diverges.
   - **Positive factorization of the sign** (`bornPartition_positive_factorization`): for
     `0 < beta < 2`, `Z(beta) * etaCoupling(beta) = Gammaℝ(beta/2) * bornSupertrace(beta)` with
     both right factors positive and `etaCoupling(beta) = 1 - 2^(1-beta/2) < 0`. The sign of `Z`
     on the whole strip — not only at `beta=1` — is carried entirely by the eta coupling scalar,
     i.e. by the deleted Euler factor at the grading prime, NOT by either trace. The
     eta/paired-sign mechanism of `ZetaRealStrip.lean` is confirmed as the source, in this exact
     localized form.
   - **Pole-mechanism exchange** (`etaCoupling_eq_zero_iff`, `etaCoupling_reflect_eq_zero_iff`):
     the coupling vanishes exactly at `beta=2` (grading resonance `2^(1-beta/2)=1`) and its Born
     reflection exactly at `beta=0` (the archimedean wall, the pole already formalized in
     `CompletedBornReflectionNoGo.lean`). The Born reflection exchanges the two boundary-pole
     mechanisms — so the conjectured duality must exchange the archimedean IR divergence with the
     `2`-adic grading resonance.
   - **New constraint 10 — the grading breaks self-duality** (`graded_reflection_cocycle`): the
     graded completed object `Gammaℝ · etaPair` satisfies only the twisted reflection identity
     with two-adic cocycle `(1-2^s)/(1-2^(1-s))`; strip convergence and exact self-duality
     exclude each other under the parity grading. The system must either compensate the cocycle
     (a `2`-adic counter-mode) or let the duality act on the pair (grading, reflected grading).
2. **Weld — EXECUTED 2026-07-12, the lift exists as a signed sector swap
   `[PROVED HERE + FORMALIZED]`** (`formal/GaloisForLFunctions/RHTower/BornSectorExchange.lean`,
   axiom-clean, lint green). The self-duality does NOT lift as a symmetry of the parity-graded
   weld (constraint 10); it lifts as a **Kramers--Wannier order/disorder exchange**. Findings:
   - Fourier duality of the two-torsion sends the parity character `n -> (-1)^n` to the
     half-integer coset `Z + 1/2`. The second sector is real: for `Re s > 1`,
     `sum_(m>=0) (m+1/2)^(-s) = (2^s - 1) zeta(s)` (`hzeta_one_half`, on the Hurwitz lane's
     `hzeta`), and its completion is `Lambda_2(s) = (2^s-1) Lambda(s)`
     (`lambdaHalfShift_eq_halfLevels`).
   - **Sector exchange with a sign**: `Lambda_4(1-s) = -Lambda_2(s)` and
     `Lambda_2(1-s) = -Lambda_4(s)` (`lambdaParity_one_sub`, `lambdaHalfShift_one_sub`): the
     reflection acts on the doubled sector pair as swap-with-negation, an involution. In Born
     form `Z_4(2-beta) = -Z_2(beta)` (`lambdaParity_born_reflect`). The two-adic cocycle is
     resolved by **sector doubling**, not compensation: on (untwisted parity-graded, half-twisted
     ungraded) the reflection is an honest involutive symmetry.
   - **The pole pair splits one per sector and is exchanged**: `s·Lambda_4 -> 1` at `s=0`
     (`tendsto_mul_lambdaParity_zero`), `(s-1)·Lambda_2 -> 1` at `s=1`
     (`tendsto_mul_lambdaHalfShift_one`), and the graded sector is **regular at the ungraded
     transition with value `log 2` = `Gammaℝ(1)·eta(1)`** (`tendsto_lambdaParity_one`).
   - **Convergence regimes swap**: the order sector converges as a supertrace on the whole
     temperature strip `beta > 0`; the disorder sector is an ordinary trace converging only at
     low temperature `beta > 2`. High-temperature graded order and low-temperature displaced
     disorder are exchanged — the literal Kramers--Wannier high-T/low-T shape, over the prime `2`.
   - The reflection eigenvectors of the doubled system are `Lambda_4 ∓ Lambda_2 =
     (2 - 2^s - 2^(1-s)) Lambda` (even) and `(2^s - 2^(1-s)) Lambda` (odd).
3. **Name the exchange category — EXECUTED 2026-07-12, both operator questions answered
   `[PROVED HERE + FORMALIZED]`** (`BornSectorExchange.lean` extension +
   `WeightOneInversion.lean`, axiom-clean, lint green).
   - **Which algebra hosts `Z + 1/2`: the same one.** The twisted module lives inside the
     `log sqrt(n)` system itself: unconditionally,
     `sum (m+1/2)^(-s) = 2^s * sum (2k+1)^(-s)` (`hzeta_one_half_eq_twisted_odd`,
     `oddLevelZeta_eq`) — the half-integer levels are the **grading-odd subspace**
     (range of `1 - mu_2 mu_2*`) with the Hamiltonian displaced by one half `2`-dilation
     quantum `-½ log 2`. Moreover `sum (m+1/2)^(-s) + zeta(s) = 2^s zeta(s)`
     (`hzeta_one_half_add_zeta`): adjoining the twisted sector reproduces the whole system at
     half-quantum shift, spectrum `½N` — **sector doubling is one rung of the `m=2` dilation
     tower** (`mPart` self-similarity). The doubled welded algebra is the original algebra one
     rung down; grading and twist are `P = mu_2 mu_2*` and `1 - P` of the same isometry.
   - **The archimedean swap is the weight-one inversion.** `J f(t) = t⁻¹ f(t⁻¹)` is an
     involution (`weightOneInversion_weightOneInversion`), anti-conjugates the scale generator:
     `J D J = -(D+1)` (`multiplicativeDeriv_weightOneInversion`), hence **commutes with the
     scaling Hamiltonian** `D²+D = D(D+1)` (`scalingHamiltonian_weightOneInversion`); on the
     Gaussian seed, `(D²+D)(J g₀) = J h` with `h` the theta-cusp seed
     (`scalingHamiltonian_weightOneInversion_thetaCuspGaussian`). On Dirichlet power profiles,
     `(D²+D) t^{-w} = w(w-1) t^{-w}` — the completed-zeta polynomial as Hamiltonian eigenvalue —
     and `J(t^{-w}) = t^{-(1-w)}` exchanges the profiles within each eigenspace
     (`scalingHamiltonian_rpow`, `weightOneInversion_rpow`). `J` moves the Gaussian state
     (`weightOneInversion_thetaCuspGaussian_ne`): the swap preserves dynamics, exchanges states.
4. **Poisson brick — EXECUTED 2026-07-12, closed by wiring `[PROVED + FORMALIZED]`**
   (`formal/GaloisForLFunctions/RHTower/BornPoissonWiring.lean`, axiom-clean, lint green).
   Mathlib's even Hurwitz development already carries the Poisson-summed pair; at the
   two-torsion point it IS the sector pair:
   - `completedCosZeta (1/2) = -Lambda_4` and `completedHurwitzZetaEven (1/2) = Lambda_2`,
     proven on `Re s > 1` by the series identifications (alternating series; `Z`-lattice
     folding `n <-> -(n+1)` onto the half-integers) and globalized off `{0,1}` by the identity
     theorem on the countable-complement-connected plane
     (`completedCosZeta_one_half`, `completedHurwitzZetaEven_one_half`).
   - Hence mathlib's `completedHurwitzZetaEven_one_sub` — proven by theta inversion, i.e.
     genuine Poisson summation — specializes to the signed sector swap:
     `lambdaHalfShift_one_sub_poisson`, agreeing with the independent scalar-FE proof
     (`lambdaHalfShift_one_sub`). Two disjoint derivations, one identity.
   - Kernel level: theta inversion IS the weight-one inversion of sector profiles:
     `disorderThetaProfile = J(orderThetaProfile)` and conversely
     (`disorderThetaProfile_eq_inversion`, via mathlib's `evenKernel_functional_equation`),
     and both profiles are lattice sums of dilated `thetaCuspGaussian` seeds — parity-signed
     integer dilations vs half-integer dilations (`orderThetaProfile_hasSum`,
     `disorderThetaProfile_hasSum`). The profile-swap-to-sector-swap conversion is closed.
5. **Graded KMS classification — EXECUTED 2026-07-12, theorem replaces shape, WITH A
   CORRECTION `[PROVED + FORMALIZED]`**
   (`formal/GaloisForLFunctions/RHTower/BornGradedKMSClassification.lean`, axiom-clean).
   - **Walls:** both sector traces have the same Gibbs wall `beta = 2` in the half-dilated
     gauge (`summable_halfDilatedWeight_iff`, `summable_halfLevelWeight_iff`), and throughout
     the high-temperature phase `0 < beta <= 2` the parity supertrace converges while the
     Gibbs trace diverges (`gradedOrder_beyond_wall`): the strip KMS datum is intrinsically
     graded.
   - **The involution's phase action (label form, classification as hypothesis):** the
     KW sector swap `beta -> 2-beta` acts WITHIN the high-temperature `III_1` phase — it never
     reaches the type-I phase (`label_sectorSwap_within_highTemp`). The gauge's own KMS
     reflection is `beta -> 4-beta`, crossing the wall exactly at its fixed point `2`
     (`label_bornReflect_eq_iff`), and the unit tower shift `beta -> beta+2` — the difference
     of the two involutions — always crosses (`label_towerShift_ne`).
   - **Correction to the conjecture's shape:** the duality does NOT exchange the
     `III_1`/type-I pair. The phase exchange belongs to the KMS reflection = swap ∘ shift; the
     KW swap itself is phase-internal. Consequently **constraint 5's non-normality obstruction
     dissolves for the true involution**: both swapped sectors sit in the `III_1` phase, so
     the sector swap may be realized by a normal graded equivalence — the conjectured system
     MATERIALIZES as a phase-internal graded involution and dies in its original
     phase-exchanging form.
6. **Kill tests inherited:** diagonal action is Born-invisible (parent Theorem 5) — dead; scalar
   partition identity alone — dead; measured trace — dead; declaring FE a gauge symmetry —
   circular. The map acts on archimedean off-diagonal structure (constraint 4); by step 5 it
   need not be non-normal — that demand transfers to the tower shift, not the duality.
7. **Degenerate control:** drop the archimedean mode — the parent card proves no duality exists
   for bare Bost--Connes; the archimedean mode is load-bearing or the conjecture is false. Drop
   the grading — constraint 2 proves the ungraded version false outright.

## Log

- 2026-07-12 — created in 0-backlog from the collapse theorem of the Born-temperature card.
- 2026-07-12 — corpus review (pipeline + RHTower + formal root): statement corrected by the
  dihedral no-go to the half-dilated gauge `Z(beta)=Lambda(beta/2)` with forced grading (both now
  formalized in `CompletedBornReflectionNoGo.lean`, axiom-clean); constraints 1--9 recorded with
  their in-tree Lean anchors; `Lambda`-hypertranscendence isolated as the `[OPEN CORE]`
  no-finite-handle certificate.
- 2026-07-12 — Approach step 1 executed: grading identified as the parity grading `1 - 2 mu_2 mu_2*`
  (unique unimodular Euler deletion), archimedean mode proven ungraded-positive, sign of `Z` on the
  whole strip localized in the eta coupling scalar, pole-mechanism exchange and the two-adic
  FE-breaking cocycle proved. All formalized in `BornEtaGrading.lean` (11 declarations,
  axiom-clean); `ZetaRealStrip.lean` eta interface made public for reuse. Card gains constraint 10;
  next open move = Approach step 2 (the weld) under the cocycle-resolution requirement.
- 2026-07-12 — Approach step 2 executed: the self-duality lifts as a Kramers--Wannier signed
  sector swap between the parity-graded sector and the half-integer (Fourier-dual coset) sector;
  the two-adic cocycle is resolved by sector doubling. Poles split one per sector and are
  exchanged; the graded sector is regular at the ungraded transition with value `log 2`;
  convergence regimes swap (supertrace on the strip vs low-temperature trace). All formalized in
  `BornSectorExchange.lean` (9 declarations, axiom-clean, reusing the Hurwitz lane's `hzeta`);
  `hzeta_one_half` is a reusable Hurwitz brick. Step 3 sharpened to the doubled-algebra involution.
- 2026-07-12 — Approach step 3 executed: both operator questions answered and formalized. The
  `Z+1/2` module is in-system (grading-odd subspace at half-quantum shift; sector doubling = one
  `m=2` tower rung; `hzeta_one_half_eq_twisted_odd` unconditional, `hzeta_one_half_add_zeta`,
  `oddLevelZeta_eq` in `BornSectorExchange.lean`). The archimedean swap is the weight-one
  inversion: involution, `J D J = -(D+1)`, commutes with `D²+D`, `(D²+D)(J g₀) = J h` on the
  theta-cusp seed, exchanges `t^{-w} ↔ t^{-(1-w)}` inside eigenspaces of eigenvalue `w(w-1)`,
  moves the Gaussian state (`WeightOneInversion.lean`, 10 declarations, axiom-clean). Gate 0→1
  ticked; card moved to 1-in-progress. Open core: Poisson/theta brick for the profile-to-sector
  conversion + graded KMS classification of the doubled-rung involution.
- 2026-07-12 — Approach steps 4 and 5 executed; both remaining bricks closed. Poisson brick closed
  by WIRING: mathlib's even-Hurwitz pair at `a=1/2` identified with the sector pair
  (`BornPoissonWiring.lean`: series identifications + identity-theorem globalization off `{0,1}`;
  `lambdaHalfShift_one_sub_poisson` re-derives the swap from genuine Poisson summation, agreeing
  with the scalar-FE proof; kernel-level `disorderThetaProfile = J(orderThetaProfile)` with both
  profiles as lattice sums of dilated theta-cusp Gaussian seeds). Graded KMS classification proved
  in label form (`BornGradedKMSClassification.lean`): walls at `beta=2` for both sectors, graded
  supertrace beyond the wall, and the involution's phase action — **correction**: the KW swap is
  phase-INTERNAL (III_1 to III_1); the phase exchange belongs to the KMS reflection = swap ∘ tower
  shift. Constraint 5's non-normality obstruction dissolves for the duality itself. The system
  materializes as a phase-internal graded involution; its original phase-exchanging form is dead.
  Open next: the paper-level C*-existence with graded KMS uniqueness on the strip, and the
  `[OPEN CORE]` `Lambda`-hypertranscendence certificate.

## Gate 1→2 execution (2026-07-12): both residual items driven to named walls

### A. The `Lambda`-hypertranscendence certificate

**A1. Holonomic rung `[PROVED HERE + FORMALIZED, zero-sequence hypothesis]`.** The tree's
pole-residue master engine (`GammaDifferentialFE.not_holonomic_master`, arbitrary injective pole
locations) applies to `xi'/xi`: at every `xi`-zero `rho` of order `m >= 1`,
`xi'/xi = m/(s-rho) + analytic`, so each iterated derivative has a pole of exact order `j+1`
with nonvanishing leading datum `m·(-1)^j·j!` — no simplicity needed
(`xiLogDeriv_iteratedDeriv_residue`). Hence, given any injective sequence of `xi` zeros
(classically true: infinitude of nontrivial zeros; not yet unconditional in the tree),
**`xi'/xi` satisfies no linear differential equation with polynomial coefficients**
(`xiLogDeriv_not_holonomic`, `formal/GaloisForLFunctions/RHTower/XiLogDerivNotHolonomic.lean`,
axiom-clean). Unconditionalization routes: Hardy-type infinitude, or the trivial-zero variant on
`zeta'/zeta` at `s = -2k` (needs `zeta'(-2k) != 0` from the differentiated FE).

**A2. The full rung reduces to a single quantitative digamma wall `[PROVED HERE, paper]`.**
Define **(QH)**: *no nonzero polynomial `P` in `s` and the jets `psi(s/2), psi'(s/2), ...` (with
`C(s)` coefficients) has `P(s, psi-jets)(sigma) = O(e^(-c*sigma))` on the real ray for some
`c > 0`.* Then:

> **Theorem.** QH implies `xi` is hypertranscendental (equivalently `Lambda` is).

*Proof.* If `xi` is DA then so is `u := xi'/xi` (log-derivative closure). Split
`u^(j) = r_j(s) + a_j + z_j` with `r_j` rational, `a_j` the `(1/2)psi(s/2)`-jets, and
`z_j = (d/ds)^j (zeta'/zeta)` the prime-log Dirichlet jets. A putative relation
`Q(s, u, ..., u^(m)) = 0` becomes `sum_alpha C_alpha(s, a-jets) * z^alpha = 0` with the
`C_alpha` polynomial in `s` and the `a`-jets; since the change of variables is triangular, some
`C_(alpha*)` is a nonzero polynomial. Each `z`-monomial expands into an absolutely convergent
Dirichlet series over frequencies `log(n_1...n_r)` with polynomial-in-`log` coefficients; group
the whole relation by frequency: `sum_m d_m(s) m^(-s) = 0` on `Re s > sigma_0`, where each
`d_m` lies in `C(s)[psi-jets]` and has power-log growth with summable majorants. The standard
minimal-frequency estimate makes the least nonzero `d_(m_0)` exponentially small on the ray, so
QH forces `d_(m_0) = 0` *as a polynomial*; hence all `d_m = 0`. Unique factorization (prime-power
frequencies `p^w` receive only `p`-supported monomials) plus Vandermonde in `log p` over
infinitely many primes — the tree's `ZetaHypertranscendental` jet bookkeeping (`jetM_inj`,
`lseries_jetProd`) — then recovers `C_alpha = 0` as polynomials for every `alpha`, contradicting
`C_(alpha*) != 0`. QED.

Moreover **QH implies Hölder's theorem** (a vanishing polynomial relation among `psi`-jets is in
particular exponentially small), so QH is a strict quantitative strengthening of the tree's named
Gamma frontier.

**A3. Dead-end localization.** Laurent/pole bookkeeping cannot pass the holonomic rung: at a
simple zero, `u' + u^2` has no double pole (the Riccati cancellation; Weierstrass `p` shows
pole-compatible nonlinear ADEs exist). The entire remaining content of the `[OPEN CORE]` is QH.
Named closure route `[CONJECTURE]`: the digamma asymptotics are Gevrey-1 in sectors
`|arg s| < pi - delta`, so a QH-violating element is exponentially flat in a sector of opening
`> pi`, and Watson's uniqueness theorem forces it to vanish; formalization of that route needs
sectorial Gevrey estimates not present in mathlib.

### B. The graded C*-system: existence data proven, uniqueness named

**B1. The system and its modular data `[PROVED, computation]`.** On `l2(N>=1)` with
`H|n> = log sqrt(n)|n>`, the dilation isometries `mu_k|n> = |kn>` satisfy
`sigma_t(mu_k) = k^(it/2) mu_k`; the parity grading satisfies `Gamma mu_k = mu_k Gamma` for odd
`k` (`gradedSign_mul_odd`) while `mu_2` twists (`gradedSign_mul_two`). The archimedean scale
mode is welded ungraded (step 1).

**B2. Graded Gibbs covariance on the strip `[PROVED HERE + FORMALIZED]`.** The diagonal shadow
of the super-KMS condition for the graded Gibbs functional holds unconditionally on the whole
strip: the `k`-dilated graded doublet weights sum to `k^(-beta/2)` times the parity supertrace
(`tsum_dilatedBornSupertraceTerm`,
`formal/GaloisForLFunctions/RHTower/BornSuperKMSCovariance.lean`, axiom-clean) — exactly the
covariance `omega(mu_k x mu_k^*) = k^(-beta/2) omega(x)` demanded of a `KMS_beta` functional,
available at temperatures where only the graded datum converges (`gradedOrder_beyond_wall`).

**B3. Uniqueness `[OPEN CORE]`.** What remains for gate 1→2 is the uniqueness of the graded
KMS functional on the strip — the supertrace analogue of the published high-temperature
ergodicity (Neshveyev-type). The phase-internality theorem (step 5) removes the non-normality
obstruction, so the target is a *normal* graded uniqueness statement; its proof requires
BC-ergodicity technology beyond this tree — a named research-scale wall, not a construction gap.

**Residue of gate 1→2 after this pass:** exactly two named walls — QH (A3) and graded KMS
uniqueness (B3). Everything mechanizable before them is proven and formalized.

### A4. QH attacked via Gevrey--Watson: it collapses into Hölder (2026-07-12, second pass)

**A4a. Unconditional holonomic rung for `zeta` `[PROVED HERE + FORMALIZED]`.** The residue law
was generalized to any analytic zero (`logDeriv_iteratedDeriv_residue_of_zero`), and the trivial
zeros `-2, -4, ...` supply an unconditional injective pole sequence for `zeta'/zeta`; the needed
"not identically zero nearby" input is the identity theorem on the punctured plane against
`zeta(2) != 0` — no simplicity of trivial zeros, no differentiated functional equation.
**`zeta'/zeta` satisfies no linear differential equation with polynomial coefficients,
unconditionally** (`zetaLogDeriv_not_holonomic`,
`formal/GaloisForLFunctions/RHTower/XiLogDerivNotHolonomic.lean`, axiom-clean). The advertised
`zeta'(-2k) != 0` brick turned out unnecessary — the multiplicity-agnostic design removes it.

**A4b. QH is equivalent to Hölder's theorem `[PROVED HERE, paper, modulo two classical
inputs]`.** The Gevrey--Watson test succeeds and collapses the wall:

> **Theorem.** Assume (i) the digamma jets admit Poincaré expansions with Gevrey-1 remainder
> bounds uniformly in sectors `|arg s| <= pi - delta` (Binet's integral representation), and
> (ii) Nevanlinna--Watson uniqueness: a function holomorphic in a sector of opening `> pi`
> that is Gevrey-1-flat (hence `O(e^(-c|s|))` there) vanishes identically.  Then QH holds if
> and only if `psi` is hypertranscendental (Hölder 1887).

*Proof.* QH implies Hölder trivially (a vanishing nonzero polynomial relation is exponentially
small). Conversely let `P != 0` be a polynomial with `F := P(s, psi-jets)` exponentially small
on the real ray; clearing denominators keeps exponential smallness. Substituting the Gevrey
expansions, `F` acquires a composite power-log asymptotic expansion with well-ordered support.
If the expansion is nonzero its leading term `c·sigma^a·log^b(sigma)` dominates, contradicting
exponential smallness. If it is zero, `F` is Gevrey-1-flat in a sector of opening
`2(pi - delta) > pi`, hence exponentially small throughout; by (ii) `F ≡ 0`, i.e. `P` is an
algebraic differential relation for `psi`, contradicting Hölder. QED.

**A4c. Consequence: the `[OPEN CORE]` is discharged at paper level.** Chaining A2 and A4b:

> `xi` (equivalently `Lambda`) is hypertranscendental — proved modulo three classical
> literature inputs: Hölder 1887, Binet/Gevrey sectorial digamma bounds, Nevanlinna--Watson
> uniqueness.

The no-finite-handle certificate demanded by constraint 7 therefore exists on paper; as
expected it is a composition of classical results, not new science `[BRIDGE]`. What remains is
purely a formalization frontier, now exactly delimited: Hölder's theorem in Lean (the tree's
named Gamma frontier, `GammaDifferentialFE` being its staging) plus sectorial Gevrey/Watson
infrastructure absent from mathlib. Gate 1→2's item (A) is closed as mathematics; item (B)
(graded KMS uniqueness) remains the single open wall of the card.

### A5. Hölder's theorem in Lean: the analytic content is now proven (2026-07-12, third pass)

The classical difference-equation proof of Hölder's theorem was decomposed; its only two
non-bookkeeping steps are proven and formalized in
`formal/GaloisForLFunctions/HTGeometry/HolderDifferenceBricks.lean` (axiom-clean, lint green):

- `shift_periodic_quotient_constant` — **shift-periodic rational functions are constant**:
  `p(X+1)·q = p·q(X+1)` with `p, q` coprime forces both constant (shift preserves degree and
  leading coefficient; a shift-invariant polynomial is constant on `ℕ`).
- `difference_single_pole_free` — **no rational function has a difference-derivative with a
  single-point pole**: `w(X+1) - w(X) = A(X)/X^{n+1}` (cross-multiplied form) forces `A = 0`.
  The classical pole-propagation argument fully algebraizes: the largest integer root of the
  denominator is pinched to `0`, the smallest to `1` — contradiction — so no integer roots;
  evaluation at `0` kills the constant coefficient of `A` and one factor of `X` cancels,
  descending by induction.  Purely polynomial; no Laurent expansions, no asymptotics.

**Remaining for full `Hölder` in Lean (pure differential-polynomial bookkeeping, no further
analytic input):** (i) minimal-rank irreducible relation selection (well-founded rank, UFD of
`MvPolynomial` over `RatFunc ℂ`, identity theorem for factor selection — machinery present in
tree); (ii) the shift substitution `P ↦ P^σ` and its evaluation compatibility from
`ψ(s+1) = ψ(s) + 1/s` and `iteratedDeriv_inv_add_const` (both in `GammaDifferentialFE`);
(iii) leading-coefficient elimination `I·P^σ - I^σ·P = 0` by minimality, giving
`P^σ = u·P`; (iv) top-homogeneous-part analysis via brick one, degree-`(D-1)` layer via brick
two, closing with the characteristic-zero Euler identity.  Estimated as one focused
formalization campaign; every analytic ingredient is now machine-checked.

### B3 status

Not advanced this pass beyond the formalized covariance shadow (B2).  Next brick: diagonal
uniqueness — the graded weight is the unique dilation-covariant graded functional on the
diagonal up to normalization — an arithmetic statement on `ℕ` formalizable with current
tools; the off-diagonal (ergodicity) part remains the research-scale wall.

### A6. Hölder's theorem PROVEN IN LEAN; the chain assembled (2026-07-12, pass 4)

**A6a. Hölder's theorem, digamma form `[PROVED HERE + FORMALIZED, axiom-clean]`.**
`Hypertranscendental Complex.digamma` — psi = Gamma'/Gamma satisfies no algebraic
differential equation over `C[s]` — is machine-checked
(`formal/GaloisForLFunctions/HTGeometry/DigammaHypertranscendental.lean`, riding
`HolderShiftElimination.lean`). The proof is a new fully algebraic execution of the classical
difference-equation argument, with no Laurent expansions and no analytic minimality:

1. *Shift elimination over `C(X)`* (`no_shift_stable_annihilator`): any subset of
   `MvPolynomial (Fin m) (RatFunc C)` closed under subtraction, `C(X)`-scalars, and the jet
   substitution `tau : a(X) -> a(X+1), Y_j -> Y_j + (-1)^j j!/X^(j+1)`, containing no nonzero
   constant, contains no nonzero element. A double-minimal member (minimal jet degree `D`,
   then minimal top-layer support) forces `tau P = u*P` by support-count elimination; the top
   layer is shift-periodic hence has constant coefficient ratios (brick 1); the `(D-1)` layer
   satisfies difference equations with right sides in the span of the pole parts, killed by
   brick 2 — the gradient of the top form vanishes, impossible in characteristic zero.
2. *No RatFunc evaluation anywhere*: the annihilator set is defined by denominator-cleared
   polynomial forms (`digammaAnnihilator`), and shift stability is verified through an explicit
   cleared substitution `Y_j -> X^m Y_j + (-1)^j j! X^(m-1-j)` (`clearedShift`) converted to
   evaluation at `z+1` by the differentiated shift law `psi^(j)(z+1) = psi^(j)(z) +
   (-1)^j j!/z^(j+1)` (from the tree's `polygamma_recurrence`).
3. The engine consumes vanishing only OFF THE POLES, so the stronger polynomial-level form
   `digamma_jet_annihilator_eq_zero` is exposed directly.

**A6b. The QH interface formalized `[FORMALIZED, axiom-clean]`**
(`formal/GaloisForLFunctions/HTGeometry/QuantitativeHolderInterface.lean`):
- `halfDigamma_jet_annihilator_eq_zero` — the VANISHING CASE OF QH IS NOW A THEOREM: a
  polynomial in `(s, psi(s/2)-jets)` vanishing off the poles is zero (substitution `s -> 2s`
  into Hölder).
- `halfDigamma_jet_annihilator_eq_zero_of_ray` — ray rigidity: vanishing on the far real ray
  suffices (jet evaluation analytic off `-2N`; complement of a countable set is connected;
  identity theorem).
- `QuantitativeHolder` (the QH Prop) and `WatsonFlatness` (the named sectorial
  Gevrey-1/Watson input, conclusion needed only on the far ray);
  `quantitativeHolder_of_watsonFlatness` — QH reduces to Watson flatness with all vanishing
  content machine-checked.

**A6c. The chain assembled `[FORMALIZED, axiom-clean]`**
(`formal/GaloisForLFunctions/RHTower/XiHypertranscendenceChain.lean`):
- `xiLogDeriv_split` — the weld identity UNCONDITIONAL on `Re s > 1`:
  `xi'/xi = 1/s + 1/(s-1) - (log pi)/2 + (1/2) psi(s/2) + zeta'/zeta`, plus its local
  function-level form `xiLogDeriv_eventuallyEq_split` (all jets split).
- `XiFrequencyCollapse` — the named Dirichlet-side input: a nonzero jet annihilator of `xi`
  yields a nonzero exponentially small half-argument digamma jet polynomial (contains: the
  triangular change of variables, frequency grouping, minimal-frequency estimate, prime-power
  Vandermonde — the A2 paper proof).
- `xi_hypertranscendental_of_quantitativeHolder` / `..._of_watsonFlatness` — THE CHAIN
  THEOREMS: `QuantitativeHolder` (resp. `WatsonFlatness`) plus `XiFrequencyCollapse` forces
  `Hypertranscendental xi`.

**Residue of the Lambda-HT certificate after pass 4 — exactly two named interfaces:**
1. `WatsonFlatness` — sectorial Gevrey-1 digamma asymptotics + Watson uniqueness (new
   mathlib-level analysis; the A4 route).
2. `XiFrequencyCollapse` — the Dirichlet-side collapse; formalization target riding the
   tree's `ZetaHypertranscendental` machinery (`zetaJetA`, `jetM_inj`,
   `LSeriesPolynomialWeightUniqueness`) against the now-proven weld split; von Mangoldt
   L-series identities are in mathlib.

**Opened (next generative moves):** (i) `XiFrequencyCollapse` is now a sharply-scoped
formalization campaign with every prerequisite named; (ii) the Gamma-transfer
`Hypertranscendental Complex.Gamma` from digamma HT — differential-algebra elimination of the
Bell substitution `Gamma^(k) = Gamma * B_k(psi-jets)`, a term-count induction in the same
MvPolynomial style; (iii) the graded KMS wall B3 is untouched by this pass and remains the
card's other gate-1->2 item.

### A7. Hölder's theorem for Γ itself PROVEN IN LEAN (2026-07-12, pass 5)

**`Hypertranscendental Complex.Gamma` `[PROVED HERE + FORMALIZED, axiom-clean]`** — the
original 1887 statement, transferred from the digamma form through the Bell substitution.
Three new modules:

1. `GammaShiftEigenrelation.lean` — the inverse shift `ratShiftInv`/`jetTranslateInv`
   (making the jet substitution an automorphism), degree preservation
   (`totalDegree_jetTranslate`, via the top-layer law, no inverse needed), and the
   **eigenrelation refutation** `no_shift_eigenrelation`: no nonzero jet polynomials with
   `sigma(f)*g = X^e*f*sigma(g)`, `e >= 1`. Reduced to relatively prime parts (UFD
   `exists_reduced_factors`), the substitution forces `sigma(f) | f`, `sigma(g) | g` with
   equal degrees, so both quotients are scalars and the top-layer coefficient ratio
   satisfies the rational Gamma FE `r(X+1) = X^e r(X)` — refuted by a pure `natDegree`
   count (LHS `deg p + deg q`, RHS `e + deg p + deg q`).
2. `GammaBellSubstitution.lean` — the structural Bell family `bellCore k` (minimal jet
   frames, rename-based recursion mirroring the tree's existential `exists_gamma_bell`),
   the evaluation identity `Gamma^(k) = Gamma * B_k(psi-jets)`, the triangular
   decomposition `B_{k+1} = x_k + (poly in x_<k)` (`pderiv_last_bellCore = 1` +
   `bellCore_succ_decomp`), and **pointwise surjectivity of the Bell value map**
   (`exists_bellCore_solution`, recursive back-substitution via `Fin.snoc` prefix vectors)
   — the step that transports nonzeroness through the substitution WITHOUT any lex-order
   or localization machinery.
3. `GammaHypertranscendental.lean` — `GammaPowerRel` (cleared Gamma-power relations),
   the **Gamma-power elimination** `gammaPowerRel_eq_zero` (strong induction on the
   Gamma-degree: the shift contributes `s^k` per degree by `Gamma(s+1) = s*Gamma(s)`;
   cross-multiplication kills the top; the eliminated relation dies by induction; the
   surviving identities are either a single term — killed by the polynomial-level Hölder
   theorem `polyJetEval_offPole_eq_zero` — or eigenrelations, killed by module 1), the
   Bell expansion `eval₂_bell_expansion`, and the capstone `hypertranscendental_gamma`.

Supporting refactor: `polyJetEval_clearedShift` (value form of the cleared substitution,
extracted from the digamma module) and `polyJetEval_offPole_eq_zero` (the
polynomial-coefficient annihilator theorem via `reshapeJet_comp_reshapeJetInv`).

**Which frontier this closes:** `Hypertranscendence.lean`'s founding target
(`Hypertranscendental Complex.Gamma`, flagged there as "the frontier statement") is now a
theorem. Together with `hypertranscendental_digamma` and `hypertranscendental_riemannZeta`
all three seed objects of the branch (Γ, ψ, ζ) are machine-checked hypertranscendental.

**Opened:** the Gamma-power elimination pattern (Bell transfer + power elimination +
eigenrelation endgame) is exactly the shape of the log-derivative closure step (a) of
`XiFrequencyCollapse` — for ξ the role of the Γ FE is played by differentiation
(`ξ' = u·ξ`), so the analogous endgame is a DIFFERENTIAL unit equation
`∂w = m·x₁·w` in the jet fraction field; the remaining collapse bricks are the
von Mangoldt Dirichlet jets (mathlib has the L-series identities) and the
minimal-frequency estimate.

### A8. XiFrequencyCollapse: the jet decomposition formalized (2026-07-12, pass 5)

**`[FORMALIZED, axiom-clean]`** (`formal/GaloisForLFunctions/RHTower/XiCollapseDirichletLeg.lean`):

- `iteratedDeriv_zetaLogDeriv_eq_LSeries` — **the von Mangoldt jet identity**: on
  `Re s > 1`, `(d/ds)^j (zeta'/zeta)(s) = (-1)^(j+1) * L((log·)^[j] Lambda)(s)` — every
  jet of the Dirichlet leg is an absolutely convergent prime-supported Dirichlet series
  with polynomial-in-log weights (rides mathlib's
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` + `LSeries_iteratedDeriv`).
- `iteratedDeriv_half_digamma` — the chain rule `(d/ds)^j psi(s/2) = (1/2)^j psi^(j)(s/2)`
  off the poles.
- `iteratedDeriv_xiLogDeriv_split` — **the full jet decomposition**: every jet of
  `xi'/xi` on `Re s > 1` splits as
  `(rational-leg jet) + (1/2)^(j+1) psi^(j)(s/2) + (-1)^(j+1) L(log^j Lambda)(s)`.
  This is exactly the `u^(j) = r_j + a_j + z_j` split of A2, machine-checked.

**XiFrequencyCollapse residue after pass 5** — three named sub-bricks:
1. Log-derivative closure for `xi`: `xi` DA ⟹ nonzero relation among `xi'/xi`-jets. The
   Gamma-transfer pattern (A7) applies verbatim EXCEPT the elimination endgame: for `xi`
   the shift is replaced by differentiation (`xi' = u·xi`), so the terminal identity is the
   DIFFERENTIAL unit equation `∂w = m·x₁·w` in the jet fraction field (∂ = ∂_s + Σ
   x_{j+1}∂_{x_j}) — refutable by a weight/degree count analogous to
   `ratShift_eq_X_pow_mul_eq_zero`.
2. The minimal-frequency estimate: grouping the relation by Dirichlet frequency and
   bounding the tail below the least frequency — the analytic wall (exponential smallness
   of the least coefficient on the ray).
3. Prime-power Vandermonde extraction — the tree's `jetM_inj`/`lseries_jetProd` machinery
   over von Mangoldt weights.

### A9. The differential unit equation no-go PROVEN IN LEAN (2026-07-12, pass 6)

**`differential_unit_no_go` / `no_differential_eigenrelation` `[PROVED HERE + FORMALIZED,
axiom-clean]`** (`formal/GaloisForLFunctions/HTGeometry/DifferentialUnitEquation.lean`) — the terminal
obstruction of XiFrequencyCollapse sub-brick (1), the differential twin of
`no_shift_eigenrelation`.

On the differential polynomial ring `ℂ{u} = MvPolynomial ℕ ℂ` (jet coordinates `x₀ = s`,
`x₁ = u`, `x_{j+1} = u⁽ʲ⁾`) with the total derivative `𝒟` (`𝒟 x₀ = 1`, `𝒟 x_k = x_{k+1}`
for `k ≥ 1`), the **differential unit equation** `𝒟 w = m·x₁·w` (`m ≥ 1`) has no nonzero
rational solution: in cleared form, for `p, q ≠ 0` (`no_differential_eigenrelation`; the
coprime core `differential_unit_no_go`),

`𝒟p·q − p·𝒟q = m·x₁·p·q`  is impossible.

**Why this is the right object.** In the Γ-transfer (A7) the `f`-power elimination
terminated against the *shift* `s ↦ s+1` (functional equation `Γ(s+1) = s·Γ(s)`) and its
eigenrelation `σf·g = Xᵉ·f·σg`. For `ξ` the functional equation is *differentiation*
(`ξ' = u·ξ`), so differentiation contributes the factor `d` in `ξ`-degree `d`, and the
terminal eigenrelation is exactly the differential unit equation with `u = ξ'/ξ = x₁`. This
is the general terminal for the **logarithmic-derivative closure of differential
algebraicity** — reusable well beyond `ξ`.

**Proof (the differential twin of the integer-root pinch).** The total derivative introduces
at the top jet variable `x_N` a fresh variable `x_{N+1}` linearly with coefficient `∂_{x_N}`
— formalized as the commutator identities `[∂_{x_{N+1}},𝒟] = ∂_{x_N}` (N≥1) and
`[∂_{x₁},𝒟] = 0` (via `Derivation.commutator_apply` + `derivation_ext`, using the total
derivative built as `mkDerivation ℂ`). Applying `∂_{x_{N+1}}` to the equation, coprimality
plus the strict total-degree drop of `∂_{x_N}` (`totalDegree_pderiv_lt`,
`pderiv_self_dvd_eq_zero`, `pderiv_ne_zero_of_mem_vars`) forces `p, q` independent of the top
variable; descending to `ℂ[x₀]`, a final `∂_{x₁}` reads off `m·p·q = 0` — impossible. No
recursion: a single case split on whether every variable is `x₀`.

**XiFrequencyCollapse residue after pass 6 — two named bricks:**
1. The log-derivative closure ENGINE: `ξ` DA ⟹ nonzero `u = ξ'/ξ` jet relation. Structure =
   Bell transfer (`bellCore` reusable) + differentiation elimination (𝒟 on
   `MvPolynomial ℕ ℂ` coefficients, cleared form) with `no_differential_eigenrelation` as the
   now-available terminal — the direct differential analog of `gammaPowerRel_eq_zero`; plus
   the off-poles concrete bridge (`ξ` entire with zeros, `u` meromorphic, jet identity holds
   off the ξ-zeros; identity-theorem extension as in `QuantitativeHolderInterface`).
2. The minimal-frequency estimate + von Mangoldt Vandermonde (the analytic wall + tree
   `jetM` bookkeeping over the now-formalized von Mangoldt jets `iteratedDeriv_xiLogDeriv_split`).

### A10. The differentiation-elimination engine + log-derivative bridge FORMALIZED (2026-07-12, pass 7)

**`[PROVED HERE + FORMALIZED, axiom-clean]`** — sub-brick (1) of XiFrequencyCollapse is now
built up to a single well-scoped Bell-graded wiring step. Two new modules:

**`formal/GaloisForLFunctions/HTGeometry/DifferentialPowerElimination.lean`** — the engine, the
`𝒟`-on-coefficients analog of `gammaPowerRel_eq_zero`:
- `diffPowerRel_yields` — **THE ENGINE**: a power relation `∑_{d≤D} f^d·(uJet u z)(Q_d) = 0`
  on an open `Ω` (hypotheses `hf : f' = u·f`, `hJ : jet-eval differentiates by 𝒟`,
  `hfne : f ≠ 0`), with not all `Q_d = 0`, yields a NONZERO `R` with `(uJet u z)(R) = 0` on
  `Ω` — a differential-algebraic relation for `u`. Strong induction on the ξ-degree:
  `derivedRelation` (differentiate the relation, coefficient `Q_d ↦ 𝒟Q_d + d·x₁·Q_d`),
  `elimRelation` (kill the top power), then either a single surviving term (the `u`-relation,
  via `f ≠ 0`) or the differential eigenrelation — refuted by `no_differential_eigenrelation`
  (pass 6). No denominator clearing (unlike the Γ shift-elimination): with `s = x₀` a jet
  variable everything is in `MvPolynomial ℕ ℂ` with `totalDeriv`.
- The analytic bridge, discharging the engine's hypotheses from analyticity: `uJet`,
  `hasDerivAt_uJetEval` (**the chain rule** `(uJet u ·)(P)' = (uJet u z)(𝒟P)`), and the
  packaged capstone `logDeriv_DA_of_powerRel` (engine + bridge for `u = f'/f`).

**`formal/GaloisForLFunctions/HTGeometry/LogDerivBellTransfer.lean`** — the transfer bricks:
- `iteratedDeriv_eq_bellCore_generic` — the **generic Bell identity**
  `f⁽ᵏ⁾ = f·B_k(u-jets)` for any analytic nonzero `f` (generalizes
  `gamma_iteratedDeriv_eq_bellCore`).
- `finPolyToNat` + `eval_uJet_finPolyToNat` — the frame translation carrying the `Fin`-frame
  Bell-graded coefficients of the Γ-transfer into the `ℕ`-frame the engine consumes, with
  `eval (uJet u z) (finPolyToNat n H) = eval₂ (evalRingHom z) (u-jets) H`.

**Remaining for sub-brick (1) — one wiring step:** assemble the power relation from `ξ` DA.
With `Ω = {ξ ≠ 0}` (open; ξ entire), `H = reshapeJet n P`, `u = ξ'/ξ`:
`eval₂_bell_expansion` (reuse) + `eval₂_reshapeJet` (reuse) + the generic Bell identity give
`∀ z ∈ Ω, ∑_dd (ξ z)^dd · (uJet u z)(finPolyToNat n (bellGraded n H dd)) = 0`; the
non-vanishing `∃ dd, finPolyToNat n (bellGraded n H dd) ≠ 0` is `P ≠ 0` via the top-degree
`bellGraded` (Bell triangularity, `bellCore_succ_decomp`) or the Bell-surjectivity
`exists_bellAt_solution` (as in `hypertranscendental_gamma`'s vanishing step). Feeding these to
`logDeriv_DA_of_powerRel` discharges sub-brick (1) end-to-end. Then the residue of
`Hypertranscendental xi` is the single analytic input `WatsonFlatness` plus the
minimal-frequency/von Mangoldt-Vandermonde bookkeeping over `iteratedDeriv_xiLogDeriv_split`.

### A11. XiFrequencyCollapse sub-brick (1) DISCHARGED END-TO-END (2026-07-12, pass 7 cont.)

**`logDeriv_DA_of_DA_full` `[PROVED HERE + FORMALIZED, axiom-clean]`**
(`formal/GaloisForLFunctions/HTGeometry/LogDerivPowerRelation.lean`): for any `f` analytic and nonzero on
an open `Ω` carrying a NONZERO differential-algebraic relation, its logarithmic derivative
`u = f'/f` satisfies a nonzero differential-algebraic relation on `Ω`. Applied to `f = ξ`
(entire, `Ω = {ξ ≠ 0}` open), this is exactly **"ξ DA ⟹ ξ'/ξ DA"** — sub-brick (1), complete.

The assembly, all axiom-clean:
- `xiDA_powerRelation` — the DA relation becomes a power relation
  `∑_d f^d·(uJet u z)(finPolyToNat n (bellGraded n (reshapeJet n P) d)) = 0` via
  `eval₂_bell_expansion` + `eval₂_reshapeJet` + the generic Bell identity + the frame
  translation.
- `exists_finPolyToNat_bellGraded_ne_zero` — the non-vanishing `P ≠ 0 ⟹ ∃ d, Q_d ≠ 0`, via
  `finPolyToNat_injective` (built from an explicit left inverse) and `Pzero_of_bellGraded_zero`
  (the Bell-surjectivity vanishing argument `exists_bellAt_solution`, reconstructed from
  `hypertranscendental_gamma`).
- `logDeriv_DA_of_powerRel` (the engine + chain-rule bridge) then delivers the `u`-relation.

**XiFrequencyCollapse residue after pass 7 — one named analytic input remains for
`Hypertranscendental xi`:** the minimal-frequency estimate + von Mangoldt Vandermonde
bookkeeping over the now-formalized jet split `iteratedDeriv_xiLogDeriv_split` (sub-brick 2),
plus `WatsonFlatness` for the QH interface. The differential-algebra spine of the whole
collapse — Hölder for Γ/ψ/ζ, the differential unit no-go, the elimination engine, and now the
log-derivative closure ξ DA ⟹ ξ'/ξ DA — is entirely machine-checked.
