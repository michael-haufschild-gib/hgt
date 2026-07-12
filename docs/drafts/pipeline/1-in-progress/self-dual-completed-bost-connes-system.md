# Graded self-dual completed Bost--Connes system: the functional equation as an operator-algebra duality

- **ID:** `self-dual-completed-bost-connes-system`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** collapse theorem and dihedral correction of
  `../3-formalized/not_new_scientific_knowledge/born-temperature-kms-factor-type-duality.md` §8;
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
   - **Remaining open core of this step:** the `J`-fixed profile is the lattice-summed theta;
     Poisson summation (`theta_4(x) = x⁻¹ theta_2(1/x)`, mathlib pointer:
     `jacobiTheta₂` functional equation) is the analytic brick converting the profile swap into
     the sector swap. And the KMS-categorical status: the duality relates `III_1` to type I off
     the fixed locus, so it is not normal there; with the doubled-rung identification the
     candidate is now precise — the grading-odd involution `J ⊗ (P ↔ 1-P)` on the one-rung-down
     welded system; its graded KMS classification is the step-4 target.
4. **Kill tests inherited:** diagonal action is Born-invisible (parent Theorem 5) — dead; scalar
   partition identity alone — dead; measured trace — dead; declaring FE a gauge symmetry —
   circular. The map must act on archimedean off-diagonal structure (constraint 4) and be
   non-normal off the fixed locus (constraint 5).
5. **Degenerate control:** drop the archimedean mode — the parent card proves no duality exists
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
