# Reboot-final: the Lean corpus condensed, and where it points

Status: 30 October 2026. **RH is open.** Sources: `formal/GaloisForLFunctions` only, read through the corpus research
tool, module docstrings and proofs, plus the four review-3010 files named in the task. No web search, no builds, no axiom
audits. Every claim below points to the companion log [`reboot-final-facts.md`](reboot-final-facts.md): sections G1–G19
hold the facts checked in source, section K holds the corpus condensed by object. Two small numerical checks are archived
in [`computations/2026-10-30-reboot-final-checks`](../../../computations/2026-10-30-reboot-final-checks/README.md).

| Label | Meaning |
|---|---|
| **K*n*** / **G*n*** | Fact-log section; each item there carries its Lean anchor and a [T]/[D]/[S] tag (title / docstring / proof read) |
| **(inference)** | This report's reading of several facts together; the facts are named and the step is stated |

---

## 0. Summary

1. **Method: condense first, interpret afterwards.** The corpus has 53,234 files and about 498,000 declarations. I
   collected the one-line statements (module docstring titles) of all 3,934 programme modules and filtered the 23,457
   `RHTower` titles. Through the research tool I queried the relations between them and read the decisive modules in
   source. The result is about 200 short facts grouped by mathematical object, not by programme (K1–K15). The picture
   below comes from those facts, not from an assumed shape of the solution.

2. **Three kinds of theorem.**
   - Reformulations: 1,718 `riemannHypothesis_iff` and 1,150 `riemannHypothesis_of` declarations.
   - Unconditional theorems that hold whatever the zeros do: positivity at bounded scale, uniqueness, no-gos.
   - A small classical core that actually constrains the zeros (G2, G12): the Vinogradov–Korobov region, Guth–Maynard
     density `30/13`, `≥ 67.25%` simple critical zeros, `4/5` of ordinates critical, `Σ(β−½) ≤ 0.066V`, anti-clustering
     of near-line zeros.

   No theorem of the second kind says anything about where zeros are. The corpus proves why (law L2).

3. **Twelve laws** recur across unrelated programmes (§2).
   - **L1** One invariant: every rate reads `Θ`, and one-sided bounds suffice.
   - **L2** Bounded scale is blind.
   - **L3** Detection is finite; exclusion must be uniform.
   - **L4** A counterexample must be crystalline near the top depth.
   - **L5** The primes are anti-crystalline.
   - **L6** Torsion of the circle carries both sides of the explicit formula.
   - **L7** Finite levels are positive; the limit loses the sign through a full-rank counterterm.
   - **L8** Zeros meet arithmetic modes only at boundaries.
   - **L9** The successor enters only through the archimedean place.
   - **L10** Quantization is everywhere.
   - **L11** Inside the strip there are only statistics.
   - **L12** Heat heals at rate `1/log T`.

4. **The picture (inference, §3).**
   - All finite arithmetic in the corpus is either positive and blind, or exactly rigid. Zeros enter only through limits
     (renormalization, horizon `N → ∞`, aperture `→ ∞`) and boundaries.
   - Positivity dies in the limit through a counterterm of full rank on the torsion orbits.
   - The undecided regime sits at one scale, doubly logarithmic in the height. At height `T` it is decided by primes up to
     a fixed power of `log T`.
   - A counterexample must be a crystalline or collapsed cluster of near-top zeros with tight twins. The primes that
     decide it have ℚ-independent logarithms, and the height `T` lies far below the Dirichlet bound `(Q+1)^d` (corpus) at
     which all `d` of their phases are guaranteed to align.

5. **Four solution shapes follow from the laws (§4).** None is a Weil-positivity statement.
   - **A. Pre-ergodic prime phases.** Exclude the crystals a counterexample needs by the Diophantine geometry of
     `(p^{iT})_{p ≤ (log T)^C}`.
   - **B. Depth at the horizon.** The zeros' real parts can reach a finite arithmetic box only through its boundary
     tail, which is Poisson-dual to the successor shells.
   - **C. A natural regularization.** Find a family of positive torsion energies whose counterterm is Hecke-covariant
     and of low rank.
   - **D. Reality invariants.** Jensen discriminants: reality-sensitive, and as yet undecidable.

   §6 lists the first theorems and the falsifiers.

6. **The two reports (§5)** read programme READMEs and stayed inside the positivity frame. They missed:
   - the classical core;
   - the hiding laws (what a counterexample must look like);
   - the horizon law (where zeros meet the arithmetic);
   - the survival law (exactly where positivity is lost);
   - the successor collar (how additive structure enters).

---

## 1. Method

- **Harvest.** For each of the 3,934 programme modules (outside `RHTower`, `HTGeometry` and the vendored folders) the
  docstring title was extracted. In this corpus the title is usually the theorem stated in one sentence ("The zeros meet
  the pole mode only at the horizon"). The 23,457 `RHTower` titles were filtered for unconditional and structural
  statements.
- **Relations.** Recurring objects (torsion, horizon, counterterm, crystal, successor, quantum, `Θ`) were queried with
  `scripts/formal_tools.py research`, and the returned statements were read.
- **Proofs read** where a law rests on them:
  - Weil cone uniqueness;
  - the fixed-overlap positivity assembly, including its capture lemma and residual budget;
  - the Hecke orbit kernel and pair-growth argument; fine towers;
  - the hiding laws and the counterexample specification;
  - archimedean domination;
  - the realization no-gos and the Hölder strip;
  - the survival law;
  - the de Bruijn–Newman strict bound.
- **Tags.** [T] means the fact is the module's own one-line statement and its proof was not read. Laws in §2 rest on at
  least two programmes and on at least one [D] or [S] item.

---

## 2. The laws

### L1. One invariant; growth equals depth; one side suffices (K1)

- **One number.** `TheWallsMeasureOneZeroWidth` proves that the deficit primitive, mean-square bands, formation energy,
  Abel exponents, lag family, CCM ground energy, heat time, window ceiling and node criticality all read
  `Θ = sup|Re ρ − ½|`.
- **Growth equals depth.** Independently, five programmes state that a growth rate equals the depth of the zeros seen:
  - packets (BSU);
  - cycles (AOG);
  - Krein–Langer pairs (HKT);
  - amplifiers (ART);
  - Lefschetz sequences (ACS).
- **One side suffices.** One-sided bounds are enough everywhere:
  - a packet bounded on one side sees no deeper zero;
  - one-sided Lefschetz bounds at one prime give the zero-free strip;
  - each half of the count is RH;
  - RH has a criterion on the nonnegative cone in which every term is a nonnegative functional, sharp at the constant
    profile (`riemannHypothesis_iff_forall_nonneg_cone`).
- **What the problem asks.** In this corpus RH is never a two-sided precision problem. It is a one-sided growth bound
  for one signed quantity, at exponent `½`.

### L2. Bounded scale is blind (K2)

- **Domination.** For every test of aperture `a`, ζ's Weil form is positive at heights where
  `log(1 + π|ξ|/4) > 10 + 68e^a + 2(sinh a − a) + O_f(1/|ξ|)`, and `L²`-coercive beyond an explicit height
  (`zetaZeroConfig_re_W_heightShift_pos_of_dominance`, `exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq`).
- **Unconditional positivity:**
  - through aperture `3/10` for every prime weight;
  - on windows up to `12/25`;
  - at most `|lowGrid(a)| + 1` negative directions at each aperture;
  - at every fixed overlap of the complete Weil matrix.
- **Blind by mechanism.**
  - The fixed-overlap margin is the synthesis tail, which equals the Weil weight `1/log N` at the critical overlap
    (G4, G9).
  - The Weil margin is `≤ Ce^{12L − πe^{2L−1/2}}` with or without RH (truncated Riemann kernel).
  - Window-averaged positivity holds for configurations with off-line zeros.
  - "A bounded aperture range certifies no rate at all."

### L3. Detection is finite; exclusion is uniform (K3)

- Every off-line zero is visible at some finite aperture:
  - finite off-line sets at a logarithmic aperture;
  - an attained top at a lag logarithmic in the separation;
  - near-top zeros at a polylogarithmic lag.
- Sparse explicit families decide RH: two-bump tests, single dyadic prime windows, one parameter.
- The corpus states the asymmetry itself: "any search for a counterexample is effective; any proof of criticality must
  be uniform" (`RefutationIsFiniteConfirmationIsNot`).

### L4. What a counterexample must look like (K4)

- **Hiding needs a crystal** (`TheHidingLaws`, `theFloorsRequireACrystal`).
  - An isolated off-line pair of depth `δ` in on-line mass `M` hides only up to lag `arsinh(M/|Q| + 1)/δ`.
  - Only infinite off-line lattices sustain hiding.
  - Mass buys aperture only logarithmically: reach `a ≤ log((3L+ℓ)/ℓ)/(2δ) + ℓ/2`.
  - Aliasing is free below Nyquist `ℓ/2` and ends exactly there.
- **Hiding is not monotone.** Adding off-line zeros can restore positivity: `exists_offLine_superset_hiding` gives
  `Z ⊆ Z'`, with `Z'` entirely off-line, `Z` negative and `Z'` positive at the same aperture.
- **For ζ specifically** (SRT, SSIC):
  - hiding up to the threshold forces uniform depth and crystalline spacing;
  - near-top zeros hide only in collapsed clusters;
  - isolated twins cannot hide;
  - twins are exponentially tight unless tripled;
  - lag positivity forces close companions.
- **Statistical limits on such clusters:**
  - near-line off-line copies obey anti-clustering, `Σ m_j² ≤ CT log T` (ShallowCauchyPrimeEnergy);
  - in every dyadic window, either `≥ 3/4` of zeros are critical or `≥ 17%` are simple off-line zeros within `A/log T`
    (G2).

### L5. The primes are anti-crystalline (K5)

- At a lag inside a crystal gap the crystal's response is a positive constant. ζ's prime phases are linearly independent
  over ℚ (`loggedPrimes_linearIndependent`) and align at some height, forcing negativity or exponential height escape
  (`crystal_gap_prime_torus_incompatibility`; "Kronecker–Bohr prime-phase realization and exponential height escape").
- `S(T)` is unbounded from prime-torus oscillation.
- Two prime towers see every ordinate difference at polynomial precision (Baker). The corpus formalizes Baker
  independence over `ℚ̄` and linear forms in prime logarithms (`RHTower/Matveev`, `BakerHomogeneousIndependence`).
- Dirichlet recurrence (pigeonhole): `d` prime phases can be brought within `2π/(Q+1)` of zero at some height
  `≤ (Q+1)^d` (`exists_fin_primeLog_phase_recurrence_quantitative`).

### L6. Torsion of the circle carries both sides of the explicit formula (K6)

- **Prime side.**
  - `I(m, mt) = φ(m)Λ(t)`: Λ is the intersection number of torsion orbits (a log-resultant of cyclotomic polynomials).
  - Weil's prime kernel is the renormalized limit of a positive torsion energy.
- **Archimedean side.**
  - Gauss's digamma theorem is the Fourier transform of the torsion energy on `μ_N`.
  - The `log N` in it is the anomaly of the multiplication map `[N]`.
- **Integrality and spectrum.**
  - The cyclotomic norm `≥ 1` gives a conductor-uniform floor.
  - Ramanujan sums diagonalize the prime matrix.
  - The prime-defect Dirichlet form has "the spectrum of the integers", `log m + Σ_{p|m} log p/(p−1)`.
- **Two energy problems.** Torsion is the stable equilibrium of the circle (Fekete). The corpus contrasts this
  directly: "on the zero divisor equilibrium is computed and stability is the open sign; on the circle both are
  theorems".

### L7. Finite levels are positive; the limit loses the sign through a full-rank counterterm (K7)

- **Survival law** (`TheRenormalizationSurvivalLaw`): positivity passes a scale limit exactly on the null cone of the
  counterterm, and that cone does not depend on the renormalization scheme.
- **The two places.**
  - The torsion (prime) germ has counterterm the identity, so nothing survives under any renormalization.
  - The archimedean germ has a rank-one counterterm and survives on the polar hyperplane (`counterterm_rank_dichotomy`).
- **Coupling does not help.** Coupling never lowers the torsion rank; a partner pays at most as many directions as the
  rank of its own counterterm, and the archimedean place pays one (`TheCoupledSurvivalLaw`). "Characters are invisible
  to polar matching."
- **Regulators tried:**
  - Abel (not Hecke-covariant, Hecke cocycle not a coboundary);
  - spacing (covariant, scalar counterterm, indefinite limit);
  - horizon (covariant; tensor counterterm equal to the identity on torsion orbits).
- **The corpus's own statement of what is missing:** "a covariant regulator whose counterterm has a nontrivial null
  cone".

### L8. The zeros meet arithmetic modes only at boundaries (K8)

- **The horizon law.** For the pole mode on `[1, N]`, the zero side is exactly the Euler–Maclaurin boundary:
  `Q(f_pole) = Re Σ_ρ m_ρ ĝ(γ_ρ)conj ĝ(conj γ_ρ)·B_N(1−ρ)B_N(ρ)`. "The zeros see the pole mode through the boundary of
  its horizon and through nothing else" (`ThePoleModeMeetsTheZerosOnlyAtTheHorizon`).
- **The boundary product splits in two:**
  - the pole parts give the Li charge `N/(ρ(1−ρ))`;
  - the remainder carries the Euler–Maclaurin tail, "whose Fourier expansion is the Poisson dual of the successor
    shells".
- **The charge is blind to depth.** "The horizon charge is blind to the real parts of the zeros":
  `|P_a(s)P_a(1−s)| ≤ N(Σ|a_d|/d)²/|s(1−s)|`. The zeros see every atomic vector only through its Möbius horizons.
- **Corollaries elsewhere.**
  - The quasimode residual of the complete Weil matrix is an `N`-independent boundary layer at `n ≈ N` (G9, G13).
  - "The shells and the pole cancel on the top band."
  - "Every unconditional input is separated from the error by the strip": inputs live at `Re s > 1` or on `Re s = ½`.

### L9. The successor enters only through the archimedean place (K9)

- **Mechanism.** Consecutive integers share no prime relation (`heckeIncidence k (k+1) = 0`). They interact only through
  the archimedean kernel, whose values there are algebraic:
  `archLevyDensity(log((k+1)/k)) = (k+1)√(k(k+1))/(2k+1)` (`TheSuccessorCollar`). Hence "the successor connection is the
  archimedean gauge field".
- **Blindness:**
  - an atomic archimedean spectrum blinds the successor (`successor_blind_of_atomic`);
  - the successor is invisible at zeros;
  - it enters the count only modulo the square-root class.
- **Yet it is necessary.** Ring structure (`gcd(n, n+1) = 1`) is what excludes Beurling systems and the golden datum
  (K13).

### L10. Quantization (K10)

- Index is even, and RH ⇔ index `≤ 1`.
- Transverse energy is `≥ 1` per off-line zero; RH ⇔ window energy `< 2`.
- Collision charge is even.
- Prime mass at the `√x` scale comes in even integer units.
- The prime mean is quantized height by height; local exponents are integers below half damping.
- Integer-valued positive-definite functions are characters.
- Integrality forbids super-conformal distortion.
- Integer quanta appear on both sides: arithmetic counts and zero multiplicities.

### L11. Inside the strip: statistics only (K11)

- The census (67.25%, 4/5, 88.76%) uses the second-moment Gram of the explicit formula.
- It is blind exactly at the coalescence of a pair with a double zero (G14).
- Its ceiling under full pair-correlation knowledge is `1 − 1/(3λ²) < 1` (G13).
- Density bounds count zeros and never locate them ("inside the strip only counts").

### L12. Heat heals at rate `1/log T` (K12)

- `0 ≤ Λ < 1/8`.
- For every `t > 0` only finitely many zeros of `H_t` are nonreal; all are real and simple beyond
  `2πe^{(1+√3/2+ε)/t}`.
- At height `t` the heat transfer is positive from time `100/log t`.
- An off-line zero of depth `δ₀` at height `γ` forces `Λ ≥ kkl(δ₀)/log γ`.
- At negative time, zeros are produced by an almost periodic Dirichlet-series model.

### Calibration facts used below (K13–K15)

- **Fakes.**
  - Λ-positive functions with the exact functional equation (even entire, at pole order 2) have off-line zeros.
  - The golden datum passes integrality, the functional equation, the λ-ring and the upper count. It fails unitarity,
    Bézout on its window surface, Riemann–Roch on its Rosati cone, positive-definiteness of its trace sequence, and the
    lower count.
- **Realizations.** Finite odd parts are impossible over ℤ; carriers indexed by zeros carry nothing beyond RH.
- **Over `𝔽_q`:**
  - square-root cancellation is a count;
  - the odd part is finite and spectral;
  - Frobenius is conformal, while the Hecke dilations of ℤ are isometric boosts.

---

## 3. What the laws say together (inference)

### 3.1 The finite level is positive; the information is in the passage to the limit

L2, L6, L7 and L8 describe one situation from four sides:
- every finite arithmetic object the corpus built is positive or rigid;
- the positive ones cannot see off-line zeros;
- the zeros appear when a finite level is taken to its limit, through the divergence of torsion self-energies (L7) and
  through horizon boundaries (L8).

A proof must therefore say something about how a finite positive structure passes through its limit. A better finite
form does not suffice. The corpus has three precise descriptions of that passage:
- the counterterm rank (L7);
- the horizon boundary (L8);
- the critical overlap where margin = synthesis error = `1/log N` (L2).

### 3.2 The problem lives at one scale, doubly logarithmic in the height

| Quantity at height `T` | Scale | Fact |
|---|---|---|
| Aperture where archimedean domination holds | `69e^a − 2a + 12 < log(1 + πT/4)`, i.e. `a ≲ log log T − 4.2` | K2: `horizonExponent(e^{2a}) = 10 + 68e^a`, `pairEnergy(½, a) = sinh a − a` |
| Aperture an isolated pair of depth `δ` can hide to | lag `v ≤ arsinh(M/\|Q\| + 1)/δ` at aperture `v/2`, with on-line mass `M ≍ log T`: `a ≲ log log T/(2δ)` | K2, K4: `theFloorsRequireACrystal`, `onLineMass` |
| Single-zero detector threshold | `e^{2δa}` beats `log T·poly(a)` | G10 |
| Critical overlap of the complete Weil matrix | `≍ log log N·(log log log N)²` | G9 |
| Heat time that makes height-`T` zeros real | `≈ (1+√3/2)/log T`; transfer positive from `100/log T` | K12 |
| Prime powers read by a test of aperture `a` | `n ≤ e^{2a}` | the Weil test `f * f̃` has support `[−2a, 2a]` (`prime_visible`, `RHTower/CCM/CCMRestrictedWeilPrimePoleMatrix.lean`) |
| Height escape in the crystal-gap obstruction | `log(1 + 2π\|ξ\|) > (B − 2e^a‖g‖₁² − O_g(1))/‖g‖₂²`, with `B` below the prime envelope over `p ≤ e^{2a}`; both are of order `e^a`, so again `a ≍ log log ξ` (inference from the statement) | `crystal_gap_prime_torus_incompatibility` |

**Inference.**
- Domination decides apertures up to about `log log T`. A pair of depth `δ < ½` hides up to about `log log T/(2δ)`.
  For `δ` near `½` the window closes; for shallow pairs it is wide.
- In between, neither mechanism decides anything. Tests in that window read primes from about `(log T)²` to
  `(log T)^{1/δ}`.
- So, at height `T`, the corpus has localized the undecided question to the joint behaviour of the phases `p^{iT}` for
  primes up to a fixed power of `log T`.
- The heat and critical-overlap scales are the same scale in other coordinates.

### 3.3 The shape of a counterexample is known, and it is the opposite of what the primes allow

L4 and L5 together give a specification:
- A counterexample must be crystalline near the top depth: uniform depth, periodic spacing, collapsed clusters,
  exponentially tight twins.
- The prime phases that would have to support such coherence are linearly independent over ℚ (and over `ℚ̄`, by Baker).
- Their coherence is guaranteed only at heights `≤ (Q+1)^d` for `d` phases.

At height `T`, the window primes number `d ≈ δ(log T)^{1/δ}/log log T`, far more than `log T`. Those heights are far
beyond `T`. The flow `t ↦ (t log p mod 2π)_{p ≤ (log T)^C}` is observed at height `T` long before it has explored its
torus. Call this the pre-ergodic regime. The corpus's Kronecker obstruction leaves exactly one escape, "exponential
height escape", and the question is whether that escape is compatible with the hiding laws at heights `≤ T`.

### 3.4 Additive structure: blind in the bulk, present at the boundary

- **The puzzle.** L9 says the successor is invisible to atomic (zero) spectra and enters the Weil form only through the
  archimedean kernel. K13 says ring structure is nevertheless indispensable, since multiplicative data alone cannot
  exclude Beurling systems.
- **The resolution in the corpus's own statements is L8.** The depth-blind part of the horizon is the charge
  `N/(ρ(1−ρ))`. The only other part is the Euler–Maclaurin tail, Poisson-dual to the successor shells. Whatever a finite
  box `[1, N]` can know about the real parts of the zeros through its pole mode therefore passes through the successor
  structure of the integers at its upper edge (inference by elimination from the two docstrings).
- **On the top band** "the shells and the pole cancel". Along the top-band witness `b + η·1_T` of the complete Weil
  matrix, the `c`-linear parts of the shell and pole moments are the same lattice-free quantity, and the joint
  coefficient is `O(G(log N + c + 1))` uniformly in `N` while each term is `≍ Gcq log N`
  (`exists_abs_jointWitnessCoefficient_le`). This is a prime-side statement on the same band `n ≈ N` whose zero side the
  horizon law identifies with `B_N` (inference: same band, two sides).

### 3.5 What is missing, in the corpus's own words

| Missing input | Where the corpus states it |
|---|---|
| A covariant regulator whose counterterm has a nontrivial null cone | `TheSpacingRegulatorRemovesTheAnomaly` |
| A carrier built independently of the zeros, such as "a category with ζ as one member among many" | `DeningerResolventCoreIsRiemannHypothesis` |
| Reality-sensitive invariants that are decidable (Jensen discriminants) | `DiscriminantIsRealitySensitive` |
| An input inside the strip that is not a count | `ContourCrossingObstruction` |
| Uniformity in the unbounded parameter (aperture, overlap, horizon, rank) | L2, L3, G4, G9 |
| Signed close prime pairs past bandwidth one | G3 (TTPC) |

---

## 4. Solution shapes the facts suggest

Each shape combines corpus facts that no programme has combined. For each, the needed statement is new information
about ζ, not a relabeling of `Θ = 0`.

### A. Pre-ergodic prime phases: exclude the crystal

- **Facts used.**
  - L4: the hiding laws, the counterexample specification, collapsed near-top clusters, tight twins.
  - L5: Kronecker obstruction with height escape, Baker independence, Dirichlet recurrence `(Q+1)^d`.
  - §3.2: the undecided window, primes up to `(log T)^{O(1)}`.
  - K4: near-line anti-clustering.
- **Needed statement.** At heights `≤ T`, the phase vector `(p^{it})_{p ≤ (log T)^C}` cannot realize the coherent pattern
  that a hiding crystal of depth `δ` requires in the window `[log log T, log log T/(2δ)]`, except on a set of heights too
  sparse to carry the infinite lattice that hiding needs.
- **Why it is new.**
  - It is a statement about the Diophantine geometry of a linear flow on a torus whose dimension grows like a power of
    `log T`, observed well before its recurrence time.
  - It is neither positivity nor an average. Random models (equidistributed phases) and `𝔽_q` (one Frobenius, rank-one
    phases) both lack this regime.
- **Known bottleneck (corpus, inference).**
  - Pigeonhole gives alignment only at heights exponential in the number of phases.
  - Baker gives qualitative independence.
  - The quantitative form needed is a lower bound for linear forms in `d ≍ (log T)^C` prime logarithms. The corpus's
    `RHTower/Matveev` layer is where its dependence on `d` would be decided.

### B. Depth at the horizon: the boundary tail and the successor shells

- **Facts used.**
  - L8: the horizon law; the charge is blind to depth; the tail is Poisson-dual to the successor shells; shells and pole
    cancel on the top band; the universal boundary layer.
  - L9: successor pairs couple only through the explicit algebraic archimedean kernel.
  - K1: the Li charge and the first sixty-eight Li coefficients.
- **Needed statement.** An exact description, as `N → ∞`, of the top-band residual after the shell–pole cancellation, as
  a functional of the zeros. Then a sign, or a rate, for its dependence on `Re ρ`.
- **Why it is new.**
  - It places RH in the additive structure of integers near a cutoff: consecutive integers near `N`, their factorizations
    against the archimedean kernel.
  - That is the one place where the corpus proves the successor is not blind.
  - It is not a positivity statement on a test space.
- **Falsifier.** If the tail is also blind to `Re ρ` at leading order, then no finite box sees depth through its pole
  mode. That would be a sharp new no-go, to be recorded with its exact order.

### C. A natural regularization with a low-rank counterterm

- **Facts used.**
  - L6: both sides are torsion energies; the torsion equilibrium is stable.
  - L7: the survival law; the counterterm dichotomy; the coupled law; the regulators tried.
- **Needed statement.** A family of positive energies of an arithmetic origin with three properties: it converges after
  renormalization to the Weil form; its counterterm is Hecke-covariant; it has a nontrivial null cone containing the
  polar-neutral tests.
- **Caution (from the survival law, inference).** For an arbitrary family this is tautological: by Finsler–Debreu such a
  family exists exactly when positivity holds on the null cone. The content is the naturalness requirement. The corpus
  shows that the circle's torsion germ, its character twists and its coupling to the archimedean germ all fail it.
- **Where to look, by the corpus's own exclusions:**
  - families not built from the circle alone (K14: "a category with ζ as one member");
  - regulators that couple different torsion orbits, so that the divergence is not diagonal.

### D. Reality invariants

- **Facts.**
  - `DiscriminantIsRealitySensitive`: discriminants of Jensen polynomials refute real-rootedness by a polynomial in the
    coefficients, with no contour and no spectrum.
  - The Jensen polynomials of `ξ` satisfy Laguerre's inequality on the half-line (ALG).
  - Heat repairs finite heads of `ξ` at every large height (ALDG).
- **Needed statement.** Decidable nonnegativity of these discriminants for all indices. The corpus records that this
  category is "not empty but hard".
- **Ranking.** Listed for completeness; the corpus contains no new mechanism here.

---

## 5. The two reports against the compiled picture

| Report claim | Compiled picture | Fact |
|---|---|---|
| Opus: "positivity proofs with margin cannot exist; estimates are the wrong instrument" | Margins exist at every bounded scale (L2), and the only zero-constraining theorems are estimates (K11, G12). The cone theorem fixes the weights and leaves the form's sign open. | G1, G9 |
| Opus: cone uniqueness is "the only global theorem" and points to modular potential theory | Its family vanishes at every zero wherever it lies, so it is a uniqueness theorem. Automorphic a priori information certifies only `Re ρ ≥ 1`. | G1, G6 |
| Opus: "prime-free" RH | The node set must contain every prime power: the weights disappear, the primes do not. | G1 |
| Opus: `WindowPositive` on `(0, log 2)` as a first target | A short-window inequality for nonnegative tests. The RH criterion on a nonnegative cone (Doob coordinates) is a different object. | G5, K1 |
| Opus: `𝔽_q` "has room" | The actual curve sits on the boundary of the cone (finite rank). What differs is the finite odd part and conformal Frobenius. | G11, K15 |
| Astra: fixed-overlap positivity is "real progress" | True positivity that is blind by mechanism; its margin is the synthesis tail. | G4, G9, L2 |
| Astra: nonlinear theta readings and heat as the main alternatives | CDG computes the divisor wherever it is. Heat heals at `1/log T`, and this is the same scale as §3.2. | K12 |
| Both: the walls as obstacles to cross | The corpus proves what a counterexample must be (L4) and what the primes forbid (L5). Neither report uses this. | K4, K5 |
| Both: no use of the horizon law, the survival law, the successor collar or the doubly-logarithmic scale | These carry the picture of §3. | K7–K9 |

**What both got right and the picture keeps:**
- Astra: the order of quantifiers decides; enlarging fixed coordinates adds nothing.
- Opus: cone uniqueness means any positive weight already forces RH; the selective structures are the pole, the Gamma
  factor and the successor.

---

## 6. Research programme

The corpus's rule for a no-go applies throughout: if a package fails, extract and record its strongest positive
statement.

### WP-A. Pre-ergodic prime phases (shape A)

- **A1. Fix the window.** From `theFloorsRequireACrystal`, `TheHidingLaws`, `exists_height_horizon_…` and
  `horizonExponent`, prove with explicit constants the aperture interval in which an isolated pair of depth `δ` at
  height `T` is neither excluded by domination nor detected. Also prove which primes the tests in that interval read.
- **A2. Crystal versus anti-clustering.** Combine `uniform_crystal_of_hiding` with the shallow-zero anti-clustering
  (`Σ m_j² ≤ CT log T`) and fixed-σ density `o(T)`. Prove which crystal parameters (depth, spacing, background mass)
  are excluded unconditionally at height `T`. This needs no new input and gives the first unconditional theorem about
  the shape of off-line configurations of ζ.
- **A3. Coherence of short prime phases.** Prove an upper bound for the measure of heights `t ≤ T` at which
  `(t log p mod 2π)_{p ≤ X}` lies within `η` of a crystalline pattern, for `X = (log T)^C`. Start with what pigeonhole
  and Baker give in `RHTower/Matveev`. Record exactly where the dependence on the number of logarithms stops the
  argument.
- **A4. Close the loop.** Show that the coherence a hiding crystal needs in the window (A1) exceeds what A3 allows below
  height `T`, for some range of depths.
  - Success, even for `δ` in a restricted range, is a new zero-free statement.
  - Failure, recorded with its exact exponent, says how much quantitative transcendence RH needs in this regime.

### WP-B. Depth at the horizon (shape B)

- **B1.** Split `weilQuad_poleMode_eq_tsum` into the charge part (blind to depth, `TheHorizonChargeIsBlind…`) and the
  tail part. Prove the tail's exact expansion as successor shells (Poisson duality).
- **B2.** Compute the `N → ∞` asymptotics of the tail contribution of a single off-line pair `{ρ, 1−ρ̄}` of depth `δ` at
  height `γ`. Does it grow like `N^{δ}`, oscillate, or vanish?
- **B3.** Write the `O(G(log N + c + 1))` residual left by the top-band cancellation
  (`exists_abs_jointWitnessCoefficient_le`) and the Mertens boundary profile `R(e^u)` (G13) as one operator in
  `u = log(N/n)`. Through the horizon law, express that operator's zero side via `B_N(ρ)B_N(1−ρ)`.
- **Falsifier.** B2 returns no depth dependence at leading order. Record it as the no-go "finite boxes see depth only
  beyond the pole mode", together with the next mode that does.

### WP-C. Natural regularizations (shape C)

- **C1.** On finitely many torsion orbits, classify the Hecke-covariant positive families of arithmetic origin. Use the
  orbit energies, their gcd twists and their couplings across orbits; record the counterterm rank of each. This is a
  finite-dimensional problem, and `survivalCone_eq_of_regularized` makes the answer scheme-independent.
- **C2.** Test whether a family that couples distinct orbits (off-diagonal divergence) can have a counterterm of rank
  below the number of orbits while its limit is still the Weil prime kernel.
- **Retire when:** every natural family has full rank. The positive survivor is then the classification itself.

### WP-D. The statistical support (L11)

- Keep the zero census as the instrument that produces zero-constraining theorems.
- Its open input past bandwidth one is the centred stabilizer discrepancy of TTPC (G3).
- WP-A2 depends on these statistics (anti-clustering, density).

### WP-E. Corpus hygiene

- Every new module that states an RH equivalence or a positivity theorem also states:
  - its `Θ`-reading (L1);
  - the scale at which it sees a pair at depth `δ` and height `T` (§3.2);
  - whether its statement constrains zeros unconditionally.
- Equivalences whose right-hand side quantifies over the zero set are labelled as relabelings (186 found, G19).

---

## 7. What would change this picture

- A theorem from a positivity, rigidity, gauge, Hodge or realization programme that constrains zero locations
  unconditionally. That would refute L2's reading.
- A configuration that hides from all tests of aperture up to `C·log log T` at height `T` without crystalline structure.
  That would refute L4.
- A finite-level object, not a limit, whose sign is RH-sensitive. That would refute §3.1.
- An expansion of the horizon tail that is blind to `Re ρ`. That would close shape B and move the boundary question to
  the next mode.
