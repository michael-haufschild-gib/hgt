# Fable review 2410: the walls, what could go around them, the field they ask for, and route WD

Scope. This review reads the five review-2410 reports (frontier map, killed routes, route-unification
ledger, hard obstacles, walls ledger) and the fifteen programme READMEs (APT, BSU, THIM, BVI, ACT,
SRT, AIP, ACCE, SSIC, ACCC, ACS, SAEI, TTPC, AOT, AOG), then checks the claims that matter against the
Lean corpus with the corpus search tool. It answers three questions: (1) is there a proof mechanism
that circumvents the walls; (2) if the walls are questions for which mathematics lacks tools, what
field would supply them; (3) the same two questions for route WD. The research log is
`logs/fable-review-2410-research.log`. No builds were run.

Evidence labels. `[L]` a Lean declaration located by search in this review and read in source
(name given, module in the evidence index). `[S]` a statement of a report or README that names its
Lean source but was not re-read here. `[P]` paper-level or heuristic content of the corpus. `[F]`
this review's own proposal or judgement.

---

## 0. Verdicts

1. There is no mechanism in sight that goes around the walls. The three wall families are three
   projections of one missing input: a **signed, single-scale, successor-selective** estimate on the
   actual Möbius or prime source at the square-root scale. Every exit the corpus has built (a rate,
   a quantized index, a transport in aperture) is proved to reduce to this input, and the first
   output of that input in any receiver is a fixed zero-free strip (quasi-RH), never RH directly.
2. The corpus has, however, isolated the input so sharply that six concrete openings exist where it
   could first enter with less than full strength (Section 2.3). All have quasi-RH as their first
   rung. None is circular, and two (the balanced cross-scale Gram, the interior-martingale
   contraction) are finite, explicit inequalities.
3. The field the walls ask for is not a new set of objects (the corpus has already built every
   object a Weil-type proof needs, and has proved that all of them are formal on impure models). It
   is a new **source of positivity**: an enumerative, sign-reading arithmetic of the successor
   `n ↦ n+1` in which cancellation is a count. Section 3 gives its charter, objects, language,
   principles, acceptance criteria and research programme, and says which parts already exist
   (correlations of multiplicative functions; Kloosterman and spectral bilinear forms; Arakelov and
   `F₁` geometry) and what would be new.
4. Route WD does not circumvent the walls. Its distinctive asset is a quantized endpoint and a
   **two-threshold structure**: the WD heat threshold `λ_WD` sits strictly between `0` and the
   de Bruijn–Newman constant `Λ` whenever RH fails, and `RH ⟺ λ_WD = 0 ⟺ λ_WD = Λ`. Its first
   rung is the constant in the Ki–Kim–Lee-scale positivity law: the corpus has `(17/25)/log t`, and
   anything below the detection constant `κ₀(δ₀)/log t` for one fixed `δ₀` is a zero-free strip.
   The field WD asks for is an oriented heat theory of divisor currents with arithmetic labels
   (Section 4.4).

---

## 1. What the corpus has settled (the load-bearing facts)

The answers below depend on a small number of facts that the corpus has proved or stated sharply.
They are collected here once.

### 1.1 Receiver completeness

The six ζ-receivers (spectral zero width, zero abscissa, Möbius damping, Liouville damping, ξ
half-plane, Suzuki formation) have the same width object and are admitted at the same rates:
`widthFunctor_obj_zetaReceivers_eq`, `categoricalGradedWidthDictionary_tfae` [L]. The Möbius
receiver's damping rate is exactly the zero width, `receiverDampingRate_eq_zetaZeroAbscissa_sub_half`
[L], and RH is cofinal admission, `riemannHypothesis_iff_cofinal_budget` [L]. The unification ledger's
Claim 6, "no reviewed theorem requires a new field", is correct at the level of objects: every
reformulation is exact and isomorphic to the unknown `1/ζ(s+ε)` beside the line (THIM 3.18: "the
receiver reads the size of the weight's own Dirichlet series beside the line, at every height").

### 1.2 The three classes of laws, and the one selective estimate

THIM sorts every conservation or dissipation law of the sieve theories into three classes
(`selectivity_class_I_beurling_universal_laws`, `selectivity_class_II_signBlind_and_parityOrbit_laws`,
`selectivity_class_III_bezout_successor_selective_laws` [L]):

- Class I (Beurling-universal): Möbius inversion, Euler products, Buchstab splits, Gibbs
  log-submodularity. They hold in Beurling systems with off-line zeros and cannot see RH.
- Class II (sign-blind): every complete-period quadratic form, lag covariance, the diagonal Vaughan
  entries. They take the same value on a parity pair (`parity_barrier`,
  `receiverBounded_amplitudeInvariant_iff` [L]: sign-blind data decide the receiver iff `ε > 1/2`).
- Class III (Bézout-selective): laws driven by `gcd(n, n+1) = 1` and `pa − qb = 1`. These are
  identities and classifications, not estimates.

The only unconditional estimate in the corpus that is selective against Beurling systems is the
Vinogradov–Korobov band of admitted dampings, `1/2 − κσ(T)/(480 log T) ≤ ε ≤ 1/2`
(`exists_receiver_le_on_vinogradovKorobovBand`, `shiftedPair_and_vkBand_selectivity` [L]). BVI
attributes its extra width over the de la Vallée Poussin band, which is the most a Beurling system
can guarantee, to Vinogradov's mean value theorem, that is, to the additive structure of `ℕ`.

### 1.3 Two sources of positivity, both at rate 1/2, both nonselective

Every proved positivity in the corpus is paid by one of two sources.

- The archimedean place. APT's complete critical form is positive on every high dyadic block, and
  the README states that all of it is paid by the archimedean gain `log M`, so the statement is
  nonselective by construction (APT 3, 7.2). ACS proves the Hodge defect of ζ finite at every
  aperture, the archimedean collar paying everything above the frequency horizon, leaving a
  finite-dimensional low-frequency sector per aperture [S].
- The zero-free region. Every receiver floor is of order `e^{r − c√r}` or `e^{r − cσ(r)}` (APT, ACT,
  AIP, ACCC), and BVI 3.15 proves the band of admitted dampings is the zero-free region in both
  directions: a band of fixed width below `1/2` would be a zero-free strip.

### 1.4 The obstruction is quantized

The corpus has turned RH into the vanishing of integer-valued or quantized invariants:

- `RH ⟺ ∀T, xiHorizontalCollisionCharge T < 2`
  (`riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two` [L]); the charge is
  `Σ_ρ ord(ρ)·(horizontalMultiplicity(Im ρ) − ord(ρ))` over strip zeros in the window.
- The Hodge defect counts distinct right zeros: the positive index of the intersection Gram over a
  Hecke orbit of a spectrally generic test is `≥ 1 + n` iff `n ≤ #(right zeros)`
  (`zeta_cyclic_hodgeDefect_iff` [L]); the defect is cyclic on one orbit and two primes suffice [S].
- Across a collision of a simple reflected off-line pair with a critical-line zero of multiplicity
  `r`, off-line charge `4r + 2` converts entirely into multiplicity charge and the total horizontal
  excess is conserved (`HTGeometry.HorizontalCharge.collision_transfer` [L]).
- A multiplicative sign pattern is paid below half damping only at logarithmic prime mean in
  `{0, −1}`, at every height; the residue-flip quarter law has threshold exactly `1/4` [S, THIM 3.18].
- All translated moments of a divisor row determine it up to one involution, the half-period
  companion (`sameRelationSpectrum_five_six_iff` [L]).
- The node-divisor Euler characteristic of the receiver is `e^s + s − 1 − ψ(e^s)`, the two-pole
  Chebyshev defect [S, AOT/ACS].

### 1.5 The obstruction is localized

Each programme has located where RH can fail, and the locations agree:

- prime anti-diagonals `|x| + y = log n` (ACT: `riemannHypothesis_iff_forall_prime_variationInequality`
  [L]; "RH is a statement about the prime anti-diagonals");
- prime-sum frustration edges, with the lattice ledger balanced (SAEI/AOT: "frustration is a
  continuum phenomenon");
- the off-diagonal entries of the 25-entry signed Vaughan Gram (THIM/BVI: the diagonal is
  sign-blind);
- the Bézout interior martingale after canonical compensation (BVI 3.8: "the whole obligation is one
  signed term", `pmInterior_strict_contraction_iff_bounded_energy` [L]);
- close prime pairs beyond the Montgomery–Vaughan threshold, `T < m ≤ T^{4/3}`, `h ≪ m/T` (TTPC);
- the single-modulus statistics of the actual rows at balanced scales `P ≍ Q` (BVI 3.13);
- a finite low-frequency sector at each aperture (ACS), and collapsed off-line clusters escaping to
  height (SRT, ACS: `zeta_near_top_cluster_collapse_of_offLineCopiesLocallyBounded` [L]).

### 1.6 No finite certificate; cofinality; height escape

Finite data of every kind admit off-line extensions (killed-routes: packets, apertures, moment lists,
jet orders, Gram tests). Bounded-aperture certificates have width resolution limit `1/2` in every
unit (`resolutionLimit_width_aperturePositivity`, `apertureResolutionJump` [L]). The golden datum
`q = 5`, `1 − 5X + 5X²` passes every finite battery and is impure
(`selectivityBattery_goldenDatum_nonObject`, `goldenDatum_beurling_not_pure` [L]); for every `n`
there is a curve datum with `|β| > 1` passing all lag tests up to order `n`
(`functionField_vs_goldenFakeCurve_and_windowHiding` [L]). Any proof must be cofinal and use
infinite information.

### 1.7 The two-sided cusp

On-line zeros force the damped Báez-Duarte residual to approach its infimum no faster than linearly
in the damping, with constant `1/(4|ρ|²)` from a critical zero
(`exists_criticalZero_linear_dualResidual_floor` [L]); off-line zeros force unboundedness. The
readout–energy uncertainty principle `κ R(c)² ≤ (log N − κ) Q^{ec}(c)` is an unconditional floor
(`exists_readout_energy_uncertainty` [L]). The receiver has no intermediate regime: across the
polynomial gap `T^{1−2ε}` a prefix bound and subpower energy are each equivalent to admission
(THIM 3.20).

### 1.8 The first rung is quasi-RH and it is reachable by a rate

Short-window power savings for Möbius or primes are equivalent to `Θ < 1`
(`moebius_and_prime_powerWindowSaving_iff_quasiRH`, `moebiusPowerWindowSaving_iff`,
`primePowerWindowSaving_iff` [L]); a fixed-width admitted band below `1/2` is a strip (BVI 3.15);
a formation-energy exponent gives `Θ ≤ 1/2 + r/2`
(`zetaZeroAbscissa_le_of_suzukiCompletedFormationEnergy_le_rpow` [L]). The walls ledger's entry
barrier is therefore exact: any route whose first output is a rate produces quasi-RH first.

---

## 2. Question 1: a mechanism that circumvents the walls?

### 2.1 What "circumvent" can mean

A route can leave the wall system through exactly three exits, and the corpus has mapped each.

- **Exit by rate.** Produce an unconditional bound at a fixed rate `σ < 1/2` in any width-reading
  receiver. By 1.8 the first output is `Θ < 1`. This is the ladder, not a circumvention; but it is
  the only exit whose first rung is a recognizable theorem.
- **Exit by index.** Prove a quantized endpoint (1.4) vanishes by computing the integer in a second,
  independent way. The corpus's index formulas evaluate to the Chebyshev defect
  `e^s + s − 1 − ψ(e^s)` or to a count of right zeros; the "section count" direction is blocked by
  the universal floor law (ACS: any ample cone of nonnegative ample degree has Riemann–Roch iff the
  open positive cone is contained and the defect is nonnegative; no section construction escapes
  the floor) and by the master equivalence `scalingSurface_hodgeIndex_iff_heckeStable_effectivity`
  [L], which makes Hecke stability of the open positive cone at the single prime `2` equivalent to
  RH. The index exists; its independent computation is the arithmetic input again.
- **Exit by transport.** Pay the finite low-frequency sector uniformly in aperture by a monotone
  quantity. The corpus proves the restricted Weil ground energy `μ(A)` is antitone with the
  compulsory ceiling `μ(A) ≤ K exp(11A/2 − π e^{2(A−2)})`, that monotonicity of a ceiling-scaled
  Lyapunov quantity would give RH (AOT/ACCE), and that no Lyapunov identity with a sign-definite
  jump is known in aperture (ACT open problem). The search found only abstract Grönwall forms
  (`monotoneOn_exp_mul_of_relative_decay` [L]) and a Sonin-type rate definition; nothing for ζ.

All three exits meet the same input. This is not an accident of the receivers: THIM's class theorem
says any bound on the actual receiver must use Class III structure, BVI's test says a mechanism that
sees RH must use Bézout structure somewhere, and SRT shows the one place a Beurling system differs
from `ℤ` is the integrality `|log(A/B)| ≥ 1/max(A,B)`.

### 2.2 Verdict

No. The walls are not artifacts of the receivers but of the available inputs. What the corpus has
achieved is to replace "prove RH" by "prove one signed, single-scale, successor-selective estimate,
in any of a dozen exactly equivalent coordinates", and to show that the first thing such an estimate
produces is a zero-free strip. The honest research deliverable is quasi-RH in receiver coordinates
(Section 2.5).

### 2.3 Six openings where the input can enter with less than full strength

These are the places where the corpus's own results make the missing input a finite, explicit
statement. Each is given with its first rung and with what it would and would not buy.

**A. Kloosterman reciprocity in the balanced cross-scale Gram (BVI 3.13, 7.4, 7.8.1).** The
energy-centred pronic Gram between a small-scale prime row (`p ∼ P`) and a large-scale row (`n ∼ Q`)
is rank two plus a remainder that is exactly a bilinear form in the Kloosterman fractions
`k q̄/p` with cosecant–Bernoulli weights (`bernoulliKernel_eq_reciprocity` [S]). The dual norm
`Σ_{p ∈ S} |Λ_p(c')|/p` is one linear statistic per small modulus with no bilinear structure left.
The actual Möbius and centred prime rows already beat the generic Type-II and large-sieve bounds
qualitatively on every range, the balanced range included [S]. Opening: apply Weil's bound and the
Kuznetsov/Deshouillers–Iwaniec spectral theory to the Kloosterman form at balanced scales, without an
external modulus or character average. What it would buy: BVI proves that a power saving in the
short-window mean square at a fixed window exponent is `Θ < 1`, so the ceiling of this opening is
quasi-RH; but the equivalence quantifies over window exponents and BVI states explicitly that it is
not a theorem that every Gram improvement is the strip. A Gram improvement at balanced scales that is
not a short-window power saving would be new relative to the walls ledger. First rung: quasi-RH.
Why it is not circular: Weil's bound is a genuinely additive input (square-root cancellation from
the geometry of a curve over `F_p`), selective against Beurling systems, and sign-reading at the
level of residues modulo `p`.

**B. A quantitative Class III law for the interior martingale (BVI 7.2, THIM 7.8.4).** After
canonical compensation the receiver energy is one signed term, and admission at a fixed `ε < 1/2` is
the coercive contraction `2M^{int}_T + 2·Counterterm·H^{comp}_T ≤ (1−δ)E_T + C_ε`
(`pmInterior_strict_contraction_iff_bounded_energy` [L]). Keeping the signed sum over interior moduli
collapses its conditional drift to Selberg coordinates on the divisors of the jump modulus,
radical-invariant and absolutely summable (`sum_Icc_mul_interiorJumpOrbitMean_eq_selbergMultiplesCoord`
[S]). The Class III laws that act here (zero-diagonal pronic Abel summation, `(2r−1)`-step shell
midpoint annihilation, the conditional jump-orbit mean classification, the least successor seed) are
identities. Opening: give one of them an exponent. The concrete finite problem is the hypercube
Dirichlet form of the dilation profile, nonnegative for all `ε` (`hypercubeDilationDirichletForm_nonneg`
[L]) and bounded uniformly in the squarefree cutoff `P` for `ε > 1/2` only; BVI 7.5 identifies its
uniform bound for `ε ≤ 1/2` as the finite form of `ζ(1+ε)·ζ(1+ε)^{-1} = 1` that the receiver needs.
Its entries are dilation profiles `Φ_r(d₁/d₂)`, pairings of two integer jump streams whose gaps are
the solutions of `pa − qb = h`, so the object is Class III. First rung: a bound at one fixed
`ε < 1/2` on this form, which by the band laws is again quasi-RH strength.

**C. The index exit: an independent count for the collision charge or the Hodge defect (AOG, ACS).**
What a circumventing theorem would have to look like is now exactly specified by the corpus. It must
be a second formula for an integer the corpus already identifies with the number of distinct right
zeros (or with the collision charge), in which the integer is manifestly bounded (by `0`, or by `1`
for the charge) because it counts arithmetic objects. AOG names the missing object: arithmetic
sections, an arithmetic `h⁰`. ACS proves `h⁰ ≥ dim W − #primePowerNodes` and that the degrees of
freedom minus node count is the two-pole Chebyshev defect [S], which is a lower bound on sections in
the direction that does not help. The candidate counting objects the corpus has built are: solutions
of `pa − qb = 1` (least successor seeds, `leastSuccessorSeed_spec` [L]); Bézout shells; the integer
lattice of the prefix matrix (unimodularly `diag(1,…,n)`, cokernel `∏ ℤ/j` [S]); the Witt ghost
coordinates in which the sieve receiver is a finite-cutoff truncation of the Big-Witt ring [S].
Opening [F]: look for a count `h(A)` of successor incidences at aperture `A` with (i) `h(A) ≥ 0` by
construction, (ii) an exact identity `h(A) = (Hodge defect at A) + (explicit nonnegative term)`, so
that the defect is forced to zero. The corpus's collision transfer law (1.4) is the model: off-line
charge is converted into multiplicity charge with a conserved total. First rung: even a count that
bounds the defect by a fixed integer would give finiteness of off-line zeros in a strip, which is
quasi-RH strength again, but by a route that has never been tried.

**D. Transport in aperture as a renormalization problem (AOT, ACCE, ACT).** The aperture spectral
jump telescopes, `RH ⟺ HasSum of jumps = μ(A₀)` [S], the jump is a boundary shell flux, and the
ceiling forces any positive floor to decay doubly exponentially. Opening [F]: treat `A ↦ μ(A)` as a
renormalization-group flow whose beta function is the shell flux of primes with `log p` in the
shell `(2A, 2A + dA)`. RH is "the flow never crosses zero" (AOT no-crossing law). The corpus's
constraint on any such law is precise: the flux bound must be compatible with the doubly-exponential
ceiling, so a crude bound of the form "flux ≤ C·μ(A)" is impossible; the law must be relative
(`−μ' ≤ β' μ` with `β` the ceiling rate, `monotoneOn_exp_mul_of_relative_decay` [L]). A Beurling
system with an off-line zero has a flow that crosses zero at the aperture where the zero becomes
visible, so the beta function must be Class III: it must read the signed prime-pair correlation in
the shell. First rung: a relative flux bound on an interval `(a₀, c]` gives `Θ ≤ 1/2 + a₀` (ACCE,
`riemannHypothesis_of_signedWork_single_sign_change` [L] for the damping analogue).

**E. A separating observable with an exponent (THIM 7.8.1, BVI 7.8.4).** Parity pairs are separated
by the logarithmic moment hierarchy and the von Mangoldt readout, which carry no exponent. The
readout–energy uncertainty principle is a floor, `κ R(c)² ≤ (log N − κ) Q^{ec}(c)`. Opening: a
ceiling of the same shape, `E_T(c) ≤ F(T)·(separating functional of c)² + (sign-blind term)`, would be
the first sign-reading estimate. The corpus shows exactly which functionals separate (first pronic
moment at prime powers; `M(c log^k)` at moduli with `≤ k+1` prime factors; the pole value
`K(1−ε)` and its Taylor coefficients) and that blindness is closed under post-processing, so the
ceiling cannot be assembled from amplitudes. First rung: a ceiling on the Vinogradov–Korobov band
that improves the band's width would already be a new zero-free region.

**F. The coalescent prime surplus (TTPC).** The 3/4 proportion needs `primeSurplus ≤ 1/18`, a signed
bound on `Σ Λ(m)Λ(m+h) K(Th/m)/m` for `T < m ≤ T^{4/3}`, `0 < h ≪ m/T`. This is the one place in the
corpus where the needed statement is a classical additive conjecture at a stated strength (a
Hardy–Littlewood-type correlation on average over short shifts), and the five-model calibration
shows the Hardy–Littlewood deficit has the favourable sign (`−1/144`). It is not an RH mechanism, but
it is the cleanest test bed for any new signed-correlation tool: the same input, if it existed at
power-saving strength, would also drive openings A and B.

### 2.4 What cannot work (so it is not retried)

- Interpolation or log-convexity in the damping. The damping is a self-adjoint contraction semigroup
  only in the coefficient-`ℓ²` norm of Dirichlet series, which is the sign-blind norm (finite iff
  `ε > 1/2`); in the receiver norm the residue modes are Bessel, not Riesz [S], and Phragmén–Lindelöf
  for `1/ζ` inside the strip is the unknown itself.
- Heat retention, bounded diagonal receivers, symmetry-only collision exclusion, exchange
  orientation, Gaussian-model positivity: all killed with explicit countermodels
  (`exists_xiGaussian_principalIdeal_unit_heat_collapse`,
  `sum_collisionPairs_multiplicity_signed_displacement_eq_zero`, `XiAffineCollisionSymmetryModelNoGo`,
  Gaussian threshold `aλ ≥ 1/4` independent of `δ` [L]).
- Any fixed-kernel, finite-rank, finite-aperture or finite-moment certificate (1.6).
- Any argument that holds verbatim for a Beurling system or for the shifted pair
  `ζ(s−a)ζ(s+a)` (`shiftedPair_leaves_weilCone_and_ramanujan` [L]).
- Any argument whose positivity is paid by the archimedean subsidy or by the zero-free region alone
  (1.3): both are rate `1/2`.
- The absolute (total-variation, `ℓ¹`, entrance-tail) norms of the damping chain: the threshold `1/2`
  there is about absolute row control, not the signed source [S].

### 2.5 Recommended deliverable

The corpus has six exact forms of quasi-RH (`Θ < 1`): short-window Möbius or prime power saving;
receiver damping rate `< 1/2`; a fixed-width admitted band; a growth exponent below `1 − 2ε` at one
`ε`; a formation-energy exponent; and, for WD, a heat rate below `κ₀(δ₀)/log t`. Every opening in
2.3 should be run with quasi-RH as its stated target, and every route card should name its
quasi-RH form.

---

## 3. Question 2: the field the walls ask for

### 3.1 The walls as questions

Read as questions for which the tools are missing, the three wall families say:

- **W1.** How does the additive structure of `ℤ` (the successor, Bézout) produce square-root
  cancellation in a *signed* multiplicative sum at a *single* scale and height? Every classical tool
  either averages over a family (large sieve, Bombieri–Vinogradov, dispersion) or is sign-blind
  (`ℓ²`, period forms), or is subpower (Vinogradov–Korobov, Matomäki–Radziwiłł–Tao). The receiver sits
  at cross-scale exponent `2`, the limit of infinite smoothness, where no `ℓ²` Type-II input passes.
- **W3.** Which observables of the arithmetic source both separate twins and carry an exponent?
  Every reading with finite resolution has width limit `1/2`; every amplitude-derived datum is
  blind below half damping; the signed norm that reads the width exactly is not estimable.
- **W14.** Is there an arithmetic object over `ℤ` whose existence or count is manifest (a section, an
  effective cycle) and whose intersection numbers reproduce the explicit formula? The corpus has
  shown that every identity of the function-field proof (Lefschetz, adjunction, λ-ring, Hecke and
  Adams stability) holds on impure models; only effectivity is missing, and effectivity is the sign.

### 3.2 Charter

Name: **Signed Successor Arithmetic**. Working definition: the quantitative theory of signed
multiplicative data along the successor `n ↦ n+1`, in which cancellation is produced by counting and
is read at a single scale.

The three words are the three walls. *Signed*: the content that Class II laws cannot see (parity,
the Möbius sign, the orientation of a zero relative to the line). *Successor*: the one structure of
`ℤ` that Beurling systems lack and that every Class III law uses (`gcd(n, n+1) = 1`, `pa − qb = 1`,
`|log(A/B)| ≥ 1/max(A,B)`, odd integers differ by at least `2`). *Arithmetic* rather than analytic:
positivity must be inherited from integers, because the corpus proves analysis alone is
Beurling-universal or sign-blind.

### 3.3 Point of view

1. The integers are the interaction of two structures, `×` (the divisor lattice, Witt vectors, the
   λ-ring, Euler products) and `+1` (the successor). RH is a statement about their interaction at
   the square-root scale. Every programme in the corpus is a different coordinate system on this
   interaction; the field studies the interaction itself.
2. Positivity comes from counting. In Weil's proof the sign comes from dimensions of spaces of
   sections. Over `ℤ` the analogous nonnegative integers must be counts of successor incidences,
   lattice points, or solutions of Bézout equations. Analytic positivity (archimedean, zero-free
   region) is a subsidy, admissible only as a remainder.
3. Single scale, single height. Averaging over heights, characters or moduli is the step that
   loses selectivity. The field's estimates are stated at one scale `X ≍ T` (the square-root
   aperture `(1/2) log T`) and one height.
4. Cofinality. No finite statement decides; every theorem is a law uniform in a scale parameter
   (aperture, damping, horizon), and the proof of RH is a transport law across that parameter.
5. Quantization. The deficit from square-root cancellation is integer-valued (collision charge,
   Hodge defect, prime mean, frustration index). A quantized deficit does not need to be estimated,
   only shown to be below the first quantum. The field prefers rigidity statements to estimates.

### 3.4 Objects

- **Successor incidences.** Pairs of divisibility events across a step: `d₁ | k`, `d₂ | k+1` (Bézout
  splitting, `Λ(k(k+1)) = 0`), the successor incidence count with its sawtooth defect in `[−1, 1]`,
  Bézout shells `{n+1−r, n+r}`, the least successor seed `pa = qb + 1`, dyadic windows where every
  consecutive divisor edge is the single pair `(2, 3)` [S].
- **Signed rows and their twins.** Divisor rows `c(d)` with Selberg and Witt ghost coordinates; the
  parity involution; parity pairs; the half-period companion; labelled moments.
- **Receivers.** The pronic prefix energy, the damping chain and its residue modes, the Ward and
  collision charges, the restricted Weil ground energy `μ(A)`, the heated slice coefficients.
- **Ledgers.** Signed incidence forms with balance and frustration (prime-sum edges, prime
  anti-diagonals), the exact incidence ledger
  `Ẑ = pool + crossing + gains − costs + remainder − pole` [S], the Chebyshev two-pole defect.
- **Counts.** `h⁰` of a window (sections), node counts, the node-divisor Euler characteristic
  `e^s + s − 1 − ψ(e^s)`, the frustration index, the Hodge defect as a count of right zeros, the
  collision charge, the lattice index `n!` of the prefix matrix.
- **The scaling surface and its correspondences.** Cycles `aH + bV + f`, the pairing from the
  explicit formula, Hecke correspondences `T_g` with `T_g T_{g'} = e^{s(g)}`, Adams operations, the
  orbit correlation `c_x(g)`, Weil planes.
- **Impure models.** The golden datum, Beurling systems with planted zeros, the shifted pair,
  parity twins, planted Euler factors, off-line lattices and clusters. These are not pathologies but
  the field's control group.

### 3.5 Language

The field speaks in **counts with defects**: every statement is an exact identity
`count = main term + defect` with the defect nonnegative by construction, followed by a
classification of when the defect vanishes. It uses **three currencies** that the corpus has shown
are not interchangeable and must be converted explicitly: width (rate), mass (energy, `m²`), and
count (index, `m`). It names coordinates (raw, response, Selberg, spectral, Witt, Mellin, Bohr),
regimes (sub-horizon, octave, polynomial window, period) and units (width, depth, damping, heat,
aperture, cross-scale exponent `θ = 2 log P/log Q`) before stating any bound. It speaks of
**orientation** (reflection-odd data: which side of the line) separately from **magnitude**
(reflection-even data: how far from the line), because the corpus proves reflection-even readers
agree on partners.

### 3.6 Foundational principles

1. **Selectivity principle.** A theorem that holds verbatim on an impure model (Beurling system,
   golden datum, shifted pair, parity twin, planted Euler factor, off-line cluster) cannot close the
   frontier. Every statement is tested against the control group before it is proved.
2. **Successor principle.** The additive input must be visible in the proof: a solution of
   `pa − qb = h`, a residue class omitted modulo `p`, a layer condition on valuations, an integrality
   `|log(A/B)| ≥ 1/max(A,B)`. Multiplicative identities, however deep, are Class I.
3. **Integrality principle.** Positivity is inherited from a count. An estimate whose positive part is
   an archimedean subsidy or a zero-free region is a remainder, not a mechanism.
4. **Single-scale principle.** No averaging over heights, characters or moduli in the statement; the
   receiver is at cross-scale exponent `2`.
5. **Cofinality principle.** Every result is a law in a scale parameter with an explicit transport
   rule; a finite certificate is a datum, not a theorem.
6. **Quantization principle.** Where the deficit is integer-valued, prove rigidity (`< 1` or `< 2`)
   rather than decay.
7. **Exactness principle.** Identity before asymptotics; retain boundary terms and signed defects;
   never bound a signed term in absolute value before the main term is subtracted.
8. **Two-sidedness.** Both the on-line zeros (linear cusp) and the off-line zeros (unboundedness)
   constrain every receiver; a mechanism must respect both, and a statement that would force a
   rate faster than linear in the damping is refuted by the zeros on the line.

### 3.7 Criteria the field must fulfil

Taken from the corpus's own batteries, the acceptance tests for any theorem of the field are:

- it fails on the golden datum and on every Beurling system with a planted off-line zero, and it
  separates the shifted pair `ζ(s−a)ζ(s+a)` for `a ≠ 0` (AOG orientation criteria; BVI, THIM, SRT);
- it reads the parity: it takes different values on the damped Möbius row and its positive twin at
  some damping `ε ≤ 1/2` (THIM parity barrier);
- it is reflection-odd where it must be (orientation), and it is not a function of amplitudes;
- it is cofinal and supra-Nyquist: it is a law uniform in aperture or horizon, and it carries
  information beyond polynomial length, that is, height at square-root precision (BSU open problem,
  the band's third test);
- its first output in receiver coordinates is a zero-free strip, and it says which one;
- it is exact: an identity with a signed defect, not an inequality with an absorbed constant;
- it uses the successor (BVI test) and the proof says where;
- it respects the ceiling: any positive floor it produces decays at least like
  `exp(−π e^{2(A−2)})` in aperture, and any residual rate it produces is at least linear in the
  damping.

### 3.8 Research programme

Ordered by rung, with the corpus location where each already has an exact form.

1. **A quantitative Class III law.** Give an exponent to one Bézout-selective identity: the
   conditional jump-orbit mean, the `(2r−1)`-shell midpoint annihilation, or the least successor
   seed resonance; target the off-diagonal Vaughan entries (THIM 7.8.4, BVI 7.2).
2. **Kloosterman reciprocity at balanced scales.** Bound the dual norm `Σ_p |Λ_p(c')|/p` for
   `p ∼ P ≍ Q` through the Kloosterman form without external averages (BVI 7.8.1).
3. **Cross-depth cancellation.** Bound the hypercube Dirichlet form uniformly in `P` for
   `0 < ε ≤ 1/2` (BVI 7.5), the finite form of `ζ(1+ε)·ζ(1+ε)^{-1} = 1`.
4. **Separation with an exponent.** A ceiling counterpart of the readout–energy uncertainty
   principle in a separating functional (THIM 7.8.1).
5. **The coalescent surplus.** Signed close prime pairs beyond the Montgomery–Vaughan threshold
   with the favourable Hardy–Littlewood sign (TTPC); a test bed for every tool of topics 1–4.
6. **Arithmetic `h⁰`.** A count of successor incidences at aperture `A` that bounds the Hodge
   defect, built without the sign (AOG; ACS 7; principle 3).
7. **The beta function in aperture.** A relative shell-flux law `−μ' ≤ β'μ` compatible with the
   doubly-exponential ceiling (AOT, ACCE, ACT transport problems).
8. **Scale-matched readings.** Schedules `L/2 < A(L) ≤ L` with precision `o(L³)` that are neither the
   archimedean horizon nor the Chebyshev deficit schedule (SSIC), so that the reading is not blind.
9. **The frustration-to-ground-energy law.** Compute the signed Cheeger constant of the actual odd
   Weil ledger, whose frustration lives on prime-sum edges (AOT, SAEI).
10. **Witt structure as an estimate.** Decide whether Frobenius and Verschiebung on the ghost
    coordinates of the sieve receiver supply a bound the Selberg coordinates do not (BVI 2.1).

### 3.9 What already exists, and what would be new

Much of the field exists in embryo. The correlations of multiplicative functions along shifts
(Matomäki–Radziwiłł–Tao, Tao's logarithmically averaged Chowla) are Class III statements and read the
Möbius sign, but are subpower. Bilinear forms with Kloosterman sums and the spectral theory of
`GL₂` (Deshouillers–Iwaniec, Bombieri–Friedlander–Iwaniec) are the one classical source of
power-saving additive cancellation beyond the square-root scale on average. Gowers norms and
nilsequences read signs with no power saving. Arakelov theory supplies an arithmetic Hodge index
theorem on arithmetic surfaces, and `F₁`-geometry (Deninger's foliated dynamical systems, Borger's
λ-rings, Connes–Consani's scaling site) supplies the formal intersection theory that the corpus has
rebuilt analytically. The corpus's own programmes are the receiver side of the field.

What would be new is the connecting principle: that signed cancellation at the square-root scale is
the shadow of a bounded integer, computed by a count that uses the successor. The corpus has proved
the two halves separately (the deficits are quantized; the selective laws are Bézout laws) and has
not found the count. That is the research question of the field, and the corpus's Claim 6 remains
correct at the level of objects: the field is a new source of positivity, not a new reformulation.

---

## 4. Question 3: route WD

### 4.1 What WD has proved

The route has two receivers and a dynamical reformulation, all verified in source in this review.

- **The Ward cap.** For almost every level `s` and every `τ`, the global cap integral equals
  `−8πτ Σ_q xiWardRightZeroStieltjes(θ(s), τ, q)` over zero copies
  (`ae_forall_xiWardGlobalCap_eq_rightZeroSum` [L]); its real part is a nonnegative sum, each term
  vanishing iff the copy is not right of the line, so the cap vanishes a.e. iff every zero copy has
  real part `1/2` (`ae_xiWardGlobalCap_eq_zero_iff` [L]). The docstring records that the single
  height `τ = 1` already decides.
- **The collision charge.** `xiHorizontalCollisionCharge T = Σ_ρ ord(ρ)(horizontalMultiplicity(Im ρ)
  − ord(ρ))`; `RH ⟺ ∀T, charge < 2 ⟺ ∀T, charge = 0`
  (`riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two`,
  `riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero` [L]); an off-line zero has
  `2·ord ≤ horizontalMultiplicity` (`two_mul_xi_order_le_horizontalMultiplicity_of_offLine` [L]);
  the reflection self-intersection charge is a lower bound for the collision charge [L].
- **The two thresholds.** `λ_WD = inf{λ : every heated slice coefficient ≥ 0 at every height}`
  (`wdHeatThreshold` [L]); `0 ≤ λ_WD ≤ 1/12`; `λ_WD ≤ Λ` and `λ_WD < Λ` whenever `Λ > 0`
  (`wdHeatThreshold_le_newmanConstant`, `wdHeatThreshold_lt_newmanConstant` [L]);
  `RH ⟺ λ_WD = Λ ⟺ λ_WD = 0` (`riemannHypothesis_iff_wdHeatThreshold_eq_newmanConstant`,
  `riemannHypothesis_iff_wdHeatThreshold_eq_zero` [L]); the admissible heats are exactly
  `[λ_WD, ∞)`; at `λ_WD > 0` some even coefficient vanishes at some height, and
  `RH ⟺ T₀(λ_WD, 0, t)` vanishes at some height
  (`riemannHypothesis_iff_exists_xiSliceHeatTransfer_zero_order_eq_zero` [L]). Chained with
  `riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le` [L], `λ_WD ≤ Λ ≤ Δ²/2`.
- **Detection.** An off-line zero `ρ` with `Re ρ ≥ 1/2 + δ₀`, `Im ρ ≥ t₁` forces
  `λ_WD ≥ κ₀(δ₀)/log Im ρ`, `κ₀(δ₀) = δ₀²/(200(log(3/δ₀) + 1))`
  (`le_wdHeatThreshold_of_offLine_zero` [L]); positivity at every rate `κ/log t` makes the zeros
  right of `1/2 + δ₀` bounded in height for every `δ₀` (`exists_im_le_of_heat_rate_zero` [L]). The
  module header locates the loss from the linear scale `δ/96(c+1)` to `δ²/log(3/δ)` in the
  three-radii lower bound, the worst case of `≍ log t` zeros clustered near `1/2 + it`.
- **Unconditional positivity.** Even heated coefficients are positive at every height
  `|t| ≥ t₀` once the heat is `≥ (17/25)/log|t|` (`exists_xiSliceHeatTransfer_pos_heat_interior` [L];
  earlier constants `100`, `19/25`, `1 + δ`), at heat `≥ 1/8` at every height
  (`xiSliceHeatTransfer_nonneg` [L]), and at every fixed `λ > 0` for all large heights
  (`exists_xiSliceHeatTransfer_nonneg_large_height` [L]).
- **Tail bounds.** The actual-ξ tail satisfies `exp(Cx² − Bx⁴) ≤ tail ≤ exp(Cx²)` with `C = A − D`,
  `0 ≤ D ≤ B/2` [S, frontier map].

### 4.2 WD's walls

The frontier map's open item is "force the global cap to vanish, or prove full signed prime−Gamma
contraction uniformly over every zero block", and it records that Gaussian-model coefficient
positivity and small tail error do not control the retained-head sign. The hard-obstacles ledger
places WD at walls 1.2 and 3.4 with the barrier B-C: heated-slice positivity at heat
`κ₀(δ₀)/log t` for one fixed `δ₀` is a zero-free strip. The killed mechanisms specific to WD are
exchange orientation (the multiplicity-weighted signed displacement over collision pairs cancels
identically; the survivor is the squared displacement, which has magnitude but no sign [L]),
line-conjugation-stable scalarization, symmetric Schwarz-cap regularization, baseline-cancelling
nonnegative cross kernels, bounded diagonal HC receivers (one off-line copy makes every finite-window
current escape to `+∞` along ordered primes; a bounded diagonal receiver exists for a window iff
that window's charge is zero [L header]), symmetry-only affine-collision exclusion (finite entire
countermodel [L]), the heat-retention step (`exists_xiGaussian_principalIdeal_unit_heat_collapse` [L]),
and the Gaussian model (threshold `aλ ≥ 1/4` independent of the offset [L header]).

### 4.3 Question 1 for WD: circumvention?

**Structure of the route.** In its cleanest form WD is the statement that the horizontal Gaussian
smoothing of `|ξ(1/2 + y + it)|²` has nonnegative Taylor coefficients in `y` at every heat `λ > 0`
and every height. At heat `0` these coefficients are the Laguerre–Jensen expressions of `Ξ` at `t`,
whose nonnegativity for all orders is necessary for real-rootedness; the heated version is the
corpus's genuinely new object. The route therefore sits between two classical phase transitions:
real-rootedness of `H_λ` (de Bruijn–Newman, threshold `Λ`) and nonnegativity of heated Laguerre
coefficients (threshold `λ_WD`). The corpus proves the second always precedes the first unless both
are zero.

**Why the three exits close for WD.**

- *Rate.* The only unconditional positivity is at the Ki–Kim–Lee scale with constant `17/25`; the
  detection constant `κ₀(δ₀)` is below `10^{-5}` for `δ₀ ≤ 1/10`. Improving the constant below
  `κ₀(δ₀)` for one `δ₀` is quasi-RH (B-C). The gap between `17/25` and `κ₀` is not a constant to be
  optimized but the cluster worst case, that is, wall 1.11 in heat units.
- *Index.* The collision charge is quantized and `RH ⟺ charge < 2`, so WD has the cleanest index
  exit in the corpus. But the only conservation law across collisions is `collision_transfer`
  (off-line charge into multiplicity charge, total horizontal excess conserved), which is a law on
  one fibre; the de Bruijn–Newman flow has no selective conserved quantity (the power sums of the
  zeros evolve explicitly through the Taylor coefficients, and the nonreal content is invisible in
  them). The nonreal count is antitone in heat and zero for `t ≥ 1/8` [S]; what is missing is a
  second computation of the charge at heat `0⁺`.
- *Transport.* In heat the transport is exact and monotone (admissible heats are an up-set;
  `(Im z)² ≤ max(Δ² − 2t, 0)` [L]); the problem is the value at `0⁺`, not the flow.

**Verdict.** WD does not circumvent the walls. Its first rung is the same quasi-RH, in the form of a
heat rate `κ/log t` with `κ < κ₀(δ₀)`.

**Openings specific to WD** [F unless marked].

1. **Cluster-robust detection.** The loss in `le_wdHeatThreshold_of_offLine_zero` is entirely the
   three-radii lower bound at `δ/2`, the worst case of `≍ log t` zeros within `δ` of `1/2 + it`.
   Under regular growth the detection is linear in `δ` [L header]. Proposal: detect with a height
   average over a window of length `≍ 1` around `γ` rather than at the exact height, and use the
   zero-density bound `N(t+1) − N(t) ≍ log t` to show that a cluster that defeats detection at one
   height cannot defeat it on a positive proportion of the window. This would replace
   `κ₀(δ) ≍ δ²/log(3/δ)` by a constant `≍ δ`, and it attacks exactly the loss the corpus has
   named. Its ceiling is quasi-RH (the positivity side still needs the constant).
2. **Labelled orientation.** The exchange no-go says an orientation sign must come from data beyond
   an unlabelled zero pair: an external label, a non-exchange-stable domain, or another
   order-breaking structure [L header]. The bounded-diagonal no-go says a surviving HC comparison
   must use signed off-diagonal cancellation and an unbounded or singular landing. The only
   arithmetic label available is the ordered prime index (the Gauss–Hodge prime current grows
   linearly in the prime label at an off-line copy [L header]). Proposal: build the HC source
   comparison on the ordered-prime current with the signed off-diagonal retained, and test it first
   against the shifted pair, which has an orientation but no Euler product of the right kind.
3. **The collision-transfer index.** `collision_transfer` conserves `C − N` (horizontal square mass
   minus divisor mass) across a collision on one fibre. Proposal: define the window invariant
   `C(T) − N(T)` for the actual ξ divisor and evaluate it at heat `t ≥ 1/8` where all zeros are real
   and simple (`deriv_riemannHeat_ne_zero_of_newmanConstant_lt` [L] above `Λ`); then prove it is
   nonincreasing backward in heat on each window. If `C − N` at `0⁺` could be bounded by its value at
   `1/8` plus a count of collisions, the charge `< 2` criterion would become a statement about
   collision counts. The obstruction is that zeros enter and leave windows under the flow, so the
   fibre law must be made global; this is the same "uniformly over every zero block" demand as the
   frontier map's open item.
4. **The heat derivative of the cap.** The Ward cap is a nonnegative sum over right zero copies at
   each `(s, τ)`. Its de Bruijn–Newman deformation has not been studied. Since nonreal zeros of `H_t`
   are finitely many for `t > 0` and move toward the axis, the heated cap is a finite sum for
   `t > 0` and vanishes for `t ≥ 1/8`. Proposal: prove the heated cap is monotone in heat on every
   level and compute its derivative as a prime–Gamma current; the derivative at `0⁺` would be the
   signed prime−Gamma contraction the route needs, written in heat coordinates where the right-zero
   sum is finite. Ceiling: a bound on the derivative at one positive heat is a zero-free strip.

### 4.4 Question 2 for WD: the field from WD's angle

**Questions.** When do the two phase transitions of a real entire function, real-rootedness under
heat and nonnegativity of heated Laguerre coefficients, coincide? What datum, beyond the unlabelled
zero divisor, orients a zero relative to the line? How is the retained head of a slice controlled
at the Ki–Kim–Lee scale independently of the cluster structure of its zeros?

**Name and charter.** An **oriented heat theory of divisor currents with arithmetic labels**: the
study of real entire functions through the sign structure of their horizontal Gaussian smoothings,
with the zero divisor carrying an external label (here the ordered primes through the explicit
formula) that breaks the exchange symmetry of unordered pairs.

**Objects.** The heated slice coefficients `T_{2m}(λ, 0, t)`; the threshold `λ_WD` and its touching
order; the de Bruijn–Newman flow and its zero dynamics; the horizontal multiplicity and the collision
charge; the Ward cap and its right-zero Stieltjes sum; the off-line and multiplicity charges with the
conserved horizontal excess; the head–tail factorization of a slice with its explicit `x²` factors
and Gaussian tail bounds; the Gaussian and cosh model families as the control group.

**Language.** Heat as the scale parameter (currency `Δ²/2`, converted to width by the lag-rate law
and to the Ki–Kim–Lee scale by `1/log t`); orientation versus magnitude; fibre laws versus window
laws; detection constants `κ₀(δ)` versus positivity constants.

**Principles.** (i) Orientation must be sourced by a label, never by symmetry (exchange no-go,
symmetry-only affine no-go). (ii) Detection must be cluster-independent, or the loss must be charged
to the height average. (iii) Positivity at a heat is inherited upward (admissible heats are an
up-set) and must be proved at the threshold, where the touching order decides. (iv) A heat-retention
step is never available; only same-time statements are. (v) Every statement is tested on the
Gaussian and cosh models, which are nonselective, and must fail on the cos-model flow at
`μ < δ` [L].

**Criteria.** A WD theorem must: distinguish `Ξ` from `H_t` at `t ∈ (λ_WD, Λ)` in the sense of
reading orientation; depend on `δ` where the Gaussian model does not; carry a label from the prime
side; survive the exchange involution with a nonzero sign; be stated at one heat and one height,
with the height average if a cluster loss is charged; and name its zero-free-strip form (a heat
rate `κ < κ₀(δ₀)`).

**Research topics.** (1) The constant in the Ki–Kim–Lee-scale law: from `17/25` toward every
`κ > 0`, which is `Θ = 1/2` with finiteness in every strip. (2) Height-averaged, cluster-robust
detection at linear scale in `δ`. (3) The heat derivative of the Ward cap as a prime−Gamma current.
(4) The global form of the collision-transfer law. (5) The relation `λ_WD` versus `Λ` on model
families: classify entire functions for which `λ_WD = Λ` away from the trivial case. (6) The touching
order: what forces the vanishing coefficient at `λ_WD` to have order `0`. (7) The labelled HC source
comparison on the ordered-prime current with signed off-diagonal cancellation and a singular landing.

---

## 5. Evidence index

Declarations read in source or located by search in this review, with modules.

| Declaration | Module |
|---|---|
| `widthFunctor_obj_zetaReceivers_eq`, `categoricalGradedWidthDictionary_tfae` | ArithmeticOrientationTheory/TheWidthFunctor |
| `receiverDampingRate_eq_zetaZeroAbscissa_sub_half`, `riemannHypothesis_iff_cofinal_budget` | RHTower/AdmissionBelowHalfDampingAboveTheZeroWidth |
| `selectivity_class_III_bezout_successor_selective_laws` | TransHorizonIncidenceMechanics/CompleteSignedTransHorizonEnergyAndTransferSelectivity |
| `parity_barrier` | TransHorizonIncidenceMechanics/RealCharacterParityPairsAndTheParityBarrier |
| `receiverBounded_amplitudeInvariant_iff` | TransHorizonIncidenceMechanics/HalfDampingIsTheExactThresholdOfTheParityPair |
| `exists_interiorEnergy_le_on_vinogradovKorobovBand` | BezoutValuationIncidence/ReceiverBoundedInTheVinogradovKorobovBand |
| `shiftedPair_and_vkBand_selectivity` | BezoutValuationIncidence/ParityPairAndSelectivitySynthesis |
| `riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two`, `..._eq_zero`, `two_mul_xi_order_le_horizontalMultiplicity_of_offLine` | RHTower/XiHorizontalCollisionChargeEndpoint |
| `xiHorizontalMultiplicity`, `two_le_xiHorizontalMultiplicity_of_offLine` | RHTower/HorizontalSingletonZeroFiber |
| `xiReflectionSelfIntersectionCharge_le_horizontalCollisionCharge` | RHTower/XiReflectionSelfIntersectionCharge |
| `HorizontalCharge.collision_transfer` | HTGeometry/HorizontalChargeTransfer |
| `sum_collisionPairs_multiplicity_signed_displacement_eq_zero` | RHTower/XiHorizontalCollisionExchangeOrientationNoGo |
| `gaussHodgePrimeLinearEscapeConstant_pos` (header) | RHTower/HCGaussHodgeBoundedDiagonalNoGo |
| `zeta_cyclic_hodgeDefect_iff` | ArithmeticCastelnuovoSeveri/TheHodgeDefectIsCyclic |
| `scalingSurface_hodgeIndex_iff`, `riemannHypothesis_iff_exists_effectivity` | ArithmeticCastelnuovoSeveri/TheScalingSurface |
| `scalingSurface_hodgeIndex_iff_heckeStable_effectivity` | ArithmeticCastelnuovoSeveri/SectionCountRiemannRochAndPrimeBlindSelectivity |
| `riemannHypothesis_iff_forall_hasseWeilAt`, `hasseWeilAt_iff_lefschetz_bound` | ArithmeticOrientationGeometry/ScalingDataAndWeilPlanes |
| `riemannHypothesis_iff_forall_prime_variationInequality` | ArithmeticCriticalityTheory/ArchimedeanZTypeLaw |
| `pmInterior_strict_contraction_iff_bounded_energy` | BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder |
| `hypercubeDilationDirichletForm_nonneg` | BezoutValuationIncidence/BezoutCouplingAndCrossDepthCancellation |
| `leastSuccessorSeed_spec` | BezoutValuationIncidence/DilationSuccessorLeastSeedResonance |
| `exists_readout_energy_uncertainty` | BezoutValuationIncidence/ReadoutEnergyUncertaintyPrinciple |
| `exists_criticalZero_linear_dualResidual_floor` | BezoutValuationIncidence/PowerDampedResidualHasLinearCusp |
| `moebiusPowerWindowSaving_iff`, `primePowerWindowSaving_iff` | BezoutValuationIncidence/ShortWindow{Moebius,Prime}SavingIsTheQuasiRiemannHypothesis |
| `moebius_and_prime_powerWindowSaving_iff_quasiRH` | ReflectiveDirichletPolynomialS2/ShortWindowDispersionAtSeventeenThirtieths |
| `sameRelationSpectrum_five_six_iff` | BezoutValuationIncidence/RelationSpectrumDeterminesTheRowUpToTheCompanion |
| `not_exists_linear_observability_horizon` | BezoutValuationIncidence/SuperlinearObservabilityHorizonAtArbitraryPhase |
| `riemannHypothesis_of_signedWork_single_sign_change` | ArithmeticContinuationAndCriticalEnergy/TheSignedWorkChangesSignOnce |
| `monotoneOn_exp_mul_of_relative_decay` | ArithmeticOrientationTheory/TransportInApertureAndTheCeilingLyapunovIdentity |
| `weil_iff_cofinal_curveReceiverEnergy` | ArithmeticCompensationTheory/TheReceiverOfACurveIsAdmittedAboveTheZeroWidth |
| `resolutionLimit_width_aperturePositivity`, `apertureResolutionJump` | ScaleSignedIncidenceCriticality/TheApertureCertificateIsBlindInEveryUnit |
| `selectivityBattery_goldenDatum_nonObject` | ArithmeticOrientationTheory/TheWidthFunctor |
| `goldenDatum_beurling_not_pure` | ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem |
| `functionField_vs_goldenFakeCurve_and_windowHiding`, `shiftedPair_leaves_weilCone_and_ramanujan` | BiScaleUncertainty/NodeCriticalityPhaseSensitivityAndCalibrationSynthesis |
| `obstructionHull_oscillating_nonempty_iff` | ArithmeticOrientationTheory/TheZerosOfZetaAreWhereTheObstructionVanishes |
| `zeta_near_top_cluster_collapse_of_offLineCopiesLocallyBounded` | ArithmeticCastelnuovoSeveri/HeightUniformVisibilityAndOffLineDensity |
| `zetaZeroAbscissa_le_of_suzukiCompletedFormationEnergy_le_rpow` | RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw |
| `riemannHypothesis_of_squarePrimeWindowCorrelationEnergySubpower` | RHTower/CCM/CCMSharpPrimeWindowSquareCorrelationEnergy |
| `ae_xiWardGlobalCap_eq_zero_iff`, `ae_forall_xiWardGlobalCap_eq_rightZeroSum` | RHTower/XiWardGlobalCapRightZeroSum |
| `ae_forall_integrable_xiWardSchwarzCapFactor` | RHTower/XiWardCapGlobalIntegrability |
| `wdHeatThreshold`, `wdHeatAdmissible`, `wdHeatThreshold_le_newmanConstant`, `riemannHypothesis_iff_wdHeatThreshold_eq_zero` | RHTower/XiSliceHeatTransferNoSlack |
| `wdHeatThreshold_lt_newmanConstant`, `riemannHypothesis_iff_wdHeatThreshold_eq_newmanConstant`, `riemannHypothesis_iff_exists_xiSliceHeatTransfer_zero_order_eq_zero`, `xiSliceHeatTransfer_pos_of_gt` | RHTower/XiSliceHeatThresholdTouching |
| `wdHeatThreshold_lt_twelfth` | RHTower/XiSliceHeatLargeHeightPositivity |
| `le_wdHeatThreshold_of_offLine_zero`, `exists_im_le_of_heat_rate_zero`, `re_xiSliceHeatTransfer_neg_of_slice_zero` | RHTower/XiSliceKKLScaleOffLineDetection |
| `exists_xiSliceHeatTransfer_pos_heat_interior` (`17/25`), `..._subconvex` (`19/25`), `..._over_log` (`100`) | RHTower/XiSliceHeatRateInteriorLindelof, ...Subconvex, XiSliceHeatEffectiveKKL |
| `xiSliceHeatTransfer_nonneg` (heat `≥ 1/8`) | RHTower/XiSliceHeatTransferPositivity |
| `exists_xiSliceHeatTransfer_nonneg_large_height` | RHTower/XiSliceHeatLargeHeightPositivity |
| `gaussianModelHeatCoeff_pos_at_scaled_heat` (threshold `aλ ≥ 1/4`) | RHTower/XiSliceHeatGaussianSharpThreshold |
| `cosDefectFlow_collision` | RHTower/XiSliceHeatNewmanCosModelFlow |
| `riemannHeat_zeros_real` (`t ≥ 1/8`), `newmanConstant_nonneg`, `riemannHeat_neg_nonreal_zeros_infinite` | RHTower/DeBruijnNewmanHalfBound, DeBruijnNewmanConstant, DeBruijnNewmanNonnegative |
| `riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le` | SquareRootThreshold/LagRateBoundsTheDeBruijnNewmanHeatTime |
| `deriv_riemannHeat_ne_zero_of_newmanConstant_lt` | RHTower/DeBruijnBarrierZerosSimple |
| `exists_xiGaussian_principalIdeal_unit_heat_collapse` | RHTower/XiGaussianHeatRetentionObstruction |
| `collisionModel` (countermodel) | RHTower/XiAffineCollisionSymmetryModelNoGo |
| `preDivisorTransverseCompletionDefect_ne_zero_iff` | RHTower/PreDivisorTransverseDualNumberFormalNeighborhood |
| `all_thetaXiWardEuclideanEnergy_eq_zero_iff_riemannHypothesis` | RHTower/Hedenmalm/HedenmalmThetaAnomalyWardKreinPythagoreanDefect |
