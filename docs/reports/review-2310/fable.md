# Review 2310: circumventing the walls, and the field that would dissolve them

Inputs: the frontier map, the killed-routes ledger, the three review-2310 ledgers (unification,
hard obstacles, walls), and the twelve programme READMEs. Every claim about what the corpus has
proved was checked with `scripts/formal_tools.py research`; every Lean name quoted below was
confirmed to exist as a declaration, by hybrid research or by exact lexical lookup. The working log
with the extracted facts and the full search record is `logs/fable-review-2310-research-log.md`.

The report answers two questions. First, whether any proof mechanism can go around the walls rather
than through them. Second, if the walls are read as questions that present-day mathematics cannot
state in a form it can attack, what field would supply the missing tools.

---

## 1. What the walls say when read together

### 1.1 One invariant in many units

Write Δ = sup |Re ρ − ½| over the zeros of ζ. Every receiver in the corpus measures Δ exactly and
nothing else, each in its own unit:

| receiver | unit | exact reading |
|---|---|---|
| damped Möbius receiver E_T(ε) | damping ε | inf of the derived set of admitted dampings = Θ − ½ (`receiverDampingRate_eq_zetaZeroAbscissa_sub_half`) |
| Weil ground energy μ(A) | aperture A | μ(A) ≥ 0 for all A iff RH; off RH μ turns negative past a contact aperture A* ≥ 3/10 |
| Chebyshev band energy ∫₀^L Ẽ² | growth exponent | linear iff RH, never sublinear, nothing between linear and exponential (BiScale) |
| 2×2 pole compression | rate of the cross term | rate = 1 + 2·width |
| intersection Gram of the scaling surface | positive inertia index | index = 1 + number of distinct right zeros (`zeta_hodgeDefect_iff`, `riemannHypothesis_iff_one_positive_square`) |
| HF window exponent θ* | exponent | Δ ≤ θ* ≤ Δ/2 + ¼ |
| LI reciprocal depth | depth | b_ρ ≤ 1/431 unconditionally |

The unification ledger's conclusion is correct: the thirty live routes, eighteen candidates and
PW-B are one receiver written in different coordinates, and the width dictionary is the change of
coordinates. The consequence for this review is that **no reformulation can count as progress unless
it changes the class of inputs**. A new unit is not a new proof.

### 1.2 The rate gap

In every unit the unconditional estimate sits exactly at the value that width ½ would give, improved
only by the Vinogradov–Korobov factor, while RH is the value at width 0:

- Deficit envelope |D(T)| ≤ C e^{T − κT^a}, a < 3/5, where e^{T/2} is needed (WL).
- Damping: the receiver is bounded on the band ½ − κσ(T)/(480 log T) ≤ ε ≤ ½ and at no fixed ε < ½ (BVI §3.15); the band is the zero-free region in both directions.
- Aperture: ℓ¹ prime cost ≍ 2e^a against depth-δ amplification e^{2δa}; these coincide at δ = ½, so every height-uniform aperture method floors at width ½ (APT).
- Horizon: period energy ≍ N^{1−2ε} for ε < ½; the receiver is smaller than it by exactly the VK factor (BVI).
- Incidence: GradedIncidenceAllocation(½, 78) holds at every aperture, which is rate 1 in e^r (AIP).

The gap between rate 1 and rate ½ is the square-root barrier, and the corpus has proved that it is
the same number in every coordinate: a power saving in the short-window Möbius mean square at any
fixed window exponent is equivalent to a zero-free strip Θ < 1 (`moebiusPowerWindowSaving_iff`),
and width 0 is the accumulation of such savings.

### 1.3 Two floors that every mechanism must clear

**The parity floor.** On the damped class, whether the receiver is bounded is a function of the
Ramanujan amplitudes exactly when ε > ½ (`parity_barrier`,
`receiverBounded_amplitudeInvariant_iff`, THIM), and blindness is closed under post-processing,
pairing and families of any cardinality. The derived set of sign-blind dampings is [½, ∞): the
threshold is reached from one side only. Every real character, Liouville, and the Fermi even flip
give unconditional parity pairs at every ε ≤ ½. Translated moments of every degree are blind to the
even flip (`translatedMoment_evenFlipRow`), yet the even flip breaks the receiver. So any mechanism
must read something that is not a quadratic or amplitude functional of the source.

**The finite-data floor.** Every finite reading admits an off-line extension: finite apertures
(mimicry by on-line translates, Carathéodory–Fejér), finite moment lists (quantum jumps), finite
rank, finite node sets (gapped or sub-square-root node density), finite prime data (RH is a
conjunction of single dyadic-window statements for X ≥ X₀, any X₀). The bounded-aperture certificate
has width limit ½ in every unit; the unbounded one has limit 0 (SSIC). Only three operations move
the floor: crossing Nyquist, reading a magnitude instead of a sign, or adding data of a third kind
(mass, dilution).

### 1.4 The assets

The corpus holds structures that did not exist before and that are the raw material for anything
new:

1. **Exact ledgers with one signed obligation.** E_T = D^act + 2P^pred + 2M^int with the first two
   bounded after compensation and the whole obligation in the Bézout interior martingale
   (`exists_pmBezoutInterior_compensated_energy_bound`,
   `pmInterior_strict_contraction_iff_bounded_energy`); the Chebyshev ledger with defect
   E(s) = e^s + s − 1 − ψ(e^s) as complete source invariant (AIP); the odd sector collapsed to one
   rank-one pole moment, sourceEnergy = weilForm + 2⟨q, tanh_L⟩² (THIM §3.13).
2. **The scaling surface with four of Weil's five ingredients** and the fifth, Riemann–Roch with a
   Bézout cone, proved equivalent to RH (`riemannHypothesis_iff_exists_effectivity`,
   `hodgeIndex_of_riemannRoch_of_bezout`, `localPair_nonneg`, `posTestCone_not_riemannRoch`),
   together with the λ-ring (Adams, Hecke, arithmetic Lefschetz) and the calibration that Witt
   integrality, functional equation and positive prime counts do not imply purity (golden q = 5).
3. **Holonomy and frustration.** Balanced ⟺ locally payable ⟺ all closed-walk holonomies +1; the
   odd Weil ledger is frustrated only on prime-sum edges; the rank-one pole is never locally payable
   (`walkHolonomy_eq_one_of_edges`, `walkHolonomy_eq_prod`, SAEI); the lattice skeleton of the pair
   kernel is a nonnegative Laplacian, and the continuum fails only in the archimedean crossing
   collar with threshold s₀ ∈ (log 5, log 6) (AIP).
4. **A complete observation theory.** Additive moments of a divisor row through degree six determine
   the row up to one involution, the half-period companion (top dyadic layer flip); nothing above
   degree six is informative, nothing below five is sufficient (BVI §3.5,
   `translatedMoment_companion`, `sign_cube_eq_one_of_translatedMoment_three`).
5. **Criticality.** The odd arithmetic jump form is rate-critical, variance-critical, has no Hardy
   weight, is not of Z-type (failure located on prime anti-diagonals |x| + y = log n), and has an
   infinite-dimensional family of sign-changing approximate ground states (ACT). The positive ground
   energy μ(A) is pinned between 1/30 on [0, 21/200] and the ceiling K exp(11A/2 − π e^{2(A−2)}).
6. **Selective inputs formalized.** Guth–Maynard Theorem 1.1 unconditionally
   (`guthMaynardLargeValuesBound_holds`), the Vinogradov mean value theorem with explicit constants
   (`exists_vinogradov_mean_value_decay`, `card_vinogradovDiagonalSolution_le_explicit`), the
   log-free large sieve with the Montgomery–Vaughan constant, zero density 30/13, and the VK band
   as the first receiver statement selective against Beurling systems.
7. **The damping chain.** A Markov semigroup in the damping with explicit entrance law, compact
   centred operators on c₀, residue modes v_d with eigenvalue d^{−η}, and the sharp location of the
   obstruction: the entrance functional has finite pronic dual norm exactly for η > ½, so the failure
   is in the centring, not the transition (BVI §3.16, SAEI).

---

## 2. Question 1: is there a mechanism that circumvents the walls?

### 2.1 The logical shape of "circumvention"

Any proof of RH implies ψ(x) − x = O(√x log² x). So no route avoids Wall 1 in the sense of never
producing the critical-rate estimate. Circumvention can only mean obtaining that estimate as a
**corollary of structure** rather than proving it directly, as Weil's proof for curves obtains
|a_p| ≤ 2√p from Riemann–Roch and the Hodge index theorem without ever estimating a character sum.

Of the three wall families, only Wall 14 (faithful realization) has a removal criterion that is a
construction and not an estimate. Walls 1 and 3 are direct by definition. Therefore:

> A circumventing route exists if and only if an effectivity (Riemann–Roch) structure can be
> constructed on the scaling surface from the ring structure of ℤ. Every other candidate is a direct
> attack in disguise.

The corpus has already reduced Wall 14 to one axiom. What remains is to say which constructions are
not yet excluded and what they would need.

### 2.2 Audit of candidate mechanisms

Each candidate is checked against the corpus (proved / premise / absent), against the selectivity
battery (§4.6), and against the killed-route patterns (finite data admits extensions; positivity
supplies no upper bound; magnitude readers erase orientation; receiver read as producer; relative
promoted to absolute; deformation-robust inequalities fail).

**M1. Balanced-scale single-modulus statistics of the prime row through trace functions.**
Corpus: the cross-scale form reduces exactly to the dual norm Σ_p |Λ_p(c')|/p with no bilinear
structure left (`abs_rowBilinear_sub_kernelStatistic_le`); the Bernoulli kernel is a
cosecant–Bernoulli sum in the Kloosterman fraction k·n̄/p (`bernoulliKernel_eq_reciprocity`);
at fixed p the prime row's statistic is the omitted residue class, of relative size 1/p
(`tendsto_mul_kernelStatistic_primeWindowRow`); the centred prime row is controlled on
P^{1+δ} ≤ Q ≤ P^{30/17−δ} by Huxley and Guth–Maynard tiling; balanced scales Q ≍ P are open; the
generic Type-II barrier Q ≥ P^{5/3} is sharp and survives readout-free side conditions.
Assessment: this is the one face where an input class that is *provably selective* can enter.
Bounds for Σ_{q≤x} Λ(q)K(q) with K a trace function modulo p have power savings for x ≥ p^{3/4+ε}
(Fouvry–Kowalski–Michel), which covers balanced scales; the input is Deligne's theorem, i.e. RH over
𝔽_p, unavailable to Beurling systems. The kernel statistic is a Dedekind–Bernoulli sum in n̄, not a
trace function, so the first task is to expand it in Kloosterman sums over primes. Verdict: not a
circumvention. A power saving at balanced scale would be of zero-free-strip strength
(`moebiusPowerWindowSaving_iff`), and the window form needs twisted prime sums over short intervals
(`window_energy_le_twisted_short_sums`), which are of square-root-barrier strength. It is the most
concrete *new input class* in the corpus's reach, and it attacks quasi-RH, not RH.

**M2. Effectivity through counting.** Corpus: the axioms are formalized and RH ⟺ ∃E with
RiemannRochAxiom E ∧ AmpleAxiom E (`riemannHypothesis_iff_exists_effectivity`); the open positive
cone must lie in E (`openPositiveCone_subset_of_effectivity`); the positive-test cone fails RR; the
Frobenius graph cone fails RR; the golden datum shows multiplicative data cannot supply E. No
construction exists. Assessment: this is the only corollary-type circumvention, and it is a
construction problem. The constraints a construction must satisfy are known: contain the open
positive cone, be Bézout-closed (effective cycles meet nonnegatively), be Hecke-stable under the
λ-ring, and use a constraint the golden datum violates, i.e. the additive structure of ℤ. The
corpus already contains Landau-density-type theorems for the prime-power node set (tests whose
Weil pairing vanishes at every log n beyond N must have spectral second moment at least 99/4 or
51/2 times their L² mass; `ninety_nine_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero`
and companions), which are the h⁰ side of a Riemann–Roch inequality without the name. Verdict:
the circumvention exists in principle, is not killed, and is the centre of the field designed in §4.

**M3. "Paid" as an index class.** Corpus: paid receivers are preserved by critical Wiener kernels
(`receiverBounded_dirichletConv`), by local factors with |a| < √p
(`bounded_weightPronicEnergy_localFactor_iff`), by sparse flips; the pole law reads the *order* of
the pole (`poleValue_eq_zero_and_poleSlope_eq_zero_of_receiverBounded`); the logarithmic moments
are a complete invariant that separates every pair and bounds nothing (`exists_logMoment_ne`).
Assessment: the predicate "paid" has the formal structure of a Fredholm index: stable under a
group of compact-type perturbations, integer-valued through orders, and read by a winding (the
argument of ζ to the right of ½). What is missing is the index *theorem*: a formula computing the
class from arithmetic counts. Verdict: equivalent to RH; not a circumvention; it is the organizing
structure of the oriented-transport face of §4.

**M4. The odd sector as a ratio-versus-product inequality.** Corpus: in the lattice, a ratio pair
(log a, log b) is an atom iff b/a is a prime power and a product pair iff ab is a prime power; the
dominance law productAtom ≤ ratioAtom makes the lattice skeleton a nonnegative Laplacian (AIP); the
continuum fails in the archimedean crossing collar; the odd eigenvector identities make RH
equivalent to sourceEnergy(|q|) ≤ 4 sourceEnergy(q⁺), and for odd q the negative lobe is the mirror
of the positive lobe, so the content is that the *reflected* pairing of a half-line lobe through
the prime-sum edges is dominated by its same-side energy; the only cross-lobe theorem is conditional
(`odd_eigenvector_eigenvalue_lt_half_of_cross_lobe_oneL_le_primeShift`). Assessment: odd Weil
positivity is a weighted inequality between difference-correlations (autocorrelation at lag log n)
and sum-correlations (self-convolution at log n) of a half-line profile, over prime powers with
weight Λ(n)n^{−½}, corrected by the archimedean odd kernel and the rank-one pole. This is a
sum–difference inequality with multiplicative targets. Additive combinatorics has sum-versus-difference
theory for counting measure on finite sets (Ruzsa calculus, sum-dominant sets) and nothing for
weighted profiles with prime-power targets. Verdict: not a circumvention, but a new language in
which the obstruction (frustration on prime-sum edges) becomes a question an existing field can
recognise.

**M5. Doob-transformed damping chain.** Corpus: compact centred semigroup on c₀, residue modes,
admission ⟺ square summability of the orbit (`admits_iff_summable_orbit`), entrance tail
not square-summable for η ≤ ½, pronic dual norm of the entrance functional finite iff η > ½
(`exists_pronicWitness_not_summable_pairing`), no backward stability. Assessment: the
missing statement is a forward pronic-ℓ² bound of the centred chain at fixed η < ½, a Poincaré-type
inequality for a Markov semigroup whose entrance law is not in the dual of the critical norm. Markov
theory handles this by h-transforms: the reciprocal observable (size bias divided out) already has a
finite pronic dual norm at every damping. The h-transform under which the centred chain is a
contraction in pronic ℓ² is not identified. Verdict: equivalent to admission at one damping; a new
tool class (functional inequalities for non-symmetric arithmetic semigroups without invariant
measure in the dual), not among the killed mechanisms, because it is an upper bound and not a
positivity statement.

**M6. Pair correlation beyond α = 1.** Corpus: Montgomery's form at leading order for 0 < α < 1,
uniformly on compact subintervals (`tendsto_montgomeryForm_div_leadingOrder`,
`eventually_montgomeryForm_div_leadingOrder_uniform`); `PairCorrelationFourThirds` is a premise
(`zeta_three_quarters_simple_of_pair_correlation`); the universal matrix barrier at 2/3 and the
anti-crystal law (`false_of_lorentzZeroSumAll_le`) use pair correlation as hypothesis; the
Selberg tangent row's period covariances converge to the Hardy–Littlewood singular series
(`selberg_and_damped_tangent_correlations_agree`). Assessment: beyond α = 1 pair correlation is
equivalent, under RH, to prime-pair correlations with a power-saving error; unconditionally it
needs additive-divisor inputs for Λ of twin-prime strength. Verdict: not a circumvention; it is the
zero-side name of the same input.

**M7. Higher-degree and labelled observables.** Corpus: cubic translated moments pin the sign at
every odd modulus; the even flip is invisible at every degree; labelled moments break the companion
symmetry by construction; cubic Möbius energies are nonnegative as Gamma-weighted L² norms
(`cubicMomentFiniteEnergy_nonneg`). Assessment: these theorems locate where orientation lives (the
top dyadic layer; first-order data at prime powers) and prove that no polynomial positivity principle
can read it. Verdict: not a mechanism; an orientation coordinate.

**M8. Transport in aperture.** Corpus: μ(A) explicit floors on [0, 3/10], doubly exponential ceiling,
capacity ratio → 1 (no uniform strict margin), compact negativity at fixed aperture, the folded
supersolution route excluded by the two-moment law (ACT), the damping analogue fully developed
(ACCE: RH ⟺ work changes sign at most once ⟺ convexity). Assessment: no monotone or Lyapunov quantity
in A is known; an aperture-derivative identity with the structure of ACCE's damping derivative
(boundary flux − jump energy − density forcing) does not exist in the corpus. Verdict: an open
reformulation; the ceiling fixes its shape (any Lyapunov functional must decay like
exp(−π e^{2(A−2)})).

### 2.3 Verdict on question 1

- No candidate circumvents Walls 1 or 3. Each is either an exact reformulation (M3–M8) or a new
  input class aimed at the same estimate (M1).
- Wall 14 admits circumvention in principle (M2), and nothing in the killed-routes ledger excludes a
  construction based on counting rather than on spectral realization; what is excluded is any
  construction that uses only multiplicative data.
- The practical opportunities, in order: (i) M2 as a programme (the field of §4); (ii) M1 as the one
  estimate where a selective external theory (ℓ-adic cohomology over 𝔽_p) can be brought to bear on a
  receiver coordinate the corpus has made exact; (iii) M5 and M4 as reformulations that import tools
  from Markov theory and additive combinatorics rather than from spectral theory, where the
  killed-route ledger is densest.

The unification ledger's sentence "no reviewed theorem requires the invention of a new field" stands.
What requires it is not a theorem but the pattern of forty-four kills: every one of them loses the
same thing, the orientation of the source, at the same place, the passage to a limit.

---

## 3. Question 2: the walls as questions mathematics cannot yet ask

Read as questions, the walls are:

**W1. What is the sign of a sum whose size is all we can bound?** Mean values, the large sieve,
Vinogradov's method and the Guth–Maynard large-values estimate bound sizes on average or at the
diagonal. Pointwise sign at a single height, for an incomplete sum over primes at the critical length,
is not something analysis can currently state as a hypothesis-free inequality. Weil and Deligne give
exactly such signs for *complete* sums over finite fields, through geometry, not estimation.

**W3. Which limits preserve orientation?** Hilbert-space limits are sign-blind (Parseval, parity
barrier); c₀ limits have no backward transport; Krein-space limits are indefinite. The passage from
finite apertures, horizons and moment lists to the cofinal statement loses exactly the datum RH is
about. Mathematics has two ways of making an orientation survive limits: topological degree and
index (integers do not move under compact perturbation) and algebraic effectivity (a divisor class
being effective is closed under specialisation). Neither exists for a source living on ℤ × (scale).

**W14. What is an effective cycle on ℤ × ℤ?** The surface exists as a real shadow (the scaling
surface), its intersection theory is exact, and its Hodge index theorem is RH. There is no notion of
section, hence no dimension count, hence no Riemann–Roch. Arakelov theory gives Riemann–Roch on
Spec ℤ (Minkowski's theorem), not on the surface, because ℤ ⊗_{𝔽₁} ℤ is not a ring.

The three questions have one answer in common: a theory of **orientation that survives limits** for
arithmetic sources. That is the field.

---

## 4. Design: Arithmetic Orientation Theory

### 4.1 Name and one-line definition

**Arithmetic Orientation Theory (AOT)**: the study of integer-valued and sign-valued invariants of
arithmetic sources at critical scale that are stable under passage to unbounded aperture, horizon,
damping and height, together with the counting theorems (Riemann–Roch type) that compute them.

The name is chosen because the three walls are three faces of one loss, orientation: sign in
estimates (W1), parity class in transport (W3), effectivity in realization (W14). "Effectivity" alone
names only the third face.

### 4.2 Point of view

RH is not treated as an inequality to be estimated but as the vanishing of an oriented defect:

- the positive inertia index of every intersection Gram equals one;
- the holonomy class of the Weil ledger is trivial after global payment;
- the companion orientation of the Möbius row is the one that pays the receiver.

The theory's theorems are identities and counts; estimates appear as corollaries, in the order of
Weil's proof (Riemann–Roch ⇒ Hodge index ⇒ bound), never in the order of the analytic tradition
(bound ⇒ zero-free region ⇒ ...). An AOT statement is well-formed only if it says in which unit of
the width dictionary it lives and which selectivity tests it passes.

The point of view is therefore geometric in its goals and sampling-theoretic in its methods: the
dimension of a space of sections on the scaling surface is a Nyquist count, the degrees of freedom of
aperture- and height-limited tests, and the arithmetic enters through the divisor of prime-power
nodes on which sections are required to vanish.

### 4.3 Questions the field exists to answer

1. **Sections.** Is there a functor h⁰ from scaling cycles to ℕ satisfying a Riemann–Roch inequality
   h⁰(x) ≥ x·x/2 + (linear in x·H, x·V) and the effectivity rule h⁰(x) ≥ 1 ⇒ x ∈ E, where E is
   Bézout-closed? Which ring-theoretic property of ℤ does h⁰ use that the golden datum lacks?
2. **Index theorem.** Is the inertia index of the intersection Gram, equivalently the pole order read
   by the receiver, equal to an independently computable count? What is the arithmetic side of that
   equality?
3. **Oriented transport.** On which function space is the parity class of a row a continuous
   invariant and the centred damping semigroup forward-bounded at fixed η < ½? What is the
   h-transform that makes it so?
4. **Frustration index.** What is the minimal global payment of the Weil ledger's frustrated cycles
   as a function of aperture, and is it the ground energy μ(A)?
5. **Sum–difference at multiplicative targets.** For half-line profiles, when do Λ(n)n^{−½}-weighted
   ratio correlations dominate product correlations up to the archimedean odd kernel and the pole?
6. **Oriented observation.** Which readings of a source are orientation-faithful, in the sense that
   their fibre never contains a source together with its companion, and what do they cost in the
   square-root precision law?
7. **The unit line.** Is there a functor from receivers to the width line through which every
   oriented invariant factors, so that the dictionary is a theorem about the category of receivers
   and not a list?

### 4.4 Objects

| object | definition | present corpus form |
|---|---|---|
| oriented source | a signed measure on the log line (prime powers with weights, archimedean density, pole) together with an orientation datum | Chebyshev/Möbius source; companion class; holonomy class; inertia index |
| scaling cycle | x = aH + bV + f, f a test on the log line, with pairing = pole-plane form − Weil form | `ScalingCycle`, `scalingSurface` |
| node divisor | the multiset {log p^k} with multiplicity Λ(p^k)/√p^k, restricted to an aperture box | prime-power node sets; deletion prices |
| section space | aperture- and height-limited tests vanishing on the node divisor of the box | prime-blind tests; spectral second-moment theorems |
| degrees of freedom | Landau–Widom count of the section space | mean-value "T + N" term; large sieve constant N + Q² − 1 |
| effectivity cone E | {x : h⁰(x) ≥ 1}, required Bézout-closed and containing the open positive cone | RiemannRochAxiom, AmpleAxiom, BezoutAxiom |
| index | positive inertia of an intersection Gram; order of the pole read by a receiver | `hermPosIndex`, pole value and pole slope |
| holonomy ledger | the ℤ/2 gauge class of a signed incidence form; frustration set = prime-sum edges | `walkHolonomy`, PairAllocation, GlobalIncidenceAllocation |
| oriented reading | a reading r : D → O whose fibre separates every source from its companion | readings, shadows, collapses (SSIC); labelled moments |
| transport | a one-parameter family of receivers in damping, aperture, horizon or height, with its derivative identity | damping chain, Markov boundary flux, Buchstab horizon step |
| unit | the coordinate on the width line in which a transport reads Δ | damping, aperture, growth exponent, rate, depth, index |

### 4.5 Language

The field's vocabulary is already in the corpus and is adopted unchanged: reading, shadow, collapse
(invisible, fatal, neutral), resolution limit, unit, width, depth, aperture, horizon, damping,
admission, cofinal, receiver, producer, source, node, deletion price, ledger, allocation, payment,
frustration, holonomy, gauge, companion, parity pair, effectivity, Hodge defect, index.

Three words are added:

- **section**: a test vanishing on the node divisor of its box;
- **orientation-faithful**: a reading or a norm in which the companion class is continuous;
- **oriented transport**: a transport whose derivative identity has a sign-definite jump term.

A sentence in the field has the form: "In unit U, the oriented invariant I of the source S reads the
value v, by the count C, and the statement passes tests T ⊆ battery." Statements without a unit, a
count or a test list are not admitted.

### 4.6 Foundational principles

**P1. Counts before estimates.** An invariant of the field is integer-valued or lower semicontinuous;
its value is computed by a count (sections, lattice points, degrees of freedom, holonomy classes),
never by a bound. Bounds are corollaries.

**P2. Selectivity is a theorem, not a remark.** Every positivity statement must be accompanied by a
proof that it fails on the battery of §4.7 (the ACS principle: every positivity argument must use a
constraint that fake data violate).

**P3. Cofinality.** Statements are quantified over unbounded apertures, horizons and heights. A finite
instance is a refutation tool only. A single admitted damping or aperture translates zeros and bounds
no width.

**P4. Global payment.** The rank-one pole charge is never locally payable; the theory's certificates
are global by construction (gauge plus budget), and local certificates are used only to locate
frustration.

**P5. Orientation before magnitude.** Amplitude functionals are provably blind below ½; the field's
primary data are signed or integer-valued, and magnitude readings are admitted only as "third-kind"
data in the sense of SSIC (mass, dilution, two-aperture ratios).

**P6. Criticality.** The prime side is used at its full rate Λ(n)n^{−½}; nothing is subtracted from
the source; mechanisms add allowance. Any positive floor must respect the doubly exponential ceiling.

**P7. Unit hygiene.** A reformulation is progress only if it changes the input class. Every result is
tagged with its unit and its position on the width line.

### 4.7 Criteria the field must fulfil

These are the certification battery. A theorem of the field that claims to move the floor must pass
all applicable tests; a theory that cannot produce a theorem passing them within its first results
is to be retired by its own rule P7.

| test | content | corpus source |
|---|---|---|
| C1 golden datum | must fail for the Beurling system P = 1 − 5X + 5X² (integral Witt, FE, positive prime counts, impure) | `WittIntegralityIsNotPurity` |
| C2 shifted pair | must fail for ζ(s−a)ζ(s+a); the temperedness gate ε(L) = 1/(2 + log L) is the one proven selective instance | APT polynomial windows |
| C3 parity twins | must separate μ from its positive twin, every real character from its twin, Liouville from κd^{−½}, the Fermi row from its even flip | `char_parityPair`, `fermi_evenFlip_parityPair` (THIM) |
| C4 deformation | must not survive one Euler-factor deformation (Estermann), the theta-power family θ₃h^{a/4}, or k + t k^{(4m)} perturbations | killed routes KR-DEF and countermodels |
| C5 nodes | must be fatal at log 4 and free at log 6; must need every prime power | node criticality (BiScale), log 4 / log 6 separation (BVI §3.1) |
| C6 unit | must produce a cofinal bound in a width unit; one interior point is translation only | zero-width dictionary |
| C7 ceiling | any positive floor must decay at least like exp(−π e^{2(A−2)}) | walls ledger, RW |
| C8 Ω-laws | must not assert ψ(x) − x = O(√x) or M(x) = O(√x) | Littlewood, Mertens kills |
| C9 finite data | must not rest on a finite computation; every finite reading admits off-line extensions | mimicry theorems, SSIC |
| C10 rate | must use the prime rate in full; no Hardy weight exists | ACT criticality |
| C11 𝔽_q[T] | must reproduce the exact constant q^{−ε} cancellation and the curve Hodge index | ACCE, `curve_hodgeIndex_tfae` |
| C12 integrality | must land on "exactly one positive square" | `riemannHypothesis_iff_one_positive_square` |
| C13 no premise | no RH-equivalent as hypothesis; no Prop stand-ins; axioms audited | proof-integrity rules |
| C14 square-root precision | excluding depth β must cost β²L³; a cheaper certificate is wrong | SSIC precision law |

### 4.8 Research topics, in dependency order

**T1. Nyquist–Riemann–Roch on the scaling surface.** Define h⁰(box(A, T) − N_A) as the dimension of
aperture-A, height-T tests vanishing on the prime-power nodes of the box; prove the inequality
h⁰ ≥ (degrees of freedom) − (node count) with the node count's error term identified as the Chebyshev
defect E(s), the complete source invariant of AIP. The classical shadow is the mean value theorem's
T + N term; its diagonal is the square-root threshold a = L/2 (SRT), and sections beyond the
diagonal are large-values statements, of which Guth–Maynard is the strongest formalized instance.
First target: restate the zero-density bound 30/13 and the density hypothesis as section-existence
statements and identify which h¹ (functional-equation duality) term the density hypothesis requires.

**T2. The effectivity cone from sections.** With h⁰ from T1 define E and prove or refute the Bézout
axiom for it; test on the curve datum (must give the Hodge index, `curve_hodgeIndex_tfae`) and on
the golden datum (must fail C1). Locate the ring property used.

**T3. The index theorem of the receiver.** Prove that the order read by the pole law equals a count
of sections; reinterpret `riemannHypothesis_iff_one_positive_square` as index = Euler characteristic
of the node divisor, and compute the Euler characteristic from the ledger.

**T4. Balanced-scale Dedekind–Bernoulli statistics.** Expand the kernel statistic Λ_p(c') of the
von Mangoldt row in Kloosterman sums over primes; apply trace-function bounds at Q ≍ P; sum over
moduli with the block masses and the n^{−3}, n^{−4} tails retained; determine the exponent reached
against the dual norm. Expected outcome: a qualitative balanced-scale gain, with the quantitative
gap equal to the short-interval twisted prime sum.

**T5. Oriented transport in damping.** Find the h-transform of the damping chain under which the
centred semigroup is a contraction in pronic ℓ² at fixed η < ½, starting from the reciprocal
observable; prove or refute a Poincaré inequality on the orbit of the first column.

**T6. Oriented transport in aperture.** Derive the aperture derivative of μ(A) as a boundary-flux
identity of ACCE type; identify the sign-definite jump term; check compatibility with the ceiling.

**T7. Sum–difference inequalities at multiplicative targets.** Formulate odd Weil positivity as a
weighted inequality between difference-correlations and sum-correlations of a half-line profile at
prime-power lags; prove it on classes defined by support geometry (box trains, aligned towers,
light-cone bands), using the dominance law as the discrete model; locate the exact class where the
archimedean crossing collar must be paid globally.

**T8. The frustration index.** Define the minimal global payment of the odd Weil ledger at aperture
A as the ground energy of a ℤ/2 gauge system on the log grid with prime-sum frustration; compute it
for the train and tower families; prove or refute that it equals μ(A).

**T9. Orientation-faithful readings.** Classify readings by whether their fibre contains companions;
prove that every orientation-faithful reading crosses Nyquist, reads a magnitude, or adds third-kind
data (the SSIC trichotomy as a theorem about readings rather than floors); compute the precision cost
of the labelled-moment reading.

**T10. The width functor.** Construct the functor from receivers to the width line and prove that every
oriented invariant factors through it; this turns the dictionary into a theorem and the selectivity
battery into a list of non-objects of the category.

### 4.9 Relation to existing programmes

The field absorbs ACS (surface, λ-ring, Hodge index, defect) as its geometric core, SSIC (readings,
collapses, units) as its logic, SAEI and AIP (holonomy, allocation, lattice dominance) as its
combinatorics, THIM and BVI (observation closure, parity barrier, damping chain) as its analysis of
transport, ACT (criticality) as its spectral theory, and SRT, BiScale, APT, ACCC, ACCE as its
calibration and counter-model library. It does not replace them; it asks them one new question each,
the count behind the estimate.

Its external relatives are Deninger's cohomological programme and Connes–Consani's 𝔽₁ geometry
(the corpus holds `DeningerArithmeticThreeTermHodge.riemannHypothesis` and
`riemannHypothesis_of_deningerFiniteJetHodge_exhaustion_commutes` as conditional capstones, and
Connes' trace formula at Re s > 1), sampling theory (Landau, Beurling–Malliavin, Slepian–Landau–Widom),
index theory, and the additive combinatorics of sum and difference sets. The field's distinctive
claim against the first two is that the carrier need not be a cohomology: a dimension count of
band-limited sections with an arithmetic node divisor is a weaker and more concrete object, and the
corpus already proves instances of it.

### 4.10 What would retire the field

The field is retired if T1 cannot produce, from its h⁰, a statement strictly stronger than the mean
value theorem at the diagonal that is selective in the sense of C1 and C2; equivalently, if the
only sections it finds are those the large sieve already counts. The honest risk is that "section"
turns out to be a relabeling of "Dirichlet polynomial on a window", in which case the field reduces to
the classical theory of large values, and its contribution is the dictionary and the battery, not a
mechanism.

---

## 5. Evidence: what the corpus search returned

Searches run with `scripts/formal_tools.py research` (hybrid mode unless stated), with the
status they established. Full output in the log.

| query (abridged) | established |
|---|---|
| pair correlation beyond λ = 1 | not proved; `PairCorrelationFourThirds` is a premise; leading order for α < 1 proved |
| Riemann–Roch effectivity on scaling surface | axioms formalized, RH ⟺ ∃E; no construction |
| coercive norm on quotient by theta radical | nothing direct; generic coercivity lemmas only |
| cross-lobe odd-sector estimate | conditional only (`odd_eigenvector_eigenvalue_lt_half_of_cross_lobe_oneL_le_primeShift`) |
| Vinogradov mean value / Beurling selectivity | VMVT formalized with explicit constants; Beurling system library present |
| labelled moments / companion | `translatedMoment_companion`; cubic moments pin odd-modulus signs |
| interior martingale contraction | equivalence and compensated bound proved; no signed bound |
| Witt ghosts in sieve receiver | exact dictionary only (`selberg_wittSieveReceiver`, Verschiebung law) |
| twisted short prime sums | replacement-hypothesis theorem `window_energy_le_twisted_short_sums`; input not supplied |
| holonomy / frustration | `walkHolonomy_*` (SAEI); general gauge-holonomy library (HTGeometry) |
| Lorentz / Krein structures | several no-go modules; Pontryagin neutral-eigenvector lemma |
| Guth–Maynard (lexical) | `guthMaynardLargeValuesBound_holds` unconditional; 30/13 density |
| balanced-scale prime row | only the dual-norm reduction; nothing at Q ≍ P |
| S(T) spectral realization | prime operator not trace class (`xiOrderedSignedPrimeOperator_not_memSchattenClass_one`) |
| Hilbert–Pólya / Berry–Keating | generic operator lemmas only |
| Deninger | large conditional infrastructure; flow, Lefschetz trace, jet Frobenius |
| Connes trace formula | Theorem 4 asymptotics, positivity-type abstract theorem, resolvent form at Re s > 1 |
| cubic / higher-degree positivity | nonnegative cubic energies, inertia of coprime matrix; no closing principle |
| fractal uncertainty / Beurling–Malliavin | absent |
| two-aperture ratio of the Weil functional | absent; only the 3/10 window floor |
| renormalization in scale | absent as a framework |
| low-mode Schur complement | generic lemmas only |
| Lindelöf / moments | fourth moment unconditional; off-line tail moment window bound `exists_offLineTailMoment_window_le` |
| single-height prime phase saving | only in the Vinogradov–Korobov regime (t ≥ N^{22}) |
| entropy / information | `riemannReflectedSourceEntropy_eq_zero_iff` (no-go file); no bound |
| Selberg trace / Maass | infrastructure, no spectral-gap use for ζ |
| de Branges / canonical systems | strict Hermite–Biehler ⇒ RH; HB unproved |
| Hodge index / function field | `scalingSurface_hodgeIndex_iff`, `riemannHypothesis_iff_one_positive_square`, `curve_hodgeIndex_tfae`, `zeta_hodgeDefect_iff` |
| proportion of zeros / mollifiers | Levinson infrastructure; ξ′ proportion theorem |
| Hardy–Littlewood singular series in rows | `selberg_and_damped_tangent_correlations_agree`, `tendsto_truncated_tupleSingularSeries` |
| boost group / Casimir | `hyperbolicCasimirInvariant_rapidity_invariant` |
