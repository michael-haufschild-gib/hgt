# Suzuki screw compact-hull and parity law

- **ID:** `suzuki-screw-compact-hull-parity-law`
- **Stage:** 2 — fully proved on paper
- **Type:** UNIVERSAL SUMMABLE-SPECTRUM LAW / SUZUKI LIMIT-PROBLEM SOLUTION
- **Scientific status:** `[PAPER-PROVED] [SUPPORTING RESULT] [REJECTED AS FLAGSHIP]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **RH used:** only in the Xi specialization, to make all zero frequencies real
- **Computation used:** no
- **Primary source problem:** Suzuki 2023, Section 7.1, determination of
  `liminf Psi(t)` and `limsup Psi(t)` under RH
- **Formal modules:**
  `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewHull.lean`;
  `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewValue.lean`;
  `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewRecurrence.lean`;
  `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewDistribution.lean`;
  `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewHilbert.lean`;
  `formal/GaloisForLFunctions/RHTower/SuzukiScrewCompactHullParityLaw.lean`

## 1. Significance and exact novelty boundary

**Disposition (2026-07-22):** mathematically valid but not significant enough for requested
flagship paper.  Retained as supporting Suzuki dynamics; superseded by the finite-aperture
boundary-phase locking program.

Suzuki proves that RH is equivalent to boundedness of his function `Psi` and remarks that even
under RH its `liminf` and `limsup` are difficult to determine.  He obtains
`liminf Psi=0` and the absolute upper endpoint only after additionally assuming simple zeros and
rational independence of all positive zero ordinates.  Matsumoto--Suzuki's later `M`-function
value-distribution theorem likewise assumes rational independence in order to construct a density.

The theorem below removes simplicity and rational independence from:

1. `liminf Psi=0`;
2. existence of the limiting value distribution;
3. determination of its support;
4. cofinal recurrence of every admissible value.

It also replaces rational independence in the upper-endpoint problem by an exact necessary and
sufficient parity condition on the complete integer-relation lattice.  This condition is strictly
weaker than rational independence.

Compact-group duality, Haar equidistribution, and Kronecker approximation are classical.  Candidate
novelty is the complete infinite-spectrum hull/support/parity law and its application to Suzuki's
exact Xi screw series, not invention of those ingredients.  External priority remains unverified.

## 2. Universal setup

Let `I` be finite or countable.  Let `omega_i>0` be distinct real numbers, let `a_i>0`, and
assume

```text
A:=sum_(i in I) a_i < infinity.                          (2.1)
```

Define

```text
P(t)=sum_i a_i(1-cos(omega_i t)),                        (2.2)
Theta(t)=(exp(i omega_i t))_i in T^I,                    (2.3)
K=closure(Theta(R)) subset T^I,                          (2.4)
F(z)=sum_i a_i(1-Re z_i).                                (2.5)
```

Let `Z^(I)` denote finitely supported integer families and define the relation lattice

```text
R_omega={k in Z^(I): sum_i k_i omega_i=0}.               (2.6)
```

The series in `(2.2)` and `(2.5)` converge uniformly because every summand has absolute value at
most `2a_i`.

## 3. Universal compact-hull law `[PROVED]`

### Theorem 3.1 (relation hull)

`K` is a compact connected abelian group and

```text
K={z in T^I:
     product_i z_i^(k_i)=1 for every k in R_omega}.       (3.1)
```

Every tail `Theta([T,infinity))`, `T in R`, is dense in `K`.

#### Proof

The product torus is compact, `Theta` is a continuous homomorphism, and the closure of a subgroup is
a compact subgroup.  Since `R` is connected, `Theta(R)` and its closure `K` are connected.

Every continuous character of the countable product torus is a finite-coordinate monomial

```text
chi_k(z)=product_i z_i^(k_i),   k in Z^(I).
```

It is trivial on `Theta(R)` exactly when

```text
chi_k(Theta(t))=exp(i t sum_i k_i omega_i)=1
```

for every real `t`, equivalently when `k in R_omega`.  Closed subgroups of a compact abelian group
are the common kernels of the characters trivial on them, giving `(3.1)`.

For tail density, put `S=closure(Theta([0,infinity)))`.  It is a compact subsemigroup of `K`.  If
`x in S`, compactness gives a subsequence `x^(n_j)` converging to some `y`; after thinning,

```text
x^(n_(j+1)-n_j) -> 1.
```

If the positive differences are eventually one then `x=1`; otherwise
`x^(n_(j+1)-n_j-1)->x^(-1)`.  Hence every `x in S` has its inverse in `S`, so `S` is a group.  It
contains `Theta([0,infinity))` and therefore also its inverses `Theta((−infinity,0])`; thus `S=K`.
Multiplication by `Theta(T)` proves density of every tail.  QED.

### Theorem 3.2 (no-gap cofinal value law)

There is a number

```text
M=max_(z in K)F(z)                                      (3.2)
```

such that the limit points of `P(t)` on every cofinal tail are exactly

```text
F(K)=[0,M].                                             (3.3)
```

For every `y in [0,M]` and `epsilon>0`, the set

```text
{t>=0: |P(t)-y|<epsilon}                                (3.4)
```

is relatively dense.  For every interior value `0<y<M`, the exact level set

```text
{t>=0:P(t)=y}                                           (3.5)
```

is relatively dense.

#### Proof

Uniform convergence makes `F` continuous and `P=F o Theta`.  Since every tail of `Theta` is dense,
the cofinal limit set is `F(K)`.  This image is compact and connected, hence a closed interval.
Every summand of `F` is nonnegative and `F(1)=0`, so its minimum is zero; compactness gives the
maximum `M`, proving `(3.3)`.

For a nonempty open `U subset K`, minimality of the translation flow gives, for every `x in K`, some
`s_x>=0` with `x Theta(s_x) in U`.  Thus the open sets `U Theta(−s)`, `s>=0`, cover `K`.
Compactness produces a finite subcover with times at most `L`.  Consequently every interval
`[tau,tau+L]` contains a time whose phase lies in `U`.  Apply this to
`F^(-1)((y-epsilon,y+epsilon))` to obtain `(3.4)`.

If `0<y<M`, choose nonempty open phase sets on which `F<y` and `F>y`.  Their return times have
bounded gaps.  Starting at arbitrary `tau`, visit the first and then the second within a uniformly
bounded total time.  Continuity of `P` gives a crossing `P(t)=y` between the two visits.  This proves
relative density of `(3.5)`.  QED.

### Theorem 3.3 (Haar value-distribution without independence)

Let `m_K` be Haar probability measure on `K` and let

```text
nu=F_*m_K.                                              (3.6)
```

For every bounded continuous `phi:R->C`,

```text
lim_(T->infinity) (1/T) integral_0^T phi(P(t))dt
  =integral_R phi(x)dnu(x),                             (3.7)
supp(nu)=[0,M].                                         (3.8)
```

#### Proof

If `chi` is a nontrivial character of `K`, then

```text
chi(Theta(t))=exp(i lambda_chi t)
```

with `lambda_chi != 0`; otherwise density of `Theta(R)` would make `chi` trivial.  Therefore its
time average is zero.  Characters span a uniformly dense self-adjoint algebra in `C(K)`, so uniform
approximation proves that time averaging along `Theta` converges to Haar integration for every
continuous function on `K`.  Apply this to `phi o F` to get `(3.7)`.

The support is contained in `F(K)`.  Conversely, if an open interval meets `F(K)`, its inverse image
under `F` is a nonempty open subset of `K`.  Every nonempty Haar-open set has positive measure,
because finitely many translates cover the compact group.  Hence the interval has positive
`nu`-measure, proving `(3.8)`.  QED.

## 4. Universal parity law `[PROVED]`

### Theorem 4.1 (odd-relation obstruction)

With `A` from `(2.1)`,

```text
M=2A
 iff (-1)_i belongs to K
 iff sum_i k_i is even for every k in R_omega.           (4.1)
```

#### Proof

For every `z in K`,

```text
2A-F(z)=sum_i a_i(1+Re z_i)>=0.                         (4.2)
```

Because every `a_i` is positive, equality holds exactly when `Re z_i=-1` for all `i`, hence exactly
when `z_i=-1` for all `i`.  Compactness makes the maximum attainable, proving the first equivalence.
By `(3.1)`, the all-minus-one phase belongs to `K` exactly when

```text
product_i (-1)^(k_i)=(-1)^(sum_i k_i)=1
```

for every relation `k`, which is exactly the even-total condition.  QED.

### Strict weakness relative to rational independence

Rational independence makes `R_omega={0}` and therefore implies `(4.1)`.  It is not necessary.  For
example, the relation `omega_1+omega_2=omega_3+omega_4` has coefficient sum zero and does not obstruct
the all-minus-one phase.  In contrast, `omega_3=omega_1+omega_2` has odd total coefficient and forces
`M<2A`.

## 5. Hilbert screw-hull law `[PROVED]`

Define

```text
S(z)_i=sqrt(a_i/2)(1-z_i) in ell^2(I).                  (5.1)
```

The map is continuous and injective, and

```text
||S(z)-S(w)||^2=F(z conjugate(w)),                       (5.2)
||S(Theta(t))-S(Theta(u))||^2=P(t-u).                    (5.3)
```

Thus closure of the summable-spectrum screw line is a compact connected monothetic group in its
intrinsic Hilbert metric, and `(3.3)--(4.1)` are geometric radius and recurrence laws for that
compact screw hull.

#### Proof

Square summability follows from `(2.1)`.  Expanding coordinatewise gives

```text
(a_i/2)|z_i-w_i|^2=a_i(1-Re(z_i conjugate(w_i))).
```

Summation proves `(5.2)` and `(5.3)`.  Uniform tail control by `2a_i` proves continuity.  Positive
weights make `S` injective.  QED.

## 6. Suzuki's Xi screw function `[PROVED FROM RH]`

Assume RH.  Let `Gamma_+` be the distinct positive ordinates of Xi zeros and let `m_gamma` be their
multiplicities.  Put

```text
a_gamma=2m_gamma/gamma^2.                               (6.1)
```

The centered Hadamard expansion gives `sum a_gamma<infinity`, and Suzuki's exact series is

```text
Psi(t)=sum_(gamma in Gamma_+) a_gamma(1-cos(gamma t)).   (6.2)
```

Let `K_Xi` be the relation hull of the positive ordinates and

```text
M_Xi=max_(z in K_Xi)
       sum_gamma 2m_gamma/gamma^2 (1-Re z_gamma).        (6.3)
```

Then, without simplicity or rational independence,

```text
liminf_(t->infinity) Psi(t)=0,                           (6.4)
limsup_(t->infinity) Psi(t)=M_Xi,                        (6.5)
cofinal-limit-set(Psi)=[0,M_Xi].                         (6.6)
```

Every approximate value return is relatively dense; every interior level is attained relatively
densely.  A limiting probability distribution exists, without LI, and has support exactly
`[0,M_Xi]`.

Finally,

```text
M_Xi=2 sum_(all Xi zeros gamma) 1/gamma^2               (6.7)
```

if and only if every finite integer relation among distinct positive Xi ordinates has even total
coefficient.  Multiplicity affects the weights but creates no simplicity premise.

Suzuki proves `RH iff Psi is bounded`.  Under RH, `(6.2)` is a uniform limit of trigonometric
polynomials, hence uniformly Bohr almost periodic.  Every uniformly almost periodic function is
bounded.  Therefore one also obtains the unconditional equivalence

```text
RH iff Psi is uniformly Bohr almost periodic.           (6.8)
```

Here “unconditional” means the equivalence itself assumes neither side; the forward proof uses RH
and the reverse proof derives RH from almost periodicity through Suzuki's boundedness criterion.

## 7. What is solved and what remains open

### Solved

- Suzuki's RH-conditional `liminf` problem: `(6.4)` needs neither simplicity nor LI.
- No-LI existence of the limiting value distribution and exact support `(6.6)`.
- Complete cofinal recurrence geometry, including syndetic returns and exact interior crossings.
- Exact classification of when Suzuki's conjectural absolute `limsup` endpoint is correct.
- Geometric RH criterion `(6.8)`.

### Not solved

- RH itself is not proved.
- The theorem does not prove the even-relation condition for actual Xi ordinates; consequently it
  does not assign a numerical value to `M_Xi` in the relation-obstructed case.
- It constructs a limiting probability measure, not necessarily a continuous density.  The
  Matsumoto--Suzuki density theorem under LI remains stronger on regularity.
- It does not prove Suzuki's 2026 cofinal finite-interval spectral-operator conjecture.

## 8. Hostile audit

1. **Positive tails:** proved by compact-semigroup inversion, not assumed from two-sided density.
2. **Infinite spectrum:** all phase-dependent series are uniformly controlled by `2sum a_i`.
3. **Connectedness:** follows from closure of the connected one-parameter subgroup, so no-gap support
   is valid even at infinite rational rank.
4. **Haar support:** nonempty open preimages have positive Haar measure.
5. **Infinite-rank parity:** characters of the product torus have finite support, exactly matching
   finite integer relations.
6. **No hidden LI:** relation lattice is arbitrary throughout.
7. **No simplicity:** multiplicities are absorbed into positive weights.
8. **No density overclaim:** only probability-measure existence and support are asserted without LI.
9. **No RH overclaim:** all real-frequency conclusions for Xi are explicitly downstream of RH;
   `(6.8)` is an equivalence, not a proof of either side.
10. **No computation:** proof is structural and exact.

Verdict: `SURVIVES HOSTILE ATTACK`.

## 9. Novelty audit

- Internal search found Suzuki's scalar Cesaro-curvature recurrence and generic almost-periodic hull
  infrastructure, but no theorem matching `(3.1)--(4.1)` or its Xi specialization.
- Suzuki 2023 states the `liminf/limsup` difficulty and uses RH + simplicity + rational independence
  for the displayed endpoints.
- Matsumoto--Suzuki 2025 constructs `M`-function densities under rational independence; targeted
  inspection found no relation-hull replacement or no-LI support theorem.
- Suzuki 2026 focuses on finite-interval Weil operators and contains no matching recurrence or
  parity theorem.
- Targeted arXiv searches for Suzuki screw almost periodicity, relation-torus value laws, and parity
  obstructions found no matching application.  This is not a certified priority search.

## 10. Paper and formalization gates

- [x] named source problem identified
- [x] universal theorem stated
- [x] complete dependency-closed proof
- [x] Xi specialization
- [x] significance and hostile audits
- [x] internal/current-primary-source collision audit
- [ ] manuscript completed
- [x] exact Lean formalization of the universal laws and their ordinate specialization
- [ ] independent specialist novelty review

## 11. Lean formalization

All of Sections 2--5 are formalized unconditionally, with no `sorry`, `admit`, `axiom`,
`opaque`, or `unsafe` declaration; every listed theorem's axiom audit returns exactly
`[propext, Classical.choice, Quot.sound]`.  The countable index hypothesis of `(2.1)` is
carried as `[Countable I]`; the product torus is `I → UnitAddCircle` and the screw line is
the one-parameter subgroup `screwPhase omega t i = omega i * t / (2 * pi)`.

### Universal compact-hull law `(3.1)`

`screwHull_eq_screwAnnihilator` : the closure of the screw line equals the common kernel of
the finite-support characters whose detuning vanishes.  Supporting statements:
`isCompact_screwHull`, `isConnected_screwHull`, `screwHullSubgroup` with
`add_mem_screwHull`, `neg_mem_screwHull`, `sub_mem_screwHull`.

The proof avoids Pontryagin duality.  Uniform time sampling on `[-A,A]` has finite-support
Fourier coefficients equal to sinc kernels (existing corpus module
`InfiniteTorusFourierWeakConvergenceLaw`); letting `A -> infinity` selects the unique
probability law `screwHaar` whose coefficients are the indicator of the relation lattice
(`existsUnique_screwHaar`, `screwHaar_fourier`).  Portmanteau gives
`screwHaar_measure_hull : mu (hull) = 1`, and Fourier uniqueness gives
`screwHaar_map_add_self`: `mu` is invariant under translation by every annihilator point.
Invariance forces `hull` and `hull - z` both to have full mass, so they meet, and the group
law returns `z` to the hull.

### Tail density and the no-gap cofinal value law `(3.3)`

`closure_screwPhase_image_Ici` : every forward tail of the screw line is dense in the hull.
Its engine is `neg_mem_screwForwardHull`, the compact-semigroup inversion argument, proved
by extracting a convergent subsequence of iterates and passing to the gap iterates.

`screwValue_image_screwHull` : the phase-defect energy image of the hull is `Icc 0 M`;
`closure_screwSeries_image_Ici` : the same interval is the closure of the image of every
cofinal tail.  Consequences `screwSeries_liminf_eq_zero` and
`screwSeries_limsup_eq_screwHullMax` are exactly `(6.4)` and `(6.5)` at the universal level.

### Relative density `(3.4)`, `(3.5)`

`exists_window_screwPhase_mem_of_isOpen` : any open set meeting the hull is entered inside
one fixed time window from any starting time.  `exists_window_screwSeries_near` and
`exists_window_screwSeries_eq` are the approximate and exact level-set versions; the second
uses the intermediate value theorem between a sub-level and a super-level visit.

### Haar value distribution `(3.7)`, `(3.8)`

`screwHaar_pos_of_isOpen` : any open set meeting the hull carries positive invariant mass
(finitely many hull translates of it cover the hull, and all translates have equal mass).
`screwHaar_support` : the invariant law is supported exactly on the hull.
`screwHaar_unique` : it is the only probability law carried by the hull and invariant under
all its translations, so it is exactly the Haar probability measure `m_K` of `(3.6)`.
`screwValueLaw` is its pushforward along the energy; `tendsto_timeAverage_screwSeries` is
the value-distribution law in explicit time-average form, and `screwValueLaw_support` is
`(3.8)`.

### Parity law `(4.1)`

`infiniteTorusFourier_screwAntipode` : the antipodal phase evaluates a character to
`(-1)^(total coefficient)`.  `screwAntipode_mem_screwAnnihilator_iff` converts hull
membership of the antipode into the even-total-coefficient criterion, and
`screwHullMax_eq_two_mul_tsum_iff` is `(4.1)` itself: for strictly positive summable
weights, `M = 2 * sum a` exactly when every finite integer relation has even total
coefficient.  `parity_of_screwRelationLattice_trivial` records that rational independence is
sufficient but not necessary.

### Hilbert screw law `(5.1)`--`(5.3)`

`screwEmbed` is the `lp _ 2` embedding `z |-> sqrt(a i / 2) * (1 - z i)`;
`sq_norm_screwEmbed_sub` is `(5.2)` and `sq_norm_screwEmbed_screwPhase_sub` is `(5.3)`.
`screwEmbed_injective` gives injectivity for strictly positive weights.

### Suzuki specialization

`RHTower/SuzukiScrewCompactHullParityLaw.lean` instantiates the universal laws at the
Suzuki weights `a_gamma = 2 m_gamma / gamma^2`, giving
`suzukiScrewFunction_liminf_eq_zero`, `suzukiScrewFunction_limsup_eq`,
`closure_suzukiScrewFunction_image_Ici`, `exists_window_suzukiScrewFunction_near`,
`exists_window_suzukiScrewFunction_eq`, `tendsto_timeAverage_suzukiScrewFunction`,
`suzukiScrewFunction_law_support`, `suzukiScrewFunction_limsup_eq_absolute_bound_iff`, and
`sq_norm_suzukiScrewEmbed_sub`.

### What is deliberately outside the formal tree

Three inputs of Section 6 are quoted external analysis, not corpus theorems, and therefore
appear only as the hypotheses of the specialization (a countable family of nonzero real
ordinates with positive multiplicities and summable weights):

1. Suzuki's exact screw expansion `Psi(t) = sum_gamma a_gamma (1 - cos(gamma t))`;
2. reality of the ordinates, which under RH is what makes the family real at all;
3. Suzuki's criterion `RH iff Psi is bounded`, used only for the geometric restatement
   `(6.8)`.

Granting `(1)` and `(2)`, statements `(6.4)`--`(6.7)` are exactly the specialization
theorems listed above.  `(6.8)` remains outside because it consumes `(3)`.
