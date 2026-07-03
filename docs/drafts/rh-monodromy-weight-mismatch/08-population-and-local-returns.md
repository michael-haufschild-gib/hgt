# 08 — After the R6 negative: population forcing (P_k) and local returns (H-loc)

Register: SEARCH-register document. One derivation `[DERIVATION]` (elementary, from cited
theorems), two labelled conjectures, one open-core candidate with a running pre-registered
probe (R6-loc). Companions: `06-reduction.md` (consumes (R_k)), `07-index-formula.md`
(transfer lemma §3, R6 verdict §6), board wave-2b pre-registrations.

---

## 1. The sub-Bagchi constraint `[DERIVATION]`

In the seed-world (some ξ-zero right of the line exists), strong recurrence of ζ FAILS:
Bagchi's own argument (verified C2: Rouché + full count + zero-density) shows strong
recurrence + a seed ⟹ ≥ cT strip zeros ⟹ contradiction with Carlson/Ingham. So:

> Any mechanism that propagates a seed into a population must be STRICTLY WEAKER than
> full-data strong recurrence — in the only world where it has work to do, the full
> recurrence is already dead.

This is the theory-side echo of the measured R6 negative (defect recurrence without data
recurrence in the D–H family). Mechanism candidates must be graded by how much less than
full-data recurrence they demand. Two survive below.

## 2. Population forcing and the droves dichotomy

**(P_k) `[CONJECTURE, open core candidate]`** If some admissible window has w_k ≠ 0 (a
coarse seed), then N(σ₀', T) ≫ T for some σ₀' > 1/2. With (D), (P_k) ⟹ defect sets empty
⟹ (06-reduction Step 2) RHLadder k. No recurrence input anywhere.

**Droves dichotomy `[CONJECTURE]`** For Dirichlet series with a Riemann-type functional
equation and reality: off-line zeros come with LINEAR density or not at all — no member of
the class has a sparse (o(T), nonempty) off-line zero set.

Evidence inventory (all verified in checks/):
- Every known FE-without-Euler example carries droves, UNCONDITIONALLY: D–H, Epstein-type,
  and general linear combinations (Voronin; Lee–Nakamura–Pańkowski ≫ T in every fixed
  strip). Nobody has ever exhibited FE + a lone (or sparse) off-line zero family.
- The trivial "manufacture a lone zero" move fails structurally: P(s)·ζ(s) with a
  symmetric real polynomial P has the FE and four extra zeros, but is NOT a Dirichlet
  series (unbounded on vertical lines in the convergence half-plane) — the class axiom
  itself excludes surgical zero-insertion. This is worth holding onto: **the
  Dirichlet-series axiom is a rigidity constraint against local surgery**, the same role
  boundedness of the critical orbit plays in the quadratic family.
- Hamburger (verified, Perelli Thm 2.1) closes the exact-ζ-FE cell entirely: there, the
  only member is cζ, so the dichotomy is vacuously true.
- For ζ itself the dichotomy at k=1 IS the level-1 ladder modulo (D): sparse-nonempty is
  the only forbidden regime, and (D) already forbids dense.

B1 reframed (replaces the FE-grafting hunt as stated on the board): **hunt for a
Dirichlet-series class with FE + o(T) off-line density + at least one off-line zero.**
Constructing one refutes the dichotomy and names the missing Euler feature; proving
emptiness in any usable class IS (P) for that class — either exit terminalizes.

## 3. Local returns (H-loc) — the surviving recurrence shape

The Rouché-transfer lemma (07 §3) never used the box shape: for ANY compact contour C
avoiding zeros, with margin m = min_C |ξ|, a τ with sup_C |ξ(·+iτ) − ξ| < m transfers the
enclosed zero configuration to height +τ. Take C = a small fixed circle around the seed.

**(H-loc) `[OPEN CORE candidate]`** If a seed ρ₀ exists, then for some fixed circle
C = ∂B(ρ₀, r) the return set {τ : sup_C |ξ(s+iτ) − ξ(s)| < m(C)} has positive upper
density. (H-loc) ⟹ (R_k) ⟹ (with (D)) RHLadder k, verbatim as in 07 §3.

Why this evades the R6 negative:
- R6's contour had perimeter ≈ 5.4 and 120 effective dimensions of data; its margin was
  set by the box edges' closest approach to the zero POPULATION. A radius-r circle around
  one zero carries data determined (by Cauchy) to accuracy δ by ~log(1/δ) Taylor
  coefficients at the center: the return event is effectively FINITE-DIMENSIONAL — a
  value-recurrence event for the jet (ξ, ξ', ..., ξ^{(K)}) at one point, the genre where
  Bohr–Jessen distribution theory and Voronin/Bohr–Courant denseness live.
- It is strictly sub-Bagchi (§1): no 2-d compact, no approximation near other zeros, one
  base point, fixed tolerance.

**The rates subtlety (why denseness alone settles nothing — both directions):**
Bohr–Courant-type denseness of ζ-values (and jet-denseness variants) at fixed
σ ∈ (1/2, 1) produces points where the jet is arbitrarily close to a zero-jet
(0, ..., 0, a). This does NOT manufacture actual off-line zeros — forcing a zero from a
small value needs the smallness at height t to beat the local derivative scale M(t), and
denseness comes with no rate. (Otherwise RH would be trivially false — a useful sanity
check.) Symmetrically, denseness does not prove (H-loc): positive upper density of
FIXED-tolerance returns is a recurrence statement, stronger than "the orbit enters every
neighborhood infinitely often". The fixed-margin, fixed-circle formulation is exactly the
register where the transfer lemma is exact (no Taylor estimates needed) and where the
statement is measurable. `[CHECK at promotion: exact Bohr–Courant and Voronin jet-denseness
statements + whether any recurrence-rate refinement exists in the Bohr–Jessen literature.]`

## 4. The running experiment decides the mechanism ranking

R6-loc (pre-registered on the board, running): circle r = 0.05, 48 points, around the
certified D–H zero at t ≈ 85.7; τ ∈ [0, 400] step 0.05.
- **Sub-margin returns found** ⟹ (H-loc) has empirical support in the family; the
  ζ-question sharpens to a recurrence property of the finite jet's value distribution at
  fixed σ₀ — a named, literature-adjacent object; (P_k) becomes the fallback.
- **No returns (min d/m > 3)** ⟹ NO recurrence mechanism at any scale sustains the
  family population; (P_k)/droves-dichotomy stands alone as M1's re-cut, and Arc B aims
  entirely at §2.

## 5. Opened

1. R6-loc readout (imminent) + if positive: R6-loc-b at a second zero and larger τ-range
   (return-gap statistics vs the defect-gap median 18).
2. B1' (the §2 hunt) — first move: check whether ANY Beurling/DMV positive system from the
   banked X5 bucket has a MEASURED off-line density (are its off-line zeros droves too?).
3. The surgery-rigidity observation (§2, P·ζ exclusion) as a lemma candidate: "no member
   of the Dirichlet-series-FE class differs from another by a finite divisor" — a
   finite-surgery no-go, Lean-able against the class axioms; would give the dichotomy its
   first unconditional fragment.
4. Cross-link to hgt proper: the dichotomy is a "constraint, not flow" statement — the
   population is fixed by the class axioms (FE + Dirichlet-series rigidity), not grown
   zero-by-zero; the moat/fiber geometry (R5b) is its measured shadow in the c-plane.

---

## 6. Experiment verdicts (2026-07-03, same day) — §4's decision tree resolved

R6-loc + the radius scan (`computations/R6LOC-RESULTS.md`, pre-registered): the middle
outcome, sharper than either registered branch. No positive-density statement is measured
(that clause of (H-loc) stays open), but **certified fixed-τ local transfers EXIST**: with
the radius as a free dial, the banked zero's circle data returns strictly within margin at
τ = 91.005, transferring it onto the zero at t ≈ 176.70. The R6 negative was a
contour-size artifact — transfer fails globally and works locally. Measured structure
behind it: the local jets of distinct off-line zeros are approximate copies of one another
(near-returns land exactly on the population), so the family's defect recurrence is
sustained by a lattice of pairwise local similarities rather than by ambient
almost-periodicity.

C5 (verified, spot-checked) calibrates §2: FE-free Beurling systems DO realize the
sparse-but-nonempty regime (finitely-many-zero systems exist; no zero-count asymptotic
without FE — Révész–Pintz, verbatim), so **the FE is the load-bearing axiom of the droves
dichotomy**; and Hilberdink–Lapidus's generalized-FE Beurling class is the candidate
testbed (B1' first move). The Lean fragment is banked: `RHTower.no_polynomial_surgery`
(no finite divisor surgery within the Dirichlet-series class, axiom-clean).

Updated ranking: (H-loc) = instantiated-but-ungraded (needs the density clause);
(P_k)/power-droves = co-primary (thresholds now T^{θ(σ₀)+ε} after the quantified
Reduction). Next objects: **R7 transfer graph** (recurrence skeleton of the population;
pre-register density of the graph), and the Hilberdink–Lapidus FE-class reading.

## 7. The graded rung, and the Deuring–Heilbronn stress test (2026-07-03)

**The rung, explicit.** Fix δ ∈ (0, 1/2) and write the quantified Reduction's open core
(06 §6) at level σ₀ = 1−δ as a single statement:

> **(Rung_δ)** `[OPEN CORE]` If ζ has a zero ρ with Re ρ ≥ 1−δ, then for infinitely many T
> the count of zeros with Re ≥ 1−δ−ε, 0 < Im ≤ T is ≥ T^{3δ/(1+δ)}·(log T)^6.

By 06 §6, (Rung_δ for all δ) ⟹ RH, one strip at a time; each rung needs only ITS OWN level.
The budget θ(1−δ) = 3δ/(1+δ) → 0 as δ → 0: at δ = 0.01 the demand is T^{0.0297} companions —
barely more than polylog. The population data (R2: D–H droves are LINEAR, T/21) sits far
above every rung, so the FE-class behaviour, where a strip zero exists at all, over-fulfils
the budget by a power.

**Attack-as-false: the repulsion guard.** The droves dichotomy (§D) must survive the one
classical configuration engineered to violate it: the exceptional-zero world. The
Deuring–Heilbronn phenomenon `[CHECK at promotion: exceptional zero repels other zeros —
Linnik, log-free density; Iwaniec–Kowalski ch. 18]` is the ONLY known mechanism by which a
single high zero constrains the rest of the population — and its sign is REPULSION: a lone
zero near σ = 1 makes companions scarcer, not denser. A Siegel-type configuration (one
zero, cleared neighbourhood) is precisely "non-absent without droves" — it is the shape a
COUNTEREXAMPLE to (Rung_δ)'s provability at small δ would take. Two consequences:

1. **The difficulty profile of the ladder is non-monotone.** Small δ: tiny budget
   (T^{3δ}), but the repulsion guard is strongest exactly there (repulsion technology
   lives near σ = 1) — the hypothesis "one zero forces companions" fights the one proven
   phenomenon in the region. Large δ (σ₀ → 1/2+): droves are the measured/expected
   behaviour (Voronin ≫T in fixed strips for the classes that do have zeros; D–H linear),
   but the budget grows to linear. The rungs are guarded at the weak end by
   Deuring–Heilbronn and at the strong end by the budget.
2. **The right attack point is an interior saddle** `[new question]`: the crossover σ₀*
   where the repulsion guard has decayed (repulsion constants degrade polynomially away
   from σ = 1) while θ(σ₀) is still ≪ 1. Locating σ₀* — even heuristically, from the
   explicit constants in log-free density theorems vs θ(σ₀) — is a concrete, bounded task
   and would name the thinnest point of the whole Reduction.

Note the alignment: repulsion is an EXPLICIT-FORMULA effect (power sums, not value
distribution), i.e. it lives on M1's side of the house (07), untouched by the blind cone
(10). The rung program and the phase law are the two currently open non-universality
surfaces; the saddle question is where the first one becomes quantitative.

### 7.1 C7 verdicts (2026-07-03, verified-fetched — checks/c7-repulsion-density-note.md)

**Budget, updated with real constants.** Near σ = 1 the density input to (Rung_δ) is not
Ingham but the Halász–Turán shape N(σ,T) ≪ T^{c(1−σ)^{3/2}}(log T)^B:
- explicit (Bellotti arXiv:2311.05136 Thm 1.2, σ₀ ≥ 0.98): c = 57.8875, B = 11.548 —
  beats Ingham's 3δ/(1+δ) for δ < 0.0027 and Huxley's 3δ/(2−3δ) for δ < 0.00067;
- non-explicit (Heath-Brown 2017, via Richert-shape bounds): c < 1/2 — at δ = 0.01 the
  rung budget is T^{0.0005}, at δ = 0.001 it is T^{0.000016}: the demand on the forcing
  mechanism is essentially polylog at the thin end. (Bookkeeping: the rung's log-power is
  B+1 of the zone used — 6 in the Ingham zone, 45 in Huxley's, 12.5 in explicit-HT's.
  A log-free zone for ζ also exists: Bellotti arXiv:2405.12545.)

**Guard, vacated.** The Deuring–Heilbronn phenomenon is intrinsically q-aspect and
cross-family (a real exceptional zero of one L(s,χ_D) repelling zeros of the OTHER
L-functions of the modulus); the delegate's targeted search for a t-aspect self-repulsion
analogue for ζ (a lone high zero at height t₀ repelling companions at other heights) came
back NEGATIVE (queries logged in the note). So §7's stress test softens decisively: no
theorem OPPOSES population-forcing near σ = 1 in the t-aspect — and none provides it. The
territory is mechanism-empty in both directions, consistent with C0 #5's verified absence
of any literature on hypothetical off-line populations.

**The saddle question, re-cut constructively.** With the guard vacant, the thin end is
genuinely thin, and the program's sharpest form is no longer "locate σ₀*" but:

> `[OPEN TARGET]` Build ANY t-aspect population-forcing mechanism at σ near 1: one zero of
> ζ at Re ρ ≥ 1−δ forces ≥ T^{cδ^{3/2}}(log T)^{B+1} zeros at level 1−δ−ε infinitely often
> — with c < 1/2 available, a nearly-polylog yield suffices. Candidate raw materials, none
> universality-shaped (so the blind cone is silent here): the explicit-formula resonance of
> a near-unity zero (x^{β₀} term of near-main-term size — M1/07's side of the house), the
> a.p. structure of log ζ near σ = 1 (absolutely convergent Euler tail — the ONE region
> where the Euler product converges and might act on the recurrence side for once, cf. the
> chiasmus 10 §6), and Turán power-sum lower bounds.

That last point deserves its own flag: near σ = 1 the Euler product is absolutely
convergent, so log ζ(σ+it) is a UNIFORMLY almost periodic function there — Bohr's theory
applies directly, with no universality needed. A zero at σ₀ = 1−δ sits just below this a.p.
zone; the rung asks whether the a.p. structure immediately above it can be made to force
recurrence just below it. `[CONJECTURE space — boundary-leakage of almost periodicity]`
