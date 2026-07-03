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
