# Route P cubic single-orbit global contact phase diagram

- **ID:** `CUBIC-SINGLE-ORBIT-GLOBAL-CONTACT-PHASE`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** completed-Xi cubic irregular-microlocal Riemann--Hilbert route
- **Statement:** For arbitrary genus and any nonempty marked-point family with one Stokes orbit at each point, one explicit global contact-budget coefficient completely classifies the unit-Rees completed-Xi cubic landing fibre: it is nonempty exactly when that coefficient is negative.

## Goal

Solve the full abstract inverse-landing problem in the single-Stokes-orbit sector, rather than add
another microlocal foundation layer or another special-case obstruction.  This determines exactly
which topology, ramification, and pairwise Puiseux contacts can carry the unconditional negative
completed-Xi cubic residual.  It does not construct the still-missing arithmetic source-to-charge
map or an actual meromorphic connection.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure claim, corpus audit, literature audit, hostile attack
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: exact Lean theorems, targeted check, new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent priority review

## Exact theorem `[PROVED HERE]`

Fix genus `g`, marked points `a : Fin (p+1)`, one Stokes orbit at every point, branch counts
`m_a`, positive common-cover degrees `N_a`, and coefficient-generated local data `d_a`.  Define the
ordered normalized contact budget

`C_a(d) = sum_{i,j : Fin(m_a)} contactNumerator_a(i,j) / N_a`

and the global unit coefficient

`A(g,d) = fusionCoefficient(g,p+1)
          + sum_a (1 + m_a^2 - C_a(d)) / m_a^2`.

Let `r(x)` be the common physical rank and

`R_Xi = normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0^3 / 4 < 0`.

Then:

1. every compatible charge satisfies the exact global contact law
   `W_unit(x) = A(g,d) r(x)^2`;
2. the completed-Xi cubic unit landing fibre is nonempty if and only if `A(g,d)<0`;
3. every landing satisfies the exact magnitude law
   `(-A(g,d)) r(x)^2 = -R_Xi`;
4. for `A(g,d)<0`, a landing is explicitly obtained from
   `r=sqrt((-R_Xi)/(-A(g,d)))` and local orbit charge `u_a=r/m_a`.

Thus `A>0`, `A=0`, and `A<0` are respectively forbidden, radical, and landing chambers for the
entire single-orbit receiver sector.

## Internal frontier

- `[CORPUS]` single-branch Euler collapse proves the specialization `A=2(1-g)` and excludes
  low-genus landing, but does not treat arbitrary branch counts or contact budgets.
- `[CORPUS]` two-branch sphere classification proves the specialization
  `A=(5-2c)/4` and its sharp `c>5/2` wall.
- `[CORPUS]` global Witt decomposition, signature rigidity, ramification capacity, and contact
  bounds give one-sided constraints, not a necessary-and-sufficient landing classification.
- `[CORPUS]` targeted research found no arbitrary-genus, arbitrary-branch single-orbit formula,
  sign phase diagram, or constructive converse.

## External frontier

- `[LITERATURE]` Arinkin's arbitrary-singularity algorithm and Euler--Poincare rigidity index
  provide parent index theory, not a completed-Xi target classification.
- `[LITERATURE]` Hiroe--Yamakawa obtain quiver descriptions and partial irregular
  Deligne--Simpson criteria for at most one unramified irregular singularity on `P1`.
- `[LITERATURE]` Kulkarni--Livesay--Matherne--Nguyen--Sage solve a maximally ramified toral
  Deligne--Simpson problem on `G_m`, a much narrower realization problem.
- `[LITERATURE]` Jakob--Yun classify isoclinic irregular `G`-connection existence in specified
  two-pole settings through Cherednik modules and affine Springer fibres.
- No audited primary source states this coefficient, its completed-Xi sign criterion, or its
  arbitrary-genus constructive landing converse.

The local Euler/contact reduction is a `[BRIDGE]` to standard irregular index theory.  The exact
completed-Xi global phase diagram is `[NOVELTY UNVERIFIED]`.

## Hostile attack

- **Circularity:** only unconditional scalar negativity of `R_Xi` enters.  No Xi-zero location,
  RH-equivalent positivity, or source landing is assumed.
- **Empty branch edge:** impossible.  Surjectivity `Fin(m_a) -> Fin 1` gives a branch over the
  unique orbit, hence `m_a>0` at every marked point.
- **Zero coefficient edge:** if `A=0`, every unit value is zero and cannot equal `R_Xi<0`.
- **Positive coefficient edge:** if `A>0`, every unit value is nonnegative.
- **Negative coefficient sufficiency:** one orbit leaves no local compatibility modulus beyond
  common rank.  Division by positive `m_a` therefore constructs all local charges simultaneously.
- **Hidden contact convention:** `C_a` is the ordered double sum, matching the formal contact
  pairing.  Diagonal terms vanish automatically; symmetric off-diagonal terms occur twice.
- **Parent-theory collapse:** the quadratic index mechanism is known, but known geometric
  existence results impose different formal-type and moduli conditions and do not identify this
  completed-Xi landing chamber.
- **Significance:** theorem exhausts every coefficient-generated single-orbit abstract receiver.
  It sharpens Route P's `LAND` target but does not solve the arithmetic source handoff.

**Preliminary verdict:** `SURVIVES PRELIMINARY ATTACK`; novelty remains unverified.

## Dependency-closed proof `[PAPER-PROVED]`

At point `a`, write `u_a` for the unique orbit charge.  Every branch maps to that orbit.  Therefore
terminal energy is `u_a^2`, physical rank is `m_a u_a`, and every lifted branch charge is `u_a`.
By the ordered definition of `C_a`, contact pairing is `C_a u_a^2`.  Hence

`localWitt_a(u_a) = (1 + m_a^2 - C_a) u_a^2`.                         `(1)`

Orbit surjectivity supplies a branch, so `m_a>0`.  Compatibility identifies all local physical
ranks with `r(x)`; thus `u_a=r(x)/m_a`.  Substitution in `(1)`, followed by the fusion term, gives

`W_unit(x)
 = fusionCoefficient(g,p+1) r(x)^2
   + sum_a ((1+m_a^2-C_a)/m_a^2) r(x)^2
 = A(g,d) r(x)^2`.                                                    `(2)`

Suppose `x` lands.  Equation `(2)` equals `R_Xi<0`.  Its right side cannot be negative when
`A>=0`, because `r(x)^2>=0`; hence `A<0`.  Rearrangement yields

`(-A) r(x)^2 = -R_Xi`.                                                `(3)`

Conversely assume `A<0`.  Since `R_Xi<0`, the quotient `(-R_Xi)/(-A)` is positive.  Set

`r = sqrt((-R_Xi)/(-A))`,  `u_a = r/m_a`.

Each `m_a>0`, so local physical rank is `m_a u_a=r`; the resulting global charge is compatible.
Its common rank is `r`, and the square-root identity gives `r^2=(-R_Xi)/(-A)`.  Equation `(2)`
then gives `W_unit=R_Xi`, constructing a landing.  This proves both directions, all boundary
cases, and the exact magnitude law.  No paper-proof dependency remains beyond already formalized
definitions and cubic negativity.

## Lean formalization `[LEAN-PROVED]`

File:
`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicSingleOrbitContactBudgetClassification.lean`

- `routePPrimitiveGammaJuliaStokesSingleOrbitContactBudget` defines the ordered normalized local
  contact mass directly from coefficient-generated Puiseux data.
- `routePPrimitiveGammaJuliaStokesSingleOrbitUnitCoefficient` defines exact arbitrary-genus global
  phase coefficient `A(g,d)`.
- `routePPrimitiveGammaJuliaStokesSingleOrbitUnitWittForm_contactBudgetLaw` proves
  `W_unit=A(g,d)r^2` for every compatible charge.
- `routePPrimitiveGammaJuliaStokesCubicSingleOrbitUnitLanding_chargeMagnitude` proves exact rank
  magnitude for every landing.
- `nonempty_routePPrimitiveGammaJuliaStokesCubicSingleOrbitUnitLandingFiber_iff_coefficient_neg`
  proves complete iff, including simultaneous square-root construction over every marked point.

Direct targeted module elaboration passed.  A `/tmp` `#print axioms` audit of exactly these five
new declarations returned `[propext, Classical.choice, Quot.sound]` for each.  Area umbrella import
was added without building the umbrella.  No repository-wide lint or full build was run.

## No-go closure / positive survivor

- **Absorbed special cases:** single-branch Euler collapse and two-branch `5/2` contact wall.
- **New invariant:** `A(g,d)` is the exact global contact budget per common-rank square.
- **Positive survivor:** explicit landing in every negative chamber, not merely a necessary bound.
- **Open core left:** realization of this charge by source-fixed irregular RH data and arithmetic
  transfer into the completed-Xi target.

## Log

- 2026-08-25 -- arbitrary-genus single-orbit phase diagram isolated after two-branch threshold;
  internal and primary-literature audits completed; hostile boundary audit and dependency-closed
  proof passed; promoted to Stage 2; exact law, magnitude theorem, and constructive iff formalized;
  targeted elaboration and five-declaration axiom audit passed; promoted to Stage 3.
