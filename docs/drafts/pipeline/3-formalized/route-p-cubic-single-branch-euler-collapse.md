# Route P cubic single-branch Euler collapse

- **ID:** `CUBIC-SINGLE-BRANCH-EULER-COLLAPSE`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** completed-Xi cubic irregular-microlocal Riemann--Hilbert route
- **Statement:** Unit Rees fusion of one Puiseux branch and one Stokes orbit at every marked point is exactly `2(1-g)r^2`; hence genus-zero and genus-one completed-Xi cubic unit landing fibres are empty.

## Goal

Use full coefficient-generated Stokes geometry to classify an actual completed-Xi landing type.
The target is not another abstract coarea foundation: it must remove a live class of candidate
source incidences without assuming the missing arithmetic source-to-charge map.

## Gates

- [x] 0 -> 1 in-progress: exact claim, source-pure attack, Door passport, literature normalization
- [x] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [x] 2 -> 3 formalized: exact Lean theorem, targeted check, new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent priority review

## Exact conjecture

Let `q=p+1` be the nonempty marked-point count on a genus-`g` curve.  At each marked point take
coefficient-generated local Puiseux data with exactly one branch and exactly one Stokes orbit, but
arbitrary positive cover degree and arbitrary exponent ceiling.  For every compatible charge `x`,
at unit Rees scale,

`globalReesWittForm(g,d,1)(x) = 2(1-g) * commonRank(x)^2`.

Consequently:

- for `g=0`, every nonzero charge has strictly positive unit form;
- for `g=1`, every charge has zero unit form;
- the negative completed-Xi cubic Malgrange residual can be reached in neither genus.

Thus no genus-zero or genus-one unit landing exists in the single-branch/single-orbit sector,
regardless of Puiseux slopes, cover degrees, exponent ceilings, or number of marked points.

## Dependency-closed proof `[PAPER-PROVED]`

Fix one marked point.  There is one orbit coordinate `x_0` and one branch.  The unique orbit map
sends the unique branch to the unique orbit.

1. Local terminal energy is `x_0^2`.
2. Local physical rank is the sum of lifted branch charges, hence is `x_0`.
3. Local contact pairing has one summand.  Its contact is zero: canonical coefficient cuts recover
   normalized highest-difference order, and a branch has highest-difference numerator zero with
   itself.  Therefore local contact pairing is zero.
4. The coefficient-generated Cartan identity gives
   `localWitt(x) = terminal(x) + rank(x)^2 - contact(x) = 2 rank(x)^2`.
5. Unit Rees specialization is the undeformed global Witt form.  Compatibility identifies every
   local rank with the common rank `r`, so the sum of the `q` local forms is `2q r^2`.
6. Global fusion contributes `2(1-g-q)r^2`.  Hence
   `globalReesWitt(g,d,1)(x) = [2q + 2(1-g-q)]r^2 = 2(1-g)r^2`.
7. A completed-Xi cubic landing has negative Witt value and nonzero common rank.  At `g=0`, the
   formula gives `2r^2>0`; at `g=1`, it gives `0`.  Both contradict negativity.

Every step uses existing coefficient-generated contact realization, the global fusion law, or
finite one-coordinate identities.  No landing existence, source transport, RH statement, or
unproved analytic input is used.

## Lean formalization

File: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicSingleBranchEulerCollapse.lean`

- `routePPrimitiveGammaJuliaStokesSingleOrbitBranchUnitReesWittForm_eulerCollapse` formalizes
  `W_unit = 2(1-g)r^2` for arbitrary compatible charges and arbitrary local covers/ceilings.
- `not_nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_singleOrbitBranch`
  excludes genus-zero completed-Xi cubic unit landing fibres.
- `not_nonempty_routePPrimitiveGammaJuliaStokesCubicTorusUnitLandingFiber_singleOrbitBranch`
  excludes genus-one completed-Xi cubic unit landing fibres.

Targeted module elaboration passed.  A `/tmp` `#print axioms` audit of exactly these three public
declarations returned `[propext, Classical.choice, Quot.sound]` for each.  No umbrella build or
repository-wide lint was run; temporary scratch and generated `.olean` files were removed.

## Hostile audit and relentless interrogation

### Killed conjecture 1: charge-free inverse-complexity gap

The first candidate was

`fusion + sum_a 1/(N_a m_a) < sum_a rootDefect_a`

for every unit completed-Xi cubic landing.  It is correct but is an immediate corollary of the
already formalized cumulative rank--coarea quantum and existing rank-debt inequality.

- **Verdict:** `BRIDGE` / scientifically too routine as the active result.
- **Exact why:** it discards almost all threshold geometry and only cancels a common nonzero rank
  square between two existing inequalities.
- **Stronger conjecture forced by the failure:** retain every threshold class when branch count is
  one.  The entire slope dependence cancels, producing an exact topology-only law rather than a
  slightly sharper inequality.

### Attack on stronger conjecture

- It is not circular: completed-Xi source incidence is never assumed.
- It is not vacuous: the exact form law holds for every compatible charge before imposing a
  landing equation.
- It is not a disguised fixed-charge two-scale statement: only unit specialization occurs.
- It is consistent with parent theory.  For a rank-one irregular connection, the endomorphism
  connection loses irregularity, and Euler/rigidity indices become topological.  This makes the
  local cancellation a `REDISCOVERED` parent mechanism, not a novelty claim.
- The completed-Xi consequence is application-specific: a prescribed negative cubic Malgrange
  value cannot live in the low-genus single-branch sector.  Corpus audit found no such
  classification.

**Verdict:** exact Euler collapse is `[BRIDGE]`; completed-Xi low-genus landing exclusion
`SURVIVES PRELIMINARY ATTACK` and is `[NOVELTY UNVERIFIED]`.

## Literature audit

- `[LITERATURE]` Arinkin, *Rigid irregular connections on P1* (Compositio Math. 2010,
  arXiv:0808.0742), gives the irregular Euler--Poincare formula and rigidity index; rank-one
  endomorphism irregularity disappears.
- `[LITERATURE]` Boalch, *Geometry and braiding of Stokes data; Fission and wild character
  varieties* (Annals of Math. 2014), constructs wild character varieties and their Stokes/fission
  geometry.
- `[LITERATURE]` Hiroe--Yamakawa, *Moduli spaces of meromorphic connections and quiver varieties*
  (2014, arXiv:1305.4092), translates irregular connection moduli and existence questions into
  quiver varieties.
- `[LITERATURE]` Kulkarni--Livesay--Matherne--Nguyen--Sage, *The Deligne--Simpson problem for
  connections on Gm with a maximally ramified singularity* (Adv. Math. 2022,
  arXiv:2108.11029), classifies an important ramified existence problem.
- `[LITERATURE]` Jakob--Yun, *A Deligne--Simpson problem for irregular G-connections over P1*
  (arXiv:2301.10967, v3 2026), gives current algebraic/geometric existence criteria and rigid-case
  classifications for isoclinic irregular types.

These parent theories explain rank-one Euler cancellation and classify specified irregular
connection problems.  Audit found no completed-Xi cubic Malgrange target or its low-genus
single-branch exclusion.  Absence is an audit inference, not a universal priority claim.

## No-go closure

- **Exact killing theorem/mechanism:** inverse-complexity gap was only an algebraic corollary of two
  existing inequalities.
- **Strongest positive survivor:** exact single-branch unit Euler law
  `W_unit=2(1-g)r^2`, plus empty genus-zero/genus-one completed-Xi cubic unit landing fibres.
- **New insight:** viable low-genus completed-Xi irregular incidence cannot be rank-one at every
  marked point; slope growth and deeper single-branch Stokes levels never repair the obstruction
  because they cancel from the unit global index.
- **Status:** dependency-closed paper proof and exact Lean formalization complete.

## Log

- 2026-08-25 -- inverse-complexity gap conjectured, then downgraded as a routine bridge.
- 2026-08-25 -- stronger exact single-branch Euler collapse found by retaining full threshold data.
- 2026-08-25 -- parent-theory and corpus attacks completed; paper proof closed.
- 2026-08-25 -- promoted to Stage 2 after dependency and circularity audit.
- 2026-08-25 -- exact Euler law and genus-zero/genus-one landing exclusions formalized; targeted
  elaboration and new-declaration axiom audit passed; promoted to Stage 3.
