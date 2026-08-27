# Parikh--Wilczek reflection-orbit aggregate no-go

- **ID:** PW-B-ROA
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + NO-GO + POSITIVE SURVIVOR
- **Parent:** PW-B
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION] [NO-GO]` Equal-weight linear aggregation of gauge-invariant Parikh--Wilczek recoil phase over complete reflection orbit vanishes identically, including off wall. Arbitrary fixed weights vanish iff weights are equal or point lies on critical wall. Quadratic orbit energy is faithful and universal vanishing at one Borel grade is exactly RH.

## Goal

Test PW-B proposed replacement of copywise balance by genuinely global aggregate. Determine whether
reflection-complete finite-mass source aggregation can force flatness without fitting individual Xi
copies.

## Gates

- [x] 0 → 1 in-progress: reflection-orbit aggregation conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: linear classification and quadratic survivor proved
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claims

Let `H_k(s)` be exact closed Parikh--Wilczek recoil holonomy and
`J(s)=1-conj(s)` critical-line reflection. Then

`H_k(J(s)) = conj(H_k(s))`,

so its physical phase `D_k(s)=Im H_k(s)` obeys `D_k(J(s))=-D_k(s)`. Therefore

`a D_k(s)+b D_k(J(s)) = (a-b)D_k(s)`.

Inside open critical strip at nonreal `s`, this aggregate is zero iff `a=b` or `Re s=1/2`.
Equal-weight reflection-complete aggregation is thus identically blind. Quadratic energy

`Q_k(s)=D_k(s)^2+D_k(J(s))^2=2D_k(s)^2`

is nonnegative and zero iff `Re s=1/2`. Universal `Q_k=0` on actual Xi divisor support, for any
single fixed grade `k`, is exactly RH.

## Complete paper proof

Conjugation commutes with polynomial recoil edges. Substituting `J(s)=1-conj(s)` swaps two edge
factors and conjugates both, giving conjugate holonomy and odd phase. Linear formula follows by
substitution. Zero-product classification combines it with existing strict-strip holonomy theorem
`D_k(s)=0 iff Re s=1/2`. Squaring removes orientation but not magnitude, giving exact energy law.
Xi divisor support is nonreal and lies in open strip; existing support endpoint converts universal
energy zero to RH and RH gives converse.

## Hostile review and novelty verdict

- Result does not prove quadratic source energy vanishes.
- Linear signed aggregate appearing naturally from reflection-complete source is zero for purely
  representation-theoretic reason and contains no RH information.
- Unequal weights restore faithfulness but insert orientation; their vanishing is already wall
  condition.
- Quadratic energy is minimal reflection-invariant faithful survivor but remains zero-indexed at
  receiver endpoint. Needed producer must identify this energy with source-first nonnegative
  quantity and force zero, or derive an oriented unequal-weight transport physically.
- Corpus had general reflection-odd trace cancellation and other Xi defect energies, but no exact
  Parikh--Wilczek Borel recoil orbit classification. Primary arXiv audit found tunnelling,
  evaporation, and current quantum-correction work but no such aggregate theorem.

Verdict: reflection algebra `[REDISCOVERED]`; PW-B physical recoil-orbit classification and exact
quadratic survivor `[NEW] [CLASSIFICATION]`, external priority provisional.

## No-go closure

- **Exact killing mechanism:** functional-equation reflection conjugates holonomy, so equal source
  weights cancel phase on each orbit independently of divisor location.
- **Strongest positive survivor:** quadratic orbit energy `2(Im H_k)^2`, faithful at every Borel
  grade and insensitive to multiplicity/coefficient normalization.
- **New insight:** global aggregation alone is insufficient. Linear reflection-complete laws are
  blind; any viable PW-B global producer must be nonlinear positive energy or source-derived
  orientation that breaks equal orbit weights before divisor specialization.
- **Status:** dependency-closed paper proof and Lean formalization complete. Remaining PW-B open
  core is source-first annihilation/control of quadratic recoil energy or physical unequal-weight
  orientation beyond self-similar finite-mass evaporation.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekReflectionOrbitAggregateNoGo.lean`
- Reflection law: `schwarzschildParikhWilczekBorelRecoilHolonomy_lineReflection`
- Linear classification:
  `schwarzschildParikhWilczekBorelLinearOrbitAggregate_eq_zero_iff`
- Quadratic survivor:
  `schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_eq_zero_iff`
- Global exact endpoint:
  `riemannHypothesis_iff_schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_zero`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekReflectionOrbitAggregateNoGo`
  passed (`11423/11423`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from PW-B holonomy and corpus reflection-odd trace/energy split.
- 2026-08-27 — linear aggregate no-go, quadratic survivor, RH endpoint, and Lean proof completed.
