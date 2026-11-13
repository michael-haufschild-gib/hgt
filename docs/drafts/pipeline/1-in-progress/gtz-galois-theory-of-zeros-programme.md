# Galois theory of the zeros — programme card (review-1211 §2.19)

- **ID:** gtz-programme
- **Stage:** 1-in-progress
- **Type:** programme
- **Source:** `docs/reports/review-1211/obstacles-summary.md` §2.19
- **Lean:** `formal/GaloisForLFunctions/GaloisTheoryOfZeros/` (umbrella `GaloisTheoryOfZeros.lean`)
- **README:** `formal/GaloisForLFunctions/GaloisTheoryOfZeros/README.md`

## Questions and status

| # | Question | Status |
|---|---|---|
| Q1 | orbit of a zero with irrational real part over `B`; an automorphism besides conjugation | open; orbit lies in the quartet; rational real part settled; over `D` reduced to sums of squares (module O1) |
| Q2 | `[L:K] ∈ {1,∞}` | open; contains B13 |
| Q3 | square-class relations among the radicands `−δ_q²` | open; ordering conjugations see the relations modulo sums of squares (module O1) |
| Q4 | group of one Jensen polynomial over its coefficient field | reduced (modules G1–G4): the group is `C₂ ≀ S_n` or `μ₂/μ₀, …, μ₂ₙ/μ₀` are algebraically dependent over `ℚ`; the independence is a transcendence statement outside the programme |
| Q5 | monodromy of the heat family at a collision, group generated, relation to conjugation | local part answered; branch points exist; global group open (below) |
| Q6 | a restriction from the prime traces forcing `H = B` | open; equivalent to RH |

## Tier 3: the heat cover (Q5)

`H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx`, complex `τ`. Cover `X = {H_τ(z) = 0} ⊂ ℂ²`.

| Module | Content | Card |
|---|---|---|
| `TheHeatCoverOfTheZeros` | analyticity, symmetries, blow-up `H_{τ₀+s²}(z₀+sy) = s^m G(s,y)`, `G(0,·) = (a/m!)Q_m` | `3-formalized/galois-zero-heat-cover-hermite-monodromy.md` |
| `TheHermiteMonodromyOfACollision` | sheets `Z_ρ`, monodromy `Z_ρ(−s) = Z_{−ρ}(s)`, laws for `c` and `r`, real and central collisions | same |
| `TheSheetsOfACollisionAreAllItsZeros` | exhaustion, simple zeros off the branch time, branch points isolated, branch times countable | same |
| `TheFunctionalEquationIsAMonodromyOfTheHeatCover` | centre value of order `≤ 3/2`, superexponential on the real axis, infinitely many nonreal centre times, `r` as local monodromy | `3-formalized/galois-zero-central-collisions-functional-equation-monodromy.md` |
| `TheCentreValueIsTheEquationOfTheSignBranchPoints` | heat equation in complex time; order `2k` at the centre ⇔ order `k` of `c`; Taylor coefficients of `c` in `K_J`; singular points = order `≥ 3`; folds; RH ⇔ no positive real branch time | `3-formalized/galois-zero-centre-value-sign-branch-points.md` |
| `TheTraceOfAFibreOfTheHeatCover` | `H_τ(z) = Σ (−1)^k c^{(k)}(τ) z^{2k}/(2k)!`; order one in `z` for every `τ`; `Σ 1/z² = c'/c`; residue at a centre time = number of colliding pairs | `3-formalized/galois-zero-fibre-trace-heat-cover.md` |
| `AZeroContinuesAlongAPathOfTimesUntilItEscapes` | chart of a simple zero; uniqueness of lifts; transport injective; a zero lifts along the whole path or escapes at a finite parameter | `3-formalized/galois-zero-continuation-until-escape.md` |
| `RealBranchTimesAccumulateAtTheTimeOfXiUnlessZerosEscape` | conjugate lifts; nonreal zeros stay nonreal without a collision; no branch time in `[a, b]`, `a < 0 < b` ⇒ infinitely many nonreal zeros escape; `0 ∈ closure` of the real branch times or escape; RH form | `3-formalized/galois-zero-real-branch-times-accumulate-at-time-zero.md` |
| `TheSignBranchPointsLieInTheForwardHalfPlane` | `Im c(τ)` has the sign of `Im τ` for `Re τ ≤ 0`; `c` maps the backward half-plane into the slit plane; every centre time has `Re τ > 0`; `√c` single-valued over backward times | `3-formalized/galois-zero-sign-branch-points-forward-half-plane.md` |

Open core of Q5 (the group generated):

1. *Non-escape.* By the continuation alternative, lifting along a path fails only if the
   modulus of the lift tends to infinity. Needed: no zero escapes over a compact set of
   times. Heuristic (two saddles of the Gaussian average of ξ): for `Re τ > 0` the far zeros
   lie near `Im z = −(π/2) Im τ · sgn(Re z)`, are simple, and drift with velocity
   `dz/dτ → −π/2 · sgn(Re z)`; a proof needs the two-term asymptotics with derivative
   control, uniformly on compact sets of forward times. For `Re τ ≤ 0` there is no gain from
   the Gaussian and the statement is of the strength of zero-spacing results for ζ.
2. *Collisions away from the centre.* A real collision at a positive time exists iff RH
   fails. Real branch times exist in every neighbourhood of the time `0`, or zeros escape
   there. None is known at a nonreal time. Not shown: that the real branch time is a collision
   at a real place (needs continuation through collisions at nonreal places).
3. *Irreducibility* of the cover (transitivity of the monodromy on the zeros of one time).
4. *Accumulation* of branch times at finite times; simplicity of the zeros of `c`.

## Tier 1: finite equations (Q4)

| Module | Content |
|---|---|
| G1 `TheGenericFoldedEquationHasTheFullSignedPermutationGroup` | `Gal(∏(X² − x_i²) / K(x)^{W_n}) ≅ C₂ ≀ S_n`, order `2ⁿ n!`; the reflection is the central uniform flip (card `3-formalized/galois-zero-generic-folded-signed-permutation-group.md`) |
| G2 `TheFoldedCoefficientsGenerateTheFixedFieldOfTheSignedPermutations` | `K(x)^{W_n} = K(γ)`, `γ_k` the coefficients of `∏(Y − x_i²)`; `Gal(K(x)/K(γ)) ≅ W_n`; degree `2ⁿ n!` |
| G3 `AFoldedEquationWithIndependentCoefficientsHasTheFullSignedPermutationGroup` | `γ` algebraically independent; `c` algebraically independent ⇒ `Gal(X^{2n} + Σ c_k X^{2k} / K(c)) ≅ W_n` |
| G4 `TheJensenEquationsHaveTheFullGroupUnlessTheMomentsAreDependent` | Jensen equation of degree `2n` = folded equation of the coefficients of `E_n`; coefficients independent ⇔ `μ₂/μ₀, …, μ₂ₙ/μ₀` independent; group full or a relation over `ℚ` |

Card for G2–G4: `3-formalized/galois-zero-folded-specialization-jensen-equations.md`.

Not done for Q4: the class of complex conjugation inside the group of a Jensen equation as a
signed permutation (needs the restriction of conjugation to a splitting field inside `ℂ`).

## Tier 2: orderings (Q1, Q3)

| Module | Content | Card |
|---|---|---|
| O1 `TheOrderingsOfTheSquaredWidthFieldAndTheirConjugations` | Artin–Schreier extension theorem; `σ_Q ∈ Gal(L/D)` for every ordering `Q` of `D`; real ordering ↦ complex conjugation; all `σ_Q = c` ⇔ all `δ_q²` sums of squares; all `σ_Q ∈ {1, c}` ⇔ all `a_q a_r` sums of squares | `3-formalized/galois-zero-orderings-squared-width-field-conjugations.md` |

Not done: orderings of `K` and `B` (needs real closures; the conjugation is then a conjugacy
class); the fixed field of `σ_Q` is formally real (needs extension of orderings to quadratic
extensions).

## Conjecture log

- *Real times suffice for the monodromy.* False as a setting: a loop around a collision time
  leaves the real axis. Pivot: complex time; all modules generalized.
- *Infinitely many real collisions at negative times follow from the infinitely many nonreal
  zeros at negative times.* A nonreal zero may come from infinity as `t ↑ 0`, so compactness
  gives no collision. Proved as a dichotomy: a branch time in `[a, b]` or infinitely many
  escaping zeros (injective transport into the finite nonreal census at `b > 0`).
- *A folded cover without branch points and without escape is a cosine (Picard).* Correct on
  paper (squared zeros entire and never equal ⇒ one similarity ⇒ a second-order equation with
  affine coefficients ⇒ static zeros), but for ξ the real-time dichotomy is stronger and needs
  no Picard. Not formalized.
- *Power sums of the reciprocal centre times lie in `K_J`.* True formally
  (`Σ τ_j^{−2} = (μ₂/μ₀)² − μ₄/μ₀`), but needs a genus-one Hadamard product for the growth
  `exp(C|τ| log²|τ|)`; the corpus product theorem covers `exp(C|τ| log|τ|)` only. Not done.
- *No centre time has `Re τ ≤ 0`.* Proved: `Φ` decreases on `[0, ∞)`
  (`strictAntiOn_riemannKernelReal_Ici`), so `Φ(√u)e^{ru}/√u` decreases for `r ≤ 0`, and the
  sine transform of a decreasing function is positive.
- *Irreducibility through three-point rigidity.* If the folded cover were unramified and
  lifting held, the squared zeros would be entire functions of `τ` never equal, and by
  Picard's theorem they would move by one similarity. Needs lifting and Picard; neither is
  available.

- *Barriers.* Circles or vertical lines free of zeros for all times of a compact set cannot
  exist when the set has interior: each far zero sweeps a region of diameter about
  `(π/2)·diam`, larger than the spacing. Non-escape needs the local asymptotics.

## Log
- 2026-11-12 — card created; README restructured to the §2.19 frame; Q5 paper proof written.
- 2026-11-13 — heat cover in complex time: six modules; generic folded group, fundamental
  theorem, specialization, Jensen equations; orderings of `D`; README updated.
