# Card `even-index-hermitian-additive-pole-law` — CLOSED, promoted to stage 3 (2026-08-08)

Card now at `docs/drafts/pipeline/3-formalized/even-index-hermitian-additive-pole-law.md`, with a
`Stage-3 Lean certificate` table naming every declaration.  Every mathematical statement of the card
is an unconditional Lean 4 theorem; all report exactly `[propext, Classical.choice, Quot.sound]`.
`lake build GaloisForLFunctions.RHTower` and `... .HTGeometry` both green.

## Nine new modules

`HTGeometry/DyadicExponentGeometricSummable`, `HTGeometry/BoundedCoefficientLaplaceMellin`,
`RHTower/EvenIndexHermitianDyadicOrbit`, `RHTower/EvenIndexHermitianOrderLowerEdge`,
`RHTower/LiouvilleDirichletSeries`, `RHTower/LiouvilleDyadicGramLaw`,
`RHTower/LiouvilleEvenIndexPositiveRecurrence`, `RHTower/RiemannXiZerosInfinite`,
`RHTower/MobiusEvenIndexPositiveRecurrence`, `RHTower/PowerSievedLiouvilleDirichlet`,
`RHTower/PowerSievedLiouvilleRecurrence`.

## Results worth reusing far beyond this card

* **`RHTower.exists_riemannZeta_zero_mem_openStrip`** — `∃ ρ, 0 < ρ.re ∧ ρ.re < 1 ∧ ζ ρ = 0`,
  unconditional.  Built from the entire `riemannXi s = (s(s-1)Λ₀ s + 1)/2` (mathlib's
  `completedRiemannZeta₀ = completedHurwitzZetaEven₀ 0` *definitionally*, so the corpus Hurwitz
  order-one envelope applies verbatim), the corpus ray-growth lemma `exists_Gammaℝ_ray_growth`, and
  `zeroSet_infinite_of_subquadratic_superlinear_ray`.  mathlib has no such statement.
* **`HTGeometry.coeffLaplaceProfile`** — generic `∑ f n e^{-nx}` for `‖f n‖ ≤ 1`, `f 0 = 0`, with
  continuity, local integrability, `O(e^{-x})`, radial form, and `mellin = Γ · L f` on `Re s > 1`.
  Generalises what `TwistedMobiusMellin` carried only for `χ·μ`.
* `isSquare_iff_factorization_even`, `isPow_iff_factorization_dvd` — mathlib has neither.

## The mechanism (reuse this, not `frequently_re_pos_of_dirichletPole`)

`mellin f = Γ·D` **cannot** be assumed near a point left of the abscissa: mathlib's `mellin`
returns `0` when the integral diverges, so that hypothesis is undischargeable for concrete
arithmetic sequences.  Instead:

1. assume `f =O[𝓝[>]0] x^{-b}`, `0 ≤ b`;
2. `mellin_differentiableAt_of_isBigO_rpow_exp` ⟹ `mellin f` analytic on `{Re s > b}`;
3. `G := mellin f / Γ` analytic there;
4. clear **every** zeta pole with the corpus entire `zetaEntire s = (s-1) ζ s`, so both sides of the
   Dirichlet identity are analytic on the *whole* half-plane — no punctured domain, connectedness
   only needs `convex_decayHalfPlane`;
5. `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` from a neighbourhood of `s = 2`;
6. evaluate at the singular point.

Sieved family: `(ms-1)·G·zetaEntire s = (s-1)·zetaEntire (m s)` dies at `s = 1/m` against
`zetaEntire 1 = 1` — **no `ζ(1/m) ≠ 0` and no zeta-zero input**.
Möbius: `G·zetaEntire s = s - 1` dies at any zeta zero.

## Pre-existing lint debt (not from this card)

`scripts/formal_tools.py lint` reports ~15 `owned module unreachable from theorem-area umbrella`
errors for modules committed in `dd5c72e47` (Deninger/Gibbs/Suzuki/RouteE/Mobius leaves).  All of
this card's modules are wired.  A concurrent agent is committing to this repo — do not rewrite the
umbrella files wholesale.
