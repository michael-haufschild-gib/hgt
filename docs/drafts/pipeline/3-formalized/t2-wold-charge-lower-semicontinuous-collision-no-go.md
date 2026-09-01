# T2 Wold-charge lower-semicontinuous collision no-go

- **ID:** t2-wold-charge-lsc-collision-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · T2 scalar-descent survivor
- **Statement:** No compact-open sequentially lower-semicontinuous scalar reporter is exact on reflected Wold orbit-charge energy across the canonical two-simple-to-double symmetric-shift collision.

## Goal

Kill T2's lower-semicontinuous coefficient-faithful scalar survivor. Together with the formalized
upper-semicontinuous escape no-go, this excludes every one-sided semicontinuous scalar descent and
forces source marking, a non-scalar carrier, or a genuinely singular relative selector.

## Gates

- [x] 0 → 1  in-progress: exact corpus energy and collision laws; explicit attack
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted build, axioms audit
- [ ] 3 → 4  publication-ready

## Corpus basis

- `principalPartOrbitChargeEnergy_two_single`: two off-wall orbit atoms of multiplicity `m` have energy `2m²`.
- `analyticOrderAt_symmetricShiftProduct_zero_shift`: collision doubles analytic multiplicity.
- `analyticOrderAt_symmetricShiftProduct_pair_eq_of_no_overlap`: separated translates retain multiplicity.
- `continuousAt_divisorPairing`: compactly supported linear-multiplicity divisor pairing is continuous.

## Conjecture and attack

Take `ρ = 3/4` and positive real shifts `aₙ = 1/(8(n+1))`. Let
`Fₙ(z)=((z+aₙ)-ρ)((z-aₙ)-ρ)` and `F∞(z)=(z-ρ)²`. Then `Fₙ→F∞` compact-open,
each `Fₙ` has two distinct simple off-wall roots `ρ±aₙ`, and `F∞` has one double off-wall root
`ρ`. Exact Wold energies are respectively `4` and `8`. Lower semicontinuity would give
`8 ≤ 4+ε`; choose `ε=1`.

## Paper proof

**[PROVED HERE]** Put `aₙ=1/(8(n+1))`. Then `0<aₙ≤1/8` and `aₙ→0`. Expanding gives
`Fₙ(z)=F∞(z)-aₙ²`, hence uniform convergence on all of `ℂ`, in particular compact-open
convergence. The roots `ρ-aₙ` and `ρ+aₙ` are distinct, lie in the open strip, have real part
strictly above `1/2`, and each has analytic multiplicity one. At `a=0` they collide at `ρ`, with
analytic multiplicity two.

The corpus energy law gives energy `2·1²=2` at each separated root, hence total `4`, while the
double root has energy `2·2²=8`. If `Q` is exact on these sources and compact-open sequentially
lower semicontinuous, applying lower semicontinuity with `ε=1` gives eventually
`8=Q(F∞)≤Q(Fₙ)+1=5`, impossible. Thus no such `Q` exists.

For the positive survivor, let `w : ℕ → ℝ` obey `w(0)=0` and
`w(m+n)=w(m)+w(n)`. Induction gives `w(m)=m·w(1)` for every `m`; conversely every such linear
weight is collision-additive. Therefore linear multiplicity is exactly the scalar collision law,
whereas Wold's quadratic weight has exact collision defect `8-4=4`.

## Hostile audit

- Semicontinuity direction checked: lower semicontinuity demands limit value at most `liminf`.
- No wall crossing: every separated root has real part in `[5/8,7/8]`.
- No hidden analytic premise: sources are explicit entire quadratics and convergence error is constant.
- Exact root multiplicities follow from the corpus symmetric-shift collision laws.
- No RH, Xi-zero existence, simplicity, enumeration, or numerical certificate is assumed.
- Literature audit through 2026-08 found general linear divisor/Lelong semicontinuity, but no exact reflected-Wold `2m²` collision theorem or T2 classification.

## No-go closure

- **Exact killing theorem/mechanism:** quadratic multiplicity energy increases under collision, contradicting compact-open lower semicontinuity.
- **Strongest positive survivor:** collision-additive scalar multiplicity weights are exactly linear weights; linear divisor mass survives this collision.
- **New insight:** scalar T2 cannot retain Wold's quadratic multiplicity energy in either semicontinuous direction; collision-compatible descent must linearize multiplicity before any noncompact completion.
- **Status:** formalized as `no_compactOpenSequentialLowerReporter_exactOn_woldOrbitChargeCollision` and `collisionAdditiveMultiplicityWeight_iff_linear` in `XiHeatCassiniWoldOrbitChargeLowerSemicontinuousCollisionNoGo.lean`; direct Lean and targeted module build pass; standard axioms only.

## Log

- 2026-09-01 — created in 1-in-progress after corpus-derived conjecture freeze.
- 2026-09-01 — `[PROVED HERE]`; promoted to 2-fully-proven.
- 2026-09-01 — formalized, targeted build green, axioms audited; promoted to 3-formalized.
