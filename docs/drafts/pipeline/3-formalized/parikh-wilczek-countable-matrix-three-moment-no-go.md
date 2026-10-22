# PW-I3 — countable Parikh–Wilczek matrix three-moment no-go

Status: **PAPER-PROVED / LEAN-PROVED**  
Route: PW-B  
Gates closed: absolutely summable linear part of `COMP`; countable linear receiver/dark classification  
Frontier-map policy: `rh-current-frontier-map.md` remained read-only.

## New result

For an arbitrary signed kernel `M : ℕ → ℕ → ℝ`, sum on the product index `ℕ × ℕ`. Assume unconditional summability of exactly the three coefficient families

\[
M_{ij},\qquad M_{ij}(d_i+d_j),\qquad M_{ij}d_i d_j,
\quad d_k=4k(k+1).
\]

Then every countable PW residual energy is summable and equals

\[
m_0x(s)^2+m_1x(s)+m_2.
\]

The full recoil energy is the PW wall square times this quadratic. It is identically zero exactly when all three moments vanish. The existing four-chamber half-line quadratic classifier therefore gives the complete receiver cone for countable moment-admissible kernels, and universal vanishing inside that cone is exactly RH.

Hence absolutely summable infinite/cofinal linear grade completion retains no fourth PW invariant. This closes that branch of PW-B's stated infinite/cofinal escape.

## Sharp infinite dark sector

Define

\[
w_n=2^{-n}+2\mathbf 1_{n=0}-4\mathbf 1_{n=1}.
\]

Lean proves

\[
\sum_n w_n=0,
\qquad
\sum_n 4n(n+1)w_n=0.
\]

The outer-product kernel `Mᵢⱼ = wᵢwⱼ` is:

- moment-admissible;
- symmetric;
- positive semidefinite on every finite principal section;
- nonzero on every diagonal grade `n ≥ 2`, hence genuinely infinite-support;
- zero in all three countable moments;
- identically zero in full PW recoil energy.

Thus neither infinite support nor positive semidefiniteness prevents a countable linear PW dark sector.

## Formal artifact

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekCountableMatrixThreeMomentNoGo.lean`

Principal declarations:

- `schwarzschildParikhWilczekCountableMatrixResidualEnergy_three_moment`
- `schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_three_moment`
- `schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_eq_zero_forall_iff_moments`
- `schwarzschildParikhWilczekCountableSignedMatrixReceiverCone_iff`
- `riemannHypothesis_iff_schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_zero`
- `schwarzschildParikhWilczekInfiniteGradeDarkWeight_hasSum`
- `schwarzschildParikhWilczekInfiniteGradeDarkWeight_shift_hasSum`
- `schwarzschildParikhWilczekInfiniteGradeDarkMatrix_admissible`
- `schwarzschildParikhWilczekInfiniteGradeDarkMatrix_moments`
- `schwarzschildParikhWilczekInfiniteGradeDarkMatrix_infinite_diagonal_support`
- `schwarzschildParikhWilczekInfiniteGradeDarkMatrix_finiteQuadraticForm_nonneg`
- `schwarzschildParikhWilczekInfiniteGradeDarkMatrix_energy_zero`

Wired into `formal/GaloisForLFunctions/RHTower.lean`.

## Verification

- Direct check: `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekCountableMatrixThreeMomentNoGo.lean` — pass.
- Targeted build: `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekCountableMatrixThreeMomentNoGo` — pass.
- Axiom audit: principal results use only `propext`, `Classical.choice`, and `Quot.sound`; no project axioms.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in the module.

## Novelty audit (2026-08-27)

Corpus search found the finite PW three-moment theorem, scalar-history collapse, general double-series infrastructure, and a reusable exact geometric second moment, but no countable PW matrix classification or genuine infinite-support PSD dark kernel. Primary-source search checked Parikh–Wilczek's energy-conserving tunnelling paper and later work on inter-emission correlations; none supplied this countable affine-rank classification. Priority remains **provisional** pending expert review.

## Surviving PW-B core

Countable indexing alone is terminal under unconditional summability and linear grade coupling. PW-B now requires at least one of:

- a conditional or renormalized summation law with source-canonical cofinal order;
- nonlinear/nonpolynomial dependence on grade residuals;
- an independent physical orbit or channel;
- a literal source annihilation law produced before Xi-divisor selection.

No RH proof is claimed.
