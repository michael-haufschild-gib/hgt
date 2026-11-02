# Positivity of the Mayer scattering divisor and the arithmetic Hodge index core

- **ID:** mayer-hodge-core
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [route WD loop](wd-three-inputs-producer-loop.md) rows 52–55; [PM](route-pm-mayer-scattering-and-escape.md) Mayer 3–6; RIT README §8 topic 1.
- **Statement:** (1) decide whether the faithful Gauss–Mayer scattering divisor carries a positivity
  structure of its own that can place its events on `Re w = 1/2`; (2) push the unconditional
  renormalized Hodge index on `v_1^⊥` beyond overlap `(log log N)^{1/16}` toward the critical overlap
  `≍ log log N (log log log N)²`, where it is RH.

## Goal

(1) is the producer question for the PM route: the divisor is a faithful receiver; a producer needs
pole-excluding positivity. (2) is the RIT open core: positivity on the pole-orthogonal hyperplane is
proved at fixed and iterated-logarithmic overlap, RH at critical overlap; every gain in the schedule
is a new unconditional positivity statement.

## Gates
- [x] 0 → 1  in-progress: both questions well-posed against corpus statements
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Ledger

| # | Conjecture / mechanism | Verdict | Evidence |
|---|---|---|---|
| 1 | (1a) Transfer (Perron–Frobenius) positivity of the Mayer boundary response selects the divisor | classified: classical strength | `Q = −∂ log b(s+1)` has coefficients `Λ(n)(1−1/n) ≥ 0`; this gives `3+4cos+cos2` and width `1/(1000 log|t|)` (`GaussMayerBoundaryZeroFree`). Coefficient positivity is sharp at that level: Beurling systems with positive primes and an integer count better than `ℕ` have zeros at any real part in `(1/2, 2/3)` (`BeurlingOverRegularIntegersOffLineZeros`) |
| 2 | (1b) Hermitian positivity of the scattering sector (Maass–Selberg, Lax–Phillips, Gauss–Mayer Cauchy contraction) places the zeta events | refuted (formal) | This positivity is unitarity on `Re s = 1/2` (`Re w = 1`) plus contractivity to the right: the corpus deck bound `‖Φv‖² ≤ ‖v‖² + (2σ−1)‖Φv‖‖v‖/|t|`; numerically `|Λ(2s−1)/Λ(2s)| ≤ 1` on `Re s ≥ 0.51`, `|t| ≥ 5`, and `≤ 1.1` near the pole `s = 1`. `scattering_positivity_blind_to_zeros`: multiplying by a Blaschke pair `P_a`, `Re a > 1/2`, keeps `ψ(s)ψ(1−s)`, the real symmetry and the modulus on the line, lowers the modulus to the right, adds a nonnegative square to every Schur form, and puts zeros at `a, ā` anywhere. So this positivity localizes the events to a half-plane (`ζ(1+it) ≠ 0` strength) and no further |
| 3 | (1c) A Hermitian form on Mayer eigenfunctions centred at `Re w = 1/2` | refuted (structural) | The geometric reflection of the transfer structure is `w ↦ 2 − w̄` (Selberg: `s ↦ 1 − s̄`, centre `Re w = 1`, cusp forms); the zeta events reflect by `w ↦ 1 − w̄`. The two compose to `w ↦ w + 1`, so no structure carries both, and `b(1−w)/b(w)` for `b = 2ζ(w−1)/ζ(w)` contains `ζ(1+w)/ζ(2−w)`, not a Gamma factor: the arithmetic reflection is not an operator symmetry of `L_w`. Consistent with the corpus kills (scattering recentering, KR-AUT, KR-SEL, complex Cauchy contraction). Verdict for (1): the divisor is a faithful receiver; pole-excluding positivity must carry the arithmetic reflection, i.e. come from the Weil/Hodge side (2) |

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism (1):** Schur positivity is invariant under Blaschke relocation
  (`scattering_positivity_blind_to_zeros`); coefficient positivity is matched by Beurling systems.
- **Strongest positive survivor (1):** the relocation adds an explicit rank-one square
  `(2 Re a − 1)|Σ c_i φ(s_i)/(s_i − (1 − ā))|²` (`schurForm_mul_halfBlaschke`): adding right zeros by
  Blaschke factors only raises the Schur form, so Schur positivity can bound how few zeros there are,
  never where they sit.
- **New insight (1):** two reflection centres, geometric `Re w = 1` and arithmetic `Re w = 1/2`.
- **Status:** `RenormalizedIntersectionTheory/ScatteringContractivityIsBlindToZeroPosition.lean`,
  standard axioms only, wired into `RenormalizedIntersectionTheory.lean`.

## Log
- 2026-11-02 — created in 1-in-progress
