# Review-0611 §2.1 Continuation, near-line, production tasks (A19–A32)

- **ID:** review-0611-a19-a32
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md), table "Continuation, near-line, production"
- **Statement:** Each task A19–A32 gets a complete unconditional Lean theorem, easiest first. Rules: no computations, no end-of-run axiom audit, corpus search first.

## Status

| Task | Status | Lean / note |
|---|---|---|
| A20 | done | `HeatScaleRepulsion/TheExceptionalExponentIsCubic.lean`: `θ(κ)=1−κ³/41943040000` for `κ≤8`; large values at level `η³/40000` are the only binding term, shadows save `η/3` |
| A28 | done | `TheScatteringMatrixIsABlaschkeProduct.lean`: `S=φ(s)(s−1)/s=ξ(2s−1)/ξ(2s)`, `−log|S(w)|=Σ_ρ G(w,(1+ρ)/2)`, no singular part; zeros are reflected resonances; Gram = Szegő kernel. `ResonantStates/HeckeWordsHaveThePoissonSpectralMeasure.lean`: physical `⟨T_w t_Y,T_{w'} t_Y⟩=‖t_Y‖²∫P_{−Re u}(t−Im u)W_wW_{w'}` for all prime words; squarefree `=μ_n(u)` |
| A31 | done | `ZeroConfigurationGeometry/ThePrimeErrorExpansionLocatesZeros.lean`, `TheOneOffsAreFiniteOscillationsOfThePrimeError.lean`: `not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation` |
| A29 | done | `ArithmeticKunnethTheory/WeightFamilies/ReciprocalQuadricTrace.lean`: exceptional directions `X³ ∣ reciprocalSeries ⇔ Q=0`; `#P(Q=0)=Σ_{j≤2k}q^j+χ((−1)^{k+r})q^k`; over degree `d` the eigenvalue is `α^d`, `α=χ((−1)^{k+r})q^k` |
| A19, A21–A27, A30, A32 | open | A32: peer AAD programme works on stencil cost (`TheParityProducerHasAQuantitativeCost`) |

## Log
- 2026-11-06 — table renumbered to the current report; older numbering closed tasks (exceptional set, Gauss–Mayer boundary, sharp depth law, EGC contour, aperture Euler product) are in Lean already.
