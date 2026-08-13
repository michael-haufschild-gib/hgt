# Suzuki inverse-log grades are nuclear in the physical Gamma measure, formalized

- **ID:** `suzuki-physical-log-grade-nuclear-summability`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-physical-log-grade-nuclear-summability.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/SuzukiPhysicalLogGradeNuclearSummability.lean`
  - coefficient recursion: `formal/GaloisForLFunctions/RHTower/SuzukiVolterraLogGradeRecurrence.lean`
  - step weights: `formal/GaloisForLFunctions/RHTower/SuzukiRootPortObservationGram.lean`
    (`suzukiPrimePowerWeight`)

## Formal content

| Card | Lean |
|---|---|
| `(1)` word-sum majorant (with equality) | `sum_prod_suzukiWordWeights` (`= M_a^k`), `sum_suzukiWordCoefficient_eq` |
| `(7)` tail integral | `integral_sq_suzukiGradeProfile` |
| `(8)` exact gradewise `L²` norm | `norm_suzukiGradeProfileLp` (`|c| L₀^{-k}/√(2k)`), `norm_suzukiGradeProfileLp_le` |
| `(9)` grade sum | `sum_norm_suzukiWordProfileLp_le` |
| `(4)` nuclear bound at threshold `(13e)` | `summable_norm_suzukiWordProfileLp`, `tsum_norm_suzukiWordProfileLp_le` (`≤ C/√2 · q/(1-q)`, `q = M_a/(2L₀)`) |
| `(5)` Hilbert carrier | `summable_suzukiWordProfileLp` (absolute summability in `L²(dL)`) |
| `(13)` exact Volterra inverse | `suzukiVolterraInverse_integral` (`α/(2α+1) · A · L^{-α-1}`) |
| `(13a)` recursion factor | `suzukiPrimeNormalGradeFactor_succ` (pre-existing) |
| `(13b)` central-binomial factor | `suzukiPrimeNormalGradeFactor_eq_centralBinom` (`θ_k = binom(2k,k)/8^k`), `suzukiPrimeNormalGradeFactor_le_half_pow` (pre-existing) |
| `(13d)` specialized majorant | `sum_suzukiWordCoefficient_le`, `sum_suzukiWordCoefficient_subtype_le` (`≤ (M_a/2)^k`) |

## What the card actually closes

The nuclear route is formal on the card's own concrete objects, not on abstract numbers: the
alphabet is the oriented prime-power alphabet with the corpus weight `log p / p^{j/2}`, the
coefficient is the corpus Volterra factor `θ_k` (now with its closed central-binomial form), and
the profile is the exact grade germ `c · L^{-(k+1/2)}`.  For any tail `L₀ > M_a/2`, the complete
descendant hierarchy is absolutely summable in `L²(dL)` with the exact geometric bound
`C/√2 · q/(1-q)` — the physical Gamma measure carries the word carrier with no `dr/r` Fourier
upgrade anywhere, which is the card's headline `(4)`–`(6)` at the improved threshold `(13e)`.
The exact Volterra integral identity certifies that one prime step raises the inverse-log
exponent by exactly one, which is where the grade decay comes from.

## Hypotheses

Object data only: a finite oriented visible alphabet, a nonnegative overall constant, and the
tail threshold `L₀ > M_a/2`.  No RH, no numerical certificate, no `sorry`, `axiom`, `opaque`, or
`unsafe`.  Every theorem named above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The uniform word-coefficient majorant `(16)` (`SUZUKI-UNIFORM-PHYSICAL-WORD-MAJORANT`) for the
actual recursively forced weak solution is the card's own named open conjecture — the correct E1
target — and is research, not missing Lean; it is deliberately not introduced as a hypothesis
wrapper.  The remaining open gates are research: instantiating `(4)` for every completed zero
mode, Gamma coercivity to trace-zero `H¹`, corona and raw Evans injectivity, and RH.
