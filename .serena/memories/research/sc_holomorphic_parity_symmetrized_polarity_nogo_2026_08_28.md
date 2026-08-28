# SC holomorphic parity-symmetrized polarity no-go (2026-08-28)

Completed hard-frontier SC cycle. Read-only frontier map was not edited.

## Lean artifact
- Module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicParitySymmetrizedPolarityNoGo.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Card: `docs/drafts/pipeline/3-formalized/sc-holomorphic-parity-symmetrized-polarity-no-go.md`
- Capstone: `RHTower.not_tendstoLocallyUniformly_normalizedXiC_of_paritySymmetrizedUnitization`

## New structural knowledge
For universal reservoir `R=I-11ᵀ`,
`det(I+R diag(b)) = ∏ᵢ(1+bᵢ)(1-Σᵢ bᵢ/(1+bᵢ))`.
When every `1+bᵢ>0`, determinant sign is classified exactly by polarity index `Σ bᵢ/(1+bᵢ)` relative to one.

At transverse input one, exact Gamma-Bockstein coefficient is `-(p-1)/(p+1)`. Forward packet unitized determinant is positive. Reflection makes weights positive and cofinal polarity index exceeds one, so reflected determinant is negative. Thus parity product `U_m(1)U_m(-1)` is eventually negative.

Corpus Xi reality plus certified zero-free unit disc imply `Re(XiC(1)/XiC(0))>0`. Therefore even, entire, center-normalized parity products cannot converge compact-open to normalized Xi.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicParitySymmetrizedPolarityNoGo.lean` PASS.
- Exact leaf `lake build GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicParitySymmetrizedPolarityNoGo` PASS, 41s.
- Scoped axioms only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden declaration scan and diff check PASS.
- Global lint reaches module but fails solely on unrelated concurrently unwired modules.

## Strongest survivor
Direct multiplicative parity symmetrization is closed. Viable SC correction must be orientation-sensitive and additive/coupled: preserve evenness and center unit while changing the reflected rank-one polarity index back across the exact wall. Novelty remains unverified pending independent expert review.