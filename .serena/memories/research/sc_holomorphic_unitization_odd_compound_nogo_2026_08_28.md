# SC holomorphic identity-unitization odd-compound no-go (2026-08-28)

Formalized `GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicUnitizationOddCompoundNoGo` and wired it into `formal/GaloisForLFunctions/RHTower.lean`. Frontier map remained read-only.

Core theorem: for `R = I - 11ᵀ`, every principal minor of `R diag(b)` indexed by `S` is `(1-|S|)∏_{i∈S} b_i`, hence `det(I+Rdiag(b)) = Σ_S (1-|S|)∏ b_i`. If all `b_i<0`, the complete odd part under `b↦-b` is termwise nonnegative and the first three coordinates provide a fixed strictly positive cubic witness. Coefficient faithfulness at real `z=±1` transfers this to the actual holomorphic prime Gamma-Bockstein reservoir. Compact-open convergence to normalized Xi is impossible because Xi is even.

Capstone: `RHTower.not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicUnitization`.

Positive survivor: any additive SC landing must cancel the source-derived third exterior compound cofinally and then every higher odd compound; symmetrized determinants or genuine additive counterterms remain live.

Verification: direct source check PASS; exact leaf build PASS (`Built ...SourceHorizontalHolomorphicUnitizationOddCompoundNoGo`, 77s); scoped axiom audit only `[propext, Classical.choice, Quot.sound]`; forbidden declaration scan and scoped diff check PASS. Global lint reached the module but remained red only on unrelated concurrently unwired modules.

Card promoted to `docs/drafts/pipeline/3-formalized/sc-holomorphic-unitization-odd-compound-no-go.md`. Novelty remains unverified against literature; classical principal-minor identities themselves are not claimed novel.