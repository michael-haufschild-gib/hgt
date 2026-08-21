# RH frontier documentation cutoff — 2026-08-21 / 34b259 + reviewed worktree

Authoritative Lean-only frontier docs updated through commit `34b259ea2461dd2f86a2b01459da0df90c221824` and current reviewed working-tree declarations:
- `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`
- `docs/drafts/pipeline/1-in-progress/rh-route-literature-exchange-august-2026.md`

Evidence policy: Lean declarations/dependencies/docstrings and `scripts/formal_tools.py research` only. No cards/papers used as evidence. No Lean builds run.

Classification remains 17 live architectures and 13 candidates. No new route/candidate.

Material current frontier:
- Route O: `CCMActualHeadMatchedPhaseDiskSchurCompletion.lean` proves PSD 2x2 phase Gram, exact disk, literal prime-phase pointwise Schur completion, and exact reserve `4 w_n ||f||^2 - w_n E_f(log n)`. `CCMActualHeadMatchedPhaseDiskCofinalGaugeNoGo.lean` proves complementary positive channel/fixed trace, nonsummable prime center trace, no finite-valued positive linear extension preserving every finite cutoff, and every exact extension unbounded below on positive observables. Local completion is closed; scalar positive finite-part assembly is terminal. First open core: coefficient-faithful coupled trace cancellation before positivity (signed/nonlinear/relative/off-diagonal), preserving original completed source, physical cutoff, and boundary collar.
- O/G/CCM-FU seam: wall derivative recovers odd orientation; scalar reflection-even transport erases it; odd-by-odd polar pairing yields reflection-even covariant current exactly positive rate times matched Suzuki current. Wall curvature is positive dressing of CCM cubic prime-entry jet. G four-unit/Ward order and CCM-FU triangular-window cancellation remain open.
- HC: `ChenGuptaLiMellinPhaseJets.lean` closes all-order phase jets; `ChenGuptaLiHtAllOrder.lean` closes full first CGL Fourier-decay family `|xi|^j ||Fourier h_t|| <= C_(w,j)(1+|t|)^j`. Remaining CGL science is conductor/height-uniform not-all-equal weighted six-label correlation and large-height absolute census, not kernel decay.
- E: `CharacterSumMeanValue.lean`, `DenseModelBohr.lean`, `DenseModelPointwise.lean`, `BohrSetExistence.lean`, and `DenseModelArithmetic.lean` close finite multiplicative dense-model package. It does not define fixed Ramaré relation or prove interval Hall/unit load/co-moving flux/Gibbs cost.
- Generic HTGeometry/Bottcher/Choi additions have no completed prime-Gamma/Xi/RH landing and do not change route count. ABHN now has finite completion/local valuation/residue/Milnor infrastructure; nonarchimedean finite ramification, global ABHN exactness, and Xi landing remain absent.

Verification:
- frontier map 3991 lines (<=4000)
- `git diff --check` clean
- exact 17 live headings / 13 candidate headings
- no placeholder declarations in new route-relevant Lean worktree files
- no RH/Xi endpoint tokens in new E/HC adapter files or generic delta
- concurrent user/other-agent changes preserved and not edited except the two frontier docs
