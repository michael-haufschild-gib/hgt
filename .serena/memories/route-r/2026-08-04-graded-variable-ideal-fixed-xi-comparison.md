# Route R graded variable-ideal fixed-Xi comparison (2026-08-04)

Constructed and formalized `formal/GaloisForLFunctions/RHTower/PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean`.

Core:
- Ambient complex prime sequences `S=P→ℂ`, fixed ideal `I={a | Summable a}`.
- Fisher twist `F_t(p)=p^t p/(p+1)^2` (complexified).
- Raw reflection `C_t(a)_p=p^{-2t}a_p`; proved `C_t(F_t)=F_-t`, `C_-t C_t=id`, bijective.
- Maximal pullback ideal `J_t=C_t^{-1}(I)`; induced `S/J_t ≃ S/I` for every real t.
- Distinguished coefficient class lands exactly on fixed `[F_-t]`.
- In Xi strip, coefficient landing is injective iff `t≤0`; reflected iff `0≤t`; both iff `t=0`.

Actual source:
- Compose actual rational-adelic H1 period-one Stokes regulator with leading Xi jet.
- Explicit resolved frame `J_t × ℂ`; retained class maps to `(0, XiC^(mρ)(ρ)) ≠0`.
- Coefficient reporter equals second coordinate of existing strict positive-resolved Xi boundary at prime-localized depth 0→1 edge.
- Fixed physical specialization factors through resolved frame and sends class to `cρ[F_-tρ]`.
- Reflected specialization sends class to `cρ[F_tρ]`.
- One-side nonerasure walls formalized; simultaneous at rho iff `Re rho=1/2`; global simultaneous physical nonerasure iff RH.
- This is unconditional classification, not RH. No critical-line/nonerasure premise used.

Paper/frontier:
- Stage1 card: `docs/drafts/pipeline/1-in-progress/route-r-graded-variable-ideal-fixed-xi-comparison.md`
- Stage3 card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm/graded-variable-ideal-fixed-xi-comparison.md`
- `rh-current-frontier-map.md` updated.
- Umbrella import wired.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean` passes.
- targeted `lake build GaloisForLFunctions.RHTower.PrimeFirstTraceGradedVariableIdealFixedXiComparison` passes.
- load-bearing #print axioms: only propext, Classical.choice, Quot.sound.
- no sorry/admit/axiom/opaque/unsafe in module; no stale Lean process.

Exact remaining open core:
`RATIONAL_ADELIC_STOKES_FIXED_IDEAL_GLOBAL_NONERASURE`: derive from pre-divisor rational-adelic/Gamma source structure that both constructed physical maps retain the source class for every actual Xi divisor. This property is formally equivalent to RH, so cannot be asserted, pulled back as a norm, or inferred from resolved nonzero coefficient. Existing Stokes regulator gives resolved coefficient faithfulness, not fixed-ideal nonerasure. Generalized-prime off-line carriers must fail one orientation.

Related memories:
- `mem:research/rh_source_forced_horizontal_vanishing_frontier_2026_08_03`
- `mem:route-r/2026-08-03-singular-xi-landing-positive-completion-wall`
- `mem:route-r/2026-08-03-graded-det2-stokes-cartier-reflection-no-go`
