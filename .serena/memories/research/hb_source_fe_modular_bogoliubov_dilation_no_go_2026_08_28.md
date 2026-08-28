# HC79: source-FE modular Bogoliubov dilation no-go

Formalized in `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEModularBogoliubovDilationNoGo`, wired into `GaloisForLFunctions.RHTower`. Card: `docs/drafts/pipeline/3-formalized/hb-source-fe-modular-bogoliubov-dilation-no-go.md`.

For each reflected Xi orbit, choose the member whose literal BM source-FE cocycle squared gain is on the expanding sheet. Define `G` as that gain, partner number `N=G-1`, Bogoliubov gain `a=sqrt G`, and real pair amplitude `b=sqrt N`.

Unconditional Lean results:
- `G ≥ 1`, `N ≥ 0`.
- `a²-‖b‖²=1`: exact `IsTwoModeBosonicCCR`.
- Full Nambu map preserves signed Hermitian form for arbitrary inputs.
- `G` and `N` are reflection invariant.
- `N=0 ↔ Re(q)=1/2`; `N>0 ↔ Re(q)≠1/2`.
- `∀q,N(q)=0 ↔ RH`.
- Pointwise `N=0` iff HB optical darkness, Deninger Ward zero, FZZ-P force zero, every-grade PW-B balance, and canonical first-copy RBH balance.

Meaning: fibrewise bosonic CCR, pseudo-unitarity, signed-Hermitian conservation, and conservative KMS-style completion cannot force RH. Tilted source gain is absorbed as genuine partner production without inconsistency. Positive survivor is exact reflection-invariant partner occupation. Remaining producer must forbid it through source-global pre-divisor dynamics/locality/singular infinite-frequency coupling; assuming partner-vacuum extinction is RH.

Verification: direct Lean pass; target build 12018/12018; audited axioms only `propext`, `Classical.choice`, `Quot.sound`; lint has no HC79 finding and only unrelated existing unreachable modules.

Bounded primary-literature audit included arXiv:2608.11957, 1503.06109, 0710.3205, 2404.09446; no matching Xi/BM cocycle orbit theorem found as of 2026-08-28.