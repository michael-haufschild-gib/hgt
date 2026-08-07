# Route E static regular-kernel closure (2026-08-07)

Two new unconditional class theorems were paper-proved and Lean-formalized.

1. `RHTower/RouteEStaticAntiscaleFrameDichotomy.lean`: for fixed nonnegative `ω_p`, if `Σ ω_p/p` is summable, complete all-prime energy `Σ (ω_p/p)|1+p^{it}|²` is arbitrarily small at arbitrarily large `t`; if mass is nonsummable, zero-frequency terms `4ω_p/p` are nonsummable. No fixed nonnegative diagonal weight is everywhere finite and uniformly coercive.
2. `RHTower/RouteEStaticAbsoluteKernelRecurrence.lean`: for arbitrary complex ordered kernel `K_{pq}` with `Σ|K_{pq}|<∞`, complete form `Σ K_{pq}(1+p^{it})conj(1+q^{it})` has arbitrarily small modulus at arbitrarily large `t`. No positivity/Hermitian/finite-rank/diagonal premise.

Both imported in `RHTower.lean`. Targeted builds passed 9719/9719 and 9720/9720. Axioms only `propext`, `Classical.choice`, `Quot.sound`. Global lint found unrelated concurrent umbrella omissions, not proof debt in these modules.

Cards: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-e-static-antiscale-frame-dichotomy.md` and `route-e-static-absolute-kernel-recurrence.md`. Active Route E and frontier map updated.

Scientific status: class closure only; `OPEN-SOURCE-001` and RH remain open. Revised hard core: `GIBBS-MOVING-OR-SINGULAR-ANTISCALE-TRANSVERSE-SOURCE`—literal source must provide moving aperture kernel, non-absolutely-summable singular renormalized principal part, or signed nonquadratic terminal-shell cancellation, and produce `D_anti` or within-parity variation at physical-power strength. Bare off-diagonal regular kernel is now dead.

Related prior memory: `mem:route_e/parity_coarse_batch_rigidity_2026_08_07`.