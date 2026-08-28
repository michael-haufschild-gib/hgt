# HC89 radiation-dressed source-FE coherent-cancellation no-go (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFECoherentCancellationNoGo`.
Card: `docs/drafts/pipeline/3-formalized/hb-radiation-dressed-source-fe-coherent-cancellation-no-go.md`.

New result: actual raw unit-seed nonlinear BM Ward projection equals retarded ingoing Green coefficient times literal polarized source. Define radiative source-FE cocycle `κrad(q)=G(Rq) κsource(q)/conj(G(q))`. It is nowhere zero, exactly transports raw amplitude anti-linearly, and satisfies `κrad(Rq) conj(κrad(q))=1`. Canonical weights `a=-κrad(q)conj(P(q))=-P(Rq)` and `b=P(q)` cancel the reflected raw pair. At every off-line copy both weights and both raw channels are nonzero. They also satisfy HC88's unique cancellation equation `a M(q)=b M(Rq)`. Main theorem packages this as a closed universal proposition.

Route impact: cancellation weights are not merely arbitrary; literal nonlinear source FE plus actual causal Green propagation canonically constructs the unique cancelling ratio. Only divisor-independent/fixed or reflection-real physical weight selection, or copywise darkness, survives.

Audit: direct Lean passed; targeted build passed 12,018/12,018; representative axioms only `propext`, `Classical.choice`, `Quot.sound`; lint had only pre-existing unreachable modules and no HC89 finding. Umbrella import wired. Frontier map remained read-only.

Next hardest audit: whether local detector/source algebra forces reflection-real weights, or whether radiative cocycle admits positive/Hermitian transported metric evading that condition.