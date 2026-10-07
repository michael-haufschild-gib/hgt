# Denominator-three rigidity

Verdict: **SCOPED NO-GO** for central zeros, negative functional-equation sign, and containment of the complete ξ zero divisor by a nontrivial degree-three datum. Assigned rigidity target: **OPEN**.

The new Lean modules prove, without assumptions beyond the assigned correspondence:

- Every full-positive coefficient system has canonical mass at ordinate zero strictly below 1/4.
- There is a fixed δ>0, independent of λ, such that third-integral interval counting forces μλ((-δ,δ])=0.
- Every corresponding degree-three completion E satisfies E(1/2)≠0 and E(1−s)=E(s).
- If ordρ(E)≥ordρ(ξ) at every point, then λ(n)=Λ(n) for all n≥2 and RH holds. Consequently every nontrivial complete datum has some ξ-zero ρ with ordρ(E)<ordρ(ξ).
- Exact atom transport: 3μλ{t}=ord(E,1/2+it). No zero multiplicity is discarded.

Central exclusion uses a compactly supported test whose arithmetic pairing vanishes, together with the corpus's unconditional absolute fourth reciprocal-zeta-zero moment. Divisor containment uses spectral subtraction: μΛ≤3μλ proves positivity of the remainder (3λ−Λ)/2; exact measure balance gives half-integer counting, so the corpus's degree-two rigidity applies. No RH for ζ, Euler product, zero simplicity, coefficient sign, finite-type condition, or regular-deviation premise is added to the final dichotomy. All four new modules passed targeted `lake --old env lean` checks and are wired into the umbrella. Axiom audits show only `[propext, Classical.choice, Quot.sound]`. Latest global lint fails on ten unrelated unreachable modules; see EVIDENCE.md.

Files: `formal/GaloisForLFunctions/RHTower/WeilWorkHigherDenominator{CentralTest,CentralExclusion,SpectralSubtraction,Multiplicity}.lean`. Parent methods are classical; the multiplicity dichotomy formalizes the corrected L223 boundary. Novelty label: **BRIDGE / UNESTABLISHED**.

Three further modules now close the finite boundary-packet receiver. A finite sum `Σ exp(−ρ log x) Pρ(log x)`, with distinct exponents of positive real part, cannot satisfy the odd weight-one modular period identities unless every polynomial vanishes. The proof derives regularity and decay from the packet, obtains the boundary bound by telescoping, then eliminates arbitrary polynomial orders by bounded finite differences. Equal real parts and oscillatory cancellation are allowed. The modular identity is also proved directly for the actual Maass inversion defect. Files: `WeilWorkHigherDenominator{PeriodDefect,PoleModes,FiniteBoundary}.lean`; all three passed targeted `lake --old env lean` checks without diagnostics and are wired. All fifteen exported theorems were axiom-audited: only `[propext, Classical.choice, Quot.sound]`. This is a classical analytic **BRIDGE**, not a novelty claim.

This excludes subclasses; it does not classify all positive-sign degree-three data or construct a producer. Next conjecture: a nontrivial datum has infinitely many multiplicity deficits. The actual quotient has not yet been transported to the checked finite-packet receiver. PROOF.md gives an explicit Poisson-integral construction and locally uniform boundary estimates for all logarithmic orders at paper level; its Lean formalization, quotient growth, and the finite-pole Mellin-axis expansion remain open. Available finite-pole Maass citations do not pay those obligations automatically. The assigned WP07 target remains **OPEN**.

Two older paper-note inferences require correction: if a zeta zero has multiplicity m, a pole of G/ζ³ of order greater than 2m gives ord(G)<m, not necessarily G(ρ)≠0. Infinitely many quotient poles likewise need not occur at simple zeta zeros. These are scope corrections, not new rigidity theorems.
