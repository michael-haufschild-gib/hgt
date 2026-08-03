# Route R graded-det2 Stokes/Cartier reflection no-go

Formalized `PrimeDepthBVWoldGradedDet2StokesCartierTrivialization.lean`.

Exact results:
- explicit anomaly satisfies `A_a(i,j,k) * A_(-a)(i,j,k) = 1`;
- reflection double `diag(A_a,A_(-a))` preserves hyperbolic Stokes pairing for every rate;
- positive Cartier diagonal `(1,1)` descends iff `a * curvature = 0`;
- on witness `(2,0),(2,1),(2,2)`, diagonal descent iff `a=0`;
- actual Xi reflected anomaly product is 1 for every divisor point;
- Xi witness diagonal descent iff `Re(rho)=1/2`;
- global positive diagonal descent iff explicit graded-det2 boundary triviality iff RH;
- concrete `a=1` theorem proves determinant/hyperbolic triviality while diagonal descent fails.

Scientific conclusion: unrestricted Stokes/Cartier trivialization is nonselective and retired. Source reflection gives indefinite metabolic trivialization, not positive same-fibre trivialization. Exact Route R open core is now an independently source-created positive same-fibre polarization plus a Stokes-flatness theorem; asserting its preservation is RH-equivalent/circular.

Cards:
- failed mechanism: `docs/drafts/pipeline/5-failed/route-r-source-stokes-cartier-graded-det2-trivialization.md`
- formal survivor: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-r-graded-det2-reflection-cartier-hyperbolic-classification.md`
- frontier map updated.

Verification: direct Lean passed; targeted lake build passed; formal lint passed; axioms only `propext`, `Classical.choice`, `Quot.sound`; no forbidden declarations; no stale Lean process.