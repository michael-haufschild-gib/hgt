# Ramanujan-Petersson Maass route audit
Goal remains unproved/unfalsified. Do not promote scalar Satake algebra or generic power-boundedness criteria to Maass temperedness.

New installed leaf modules under formal/GaloisForLFunctions/HTGeometry:
- GaussianStationaryDecay.lean: exact J(t)^2*(1-i*t)^3=pi/16 and norm(J(t))^4*(1+t^2)^3=pi^2/256, J(t)=integral_0^infinity x^2 exp(-(1-i*t)*x^2). q^4 norm(J(q^2)) unbounded even q=2^n. Finite quadratic vanishing does not imply rapid stationary-phase decay. Positive survivor is exact magnitude law.
- QuadraticPhaseTransport.lean: L=y*d/dx+x*d/dy, K=exp(i*(a*(x^2-y^2)+b*x)); L^2K=(i*b*x-b^2*y^2)K. Opposite-phase pair norm <=2*b^2*(x^2+y^2) for real parameters. Pairing repairs local quadratic bound, so missing product-rule term does not alone kill whole route. Distribution-to-kernel correspondence is not formalized.

Actual next obstacle: uniform cancellation for paired primitive-lattice sums under rational shear averaging/dilation, or another actual Maass Hecke-power bound. Absolute Fourier L1/moment bounds scale q and q^3, costing q^4; this is NOT actual lattice-sum growth lower bound. No actual Maass spectral exponent improvement was proved.

Both leaf builds and imported-module #print axioms audit of all 9 theorems pass; only propext/Classical.choice/Quot.sound. Default heartbeats, no numerical experiments. Removed Mathlib.Tactic import and replaced terminal nlinarith with multiplication monotonicity in kernel proof. Umbrella imports installed; no full build. Index completed. Global lint --check-generated failed on four unrelated unwired Theta modules plus stale LEAN_API/LEAN_OVERVIEW during concurrent changes; don't claim global lint success.

Own research card and crisp fact log: docs/drafts/pipeline/1-in-progress/ramanujan-petersson-maass-2026-09-26.md and -facts.md. Current source inspected: arxiv.org/html/2001.10956v16 Sections7-8 (claimed proof, not verified). Whole-index hybrid/deep/method searches often partial/source-only; no exhaustive corpus absence claim.