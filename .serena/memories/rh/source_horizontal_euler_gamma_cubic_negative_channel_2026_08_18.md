# Pre-Xi Euler--Gamma cubic negative renormalized channel (2026-08-18)

Formal module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel.lean`.
Pipeline card: `docs/drafts/pipeline/3-formalized/source-horizontal-euler-gamma-cubic-negative-renormalized-channel.md`.

Heavy loop:
- genus-one det2 cubic failed: HS cube is trace class/summable;
- causal von Mangoldt derivative had correct scale but no source-forced sign;
- survivor is literal negative third derivative of finite Euler logarithm.

For prime p:
- Gamma/Euler atom G_p = (log p)^3 sum_{k>=1} k^2 p^{-k};
- Wold atom W_p = woldCoeff 1 p (log p)^2;
- D_p=G_p-W_p>0 and D_p <= 56(log p)^3/p^2, hence summable.
- raw G is non-summable and normalized ordered mass tends to 1/3.
- natural-number source extensions vanish off primes; ordinary `Finset.range X` cutoff proves (-G)+W=-D converges with cutoff-independent coefficients.
- finite raw negative current equals Euler third jet; exact k^2 depth series and reflected-Hellinger presentation proved.
- compensated BV Krein energy tends 0 and is eventually below every nonzero primitive source budget.

Capstone: `sourceHorizontalEulerGammaCubicNegativeRenormalizedChannel_producer`.
Leaf `.olean` build passed. Axiom audit: only propext, Classical.choice, Quot.sound. Module wired into RHTower umbrella; umbrella not built.
Global lint still fails only on pre-existing unreachable HTGeometry modules.

Frontier change: pre-Xi arithmetic primitive-budget obstruction is closed. Remaining open core is completed Gamma/polar physical descent carrying negative Euler third jet and positive Wold counterterm as independent signed/Krein legs on same Xi fibre, preserving prime/depth k^2, analytic multiplicity, four orientations, and BV endpoint defect. Alternate-presentation identification would double-count/erase summable defect.