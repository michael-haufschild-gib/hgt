# BAG actual Gaussian/logarithmic amplitude derivative budgets

01ax. Route BAG; hard moving-profile Sobolev transfer. Exact reciprocal
Fourier identity production13249 PASS, axiom77734 standard3. This card
targets its actual amplitude, not an auxiliary stationary replacement.

Corpus search /tmp/bag-parameter-derivatives-search-01ax.json: partial
semantic retrieval (Qdrant timeout), all66667 source files indexed,
generation1250191 current, background refresh incomplete. All20+20
candidate/source statements inspected. Relevant compact tensor derivative
mechanism: ChiRamanujanCubicBoundaryCancellation.compact_second_derivative_bound.
Actual all-order smoothness: contDiffOn_smoothAFECutoff_infty_pos.
Selected cutoff budgets: ChiCubicControlledCutoff, already audited.

Conjecture: F_(delta,h)(P)=eta_delta(P)*V(P)/(1+h*log P),
0<delta<1/2, 0<=h<=1, has uniform L1 mass and uniform first variation;
every kth positive derivative has L1 mass at most C_k/delta^(k-1).
For the original band, h=1/logN and delta=N^(-3/4). On support,
F_(delta,h)=logN*bagCubicMellinSliceValue N eta_N 0 (N*P).

Paper route: joint smoothness of G(h,P)=V(P)/(1+h*log P) near the compact
rectangle [0,1]x[1,2], denominator>=1. Parameter-dependent fderiv and
evaluation at1 show every partial P derivative is jointly smooth there.
Compactness bounds each derivative uniformly in h. Leibniz plus the
proved cutoff derivative L1 budgets gives the claimed full amplitudes.
Outside support local zero removes the log singularity; endpoints follow
the smooth cutoff's zero jets. Formalization starts in
/tmp/bag-amplitude-budgets-01ax.lean. No result claimed yet.

After this input: exact normalization, P/Q/R integration by parts,
curved-energy/Minkowski assembly, high-frequency and logarithmic-coordinate
tails. Arithmetic moving-test transfer and full sharp-action bridge remain
hard open. No RH conclusion.

CLOSED01ax: fullscratch7804emptyPASS, production70720emptyPASS, axiom83857
all5standard3. Index8173PASS/API5/importonce; lint19711two unrelated
unreachable362warnings,noownederror. P2/P3 record the exact actual family
and derivative budgets. Next P1 bag-actual-reciprocal-kernel-energy.
