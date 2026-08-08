# Arithmetic static-local hardness--recurrence window law (2026-08-08)

Stage-2 paper proof: docs/drafts/pipeline/2-fully-proven/arithmetic-static-local-hardness-recurrence-window-law.md
Master log appended: docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md

New theorem:
- If an integer-characteristic-polynomial Hermitian D-level H has rationally independent projective frequencies and R >= ||H||, every relative phase cube radius rho occupies at least mu/2 of every time window of explicit length
  T = 8(2N+1)^(D-1)(2(D-1)NR)^(D!-1),
  mu=(rho/(2pi))^(D-1), N=ceil((8pi(D-1)/(rho mu))^2).
- Proof: field norm gives |k.omega| >= (2(D-1)NR)^(-(D!-1)) for bounded nonzero k; product Fejer tent has uniform approximation error mu/4; shifted Fourier averaging gives cube occupation mu/2.
- Minimum spectral gap retired again: spectrum {0,1,2+eta} has pairwise gap >=1 but action 2omega_1-omega_2=-eta.

Physical specialization:
- Product-local-Clifford Gaussian full-two-local family has collision-good cyclic open locus.
- Generic full-two-local characteristic polynomial has S_(2^n) Galois group.
- To put a rational S_D specialization inside any rational real box B, use birational T_i=(a_i+b_iY_i)/(1+Y_i). Positive integers map into B and preserve generic function field. Castillo--Dietmann quantitative HIT makes bad positive integer specializations o(H^m). Scale rational point to integer couplings.
- Same H gives product-input approximate complexity Omega((3/2)^n/log M) with positive occupation in every computably long window.
- Stronger Choi/TFD corollary: combine explicit phase-window law with existing universal Choi cap. Complexity Omega(2^n/log M) occupies positive amount of every explicit window; projective returns have explicit windows; consecutive return/hard/return blocks give computable repeated alternation.

Important priority boundary:
- Existing docs/drafts/pipeline/3-formalized/universal-static-choi-complexity-plateau.md already proves qualitative syndetic Choi hardness and ordered alternation. New content is explicit computable syndeticity constant L and positive occupation in every window for one algorithmically selected integer static two-local H. Do not reclaim qualitative syndeticity.
- Abstract torus filling (Dumas--Fischler 2112.11786) and quantitative HIT (Castillo--Dietmann 1602.00314) are known. Novelty candidate is their unconditional composition with robust static-local circuit obstruction and Choi alternation.
- Hostile limitations: T is catastrophically nonphysical (D! exponent); all-to-all two-local, uncontrolled coefficient height; no linear ramp, Brown scale, thermodynamic limit, or maximal arbitrary-2n-qubit state complexity. Product-input scale remains (3/2)^n.
- Finite Anderson corpus gives real dense/residual maximal rank but does not automatically give rational/integer arithmetic specialization in qubit-local geometry.
- No Lean written or built because corpus refactor active. Lean read only.
