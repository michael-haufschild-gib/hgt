# Differential parity of literal polar radical tails

Cycle 14. Status: PROVED in Lean; full scratch and final installed leaf/cache audits pass without warnings. Universal WP02 lower inequality remains OPEN.

For every integer k>=0 put F_k=D^(k+2)Phi-(1/4)D^k Phi. Conjecture that, for some Y_k and every y>=Y_k,

    exp(-2*pi*exp(2)*exp(y)) <= (-1)^k integral F_k(t) F_k(t-y) dt.

These are literal real Riemann-kernel derivatives, not arbitrary profiles or a positivity premise. Their complex Fourier transforms equal (-iz)^k*(-z^2-1/4)*Xi(z), with the corpus's exact Xi normalization. Hence both half-poles and every actual Weil zero evaluation vanish. Every even derivative order has a positive autocorrelation tail; every odd order has a negative tail. This is a source sign classification, not an archimedean lower bound or an opposite-ray matching theorem.

Utility: cycle10's uniformly positive tail excluded only positive mixtures of even shifted sources. Odd differential polar radical sources escape that sign restriction while preserving the radical zeros. Before constructing a finite repair, retain compact truncation errors, every integer atom, exact target proportions and energy. A negative tail alone does not match -w_N and does not prove the endpoint.

Corpus audit: `RiemannKernelCuspSeries` proves the exact derivative cusp polynomial, leading coefficient, parity, superexponential decay and radical Fourier transform. `WeilWorkExposingRayUniformPolarTail` proves the k=0 differential-source case and a full signed-correlation error estimate. The new obligation is all-order parity with all oppositely signed contributions paid; no recalled analytic theorem is used as a premise. The targeted deep search completed non-partial, with 68,491 inventoried files and incomplete background/compiler refresh. Candidate and source-argument hits and the proposed ingredient set were inspected; the returned evenness/decay recipe does not prove this sign classification. No scientific novelty claim follows from retrieval.

External parent audit: Connes–Consani, *Weil positivity and Trace formula: the archimedean place*, https://alainconnes.org/wp-content/uploads/Selecta.pdf, pp.1–2, fixes the convolution/polar framework and explicitly distinguishes the small archimedean window from finite-prime positivity. It does not supply this derivative tail estimate or the missing WP02 inequality. Classical differentiation and Laplace-tail dominance are parent mechanisms; external novelty remains unestablished.
