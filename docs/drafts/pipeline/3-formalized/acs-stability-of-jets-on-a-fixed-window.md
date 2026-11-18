# Stability of archimedean jets on a fixed window

Fix a positive integer $K$. Suppose $|f|,|g|\le A$, both functions are $A$-Lipschitz, and $|f-g|\le\varepsilon$. Suppose they agree outside $(\log 3,\log K)$. At every positive mesh resolution $r$ the regularized jet forms on the window of length $3K$ then differ by at most $C_K A\varepsilon$. The bound is independent of $r$.

In the discrete Lévy decomposition the diagonal coefficient is the renormalized row minus its low and high tails. Wherever $f^2-g^2$ is nonzero, the degree index satisfies $3r<j<Kr$. On this interval the row finite part is bounded by convergence, and each tail is bounded by a constant times the Lévy antiderivative at $\log3$. Also $|f^2-g^2|\le2A\varepsilon$.

For two logarithmic sample points $u,v$ write $t=|u-v|$. The two increments differ by at most $2\varepsilon$ and their absolute values are at most $At$. The difference of their squares, multiplied by the Lévy density, has absolute value at most $4A\varepsilon t\omega(t)\le2A\varepsilon e^{t/2}$. The window bounds $t\le\log(1+3K)$, and its harmonic mass is at most $3K$. Summation gives the claim.

In particular, for a uniformly Lipschitz family converging uniformly to a fixed compact packet on this window, the jet forms converge to the same continuous archimedean value along every sequence of resolutions tending to infinity.

## Lean

`degreeForm_stable_on_compact_window` gives the resolution-independent bound. `tendsto_degreeForm_varying_compact_packets` gives the continuous archimedean limit for moving packets and resolutions together. [StabilityOfArchimedeanJetsOnACompactWindow.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/StabilityOfArchimedeanJetsOnACompactWindow.lean)
