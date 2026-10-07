# Next conjecture: compact polar radical approximants with a uniform negative trace tail

Status: OPEN; source proof mechanism to audit, not a Lean theorem. Full exposing-ray matching and energy lower inequality remain OPEN.

Let F=D^3 Phi-(1/4)D Phi. Seek actual odd real C2 polar tests f_L supported in [-L,L], fixed Y,L0, and a quantitative superexponential approximation to F, such that for every L>=L0:

1. crossCorr(f_L,f_L)(y)<=0 for EVERY y>=Y, including the cutoff boundary and all lags above2L;
2. exp(-2*pi*exp(2)*exp(y))<=-crossCorr(f_L,f_L)(y) whenever Y<=y<=2L-4;
3. every integer trace and signed archimedean energy approximate those of F with explicit weighted error, strong enough to compare L=(log N)/2+C with the original exposingTail(N).

The first two assertions are a new constructive source goal suggested by all-order parity. Assertion3 is stronger and must be paid separately. None matches the prescribed negative exposing proportions merely by having negative signs. No negative full Weil energy is conjectured from a negative tail.

## Candidate construction avoiding cutoff derivatives

Use the existing nonnegative even C2 cutoff chi_L, equal1 on [-L+1,L-1] and zero outside[-L,L]. Fix eta(u)=fejerTestReal(u-1)-fejerTestReal(u+1), a real odd compact C2 source, with nonzero half-pole moment by its exact translation multiplier. Define

    f_L = chi_L F - a_L eta,
    a_L = FT(chi_L F)(i/2) / FT(eta)(i/2).

Both moments are real. Oddness gives the other half-pole from the first. Since FT(F)(i/2)=0, a_L is precisely a tail integral; the full theta envelope should make it superexponentially small. This keeps the tail sign of F and supplies exact polar admission without differentiating a cutoff. The literal corpus definitions and all Fourier normalizations must be checked before code.

Choose R containing eta's support and beyond F's fixed right-tail sign threshold. Outside[-R,R], chi_L has a fixed nonnegative sign, so f_L has the same one-sided sign as F wherever nonzero. A common full-series absolute envelope follows from bounded a_L and eta's fixed compact support. For y<=L+R, a central interval of length2 lies in the untouched cutoff plateau once L>=R+4. Its signed main term is the one from DIFFERENTIAL-PARITY-PROOF.md; adverse products require one argument in the compact core and are paid by the same exp(-a exp(2(y-R))) error. For y>=L+R, every nonzero convolution factor has BOTH arguments >=R, by compact support, so the convolution is nonnegative pointwise and odd autocorrelation is nonpositive. This covers the entire transition to zero beyond2L, not just fixed y as L tends to infinity.

[OPEN CORE] Verify a_L real/nonzero denominator, exact C2/support/polar identities, common envelope, plateau/core partition including endpoints, all integer weighted errors, and full signed Gamma-energy convergence. Retain the finite head n<exp(Y), which may have either sign. Those finitely many traces and the exact negative exposing proportions remain additional unsolved endpoint obligations; never discard them.

## Utility and novelty gate

This would construct a family of actual admissible compact sources with a uniform complete tail sign, rather than another obstruction imposed by a repeated spectral lattice. However, if the corpus already supplies this class, use it directly. A finite sign family alone is not significant progress on the exact endpoint unless its signed head and energy budget can be exploited. Before implementation, search the corpus and audit the natural-aperture/vanishing-tail comparison.
