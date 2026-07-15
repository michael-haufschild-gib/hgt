# Library update ticket: critical Möbius beta-wavelet bridge

Please add the following stage-2 paper theorem to the Door/library indexes during the next
single-writer index pass:

- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/baez-duarte-critical-mobius-beta-wavelet-law.md`

Index summary:

```text
The sequential Báez--Duarte coefficient is exactly one zero-mean beta-wavelet value of the
critical L2 Möbius boundary vector.  The wavelet is centered at log(2k+1)/2 and has an exact
weighted beta-function norm.  Plancherel also gives the exact zero-free-line value
(4pi)^(-1) integral B((1-it)/2,k+1)/zeta(1+it)dt.  An exp(alpha t)L2 moment gives exponent
(1+alpha)/2.  In the fixed safe squarefree Gibbs channel, |c_k| is exactly Z_* times the norm of
the existing signed-source projection of Y_k; the unconditional norm law ||Y_k||~C k^(-1/4)
turns the RH endpoint into normalized source-angle decay k^(-1/2+epsilon).  Thus the half-unit
continuation seam is precisely the missing quarter-power between the unconditional
k^(-1/2) bound and the RH-critical k^(-3/4+epsilon) bound.  The weaker source target is one
arithmetic cancellation coefficient per scale, not the full weighted-domain tower.
```

No Lean module was added: the current formal tree has the Möbius L-series and square-dilated
finite carrier, but not the critical Möbius `L2`/Stieltjes boundary API or the imported analytic
Báez--Duarte endpoint.  Verification was intentionally not run under the active no-computation
boundary.
