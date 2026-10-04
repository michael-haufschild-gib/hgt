# Route PM: uniform separation on the actual logarithmic source carrier

- **ID:** pm-ramanujan-band-physical-separation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, fully audited)
- **Dependency:** `PMRamanujanBandSpectralEscape`, fully audited.

## Exact target and paper proof

Let G_X be X^epsilon times the actual logarithmic source vector for the complete natural band (floor X, floor(2X)], defined as zero below the admitted cutoff. For every epsilon>0 there exists c>0 such that for every fixed physical logarithmic L2 vector G and every real B there exists X>=B with ||G_X-G||>=c.

The literal finite-band Fourier identification already gives T_X(tau)=Fourier(g_X)(tau/(2*pi)). Define the unitary V by Fourier followed by the normalized L2 dilation with factor (2*pi)^(-1). Its representative is (2*pi)^(-1/2)*Fourier(g)(tau/(2*pi)). Consequently the actual critical-frequency vector is exactly sqrt(2*pi)*V(g_X), as an L2 vector, not just an equality of individual norms. Almost-everywhere Fourier representation and nonsingular dilation justify this identity for the actual L1 and L2 logarithmic source.

The same identity holds after normalization by X^epsilon and below the cutoff where both carriers are zero. Apply the common frequency-space separation radius to sqrt(2*pi)*V(G). Linearity and the exact isometry law turn the difference norm into sqrt(2*pi)*||G_X-G||. Dividing the frequency radius by this positive constant proves the target, uniformly in G.

## Scope

The already audited squared norm of g_X is exactly the original complete discrete reciprocal-weight energy. This transfer identifies the same physical source, with every denominator and mixed term retained. Integer/dyadic cutoff strengthening is separate. This does not bound the moving remainder from above or prove/falsify RH.

Search155 was partial with complete inventory and mixed compiler freshness; all candidate/source statements and both ingredient groups inspected. The seven exports passed the targeted old-mode leaf build (105 seconds), mandatory final actual-file `lake env lean` with no diagnostics, and seven individual axiom queries, all showing only propext, Classical.choice and Quot.sound. Umbrella wired once. Lint has eleven unrelated unreachable modules, no own finding. Completed audit artifacts cleaned after verification.
