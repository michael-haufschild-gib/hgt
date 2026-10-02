# TG exact Fourier-source completion and neutral obstruction

- **ID:** TG-C8-COMPLETION
- **Stage:** 3-formalized
- **Route:** TG
- **Module:** `RHTower.PrimeBurnolFourierCompletion`
- **Parent:** `../1-in-progress/tg-fourier-paired-source-collision.md`

## Exact source completion

Let H be the corpus's actual even physical L2 carrier and J its Fourier involution. The exact
unitary `V=halfLineExpUnitary.trans logEvenUnitary.symm` satisfies
`e_i=sqrt(2) V f_i` for each literal even prime column. Consequently, every individual prime's
depth span is dense in H, and the two-coordinate depth core is dense in H × H.

Its bounded joint synthesis is `S(x,y)=x+Jy`. The kernel is exactly `x=-Jy`. Define

```
T(h) = (h/2, Jh/2),
K(x,y) = ((x-Jy)/2, (y-Jx)/2).
```

Lean proves `S T=I`, `S K=0`, `T S+K=I`, `K²=K`, and `Kz=z iff Sz=0`.
These identities classify the actual bounded completion and its split quotient. No Hilbert
quotient-norm claim is inferred from the product-space norm used in the source code.

For every prime p and every real C, the finite-coordinate source core contains z with
`C norm(Sz) < norm(z)`. Proof: otherwise continuity extends that closed inequality from the
dense source core to a nonzero actual kernel vector, a contradiction. This is a failure of
uniform inverse control in physical channel norms, not an asserted numerical divergence rate
for arbitrary coefficient normalizations.

## Neutral information lost by the quotient

For `P(x,y)=(x,0)`, every actual nonzero source column v gives kernel vector `(-Jv,v)` but
`S P(-Jv,v)=-Jv != 0`. Thus the original neutral projection does not descend. Its canonical
section compression is exactly `S P T=I/2`; the idempotence defect is `-I/4`.

Together with `PrimeBurnolFourierPair`, this distinguishes finite collision repair from a
usable completed projection pair. The finite independence and bounded split synthesis are
positive survivors, now formalized. This closes only bounded inversion and original-neutral
descent for this particular source/Fourier completion. It does not exclude signed relative
constructions retaining additional source information.

Actual Gamma–Xi identification, a suitable cofinal relative cubic, Hardy-index transfer and
the sub-unit source action remain open. RH remains unproved and unfalsified. The next concrete
candidate retains the literal order-two radial jet before completion (TG-C9).

## Audit

- Production `lake --old env lean -o ... PrimeBurnolFourierCompletion.lean`: exit 0,
  no warnings, default heartbeats.
- Separate `lake --old env lean /tmp/tg-c8-completion-audit-01a0.lean`: all 18 public theorems
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- Both new leaves are wired to RHTower and present in the refreshed corpus index.
- Authoritative lint exits 1 for twelve unrelated unwired RHTower leaves:
  CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
  CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
  CCMRetainedChainKernelLower, MobiusDivisorCriticalAbelBoundaryMoments,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  RoutePDepthBinomialXiGraphCollapse, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
  Neither new TG leaf has a lint error. No unrelated repair was made.
- No full/umbrella build, raised heartbeat, numerical experiment, subagent, commit or push.
- Owned scratch, search and diagnostic files cleaned after recording evidence; production
  oleans retained. No owned process remains running. Scoped whitespace checks pass.
