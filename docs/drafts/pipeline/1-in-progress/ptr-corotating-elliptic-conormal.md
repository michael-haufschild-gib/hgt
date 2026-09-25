# PTR co-rotating elliptic conormal test

- **ID:** ptr-corotating-elliptic-conormal
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (frozen; no route kill claimed)
- **Source:** [PTR frontier](rh-current-frontier-map.md#candidate-ptr), [literal ladder](../../../../formal/GaloisForLFunctions/RHTower/PhotonicHelicalInfiniteLadderCore.lean), [rotating-cylinder paper](https://arxiv.org/html/2609.08748v1), Eqs. (1)–(7).
- **Chain:** source-free rotating-cylinder Maxwell equation → full infinite interface relation → prime conormal landing/exclusion → RH.

## Frozen conjecture

For the literal two-dimensional nonmagnetic rotating-cylinder TE Maxwell equation, fix one helical Floquet sector with grades `(ω+nΩ, ℓ+nm)` and a cylinder collar where the local rotation speed `|Ω|r/|m|` is strictly below the local wave speed on **both** sides of the interface. Any distributional source-free solution satisfying Maxwell transmission has a smooth trace in the co-rotating angle at that interface. Consequently no fixed local finite-order trace/port of such a solution has the nonzero unit-modulus bilateral geometric sidebands `photonicPrimePCMConormalSideband p s` for `Re s=1/2`.

**Public meaning:** below the light cylinder, the apparent infinite time-crystal ladder is an elliptic spatial problem; a prime conormal delta would need a singular interface drive, a nonlocal ultraviolet port, or loss of subluminal ellipticity.

**Why this is a route-level test:** `PhotonicConormalFiniteEnergyNoGo` excludes only `ℓ²` traces; the current route survives through distributional traces and moving spatial modes. This conjecture addresses those escapes for the literal *local* cylinder trace. It does not exclude an independently specified nonlocal port or a driven interface.

## Attack and falsifiers

Write `φ=θ−(Ω/m)t`. Each locked mode becomes `exp(−i(ω−ℓΩ/m)t) exp(i(ℓ+nm)φ)`. The TE equation `ΔE−c⁻²∂t²(ε E)=0` becomes a spatial operator whose second-order angular coefficient is `r⁻²−c⁻² ε(φ)(Ω/m)²`. Strict subluminality makes its real principal form positive. With continuous tangential field and normal Maxwell flux, prove the elliptic transmission complementing condition, then tangential smoothness of every distributional solution. A unit-modulus geometric sequence is a translated Dirac comb in `φ`, not the Fourier sequence of a smooth trace.

Falsify by producing a source-free distributional Maxwell mode with this trace in a strictly subluminal collar, or by showing the physical prime port is not a fixed local trace of the locked sector. Check separately whether the paper's displayed device parameters satisfy the strict condition; no numerical experiment is evidence.

**Corpus shadows:** material grade/OAM locking becomes the co-rotating coordinate; the finite-modal regularity conjecture is its Galerkin shadow; finite-energy failure is its weak trace shadow; the surviving UV-escape example is tested by the full transmission claim. **Risky prediction:** in a source-free subluminal device, *every* critical-line prime conormal direct cylinder trace is excluded, although it is a tempered distribution. The light-cylinder threshold is the predicted sharp boundary.

**Lean-closed premise:** [`PhotonicCorotatingInterfaceSymbol.lean`](../../../../formal/GaloisForLFunctions/RHTower/PhotonicCorotatingInterfaceSymbol.lean) proves the exact locked-phase shear, sharp real-principal light-surface threshold, strict subluminality for the paper's displayed real dielectric and wall speed, and zero kernel for its two-sided decaying principal transmission system. Direct Lean and targeted `lake build --old` pass; umbrella import is wired, not built. This closes the *principal-symbol/complementing* premise only.

**Still open:** derive the source-faithful TE weak/interface equation and prove distributional variable-coefficient elliptic transmission regularity in Lean; then prove Fourier trace decay. More importantly, Eq. (5) of the physical paper has independent spatial index `σ`. Its full square-lattice Floquet field is not shown to occupy one locked helical sector or to read the prime sideband as a fixed local angular trace. That identification must be proved, not inserted. A fixed-sector local-trace no-go would retire that particular landing, not every nonlocal/mixed-sector PTR realization. The classical `PlanarLocalEllipticRegularity` starts from `C²` solutions and does not supply the distributional theorem.
