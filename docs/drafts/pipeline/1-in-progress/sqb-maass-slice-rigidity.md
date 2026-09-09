# SQB original Maass slice rigidity

Status: original modal Cauchy uniqueness, open-band nonvanishing and strict
exceptional slice mass are formalized and audited. RH remains open.
Frontier map is read-only.

Full chain: original modular source → independent current comparison or
full-Xi spectral occurrence → critical-line classification → RH.

Height continuity reduces zero rectangle current to zero current on every
height in the band. Excluding that case requires genuine source rigidity.
Broad corpus inspection found no applicable general Maass nodal continuation
theorem. Build the actual Fourier-mode Cauchy argument and audit the stronger
whole-slice vanishing obstruction exposed by the existing boundary form.

The defining PDE gives a second-order linear ODE for every original Fourier
coefficient. On any positive compact height interval, its coefficient is
bounded. Apply Grönwall to the pair consisting of mode value and derivative
along an affine path to propagate zero Cauchy data in either direction.
Actual Parseval and source continuity then recover the whole source.

For an exceptional eigenvalue in (0,1/4), a whole zero horizontal slice also
annihilates outgoing flux and the actual Bessel boundary form. The existing
boundary-square identity and spectral tail identity force zero tail mass.
Continuity then gives a zero cusp region; the Fourier Cauchy theorem
propagates this to every positive height, contradicting the original
nonzero Maass source.

- [x] Broad OR corpus searches for PDE rigidity, coercivity, mode uniqueness and traces.
- [x] Prove original-mode Cauchy uniqueness on the full positive height domain.
- [x] Recover whole-source uniqueness from original Fourier data.
- [x] Prove whole-slice vanishing impossible for actual exceptional sources.
- [x] Extract strict slice-mass/nonvanishing consequences.
- [x] Audit scratch/source, targeted builds, axioms, wiring, index and lint.
- [ ] Exclude or quantitatively control zero current and the remaining common flat nodes.

A whole zero slice is stronger than a slice containing a common flat node.
This work must not conflate them or claim the remaining flat-node alternative
excluded. Quantitative area comparison and independent full-Xi occurrence
remain required for RH.

Every real-eigenvalue Maass source is nonzero somewhere in every open
positive-height band. For an exceptional source, every cusp tail and every
horizontal slice have strictly positive squared mass. Compact height bands
therefore have a positive integrated-mass floor. The full modular trace has
a positive point in each unit period at every height, and original zero
means supply separated positive-density directions at every height.

All 20 declarations passed scratch/source, the sole-target build and
standard-only axiom audits. All are indexed once and wired once; formal
lint passed. No owned compiler remains. The integrated-mass floor is not
a pointwise amplitude floor or a positive-current theorem.
[Complete proof and audit](../3-formalized/sqb-maass-slice-rigidity.md).
