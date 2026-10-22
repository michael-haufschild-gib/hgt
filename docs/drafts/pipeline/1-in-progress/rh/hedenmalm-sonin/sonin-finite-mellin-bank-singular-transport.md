# Sonin finite-Mellin-bank singular transport

- **Stage:** 1-in-progress
- **Status:** paper proof complete; Lean scratch written, foreground verification pending
- **RH status:** unconditional; neither assumes nor proves RH
- **Target manuscript:** 4-publication-ready/riemann-source-modular-superselection

## Exact theorem

Fix \(0<a<b<c\), \(q\in(a,b)\), and an aperture clock \(r_n\to\infty\) with
\(r_n>1\) and \(c\le r_na\). Let

\[
 f_n=f_{b,c,\,2\pi r_nq}
\]

be the actual normalized Sonin annular packet and let \(Z_n\) be successive-aperture transport
from the \(a<b<c\) flag at scale \(r_n\).

For every finite set \(E\subset\mathbb C\), every \(N\ge0\), and every
\(\varepsilon>0\), eventually

\[
 \max_{s\in E}(r_nq)^N
   \left|\mathcal M f_n(s)\right|<\varepsilon,
 \qquad
 \frac{\|Z_nf_n\|}{\|f_n\|}>1-\varepsilon.
 \tag{1}
\]

Consequently the same literal packet family is invisible faster than every prescribed algebraic
order to every fixed finite Mellin detector bank, while successive-aperture transport retains
asymptotically its full norm.

Independently, finite unit-weight packets assembled from this family drive the aperture-curvature
trace below every prescribed real level. Thus the invisible transport is not a vanishing
bookkeeping seam: its accumulated curvature is unbounded below.

## Proof

For each fixed \(s\) and \(N\), smooth compact support plus repeated Fourier integration by parts
gives

\[
 w^N\left|\mathcal M f_{b,c,2\pi w}(s)\right|\longrightarrow0.
\]

Composition with \(w_n=r_nq\to\infty\) gives the assertion for one exponent. Since \(E\) is finite,
intersection of these eventual sets gives the first half of (1).

Both \(\|f_n\|\) and \(\|Z_nf_n\|\) tend to the same strictly positive limit

\[
 L_{b,c}=\left(\frac12\int f_{b,c}(x)^2\,dx\right)^{1/2}>0.
\]

Their quotient therefore tends to one, proving the second half of (1). The curvature claim follows
from the uniform Hilbert--Schmidt energy floor \(1/4\) per sufficiently late unit packet and finite
packet summation.

## Universal interpretation

This is an exact incompatibility of observer topologies:

    every fixed finite Mellin bank, to every algebraic order
      -> packet disappears
    same packet under aperture transport
      -> asymptotically full relative norm
    finite packet accumulation
      -> curvature unbounded below

It upgrades “Sonin transport is singular” to a quantitative finite-observer theorem. It explains
why the manuscript's crease, pole, and frequency charts must remain complementary: no regular
finite scalar analytic observer can substitute for relation-valued transport.

## Formal map

Existing inputs:

- SoninMellinBlindness.tendsto_pow_mul_norm_soninPacketMellin
- SoninCouplingNonannihilation.tendsto_norm_soninPacketEven
- SoninCouplingNonannihilation.tendsto_norm_soninApertureCoupling_apply_soninPacketEven
- SoninUnboundedSourcePacket.exists_soninAperturePacketCurvature_re_opTrace_lt

Scratch:

- /tmp/SoninFiniteMellinBlindTransport.lean
- tendsto_soninAperturePacketTransportRatio_one
- eventually_finiteMellinBlind_and_soninTransportFull

## Gates

- [x] prior-research search
- [x] dependency-closed paper proof
- [ ] foreground lake env lean /tmp/SoninFiniteMellinBlindTransport.lean
- [ ] promote verified module into formal/GaloisForLFunctions/RHTower
- [ ] axiom audit
- [ ] manuscript theorem and proof
- [ ] literature novelty audit
- [ ] antagonistic journal review
