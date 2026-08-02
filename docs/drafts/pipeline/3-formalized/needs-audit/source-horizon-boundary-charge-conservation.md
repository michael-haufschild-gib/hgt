# Source-horizon-boundary charge conservation

- **ID:** source-horizon-boundary-charge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** complete largest-valuation source, least-atom modular transfer, source-Cayley horizon, and Xi normal cone
- **Statement:** Reflected source entropy, source-horizon Poisson escape, and horizontal completed-divisor charge are exact representations of one base-independent invariant.

## Goal

Unify two previously separate corpus “parent laws” rather than append another
RH-equivalent coordinate.  The theorem must identify one invariant already
present before scalar divisor fusion, prove that it survives the singular
source-to-boundary transition, and show exactly how compact, even, or bounded
observers lose it.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete algebraic/analytic proof, no open dependency
- [x] 2 → 3  formalized: direct Lean checks passed
- [ ] 3 → 4  publication-ready: manuscript, priority audit, hostile review, final build/axiom/lint gates

## The law

Let
\[
\chi_{q,c}(s)=q^{c/2-s},\qquad q>1,
\]
and define its base-normalized entropy
\[
h_{q,c}(s)=\frac{\log|\chi_{q,c}(s)|}{\log q}.
\]
For reflection \(\sigma_c(s)=c-\bar s\),
\[
h_{q,c}(s)-h_{q,c}(\sigma_c s)
=-2\left(\Re s-\frac c2\right).
\]
Hence, for every multiplicity \(m\),
\[
\Re\!\left[-m\left(s-\frac c2\right)\right]
=\frac m2\bigl(h_{q,c}(s)-h_{q,c}(\sigma_c s)\bigr).
\]
Both sides are independent of atom base \(q\).

For a source-Cayley point \(a\), put \(c=2\Re a-1\).  Its exact Poisson
escape rate is
\[
\nu_a(s)=2\Re(s-a)+1
=-\bigl(h_{q,c}(s)-h_{q,c}(\sigma_c s)\bigr).
\]
Consequently the canonical-time transported residue packet is
\[
|m|^2
\exp\!\left(
 -[h_{q,c}(s)-h_{q,c}(\sigma_c s)]\,\tau
\right)\operatorname{Pois}_\tau(r).
\]

For the Riemann source \(a=1\), \(c=1\), and the canonical arithmetic
clock is the cofinal prime-two tail
\(\chi_{2,1}(s)=2^{1/2-s}\).  At a Xi zero \(\rho\) of multiplicity \(m\),
the nearby-cycle outer charge and the completed current
\[
\mathcal J_\Xi(s)=-(s-\tfrac12)\Xi'(s)/\Xi(s)
\]
have the same residue \(-m(\rho-\tfrac12)\), while
\[
\Re\operatorname*{Res}_{s=\rho}\mathcal J_\Xi
=\frac{m}{2\log2}
\log\frac{|2^{1/2-\rho}|}
{|2^{1/2-(1-\bar\rho)}|},
\qquad
\nu_1(\rho)
=-\frac1{\log2}
\log\frac{|2^{1/2-\rho}|}
{|2^{1/2-(1-\bar\rho)}|}.
\]

Thus the source-tail orientation, source-horizon escape exponent, and
horizontal divisor charge are one conserved scalar.  The two-prime source
tomography plus the multiplicity channel reconstructs the full complex
oriented divisor atom.

The law also has a global form.  For every Xi zero
\(\rho=\beta+i\gamma\), put
\(\delta_\rho=h_2(\rho)-h_2(1-\bar\rho)\).  Then
\[
\sum_\rho
\frac{\delta_\rho^2\gamma^2}
{((\beta-\tfrac12)^2+\gamma^2)^4}
=\mathcal E_{\rm thermal}
<\frac1{150000}.
\]
Thus the completed reciprocal-square orientation budget is exactly a
weighted \(L^2\)-budget for reflected arithmetic source entropy.

The singular completion forced by the local and cofinal no-go theorems exists
for this exact entropy, not only for a surrogate orientation coordinate.  Put
\[
F_\perp(z)=\Im(z^{-2}),\qquad
v_\perp(q)=F_\perp((\rho_q-\tfrac12)(-i)).
\]
Then
\[
Jv_\perp=-v_\perp,\qquad
\|v_\perp\|^2=\mathcal E_{\rm src},\qquad
\mathcal Q_\Xi(v_\perp)=-\mathcal E_{\rm src}.
\]
There are finite pairwise-separated continued prime--Gamma source packets
whose evaluation vectors converge to \(v_\perp\) and whose exact source
energies converge to \(-\mathcal E_{\rm src}\).  This closes common-test
representation unconditionally.  It does not close RH because the packet
section is selected through the target divisor vector rather than source data
alone.

## What this explains

- Squared Julia coordinates and reflection-even norms erase the entropy sign.
- Argument-principle and \(8\pi\) counts retain multiplicity but cancel the
  centered vector over a reflected quartet.
- Fixed compact/Ward windows lose a nonzero rate by escape, while canonical
  quadratic observation preserves its exact Poisson packet.
- Scalar source fusion kills the radical carrying the entropy, although the
  complete \(\ell^1\) source remains injective.
- A single prime clock orients the horizontal side but is vertically periodic;
  two incommensurable clocks reconstruct the full point.
- Fixed-scale positive fusion keeps the zeta bulk; inverse-depth passage
  creates the signed reciprocal boundary on which divisor polarity and the
  completed current live.

These are exact specializations.  Hedenmalm, Wold, Sonin--Calkin, and
four-unit Ward constructions are included only where their formal theorems
instantiate one of the stated information-loss mechanisms; analogy alone
does not count as a corollary.

## Formal source

- `formal/GaloisForLFunctions/HTGeometry/LeastAtomSourceBoundaryChargeConservation.lean`
  - `leastAtomTransferEntropy_reflectionDifference`
  - `centeredAffineCharge_real_eq_reflectedLeastAtomEntropy`
  - `sourceCayleyTransverseRate_eq_neg_reflectedLeastAtomEntropy`
  - `centeredCayleyAffineCharge_real_eq_sourceCayleyRate`
  - `sourceCayleyResidueMode_horizonConservation_entropy`
- `formal/GaloisForLFunctions/RHTower/XiSourceBoundaryOrientationConservation.lean`
  - `reflectedShellTailLogRatio_eq_centeredHorizontalDisplacement`
  - `centeredDivisorCharge_real_eq_reflectedShellTailLogRatio`
  - `riemannSourceCayleyRate_eq_neg_reflectedShellTailEntropy`
  - `centeredDivisorCharge_real_eq_neg_half_sourceCayleyRate`
  - `riemannSourceCayleyResidueMode_horizonConservation_shellTail`
  - `twoPrimeSourceSpectrum_determines_xiAffineCharge`
  - `xiZeroCopyThermalOrientationTerm_eq_sourceEntropyDensity`
  - `xiSourceEntropyOrientationEnergy_eq_thermalOrientationEnergy`
  - `xiSourceEntropyOrientationEnergy_lt_one_over_oneHundredFiftyThousand`
  - `xiDepthNearby_sourceBoundaryOrientationConservation`
- `formal/GaloisForLFunctions/RHTower/XiSourceEntropySeparatedSourceReconstruction.lean`
  - `xiSourceEntropyOrientationVector_apply_eq_sourceEntropyAmplitude`
  - `norm_sq_xiSourceEntropyOrientationVector`
  - `xiWeilLineConjLp_xiSourceEntropyOrientationVector`
  - `xiWeilHilbertQuadratic_xiSourceEntropyOrientationVector`
  - `xiSourceEntropyOrientationEnergy_separatedContinuedSource_reconstruction`

Direct checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/LeastAtomSourceBoundaryChargeConservation.lean
lake env lean GaloisForLFunctions/RHTower/XiSourceBoundaryOrientationConservation.lean
lake env lean GaloisForLFunctions/RHTower/XiSourceEntropySeparatedSourceReconstruction.lean
```

All three exited successfully on 1 August 2026.

## Novelty boundary

No novelty is claimed for logarithmic modulus of \(q^{c/2-s}\), residues
of \(F'/F\), or algebraic rewriting of a centered coordinate.  Novelty
claim is the exact conjunction with the independently constructed
largest-valuation zeta source, its prime-tail limit, canonical Cayley
Poisson transport, inverse-depth Möbius boundary, and completed Xi
normal-cone residue.  Targeted exact-phrase and formula searches found no
prior source stating this source-to-boundary conservation chain.  Search
failure is evidence, not proof of priority.

## Log

- 2026-08-01 — derived by equating independently formalized source-tail,
  source-horizon, and Xi-residue coordinates.
- 2026-08-01 — generalized from prime \(2\) to every atom clock \(q>1\);
  direct Lean checks passed.
- 2026-08-01 — constructed the signed source-entropy orientation vector and
  proved its exact separated prime--Gamma source-packet reconstruction;
  direct Lean check passed.
