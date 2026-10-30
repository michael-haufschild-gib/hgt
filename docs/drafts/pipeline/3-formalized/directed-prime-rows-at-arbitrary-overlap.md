# Directed prime rows at arbitrary bounded overlap

- **ID:** directed-prime-rows-at-arbitrary-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual non-ratio prime form is infinitesimally bounded relative
  to the prime-edge defect, uniformly on every bounded overlap interval.

## Theorem

For each `K>0` and `ε>0`, whenever
`0<w≤1` and `Nw≤K`, every real coefficient packet satisfies

`|NR_w(x)| ≤ (∫g²) [ε D_N(x) + C(K,ε) Σx_n²]`,

where `C(K,ε)=8(log 4+4)e⁴K²/ε + ε(ψ₀+1/2)` and `ψ₀=log 4+4/e`.

The profile is continuous and supported in `[0,w]`; `NR` uses the actual von
Mangoldt coefficients and every prime power. This is a source estimate, not a
positivity premise. More strongly, the actual normalized prime energy

`E_N=log(N)Σx_n²−primeSum(f_x)/(∫g²)`

eventually satisfies

`E_N≥D_N/2+[γ−1/4−C(K,1/4)]Σx_n²`.

One horizon works for all admissible widths, profiles, and signed coefficient
vectors. Every unit-mass bounded-energy sublevel admits approximation to any
prescribed squared error by one finite Ramanujan span, also uniformly over
those parameters. Complete Weil positivity still needs its archimedean and
polar comparison.

## Connection

`SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap` separates directed up
rows, bounded by a constant times `K`, from down rows, bounded by a constant
times `K(m/N)(log m+1)`. Existing estimates symmetrize these costs too early.
The free Young parameter replaces a fixed defect coefficient by any positive
coefficient, beyond every fixed successor shell. The existing small-overlap
bound required shrinking the ratio interval toward one; this theorem works
at every prescribed bounded ratio, with an explicit mass cost quadratic in
that ratio. It supplies the mixed prime-action estimate requested by CACT
and the bounded-overlap source comparison needed by completed-form methods.

## Paper argument

Put `A=2(log 4+4)e^(5/2)K`, `B=2e^(3/2)K`, and `S=Σx_n²`.
For each directed edge `m→n`, apply
`2|x_m x_n|≤t⁻¹√(m/n)x_m²+t√(n/m)x_n²`.
The two orientations of the actual source give

`|NR|/(∫g²) ≤ (A/t)S + t B Σ(m/N)(log m+1)x_m²`.

The existing prime-edge identity gives
`Σ(m/N)log m x_m²≤2D+2ψ₀S`, where `ψ₀=log 4+4/e`.
Take `t=ε/(2B)`. The target holds with

`C(K,ε)=8(log 4+4)e⁴K²/ε + ε(ψ₀+1/2)`.

Moreover, the sharp ratio-source bound
`P_N+(1−δ)D_N≤(log N−γ+δ)S` and the exact identity
`primeSum(f_x)/(∫g²)=P_N+NR/(∫g²)` show that the actual normalized
prime source retains a positive defect reserve at every bounded overlap.
Consequently its bounded renormalized energy sublevels still admit uniform
finite Ramanujan approximation, using the existing arithmetic compactness
theorem. This extends source control past all finitely many successor shells;
it does not identify the complete Weil form with this renormalization.

## Lean verification

Module: `CriticalArithmeticCorrelationTheory/DirectedPrimeRowsPreserveTheDefect.lean`.

- `abs_nonRatioForm_le_relative_defect`: explicit actual-source bound.
- `eventually_overlapPrimeEnergy_ge_defect`: positive defect reserve.
- `exists_ramanujan_approximation_of_overlapPrimeEnergy_le`: uniform arithmetic compactness.

Required no-olean check passed:
`lake --old env lean GaloisForLFunctions/CriticalArithmeticCorrelationTheory/DirectedPrimeRowsPreserveTheDefect.lean`.
All three transitive axiom lists contain only `propext`, `Classical.choice`,
and `Quot.sound`. Imported by the CACT umbrella; no umbrella build or new olean.

One source-estimate contribution; its helper lemmas and compactness consequence
are not counted separately. No RH, quasi-RH, census, or complete-Weil sign claim.
