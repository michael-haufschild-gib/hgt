# Directed prime rows at arbitrary bounded overlap

- **ID:** directed-prime-rows-at-arbitrary-overlap
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** The actual non-ratio prime form is infinitesimally bounded relative
  to the prime-edge defect, uniformly on every bounded overlap interval.

## Target

For each `K>0` and `ε>0`, find an explicit `C(K,ε)` such that, whenever
`0<w≤1` and `Nw≤K`, every real coefficient packet satisfies

`|NR_w(x)| ≤ (∫g²) [ε D_N(x) + C(K,ε) Σx_n²]`.

The profile is continuous and supported in `[0,w]`; `NR` uses the actual von
Mangoldt coefficients and every prime power. This is a source estimate, not a
positivity premise. Its positive consequence would be a uniform lower bound
for `D_N−NR_w/(∫g²)` retaining a positive fraction of the defect at arbitrary
bounded overlap. Complete Weil positivity also needs the archimedean and polar
comparison.

## Connection and proof obligations

`SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap` separates directed up
rows, bounded by a constant times `K`, from down rows, bounded by a constant
times `K(m/N)(log m+1)`. Existing estimates symmetrize these costs too early.
Use a free Young parameter before symmetrizing, then pay the down-row mass by
`sum_top_le_poleDefect_param`. This should replace a fixed defect coefficient
by any prescribed positive coefficient, including beyond the first shell.

- Check corpus for the same relative estimate.
- Prove the directed finite Schur inequality and the exact source bound.
- Retain all prime powers, both orientations, and the finite tail cutoff.
- Derive explicit uniform constants and the positive high-defect consequence.
- Check Lean, standard axioms, and umbrella integration before credit.

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
