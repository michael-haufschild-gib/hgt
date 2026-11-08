# Local Gamma Grams detect spline resonances

- **ID:** local-gamma-grams-detect-spline-resonances
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Fixed neighboring integer blocks retain exactly their autocorrelation Gram as leading logarithmic Gamma energy. Two adjacent copies of the tilted spline admit no uniform positive logarithmic Gamma reserve by coefficient mass, already at overlap two.

## Exact local law

Let `φ` be real and `C²`, supported in `[0,1]`. Fix `c>0`, `m∈ℕ`, and real coefficients `x_j`. For

`H=N+m`, `F_N(u)=Σ_(j<m) x_j φ(H(u−log(1+j/N))/c)`,

as `N→∞`,

`(H/log H) archForm(F_N) → c Σ_(i,j<m) x_i x_j G((i−j)/c)`,

where `G(t)=∫φ(v)φ(v+t)dv`.

## Proof

The rescaled centers satisfy `H log(1+j/N)→j`. Uniform compact support and Lipschitz bounds give convergence of the rescaled square mass. The existing two-sided atom self-energy inequalities give `archForm(F_N)=log H·∫F_N²+O(1/H)`, since each block has width `O(1/H)`, Lipschitz constant `O(H)`, and absolute integral `O(1/H)`.

**Exact two-copy resonance.** For any `C²` profile `ψ` supported in `[0,1]`, put `φ(u)=ψ(2u)+ψ(2u−1)`. At overlap `c=2`,

`Σ_(j<m) (−1)^j φ((v−j)/2)=ψ(v)−(−1)^m ψ(v−m)`.

For every `m≥1`, disjoint support gives square mass `2∫ψ²`, independent of `m`, while coefficient square mass is `m`. Also `∫φ²=∫ψ²`. Embedding these coefficients at the literal integers `N,...,N+m−1` and using translation invariance of Gamma energy gives the same limit for the actual horizon `H=N+m`.

Consequently there are no `a>0,b∈ℝ` such that, eventually for every horizon `H` and every coefficient vector `x`,

`((a log H−b)/H) Σ_(1≤n≤H) x_n² ≤ archForm(atomicTest H x (atomDilate φ (2/H)))`.

Such a bound would imply `a m≤2∫ψ²` for every fixed `m≥1`. Taking `ψ=tiltedUnitSpline` gives an explicit nonzero smooth counterexample.

**Positive classification.** Writing `M=∫ψ²`, the limiting Gram has diagonal `2M`, adjacent entries `M`, and all other entries zero. Indeed

`G_φ(t)=[2G_ψ(2t)+G_ψ(2t−1)+G_ψ(2t+1)]/2`.

Alternating conjugation gives the discrete Dirichlet Laplacian. The obstruction is loss of a uniform coefficient-mass floor, while every fixed block retains its physical Gram energy.

## No-go closure

- **Failed claim:** Every nonzero smooth supported profile retains a positive logarithmic Gamma reserve by coefficient square mass at bounded overlap.
- **Positive survivor:** Exact local Gamma Gram law and explicit tridiagonal kernel. The two-copy profile preserves square mass, while alternating atom coefficients cancel throughout the interior.
- **Scope:** This rejects a universal profile-transfer argument. Full Weil positivity and AAL remain undecided.

## Lean certificates

Namespace: `GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations`.

- `TheLocalGammaGramIsTheAutocorrelationMatrix.lean`: `tendsto_localIntegerBlock_archForm`.
- `AlternatingNeighborsPreventAUniformGammaReserve.lean`: `alternating_twoCopyProfile_square_mass`, `twoCopyProfile_local_gram_kernel`, `tendsto_alternating_twoCopyProfile_archForm`, `resonantTiltedSpline_certificate`.

Both direct `lake --old env lean` audits pass without warnings. All five capstones have exactly `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into the umbrella. The general Gram law quantifies over the stated class of smooth profiles; the explicit counterexample certificate has no hypotheses.
