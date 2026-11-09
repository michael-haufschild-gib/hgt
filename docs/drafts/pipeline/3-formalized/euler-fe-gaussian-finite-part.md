# The finite part of the full Gaussian prime current

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Euler–FE transport theory, §2.10: reflection of the rigid prime oscillation.

For `0<σ≤1`, write

`Gσ(y)=Σ Λ(n)n^(−σ)e^(−yn²)−∫₁∞u^(−σ)e^(−yu²)du`,

`Bσ(y)=Σρ ½Γ((ρ−σ)/2)y^(−(ρ−σ)/2)`, with multiplicity.

## Statement

`Gσ(y)+Bσ(y) → A(σ)−ξ′/ξ(σ)` as `y→0⁺`, without a
zero-free assumption. Here `A(s)=1/s+Γℝ′/Γℝ(s)` retains the polar and
archimedean terms. If a finite set `F` contains every zero with real part
at least `σ`, replace the full counterterm by its sum over `F`; the
infinite complementary series tends to zero. For `0<σ<1`, the sum of
the full finite parts at `σ` and `1−σ` tends to `A(σ)+A(1−σ)`.

## Proof

Write `E(y,a)=∫₁∞e^(−yu²)u^(a−1)du` and
`Rρ(y)=e^(−y)/(ρ−½)+E(y,ρ−σ)−½Γ((ρ−σ)/2)y^(−(ρ−σ)/2)`.
The exact Gaussian explicit formula gives `Gσ+Bσ=A_y−Σρ Rρ(y)`.
The Gamma germ estimate gives

`|Rρ(y)−e^(−y)Cρ|≤(9/4)(2y+2y²)|ρ−½|⁻²`,

where `Cρ=(½−σ)/[(ρ−½)(ρ−σ)]=(ρ−½)⁻¹+(σ−ρ)⁻¹`.
Thus `Rρ(y)→Cρ`. On `0<y≤1`, the summable bound
`|Rρ(y)|≤[(3/2)|½−σ|+9]|ρ−½|⁻²` permits dominated convergence through
the complete zero series. Xi has no real zero; its paired partial fractions
give `Σρ Cρ=ξ′/ξ(σ)`. The proved trivial-zero expansion gives `A_y→A(σ)`.
This proves the full finite part without an abscissa restriction.

For `ρ∉F`, the modulus of its Gamma mode is
`½|Γ((ρ−σ)/2)|y^((σ−Re ρ)/2)`. It tends to zero and is at most its
Gamma amplitude for `0<y≤1`. Those amplitudes are absolutely summable,
so the whole complementary series tends to zero. This uses strict
inequality for each zero, without assuming a common positive gap.
Absolute summation splits the full field into `F` and its complement,
proving the finite-layer statement. The corpus's isolated-top theorem
supplies this `F` from `¬AAL` throughout the interval between top and tail.

Finally `ξ′/ξ(1−σ)=−ξ′/ξ(σ)` cancels the two completed currents in the
sum of the full finite-part limits. The polar and archimedean background
survives exactly. No infinite Euler or zero tail is discarded.

## Scope

Existing Gaussian extremal laws identify the normalized leading oscillation.
This result recovers the unscaled continued background and its exact
reflection after subtraction of the full or admissible finite Gamma field.
It does not justify truncating the reflected field merely because the
original side has a finite top. Replication, `LinAt C`, and AAL remain open.
The reflection here acts on the Mellin weight `σ`. The literal theta action
on the prime oscillation still needs its own arithmetic construction.

## Formalization

Module: `EulerFETransportTheory/TheFinitePartOfTheGaussianPrimeCurrent.lean`.

- `tendsto_gaussianPrimeFinitePart`: the full continued finite part.
- `tendsto_gaussianPrimeFinitePart_reflection`: the exact reflected background.
- `tendsto_gaussianPrimeCurrent_add_finite_modes`: finite subtraction, with the
  whole complementary zero tail controlled and no uniform gap assumed.
- `not_asymptoticAbscissaLaw_has_gaussian_finitePart`: application to the actual
  finite top layer forced by failure of AAL.

Direct `lake --old env lean` check passes. All four transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
