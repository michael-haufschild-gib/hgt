# A gap for integrable functional-equation defects

- **ID:** integrable-fe-defect-gap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Γ74
- **Statement:** A countable Beurling system satisfying the existing Hamburger strip conditions and `Σ|x|⁻³/²<∞`, with integrable uncompleted FE defect `g` and `6400‖g‖₁≤1`, has exactly the positive integers as generalized integers, each once, and exactly the rational primes as prime labels.

## Paper proof

Finite norm sublevels follow from summability. The existing small-defect theorem at `N=4` gives unique atoms within `1/8` of 1 and 2. In particular a prime label exists; multiplication by its norm shows that the distinct norms have no maximum. Their locally finite order, with minimum 1, therefore has order type ℕ. Write them as `1=λ₀<λ₁<…`, with positive integer multiplicities `Aₙ`. Regrouping the summable series by finite norm fibers preserves the theta transform and inverse-square moment.

Mellin inversion gives the defective theta relation and its Laplace identity
`L(z)=F(z)−β/(πz)+β+J_g(z)`.
The estimate `|εJ_g(ε+iy)|≤(3/2π)√ε‖g‖₁→0` implies that the Abel cosine means have limits
`C₀→β/π`, `C_λₙ→Aₙ/(2π)`, and `C_y→0` at positive frequencies separated from the spectrum.
The complex radial limit `εF(ε)→β/π` is real, hence `β` is real. Put `ρ=2β`.
Positivity gives `1≤Aₙ≤ρ`.

For every real `r,p,q`, positivity of `|r−exp(itp)−exp(itq)|²` gives
`2r(C_p+C_q)≤(r²+2)C₀+2C_(q−p)`.
If `ρ²<2`, all `Aₙ=1`. If two consecutive atoms differ by `d<1`, then `C_d→0`; taking `r=ρ` gives `ρ²≥2`, a contradiction. Thus consecutive gaps are at least 1, and `λₙ≥n+1`.
The geometric-series bound gives `C₀(ε)≤1/(2π)`. Hence `ρ≤1`, and unit-density rigidity forces `ρ=1`, `λₙ=n+1`, `Aₙ=1`.
This proves the residue gap: `ρ∈{1}∪[√2,∞)`.

To enter the gap, put `M=‖g‖₁≤1/6400`. The existing rounding estimate gives
`|u−round u|≤√(3πM/2)u`; since `π<4`, atoms with `u≤2` are within `1/8` of their rounds.
Only the unique atoms near 1 and 2 can contribute to the unit tent at 1. Their contributions are respectively 1 and at most `1/8`, so its mass is at most `9/8`.
The tent FE error is at most `8M≤1/16`, hence `0≤ρ≤19/16` and `ρ²<2`.
The exact integer measure follows. Existing categorical Beurling rigidity then identifies the zeta function and gives a norm-preserving bijection of prime labels with rational primes.

## Lean

`ArithmeticPositiveDuality/SmallIntegrableDefectsForceTheRationalPrimes.lean`:
`beurlingSystem_rigidity_of_small_critical_line_defect`.

Supporting proofs: `IntegralSpectraHaveAPoleResidueGap`, `SmallDefectsBoundThePoleResidue`,
`BeurlingNormsHaveAnOrderedIntegralSpectrum`, and the radial pole-reality lemma in
`IntegrableDefectsAtUnitDensityAreRigid`.

The full residue classification is `pole_residue_gap_of_integrable_theta_defect`.

Direct `lake --old env lean GaloisForLFunctions/ArithmeticPositiveDuality/SmallIntegrableDefectsForceTheRationalPrimes.lean` check passed without warnings. All supporting modules passed Lean. Wired into `ArithmeticPositiveDuality.lean`.

Axiom checks skipped as requested. No ledger status change.
