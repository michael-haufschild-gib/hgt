# Mass–Xi prime-square boundary residue

## Status

- Lane: `3-formalized`
- Conjecture: `C32` — proved
- Parent: C31 high-prime-power vertical ideal
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- Lean: `formal/GaloisForLFunctions/RHTower/XiMassPrimeSquareBoundaryResidue.lean`

## Exact theorem

Define the centered prime-square channel

```text
S₂(a,τ) = ∑' p : Nat.Primes, xiMassCenteredPrimeAtom a τ (p^2).
```

For every `a>0` and `σ>0`, Lean proves unconditionally

```text
∃ B : ℝ, ∀ u : ℝ, ‖S₂(a,σ+iu)‖ ≤ B.
```

Together with C31, this factors the literal §9.3 source modulo a vertically bounded ideal
through the valuation-one prime channel alone.

## Exact mechanism

For every `0<d<a`, atomwise strip transport and absolute reassembly give

```text
S₂(a,τ)
  = ∫ℝ xiMassBottomTest a d τ x · Q(1+2d+2ix) dx,
Q(s) = ∑' p, log(p) / p^s.
```

Rather than estimating `Q` by a lossy Chebyshev partial summation, the proof uses the exact
Euler-valuation identity

```text
Q(s) = (s-1)⁻¹ + zetaLogDerivReg(s) - H(s),
```

where `H` contains all valuation depths at least two in `-ζ'/ζ` at the doubled variable.
For `Re s≥1`, `H` has one uniform summable norm envelope. The pole-removed logarithmic derivative
has the global unconditional bound

```text
‖zetaLogDerivReg(σ+it)‖ ≤ K (1+|t|)^9
```

on every fixed strip `1≤σ≤D`; this combines the corpus low-box regularity bound with
`PNTPlus.ZetaBounds.LogDerivZetaBndUnif` above height nine.

Choose

```text
d(u) = min(a/2, 1/(1+|u|)).
```

Then `0<d(u)<a`, `|u|d(u)≤1`, and `1+2d(u)≤1+a`. The mass test is uniformly dominated by
`exp(1) exp(-σ|x|)`. Hence the regular term is controlled by the integrable function

```text
exp(1) K (1+2|x|)^9 exp(-σ|x|),
```

and `H` by a constant multiple of `exp(-σ|x|)`.

The pole does not cost `d(u)⁻¹`. A new generic even horizontal Cauchy theorem proves

```text
∫ℝ F(x-id) (x-id)⁻¹ dx = π i F(0)
```

for every even strip-analytic exponentially decaying `F`. Since
`s-1=2i(x-id)` on the natural square line, its contribution is exactly

```text
(π/2) xiMassAnalyticTest a (σ+iu) 0,
```

whose norm is at most `π/2` uniformly in `u`.

## New scientific knowledge

Valuation two is a removable Dirichlet boundary residue, not an RH-strength cancellation layer.
Its apparent critical weight `(log p)/p` is resolved only after preserving the full analytic
Euler identity: one rank-one pole plus a pole-removed zeta response and an absolutely summable
higher-valuation correction. Taking absolute values before this decomposition loses precisely the
residue structure and falsely leaves the square layer at the entropy wall.

C30–C32 yield a sharp quotient theorem: contour depth is a gauge; valuation depths `r≥3` form a
bounded ideal; valuation depth `r=2` is a bounded boundary residue. Only valuation depth `r=1`
can carry RH-strength vertical growth.

## Lean declarations

- `RHTower.integral_even_horizontal_cauchy_of_decay`
- `RHTower.integral_test_mul_xiPrimeLogDirichlet_eq_primeSquareLayer`
- `RHTower.xiPrimeLogDirichlet_eq_pole_add_regular_sub_higherValuation`
- `RHTower.exists_norm_zetaLogDerivReg_right_envelope`
- `RHTower.integral_xiMassBottomTest_mul_naturalPole`
- `RHTower.xiMassPrimeSquareAdaptiveDepth_spec`
- `RHTower.exists_norm_xiMassPrimeSquareLayer_vertical_bound`

## Verification

- `lake env lean GaloisForLFunctions/RHTower/EvenHorizontalCauchyResidue.lean`: PASS
- `lake env lean GaloisForLFunctions/RHTower/XiMassPrimeSquareBoundaryResidue.lean`: PASS
- `lake build GaloisForLFunctions.RHTower.XiMassPrimeSquareBoundaryResidue`: PASS (`9469/9469`)
- Axiom audit of four capstones: only `propext`, `Classical.choice`, `Quot.sound`
- No `sorry`, `admit`, local axiom, `opaque`, `unsafe`, computation proof, or RH hypothesis
- Both new modules wired into `GaloisForLFunctions.RHTower`

## Novelty audit

`[LOCAL-RESEARCH] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

Euler-product logarithmic derivatives, Cauchy residues, and zero-free-region log-derivative bounds
are classical ingredients. The exact classification of the mass–Xi prime-square channel as a
uniformly bounded boundary-residue layer, the adaptive-depth proof, and the resulting
valuation-one quotient were not found in the audited route corpus. External priority remains
unverified.
