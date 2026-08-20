# Reciprocal Hadamard mixed-cumulant reconstruction — Lean certification

- **ID:** ULF-BFIM-1
- **Lean modules:** `HTGeometry.ConstitutiveBiFormationInterference`,
  `HTGeometry.ConstitutiveBiFormationAllOrder`,
  `HTGeometry.GaussianQuadraticCumulantCharacterization` (new)
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## The gap that this session closed

The card's own Lean certificate recorded exactly one uncertified item:

> The analytic identification of a quadratic moment-generating germ with a Gaussian probability law
> remains a dependency-closed paper proof, not yet Lean-certified.

That is clause 4 of **Theorem 2.2**.  Mathlib has the easy direction (`mgf_gaussianReal`) but no
characterization.  The new leaf supplies it:

* `gaussianComplexMGF`, `analyticOnNhd_gaussianComplexMGF`;
* `map_eq_gaussianReal_of_mgf_quadratic` — if the moment generating function of `X` is finite on
  `(−δ, δ)` and equals `exp(m t + v t²/2)` there, then `μ.map X = gaussianReal m v`;
* `mgf_eq_quadratic_of_map_eq_gaussianReal` — the converse, from mathlib.

**No Marcinkiewicz theory is used.**  `complexMGF X μ` is analytic on the open vertical strip
`|Re z| < δ` (because `(−δ, δ)` is open and contained in `integrableExpSet X μ`, hence in its
interior).  The entire function `exp(m z + v z²/2)` agrees with it on the real segment, so
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` on the convex — hence preconnected — strip
forces agreement on the whole strip.  The imaginary axis lies in that strip, so
`complexMGF_mul_I` and `charFun_gaussianReal` identify the two characteristic functions and
`Measure.ext_of_charFun` concludes.

## Everything else

Theorems 2.1, 3.1, Corollary 3.2, Theorems 4.1, 4.2, §6 split recovery and §7.1 carrier-valued
fusion are carried by the two pre-existing leaves, whose 24 public declarations were re-audited on
2026-08-20: both elaborate with 0 errors and use only `propext`, `Classical.choice`, `Quot.sound`.
All three modules are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.
