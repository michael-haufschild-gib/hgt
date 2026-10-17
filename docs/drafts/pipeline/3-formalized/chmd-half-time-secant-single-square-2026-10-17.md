# CHMD causal wave: the two-point sum as a single spectral square; polar anti-node tests

- **ID:** chmd-half-time-secant-single-square
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** user directive 2026-10-17 (Step B, two-leg convolution-square level) · STATUS MUST-1573
- **Statement:** `Ψ_{y/2}(z) = cos((y/2)ρ(z)) sech(z/2)` is an even strip function with
  `Ψ_{y/2}Ψ_{y/2}^# = ½(sech sech^# + cos(yρ) sech sech^#)`; `(φ_Λ(0)+φ_Λ(y))/2 = L_Λ(Ψ_{y/2}Ψ_{y/2}^#)
  = A(g_{y/2}) − T_Λ(g_{y/2}⋆g̃_{y/2})`, `g_{y/2} = stripTest Ψ_{y/2}`; at `y_k = (2k+1)π/√(7/4)` the test is
  pole-free and the two-point sum is a pure archimedean-minus-prime energy.

## Goal
Upgrade the one-leg linear transport (MUST-1566–1571) to the two-leg level: exhibit the two-point sum packet,
whose positivity for all `y` is RH, as the Weil form of one explicit real even test, and isolate the pole-free
members of the family.

## Gates
- [x] 0 → 1, 1 → 2 (paper proof: half-angle identity + strip conjugation symmetry + point congruence)
- [x] 2 → 3: `RHTower/CHMDHalfTimeSecantAutocorrelationAndPolarAntiNodeTests`, `lake env lean` clean,
  `lake build --old` olean, standard axioms, wired
- [ ] 3 → 4 not pursued

## Not done
Light-cone transmutation of `g_{y/2}` from `g_0 = sech(πx)`: the corpus has no Fourier pair for `sech(r/2)`
(only `|Γ(½+it)|² = π/cosh(πt)` and the `sech²` pair), so the closed form `g_0(x) = sech(πx)` and the
positivity of the initial profile are not in Lean. The anti-node tests `g_{y_k/2}` decay exponentially but
are not compactly supported, so they lie in the closure of, not literally in, the even polar cone of MUST-1524.

## Log
- 2026-10-17 — created in 3-formalized; STATUS MUST-1573.

## Update 2026-10-17 (later): transmutation and convolution square done
- Found the sech Fourier pair in the corpus (`HTGeometry/SechComplexFourierTransform.integral_cexp_div_cosh`),
  so the "Not done" item above is now done in the same module: `integral_inv_cosh_half_mul_cos`,
  `stripTest_sechHalf_eq` (`g₀ = sech(πx)`), `stripTest_sechHalf_pos`, `stripTest_halfTimeSecant_eq_lightCone`
  (half-time d'Alembert pair minus Bessel light-cone tail), `half_kernel_sum_eq_two_mul_crossCorr`
  (`½(K₀+K_y) = 2 g_{y/2}⋆g_{y/2}`). Standard axioms; olean built; wired.
- Still outside the literal MUST-1524 cone: `g_{y_k/2}` decays like `e^{−π|x|}` but is not compactly supported.
