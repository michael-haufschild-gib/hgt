# Arithmetic Auxiliary Dynamics programme

- **ID:** AAD
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0611/obstacles-summary.md, the field section "If positivity, Weil positivity and spectral methods are excluded"
- **Statement:** how the rational integers force zeros of ζ by construction and transport, with no sign.

## Goal
Develop the field: objects, tools, answers to its questions. Lean folder `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/`, umbrella `ArithmeticAuxiliaryDynamics.lean`, foundational document `ArithmeticAuxiliaryDynamics/README.md`.

## Status
All results below are Lean theorems, unconditional. Paper targets are closed.

- Scale: floor `c₁/(√K (1+log K))` (`exists_half_floor`); `K^{-a}` reads `Re ρ ≤ 1−a`; rates for all `a<1/2` give RH; `a>1/2` impossible. Peak law `w ≤ 100 (1+log K)² (K T + m)`.
- Construction: VK rate on polynomial alphabets (`hasRate_vk`); smooth compensation of the large primes gives RH ⇒ every `a<1/4`, strip `Θ` ⇒ `a<2(1−Θ)/(5−2Θ)` (`hasRate_of_riemannHypothesis_quarter`, `hasRate_of_zeroFree_quarter`). Exponent under RH in `[1/4,1/2]`.
- Rate = Mertens: `|M(n)| ≤ ε n + 12 (w/m) √n + K` (`IsProducer.abs_mertens_le`), `|M(n)| ≤ 3 ε n` past `K² log⁶ K`; scales coincide, elementary (`hasRate_exp_iff_mertens`, `exists_hasRate_rpow_iff_mertens`). So no certificate avoids `M(x)`.
- Exact LP duality, extremal fake prime measure, distance from the pronic one (`exists_extremal_bracket`). Profinite rigidity: class masses pinned at high level (`exists_level_classMass_close`); every finite shape reached at pronic cost (`exists_shape_producer`, `exists_spike_producer`).
- Parity: factor 2 is one Hecke factor; parity neutral producers at the Mertens level (`hasParityNeutralRate_vk`, `exists_hasParityNeutralRate_rpow_iff`). Rate bounds `L(x)` too (`IsProducer.abs_liouvilleR_le`).
- Curves: linear stencil window is `|a| ≤ q+1`; purity is the upper bound for curve and twist (`isPure_iff_upper_bound`).
- Ledger ladder: order law for all analytic `f`, generating function, twin gap.
- Transport: phase returns exist, aligned shifts below `(7N)^N` (`exists_isHeadReturn_le`); local effective transport with bound `N^A` in the aligned length (`exists_exponent_transport`). The disc of radius `31/10` about `3 + iγ` crosses the line, so the statements on it are vacuous: every disc of radius `R > 5/2` has `sup |ζ(· + iτ)| ≥ c τ^b` (`exists_rpow_le_of_norm_le_on_disc`, reflection plus a three-circle chain), an aligned length is `< 1024 (log τ)⁴ (log log τ)²` (`length_lt_of_isHeadReturn`), so `N^A` fails there at every long head return for every `A`, and the hypothesis of `asymptoticAbscissaLaw_of_slowReturns` is RH (`slowReturnHypothesis_iff_riemannHypothesis`). Along a phase return, bounded translates live in `Re s > ½` (`IsPhaseReturn.re_gt_half_of_translatesBoundedOn`). Survivor: transport and the AAL receiver on discs with left edge `σ₀ ∈ [½, β)`, exponent `transportExponent β (3 − σ₀)` (`transport_of_isHeadReturn_on_disc`, `asymptoticAbscissaLaw_of_slowReturns_right`; module `TheSlowReturnBoundLivesRightOfTheLine`).
- Tools: multiplicity and zero estimates on the gauge torus, Siegel with parity, effective Kronecker, Hurwitz limit set in the torus, transport count, return exponent, folding.

## Open core
A proof of `g ≥ 0` for an explicit family without a bound on `M(x)`; exponent under RH in `[1/4, 1/2]`; parity through the primes; arithmetic input for a nonlinear ledger (RigidArithmeticOfCuts); slow aligned returns at a zero on a disc with left edge in `[½, β)`, a bound `(log τ)^{O(1)}` at the aligned heights (heuristic, unproved: at a generic aligned return the head `Σ_{p≤N} p^{-s}` makes `|ζ| ≈ exp(c N^{1−σ₀}/log N)` there, so only returns whose alignment fades smoothly past `N` can qualify); Stepanov's twist over `ℤ`; finite-`K` form of the extremal measure. The first, the second and the fifth are at or past the strength of RH or AAL: they are research problems, not remaining formalization.

## Beyond the quarter
The compensated producer pays a failure at a prime power `Q` with the full mass `D_Q ≈ T/Q` of the letters `Q` divides. The typical deficit is `√T`. A bound of the worst-case deficit by `T^{1/2+ε}` would give `G ≈ √T/δ` and the exponent `1/3`; no such bound is known, and it is a statement about sup norms of truncated Möbius sawteeth.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (programme stays open on the core above)
- [ ] 2 → 3  formalized
