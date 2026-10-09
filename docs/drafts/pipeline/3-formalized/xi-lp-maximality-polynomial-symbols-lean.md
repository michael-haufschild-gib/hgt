# Ξ is LP-maximal for every real-rooted polynomial symbol (Lean)

- **ID:** lp-max-poly
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** card `1-in-progress/finite-order-newman-laplace-operator.md`; STATUS CANNOT-497 (Lean lines), MUST-868; loop rows 690–693 (`rh-route-candidates-loop-2026-10-08.md`)
- **Statement:** For every real polynomial `P` with only real roots and at least one nonzero root, no Laguerre–Pólya `ψ` satisfies `P(D)ψ = Ξ`.

## Goal
This closes the operator half of the W1C no-go. No producer of Ξ is a real-rooted differential operator applied to a real-rooted function. Together with Newman (`not_real_rooted_of_neg`, the Gaussian factor), RH, if true, has zero slack in every finite-order LP direction. The statement is unconditional; under ¬RH it is trivial.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven (degree two via theta Parseval; degree one via the large-gap tail and the two-radius energy core; polynomial symbols via first-order closure)
- [x] 2 → 3 formalized. Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`):
  - `RHTower.KernelStrip.not_exists_laguerrePolya_secondOrder_preimage_XiC`: `a₁, a₂ > 0`; module `RiemannKernelStripLPMaximality`.
  - `RHTower.KernelStrip.not_exists_laguerrePolya_firstOrder_preimage_XiC`: every real `a ≠ 0`; module `XiFirstOrderLaguerrePolyaMaximality`.
  - `RHTower.KernelStrip.not_exists_laguerrePolya_polynomial_preimage_XiC`: `(1 − c₁D)⋯(1 − c_nD)ψ = Ξ` impossible for nonzero `c_j`, any signs.
  - `RHTower.not_exists_laguerrePolya_firstOrderChain_iterate_deriv_preimage_XiC` (hgt-61): extra factors `D^m` are allowed; module `XiRealRootedPolynomialPreimage`.
  - Kernel forms (hgt-61): `not_laguerrePolya_dampedKernelTransform`, `not_laguerrePolya_gaussDampedKernelTransform`.

## Approach
1. **WLOG RH.** A first-order preimage makes Ξ Laguerre–Pólya (`laguerrePolya_sub_smul_deriv`), hence RH.
2. **Identification.** Zeros far to the right identify `Re f` with `kernelPsi (lorentzOne a)` (D1, hgt-61).
3. **Zero data.** Interlacing and Littlewood windows put a zero of `ψ` in `[x − 1, x]` and in every window containing two zeros of ξ (D3, hgt-61).
4. **Large-gap tail under RH.** `volume.real{t ∈ [T, 2T] : N(t+h) = N(t)} ≤ C T/(1 + h log T)^k` (`ZeroGapLargeGapTail`, hgt-61).
5. **Theta-boundary second moment.** `∫_X^{2X} e^{πy/2}\|Ξ\|² ≤ C X^{9/2} log X` (`exists_integral_exp_mul_norm_sq_XiC_le`). On `Im u = π/4 − 1/(2X)`, Riemann's kernel is a theta derivative at `τ = −e^{2u}e^{−2iε}`:
   - Parseval over the periods of `Re τ` gives flat window mass `κ^{−9/2}` below height 1;
   - Parseval masses decay like `e^{−πy}` above height 1;
   - the `log X` counts the unit windows.
   No approximate functional equation is used.
6. **Fourth moment.** `XiDyadicFourthMoment` (hgt-61): exact Gamma telescoping plus the corpus ζ fourth moment.
7. **Energy core.** `false_of_firstOrder_data`:
   - two-radius Grönwall `ψ² ≤ a²e^{2|a|r}·r·∫F²`;
   - a bad set controlled by the flat set `{N(t+h) = N(t)}`;
   - AM–GM against the fourth moment;
   - Abelian dyadic sums `Σ X_j^{9/2}e^{−δX_j} ≲ δ^{−9/2}`.
   Against the flat-mass lower bound for `kernelPsi (lorentzOne a)` (`exists_integral_norm_sq_shiftedProfile_lorentzOne_ge`), this gives a contradiction.
8. **`a < 0`** follows by reflection: `laguerrePolya_comp_neg`, using that Ξ is even.
9. **Polynomial symbols.** The inner factors keep LP, so the outer factor is a first-order preimage.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** the RC-filtered preimage keeps Ξ's low-frequency band `u = O(1)`. The flat theta mass gives that band a `1/log` share of the energy, but a preimage must vanish every `π/L` (`L = ½log(t/2π)`), and Poincaré allows only a share of order `1/L²`.
- **Strongest positive survivor:**
  - (i) The theta-boundary flat-mass law `∫_U^{U+1}\|Φ(u+ic)\|² ≍ (cos 2c)^{−9/2}`, uniform in `U` below height 1, as a Riemann–Siegel-free mean-value engine [L].
  - (ii) Under RH, for every `a ≠ 0`, the partial integrals `∫_{−∞}^{γ_k}e^{y/a}Ξ` fail to alternate in sign at some pair of consecutive zeros (loop row 692a: alternation ⟺ a first-order LP preimage exists, which the degree-one theorem excludes).
- **Sharp boundary [L]** (loop rows 700–701):
  - Ξ ∉ D^m·LP (`XiDerivativeLaguerrePolyaPreimage`), so every nonconstant real-rooted polynomial symbol is excluded.
  - Off the line, cos(hD)Ξ is LP for h ≥ ½ (`laguerrePolya_cosineShiftXi`) and lies in (1 − (2h/π)D)·LP for h ≥ 3/2, and for every h > 0 under RH (`exists_laguerrePolya_firstOrder_preimage_cosineShift_of_le`/`_of_rh`, hgt-8a). Zero slack is exactly an h = 0 phenomenon.
- **New insight:** RH has zero slack in every LP direction, whereas the function-field analogue has slack, since its minimum zero gap is positive (loop row 693). A proof of RH cannot be a stable-margin argument.
- **Status:** dependency-closed and in Lean for polynomial symbols, and for transcendental LP symbols with a real zero on the kernel side (`RHTower.KernelStrip.not_laguerrePolya_paperFT_div_symbol`, hgt-8a, MUST-873).

## Log
- 2026-10-09 — created in 3-formalized after the degree-one capstone (with hgt-61) and the polynomial-symbol closure.
- 2026-10-09 — Gaussian side of the boundary, now [L]: `e^{τD²}cos(hD)Ξ` has non-real zeros for every `τ > 0`, `h > 0` (`RHTower.DeBruijn.exists_cosineShift_negHeat_zero_im_neg`). Heat rigidity is shift-blind; only the finite-order rigidity sits at `h = 0`.
