# PW-B complementary-clock forcing rigidity

- **ID:** PWB-cross-clock-forcing
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper; Lean pending)
- **Statement:** For every `q : XiZeroCopy`, neither the literal scalar `crossBranchClockForcing q` nor its coexact `crossBranchForcingCovector q` is identically zero on the upper half-plane.

## Proof chain and consequence

Literal two-event CTP source → complementary-rate product metric at clock `−6` → **nonzero forced** angular covector → ordered metric/contact current → oriented optical incidence → extinction/RH. This rules out a homogeneous scalar *or covector* cross-rate carrier. It does not identify the forced current with literal CTP, its boundary, optical flux, or RH.

## Paper proof

Write `U_b = fullAngularField q b`, `H = U_true U_false`, `S = scalar (center q)`. The corpus proves `ΔU_b − μ_b U_b = (μ_b/2)S²`, `μ_b ≠ 0`, modular invariance and smoothness. Its low-strip Weyl-mean argument (`pwb_forcingVector_ne_zero`) supplies a nonempty open patch `W` below height `2` where `S ≠ 0`. On `W`, neither `U_b` can vanish on a nonempty open subset: the equation would give `0 = (μ_b/2)S²`. Both nonzero loci are therefore open dense in `W`; they intersect. Hence `H` is not identically zero.

On the cusp `y > 3`, each `U_b = K_b(y) + R_b(x,y)`. `K_b` is the corpus's three-power `cuspResponse`, with exponents `2q, 1, 2−2q`, all real parts `< 2` because `0 < Re q < 1`. `R_b` is the actual response in hyperbolic `L²` on the modular cell (`globalResponse_ae_lift`, `globalLift_eq_on_fd`, `cellExtension_memLp`). Cauchy–Schwarz applied to `K_+R_-`, `R_+K_-`, and `R_+R_-`, plus the strict exponent bound for `K_+K_-`, gives

`∫_{y>3} |H(x,y)| y^(−4) dx dy/y² < ∞`.

Suppose `crossBranchClockForcing q ≡ 0`. The proved product equation and `crossBranchClockParameter_eq_twenty` give `ΔH = 20H`. More generally, **spectral rigidity:** any smooth modular field `G` with `ΔG=20G` and `∫_{y>3}|G|y⁻⁴ dx dy/y²<∞` vanishes. Indeed, expand in width-one horizontal Fourier modes. The constant mode is `c y⁵ + d y⁻⁴`; weighted integrability excludes `c`. At frequency `n ≠ 0`, put `a=2π|n|`. Its ODE is `f''=(a²+20/y²)f`, with independent solutions `e^(−ay)P(1/(ay))` and `e^(ay)P(−1/(ay))`, where `P(t)=1+10t+45t²+105t³+105t⁴`. Weighted integrability excludes the growing solution. Smooth Fourier data at a fixed cusp height and exponential decay then give `G∈L²`; Green's identity on the modular quotient yields `20‖G‖²=−‖∇G‖²`, hence `G=0`. Apply this to `H`, contradiction.

The coexact loophole also closes. Each cusp principal `K_b` has a nonzero leading Weyl coefficient on both branches: if `Re q>1/2`, use the `2q` coefficient; if `Re q<1/2`, use the `2−2q` coefficient; on the line, the `2q` coefficient is nonzero and both `K_b/y` are nonzero periodic exponential polynomials in `log y`. Nonzero source coefficients, branch parameters, and all three resolvent denominators are corpus theorems. Consequently there are arbitrarily large common height intervals where `|K_true|,|K_false| ≥ c y^β`, with `β=max(2 Re q,2−2 Re q)≥1`; off-line this holds at every sufficiently large height, on-line on periodically repeating log-height intervals. If `H=C` were constant, then for large heights in these intervals at least one `|R_b(x,y)|≥c y^β/2` at **every** horizontal `x`; otherwise `|U_true U_false|>|C|`. This makes `∫(|R_true|²+|R_false|²)dxdy/y²` diverge, contradicting their actual `L²` status. Hence `H` is not constant.

Finally `crossBranchForcingCovector = coexact(ΔH−20H)` on the positive-height chart. If this covector vanished everywhere, both coordinate derivatives of `ΔH−20H` would vanish, so that scalar would be a constant `C`. Then `G=H+C/20` is homogeneous and still has the weighted `L¹` cusp bound. Spectral rigidity gives `G=0`, making `H` constant—a contradiction. Thus the actual covector forcing is nonzero somewhere.

## Audit status

- Corpus source equations, clock `20`, cusp decomposition, and `L²` response verified by source inspection and corpus search.
- Paper argument dependency-closed; explicit modal ODE and modular Green step still require Lean infrastructure and formal audit. No Lean/Lake process launched after the OOM warning.
- Positive survivor: the exact nonzero coexact forcing must remain in any literal clock-`−6` stream metric equation; an ordered metric/contact current must transport it rather than substitute a homogeneous eigenmode.
