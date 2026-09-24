# TP2 → TP_∞ for the theta kernel: two routes killed, and why

`ThetaCuspKernelLogConcavity` proves `thetaCuspFullSource` (= Pólya kernel Φ) strictly log-concave
and says so itself: "order-two total positivity is strictly weaker than the all-order condition".
The all-node Bochner positivity of `thetaCuspCenterMixedDensity a` is RH-equivalent
(`thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis`). Two natural upgrades are dead.

**1. Pólya's convexity criterion is structurally unavailable.** If an even continuous `D → 0` is
convex on `[0,∞)` it is positive-definite. But `D_a` is smooth and even, so `D_a'(0) = 0`; convex on
`[0,∞)` with `D_a'(0)=0` forces non-decreasing, while the corpus proves
`thetaCuspCenterMixedDensity_le_zero : D_a t ≤ D_a 0` (max at the origin). Both hold only if `D_a`
is constant. So NO smooth even PD candidate here can be convex on `[0,∞)`; convexity-based
upgrades of TP₂ cannot work for this kernel. (Pólya's criterion needs a corner at 0, e.g. `e^{-|t|}`.)

**2. The fibrewise route is dead because the fibres are super-Gaussian.**
`D_a(t) = ∫₀^∞ r sinh(ar) Φ(r/2+t) Φ(r/2−t) dr`, so PD of `D_a` would follow from PD of each fibre
`f_u(t) = Φ(u+t)Φ(u−t)`. Log-concavity of Φ gives log-concavity of `f_u` — which does NOT give PD
(an even log-concave function can have a sign-changing transform, e.g. `1_{[-1,1]}`). Worse,
faster-than-Gaussian decay actively breaks PD (`e^{-t⁴}`). And Φ IS strongly super-Gaussian: the
corpus's own `thetaCuspLogConcavityScale x = π * exp x ^ 2 = π e^{2x}` is the natural curvature
scale of `log Φ`, i.e. `(log Φ)″ ≍ −e^{2x}`, unbounded, versus constant for a Gaussian. With
`Φ ~ 4π² e^{9x/2} e^{−π e^{2x}}` the fibre decays like `exp(−4π e^{2u} cosh 2t)`, whose transform is
a Macdonald function of imaginary order `K_{iν}` — exactly the object whose sign changes carry the
RH content. So fibrewise positivity is not available; the positivity of the whole IS the problem.

**Consequence.** Do not try to upgrade log-concavity to all-order total positivity by convexity, by
fibrewise decomposition, or by "Φ is log-concave hence nice". The corpus only extracts the SIGN of
`(log Φ)″` (`thetaCuspLogConcavityNumerator_neg_all`); what any real attempt needs is its
MAGNITUDE compared to a Gaussian benchmark, and that comparison comes out on the unfavourable side.

Related clean bricks added 2026-09-23 (all axiom-clean, RHTower):
`riemannHypothesis_of_laguerrePolya_XiC`, `riemannHypothesis_of_splits_jensenPoly_XiC`,
`laguerre_margin_neg_not_riemannHypothesis` (discharges the `hPolya` interface of
`laguerre_margin_neg_not_RH_of_polya` using `xi_laguerrePolya_of_rh` — a single real `t` with
`(Ξ')² < Ξ Ξ''` now refutes RH unconditionally), `laguerre_inequality_Xi_of_riemannHypothesis`.
