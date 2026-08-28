# PW-B finite-polynomial grade darkness — 2026-08-28

Formalized a sharp no-go for every fixed finite polynomial nonlinear readout of literal Schwarzschild Parikh--Wilczek grade holonomy.

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekFinitePolynomialGradeNoGo.lean`.

Core result: literal imaginary PW holonomy is quadratic in grade. For reporter degree `d`, order `n=2d+1` weights `(-1)^(n-k) choose(n,k)` annihilate every degree-`d` polynomial reporter uniformly in `s`. Their outer product is finite-support, symmetric, nonzero (`K_nn=1`), and PSD on every finite section. It annihilates separable polynomial energies and every nested bivariate polynomial reporter whose outer degree is at most `d`.

Sharpness: order `2d` on monomial reporter equals `(2d)! * (4*wall(s))^d`; at explicit open-strip `s=1/4+I`, wall is 1, hence nonzero. Thus `2d+1` is exact first universally dark order.

Verification: direct `lake env lean` PASS; targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFinitePolynomialGradeNoGo` PASS; main theorem axioms only `[propext, Classical.choice, Quot.sound]`; scoped banned-token and diff checks PASS. Umbrella import added. Global lint still fails only for unrelated pre-existing unreachable modules.

Cards: `docs/drafts/pipeline/3-formalized/pw-b-finite-polynomial-grade-darkness.md` and `docs/drafts/pipeline/5-failed/pw-b-fixed-finite-polynomial-readout-no-go.md`. Frontier map remained read-only.

Literature audit: Parikh--Wilczek 2000, Kuwakino--Wen 2015, Roy--Rahat 2014, Ming 2024; none found finite-difference/binomial dark kernels or exact bounded-polynomial observability order.

Next PW-B survivor: unbounded/nonpolynomial grade resolution or independent dynamics.