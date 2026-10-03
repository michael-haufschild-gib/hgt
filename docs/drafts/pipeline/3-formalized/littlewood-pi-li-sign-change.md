# Littlewood: π(x) > li(x) infinitely often

Stage: 3-formalized (2026-10-03). Target (unconditional): `π(x) − li(x)` takes positive values for
arbitrarily large `x` (li(x) = ∫_2^x dt/log t); with the easy direction, it changes sign infinitely often.

## Plan (paper)

**Non-RH branch (Landau with log ζ).**  Π(x) = Σ_{n≤x} Λ(n)/log n; Π − π ≤ (ψ − θ)/log 2 ≤ C√x.
L(t) = ∫_0^t (e^u − 1)/u du has Laplace transform (1/s)log(s/(s−1)) (Frullani by Tonelli), and
L(log x) = li(x) − log log x + O(1).  If π ≤ li eventually then g(t) = (C+1)e^{t/2} + L(t) − Π(e^t) ≥ 0
eventually; s·Laplace(Π(e^t)) = CEL(s) (canonical Euler log, `canonicalEulerLogZeta`).  So for real s > 1,
s·Laplace(g)(s) = (C+1)s/(s−1/2) + log(s/(s−1)) − CEL(s) + entire = (C+1)s/(s−1/2) − log((s−1)ζ(s)/s) + entire,
analytic near the real ray (1/2, ∞).  Landau ⇒ abscissa = 1/2 ⇒ A(s) := s·(...) analytic on Re s > 1/2 with
exp(−A + ...) = (s−1)ζ(s)/s on Re s > 1 ⇒ ζ ≠ 0 on Re s > 1/2 ⇒ RH.

**RH branch.**  π − li = (θ(x) − x)/log x + ∫_2^x (θ(t) − t)/(t log²t) dt + c₀.  Under RH,
G(x) = ∫_2^x (ψ − t)/t = O(√x) (`riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound`), so by parts
∫(ψ − t)/(t log²t) = O(√x/log²x); ψ − θ ≤ C√x.  At Littlewood points ψ − x > c√x logloglog x
(`frequently_littlewood_lt_chebyshevError_of_riemannHypothesis`), hence π − li > 0.

## Lean status (all `[propext, Classical.choice, Quot.sound]`, wired after `LittlewoodOmega`)
- [x] Π (`primePowerCount`), Laplace `∫Π(e^t)e^{−σt} = CEL(σ)/σ` (`integral_primePowerCount_exp_mul`,
  PrimePowerCountLaplace.lean); `Π ≤ π + (ψ−θ)/log 2` (`primePowerCount_le_primeCounting_add`).
- [x] L = `logIntegralCompare`; Frullani `∫(e^u−1)/u·e^{−σu} = log(σ/(σ−1))` via
  `thetaRenewalFrullani_eq`; Laplace of L = log(σ/(σ−1))/σ; li(x) ≤ L(log x) + log log x + 1
  (LogIntegralLaplaceComparison.lean).
- [x] Landau: `zetaResidueUnit_ne_zero_of_primePowerCount_le` (Π(e^t) ≤ Ke^{at} + L(t) + M ⇒ no zero in
  Re > a, any 0 < a ≤ 1) and `riemannHypothesis_of_primeCounting_le_logIntegral_add_sqrt`
  (π ≤ li + K√x eventually ⇒ RH) (PrimeCountingLiLandau.lean).
- [x] RH branch: partial summation `primeCounting_sub_logIntegral_eq`, log-variable change
  `integral_theta_sub_eq_log_variable`, by parts against D(s) (`integral_chebyshevDeficit_div_sq_eq`),
  `exists_primeCounting_sub_logIntegral_ge_of_riemannHypothesis`.
- [x] Final: `frequently_logIntegral_add_littlewood_lt_primeCounting`
  (π(x) > li(x) + (c/2)√x logloglog x/log x i.o., c = 1/(70π³)) and
  `frequently_logIntegral_add_const_lt_primeCounting` (π > li + B i.o. ∀ B; B = li(2) gives the
  principal-value li) (PrimeCountingLogIntegralSignChange.lean).

## Log
- 2026-10-03: card opened (loop cycle 226).
- 2026-10-03: closed in Lean (MUST-724). The Landau receiver is stated for Π: any one-sided bound
  `Π(x) ≤ L(log x) + K x^a + M` (0 < a ≤ 1) excludes zeros of ζ from Re s > a [L]; for π this gives
  a ≥ 1/2 because Π − π ≍ √x/log x. The opposite sign (π ≥ li − K√x ⇒ RH) needs the same measure with
  density `K e^{at} + Π(e^t) − L(t) + M` (done below).
