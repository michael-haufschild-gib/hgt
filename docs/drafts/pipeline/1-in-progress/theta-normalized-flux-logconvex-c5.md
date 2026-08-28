# Normalized reflected-source flux log-convexity forces global C5

- **ID:** CLG-TTF-NFL-C5
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md`, Routes CLG/TTF, global C5 burden
- **Statement:** For the completed-theta reflected product `P_u(t)`, the squared-displacement normalized decay flux `h_u(x) = -P_u'(sqrt x) / sqrt x` is log-convex on `x > 0`; equivalently its division-free residual `R_u(t) = 2 D_u(t)^2 - t D_u(t) J_u(t) + t^2 (D_u(t) K_u(t) - J_u(t)^2)` is nonnegative for `t > 0`, where `D_u = -P_u'`, `J_u = D_u'`, and `K_u = J_u'`.

## Goal

Close the global completed-source C5 numerator and hence the literal rank-four odd wall. This is source-pure: `P_u(t) = thetaCuspFullSource (u+t) * thetaCuspFullSource (u-t)` and no RH-equivalent statement is assumed.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Let `A_u(t) = P_u(0) - P_u(t)` and `D_u(t) = -P_u'(t)`. Then

`A_u(t) = ∫₀ᵗ D_u(s) ds`

and, after `x = t²`,

`A_u(sqrt x) / x = (1 / (2x)) ∫₀ˣ h_u(y) dy`,

where `h_u(x) = D_u(sqrt x) / sqrt x`. Direct differentiation gives

`4 t⁴ D_u(t)² (log h_u)''(t²) = R_u(t)`.

Positive scale averages preserve log-convexity by the two-variable Cauchy–Schwarz/Hölder determinant. Therefore `R_u ≥ 0` implies log-convexity of the squared-variable divided drop. The corpus identity

`C5_u(t) = 5 L_u(t) + (2 A_u(t) - t D_u(t))²`

then gives global `C5_u(t) ≥ 0`.

Equivalent direct integral mechanism:

- `tD_u(t) = ∫₀ᵗ (D_u(s) + sJ_u(s)) ds`;
- `4A_u(t) - tD_u(t) + t²J_u(t) = ∫₀ᵗ (3D_u(s) + sJ_u(s) + s²K_u(s)) ds`;
- the pointwise determinant between these two integrands is exactly `R_u(s)`.

The hard core is proving `R_u(t) ≥ 0` from the completed-theta atom–likelihood structure. Existing second-level concavity, correlation-angle concavity, local C5, Riccati margin, and six likelihood-jet orientations do not imply it.

## Hostile audit

- Corpus search used `scripts/formal_tools.py research`; no existing normalized-flux log-convexity declaration was found.
- The strongest corpus no-go kernel is `P(t) = exp (-(2t² + t⁴/5 + t⁶))`. Writing its action jets as `a=q'`, `b=q''`, `c=q'''`, one has
  `R/P² = 2a² - tab + ta³ + t²(ac - a²b - b²)`.
  At `t² = 1/2`, this is exactly `-46897/1000`. Thus the conjecture excludes, rather than inherits, the known second-level/Riccati/global-C5 counterexample.
- Targeted August 2026 literature audit found second-level concavity and general total-positivity/log-convex integration results, but no completed-theta normalized-flux theorem. Priority remains `[NOVELTY UNVERIFIED]` pending broader audit.

## Pivot criterion and positive survivor

If pointwise `R_u ≥ 0` fails for the completed source, retain the exact integrated decomposition

`L_u(t) = [A_u(t) ∫₀ᵗ (D_u+sJ_u)²/D_u ds - (tD_u(t))²] + A_u(t) ∫₀ᵗ R_u(s)/D_u(s) ds`.

The bracket is nonnegative by Cauchy–Schwarz. This yields the sharp signed-residual balance needed for `L_u ≥ 0` and is the mandatory nonlocal positive survivor if pointwise log-convexity is killed.

## Log

- 2026-08-28 — Created directly in `1-in-progress` after corpus-first derivation and hostile test against the strongest existing no-go.
