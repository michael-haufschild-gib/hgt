# PW-B fixed finite-polynomial readout no-go

- **ID:** PW-B-P1-NOGO
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · PW-B
- **Statement:** Replacing affine PW-B cross-grade readout by any fixed bounded-degree polynomial readout does not restore observability.

## Goal

Test whether finite polynomial nonlinearization can remove the signed PSD dark sector of literal PW grade holonomy.

## No-go closure

- **Exact killing theorem/mechanism:** Literal imaginary PW holonomy is quadratic in grade. For degree bound `d`, the order-`2d+1` alternating binomial packet kills every composed reporter by finite-difference degree collapse. Its outer product is a nonzero symmetric finite-support PSD kernel and kills every bivariate reporter with bounded degree in one grade variable, uniformly in spectral parameter.
- **Strongest positive survivor:** Exact observability boundary. Order `2d` retains the degree-`d` monomial with value `(2d)! (4 wall(s))^d`; at `s=1/4+i` it is nonzero. Thus `2d+1` is sharp, not an artifact of a loose degree estimate.
- **New insight:** Finite nonlinearity cannot cure literal PW grade blindness. Any surviving PW-B mechanism must have unbounded/nonpolynomial grade resolution, depend on a genuinely independent dynamical channel, or alter the literal quadratic grade law.
- **Status:** Paper proof dependency-closed and formalized in `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekFinitePolynomialGradeNoGo`; direct Lean, targeted build, standard-axiom audit, scoped banned-token check all pass. Literature audit recorded on formalized card.

## Log

- 2026-08-28 — Fixed finite-polynomial PW-B repair retired by explicit sharp PSD dark kernel. Positive survivor formalized before closure.
