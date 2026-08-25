# Painlevé III–Xi Differential-Gauge No-Go

- **ID:** painleve-iii-xi-differential-gauge-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** Michel Planat, *Wild Character Varieties, Painlevé III\(_{D_6}\), the Isomonodromic Cosine, and a Complete Positivity Framework toward the Riemann Hypothesis* (2026), Conjecture 3 and §10
- **Statement:** No fixed-monodromy Painlevé III\(_{D_6}\) isomonodromic tau-function, pulled back by `t = s(1-s)` and multiplied by any polynomial exponential gauge, can equal the completed Riemann `xi` function.

## Goal

Decide the paper's open Monodromy Selection Conjecture for its stated finite-dimensional wild
Riemann--Hilbert family.  The argument must be independent of zero computations, asymptotic phase
tests, RH, and choice of Stokes/monodromy point.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems `RHTower.xi_expPolynomialGauge_hypertranscendental` and `RHTower.no_entire_differentiallyAlgebraic_expPolynomialBridge_to_xi`; targeted `lake env lean` and module build green; new declarations pass `#print axioms`
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Literature audit

- Planat defines `E_D6(s) = exp(-2s) * tau_D6(s(1-s))`, conjectures
  `xi(s) = exp(Q(s)) * E_D6(s)` for a polynomial `Q` of degree at most two, and leaves selection of
  a distinguished monodromy pair open.  The paper states that a negative answer would prove the
  isomonodromic and arithmetic Hermite--Biehler subfamilies disjoint.
- Jimbo--Miwa--Ueno/Okamoto theory gives `sigma(t) = t * tau'(t) / tau(t)` and the
  Painlevé III\(_{D_6}\) sigma equation.  Modern PIII tau literature uses the same
  logarithmic-derivative/sigma characterization.
- Targeted searches found no use of differential hypertranscendence to decide this bridge.
- Novelty verdict: **[BRIDGE] [PROVED HERE]**.  Differential-algebra closure is standard; applying
  it to close the stated 2026 wild-RH monodromy-selection problem is the new delta.

## Corpus audit

- `RHTower.xi_hypertranscendental` proves unconditionally that completed `xi` satisfies no nonzero
  algebraic differential equation over `C(s)`.
- `differentiallyAlgebraic_exp_polynomial` and `differentiallyAlgebraic_mul` provide the exact
  polynomial-exponential gauge closure needed for Lean.
- No corpus theorem states the Painlevé/isomonodromic exclusion or polynomial-gauge invariance for
  `xi`.  Lean formalization should be an applied RHTower leaf, not new irregular-RH foundations.

## Conjecture and hostile attack

### Candidate killing theorem

Let `tau` be a nonzero local Painlevé III\(_{D_6}\) tau-function with fixed parameters and fixed
monodromy data.  If

`sigma(t) = t * tau'(t) / tau(t)`

satisfies

`(t sigma'')^2 = (2 sigma' - theta0 - thetaInf)^2 (sigma - t sigma')
  + 4 sigma' (sigma' - theta0) (sigma' - thetaInf)`,

then, for every polynomial `Q`, the function

`F(s) = exp(Q(s)) * tau(s(1-s))`

is differentially algebraic wherever defined.  Consequently no entire continuation of `F` equals
`xi`.

### Attacks

1. **Tau logarithm/movable zeros.**  `tau'/tau` is only meromorphic.  Clear denominators in the
   sigma equation.  Result is a polynomial differential equation for `tau`, valid off its zeros and
   then everywhere by analytic continuation.
2. **Could cleared relation vanish identically as a differential polynomial?**  No.  Its squared
   highest-jet term has coefficient `t^4 * tau^4` and no right-hand term contains `tau'''`.
3. **Quadratic pullback critical point.**  Away from `s = 1/2`, chain rule is triangular with
   nonzero diagonal powers of `1-2s`; clearing them gives a nonzero relation.  Analytic continuation
   crosses the isolated critical point.
4. **Exceptional monodromy.**  Monodromy selects a solution, not the sigma equation.  Every fixed
   monodromy choice remains differentially algebraic.
5. **Gauge escape.**  `exp(Q)` is differentially algebraic for every polynomial `Q`, with no degree
   bound.  Multiplication cannot leave the differential-algebraic field.
6. **Canonical-system escape.**  A de Branges function not represented by a finite-dimensional
   isomonodromic tau-function is not excluded.  This is the positive survivor, not a loophole in the
   killing theorem.

## Paper proof

Write `u = tau`, `u_j = d^j u/dt^j`, and

`A = u*u_1 + t*u*u_2 - t*u_1^2`,

`B = 2*u*(u*u_2-u_1^2) + t*(u^2*u_3-3*u*u_1*u_2+2*u_1^3)`.

On any open set where `u` is nonzero,

`sigma' = A/u^2`,

`sigma - t*sigma' = t^2*(u_1^2-u*u_2)/u^2`,

`t*sigma'' = t*B/u^3`.

Substitution in the sigma equation and multiplication by `u^6` gives

`t^2*B^2 = t^2*(2*A-(theta0+thetaInf)*u^2)^2*(u_1^2-u*u_2)
  + 4*A*(A-theta0*u^2)*(A-thetaInf*u^2)`.

This is an algebraic differential equation with polynomial coefficients.  It is nonzero: coefficient
of `u_3^2` on left is `t^4*u^4`, while right side contains no `u_3`.  Both sides are analytic after
denominator clearing, so identity extends across zeros of `u`.  Hence every fixed-monodromy PIII
tau-function is differentially algebraic over `C(t)`.

Let `g(s)=s(1-s)` and `y(s)=u(g(s))`.  On `s != 1/2`, chain rule expresses each
`u^(k)(g(s))` triangularly as a rational expression in `s,y,...,y^(k)`, with top coefficient
`(g'(s))^(-k)=(1-2s)^(-k)`.  Substitute these expressions into a nonzero differential equation for
`u` and clear powers of `1-2s`.  Nonconstancy of `g` and triangularity preserve nonzeroness.
Analytic continuation crosses `s=1/2`; therefore `y` is differentially algebraic over `C(s)`.

For every `Q in C[s]`, `exp(Q(s))` satisfies the first-order algebraic differential equation
`v' - Q'v = 0`.  Differentially algebraic meromorphic functions form a differential field, so
`F(s)=exp(Q(s))*y(s)` is differentially algebraic.  If an entire continuation of `F` equalled
completed `xi`, then `xi` would be differentially algebraic.  This contradicts the unconditional,
dependency-closed theorem `RHTower.xi_hypertranscendental`.  Thus no polynomial gauge and no fixed
monodromy pair realizes the proposed bridge.  QED.

## No-go closure

- **Exact killing theorem/mechanism:** finite-dimensional PIII\(_{D_6}\) tau-functions are
  differentially algebraic; `xi` is hypertranscendental; algebraic pullback and polynomial
  exponential gauge preserve differential algebraicity.
- **Strongest positive survivor:** polynomial-exponential gauge class of `xi` is entirely
  hypertranscendental.  Any successful irregular microlocal RH realization must therefore escape
  finite-dimensional isomonodromy--for example through a genuinely arithmetic ind/pro-holonomic
  object or a non-differentially-algebraic canonical system.
- **New insight:** missing arithmetic input cannot be encoded by choosing one point of the finite
  PIII wild character variety.  It must enlarge representation class, not merely select monodromy.
- **Status:** **[PROVED HERE] [FORMALIZED]** in
  `GaloisForLFunctions.RHTower.XiPainleveTauGaugeNoGo`; targeted direct Lean and module build pass.
  Both new public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-24 — created in `1-in-progress`; internal corpus and primary-literature audits complete.
- 2026-08-24 — hostile audit closed; paper proof promoted to `2-fully-proven`.
- 2026-08-24 — exact survivor and closed bridge exclusion formalized; promoted to `3-formalized`.
