# Mass-shifted Gamma radial aperture envelope

- **ID:** `mass-shifted-gamma-radial-aperture-envelope`
- **Stage:** 3-formalized
- **Route:** U, C43-Y `(24.136)` / PDH.6
- **Scientific status:** `[BRIDGE] [FORMALIZED] [UNCONDITIONAL]`
- **Depends on:** `mass-shifted-polynomial-gaussian-local-concentration`;
  `HardyZPhaseAsymptotic`

## Exact frozen theorem GRAE.1

Put `g(x)=gammaHardyPhaseRate(x)`. For every real polynomial `Q`, positive heat time `t`, and
nonnegative radius `R`, let

\[
 f_{Q,t}(x)=Q(x^2)^2e^{-t x^2},\qquad
 M_Q(t)=\int_{\mathbb R}f_{Q,t}(x)\,dx.
\]

Then

\[
 \boxed{
 \int_{\mathbb R} f_{Q,t}(x)g(x)\,dx
 \ge
 \left[g(R)-18R\bigl(g(R)-g(0)\bigr)
       \sqrt{t(\deg Q+1)}\right]M_Q(t).
 }
 \tag{GRAE.1}
\]

Heat positivity and radius nonnegativity must be encoded in subtypes in Lean. No nonzero-polynomial,
coefficient, RH, asymptotic, or source-sign premise is allowed.

## Failure-driven formation

1. `[REDISCOVERED]` **Eventually positive Gamma tail.** Continuity and
   `g(x)-(1/2)log(|x|/(2pi))->0` give some positive tail floor. This is already C43-Y's proof and
   discards the corpus's exact radial monotonicity.
2. `[BRIDGE]` **Canonical fixed cutoff above the unique positive zero.** This gives constants in
   `(24.136)`, but hides a stronger law: no cutoff choice is needed.
3. `[PAPER-PROVED]` **All-radius aperture envelope GRAE.1.** The killing observation becomes the
   design constraint: retain `R` and the literal values `g(R),g(0)`. The result simultaneously
   contains global minimum control (`R=0`), every compact split, and the positive-tail wedge.

## Paper proof

The corpus proves that `g` is even and strictly increasing on `[0,infinity)`. Hence

\[
 g(0)\le g(x)\quad(x\in\mathbb R),
 \qquad
 g(R)\le g(x)\quad(|x|\ge R).
\]

Write `L_R=integral_[-R,R] f`. Splitting the integral into the compact interval and its complement,
and using `f>=0`, gives the exact two-zone estimate

\[
 \int f g
 \ge g(0)L_R+g(R)(M-L_R)
 =g(R)M-(g(R)-g(0))L_R.                    \tag{GRAE.2}
\]

Radial monotonicity also gives `g(R)-g(0)>=0`. The already formalized native Route-U concentration
theorem gives

\[
 L_R\le18R\sqrt{t(\deg Q+1)}M.
\]

Multiplying by the nonnegative phase difference and substituting in `(GRAE.2)` proves GRAE.1.
Polynomial--Gaussian decay and the corpus theorem that multiplying a Schwartz function by the
temperate Gamma phase rate remains Schwartz give all integrability statements.

## Hostile audit

- `Q=0`: both sides vanish; no mass division occurs.
- `R=0`: GRAE.1 reduces to the sharp global-minimum bound `integral f g >= g(0)M`.
- `g(R)<0`: theorem remains valid; tail positivity is not smuggled into its statement.
- Large `R`: penalty may become weak but never invalidates the estimate.
- The theorem controls only the Gamma face. It does not assume the completed explicit formula or
  prime-tail sign and therefore is not an RH surrogate.

## External parent audit

- Rodgers--Tao's de Bruijn--Newman work studies zero dynamics under a different heat deformation;
  it does not provide this polynomial-filtered explicit-formula inequality:
  <https://arxiv.org/abs/1801.05914>.
- Connes's heat expansion assumes RH to form a self-adjoint zero operator and obtains heat
  asymptotics, not unconditional filtered Gamma coercivity: <https://arxiv.org/abs/2402.13082>.
- Connes--Consani formulate semilocal Weil-positivity operator problems but do not state the exact
  all-radius polynomial--Gaussian envelope: <https://arxiv.org/abs/1910.14368>.

No standalone novelty is claimed: GRAE.1 is a new exact Route-U composition of corpus results, not
an identified new parent-theory theorem.

## Downstream consequence

Choosing any radius beyond the corpus's unique positive zero of `g` yields universal positive
`c_0` and finite `C_0`, hence C43-Y `(24.136)` exactly. Keeping `R` free exposes a variational
aperture profile that can later be optimized when the prime face is assembled.

## Lean closure

Formalized in
`formal/GaloisForLFunctions/RHTower/PolynomialGaussianGammaRadialEnvelope.lean` as
`RHTower.integral_norm_routeUPolynomialGaussianDensity_mul_gammaHardyPhaseRate_ge`.

The implementation does not rely on the convention that an undefined integral is zero. It builds
the native density as a scaled pointwise product of Schwartz functions, proves both unweighted and
Gamma-weighted integrability, proves the two radial sign inequalities from exact evenness and
strict monotonicity, splits the line into `[-R,R]` and its complement, then imports the already
formalized local-concentration theorem.

Audit on 2026-08-13:

- `lake env lean GaloisForLFunctions/RHTower/PolynomialGaussianGammaRadialEnvelope.lean`: pass;
- umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`;
- `lake build GaloisForLFunctions.RHTower.PolynomialGaussianGammaRadialEnvelope`: pass
  (`9218/9218`);
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-token scan and `scripts/formal_tools.py lint`: pass.
