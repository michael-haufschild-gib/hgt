# Mass-shifted polynomial--Gaussian prime tail

- **ID:** `mass-shifted-polynomial-gaussian-prime-tail`
- **Stage:** 3-formalized
- **Route:** U, C43-Y `(24.138)` / PDH.6
- **Scientific status:** `[BRIDGE] [STRENGTHENED] [FORMALIZED] [UNCONDITIONAL]`
- **Depends on:** `mass-shifted-polynomial-gaussian-fourier-aperture`

## Exact frozen theorem PGPT.1

For a real polynomial `Q`, encode positive heat time and the parabolic aperture condition by

\[
 t\in\mathsf W_Q
 \quad\Longleftrightarrow\quad
 t>0,\qquad
 t(\deg Q+1)\le \frac{(\log 2)^2}{256}.
\]

Put

\[
 \mathcal P_{Q,t}
 =\sum_{n\ge0}\frac{\Lambda(n)}{\sqrt n}
   \left|\widehat F_{Q,t}(\log n)\right|,
 \qquad
 C_\Lambda=\sum_{n\ge0}\Lambda(n)n^{-2}.
\]

The `n=0,1` terms are zero. Then

\[
 \boxed{
 \mathcal P_{Q,t}
 \le C_\Lambda M_Q(t)
 \exp\!\left(-\frac{(\log 2)^2}{16t}\right).
 }
 \tag{PGPT.1}
\]

The Lean statement must take `t : routeUPrimeGaussianWedge Q`; it may not expose an analytic or
summability premise. It must also prove summability of the literal nonnegative series.

## Conjecture--failure--pivot loop

1. `[REDISCOVERED]` Shell counting with `Lambda(n)<=log n` reproduces the paper proof but demands a
   separate Gaussian shell-sum library and hides the exact arithmetic constant.
2. `[FAILED AS DESIGN]` Bound the residual Gaussian by `n^-1`. This is sufficient, but lands at
   the less convenient half-density mass `sum Lambda(n)n^-3/2`.
3. `[STRENGTHENED]` Spend the same wedge reserve twice. The residual Gaussian is at most `n^-2`,
   landing directly on the corpus's absolutely convergent right-half-plane von-Mangoldt mass
   `C_Lambda`. This removes shell counting and yields an exact constant.

## Paper proof

The formal Fourier aperture already gives, for `xi>=log 2`,

\[
 \frac{|\widehat F_{Q,t}(\xi)|}{M_Q(t)}
 \le \exp\!\left(-\frac{\xi^2}{4t}
       +2\sqrt{\deg Q}\frac{\xi}{\sqrt t}\right).
\]

The wedge implies

\[
 16\sqrt{t\deg Q}\le\log 2\le\xi,
\]

so the translation term consumes at most half the Gaussian exponent:

\[
 |\widehat F_{Q,t}(\xi)|
 \le M_Q(t)e^{-\xi^2/(8t)}.                       \tag{PGPT.2}
\]

The same wedge also implies `32t<=log 2`. For `xi>=log 2`, monotonicity after squaring gives

\[
 \frac{\xi^2}{16t}\ge\frac{(\log2)^2}{16t},
 \qquad
 \frac{\xi^2}{16t}\ge2\xi.
\]

Therefore

\[
 e^{-\xi^2/(8t)}
 \le e^{-(\log2)^2/(16t)}e^{-2\xi}.              \tag{PGPT.3}
\]

At `xi=log n`, the last factor is `n^-2`. Since `n>=2` also gives `sqrt n>=1`,

\[
 \frac{\Lambda(n)}{\sqrt n}|\widehat F_{Q,t}(\log n)|
 \le M_Q(t)e^{-(\log2)^2/(16t)}\Lambda(n)n^{-2}.
\]

The corpus theorem `summable_vonMangoldt_rpow` at exponent `2` supplies absolute summability;
termwise summation proves PGPT.1.

## Hostile audit

- `Q=0`: mass and every Fourier term vanish; no division by mass occurs.
- `n=0,1`: von Mangoldt weights vanish, so `log 0` and `sqrt 0` do not create a hidden term.
- Endpoint wedge equality is allowed throughout.
- Only unconditional absolute convergence for the von-Mangoldt Dirichlet series at `s=2` enters;
  no PNT, zero-free region, RH, or finite computation enters.
- PGPT.1 controls the absolute prime face. It does not assert the completed explicit formula or
  positivity of the completed trace.

## External audit

Targeted primary-source searches found standard Riemann--von Mangoldt explicit-formula error work
and unrelated Gaussian heat kernels, but no exact coefficient-uniform polynomial--Gaussian
inequality with the parabolic wedge and `C_Lambda` constant. No standalone novelty is claimed:
PGPT.1 is an exact Route-U strengthening and a bridge to the completed wedge.

## Big-picture interpretation

Small-ball Gamma control and large-frequency prime control are the same oscillator aperture
transition. The wedge does more than make the Fourier exponent negative: it converts log-Gaussian
decay into a fixed right-half-plane Dirichlet mass. The apparent need for integer shell counting
was a shadow of this exponent-extraction principle.

## Lean closure

Formalized in `formal/GaloisForLFunctions/RHTower/PolynomialGaussianPrimeTail.lean`.

Principal declarations:

- `RHTower.routeUPrimeGaussianWedge` encodes positive heat and exact closed wedge;
- `RHTower.norm_routeUPolynomialGaussianFourier_le_wedge` proves `(PGPT.2)`;
- `RHTower.summable_routeUPolynomialGaussianPrimeAbsoluteTail` proves absolute summability of the
  literal source;
- `RHTower.routeUPolynomialGaussianPrimeAbsoluteTail_le` proves `(PGPT.1)` / `(24.138)`.

Audit on 2026-08-13:

- direct `lake env lean` check: pass;
- umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`;
- final `lake build GaloisForLFunctions.RHTower.PolynomialGaussianPrimeTail`: pass
  (`8835/8835`);
- both exported summability and tail theorems have axioms only `propext`, `Classical.choice`, and
  `Quot.sound`;
- forbidden-token scan and `scripts/formal_tools.py lint`: pass.
