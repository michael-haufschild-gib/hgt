# Mass-shifted completed prime--Gamma wedge

- **ID:** `mass-shifted-completed-prime-gamma-wedge`
- **Stage:** 3-formalized
- **Route:** U, C43-Y `(24.139)` / PDH.6
- **Scientific status:** `[BRIDGE] [STRENGTHENED] [FORMALIZED] [UNCONDITIONAL]`
- **Depends on:** `mass-shifted-gamma-radial-aperture-envelope`,
  `mass-shifted-polynomial-gaussian-prime-tail`

## Exact frozen theorem CPGW.1

Let `g` be the exact normalized Gamma Hardy-phase rate. Let `T_*` be its unique positive zero and
put

\[
 R_*:=T_*+1,\qquad g_*:=g(R_*),\qquad \Delta_*:=g(R_*)-g(0),
 \qquad C_\Lambda:=\sum_{n\ge0}\Lambda(n)n^{-2}.
\]

The corpus proves `g_*>0`, `Delta_*>0`, and `C_Lambda>=0`. Define three positive budgets

\[
 a_0=\frac{(\log 2)^2}{256},\qquad
 a_\Gamma=\left(\frac{g_*}{72R_*\Delta_*}\right)^2,
 \qquad
 a_p=\frac{g_*(\log 2)^2}{64(C_\Lambda+1)},
\]

and the canonical aperture

\[
 \eta_*:=\min\{a_0,a_\Gamma,a_p\}>0.
\]

For every real polynomial `Q` and every typed heat time

\[
 t>0,\qquad t(\deg Q+1)\le\eta_*,
\]

write `M_Q(t)` for native polynomial--Gaussian mass, `G_Q(t)` for its exact Gamma-rate integral,
and `P_Q(t)` for the complete absolute von-Mangoldt Fourier tail. Then

\[
 \boxed{
 \frac{g_*}{2}M_Q(t)\le G_Q(t)-P_Q(t).
 }
 \tag{CPGW.1}
\]

If `Q!=0`, then `M_Q(t)>0`, hence

\[
 \boxed{0<G_Q(t)-P_Q(t).}
 \tag{CPGW.2}
\]

The Lean statement encodes `Q!=0`, `t>0`, and the aperture in input subtypes. It exposes no
analytic premise, coefficient premise, cutoff premise, axiom, or RH hypothesis.

## Conjecture--failure--pivot loop

1. `[FAILED AS DESIGN]` Ask only for existence of some small heat threshold. This would hide the
   interaction between the Gamma and prime constants and create an unusable downstream interface.
2. `[FAILED AS DESIGN]` Divide both estimates by `M_Q(t)`. This excludes `Q=0` prematurely and
   creates a nonzero-mass premise whose proof is unrelated to the quantitative comparison.
3. `[PIVOT]` Keep mass multiplicative and split the single parabolic scale into three explicit
   budgets. The zero polynomial remains covered by the quantitative theorem; strictness is a
   separate typed corollary for nonzero polynomials.
4. `[STRENGTHENED]` Linearize the exponentially small prime factor symbolically from
   `1+x<=exp(x)`. This replaces an existential exponential threshold by the exact budget `a_p` and
   uses no numerical computation.

## Paper proof

Strict monotonicity of `g` on the positive ray gives

\[
 g_*=g(T_*+1)>g(T_*)=0.
\]

Since `g(0)<0`, also `Delta_*>0`; all three budgets and `eta_*` are therefore strictly positive.

The exact Gamma radial envelope at radius `R_*` is

\[
 G_Q(t)\ge
 \left(g_*-18R_*\Delta_*\sqrt{t(\deg Q+1)}\right)M_Q(t).
\]

The inequality `t(deg Q+1)<=a_Gamma` gives

\[
 18R_*\Delta_*\sqrt{t(\deg Q+1)}\le g_*/4,
\]

so `G_Q(t)>=(3g_*/4)M_Q(t)`.

The exact complete prime-tail theorem gives

\[
 P_Q(t)\le C_\Lambda M_Q(t)
 \exp\left(-\frac{(\log2)^2}{16t}\right).
\]

For `A,t>0`, `A/t<=1+A/t<=exp(A/t)` implies

\[
 e^{-A/t}\le t/A.
\]

Taking `A=(log 2)^2/16`, using `t<=t(deg Q+1)<=a_p`, and enlarging
`C_Lambda` to `C_Lambda+1` gives

\[
 C_\Lambda e^{-(\log2)^2/(16t)}
 \le \frac{16(C_\Lambda+1)t}{(\log2)^2}
 \le g_*/4.
\]

Thus `P_Q(t)<=(g_*/4)M_Q(t)`, and subtraction proves CPGW.1.

For `Q!=0`, the polynomial `Q(X^2)` is nonzero. It therefore has a real point where it is nonzero.
At that point the continuous nonnegative density
`|Q(x^2)^2 exp(-t x^2)|` is nonzero. Its support contains a nonempty open set of positive Lebesgue
measure, so its integrable total mass is strictly positive. Combining this with `g_*>0` and
CPGW.1 proves CPGW.2.

## Hostile audit

- `Q=0`: CPGW.1 remains meaningful and reduces to equality at zero; no division by mass occurs.
- `Q!=0`: strict mass positivity is proved from continuity and positive measure, not computation.
- All denominator factors are symbolically positive: `R_*>0`, `Delta_*>0`, `log 2>0`, and
  `C_Lambda+1>0`.
- Endpoint aperture equality is allowed.
- Prime control uses the literal complete absolutely summable tail from PGPT.1.
- CPGW.2 is Gamma minus the *absolute* prime tail. It is stronger than any signed prime-phase
  comparison, but it is not yet the completed explicit-formula identity or PDH global conclusion.

## Big-picture interpretation

Gamma leakage and arithmetic frequency suppression are two faces of one parabolic uncertainty
budget. The obstruction looked like an incompatibility between a spatial small-ball estimate and a
frequency tail estimate because each was assigned its own unspecified threshold. Their common
scale `t(deg Q+1)` exposes a universal finite-budget intersection. The exponential prime face does
not require transcendental threshold solving: convexity converts it to the same linear scale used
by the Gamma face.

## Lean closure

Formalized in
`formal/GaloisForLFunctions/RHTower/PolynomialGaussianCompletedPrimeGammaWedge.lean` and wired into
`formal/GaloisForLFunctions/RHTower.lean`.

Principal declarations:

- `RHTower.routeUPolynomialGaussianMass_pos` proves native mass is strictly positive for every
  typed nonzero polynomial;
- `RHTower.routeUCompletedPrimeGammaAperture_pos` proves the canonical three-budget aperture is
  strictly positive;
- `RHTower.routeUPolynomialGaussianCompletedPrimeGammaGap_ge` proves CPGW.1;
- `RHTower.routeUPolynomialGaussianCompletedPrimeGammaGap_pos` proves CPGW.2 / `(24.139)`.

Audit on 2026-08-13:

- direct `lake env lean` check: pass;
- named-module build: pass (`9229/9229`);
- all four principal theorems have axioms only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-token scan and `scripts/formal_tools.py lint`: pass.
