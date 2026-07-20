# Diagonal-normalized Xi aperture relative-Krein contraction

- **ID:** xi-normalized-aperture-relative-krein-contraction
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `ThetaCuspFourierLaplace.lean`; `HedenmalmHankelKreinChamber.lean`;
  `XiNormalizedApertureRelativeKrein.lean`
- **Statement:** The unit-diagonal theta/Xi autocorrelation contracts in the aperture Hilbert
  metric; equivalently its denominator-free relative Krein curvature is nonnegative.

## Goal

For `0 <= a < b < 1` and `t : R`, put

```text
M(a,t)=|xi(1/2+a+i t)|^2,
C_a(t)=M(a,t)/M(a,0),
d_a(t)^2=2(1-C_a(t)),
N(a,t)=partial_a M(a,t) M(a,0)-M(a,t) partial_a M(a,0).
```

The conjecture is

```text
C_a(t) <= C_b(t),
equivalently d_b(t)^2 <= d_a(t)^2,
equivalently N(a,t) >= 0 on 0<a<1/2.                   (DNAC)
```

The object is source-pure.  `C_a` is the squared characteristic function of the actual
exponentially tilted positive theta-cusp source, divided by its exact diagonal mass.  It is an
infinite source correlation evaluated at the literal height `t`; no source/zero packet matching,
finite frame, target-selected coefficient, or source-span closure occurs.

If `(DNAC)` holds and an off-critical zero has positive transverse displacement `b`, then at its
height `t` one has `C_b(t)=0`.  Nonnegativity and aperture monotonicity force `C_a(t)=0` for every
`0<=a<=b`.  The resulting horizontal interval of Xi zeros contradicts analyticity and
nontriviality.  Reflection handles the negative displacement.  Thus `(DNAC)` is a producer-shaped
RH conjecture, not an implication whose premise names the zero divisor.

## Gates

- [x] 0 -> 1 in-progress: the object is canonical and source-pure; exact Lean definition,
  derivative, range, determinant laws, and hostile factor audit exist
- [ ] 1 -> 2 fully-proven: prove `(DNAC)` from the positive theta source, or falsify it and close
  the no-go with its strongest positive survivor
- [ ] 2 -> 3 formalized: formalize the source proof and the analytic zero-exclusion consequence;
  run the final module audit and `#print axioms`
- [ ] 3 -> 4 publication-ready: standalone proof, exact external novelty audit, Lean certificate

## Anti-theatre audit

1. **Known unnormalized parent removed.**  Sondow--Dumitrescu prove horizontal monotonicity of
   `|xi(1/2+a+i t)|` in a zero-free half-plane.  Their derivative is `partial_a M(a,t)`.  `(DNAC)`
   asks for

   ```text
   partial_a M(a,t) M(a,0)-M(a,t) partial_a M(a,0) >= 0,
   ```

   so the entire known scalar growth channel is subtracted.  Kobayashi's Hadamard/autocorrelation
   discussion has the same unnormalized parent.  Neither source found states the normalized
   comparison.
2. **Generic probability theory does not answer it.**  Exponential/Esscher tilting explains the
   family `C_a`, but characteristic-function modulus is not generically monotone under a natural
   exponential-family parameter.  The proposed sign is a special theta-source theorem.
3. **Positive-semidefinite theatre is impossible.**  `C_a-C_b` has zero diagonal.  Lean proves its
   two-point determinant is the negative square of the off-diagonal refinement.  A nonzero
   refinement is necessarily indefinite, exactly as demanded by the aperture response signature.
4. **Factorwise Hadamard theatre is impossible.**  For one on-line zero pair of ordinate `gamma`,
   the normalized factor is

   ```text
   F_gamma(a,t)=((gamma^2+a^2-t^2)^2+4a^2t^2)/(gamma^2+a^2)^2,
   partial_a F_gamma
     =4 a t^2(3gamma^2-a^2-t^2)/(gamma^2+a^2)^3.        (H1)
   ```

   Lean proves the sharp sign trichotomy.  The factor is increasing precisely inside
   `a^2+t^2<3gamma^2`, stationary on the circle, and decreasing outside.  Therefore `(DNAC)`, if
   true, is a collective infinite-source cancellation theorem and cannot be obtained by declaring
   every zero factor positive.
5. **No hidden coupling.**  Unlike the retired CAVC wording, every variable in `(DNAC)` belongs to
   one canonical theta/Xi orbit.  There is no undefined word such as "matched" between a prime
   packet and a zero packet.
6. **Direct falsifier.**  One exact triple `(a,b,t)` with `0<=a<b<1` and `C_b(t)<C_a(t)` kills the
   conjecture.  No numerical evidence is being used as proof or as a substitute for the source
   analysis.

External parent audit:

- Jonathan Sondow and Cristian Dumitrescu, *A monotonicity property of Riemann's xi function and a
  reformulation of the Riemann Hypothesis*, <https://arxiv.org/abs/1005.1104>.
- Hisashi Kobayashi, *Some results on the xi and Xi functions associated with Riemann's zeta
  function*, <https://arxiv.org/abs/1603.02954>.

Exact-formula and concept searches for the diagonal-normalized ratio, the relative numerator, and
Esscher-tilt characteristic-modulus monotonicity produced no collision.  This is search
noncollision, not a priority claim.

## Approach

Let

```text
p_a(x)=exp(-a x) Phi(x)/Z_a
```

be the actual positive theta-cusp probability density.  Then

```text
C_a(t)=|E_a exp(-i t X)|^2
      =E_a cos(t(X-Y))                                  (P1)
```

for independent `X,Y~p_a`.  Differentiating the normalized law gives the exact source form

```text
partial_a C_a(t)
 =-E_a[(X+Y-2 E_a X) cos(t(X-Y))].                      (P2)
```

The research problem is to prove the sign of `(P2)` from the special theta density.  In
center/difference coordinates `m=(X+Y)/2`, `d=X-Y`, the tilt depends only on `m`, while height
appears only through `cos(t d)`.  This is the source-derived separation absent from raw Xi
log-derivative criteria.  The next paper step is to derive a nonnegative integral decomposition of
`(P2)` using the theta reflection/Ward identities, or to identify the first exact sign-changing
source term and close the no-go.

The small-height necessary condition is aperture decay of the tilted variance:

```text
partial_a Var_a(X) <= 0,
```

equivalently a signed third-cumulant inequality for the tilted theta source.  This is a hostile
local gate, not sufficient for `(DNAC)`; it should be attacked before any global proof attempt.

## Unconditional formalized mathematics

Permanent module:
`formal/GaloisForLFunctions/RHTower/XiNormalizedApertureRelativeKrein.lean`.

It proves:

- the exact theta-source Fourier bound and `0<=C_a(t)<=1` for `|a|<1`;
- `d_a(t)^2 in [0,2]`, `d_a(0)^2=0`, and the exact correlation/contraction equivalence;
- the denominator never vanishes, using the source-pure Xi height gap;
- evenness and the exact zero correspondence;
- `partial_a C_a(t)=N(a,t)/M(a,0)^2`;
- zero diagonal, negative-square two-point determinant, and cubic three-point determinant for the
  aperture refinement;
- the sharp factor derivative and sign trichotomy `(H1)`.

The module contains no conjectural declaration or assumed sign.

## No-go closure if `(DNAC)` fails

- **Exact killing theorem/mechanism:** record an analytic source term or exact aperture/height
  region where `N(a,t)<0`; a floating-point sample is not closure.
- **Strongest current positive survivor:** the true unit-diagonal theta/Xi Hilbert correlation,
  exact relative-Krein derivative, indefinite refinement determinants, and sharp one-factor cone
  `(H1)` are already unconditional and formalized.
- **New insight:** normalization creates the required response signature but destroys factorwise
  horizontal monotonicity.  Any replacement must be height-adaptive or exploit collective theta
  cancellation; returning to unnormalized modulus growth is not a pivot.
- **Status:** conjecture open; unconditional survivor checked by direct Lean leaf compilation.

## Log

- 2026-07-20 — conjectured after retiring the ill-typed matched-packet CAVC; exact source object,
  relative curvature, true correlation range, determinant signature, and hostile factor cone
  formalized in Lean; external parent search found no normalized collision.
