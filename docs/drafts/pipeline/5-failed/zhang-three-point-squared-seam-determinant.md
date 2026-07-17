# Zhang-Mechanism Three-Point Squared-Seam Determinant

- **ID:** `zhang-three-point-squared-seam-determinant`
- **Stage:** 5-failed
- **Type:** FAILED ROUTE / finite unconditional RH-disproof candidate
- **Scientific status:** `[REFUTED] [DETERMINANT STRICTLY POSITIVE] [NO RH CONSEQUENCE]`
- **Source:** Ruiming Zhang, *Complete Monotonicity of Special Functions*;
  `../2-fully-proven/needs-audit/squared-xi-logderivative-three-point-orbit-positivity.md`
- **Statement:** The proposed negative determinant at the points `1,2,3` cannot occur. The matrix

  `[[g(0),g(1),g(4)],[g(1),g(0),g(1)],[g(4),g(1),g(0)]]`

  is positive definite unconditionally.

## Candidate

Let

`g(y)=xi'(1/2+sqrt(y))/(2*sqrt(y)*xi(1/2+sqrt(y)))`

with its removable value at zero. Under RH, Zhang's complete-monotonicity theorem makes
`g((u-v)^2)` a positive-definite kernel. A negative determinant at a finite point set would
therefore disprove RH.

The candidate point set was `1,2,3`, giving squared differences `0,1,4`. The current Zhang paper
does not state this determinant and does not report a negative value for it; the point set was an
in-project conjectural discriminator.

## Exact Refutation

Riemann's theta integral proves without numerical zero data that every Xi zero
`rho=sigma+i*gamma` has `|gamma|>3/2`. Put

`delta=sigma-1/2`, `t=gamma^2-delta^2`, `q=4*delta^2*gamma^2`.

The critical strip then gives

`t>2`, `0<=q<=t+1/4`.

After passing to the genus-zero squared variable, every off-line conjugate root pair contributes a
positive multiple of

`H_(t,q)(y)=(t+y)/((t+y)^2+q)`

to `g(y)`; an on-line root is the case `q=0`. For the values `y=0,1,4`, the matrix

`[[H(0),H(1),H(4)],[H(1),H(0),H(1)],[H(4),H(1),H(0)]]`

is positive definite throughout `t>2`, `0<=q<=t+1/4`. The proof is exact polynomial algebra and
is recorded in the cited stage-2 theorem. The logarithmic-derivative matrix is an absolutely
convergent positive sum of these orbit matrices, and is therefore itself positive definite.

Consequently

`det [[g(0),g(1),g(4)],[g(1),g(0),g(1)],[g(4),g(1),g(0)]] > 0`.

## Positive Residue

The orbit calculation gives a protected low-diameter chamber for squared-seam tests. Any finite
kernel disproof must use a point geometry outside this chamber or a higher-order packet whose sign
is not protected by the strip and the elementary low-height zero-free bound.

## Anti-Theatre Gate

- The conditional Zhang mechanism is valid, but it supplies no negative source sign.
- The nonexistent external decimal is removed from the provenance.
- The exact conjectured sign was attacked and reversed before any Lean capstone was built.
- No numerical zero table or floating-point evaluation was used.

## Gates

- [x] Conditional finite-kernel disproof endpoint identified.
- [x] Exact source coordinates derived.
- [x] Primary-source provenance corrected.
- [x] Low-height zero-free rectangle proved analytically.
- [x] Per-orbit matrix positivity proved by exact algebra.
- [x] Canonical-product sum shown positive definite.
- [x] Candidate retired; do not formalize a false negative-sign capstone.

## Log

- 2026-07-17 -- Opened as an exact finite discriminator for Zhang's conditional mechanism.
- 2026-07-17 -- Source audit showed that the point triple and alleged decimal were not in the
  cited paper.
- 2026-07-17 -- Proved the determinant strictly positive unconditionally and retired the route.
