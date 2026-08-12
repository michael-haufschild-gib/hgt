# Mass-shifted complex Gaussian translation

- **ID:** `mass-shifted-complex-gaussian-translation`
- **Stage:** 2-fully-proven
- **Route:** U, C43-Y / PDH.9
- **Scientific status:** `[PAPER PROVEN] [UNCONDITIONAL] [LEAN PENDING] [NOVELTY UNVERIFIED]`
- **Depends on:** `mass-shifted-hermite-derivative-energy`

## Frozen theorem CGT.1

For `P ∈ ℝ[X]`, `z ∈ ℂ`, and `d = natDegree(P)`, set

\[
 (T_zP)(x)=\sum_{k=0}^{d}\frac{z^k}{k!}P^{(k)}(x)e^{-\pi x^2},
 \qquad x\in\mathbb R.
\]

Then, without a nonvanishing or degree hypothesis,

\[
 \boxed{
 T_zP(x)=P_{\mathbb C}(x+z)e^{-\pi x^2},\qquad
 \|T_zP\|_2
 \le e^{|z|\sqrt{4\pi d}}\|Pe^{-\pi x^2}\|_2.}
 \tag{CGT.1}
\]

The zero polynomial and constant polynomials are included. The first equality makes this a literal
complex translation theorem, not a proxy operator bound.

## Proof

Write `D` for polynomial differentiation and

\[
 A=\sqrt{4\pi d}.
\]

The closed Hermite derivative-energy theorem gives, for every real polynomial `R`,

\[
 \|R'e^{-\pi x^2}\|_2^2
 \le 4\pi\,\deg(R)\|Re^{-\pi x^2}\|_2^2.
\]

Apply this to `R=D^kP`. Since `deg(D^kP)≤d`, nonnegativity and square-root monotonicity give

\[
 \|D^{k+1}Pe^{-\pi x^2}\|_2
 \le A\|D^kPe^{-\pi x^2}\|_2.
\]

Induction therefore proves the coefficient-free iterated estimate

\[
 \|D^kPe^{-\pi x^2}\|_2\le A^k\|Pe^{-\pi x^2}\|_2
 \qquad(k\ge0).                                           \tag{CGT.2}
\]

Polynomial Taylor expansion is finite because `D^kP=0` for `k>d`:

\[
 P_{\mathbb C}(x+z)=\sum_{k=0}^{d}\frac{z^k}{k!}D^kP(x).
 \tag{CGT.3}
\]

Multiplication by the real Gaussian proves the pointwise identity in CGT.1. The Hilbert-space
triangle inequality and CGT.2 give

\[
 \begin{aligned}
 \|T_zP\|_2
 &\le \sum_{k=0}^{d}\frac{|z|^k}{k!}
       \|D^kPe^{-\pi x^2}\|_2\\
 &\le \left(\sum_{k=0}^{d}\frac{(|z|A)^k}{k!}\right)
       \|Pe^{-\pi x^2}\|_2\\
 &\le e^{|z|A}\|Pe^{-\pi x^2}\|_2.
 \end{aligned}
\]

This proves CGT.1.

## C43-Y normalization

For the weight `e^{-y²}dy`, substitute `y=√(2π)x`. If `Q` has degree at most `N`, CGT.1 becomes

\[
 \|Q(\cdot-iu)\|_{L^2(e^{-y^2}dy)}
 \le e^{|u|\sqrt{2N}}
       \|Q\|_{L^2(e^{-y^2}dy)}.                           \tag{CGT.4}
\]

Taking `N=2d` and `u=ω/2`, then squaring, yields the exact translation factor
`exp(2√d |ω|)` used in (24.137). Thus the square-root degree scale and parabolic boundary
`t d ≍ 1` are preserved; replacing it by a linear degree estimate would not suffice.

## Hostile audit

- Monomial coefficient bounds fail coefficient-uniformly and lose the square-root degree scale.
- The derivative theorem alone is insufficient: CGT.2, factorial summation, and literal Taylor
  evaluation are all required.
- No contour shift or Fourier identity is smuggled into CGT.1. Those remain separate consumers.
- Real translation is not enough; completed-square contour displacement is imaginary. CGT.1 is
  proved for every complex `z`.
- Infinite Hermite completeness is not used. Degree truncation is what produces `√d`.

## Novelty audit

Classical Gaussian Bernstein--Markov theory contains the sharp derivative norm `√(2N)` in the
`e^{-y²}` normalization. Li--Geng--Ling--Wang (arXiv:2411.16359) explicitly treats exact weighted
`L²` Bernstein--Markov factors and identifies classical Hermite extremizers. The finite exponential
translation consequence is elementary operator theory. No external source located in this audit
states its completed-Xi prime-aperture use, normalization match, or the resulting universal
degree--time horizon. Priority is therefore claimed only for the corpus synthesis, not for the
standalone inequality.

## Remaining Route U boundary

CGT.1 closes the coefficient-uniform complex-translation component. C43-Y still needs literal Lean
proofs of completed-square contour translation, Fourier normalization, prime-shell summation,
Mehler/projector concentration, and completed-source Gamma/polar assembly.
