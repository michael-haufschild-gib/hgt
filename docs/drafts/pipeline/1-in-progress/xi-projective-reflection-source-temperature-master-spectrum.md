# Xi projective reflection source--temperature master spectrum

- **ID:** xi-projective-reflection-source-temperature-master-spectrum
- **Status:** `[CONJECTURE]` in development; exact pointwise identities derived, formal proof pending.
- **Route:** Connes / fixed-window Guinand--Weil / endpoint reflection.

## Master invariant

For a multiplicity copy `q` of a nontrivial Xi zero `rho`, put

\[
r_q=\rho^{-1},\qquad q^\dagger=1-\overline\rho,
\]

and define the projective reflection displacement

\[
\mathfrak p(q)
 =\frac{|r_q-r_{q^\dagger}|}
 {2|r_q|\,|r_{q^\dagger}|}.
\]

The proposed master theorem is the exact identity

\[
\mathfrak p(q)
 =\left|\Re\rho-\frac12\right|
 =\frac14\left|\beta_B(\rho)-\beta_B(\rho^\dagger)\right|,
\qquad \beta_B(s)=2\Re s.
\]

Consequently the right-transverse radius

\[
\mathfrak R=\sup_{\Re\rho>1/2}\mathfrak p(\rho)
\]

is simultaneously:

1. the exact horizontal support radius of the Xi divisor;
2. one quarter of the maximal reflected Born-temperature mismatch;
3. the shift of the fixed-window prime--Gamma negative-source Dirichlet abscissa under false RH:
   \(\sigma_{\rm abs}=1+\mathfrak R\);
4. the uniform control parameter for the endpoint reflection energy.

For `0 <= alpha <= 1/2`, the intended quantitative endpoint bridge is

\[
\mathfrak R\le\alpha
\quad\Longrightarrow\quad
E\le
\frac{4\alpha^2 C}
{C^{-1}-\frac34-\alpha^2},
\qquad
C=2+\gamma-\log(4\pi).
\]

This is a genuine coupling theorem: the fixed-window source controls the projective `L-infinity`
reflection displacement, while the endpoint law is its completed weighted `L^2` shadow. The
quadratic estimate tends to zero with the source abscissa shift.

## Proof obligations

- [ ] Prove the pointwise reciprocal projective identity.
- [ ] Prove the Born-temperature identity.
- [ ] Reuse the exact fixed-window abscissa theorem to identify `1 + R`.
- [ ] Prove the pointwise endpoint-energy bound from `R <= alpha` and the completed source height
  gap, then sum it.
- [ ] Package the single master spectrum theorem.
- [ ] Run the formal lint and axiom gates.
- [ ] Only after completion, replace the manuscript's two-layer headline theorem.

## Honesty gate

- `[CONJECTURE]` until all displayed implications are proved unconditionally.
- `[NOVELTY UNVERIFIED]`: no novelty claim is made at this stage.
- The theorem does not prove RH. It identifies one exact defect across source, reflection,
  thermodynamic, and endpoint-energy charts and turns every source half-plane improvement into a
  quantitative endpoint improvement.
