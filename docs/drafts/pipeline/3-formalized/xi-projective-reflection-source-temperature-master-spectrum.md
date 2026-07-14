# Xi projective reflection source--temperature master spectrum

- **ID:** xi-projective-reflection-source-temperature-master-spectrum
- **Status:** `[PROVED]` unconditionally and formalized.
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

The master theorem begins with the exact identity

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

For `0 <= alpha <= 1/2`, the quantitative endpoint bridge is

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

Define

\[
B_C(\alpha)=\frac{4\alpha^2 C}{C^{-1}-\frac34-\alpha^2}.
\]

Then `B_C` is strictly increasing on `[0,1/2]` and

\[
B_C(0)=0,
\qquad
B_C(1/2)=\frac{C^2}{1-C}.
\]

Thus one theorem interpolates from the RH zero-defect endpoint to the previously established
unconditional full-strip endpoint budget. For every admissible fixed window and cutoff and every
`0 <= alpha <= 1/2`, the following are equivalent:

\[
\sigma_{\rm abs}(S^-_{L,N})\le 1+\alpha,
\qquad
\mathfrak R\le\alpha,
\qquad
\mathfrak R_B\le\alpha,
\qquad
\Re\rho\le\frac12+\alpha\quad(\xi(\rho)=0),
\]

and any of them implies `E <= B_C(alpha)`.

The intrinsic form eliminates the auxiliary half-plane parameter:

\[
0\le\mathfrak R\le\frac12,
\qquad
E\le B_C(\mathfrak R).
\]

## Proof obligations

- [x] Prove the pointwise reciprocal projective identity.
- [x] Prove the Born-temperature identity.
- [x] Reuse the exact fixed-window abscissa theorem to identify `1 + R`.
- [x] Prove the pointwise endpoint-energy bound from `R <= alpha` and the completed source height
  gap, then sum it.
- [x] Package the single master spectrum theorem.
- [x] Prove the strict budget interpolation and its two endpoint values.
- [x] Prove the intrinsic completed-energy bound `E <= B_C(R)`.
- [x] Run the narrow compilation and formal lint gate.
- [x] Audit the theorem surface for forbidden proof debt and print the axioms of the master,
  interpolation, pointwise, and zero-fiber theorems; only `propext`, `Classical.choice`, and
  `Quot.sound` remain.
- [x] Replace the manuscript's two-layer headline theorem by the source--temperature master
  spectrum and its Born--Witten--KMS quantitative endpoint.

## Honesty gate

- `[NOVELTY UNVERIFIED]`: no novelty claim is made at this stage.
- The theorem does not prove RH. It identifies one exact defect across source, reflection,
  thermodynamic, and endpoint-energy charts and turns every source half-plane improvement into a
  quantitative endpoint improvement.

## Formal artifact

`formal/GaloisForLFunctions/RHTower/XiProjectiveReflectionSourceTemperatureSpectrum.lean`

The principal declarations are:

- `xiEndpointProjectiveReflectionDisplacement_eq_abs`;
- `xiProjectiveReflectionRadius_eq_transverseSup`;
- `xiBornReflectionRadius_eq_projectiveReflectionRadius`;
- `primeGamma_abscissa_le_iff_projectiveReflectionRadius_le`;
- `xiEndpointDefectEnergy_le_of_projectiveReflectionRadius`;
- `xiEndpointDefectEnergy_le_intrinsicProjectiveBudget`;
- `xiProjectiveSourceTemperatureMasterSpectrum`;
- `xiProjectiveEndpointBudget_strictMonoOn`;
- `xiProjectiveBornEndpoint_zero_iff_rh`.
