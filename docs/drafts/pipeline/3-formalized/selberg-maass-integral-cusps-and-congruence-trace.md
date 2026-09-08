# Actual integral cusp transport and finite congruence trace

- **ID:** SELBERG-MAASS-INTEGRAL-CUSPS-CONGRUENCE-TRACE
- **Stage:** 3-formalized; final module audits pending below.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 24.
- **Scope:** Actual C² Maass cusp eigenforms at every positive principal congruence level.

## Exact result

For an actual Maass cusp eigenform `f` at level `w=N+1`, every integral matrix `A` gives an actual eigenform `f_A(z)=f(A*z)` at the same level and eigenvalue. The source's C² regularity, eigen-equation, nonvanishing, congruence invariance, and decay at every integral cusp are all retained by proof. The inverse matrix gives an inverse equivalence. Matrices in the congruence subgroup act trivially.

For `0<lambda<1/4`, each `f_A` therefore has zero constant Fourier coefficient and the already-proved exact physical Bessel boundary decomposition, at every positive height. The period used is `w`; no minimal cusp-width assertion is made.

Let `Q=SL(2,Z)/Gamma(w)`, a finite group, and let `f_q` be the actual translated Maass form, independent of the representative of `q`. Define

`D(z)=sum_(q in Q) |f_q(z)|^2`.

This is a real C² density, nonnegative, positive somewhere, invariant under the full integral modular group, and uniformly zero at infinity. In particular, its horizontal slices have period one. For every `y>0`, let

`H(y)=integral_0^1 D(x+i*y) dx`.

The exact width normalization is

`H(y)=sum_q M_q(y)`,

where `M_q` is the existing width-normalized physical mass of `f_q`. Moreover,

`H'(y)=2*sum_q J_q(y)`,

`H''(y)=2*sum_q (G_q(y)-lambda*M_q(y)/y^2)`.

For every `Y=exp(T)>0` in the exceptional interval, `H(y)/y²` is integrable on the full tail. The actual unit-strip tail mass satisfies

`-sum_q J_q(Y)+(lambda-1/4)*integral_Y^infinity H(y)/y^2`

`= sum_q boundaryForm(log(w),T,actualTrace(f_q,T)) + sum_q sum_n actualSquareTail(f_q,T,n)`.

Every square contribution is nonnegative and its infinite Fourier series is already proved convergent for its actual Maass source. This yields the corresponding lower bound by the sum of the actual boundary forms.

The coset family is not asserted to enumerate distinct cusps once. The unit-strip normalization above is proved directly from period one of the finite trace. No global fundamental-domain measure decomposition or compact-core inequality is asserted. The full Selberg conjecture remains unproved.

## Corpus conjecture, proof, and pivot

The inspected `ThetaCuspHawkingBMModularLaplacian.chartLaplacian_modular_pullback` requires a C∞ wrapper, while its proof uses only C² at the image point and a holomorphic Möbius chart. This suggested the precise C² transport conjecture. The proof succeeds using its source `planarLaplacian_holomorphic_comp`, the actual Möbius derivative, and the height law, with the sign converted to the source Maass positive Laplacian.

Mathlib's actual `Gamma_normal` gives invariance under integral conjugation. It does not assert that the real congruence image is normal in the full real group; no such claim is needed or made. The actual translate then supplies every previous cusp theorem without adding a smoothness or automorphy hypothesis.

Fresh whole-corpus searches for truncated Stokes identities found `ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral.d4BM_actualFirstStokesPairedTruncatedBulk_eq_cuspTop`. That source cancels translation sides and paired inversion arcs for a concrete Eisenstein current. It cannot be substituted for a Maass current. The next conjecture was to construct the finite congruence trace as the actual modular scalar source for a corresponding Maass boundary calculation. This finite trace construction, its regularity, and its cusp normalization now succeed.

## Dependency-closed paper proof

1. The real second chain rule under a holomorphic Möbius map scales the planar Laplacian by the squared norm of its complex derivative. The exact height transformation cancels that factor in the hyperbolic Laplacian. C² of the original Maass field is sufficient. Composition also preserves C².
2. If `g` lies in `Gamma(w)`, so does `A*g*A^-1`. Original invariance applied to that element proves invariance of `f_A`. Evaluation at `A^-1*z` proves nonvanishing. Composition of integral scaling matrices proves all cusp decay conditions. Covariance gives the same eigenvalue.
3. Pullbacks compose in matrix order, act trivially on congruence elements, and have inverse pullbacks. If `A^-1*B` is in the congruence group, pullback by `B` equals pullback by `A`. Thus the actual Maass family descends to `Q`, without selecting or assuming compatible representatives.
4. Positive level makes `Q` finite by the actual congruence finite-index instance. Multiplication on `Q` permutes its elements, while `f_q(A*z)=f_(q*A)(z)`. Summing squared norms proves full modular invariance of `D`. The identity coset dominates the original squared norm, so original nonvanishing makes `D` positive somewhere. Real and imaginary polynomial squares prove C². The finite sum of the proved cusp limits proves decay.
5. Full modular invariance gives period one of the actual horizontal trace. Finite-sum integration over width `w` equals `w*sum_q M_q`. The exact periodic interval-integral multiple formula gives the same integral as `w*H`; positive `w` cancels. This proves the unit-width normalization without a measure or multiplicity assumption.
6. On positive heights, this equality holds locally. Finite sums of the previously proved actual mass and flux derivatives give the two derivatives of `H`. The finite sum of the existing actual hyperbolic tail integrability proofs proves integrability of `H/y²` and justifies its integral as the sum of the actual tail masses.
7. Sum the existing exact flux/Bessel identity over the finite group. The normalization from steps 5–6 identifies the tail mass with the literal unit-strip integral of `D`. Nonnegative square terms give the lower bound. No term from the compact modular core has been removed.

## Lean audit

- `GaloisForLFunctions.RHTower.SelbergMaassCuspTransport`: C² covariance, actual translates and their composition/inverse laws, and every integral cusp's constant coefficient and Bessel identities. Complete scratch and direct source checks passed without warnings.
- `GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace`: finite quotient family, modular invariant density, physical unit-width mass normalization and derivatives, exact trace tail and boundary identities. Complete mathematical scratch proof passed; final exported-instance check and source audit pending.

Final targeted builds, axiom audits, index refresh, lint, whitespace, and process cleanup will be recorded here from their actual terminal outputs.

## Remaining conjecture and next proof attempt

Use the actual finite trace density to derive its pointwise second-derivative identity, retaining every squared-gradient term. Its modular invariance should give the exact translation-side and inversion-arc current cancellations used by the inspected curved-boundary Stokes construction. Prove the Maass version for the physical truncated core, then attach the completed trace cusp decomposition. The resulting combined core-plus-cusp quarter form still needs a genuine congruence-uniform lower bound. Neither its Green assembly nor that lower bound has been proved here; the Selberg goal remains active.
