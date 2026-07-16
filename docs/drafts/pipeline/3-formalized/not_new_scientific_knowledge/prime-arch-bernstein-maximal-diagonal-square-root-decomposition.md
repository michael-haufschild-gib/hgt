# Prime--archimedean maximal-diagonal square-root decomposition

- **ID:** `prime-arch-bernstein-maximal-diagonal-square-root-decomposition`
- **Stage:** 3-formalized
- **Type:** THEOREM / FALSE-PHASE NORMAL FORM / BRIDGE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Source:** endpoint prime--Gamma moment germ and its Xi atomic Bernstein packet

## Theorem

Let

\[
  \chi(t)=\sum_{n\ge 0}\Pi_n t^n
\]

be the endpoint Bernstein susceptibility. If RH is false, there are a finite nonempty maximal
coordinate packet `D`, numbers

\[
  1<\beta<B,\qquad R=B^{-2}<1,
\]

and a positive coefficient

\[
  L=\sum_{u\in U_D}|C_D(u)|^2c(u)>0
\]

with the following properties.

1. `R` is the exact Abel radius of `chi`.
2. The maximal diagonal susceptibility is exactly

   \[
   \chi_D^{\mathrm{diag}}(t)
   =\sum_{u\in U_D}|C_D(u)|^2
     \frac{1}{\sqrt{1-B^2t}\,
       \sqrt{1-(|u|-|1-u|)^2t}}
   \]

   for every `0<t<R`.
3. On the same interval there is the exact decomposition

   \[
     \chi(t)=\chi_D^{\mathrm{diag}}(t)+\mathcal R_D(t),
   \]

   where the defining series of `R_D` is summable at every interior point.
4. At the selected boundary,

   \[
   \sqrt{1-B^2t}\,\mathcal R_D(t)\longrightarrow0,
   \]

   while

   \[
   \sqrt{1-B^2t}\,\chi_D^{\mathrm{diag}}(t)
   \longrightarrow\sqrt\pi L,
   \qquad
   \sqrt{1-B^2t}\,\chi(t)
   \longrightarrow\sqrt\pi L.
   \]

Thus every false phase has a finite, positive, source-selected algebraic square-root normal form.
The off-diagonal maximal modes and the complete nonmaximal Xi complement contribute zero at the
leading square-root scale.

## Proof structure

For one affine Bernstein coordinate `u`, the diagonal row energy is the central-binomial
convolution with characteristic radii

\[
  B=|u|+|1-u|,
  \qquad D_u=|u|-|1-u|.
\]

Its generating series is exactly

\[
  ((1-B^2t)(1-D_u^2t))^{-1/2}.
\]

Failure of RH supplies a finite maximal Xi packet with common `B>1`. Equal normalized coordinates
are aggregated first, so every occupied fibre has nonzero weight. Distinct maximal coordinates
have a strict mixed Gutzmer gap, and the complete complement has a uniform amplitude `beta<B`.
The already proved full-packet asymptotic and the finite diagonal asymptotic therefore have the
same positive half-order coefficient `L`. Their difference has normalized coefficient limit zero.
The signed Abel transfer theorem sends that zero coefficient limit to the vanishing boundary law
for `R_D`. Interior summability gives the exact pointwise decomposition.

## Strengthened master theorem

`PrimeArchEndpointBernsteinAbelSharpFalsePhase` now includes the exact finite square-root kernel,
the interior decomposition, and the vanishing leading-scale remainder. Consequently the single
sharp Abel selection master theorem contains the finite positive chamber, the unique exact radius,
the RH unit phase, and this full false-phase normal form.

## Formal artifacts

- `formal/GaloisForLFunctions/RHTower/FiniteBernsteinDiagonalSquareRootDecomposition.lean`
- `formal/GaloisForLFunctions/RHTower/XiBernsteinPuritySquareRootDecomposition.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinAbelSharpSelectionMaster.lean`

The principal declarations are:

- `hasSum_finiteBernsteinCoordinateDiagonalEnergy_eq_squareRootKernel`;
- `exists_exact_maximalDiagonalSquareRootDecomposition_of_not_rh`;
- `primeArchEndpointBernsteinAbelSharpSelectionMaster`.

Their axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Positive Connes obligation

The 2025 zeta-spectral-triple construction supplies finite self-adjoint operators and proposes
normalized determinant convergence toward `Xi`; that convergence remains unproved. The present
theorem identifies the exact statement a successful convergence theorem must force:

> the normalized Connes determinant/source response must exclude every finite positive algebraic
> square-root packet at `R<1`, equivalently extend the susceptibility collar to the unit boundary.

Finite self-adjointness, numerical spectral agreement, or a bounded Hilbert--Schmidt Sonin
scalarization cannot do this. The source producer must transport the unbounded logarithmic
Weyl/finite-part channel through the cutoff-resolvent descent and prove a nonhomogeneous completed
prime--Gamma estimate. The current theorem localizes the entire forbidden singularity but does not
provide that estimate.

## Literature classification

The diagonal generating identity is a standard central-binomial/analytic-combinatorics fact, and
finite dominant-mode extraction is standard singularity analysis. Its exact Xi/Connes packaging is
useful project infrastructure but is not claimed as new scientific knowledge.

