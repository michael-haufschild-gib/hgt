# Exact finite part and convergence boundary of raw Mayer determinants

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Theorem

For the actual finite-branch operators `L_N(w)`, write
`a_N(w)=Σ_{n≤N}n^(−w)` and `E_N(w,λ)=det(I−λL_N(w))`.
On `Re w>0`, the exact finite part is

`E_N(w,λ)−a_N(w)B(w,λ) → A(w,λ)`,

where `D(w,λ)=A(w,λ)+ζ(w)B(w,λ)` is the checked source determinant.
For `w≠1`, equivalently

`E_N−N^(1−w)B/(1−w) → D`.

For `0<Re w<1`, convergence of raw determinants is therefore equivalent
to `B(w,λ)=0`; the limit is then `D=A`. Otherwise

`|E_N|/N^(1−Re w) → |B(w,λ)|/|1−w| > 0`.

## Proof mechanism

1. The genuine decomposition is `L_N=R_N+a_NP`, with `P f=f(0)·1`.
   Let `Q=I−P`, `K_N=QR_NQ`, and `K=QRQ`. Finite row multilinearity
   and geometric Fredholm limits give
   `E_N=A_N+a_NB_N`, where `A_N=det(I−λR_N)` and
   `B_N=−λ fdet(C_N,λ)`; likewise `B=−λ fdet(C,λ)`.
   Here `C_N,C` are the complementary Cauchy blocks identified below.

   In the rescaled Cauchy coordinates, `P` occupies row zero with entries
   `q_j=s^(−j)(−1)^j`, `q_0=1`. Multiplying the evaluation-row matrix by
   the triangular determinant-one shear with first row `(1,−q_1,−q_2,…)`
   leaves the complementary block `M_{i+1,j+1}−M_{i+1,0}q_{j+1}`.
   Laplace expansion proves the coefficient identity in each finite section.
   The complementary block equals the positive-index block of the actual
   double-centered Cauchy matrix. No inverse or determinant nonvanishing
   is assumed.
2. For the genuine branch put `a(z)=(n+z)^(−w)`, `u(z)=1/(n+z)`.
   Its compressed action is

   `a(z)[f(u(z))−f(u(0))]+[a(z)−a(0)][f(u(0))−f(0)]`.

   On `|z−1|≤3/2`, the checked source bounds give
   `|u(z)−u(0)|≤5/n²`, `|u(0)|=1/n`, and both inverse images lie in
   `|u−1|≤1`. For `f_j(z)=(z−1)^j`, the power-difference inequality yields

   `‖Q B_n(w) Q f_j‖ ≤ j H(w)n^(−Re w−2)`,

   `H(w)=5M(w)+(5/2)|w|M(w+1)`.

   This is an estimate for the actual disc-algebra branch, not an assumed matrix.
3. The existing rescaled Cauchy majorant absorbs `(j+1)(8/9)^j`.
   Thus `K_N,K` have one common geometric matrix bound and their difference
   has geometric constant at most

   `H(w) degreeBound · Σ_{n>N}n^(−Re w−2)`.

   Entrywise limits and the actual branch HasSum identify the limiting matrix.
4. Row replacement gives the certified perturbation estimate

   `|fdet(M,λ)−fdet(N,λ)| ≤ δ|λ|S² exp(|λ|CS²)`, `S=(1−η)⁻¹`,

   whenever both matrices have common geometric constant `C` and their
   difference has constant `δ`. The bound is uniform in finite-section size
   and passes to the Fredholm limit.
5. Consequently `|B_N−B|≤C(w,λ) Σ_{n>N}n^(−Re w−2)`.
   The checked bound `|a_N|≤N` gives

   `|a_N(B_N−B)|≤C(w,λ) Σ_{n>N}n^(−Re w−1)→0`.

   Uniform geometric convergence of `R_N` gives `A_N→A`.
   Subtracting `a_NB` proves the exact finite part.
6. The checked scalar finite part is
   `a_N−N^(1−w)/(1−w)→ζ(w)` for `w≠1`.
   Combining limits gives the second normalization. In the critical strip,
   multiplication by `N^(w−1)` gives limit `B/(1−w)`; taking norms gives
   the sharp growth law. If `B=0`, the unscaled finite-part limit converges.
   If `B≠0`, the positive norm asymptotic forces divergence.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerRawDeterminantFinitePart.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFinitePart`.

- `compressed_branch_apply`, `inverse_branch_difference_bound`,
  `norm_compressed_branch_monomial`, `hasSum_compressed_branch`.
- `tendsto_mul_doubleTail`, `norm_compressed_monomial_tail`,
  `compressed_matrix_tail_bound`, `complementaryMatrix_eq_compressed`.
- `polePart_eq_complement`, `rawSpectralDeterminant_decomposition`.
- `rawSpectralDeterminant_finitePart_tendsto`,
  `rawSpectralDeterminant_counterterm_tendsto`.
- `rawSpectralDeterminant_scaled_tendsto`, `rawSpectralDeterminant_norm_ratio`,
  `rawSpectralDeterminant_norm_atTop`.
- `rawSpectralDeterminant_tendsto_iff`, `rawSpectralDeterminant_has_limit_iff`.

The supporting modules `GaussMayerDeterminantPerturbation.lean` and
`GaussMayerComplementaryDeterminant.lean` supply the uniform determinant
bound and exact complementary Fredholm identity. Direct production checks
passed without diagnostics; all eighteen source audits, three perturbation
audits, and five complementary-identity audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella imports wired.

## Scope

The source pole coefficient classifies raw determinant convergence in
the critical strip, beyond the already certified negative-unit parameter.
This supplies neither determinant nonvanishing nor a scattering identity,
and it does not establish RH. Finite branch cutoffs and finite Cauchy
matrix sections remain distinct throughout.

The [positive real coefficient theorem](gauss-mayer-positive-real-pole-coefficient.md)
now proves `B(w,λ)≠0` for real `w>0`, `0<λ<(3/2)^w`.
