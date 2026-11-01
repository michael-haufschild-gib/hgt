# Raw negative-unit determinants converge despite divergent Mayer operators

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [successor cancellation](gauss-mayer-negative-unit-pole-cancellation.md).

## Theorem

On the actual Banach disc algebra `|z−1|≤3/2`, put

`L_N(w)f(z)=Σ_{n=1}^N(n+z)^(−w)f((n+z)^(−1))`.

For every `Re w>0`, the genuine finite-branch Fredholm determinants satisfy

`det(I+L_N(w)) → D(w,−1)=det(I+R(w))`.

The branch cutoff is distinct from the Cauchy matrix section defining each
Fredholm determinant. Each finite-branch determinant still has infinitely many Cauchy indices.
For `0<Re w<1`, the raw operators diverge in norm; their negative-unit
Fredholm determinants nevertheless converge. This includes every actual
nontrivial zeta parameter, without distinguishing critical zeros.

## Proof

Write `σ=Re w`, `M(w)=2^σ exp(π|Im w|)`, `P f=f(0)·1`, and
`a_N=Σ_{n=1}^N n^(−w)`. Let `R_N=L_N−a_NP`.

1. Each branch maps the outer disc into `|u−1|≤1`, so its image of
   `(z−1)^j` has norm at most `M(w)n^(−σ)`, independently of `j`.
   Cauchy's formula and the coefficient norm bound therefore give the
   actual summable rank-one expansion of every branch and every `L_N`.
   The matrix realization on the fixed Hilbert coefficient space satisfies
   `L_N^H Qf=Q L_Nf`, and its matrix is precisely the actual rescaled
   Cauchy matrix of `L_N`.
2. The proved principal-power telescope, with
   `f_w=1−(1+z)^(−w)` and `h_N=(N+1+z)^(−w)`, gives
   `(I+L_N)f_w=1−h_N` and `f_w(0)=0`. Put
   `b_N=a_N/(1−h_N(0))`. The denominator is eventually bounded below
   in norm by `1/2`, since `h_N(0)→0`. Define
   `v_N=−b_N(1−h_N)` and `e_N=b_N(h_N−h_N(0))`. Direct algebra gives
   `S_N:=L_N+v_N⊗ev₀=R_N+e_N⊗ev₀`, and `v_N(0)=−a_N`.
3. The actual Hilbert vectors `u_N=−b_N Qf_w`, `x_N=Qv_N`, with
   evaluation functional `q`, satisfy
   `u_N+L_N^H u_N=x_N`, `q(u_N)=0`, `q(x_N)=−a_N`.
   The Hilbert–Schmidt rank-one update gives
   `det₂(I+S_N^H)=det₂(I+L_N^H) exp(a_N)`.
   Cauchy evaluation identifies the diagonal sum of the rank-one update
   with `v_N(0)=−a_N`. The ordinary determinant's diagonal correction
   cancels this exponential exactly. Thus `det(I+L_N)=det(I+S_N)`
   for all sufficiently large `N`. No inverse is assumed.
4. The source difference estimate gives
   `‖h_N−h_N(0)‖≤(5/2)|w|M(w+1)(N+1)^(−σ−1)`.
   Since `|a_N|≤N` and eventually `|b_N|≤2N`,
   `‖e_N‖≤5|w|M(w+1)(N+1)^(−σ)→0`.
   Normal convergence gives `R_N→R`; hence `S_N→R` in operator norm.
5. Nuclear control is separate. The established degree-linear bound gives
   `‖R_N(z−1)^j‖≤[2jM(w)+(5/2)|w|M(w+1)]Σ_{n≥1}n^(−σ−1)`
   uniformly in `N`. Boundedness of `(j+1)(8/9)^j` shows that the
   rescaled image vectors decay as `(15/16)^j`. The coefficient
   functionals have the same rate. The residual rank-one matrices satisfy
   this uniform bound too, since `e_N` is bounded and evaluation weights
   are `(−1)^j(5/6)^j`. Thus the matrices of `S_N` have a common
   geometric bound `C(15/16)^(i+j)`.
6. Operator convergence gives entrywise convergence to the actual remainder
   matrix. Fix a Cauchy section large enough to make both Fredholm tails
   small using the established uniform geometric error. On that fixed
   section, determinant continuity gives convergence. A three-term
   estimate proves `det(I+S_N)→det(I+R)`. The proved successor cancellation
   identifies the latter with the actual `D(w,−1)`, including at `w=1`.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerRawNegativeUnitDeterminants.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRaw`.

- `cutoff_response`, `finiteRemainder_geometric`, `shearResidual_tendsto`.
- `hasSum_branch_expansion`, `hasSum_cutoff_rankTerms`, `rawHilbertOperator_analysis`.
- `correctedOperator_eq_update`, `det2_raw_update`, `rawDeterminant_eq_corrected`.
- `correctedDeterminant_tendsto`, `rawDeterminant_tendsto`.
- `nontrivialZero_rawDeterminant_and_operator`.

Direct production check passed without diagnostics. Thirteen transitive axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.

## Scope

The scalar divergence, monomial estimate, rank-one update, and geometric
Fredholm section error already existed. The source-specific contribution
is their exact finite successor shear and raw determinant limit.
No literature-priority claim is made.

The theorem supplies no exclusion of off-critical resonances and no
Selberg/scattering identity. It does not assert determinant convergence
at `λ=1` or at general spectral parameters. The raw operator obstruction
remains valid.
