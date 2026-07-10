# Exact Essential Norm of the Actual Sonin Euler-Metric Corner

- **ID:** sonin-euler-metric-corner-noncompact
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Grade:** BRIDGE / GATEKEEPER (new source-specific operator consequence); not C5
- **Source:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Definition 4.3, equations (51)--(53), Propositions 4.6--4.8;
  `sonin-place-transition-cutoff-dichotomy.md`;
  `../../1-in-progress/sonin-cutoff-transversality-realization.md`
- **Statement:** For every `lambda > 0` and every real scale `p>1`, the dilation corner across the
  **actual** even archimedean Sonin projection has essential norm exactly `1`. The positive local
  Euler corner therefore has essential norm exactly `p^(-1/2)`. Consequently it is in no finite
  Schatten class and cannot directly define the trace-ideal/determinant seam sought by the current
  `M+` extension.

## Theorem

Let `H = L^2(R)^ev`. Let `A_lambda` be multiplication by the indicator of
`[-lambda,lambda]`, let `F` be the unitary Fourier transform, and put

`R_lambda := F^* A_lambda F`, `E_lambda := 1-A_lambda`.

The archimedean Sonin space and its orthogonal projection are

`S_lambda = ker(A_lambda) intersect ker(R_lambda)`, `Q_lambda = P_{S_lambda}`.

For `p>1`, let the unitary dilation be

`(U_p f)(x) = p^(1/2) f(px)`.

Then

`L_{p,lambda} := (1-Q_lambda)(U_p+U_p^*)Q_lambda`

satisfies

`||L_{p,lambda}||_ess = 1`.                              (0)

On the archimedean dual Hardy--Titchmarsh line, the positive Euler weight

`w_p(s) = |1-p^(-1/2-is)|^2
        = 1+p^(-1)-p^(-1/2)(p^(is)+p^(-is))`

acts, after pullback by `upsilon_infinity`, as

`(1+p^(-1))1-p^(-1/2)(U_p+U_p^*)`.

The precise source meaning of this weight is metric, not a residual place factor. If
`iota'_p` is the identity from the archimedean Hardy--Titchmarsh line to the `{infinity,p}` line,
then Proposition 4.7 gives

`upsilon_{infinity,p} theta_p = iota'_p upsilon_infinity`,

because the factor `1-p^(-1/2-is)` from Proposition 4.6 cancels against the finite Euler factor in
`beta_{infinity,p}`. The Radon--Nikodym/Gram operator is

`(iota'_p)^* iota'_p = M_{w_p}`.

Proposition 4.8 identifies the Sonin space with the common entire-function carrier `B_lambda`, with
a norm depending on the set of places. Let `Pi^B_{lambda,infinity}` denote the orthogonal projection
onto the boundary image of that carrier in the **archimedean-norm** critical-line Hilbert space.
Then

`upsilon_infinity^* (1-Pi^B_{lambda,infinity}) M_{w_p} Pi^B_{lambda,infinity} upsilon_infinity
   = (1-Q_lambda)((1+p^(-1))1-p^(-1/2)(U_p+U_p^*))Q_lambda
   = -p^(-1/2)L_{p,lambda}`.

Thus `(1-Pi^B_{lambda,infinity}) M_{w_p} Pi^B_{lambda,infinity}` is unitarily
equivalent to `-p^(-1/2)L_{p,lambda}` and has essential norm exactly `p^(-1/2)`.

## Proof

### 1. The two-cutoff projection has a bounded correction formula

Regard

`C_lambda := R_lambda E_lambda : E_lambda H -> R_lambda H`.

Its adjoint is `E_lambda R_lambda`, and on `R_lambda H`,

`C_lambda C_lambda^* = R_lambda E_lambda R_lambda
                           = 1_{R_lambda H}-R_lambda A_lambda R_lambda`.

The prolate block `R_lambda A_lambda R_lambda` is compact. Indeed,
`A_lambda R_lambda` is Hilbert--Schmidt: after conjugating one Fourier transform, its kernel is
restricted to a finite time-frequency rectangle. Hence

`R_lambda A_lambda R_lambda=(A_lambda R_lambda)^*(A_lambda R_lambda)`

is compact and positive.

It has no eigenvalue `1`. If `R_lambda A_lambda R_lambda h=h` with `R_lambda h=h`, then

`||h||^2 = <h,R_lambda A_lambda R_lambda h> = ||A_lambda h||^2`,

so also `A_lambda h=h`. Such an `h` is supported in a bounded interval and its Fourier transform is
supported in a bounded interval. The Fourier uncertainty theorem forces `h=0`. Since the block is
compact and positive, it follows that

`||R_lambda A_lambda R_lambda|| < 1`.

Thus `C_lambda C_lambda^*` is boundedly invertible and `C_lambda` is onto. The orthogonal projection
onto

`ker(C_lambda)=E_lambda H intersect ker(R_lambda)=S_lambda`

is, on `E_lambda H`,

`Q_lambda = 1-C_lambda^*(C_lambda C_lambda^*)^(-1)C_lambda`.

Writing `r_lambda=||R_lambda A_lambda R_lambda||<1`, the closed-range estimate gives, for every
`g in E_lambda H`,

`||g-Q_lambda g|| <= (1-r_lambda)^(-1/2) ||R_lambda g||`.                            (1)

### 2. High-frequency shell modes are asymptotically Sonin

Let

`J_{p,lambda} = {x : lambda < |x| < p lambda}`.

Choose any orthonormal sequence of even functions `g_n` supported in this shell; normalized
indicators of countably many disjoint symmetric sub-shells give one explicit choice. The restricted
operator

`A_lambda F 1_{J_{p,lambda}}`

is Hilbert--Schmidt because its Fourier kernel is restricted to a finite time--frequency rectangle,
hence compact. A compact operator sends an orthonormal sequence to a norm-null sequence, so

`||R_lambda g_n|| = ||A_lambda F g_n|| -> 0`.

Equation (1) gives

`f_n := Q_lambda g_n in S_lambda`, `||f_n-g_n|| -> 0`.

The sequence `g_n` is orthonormal, hence weakly null; therefore `f_n` is bounded and weakly null as
well.

### 3. Dilation moves the shell across the physical cutoff

The dilation `U_p` sends `J_{p,lambda}` to

`{x : lambda/p < |x| < lambda}`,

inside the physical cutoff, while `U_p^*` sends it to

`{x : p lambda < |x| < p^2 lambda}`,

outside. Hence

`A_lambda(U_p+U_p^*)g_n = U_p g_n`, `||U_p g_n||=1`.

Since `f_n-g_n -> 0`,

`||A_lambda(U_p+U_p^*)f_n|| -> 1`.                                      (2)

The Sonin space lies in `ker(A_lambda)`, so `A_lambda Q_lambda=0` and
`A_lambda(1-Q_lambda)=A_lambda`. Using `Q_lambda f_n=f_n`, equation (2) yields

`liminf_n ||L_{p,lambda}f_n|| >= 1`.

A compact operator sends bounded weakly null sequences to norm-null sequences. Therefore
`L_{p,lambda}` is noncompact.

### 4. The Calkin image is a norm-one partial isometry

Let `pi` be the Calkin quotient and write

`alpha_b=pi(A_b)`, `rho_b=pi(R_b)`, `q=pi(Q_lambda)`, `u=pi(U_p)`.

Every finite time--band block `A_bR_c` is compact. Hence `alpha_b rho_c=0` for all finite
`b,c>0`. The strict prolate bound in Step 1 implies that the projection onto
`range(A_lambda)+range(R_lambda)` differs compactly from `A_lambda+R_lambda`. Therefore

`q=1-alpha_lambda-rho_lambda`.                           (3)

There are two exact support vanishings:

`A_lambda U_p^* Q_lambda=0`, `R_lambda U_p Q_lambda=0`.   (4)

The first uses the enlarged physical gap under `U_p^*=U_(1/p)`; the second is its Fourier-dual
counterpart. Equations (3)--(4) give

`pi(L_{p,lambda})=alpha_lambda u q+rho_lambda u^*q`.      (5)

The dilation conjugation identities are

`u^*alpha_lambda u=alpha_(p lambda)`,
`u rho_lambda u^*=rho_(p lambda)`.

All mixed time--frequency products vanish in the Calkin algebra. Consequently

`pi(L_{p,lambda})^*pi(L_{p,lambda})`

`= (alpha_(p lambda)-alpha_lambda)
   +(rho_(p lambda)-rho_lambda)`.                         (6)

The two summands are orthogonal nonzero projections: they are the physical and Fourier shell
projections for `lambda<|x|<=p lambda`. Their sum is therefore a nonzero projection. Equation (6)
shows that `pi(L_{p,lambda})` is a partial isometry in the Calkin algebra and

`||L_{p,lambda}||_ess=||pi(L_{p,lambda})||=1`.

The positive Euler corner is the scalar multiple `-p^(-1/2)L_{p,lambda}`, so its essential norm is
exactly `p^(-1/2)`.

### 5. Consequence for the metric semicommutator

The diagonal compression defect of the Euler metric, with
`Pi = Pi^B_{lambda,infinity}`, is

`Pi M_{w_p^2}Pi-(Pi M_{w_p}Pi)^2 = H_p^*H_p`,

where `H_p=(1-Pi)M_{w_p}Pi`. If `H_p^*H_p` were compact, then
`|H_p|=(H_p^*H_p)^(1/2)` and hence `H_p` would be compact. Thus the diagonal defect is also
noncompact. In fact, the C-star identity gives the exact value

`||Pi M_(w_p^2)Pi-(Pi M_(w_p)Pi)^2||_ess`

`=||H_p^*H_p||_ess=||H_p||_ess^2=p^(-1)`.                (7)

No trace, Hilbert--Schmidt pairing, Fredholm determinant, or finite Fitting boundary is available
for this unsmoothed source operator.

## Attack and scope

- `[PROVED]` The theorem fails at `lambda=0`: the Sonin constraint is the full space and the corner is
  zero. The positive-cutoff hypothesis is essential.
- `[PROVED]` The shell degenerates at scale factor `1`; the theorem uses `p>1`.
- `[PROVED]` Since `U_p+U_p^*=U_(1/p)+U_(1/p)^*`, the dilation statement extends to every
  `p>0`, `p!=1`. Thus `L_{1,lambda}=0` while `||L_{p,lambda}||_ess=1` for every `p!=1`: the
  strongly continuous dilation group has an essential-norm discontinuity after crossing the fixed
  Sonin constraint.
- `[PROVED]` The sequence is constructed in the even subspace, so it applies to the carrier used by
  the semilocal cyclic pair.
- `[PROVED]` This is not the earlier raw-support calculation. The vectors `f_n` lie in the full
  physical-and-Fourier Sonin intersection, and `Q_lambda` is its actual orthogonal projection.
- `[PROVED]` The source transport is for the pinned archimedean metric and the forward identity
  `iota'_p` obtained by adjoining `p`; its Gram operator is `M_{w_p}`. The map `theta_p` is boundedly
  invertible, not unitary.
- `[PROVED]` The source projection is `Pi^B_{lambda,infinity}`, the archimedean-norm projection onto
  the boundary carrier. It is not the paper's physical time-limiting projection `P_lambda` and not
  the projection defined by the `{infinity,p}` norm.
- `[PROVED]` Every projection in the statement is at fixed cutoff `lambda`. No
  `lambda -> infinity` limiting projection is asserted.
- `[PROVED]` The result closes the positive Euler **metric** compression as a trace-ideal seam. It does
  not decide the formal prolate naturality defect `W_{lambda,S}eta_S-eta_SW_{lambda,infinity}` or a
  separately justified relative-resolvent smoothing.
- `[PROVED]` The Calkin image is a partial isometry with explicit initial projection equal to the sum
  of the physical and Fourier `p`-shell projections.
- `[OPEN CORE]` The theorem does not yet cover the orthogonal projection for every already-semilocal
  `S`-dependent norm or the inverse weight `w_p^(-1)`. The two-prime product is settled separately by
  `sonin-two-scale-quadratic-corner-noncompact.md`.
- `[SEARCH]` The compactness of the time-band prolate block and the Toeplitz--Hankel algebra are
  classical ingredients. The source-specific assembly above is the result: it determines the
  previously unresolved actual-Sonin corner rather than another ambient support corner.

## Novelty and significance gates

- **NOVEL:** The cited 2023 paper states the prime-dependent norms on the common carrier but does not
  determine the Calkin class of their corner across the actual Sonin projection. The related 2020
  quasi-inner paper studies local-factor **phase ratios** across a Hardy projection; it does not prove
  this positive Euler-metric essential-norm identity. A targeted corpus and primary-source search found
  no prior statement of the exact norm or partial-isometry formula. The defensible publication claim is
  "we are not aware of this stronger essential-norm statement," not an absolute priority claim.
- **SIGNIFICANT:** The prior dichotomy deliberately left open whether the full Sonin intersection could
  regularize the raw shell crossing. It does not. The actual constraint still admits asymptotically
  shell-localized high-frequency modes, so the canonical bounded metric candidate lies outside every
  Schatten ideal. Any surviving determinant seam now needs genuinely additional smoothing, not a
  reinterpretation of the source norm.

## Lean realization

The noncompactness theorem and the concrete archimedean source transport are formalized without an
intertwining hypothesis. The exact essential-norm strengthening is paper-level. The source stack is:

- `L2MellinUnitary.lean`: multiplicative-Haar Mellin--Plancherel with exact `2π` normalization;
- `EvenL2LogUnitary.lean`: the even-`L²(dx)` logarithmic Jacobian unitary;
- `HardyTitchmarshBetaInfinity.lean`: the unitary `beta_infinity` into
  `L²(ds/|Gamma_R(1/2+is)|²)`;
- `HardyTitchmarshSourceTransport.lean`: source-image projection, Gram, corner pullback, and
  unitary invariance of noncompactness;
- `HardyTitchmarshEulerConcrete.lean`: the composed dual Hardy--Titchmarsh unitary, pointwise
  `1-p^(-1/2-is)` local factor, literal `M_(w_p)` Gram, and source corner theorem.

The final endpoints are `archimedeanPrimeEulerCorner_pullback`,
`archimedeanPrimeEulerCorner_not_isCompactOperator`, and
`archimedeanPrimeEulerCorner_natPrime_not_isCompactOperator`. The formal carrier projection is the
orthogonal projection onto the actual unitary image of the exact even Sonin carrier. Lean does not
yet define a separate de Branges entire-function object `B_lambda` and identify that independent
object with the image carrier, nor does it encode the full semilocal `theta_p`/`iota'_p` square.

The companion module `SoninEulerQuadraticCorner.lean` now proves the sharp one-scale inequalities

`1 <= ||L_{p,lambda}-K||`

and

`p^(-1/2) <= ||-p^(-1/2)L_{p,lambda}-K||`

for every compact `K` (with the Euler coefficient represented by its exact complex norm). Thus the
lower half of the new essential-norm identity is formalized without introducing a quotient API.

The modules `SoninCalkinNormBound.lean` and `SoninEulerEssentialNorm.lean` complete the identity.
`essentialNorm` is defined in-tree as the distance to the compact ideal, and the upper half is
proved from the one-scale compact congruence

`L^*L =_K (alpha_(p lambda)-alpha_lambda)+(rho_(p lambda)-rho_lambda)`

by a finite-rank orthogonal cut of the compact defects; no Calkin quotient and no spectral theory
enter. The endpoints are:

- `evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell`: the one-scale initial-projection
  law, obtained as the diagonal degeneration of the mixed shell-translation identity;
- `evenCentralSoninDilationCorner_isCalkinPartialIsometry`: the corner is a partial isometry
  modulo compact operators, with the final-projection congruence derived from the initial one by
  the compactness of `L(1-Sigma)`;
- `essentialNorm_evenCentralSoninDilationCorner`: `||L_{p,lambda}||_ess = 1` exactly;
- `essentialNorm_evenCentralPositiveEulerCorner`: `||-p^(-1/2)L_{p,lambda}||_ess = p^(-1/2)`;
- `essentialNorm_archimedeanPrimeEulerCorner` and its rational-prime specialization: the literal
  archimedean Hardy--Titchmarsh source corner has essential norm exactly `p^(-1/2)`, uniformly in
  the cutoff.

All endpoints are axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

Four further scope items are now unconditional Lean theorems:

- **All scales.** `SoninEssentialNormExtensions.lean` extends the corner to every positive
  scale via the symmetry `U_r+U_r^* = U_(1/r)+U_(1/r)^*`:
  `essentialNorm_evenCentralSoninDilationCornerAll` gives `||L_r||_ess = 1` for every real
  `r>0`, `r != 1`, and the corner vanishes at `r = 1` — the essential-norm discontinuity of
  the dilation family is formal.
- **Semicommutator value.** The literal diagonal compression defect
  `Pi G_p^2 Pi - (Pi G_p Pi)^2` is defined as `archimedeanPrimeEulerSemicommutator` and proved
  equal to the equal-scale quadratic corner; `essentialNorm_archimedeanPrimeEulerSemicommutator`
  gives the exact value `p^(-1)` of equation (7).
- **Schatten exclusion.** `SchattenApproximation.lean` defines Schatten classes by
  `p`-summability of approximation numbers (distance to rank-`<=n` operators), proves every
  class lies in the compact ideal, and excludes the dilation, Euler, source, quadratic, and
  semicommutator operators from every finite Schatten class
  (`not_memSchattenClass_archimedeanPrimeEulerCorner` and companions): the trace-ideal
  obstruction is formal.
- **The `theta_p`/`iota'_p` square.** `HardyTitchmarshSemilocalSquare.lean` constructs the
  `{infinity,p}` semilocal weighted line, the finite-Euler-factor unitary, and the forward map
  `iota'_p` (`semilocalForwardMap`, the measurable set-identity by `semilocalForwardMap_ae`),
  and proves the Gram identity `(iota'_p)^* iota'_p = M_(w_p)`
  (`adjoint_semilocalForwardMap_comp_self`) together with the commuting square
  `upsilon_(infinity,p) theta_p = iota'_p upsilon_infinity`
  (`semilocalDualHardyTitchmarshUnitary_comp_localFactor`), with `theta_p` boundedly
  invertible and not unitary.

For the entire-function carrier, `SoninDeBrangesCarrier.lean` proves the two polarized
half-plane bricks unconditionally: the completed transform
`2 Gamma_R(z) int f(t) t^(-z) dt` of every Sonin-carrier element is absolutely convergent and
holomorphic on `Re z > 1/2`, and the dual transform of its Fourier image is holomorphic on
`Re z < 1/2` (`soninCarrier_deBranges_bricks`, `evenSoninCarrier_deBranges_bricks`). The
remaining de Branges weld — that the two halves glue across the critical line to one entire
function and realize `B_lambda` — is the still-open identification.

## Gates

- [x] 0 -> 1: actual source operator, actual Sonin projection, and degenerate cases isolated.
- [x] 1 -> 2: noncompactness proved by the two-projection correction formula and shell Weyl sequence.
- [x] 2 -> 3: the complete analytic theorem and concrete archimedean dual Hardy--Titchmarsh
  unitary transport are formalized through `HardyTitchmarshEulerConcrete.lean`, with stage-3 card
  `../../3-formalized/new_scientific_knowledge/even-sonin-euler-corner-noncompact.md`. The source-image projection,
  pointwise local Euler multiplier, exact pullback, and noncompactness are all encoded.
- [x] Strengthened 2 -> 3: the norm-one Calkin partial-isometry identity and the exact positive
  Euler essential norms `||L||_ess=1`, `||C_p||_ess=p^(-1/2)` are encoded, including the literal
  archimedean source operator (`SoninCalkinNormBound.lean`, `SoninEulerEssentialNorm.lean`).
- [ ] 3 -> 4: requires standalone analytic exposition and an independent source/literature audit.
