# Actual Sonin Euler-Metric Corner Is Noncompact

- **ID:** sonin-euler-metric-corner-noncompact
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Grade:** BRIDGE / GATEKEEPER (new source-specific operator consequence); not C5
- **Source:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Definition 4.3, equations (51)--(53), Propositions 4.6--4.8;
  `sonin-place-transition-cutoff-dichotomy.md`;
  `../../1-in-progress/sonin-cutoff-transversality-realization.md`
- **Statement:** For every `lambda > 0` and every prime `p`, the corner of the positive local Euler
  metric across the **actual** archimedean Sonin projection is noncompact. Consequently it is in no
  finite Schatten class and cannot directly define the trace-ideal/determinant seam sought by the
  current `M+` extension.

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

is not compact.

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

Thus `(1-Pi^B_{lambda,infinity}) M_{w_p} Pi^B_{lambda,infinity}`

is unitarily equivalent to `-p^(-1/2)L_{p,lambda}` and is noncompact.

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

### 4. Consequence for the metric semicommutator

The diagonal compression defect of the Euler metric, with
`Pi = Pi^B_{lambda,infinity}`, is

`Pi M_{w_p^2}Pi-(Pi M_{w_p}Pi)^2 = H_p^*H_p`,

where `H_p=(1-Pi)M_{w_p}Pi`. If `H_p^*H_p` were compact, then
`|H_p|=(H_p^*H_p)^(1/2)` and hence `H_p` would be compact. Thus the diagonal defect is also
noncompact. No trace, Hilbert--Schmidt pairing, Fredholm determinant, or finite Fitting boundary is
available for this unsmoothed source operator.

## Attack and scope

- `[PROVED]` The theorem fails at `lambda=0`: the Sonin constraint is the full space and the corner is
  zero. The positive-cutoff hypothesis is essential.
- `[PROVED]` The shell degenerates at scale factor `1`; the theorem uses `p>1`.
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
- `[OPEN CORE]` The theorem does not yet cover the orthogonal projection for every already-semilocal
  `S`-dependent norm, the inverse weight `w_p^(-1)`, or the two-prime product
  `P M_{w_p}(1-P)M_{w_q}P`. A product of two noncompact corners can be compact.
- `[SEARCH]` The compactness of the time-band prolate block and the Toeplitz--Hankel algebra are
  classical ingredients. The source-specific assembly above is the result: it determines the
  previously unresolved actual-Sonin corner rather than another ambient support corner.

## Novelty and significance gates

- **NOVEL:** The cited 2023 paper states the prime-dependent norms on the common carrier but does not
  determine the compactness of their corner across the actual Sonin projection. The related 2020
  quasi-inner paper studies local-factor **phase ratios** across a Hardy projection; it does not prove
  this positive Euler-metric noncompactness theorem. A targeted corpus and primary-source search found
  no prior statement of this result.
- **SIGNIFICANT:** The prior dichotomy deliberately left open whether the full Sonin intersection could
  regularize the raw shell crossing. It does not. The actual constraint still admits asymptotically
  shell-localized high-frequency modes, so the canonical bounded metric candidate lies outside every
  Schatten ideal. Any surviving determinant seam now needs genuinely additional smoothing, not a
  reinterpretation of the source norm.

## Lean realization

The analytic theorem and the concrete archimedean source transport are formalized without an
intertwining hypothesis. The source stack is:

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

## Gates

- [x] 0 -> 1: actual source operator, actual Sonin projection, and degenerate cases isolated.
- [x] 1 -> 2: noncompactness proved by the two-projection correction formula and shell Weyl sequence.
- [x] 2 -> 3: the complete analytic theorem and concrete archimedean dual Hardy--Titchmarsh
  unitary transport are formalized through `HardyTitchmarshEulerConcrete.lean`, with stage-3 card
  `../../3-formalized/new/even-sonin-euler-corner-noncompact.md`. The source-image projection,
  pointwise local Euler multiplier, exact pullback, and noncompactness are all encoded.
- [ ] 3 -> 4: requires standalone analytic exposition and an independent source/literature audit.
