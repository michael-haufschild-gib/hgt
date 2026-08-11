# Adaptive orthogonal source is Jacobi-compression energy

- **ID:** adaptive-orthogonal-source-jacobi-coercivity
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3, equations (9.3.375)--(9.3.377)
- **Statement:** For every positive real moment form and every positive degree, adaptive shear of its monic orthogonal polynomial has strictly positive moment; exactly, it is orthogonal norm times a positive Jacobi-compression square plus positive boundary couplings.

## Goal

Test whether inverse-Hankel conditioning in (9.3.377) is intrinsic or only an artifact of monomial
coordinates.  Replace coefficient perturbation by exact recurrence-coordinate evaluation of the
source scalar itself.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, hostile attacks and Door passport recorded
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy`, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frontier and audit

- `[CORPUS]` `HTGeometry.monicOrtho_three_term` supplies the exact three-term recurrence for every
  `PositiveMomentForm`; `monicOrtho_inner_eq_zero_of_degree_lt` supplies lower-degree annihilation.
- `[CORPUS]` `RHTower.xiShiftedHankelBoundary_adaptiveShear_eq_adjacentDefects` already proves that
  at flat odd contact adaptive source reduces to two adjacent Padé defects.  It does not prove
  source positivity in an open positive chamber.
- `[CORPUS]` exact arcsine computation gives margins `11/64` and
  `2^(2-4n)(8n+3)/16`, but its coefficientwise proof leaves a collapsing-margin/conditioning wall.
- `[LITERATURE]` current orthogonal-polynomial perturbation work studies recurrence-coefficient,
  Jacobi-resolvent, Toda/Laguerre--Freud, and asymptotic stability mechanisms.  No audited source
  states the exact adaptive-shear/Jacobi-energy identity below.  Novelty remains unverified.

## Conjecture/failure loop

1. `[CONJECTURE]` Positivity might require shifted support on `[0,∞)`.
   **Verdict: FALSE AS A NECESSITY.** Exact recurrence algebra uses no support sign; arbitrary real
   Jacobi diagonals enter a positive quadratic form.
2. `[CONJECTURE]` Negative Jacobi diagonal can make adaptive source negative.
   **Verdict: FALSIFIED.** Completing squares absorbs every diagonal sign; two strictly positive
   neighbouring subdiagonal couplings force strict positivity.
3. `[CONJECTURE]` Inverse-Hankel conditioning is required to transfer arcsine source positivity.
   **Verdict: FALSIFIED inside any positive moment chamber.** Source scalar has an exact
   coordinate-free Jacobi formula and is positive without closeness to arcsine.
4. `[BRIDGE]` Surviving exact theorem: adaptive source is positive Jacobi-compression energy.
   This does not by itself orient a fixed outgoing flag after it ceases to be orthogonal to the
   evolving moment form.

## Exact claim

Let `L` be a positive definite real moment functional, let `(P_k)` be its monic orthogonal
polynomials, and write

`h_k=L(P_k^2)>0`,

`α_k=L(X P_k^2)/h_k`,

`β_k=h_k/h_{k-1}>0` for `k≥1`.

For `n≥1`, set

`A(P_n)=(X P_n) X (X P_n' + P_n)`.

Then

`L(A(P_n)) = h_n E_n`,

where

`E_n = Σ_{j<n} α_j^2 + α_n Σ_{j<n} α_j + (n+1)α_n^2`

`      + 2 Σ_{1≤j<n} β_j + (n+1)(β_n+β_{n+1})`.

Equivalently,

`E_n = Σ_{j<n}(α_j+α_n/2)^2 + (3n/4+1)α_n^2`

`      + 2 Σ_{1≤j<n}β_j + (n+1)(β_n+β_{n+1}) > 0`.

If `J_n` is leading `n×n` Jacobi compression, this is

`E_n = ||J_n+(α_n/2)I||_F^2 + (3n/4+1)α_n^2`

`      + (n+1)(β_n+β_{n+1})`.

## Dependency-closed paper proof `[PROVED HERE]`

For `k≥0`, the monic three-term recurrence is

`XP_k=P_{k+1}+α_kP_k+β_kP_{k-1}`,

where the last term is omitted at `k=0`.  Positivity of the moment form gives `h_k>0` and
`β_k=h_k/h_{k-1}>0`.  Write

`P_k=X^k+a_kX^{k-1}+b_kX^{k-2}+O(X^{k-3})`,

with the absent coefficients at degrees zero and one interpreted as zero, and put
`S_k=Σ_{j<k}α_j`.  Comparing the first two subleading coefficients in the recurrence gives

`a_{k+1}=a_k-α_k`,

`b_{k+1}=b_k-α_ka_k-β_k` for `k≥1`.

Starting from `a_0=0`, `b_1=0`, induction therefore gives

`a_k=-S_k`,

`b_k=Σ_{0≤i<j<k}α_iα_j-Σ_{1≤j<k}β_j`.                                      (1)

Fix `n≥1` and set

`R_n=X²P_n+X³P_n'`.

Its top three coefficients are respectively `n+1`, `na_n`, and `(n-1)b_n`.  Consequently there
are unique `u_n,v_n∈ℝ` and a polynomial `D_n` of degree `<n` such that

`R_n=(n+1)P_{n+2}+u_nP_{n+1}+v_nP_n+D_n`.                                  (2)

Comparison at degrees `n+1` and `n` gives

`u_n=na_n-(n+1)a_{n+2}=S_n+(n+1)(α_n+α_{n+1})`,                             (3)

`v_n=(n-1)b_n-(n+1)b_{n+2}-u_na_{n+1}`.                                    (4)

Apply (1) twice:

`a_{n+1}=-(S_n+α_n)`,

`b_{n+2}=b_n+α_nS_n+α_{n+1}(S_n+α_n)-β_n-β_{n+1}`.

Substitution in (4) cancels every `α_{n+1}` term and yields

`v_n=S_n²-2b_n+α_nS_n+(n+1)α_n²+(n+1)(β_n+β_{n+1})`.                       (5)

Equation (1) also gives

`S_n²-2b_n=Σ_{j<n}α_j²+2Σ_{1≤j<n}β_j`.                                     (6)

Since

`A(P_n)=(XP_n)X(XP_n'+P_n)=P_nR_n`,

orthogonality kills the `P_{n+2}`, `P_{n+1}`, and `D_n` terms of (2).  Thus

`L(A(P_n))=v_nL(P_n²)=h_nv_n`.

Equations (5)--(6) identify `v_n=E_n`.  Finally,

`Σ_{j<n}α_j²+α_nS_n+(n+1)α_n²`

`  =Σ_{j<n}(α_j+α_n/2)²+(3n/4+1)α_n²`.                                    (7)

Every square in (7) is nonnegative, while `β_n,β_{n+1}>0` and `n+1>0`; hence `E_n>0`, and then
`L(A(P_n))>0` because `h_n>0`.  This proves the exact identity and strict positivity without any
support, asymptotic, or conditioning hypothesis.

For the leading Jacobi compression `J_n` in the orthonormal basis, its diagonal entries are
`α_0,…,α_{n-1}` and its two off-diagonals are `√β_1,…,√β_{n-1}`.  Hence

`||J_n+(α_n/2)I||_F²=Σ_{j<n}(α_j+α_n/2)²+2Σ_{1≤j<n}β_j`,

which proves the coordinate-free form.

For the shifted arcsine form, `α_j=1/2`, `β_1=1/8`, `β_j=1/16` for `j≥2`, `h_1=1/8`, and
`h_n=monicScale(n)²/2` for `n≥2`.  Substitution gives `E_1=11/8` and
`E_n=(8n+3)/8` for `n≥2`, hence the previously proved margins `11/64` and
`monicScale(n)²(8n+3)/16`.  Their apparent decay is entirely the norm factor `h_n`; the normalized
Jacobi energy grows linearly.

## Hostile review

- **Sign attack:** arbitrary negative and mixed-sign `α_j` are absorbed by (7); no support
  restriction is hidden.
- **Boundary-index attack:** at `n=1`, the interior `β` sum is empty but
  `2(β_1+β_2)>0`; no `P_{-1}` or absent coefficient is used.
- **Conditioning attack:** formula uses recurrence coordinates and positive norm ratios, never an
  inverse Hankel matrix.  Monomial ill-conditioning cannot change its sign.
- **Circularity attack:** positivity of moment form is used only for orthogonality, `h_k>0`, and
  `β_k>0`; no Xi zero-location statement enters.
- **Priority attack:** exact-phrase and structural searches found standard recurrence, Jacobi,
  ladder-operator, and perturbation results, but no matching adaptive derivative-source identity.
  This is evidence only; novelty remains unverified pending specialist review.

## Door passport

- **Input purity:** positive moment form, monic orthogonal admission, its Jacobi recurrence.
- **No circularity:** no Xi zero-location, RH, asymptotic closeness, inverse-Hankel bound, reporter,
  or reflection aggregation.
- **Output:** exact adaptive source scalar and strict positivity in every degree.
- **Boundary:** does not apply once a flag is frozen and moment functional evolves away from its
  admission point; that connection term is next open object.

## Lean certificate

- `HTGeometry.FiniteOrthogonalMomentPolynomials`
  - `positiveMomentFormBelow_of_hankelPosDef` — one finite positive Hankel block gives bounded
    moment positivity;
  - `monicOrtho_three_term_below` — Gram--Schmidt orthogonality and Jacobi recurrence localized to
    that block.
- `HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy`
  - `monicOrtho_coeffJet_energy` — exact first/second coefficient-jet invariant;
  - `adaptiveOrthoProjectionCoeff_eq_energy` — companion projection equals completed Jacobi energy;
  - `degree_adaptiveOrthoRemainder_lt` — all unreported terms lie below the admitted degree;
  - `momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy` — literal mixed-amplitude
    source equals orthogonal norm times energy;
  - `momentFunctional_adaptiveOrthoSourcePolynomial_pos` — unconditional strict positivity from
    `PositiveMomentForm` and positive degree.
  - `momentFunctional_adaptiveOrthoSourcePolynomial_pos_of_hankelPosDef` — the `(n+2) × (n+2)`
    positive Hankel block alone forces literal source positivity.
- `RHTower.XiShiftedAdaptiveOrthogonalSourceJacobiEnergy`
  - `xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_jacobiEnergy` — completed
    `P^sharp` arithmetic aggregate equals twice the same energy for moving shifted-Xi admission;
  - `xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_pos` — strict source positivity in
    every positive shifted-Xi moment chamber.
  - `neg_adaptiveArithmeticSource_forces_hankelFailure_or_admissionMismatch` — any negative event
    lies exactly in higher-block chamber failure or fixed/moving admission mismatch.

## Log

- 2026-08-11 — created in `1-in-progress`; three competing necessity/negativity/conditioning
  conjectures killed by exact recurrence algebra.
- 2026-08-11 — `[PROVED HERE]`; coefficient comparison, square completion, boundary-index audit,
  and arcsine specialization completed.  Promoted to `2-fully-proven`.
- 2026-08-11 — formalized exact coefficient cancellation, lower-remainder annihilation, universal
  positivity, and completed shifted-Xi arithmetic connector.  Promoted to `3-formalized`.
