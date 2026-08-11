# Fixed-degree Xi orthogonal admission and adaptive-source recession

- **ID:** mass-shifted-fixed-degree-xi-orthogonal-admission-recession
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** Every fixed nonzero degree has a canonical monic Xi moment admission; after exact mass dilation it converges coefficientwise to shifted monic Chebyshev, and its source-first adaptive arithmetic aggregate has the strictly positive arcsine margin already computed in Lean.

## Goal

Replace informal “moving null polynomial” by an admission-sensitive arithmetic producer defined
before flatness: solve the leading Hankel equations for the unique monic orthogonal polynomial,
then feed that polynomial into the existing bilinear adaptive source.  At a flat next Hankel face
the same vector becomes the true null flag.  This supplies the actual Xi lift of the arcsine margin
without a reporter, orientation map, or RH assumption.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean certificates below, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Write `H_n(s)=(s_{i+j})_{i,j<n}` and `b_n(s)=(s_{i+n})_{i<n}`.  Whenever
`det H_n(s) != 0`, define

`a_n(s) = -H_n(s)^{-1} b_n(s)`,

`O_n(s;X) = X^n + sum_{j<n} a_n(s)_j X^j`.

For shifted Xi use normalized moments

`t_w(k) = 2 w^(2k+1) / log(w) * Re m_k(w^2)`.

Define dimensionless admission `Q_{n,w}=O_n(t_w)` and source-coordinate admission

`P_{n,w}(X)=w^(-2n) Q_{n,w}(w^2 X)`.

## Paper proof

### 1. Canonical admission is the Hankel solve

For `i<n`, coefficient expansion gives

`L_s(X^i O_n(s)) = b_n(s)_i + (H_n(s)a_n(s))_i = 0`.

The polynomial is monic because its lower summand has degree `<n`.  If another monic degree-`n`
polynomial has these `n` orthogonality equations, subtraction gives `H_n(s)(a-a')=0`; invertibility
forces equality.  Thus `O_n(s)` is the unique monic admission.  If additionally the next block
`H_{n+1}(s)` is singular with terminal-normalized kernel vector, its first `n` rows are exactly
the displayed equations, so that null polynomial equals `O_n(s)`.  Admission is therefore defined
before flatness and specializes to the true null flag at flatness.

### 2. Fixed-degree Xi coefficients converge

The corpus theorem

`t_w(k) -> c_k := normalizedCentralBinom(k)`

holds for every fixed `k`.  Hence every entry of `H_n(t_w)` and `b_n(t_w)` converges to the
corresponding entry for `c`.  Corpus arcsine positivity gives `H_n(c).PosDef`, hence
`det H_n(c)>0`.  Matrix inversion is continuous at every nonsingular real matrix, so

`a_n(t_w) -> a_n(c)` coordinatewise.

The shifted monic Chebyshev polynomial

`A_n(X)=2^(1-2n) T_n(2X-1)`

is monic for `n>0`.  Chebyshev orthogonality under the arcsine bridge makes it orthogonal to every
polynomial of degree `<n`; uniqueness from Step 1 therefore gives `O_n(c)=A_n`.  Consequently
`Q_{n,w}->A_n` coefficientwise.  Positivity is open, so `H_n(t_w)` is invertible eventually and
the solve is the genuine unique Xi admission there.

### 3. Exact mass-dilation source identity

Let `S(A)=(X A)(X (X A'+A))`, the corpus adaptive shear.  Direct differentiation gives, for
`P(X)=w^(-2n)Q(w^2X)` and `w!=0`,

`S(P)(X)=w^(-4n-4) S(Q)(w^2X)`.

Since `t_w(k)=(2w/log w) w^(2k) s_w(k)`, coefficient expansion yields

`L_{t_w}(S(Q)) = (2w/log w) L_{s_w}(S(Q)(w^2X))`.

The literal source law already formalized in the corpus is

`Source(w,P)=2 L_{s_w}(S(P))`.

Combining the three exact identities gives

`w^(4n+5)/log(w) * Source(w,P_{n,w}) = L_{t_w}(S(Q_{n,w}))`              (w>1).

This is source-first and admission-sensitive: `Q_{n,w}` is chosen from Xi moments before the
bilinear landing and before reflection/source aggregation.

### 4. Adaptive source converges to exact positive margin

For fixed `n`, `S(Q)` has degree at most `2n+2`, and each of its finitely many coefficients is a
polynomial expression in the coefficients of `Q`.  Therefore coefficientwise convergence
`Q_{n,w}->A_n`, together with `t_w(k)->c_k`, implies

`L_{t_w}(S(Q_{n,w})) -> L_c(S(A_n))`.

The latter value is already proved exactly in Lean:

- `11/64` for `n=1`;
- `2^(2-4n)(8n+3)/16` for `n>=2`.

Both are strictly positive.  Thus for every fixed `n>0`, the literal adaptive Xi arithmetic
source selected by canonical admission is eventually strictly positive.

### 5. Sharp obstruction exposed

The margins equal `(2n+3/4)16^(-n)` for `n>=2` and tend to zero.  Hence fixed-degree convergence
cannot be diagonalized into a degree-uniform sign theorem without a quantitative relation between
Xi moment error, inverse-Hankel conditioning, and degree.  Remaining §9.3 core is precisely this
degree-escape estimate, not construction of another source or orientation.

`[PROVED HERE]`

## Door passport

- **Input purity:** shifted-Xi reciprocal moments, normalized Hankel blocks, existing literal
  rational-Gamma minus von-Mangoldt source identity, arcsine positivity/orthogonality.
- **No circularity:** no zero-location statement, RH hypothesis, fixed reporter, or post-aggregate
  classifier.
- **Exact output:** canonical admission, boundary specialization, exact dilation identity, fixed-
  degree positive arithmetic-source recession, and sharp degree-escape obstruction.

## Lean certificate

- Generic canonical monic admission and uniqueness:
  `GaloisForLFunctions.HTGeometry.MonicMomentAdmission`
- Shifted-arcsine identification and fixed-degree Xi coefficient recession:
  `GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionRecession`
- Exact source-coordinate dilation, scaled literal-source recession, exact margins, and eventual
  positivity:
  `GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSourceRecession`
- Capstones:
  `HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal`,
  `HTGeometry.tendsto_monicMomentAdmissionPolynomial_coeff`,
  `RHTower.XiShiftedCanonicalAdmission.monicMomentAdmissionPolynomial_normalizedCentralBinom_eq_amplitude`,
  `RHTower.XiShiftedCanonicalAdmission.scaled_arithmeticSource_sourceCoordinateDilation`,
  `RHTower.XiShiftedCanonicalAdmission.tendsto_scaled_canonicalArithmeticSource`, and
  `RHTower.XiShiftedCanonicalAdmission.canonicalArithmeticSource_eventually_pos`.
- Verification: direct `lake env lean` checks passed; targeted
  `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSourceRecession` passed;
  axiom audit reports only `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-11 — created directly in `1-in-progress`; dependency-closed paper proof completed.
- 2026-08-11 — formalized full fixed-degree producer law and source recession; targeted build and
  axiom audit passed; moved to `3-formalized`.
