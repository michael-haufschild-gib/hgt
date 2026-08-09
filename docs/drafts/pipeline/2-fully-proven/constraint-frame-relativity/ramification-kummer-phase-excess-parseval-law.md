# Ramification Kummer-phase excess and Parseval detection law

- **ID:** `cfr-ramification-kummer-phase-excess`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / SOURCE-ASYMMETRIC SECOND OBSERVER / PRO-TORIC KUMMER CHART
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE-ASYMMETRIC] [KUMMER-GRADED] [FOURIER-PARSEVAL DETECTION] [COMPOSITION-COMPATIBLE] [FLAT] [BRIDGE] [NOT FIELD EQUATION] [NOT RH] [NO LEAN WRITTEN OR BUILT]`
- **Statement:** The strict complement of a ramification power image is exactly the sum of
  nontrivial Kummer valuation-residue sectors. Haar averaging over the compact torsion-phase
  group extracts the inherited image, while Parseval gives a positive quantitative detector of
  analytic excess and finite-aperture two-sided loss bounds.

## Goal

Construct a second observer that is nonzero on the marked split-defect kernel `K_r`. Ordinary
prime-diagonal Gibbs, capacity, logit, and recurrence phase live entirely on the power image. The
new observer must be defined from the same source map `P_r`, carry its composition law, and avoid
fitting any RH endpoint.

## 1. Valuation lattice and Kummer quotient

Fix `m>=2` and an integer `r>=2`.

Let

\[
 \Lambda=\bigoplus_{p\in\mathbb P}\mathbb Ze_p,
 \qquad
 \Lambda_+=\bigoplus_{p\in\mathbb P}\mathbb Ne_p,
\tag{KP.1}
\]

and identify an integer `n>=1` with its finite-support valuation vector

\[
 v(n)=(v_p(n))_p\in\Lambda_+.
\]

The power map `P_r(n)=n^r` is multiplication by `r` on `Lambda`. Define

\[
 \mathsf K_r=\Lambda/r\Lambda,
 \qquad
 \Omega_r=\widehat{\mathsf K_r}\cong\prod_p\mu_r,
\tag{KP.2}
\]

with normalized Haar probability measure. For `omega=(omega_p)_p in Omega_r`, set

\[
 \omega(n)=\prod_p\omega_p^{v_p(n)}.
\tag{KP.3}
\]

The product is finite for each integer.

### Theorem 1.1 — intrinsic image/complement grading

For the shell support `A_m={n>=2:max_p v_p(n)=m}`,

\[
 P_r(A_m)=A_{rm}\cap r\Lambda,
\tag{KP.4}
\]

and therefore

\[
 \boxed{
 b_{m,r}(n)=a_{rm}(n)\mathbf1_{[v(n)]_r=0},
 \qquad
 c_{m,r}(n)=a_{rm}(n)\mathbf1_{[v(n)]_r\ne0}.}
\tag{KP.5}
\]

### Proof

An integer is an `r`-th power precisely when every prime valuation is divisible by `r`. If it
also lies in `A_(rm)`, division of all valuations by `r` produces a unique element of `A_m`.
This proves `(KP.4)` and the two characteristic-function identities. `[PROVED HERE]`

Thus the inherited power image is the trivial Kummer sector and the marked split defect is the
sum of all nontrivial sectors.

## 2. Kummer-phase transform

For `Re z>1`, define

\[
 \Phi_{m,r}(z,\omega)
 =\sum_{n\ge1}a_{rm}(n)\omega(n)n^{-z}.
\tag{KP.6}
\]

The series converges uniformly and absolutely in `omega` on every half-plane
`Re z>=1+epsilon`, since its absolute value is bounded termwise by `n^(-Re z)`.

### Theorem 2.1 — Haar extraction of inherited law

For `Re z>1`,

\[
 \boxed{
 \int_{\Omega_r}\Phi_{m,r}(z,\omega)\,d\omega=S_m(rz),}
\tag{KP.7}
\]

and hence

\[
 \boxed{
 C_{m,r}(z)=S_{rm}(z)
 -\int_{\Omega_r}\Phi_{m,r}(z,\omega)\,d\omega.}
\tag{KP.8}
\]

### Proof

Haar character orthogonality gives

\[
 \int_{\Omega_r}\omega(n)\,d\omega
 =\begin{cases}
 1,&[v(n)]_r=0,\\
 0,&[v(n)]_r\ne0.
 \end{cases}
\tag{KP.9}
\]

Uniform absolute convergence permits termwise integration. By `(KP.5)`, the surviving terms are
the power image, and reindexing `n=k^r` gives

\[
 \sum_{k\in A_m}(k^r)^{-z}=S_m(rz).
\]

Subtracting from `S_(rm)(z)` proves `(KP.8)`. `[PROVED HERE]`

This is a second observer of the split defect: the full torsion-phase profile is nonconstant
exactly when nontrivial Kummer sectors are present.

## 3. Parseval excess energy

For real `sigma>1` and `alpha in K_r`, define the nonnegative sector mass

\[
 A_\alpha(\sigma)=
 \sum_{\substack{n\in A_{rm}\\[v(n)]_r=\alpha}}n^{-\sigma}.
\tag{KP.10}
\]

Then

\[
 C_{m,r}(\sigma)=\sum_{\alpha\ne0}A_\alpha(\sigma).
\tag{KP.11}
\]

### Theorem 3.1 — Kummer Parseval detector

Put

\[
 \mathcal V_{m,r}(\sigma)=
 \int_{\Omega_r}
 \left|\Phi_{m,r}(\sigma,\omega)-S_m(r\sigma)\right|^2d\omega.
\tag{KP.12}
\]

Then

\[
 \boxed{
 \mathcal V_{m,r}(\sigma)=\sum_{\alpha\ne0}A_\alpha(\sigma)^2>0,}
\tag{KP.13}
\]

and

\[
 \boxed{
 \sqrt{\mathcal V_{m,r}(\sigma)}\le C_{m,r}(\sigma).}
\tag{KP.14}
\]

### Proof

Grouping `(KP.6)` by residue class gives an absolutely convergent Fourier series on `Omega_r`:

\[
 \Phi_{m,r}(\sigma,\omega)
 =\sum_{\alpha\in\mathsf K_r}A_\alpha(\sigma)\chi_\alpha(\omega).
\]

The trivial coefficient is `A_0(sigma)=S_m(r sigma)` by Theorem 2.1. Parseval proves the equality
in `(KP.13)`. It is strictly positive because `2^(rm)3 in A_(rm)` has nonzero `3`-valuation
modulo `r`. Inequality `(KP.14)` is the elementary `ell^2<=ell^1` inequality for the nonnegative
sector masses. `[PROVED HERE]`

### Corollary 3.2 — finite-aperture inverse-loss bound

Fix a finite prime set `F` of size `d>=2` and restrict all sums to integers supported on `F`.
Then `K_(r,F)=(Z/rZ)^d`, so

\[
 \boxed{
 \sqrt{\mathcal V^F_{m,r}(\sigma)}
 \le C^F_{m,r}(\sigma)
 \le\sqrt{r^d-1}\sqrt{\mathcal V^F_{m,r}(\sigma)}.}
\tag{KP.15}
\]

### Proof

There are at most `r^d-1` nontrivial residue classes. Apply Cauchy--Schwarz to their nonnegative
masses for the upper bound and `ell^2<=ell^1` for the lower bound. Strict positivity follows from
the two-prime witness `p_1^(rm)p_2`. `[PROVED HERE]`

Thus Kummer-phase variance and analytic excess determine one another up to an explicit finite
aperture factor. Ordinary recurrence phase on the pure-prime diagonal has no such property because
it occupies only the trivial residue sector.

## 4. Composition geometry

For positive integers `r,s`, multiplication by `s` and reduction modulo `s` give the exact
sequence

\[
 \boxed{
 0\longrightarrow\Lambda/r\Lambda
 \xrightarrow{\times s}\Lambda/(sr)\Lambda
 \longrightarrow\Lambda/s\Lambda\longrightarrow0.}
\tag{KP.16}
\]

Its Pontryagin dual is

\[
 1\longrightarrow\Omega_s\longrightarrow\Omega_{sr}
 \longrightarrow\Omega_r\longrightarrow1.
\tag{KP.17}
\]

### Theorem 4.1 — outer/transported sector decomposition

The nontrivial `sr`-residue sectors split into:

1. outer sectors already nonzero modulo `s`;
2. transported inner sectors zero modulo `s` but nonzero modulo `sr`.

Under the integer-shell marking this is exactly

\[
 X_{m,sr}=X_{rm,s}\sqcup P_s(X_{m,r}),
\tag{KP.18}
\]

and Haar disintegration along `(KP.17)` realizes the analytic cocycle

\[
 \boxed{
 C_{m,sr}(z)=C_{m,r}(sz)+C_{rm,s}(z).}
\tag{KP.19}
\]

### Proof

Exactness of `(KP.16)` follows directly: multiplication by `s` is injective modulo `sr`, its image
is the kernel of reduction modulo `s`, and reduction is surjective. Pontryagin duality gives
`(KP.17)`. A valuation vector nonzero modulo `sr` is either nonzero modulo `s`, or is `s` times a
vector nonzero modulo `r`. These alternatives are disjoint and prove `(KP.18)`. Reindexing the
second support by `P_s` proves `(KP.19)`; equivalently, apply Fubini to Haar disintegration in the
dual sequence. `[PROVED HERE]`

The full Kummer sector profile therefore carries strict source composition. Its scalar Parseval
energy generally does not satisfy an additive cocycle: squaring after sector aggregation creates
cross-terms. Full graded profile, not one energy scalar, is load-bearing.

## 5. CFR consequence

The source power event now has two exact views of its non-surjective complement:

- marked coefficient/Dirichlet split defect `c_(m,r),C_(m,r)`;
- Kummer torsion-phase profile and its Parseval detector.

The coordinate-free local architecture is a **pro-toric Kummer-graded Adams recollement**:
power image is the trivial sector, excess is the nontrivial sector sum, and composition is governed
by `(KP.16)`. This is a viable exact chart inside Constraint-Frame Relativity, not a replacement
name for the whole field.

It is still flat. Haar transport reproduces the same split composition law, and Fourier inversion
relates the two views. No incompatible comparison, curvature, physical cost, or field equation has
appeared. The next serious test is whether a non-Fourier observer—Stokes contact, orientation, or
boundary flux—carries a nontrivial Kummer sector with a composition law incompatible with this
Haar-flat chart.

## 6. Conjecture / proof / fail loops

1. **Ramification excess is an unnamed analytic remainder.** Failed by `(KP.5)` and `(KP.8)`.
   **Survivor:** it is exactly nontrivial Kummer-phase content.
2. **Ordinary prime recurrence phase detects source asymmetry.** Failed: pure-prime coordinates
   lie in the trivial residue sector. **Survivor:** use torsion phase on all valuation residues.
3. **One scalar phase energy carries composition.** Failed in general by aggregation cross-terms.
   **Survivor:** retain the full Kummer sector profile.
4. **Kummer detection creates curvature.** Failed: Haar disintegration is flat and recovers the
   split cocycle. **Survivor:** use this chart as the flat source-asymmetric baseline.
5. **Nonzero Kummer energy proves hypertranscendence or RH leverage.** Failed: no such implication
   is established. **Survivor:** it proves only exact excess detection and finite inverse-loss.

## 7. Scope and parents

- The analytic theorem is over `C`; algebraic character averaging would require characteristic
  prime to `r`.
- Infinite prime rank produces a compact product/pro-toric object, not a finite-type toric variety.
- Formulas use `Re z>1`; no continuation or zero-free theorem for `C_(m,r)` is proved.
- The exact parents are standard Adams composition, toric power isogenies, Kummer grading, Haar
  Fourier analysis, and Parseval. Their synthesis is used here as source-specific CFR geometry;
  no novelty claim is needed.
- Relevant current parents include Joshua--Pelaez on Adams operations
  ([arXiv:2407.10394](https://arxiv.org/abs/2407.10394)), Hanlon--Hicks--Lazarev on toric
  Frobenius summands ([arXiv:2303.03763](https://arxiv.org/abs/2303.03763)), Raczka on toric
  Frobenius generation ([arXiv:2402.07554](https://arxiv.org/abs/2402.07554)), and Ahlqvist on
  stacky/Kummer covers ([arXiv:2012.10290](https://arxiv.org/abs/2012.10290)).
- No Stokes contact, signed orientation, boundary flux, physical time, Xi condition, or RH theorem
  is asserted.
- No Lean file has been written or built.

## Lean-return notes

- Reuse valuation-vector and torus Kummer membership parents; do not rebuild power membership.
- Formalize finite-aperture character orthogonality before the infinite compact product.
- Keep Parseval at paper level until the finite character transform API is audited.
- No Lean file has been written or built.

## Gates

- [x] intrinsic Kummer grading of power image and complement
- [x] second source-asymmetric observer nonzero on the split defect
- [x] Haar extraction of inherited image
- [x] Parseval excess detector and finite inverse-loss bounds
- [x] strict composition through Kummer exact sequence
- [x] hostile flatness and scalar-energy scope
- [ ] incompatible non-Fourier comparison
- [ ] nonzero curvature/interchange defect
- [ ] withheld Stokes/extension/flux response
- [ ] Lean formalization

## Log

- 2026-08-09 — constructed after wide Adams/plethysm/toric/Kummer audit identified valuation-residue
  phase as the minimal second observer carrying ramification excess.
