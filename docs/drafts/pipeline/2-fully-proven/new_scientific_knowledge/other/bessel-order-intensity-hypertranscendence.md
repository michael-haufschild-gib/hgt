# Modified-Bessel order and intensity are hypertranscendental

- **ID:** `bessel-order-intensity-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / DIFFERENCE GALOIS THEORY / BLACK-HOLE RESPONSE
- **Statement:** For every real `s > 0`, both `ν ↦ K_ν(s)` and
  `ν ↦ K_ν(s) K_{ν-2}(s)` are hypertranscendental over `ℂ(ν)`.
- **Status:** `[PROVED HERE]` on paper; novelty search found no collision; Lean formalization has
  closed every analytic, recurrence, scalar-annihilator, arbitrary-period progression-growth,
  factorial-growth, rational-Riccati, meromorphic intensity-recovery, and physical-scan obligation.
  The exact Dreyfus higher-order classification theorem remains unformalized, so this card is not
  promoted.

## Theorem

Fix \(s>0\), and write

\[
  y(\nu):=K_\nu(s),\qquad
  I_s(\nu):=K_\nu(s)K_{\nu-2}(s).
\]

Then \(y\) and \(I_s\) are entire functions of \(\nu\), and neither satisfies a nonzero algebraic
differential equation over \(\mathbb C(\nu)\).

The second assertion matters physically: on the line
\(\nu=1+2i\omega/\kappa\),

\[
  \left|K_{1+2i\omega/\kappa}(s)\right|^2
  =K_\nu(s)K_{2-\nu}(s)
  =K_\nu(s)K_{\nu-2}(s),                                  \tag{1}
\]

because \(K_{-\mu}=K_\mu\). Thus the theorem applies directly to intensity, not only phase.

## Complete paper proof

### 1. Entire order dependence, recurrence, and positivity

For \(s>0\),

\[
  K_\nu(s)=\int_0^\infty e^{-s\cosh t}\cosh(\nu t)\,dt.    \tag{2}
\]

The superexponential decay of \(e^{-s\cosh t}\) dominates \(\cosh(\nu t)\) locally uniformly in
\(\nu\). Hence `(2)` defines an entire function of \(\nu\). It is positive for real \(\nu\).
Integration by parts, or the standard modified-Bessel recurrence, gives

\[
  y(\nu+1)=y(\nu-1)+\frac{2\nu}{s}y(\nu).                  \tag{3}
\]

In particular, for real \(\nu>0\),

\[
  y(\nu+1)>\frac{2\nu}{s}y(\nu).                          \tag{4}
\]

### 2. Both functions satisfy rational linear shift equations

Equation `(3)` is already a second-order linear shift equation over \(\mathbb C(\nu)\) for \(y\).
For the product, put

\[
  Z(\nu)=
  \begin{pmatrix}
  y(\nu)^2\\
  y(\nu)y(\nu-1)\\
  y(\nu-1)^2
  \end{pmatrix},
  \qquad a(\nu)=\frac{2\nu}{s}.
\]

Then

\[
  Z(\nu+1)=
  \begin{pmatrix}
  a(\nu)^2&2a(\nu)&1\\
  a(\nu)&1&0\\
  1&0&0
  \end{pmatrix}Z(\nu),                                    \tag{5}
\]

and the matrix in `(5)` is invertible. Equation `(3)` also gives

\[
  I_s(\nu)
  =y(\nu)^2-\frac{2(\nu-1)}s\,y(\nu)y(\nu-1).              \tag{6}
\]

Therefore \(I_s,\rho I_s,\rho^2 I_s,\rho^3 I_s\), with
\(\rho f(\nu)=f(\nu+1)\), are four rational linear forms on one three-dimensional rational
difference module. They are linearly dependent over \(\mathbb C(\nu)\). Taking a relation of
minimal shift length gives

\[
  a_0 I_s+a_1\rho I_s+\cdots+a_m\rho^m I_s=0,
  \quad a_j\in\mathbb C(\nu),\quad a_0a_m\ne0.             \tag{7}
\]

Thus Dreyfus's scalar theorem applies to both \(y\) and \(I_s\).

### 3. Differential algebraicity would force exponential-polynomial shift growth

Dreyfus proves: if a meromorphic solution \(f\) of a rational linear shift equation is
differentially algebraic over \(\mathbb C(\nu)\), then for some integer \(\ell>0\) and finitely many
\(\lambda_j\in\mathbb C\),

\[
  f\in C_\ell(\nu)
      [e^{\lambda_1\nu},\ldots,e^{\lambda_k\nu}],          \tag{8}
\]

where \(C_\ell\) is the field of \(\ell\)-periodic meromorphic functions.

Choose a real \(\nu_0>2\) avoiding the finitely many coefficient poles and denominator-degeneracy
sets in one representation `(8)`. On the progression \(\nu=\nu_0+\ell n\), every periodic
coefficient is constant. Every rational function over those coefficients has at most polynomial
growth, apart from finitely many denominator zeros, while every exponential monomial has
exponential growth. Consequently there are constants \(C,A>0\) and an integer \(d\) such that,
for all sufficiently large \(n\),

\[
  |f(\nu_0+\ell n)|\le C(1+n)^d A^n.                      \tag{9}
\]

### 4. Exact recurrence forces factorial growth

Iterating `(4)` gives, for every integer \(N\ge1\),

\[
  y(\nu_0+N)>
  y(\nu_0)\left(\frac2s\right)^N(\nu_0)_N.                \tag{10}
\]

This exceeds every polynomial times every fixed exponential: the final \(N/2\) factors in
\((\nu_0)_N\) are each at least \(N/2\). Taking \(N=\ell n\) contradicts `(9)`. Hence \(y\) is
hypertranscendental.

Applying the same bound separately at \(\nu_0\) and \(\nu_0-2>0\) yields

\[
  I_s(\nu_0+N)>
  I_s(\nu_0)\left(\frac2s\right)^{2N}
  (\nu_0)_N(\nu_0-2)_N.                                  \tag{11}
\]

This has factorial-squared growth and again contradicts `(9)`. Therefore \(I_s\) is
hypertranscendental. This proves the theorem.

## Exact extremal-radiation corollary

For the all-time extremal Reissner--Nordström moving-mirror kernel of Good, fix
\(\kappa>0\), and, for

\[
  0<\omega<\frac{\kappa s}{2},
\]

let

\[
  \omega_p=\omega+\omega',\qquad
  \omega_p(\omega)=\frac{\kappa^2s^2}{4\omega},
  \qquad
  \omega'(\omega)=\frac{\kappa^2s^2}{4\omega}-\omega>0.    \tag{12}
\]

Then the modified-Bessel argument is exactly \(s\), and Good's exact all-time coefficient gives

\[
 |\beta_{\omega\omega'(\omega)}|^2
 = \frac{e^{-2\pi\omega/\kappa}\,\omega'(\omega)}
        {\pi^2\kappa^2\omega_p(\omega)}
   I_s\!\left(1+\frac{2i\omega}{\kappa}\right).           \tag{13}
\]

The displayed prefactor is nonzero and differentially algebraic on this interval, while its
Bessel intensity is `(1)`.
Nonzero affine substitution and multiplication or division by a nonzero differentially algebraic
function preserve differential transcendence. Therefore the calibrated intensity scan in
`(12)`--`(13)` is hypertranscendental over \(\mathbb C(\omega)\) (equivalently, it satisfies no
algebraic differential equation on any nonempty open subinterval of the displayed domain).

Here \(\kappa=1/(2M)\) is the scale used in the extremal moving-mirror model; it is not the physical
surface gravity, which vanishes.

## Novelty and scope

Targeted searches across arXiv, zbMATH-indexed results, order-derivative literature, Bessel
inequality literature, and the internal corpus found no prior differential-transcendence theorem
for \(K_\nu(s)\) as a function of its order, nor for the intensity product \(I_s\). This is a
priority lead, not a conclusive global bibliographic proof.

The physical corollary is exact for the cited \(1+1\)-dimensional moving-mirror reduction. It does
not by itself establish a universal extremality phase transition: full nonextremal RN collapse has
variable-parameter confluent-hypergeometric kernels, and greybody factors, \(3+1\) propagation,
backreaction, and collapse stability remain outside the model.

## Lean obligations

- [ ] Formalize the needed special case of Dreyfus's DA-to-periodic-exponential theorem, with no
  axioms.
- [x] Define order-variable \(K_\nu(s)\) from `(2)` and prove entire dependence, reflection,
  recurrence, and real positivity.
- [x] Formalize the symmetric-square system `(5)` and scalar-annihilator existence `(7)`.
- [x] Formalize periodic-progression rational-exponential upper growth.
- [x] Formalize recurrence lower bounds `(10)`--`(11)` and the growth contradiction.
- [x] Prove affine-change and nonzero-DA-factor preservation for the physical scan.

## Primary sources

- T. Dreyfus, *Hypertranscendence and linear difference equations, the exponential case*,
  Journal of Algebra 686 (2026), 775--792,
  <https://arxiv.org/abs/2212.00388>.
- NIST Digital Library of Mathematical Functions, modified-Bessel integral representation,
  recurrence, and reflection formulas,
  <https://dlmf.nist.gov/10.32#E9>,
  <https://dlmf.nist.gov/10.29#E1>,
  <https://dlmf.nist.gov/10.27#E3>.
- M. R. R. Good, *Extreme Hawking Radiation*, Physical Review D 101, 104050 (2020),
  <https://arxiv.org/abs/2003.07016>.

## Gates

- [x] 0 → 1: exact function, attack, and physical carrier identified.
- [x] 1 → 2: dependency-closed paper proof.
- [ ] 2 → 3: unconditional Lean theorem.
- [ ] 3 → 4: standalone paper and Lean certificate.

## Log

- 2026-07-28 — exact constant-argument extremal intensity scan isolated.
- 2026-07-28 — Dreyfus plus exact recurrence-growth proof closed for \(K_\nu(s)\) and
  \(K_\nu(s)K_{\nu-2}(s)\).
- 2026-07-28 — universal extremality phase interpretation rejected; exact model corollary retained.
- 2026-08-03 — formalized the Schlaefli carrier, entire order dependence, conjugation, reflection,
  strict real positivity, and the exact order recurrence in `BesselOrderIntegral` and
  `BesselOrderRecurrence`.
- 2026-08-03 — formalized the explicit symmetric-square scalar annihilator with nonzero polynomial
  endpoints, formulas `(10)`--`(11)`, exact modulus identity on the physical line, and exclusion of
  every rational-exponential progression representation in `BesselOrderIntensityShift`,
  `BesselOrderFactorialGrowth`, `BesselOrderIntensity`,
  `RationalExponentialProgressionGrowth`, and `BesselOrderDreyfusSeam`.
- 2026-08-03 — formal audit isolated one remaining dependency: Dreyfus Theorem 1/Corollary 2 itself
  (parameterized Picard--Vessiot/difference-Galois classification). No corresponding formal theory
  exists in mathlib or this repository; no axiom or conditional substitute was introduced.
- 2026-08-03 — closed the exact meromorphic recurrence and quartic intensity-to-order recovery in
  `BesselOrderMeromorphic`: differential algebraicity of the intensity now forces differential
  algebraicity of the order carrier, so a separate rank-three classification theorem is unnecessary.
- 2026-08-03 — closed the omitted positive-integer-period case in `BesselOrderFactorialGrowth`,
  `BesselOrderIntensity`, and `BesselOrderDreyfusSeam`.  The contradiction now applies to the
  `ell`-period progressions produced by Dreyfus, not only to a unit-step progression.
- 2026-08-03 — proved in `BesselOrderRiccati` that the rank-two order recurrence has no rational
  Riccati solution for every nonzero slope, including `2 / s` for `s > 0`.  Reduced numerator and
  denominator divisibility force a common nonunit factor; the remaining unit case contradicts
  polynomial degree.  This supplies the exact ordinary irreducibility obstruction but does not
  replace the missing parameterized Picard--Vessiot classification.
- 2026-08-03 — closed the exact extremal physical scan in `BesselOrderPhysicalScan`: affine order
  transport, multiplication by the nonzero entire DA Good prefactor, and the physical prefactor
  identity are all Lean-proved.
