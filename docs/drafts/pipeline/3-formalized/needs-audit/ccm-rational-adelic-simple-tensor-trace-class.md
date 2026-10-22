# Rational adelic algebraic Bruhat tensors give trace-class CCM weighted shifts

- **ID:** `ccm-rational-adelic-simple-tensor-trace-class`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `ccm-rational-archimedean-schwartz-lattice`,
  `ccm-rational-finite-adele-denominator`, and
  `ccm-rational-weighted-shift-trace-class`
- **Statement:** every algebraic tensor in
  \(\mathcal S(\mathbb R)\otimes\mathcal S(\mathbb A_{\mathbb Q,f})\) has an
  \(\ell^1(\mathbb Q^\times)\) orbit at every finite idele and nonzero archimedean base; its
  rational CCM monomial is trace class.

## Theorem

Let
\[
  t\in\mathcal S(\mathbb R,\mathbb C)\otimes_{\mathbb C}
    \mathcal S_c^{\mathrm{lc}}(\mathbb A_{\mathbb Q,f}),
\]
let \(b_\infty\in\mathbb R^\times\), and let
\(b_f\in\mathbb A_{\mathbb Q,f}^{\times}\). Evaluation of \(t\) gives
\[
  a_t(q;b)=t(qb_\infty,qb_f),\qquad q\in\mathbb Q^\times.
\]
Then
\[
  \sum_{q\in\mathbb Q^\times}|a_t(q;b)|<\infty.
\]
For every \(k\in\mathbb Q^\times\), the corresponding weighted shift
\[
  (W_{t,b,k}\xi)(q)=a_t(q;b)\xi(k^{-1}q)
\]
on \(\ell^2(\mathbb Q^\times)\) is trace class.

## Proof

First take a pure tensor \(f_\infty\otimes\phi_f\). Right multiplication by the finite idele
\(b_f\) is a homeomorphism of the finite adele ring, so
\(\phi_f(\,\cdot\,b_f)\) remains locally constant and compactly supported. It is globally
bounded by some \(C\).

Common-denominator confinement supplies a nonzero \(d\in\mathbb Z\) such that
\[
  \phi_f(qb_f)\ne0\Longrightarrow dq\in\mathbb Z.
\]
The supported rationals therefore inject into \(\mathbb Z\) via \(q\mapsto dq\). On this
support,
\[
  |f_\infty(qb_\infty)\phi_f(qb_f)|
  \le C\left|f_\infty\!\left(\frac{b_\infty}{d}(dq)\right)\right|.
\]
Since \(b_\infty/d\ne0\), the archimedean lattice theorem makes the right-hand sequence
summable. Extension by zero gives summability over all \(\mathbb Q\), hence over
\(\mathbb Q^\times\).

Every element of the algebraic tensor product is a finite sum of pure tensors. The orbit
evaluation is bilinear, and absolute summability is closed under finite addition, so tensor
induction proves the result for arbitrary \(t\). The previously proved \(\ell^1\)-coefficient
criterion then makes every \(W_{t,b,k}\) trace class.

## Hostile audit

- This covers the complete algebraic tensor product, not only one pure tensor.
- It is fixed-base trace class. It does not yet prove continuity or strong-Schwartz decay as
  \(b\) varies.
- It does not construct the LF completion of adelic Bruhat--Schwartz space or extend the
  restriction map continuously to that completion.
- No rearrangement, numerical computation, Poisson formula, zero spectrum, positivity, or RH
  premise is used.

## Strongest positive survivor

The actual rational CCM restriction formula is now trace-class-valued on the full algebraic
Bruhat tensor core. Remaining analytic issue is parameter-uniform seminorm control and
continuity needed for CCM's strongly-Schwartz completed target.

## Gates

- [x] exact conjecture
- [x] dependency-closed paper proof
- [x] formalize in Lean 4
- [ ] prove strong-Schwartz base-parameter estimates
- [ ] extend through the LF/completed Bruhat--Schwartz source

## Lean realization

- **Module:**
  `GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicBruhatSimpleTensorTraceClass`
- **Capstones:**
  - `ccmRationalAdelicBruhatPureTensorOrbit_summable`
  - `ccmRationalAdelicBruhatTensorOrbit_summable`
  - `ccmRationalAdelicBruhatTensorOrbitCoefficient_summable`
  - `ccmRationalAdelicBruhatTensorWeightedShift_isTraceClass`
- **Verification:** direct `lake env lean` check, cached leaf-module build, and `#print axioms`
  audit passed. Every capstone depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.

## Log

- 2026-07-25 — combined finite-adele denominator confinement, archimedean lattice decay, and the
  Hilbert--Schmidt factorization to prove fixed-base trace class on the full algebraic tensor
  core; no computation or RH input used.
- 2026-07-25 — formalized pure-tensor summability, tensor-product induction, the actual
  \(\mathbb Q^\times\) coefficient, and its trace-class weighted shift in Lean.
