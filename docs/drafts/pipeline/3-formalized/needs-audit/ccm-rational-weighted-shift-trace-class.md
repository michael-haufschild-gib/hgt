# An \(\ell^1\) CCM orbit coefficient gives a trace-class weighted shift

- **ID:** `ccm-rational-weighted-shift-trace-class`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `ccm-rational-weighted-shift-real-equivariance`
- **Statement:** a rational CCM weighted shift \(W_{a,k}\) is trace class whenever its orbit
  coefficient \(a:\mathbb Q^\times\to\mathbb C\) is absolutely summable.

## Theorem

Let
\[
  (W_{a,k}\xi)(q)=a(q)\xi(k^{-1}q).
\]
If
\[
  \sum_{q\in\mathbb Q^\times}|a(q)|<\infty,
  \tag{1}
\]
then \(W_{a,k}\) is trace class.

## Proof

Put \(r(q)=\sqrt{|a(q)|}\). Define
\[
  s(q)=
  \begin{cases}
    a(q)/r(q),&a(q)\ne0,\\
    0,&a(q)=0.
  \end{cases}
\]
Then
\[
  s(q)r(q)=a(q),\qquad |s(q)|^2=|r(q)|^2=|a(q)|.
  \tag{2}
\]
By (1), the weighted shifts \(W_{s,1}\) and \(W_{r,k}\) are Hilbert--Schmidt: on the standard
basis,
\[
  \|W_{c,k}\delta_q\|=|c(kq)|,
\]
and multiplication by \(k\) only permutes \(\mathbb Q^\times\). Equation (2) gives
\[
  W_{a,k}=W_{s,1}W_{r,k}.
\]
Thus \(W_{a,k}\) is a product of two Hilbert--Schmidt operators and is trace class.

Absolute summability also gives the uniform coefficient bounds needed to define all three
bounded weighted shifts: each \(|a(q)|\) is at most the sum in (1), and each
\(|r(q)|=|s(q)|\) is at most its square root.

## Hostile audit

- This is a sufficient trace-class criterion, not yet the CCM Bruhat--Schwartz orbit theorem.
- The result does not assert trace-class continuity or strong-Schwartz decay in the base
  parameter \(b\).
- No enumeration, rearrangement, numerical computation, spectrum, positivity, or RH premise is
  used.

## Strongest positive survivor

The completed restriction gap is reduced to an arithmetic Schwartz estimate:
\[
  \sum_{q\in\mathbb Q^\times}|f_k(qb)|<\infty
\]
with strong-Schwartz control in \(b\). Once established, the actual CCM monomial operator is
trace class by this theorem and Real equivariance follows from the separately proved weighted
shift identity.

## Gates

- [x] exact trace-class conjecture
- [x] dependency-closed paper proof
- [x] formalize in Lean 4
- [ ] prove adelic Bruhat--Schwartz orbit summability uniformly in CCM base parameter

## Lean realization

- **Module:** `GaloisForLFunctions.RHTower.CCM.CCMRationalWeightedShiftTraceClass`
- **Capstones:**
  - `ccmRationalMoritaWeightedShift_isHilbertSchmidt`
  - `ccmRationalMoritaCoefficientSqrtPhase_mul_sqrtNorm`
  - `ccmRationalMoritaCoefficientSqrtPhase_summable_sq`
  - `ccmRationalMoritaWeightedShift_isTraceClass_of_summable`
- **Verification:** direct `lake env lean` check, cached leaf-module build, and `#print axioms`
  audit passed. Every capstone depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.

## Log

- 2026-07-25 — derived from the actual weighted-shift representation. No numerical evidence
  and no RH assumption used.
- 2026-07-25 — formalized the Hilbert--Schmidt factorization and trace-class conclusion in Lean
  without `sorry`, `axiom`, numerical computation, or an RH premise.
