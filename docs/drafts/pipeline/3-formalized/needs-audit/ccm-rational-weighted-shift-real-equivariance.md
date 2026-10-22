# Rational CCM weighted shifts are Real-equivariant

- **ID:** `ccm-rational-weighted-shift-real-equivariance`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), novelty needs audit
- **Source:** `kreal-quaternionic-ccm-cokernel` · analytic restriction lane
- **Statement:** every bounded rational CCM monomial acts on the actual Morita Hilbert fiber as
  a bounded weighted shift, and quaternionic operator conjugation is exactly the source
  sign-reflection twist.

## Setup

Let \(H=\ell^2(\mathbb Q^\times)\), let
\[
  (J\xi)(q)=\operatorname{sgn}(q)\overline{\xi(-q)},
\]
and let \(k\in\mathbb Q^\times\). For a bounded coefficient
\(a:\mathbb Q^\times\to\mathbb C\), define
\[
  (W_{a,k}\xi)(q)=a(q)\xi(k^{-1}q).                       \tag{1}
\]
Define its Real-twisted coefficient by
\[
  a^{\alpha,k}(q)=\operatorname{sgn}(k)\overline{a(-q)}.  \tag{2}
\]

For the CCM matrix associated to a source monomial \(f_kU_k\) and base point \(b\),
\(a(q)=f_k(qb)\), so (1) is exactly the operator represented by
\(M_b(x,y)=f_k(xb)\) when \(k=xy^{-1}\).

## Theorem

`[PROVED HERE]`

1. Rational left scaling \(L_k\xi(q)=\xi(k^{-1}q)\) is unitary.
2. If \(\|a(q)\|\le C\) for all \(q\), then \(W_{a,k}\) is bounded and
   \[
     \|W_{a,k}\|\le C.                                    \tag{3}
   \]
3. Quaternionic operator conjugation satisfies
   \[
     \alpha(W_{a,k})=W_{a^{\alpha,k},k}.                  \tag{4}
   \]
4. The twisted coefficient has the same uniform bound as \(a\).

Consequently the rational CCM restriction map is Real-equivariant on every bounded monomial
as an equality of actual bounded operators on the single Hilbert fiber, not merely as a formal
kernel identity.

## Proof

Multiplication by \(k^{-1}\) permutes \(\mathbb Q^\times\), hence preserves the \(\ell^2\)-sum
and proves claim 1. Pointwise,
\[
  \|a(q)\xi(k^{-1}q)\|\le C\|\xi(k^{-1}q)\|.
\]
Comparison in \(\ell^2\), followed by claim 1, proves (3).

For claim 3, direct substitution gives
\[
\begin{aligned}
  (\alpha(W_{a,k})\xi)(q)
   &=-\operatorname{sgn}(q)\,
      \overline{a(-q)(J\xi)(-k^{-1}q)}\\
   &=\operatorname{sgn}(k)\overline{a(-q)}\,
      \xi(k^{-1}q),
\end{aligned}
\]
because
\(\operatorname{sgn}(-k^{-1}q)
  =-\operatorname{sgn}(k)\operatorname{sgn}(q)\).
This is (4). Since sign and conjugation have norm one and negation permutes indices, claim 4
follows.

## Hostile audit

- Boundedness alone does not imply trace class. For the completed CCM target one must prove
  rapid trace-norm decay of the actual Bruhat--Schwartz orbit coefficient.
- This theorem is degree zero. Tensorwise cyclic propagation is supplied separately by the
  proved cyclic-word theorem.
- No completed adelic tensor product, bornology, spectrum, positivity, or RH premise appears.

## Strongest positive survivor

The kernel-level Real identity has upgraded to the actual bounded-operator representation.
Remaining analytic input is now precise: prove that every CCM Bruhat--Schwartz monomial orbit
\(q\mapsto f_k(qb)\) lies in the trace ideal with strongly-Schwartz dependence on \(b\).

## Gates

- [x] exact weighted-shift conjecture
- [x] dependency-closed paper proof
- [x] formalized in Lean 4; minimal check, cached leaf build, and foundational axiom audit pass
- [ ] connect actual Bruhat--Schwartz orbit coefficients to trace class

## Lean realization

Module:

- `GaloisForLFunctions.RHTower.CCM.CCMRationalWeightedShiftReal`

Capstones:

- `ccmRationalMoritaHilbertLeftScaleIsometry`;
- `ccmRationalMoritaWeightedShiftFunction_memℓp`;
- `ccmRationalMoritaWeightedShift_norm_le`;
- `ccmRationalMoritaCoefficientRealTwist_bound`;
- `ccmRationalMoritaWeightedShift_real_equivariant`.

## Sources

- Connes--Consani--Marcolli, *The Weil proof and the geometry of the adeles class space*,
  arXiv:math/0703392, rational Morita matrix formula.

## Log

- 2026-07-25 — extracted after target trace-norm Real isometry was formalized. No numerical
  evidence and no RH assumption used.
- 2026-07-25 — formalized on the actual \(\ell^2(\mathbb Q^\times)\) fiber. Minimal
  `lake env lean`, final cached leaf `lake build`, and capstone axiom audit passed; dependencies
  are only `propext`, `Classical.choice`, and `Quot.sound`.
