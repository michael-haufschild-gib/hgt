# Rectangular quaternionic Hodge atom

- **ID:** `deninger-rectangular-quaternionic-hodge`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/Deninger program.md` · `deninger-rectangular-isogeny-half-density`
- **Statement:** Complexified moving rectangular tangent planes carry a canonical positive
  anti-linear Hodge operator with square \(-1\); centered moving-modulus maps are unitary Hodge
  intertwiners.

## Goal

Upgrade the divisor-free rectangular weight-one source to the local \(K_{\mathbb R}\)-odd Hodge
object required by Deninger's arithmetic \(H^1\).  This is a local theorem.  It does not assert
global prime-packet selection, Steinberg descent, Gamma compactification, or comparison with the
Xi cohomology carrier.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement and hostile boundary recorded
- [x] 1 → 2 fully-proven: complete proof below
- [ ] 2 → 3 formalized: exact theorem in
  `DeningerArithmeticRectangularQuaternionicHodge.lean`
- [ ] 3 → 4 publication-ready

## Exact theorem

For \(r>0\), let \(V_r=\mathbb C^2\) and define
\[
  J_r(z,w)=(-rw,z/r),\qquad
  \kappa(z,w)=(\overline z,\overline w),\qquad
  \star_r=J_r\kappa .
\]
Give \(V_r\) the positive quadratic energy
\[
  \| (z,w)\|_r^2=\frac{|z|^2}{r}+r|w|^2.
\]
For \(q>0\), put
\[
  A_q(z,w)=(qz,w).
\]
Then:

1. \(\star_r\) is anti-linear and \(\star_r^2=-1\);
2. \(\|\star_r v\|_r^2=\|v\|_r^2\), and the energy is positive definite;
3. \(A_q\star_r=\star_{qr}A_q\);
4. \(\|A_qv\|_{qr}^2=q\|v\|_r^2\);
5. for the centered map \(U_q=q^{-1/2}A_q\),
   \[
     U_q\star_r=\star_{qr}U_q,\qquad
     \|U_qv\|_{qr}^2=\|v\|_r^2;
   \]
6. \(U_{q_1}U_{q_2}=U_{q_1q_2}\).

Thus each local prime map \(r\mapsto pr\) has an uncentered weight-one action and a centered
unitary action.  Its infinitesimal generator has the formal decomposition
\(\Theta=\tfrac12+S\), with \(S\) skew on the centered local Hodge carrier.

## Proof

Because \(J_r\) has real coefficients, it commutes with coefficient conjugation.  The real
rectangular theorem gives \(J_r^2=-1\), hence
\[
  \star_r^2=J_r\kappa J_r\kappa=J_r^2\kappa^2=-1.
\]
For \(a\in\mathbb C\),
\[
  \star_r(av)=J_r(\overline a\,\kappa v)
    =\overline a\,\star_r(v),
\]
so \(\star_r\) is anti-linear.

Writing \(v=(z,w)\),
\[
\begin{aligned}
  \|\star_r v\|_r^2
   &=\frac{|-r\overline w|^2}{r}
      +r\left|\frac{\overline z}{r}\right|^2\\
   &=r|w|^2+\frac{|z|^2}{r}
    =\|v\|_r^2.
\end{aligned}
\]
Both summands are nonnegative and, since \(r>0\), their sum vanishes exactly when \(z=w=0\).

The already proved real rectangular identity \(A_qJ_r=J_{qr}A_q\), together with
\(A_q\kappa=\kappa A_q\) for real \(q\), gives
\[
  A_q\star_r=\star_{qr}A_q.
\]
Directly,
\[
  \|A_q(z,w)\|_{qr}^2
   =\frac{q^2|z|^2}{qr}+qr|w|^2
   =q\|v\|_r^2.
\]
Multiplying \(A_q\) by the positive real scalar \(q^{-1/2}\) preserves Hodge
intertwining and cancels the factor \(q\) in the energy.  Finally,
\[
  U_{q_1}U_{q_2}
   =(q_1q_2)^{-1/2}A_{q_1q_2}
   =U_{q_1q_2},
\]
using the positive square-root law.  Every dependency is closed.

## Hostile audit

- The anti-linear operator is constructed from local leaf orientation, complex structure, and
  conjugation; no zero of Xi occurs.
- Positivity is pointwise algebra, not Weil positivity transported from the divisor.
- Local conjugation gives an additional real form.  Deninger's theorem
  does not exclude this on the isolated \(\mathbb Q\) object; it excludes
  a real-valued theory functorial over all number fields.  The local odd
  \(K_{\mathbb R}\) operator is therefore admissible for the
  \(\zeta_{\mathbb Q}\)-to-RH path.  A nontrivial
  \(K_{\mathbb R}\)/Steinberg descent twist is still required for the
  all-number-fields extension.
- Centering is not an assumption: the exponent \(1/2\) is forced by the proved weight-one metric
  law.

## Status

`[BRIDGE] [PAPER-PROVED]`.  The local Hodge/purity mechanism is complete.  Remaining arithmetic
theorem is global twisted descent and dense cup-isometric comparison.

## Log

- 2026-07-26 — exact local quaternionic Hodge and centered-unitary laws proved.
