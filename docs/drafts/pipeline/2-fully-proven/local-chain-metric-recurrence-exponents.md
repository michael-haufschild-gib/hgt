# Sharp metric recurrence exponents for generic local quantum chains

- **ID:** `local-chain-metric-recurrence-exponents`
- **Stage:** 2-fully-proven
- **Type:** PAPER-PROVED BRIDGE / FIRST-RETURN LAW
- **Source:** open core I.5 of
  `../1-in-progress/temporal-codimension-interaction-law.md`
- **Scientific status:** `[PAPER-PROVED USING PUBLISHED METRIC THEOREM] [PRIORITY OPEN]`
- **Imported theorem:** Kleinbock--Margulis extremality of analytic
  nondegenerate manifolds

## Main theorem

Let \(\mathcal L_{P_n}\) be the full real space of traceless one-site and
nearest-neighbour two-site Hamiltonians on an open chain of \(n\geq2\)
qubits. Put
\[
 D=2^n,\qquad d=D-1.
\]
For a simple-spectrum Hamiltonian, order the eigenvalues and define its
projective gap vector
\[
 g(H)=(E_2-E_1,\ldots,E_D-E_1)\in\mathbb R^d.       \tag{1}
\]

For Lebesgue-almost every \(H\in\mathcal L_{P_n}\), the following limits
hold.

For integer-time sampling, let
\[
 T_H^{\rm disc}(r)
 =
 \min\left\{
 k\geq1:
 \left\|k\,\frac{g(H)}{2\pi}\right\|_{\mathbb T^d}<r
 \right\}.                                           \tag{2}
\]
Then
\[
 \boxed{
 \lim_{r\downarrow0}
 \frac{\log T_H^{\rm disc}(r)}{\log(1/r)}
 =d=2^n-1.
 }                                                    \tag{3}
\]

For continuous time, use the first gap as a Poincaré clock and put
\[
 \alpha(H)
 =
 \left(
 \frac{E_3-E_1}{E_2-E_1},\ldots,
 \frac{E_D-E_1}{E_2-E_1}
 \right)\in\mathbb R^{d-1}.                           \tag{4}
\]
Define the first return after at least one winding of that clock by
\[
Q_H(r)
 =
 \min\{q\geq1:\|q\alpha(H)\|_{\mathbb T^{d-1}}<r\}.
                                                               \tag{5}
\]
Define
\[
 T_H^{\rm cont}(r)
 =
 \inf\left\{
 t\geq\frac{\pi}{E_2-E_1}:
 \left\|t\,\frac{g(H)}{2\pi}\right\|_{\mathbb T^d}<r
 \right\}.                                            \tag{5a}
\]
For sufficiently small \(r\), this lower cutoff excludes only the initial
departure near \(t=0\) and forces at least one winding of the Poincaré clock.
The corresponding physical time differs from
\(2\pi Q_H(r)/(E_2-E_1)\) by \(O_H(r)\). Hence
\[
 \boxed{
 \lim_{r\downarrow0}
 \frac{\log T_H^{\rm cont}(r)}{\log(1/r)}
 =d-1=2^n-2.
 }                                                    \tag{6}
\]

If recurrence accuracy is measured by any reporter deficit with a
nondegenerate quadratic minimum at the return point, then phase radius
\(r\asymp\sqrt\varepsilon\). Therefore
\[
 \boxed{
 \lim_{\varepsilon\downarrow0}
 \frac{\log T_H^{\rm disc}(\varepsilon)}
      {\log(1/\varepsilon)}
 =\frac{2^n-1}{2},
 \qquad
 \lim_{\varepsilon\downarrow0}
 \frac{\log T_H^{\rm cont}(\varepsilon)}
      {\log(1/\varepsilon)}
 =2^{n-1}-1.
 }                                                    \tag{7}
\]

Thus generic local-chain first recurrence has an exact exponent, not only a
volume-density law or worst-case upper bound.

## Lemma 1 — extremality gives an exact first-hit exponent

For \(\beta\in\mathbb R^m\), let
\[
 N_\beta(r)=\min\{q\geq1:\|q\beta\|_{\mathbb T^m}<r\}.
                                                               \tag{8}
\]
If the simultaneous Diophantine exponent of \(\beta\) is \(1/m\), then
\[
 \lim_{r\downarrow0}
 \frac{\log N_\beta(r)}{\log(1/r)}=m.                \tag{9}
\]

### Proof

Simultaneous Dirichlet approximation gives
\[
 N_\beta(r)\leq C_m r^{-m}
 \]
for all sufficiently small \(r\), which proves the limsup bound.

Fix \(\eta>0\). Diophantine exponent \(1/m\) says that only finitely many
\(q\) satisfy
\[
 \|q\beta\|_{\mathbb T^m}<q^{-1/m-\eta}.
 \]
For small \(r\), put \(q=N_\beta(r)\). Then
\[
 q^{-1/m-\eta}\leq\|q\beta\|_{\mathbb T^m}<r,
 \]
and hence
\[
 q>r^{-1/(1/m+\eta)}.
 \]
Letting \(\eta\downarrow0\) gives the liminf bound \(m\). ∎

## Lemma 2 — the local spectral manifold is nondegenerate

On a simple-spectrum chart, regard the centered ordered spectrum as an
analytic map
\[
 F:\mathcal L_{P_n}\longrightarrow
 W=\{x\in\mathbb R^D:\sum_jx_j=0\}.                  \tag{10}
\]
The endpoint-extension theorem proves that on one such chart there is no
constant real affine relation among the eigenbranches except trace.
Consequently the positive-order derivatives of \(F\), up to some finite
order, span \(W\) at some point: otherwise a nonzero covector annihilating
their span would make its pairing with \(F\) locally constant and hence give
an affine branch relation.

This witness can be globalized without choosing an eigenvalue ordering.
Choose finitely many parameter multiindices whose derivative columns span
\(W\) at the witness. Form a maximal minor for one eigenvalue labeling and
multiply its squared value over all \(D!\) labelings. Derivatives of simple
roots are rational functions of the characteristic coefficients and the
discriminant. After multiplication by a sufficiently high discriminant
power, this symmetrized product is a polynomial in the local Hamiltonian
parameters. It is nonzero at the witness. Its zero set is therefore null.

Outside that null set, \(F\) is nondegenerate in the metric-Diophantine
sense. Invertible linear coordinates on \(W\) show that the gap map \(g\) is
nondegenerate. Projectivization on \(E_2-E_1\neq0\) shows that the ratio map
\(\alpha\) is also nondegenerate: an affine relation among its coordinates
would become a linear relation among the gap branches.

## Lemma 3 — metric extremality applies

Kleinbock and Margulis prove that almost every point, with respect to the
parameter measure on an analytic nondegenerate manifold in \(\mathbb R^m\),
has simultaneous Diophantine exponent \(1/m\):

- D. Kleinbock and G. Margulis, *Flows on homogeneous spaces and
  Diophantine approximation on manifolds*, Annals of Mathematics 148 (1998),
  339--360,
  [journal](https://annals.math.princeton.edu/articles/12997).

Apply this theorem to \(g/(2\pi)\in\mathbb R^d\) and to
\(\alpha\in\mathbb R^{d-1}\). Lemma 1 gives `(3)` and the winding-number
form of `(6)`.

## Lemma 4 — winding number equals continuous return time

If all projective phases are within \(r\) of the identity and \(r\) is
small, then
\[
 t(E_2-E_1)=2\pi q+O(r)
\]
for a unique integer \(q\). Substitution in the remaining phases gives
\[
 \|q\alpha(H)\|_{\mathbb T^{d-1}}=O_H(r).
 \]
Conversely, an \(r\)-approximation in `(5)` evaluated at
\(t=2\pi q/(E_2-E_1)\) returns every projective phase within \(O_H(r)\).
The fixed multiplicative constants and the \(O_H(r)\) time correction do
not change a logarithmic exponent. This proves `(6)`.

For a smooth reporter deficit with positive-definite Hessian on the minimal
temporal hull, compactness and Taylor expansion give
\[
 c_H\,\operatorname{dist}(z,0)^2
 \leq Q_H(z)
 \leq C_H\,\operatorname{dist}(z,0)^2
 \]
near the return point. Replacing \(r\) by \(\sqrt\varepsilon\) proves `(7)`.
∎

## What this closes

1. Long-time return density and first return are now separate proved laws.
2. The continuous exponent loses exactly one phase dimension because time
   itself supplies one winding direction.
3. Static nearest-neighbour locality attains the exponent associated with the
   full projective Hilbert dimension.
4. The result is typical in physical coupling space, not in an unrestricted
   random-matrix ensemble.

## Hostile boundary

1. The theorem is almost-everywhere, not a uniform bound for every local
   Hamiltonian.
2. Constants and finite-resolution crossover times remain Hamiltonian
   dependent.
3. Translation-invariant low-parameter families require a separate
   nondegeneracy proof.
4. Continuous spectra, thermodynamic limits and open-system contraction are
   not covered by this finite-chain theorem.
5. Formalization requires a first-principles development of the imported
   metric extremality theorem or a formally proved replacement; no manuscript
   claim is authorized before that dependency is closed.

## Gates

- [x] exact Diophantine-to-first-return lemma
- [x] local spectral nondegeneracy bridge on paper
- [x] discrete exponent
- [x] continuous transverse exponent
- [x] quadratic-deficit conversion
- [ ] exact-object priority audit
- [ ] specialist audit of algebraic symmetrization
- [ ] formal metric-Diophantine dependency
