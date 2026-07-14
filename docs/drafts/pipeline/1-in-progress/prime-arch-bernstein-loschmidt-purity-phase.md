# Prime--archimedean Bernstein Loschmidt purity phase

- **ID:** `prime-arch-bernstein-loschmidt-purity-phase`
- **Stage:** 1-in-progress
- **Type:** THEOREM / SOURCE--TEMPERATURE BRIDGE
- **Scientific status:** `[CONJECTURE] [LEAN IN DEVELOPMENT]`

## Target

For the endpoint Bernstein masses

\[
a_{M,i}=\ell_s\!\left(\binom MiX^i(1-X)^{M-i}\right),
\qquad
T_M=\sum_{i=0}^M|a_{M,i}|,
\]

define the positive coefficient purity

\[
\Pi_M=\sum_{i=0}^M a_{M,i}^2.
\]

Prove the exact exponential-phase equivalence

\[
\mathrm{RH}
\Longleftrightarrow
\forall r>1,\qquad \frac{\Pi_M}{r^{2M}}\longrightarrow0.
\]

The finite-dimensional norm inequalities

\[
\Pi_M\le T_M^2\le(M+1)\Pi_M
\]

show that this is equivalent to the already proved Bernstein order-unit criterion.  Unlike
\(T_M\), the quantity \(\Pi_M\) is a positive quadratic observable and contains no negative-part
operation.

## Loschmidt realization

Choose any injective family of unit phases \(z_{M,i}\), for example the real Cayley phases

\[
z_{M,i}=\frac{1+\mathrm i i}{1-\mathrm i i}.
\]

The finite amplitude

\[
\mathcal L_M(n)=\sum_{i=0}^M a_{M,i}z_{M,i}^n
\]

then satisfies the exact dephasing law

\[
\frac1K\sum_{n<K}|\mathcal L_M(n)|^2
\longrightarrow \Pi_M.
\]

Thus the remaining RH estimate is equivalently zero exponential rate of a positive long-time
Loschmidt purity.  This is an estimate target, not an assertion that the target has already been
proved.

## Gates

- [ ] coefficient \(\ell^1\)--\(\ell^2\) inequalities
- [ ] subexponential purity iff subexponential total variation
- [ ] real Cayley phases have unit norm and are injective
- [ ] exact finite Cesaro mean-square identity
- [ ] RH equivalence
- [ ] Lean build, axiom audit, and lint
- [ ] manuscript integration
