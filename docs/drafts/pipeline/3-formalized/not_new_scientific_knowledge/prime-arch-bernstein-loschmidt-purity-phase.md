# Prime--archimedean Bernstein Loschmidt purity phase

- **ID:** `prime-arch-bernstein-loschmidt-purity-phase`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SOURCE--TEMPERATURE BRIDGE
- **Scientific status:** `[PROVED HERE]`

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
\forall r>1,\qquad \frac{\Pi_M}{r^M}\longrightarrow0.
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
Loschmidt purity.  The exact equivalence and dephasing identity are proved; establishing the
zero-rate side unconditionally would prove RH.

## Gates

- [x] coefficient \(\ell^1\)--\(\ell^2\) inequalities
- [x] subexponential purity iff subexponential total variation
- [x] real Cayley phases have unit norm and are injective
- [x] exact finite Cesaro mean-square identity
- [x] RH equivalence
- [x] narrow Lean check and axiom audit
- [x] manuscript integration

## Formal certificate

- `subexponentialSquareEnergy_iff_l1`
- `tendsto_bernsteinCoefficientLoschmidtAmplitude_cesaro_norm_sq`
- `tendsto_primeArchEndpointBernsteinLoschmidtAmplitude_cesaro_norm_sq`
- `riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential`

The declarations use only the standard foundations `propext`, `Classical.choice`, and
`Quot.sound`.
