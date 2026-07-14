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

## Exact static kernel behind the purity

The paper theorem
[`prime-arch-bernstein-legendre-double-source-kernel.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-legendre-double-source-kernel.md)
adds a non-dynamical realization of the same `Pi_M`.  For any moment functional `L_m`,

\[
 \sum_{M\ge0}\Pi_Mt^M
 =(L_m\otimes L_m)
 \frac1{\sqrt{1-2t(1-x-y+2xy)+t^2(1-x-y)^2}}.
\]

This packages all finite Loschmidt purities into one algebraic constraint and exhibits the exact
simultaneous complement reflection `(x,y) -> (1-x,1-y)`.  The source-side continuation target and
its Pringsheim-to-RH splice are recorded in
[`prime-arch-bernstein-reflected-kernel-collar.md`](../../1-in-progress/prime-arch-bernstein-reflected-kernel-collar.md)
and
[`prime-arch-bernstein-pringsheim-collar-transfer.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-pringsheim-collar-transfer.md).

The one-source companion
[`prime-arch-bernstein-mobius-pullback-gutzmer-law.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-mobius-pullback-gutzmer-law.md)
packages all degree pencils as a Möbius pullback of `normalizedPrimeArchMomentGerm` and obtains the
complete Abel susceptibility by a second Gutzmer average.  It is the static source formula behind
the finite Loschmidt dephasing in this card.
