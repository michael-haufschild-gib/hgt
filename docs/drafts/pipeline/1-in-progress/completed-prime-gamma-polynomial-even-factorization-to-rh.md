# Completed prime--Gamma polynomial even-factorization route to RH

- **ID:** `completed-prime-gamma-polynomial-even-factorization-to-rh`
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE]`
- **Scientific status:** `[PROVED INTERFACE] [PAPER FAR-RIGHT INPUT] [OPEN CORE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingPolynomialParity.lean`

## Static moving test

For a real polynomial (P), define

\[
  \mathcal Q_P(\sigma)
  =\sum_{k\ge0}[X^k]P(X)^2\,
    \frac{(-1)^k}{(2k+1)!}
    \left(\frac{\xi'}{\xi}\right)^{(2k+1)}(\sigma).
\]

The sum is finite.  Lean proves the exact value and reflection relations

\[
  \mathcal Q_P(1/2)=\operatorname{primeArchSourceTraceHankel}(P),
  \qquad
  \mathcal Q_P(1-\sigma)=\mathcal Q_P(\sigma),
\]

and Schwarz equivariance, so \(\mathcal Q_P(x)\in\mathbb R\) for real \(x\).

## Far-right polynomial anchor

Let (r) be the smallest index with coefficient (a_r\ne0).  The proved moment asymptotic

\[
  x^{2k+1}c_k(x)\longrightarrow \frac{(-1)^k}{2(2k+1)}
\]

implies

\[
  x^{4r+1}\mathcal Q_P(x)
  \longrightarrow \frac{a_r^2}{2(4r+1)}>0.
\]

Indeed, every coefficient of (P^2) below degree (2r) vanishes, its degree-(2r)
coefficient is (a_r^2), and all higher terms decay by at least two additional powers of
\(x\).  Thus every nonzero integer-polynomial test has a positive far-right anchor.  This is
a scalar corollary of the paper proof in
`completed-prime-gamma-hankel-far-right-anchor.md`.

Lean now formalizes the complete finite algebraic passage from the scalar moment limits to this
anchor.  It uses `natTrailingDegree` to isolate the lowest coefficient of `P^2`, proves every
higher term vanishes after scaling, and proves the surviving coefficient is a positive square.
The remaining far-right formalization is therefore only the all-order scalar source asymptotic

\[
  \forall k,\qquad
  x^{2k+1}\operatorname{Re}c_k(x)
  \longrightarrow \frac{(-1)^k}{2(2k+1)}.
\]

The project already proves the all-order polygamma--Hurwitz value identity and the completed-source
jet decomposition; these are the intended inputs for this last analytic step.

## Top-down chain

The determinant route separately required central nonvanishing because its RH consumer used
strict leading determinants.  The countable quadratic-form consumer only requires nonnegativity.
Consequently a central zero is harmless if its multiplicity is even.

```text
all-order completed-moment far-right asymptotic                           [PAPER, OPEN IN LEAN]
  -> positive far-right anchor for every nonzero integer-polynomial test  [Lean]
  + finite even-multiplicity real factorization on every right segment   [OPEN CORE]
  -> every central integer-polynomial test is nonnegative                 [Lean]
  -> complete countable prime--Gamma source cone                          [Lean]
  -> RH.                                                                  [Lean]
```

The open condition is the concrete source statement

\[
\forall P\in\mathbb Z[X]\setminus\{0\},\ \forall R>1/2,
\quad
\mathcal Q_P(x)=
\prod_{z\in Z_{P,R}}(x-z)^{2m_z}\,u_{P,R}(x)
\quad (1/2\le x\le R),
\]

where (Z_{P,R}\subset[1/2,R)) is finite and (u_{P,R}) is continuous and nowhere zero.
This is a divisor-parity constraint, not a positivity assumption: the cofactor may have either
sign before the positive far-right anchor fixes its chamber.

## Why this is sharper than the determinant continuation route

- No central nonvanishing theorem is needed.
- No strict determinant inequality is transported.
- The target is countable and scalar.
- A source proof may work test-by-test; it need not control simultaneous eigenvalue crossings of
  every finite Hankel matrix.

## Gates

- [x] moving polynomial test defined in Lean
- [x] exact center value relation
- [x] functional-equation reflection
- [x] Schwarz reality
- [x] abstract even-factor sign transfer allowing a central zero
- [x] chain from the two source inputs to RH
- [x] paper proof of the scalar far-right anchor
- [x] Lean reduction of every polynomial far-right anchor to scalar moment asymptotics
- [ ] Lean proof of the all-order scalar completed-moment asymptotic
- [ ] source proof of even real-root factorization
