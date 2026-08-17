# Completed prime--Gamma polynomial even-factorization route to RH

- **ID:** `completed-prime-gamma-polynomial-even-factorization-to-rh`
- **Stage:** 5-failed
- **Type:** `FALSIFIED`
- **Scientific status:** `[PROVED INTERFACE] [LEAN FAR-RIGHT INPUT] [LEAN CLOSED NO-GO] [FALSE PARITY PREMISE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingPolynomialParity.lean`;
  `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMomentFarRightAsymptotic.lean`;
  `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaSecondMomentCenterPositive.lean`

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

Lean formalizes both the finite algebraic passage and the all-order scalar source asymptotic

\[
  \forall k,\qquad
  x^{2k+1}\operatorname{Re}c_k(x)
  \longrightarrow \frac{(-1)^k}{2(2k+1)}.
\]

The proof is source-side.  An improper antitone Riemann-sum theorem gives the exact shifted-power
tail limit; its Hurwitz and polygamma specializations provide the Gamma main term.  The completed
source decomposition then proves that the polar leg has one additional inverse power and the
von Mangoldt leg is exponentially small.  The Lean theorem
`completedOddLogDerivMomentFarRightAsymptotic` discharges the displayed limit unconditionally.

## Top-down chain

The determinant route separately required central nonvanishing because its RH consumer used
strict leading determinants.  The countable quadratic-form consumer only requires nonnegativity.
Consequently a central zero is harmless if its multiplicity is even.

```text
all-order completed-moment far-right asymptotic                           [Lean]
  -> positive far-right anchor for every nonzero integer-polynomial test  [Lean]
  + finite even-multiplicity real factorization on every right segment   [FALSE]
  -> every central integer-polynomial test is nonnegative                 [Lean]
  -> complete countable prime--Gamma source cone                          [Lean]
  -> RH.                                                                  [Lean]
```

The rejected condition is the concrete source statement

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

## Falsification and positive successor

Take `P=X`.  Then `Q_P(x)=c_2(x)`, the second normalized odd completed
logarithmic-derivative moment.  The paper theorem
`completed-prime-gamma-second-moment-four-crossing-law` proves

\[
  c_2(1/2)>0,\qquad c_2(10)<0,\qquad c_2(x)>0
  \quad\text{for all sufficiently large }x.
\]

Thus `c_2` has an odd-multiplicity real zero in `(1/2,10)` and another in `(10,infty)`.
The reflection law supplies two further crossings on the left.  In particular the proposed
right-even factorization already fails for `P=X`; the failure is not confined to a high-degree
determinant or a central zero.  The positive replacement is the four-crossing theorem recorded in
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/completed-prime-gamma-second-moment-four-crossing-law.md`.

## Why this is sharper than the determinant continuation route

- No central nonvanishing theorem is needed.
- No strict determinant inequality is transported.
- The target is countable and scalar.
- A source proof may work test-by-test; it need not control simultaneous eigenvalue crossings of
  every finite Hankel matrix.

## Literature boundary

The generalized Laguerre inequalities provide necessary-and-sufficient real-zero criteria for
appropriate real entire functions, but applying the complete family to the centred Xi function is
already a real-zero selection principle.  They do not control the parity of the real zeros of the
moving differential polynomials `Q_P`.  See Cardon,
[*Extended Laguerre inequalities and a criterion for real zeros*](https://arxiv.org/abs/0911.1122),
and Csordas--Vishnyakova,
[*The generalized Laguerre inequalities and functions in the Laguerre--Polya class*](https://doi.org/10.2478/s11533-013-0269-x).

The unconditional Turan inequalities for Xi coefficients proved by Csordas--Norfolk--Varga are
necessary finite coefficient inequalities, not a source theorem excluding sign-changing zeros of
all `Q_P`; see
[*The Riemann Hypothesis and the Turan Inequalities*](https://doi.org/10.2307/2000378).
Thus the literature supplies comparison criteria but does not repair the false factorization
premise.

## Gates

- [x] moving polynomial test defined in Lean
- [x] exact center value relation
- [x] functional-equation reflection
- [x] Schwarz reality
- [x] abstract even-factor sign transfer allowing a central zero
- [x] chain from the two source inputs to RH
- [x] paper proof of the scalar far-right anchor
- [x] Lean reduction of every polynomial far-right anchor to scalar moment asymptotics
- [x] Lean proof of the all-order scalar completed-moment asymptotic
- [x] source parity premise falsified by the `P=X` two-right-crossing theorem

## Lean no-go closure — 2026-08-15

The falsification no longer depends on a hypothesis. In
`formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaSecondMomentCenterPositive.lean`, Lean now
proves the closed chain

```text
completedEulerMoment_two_ten_lt
  -> completedOddLogDerivMoment_two_ten_re_neg
  -> not_completedOddLogDerivPolynomialRightEvenFactorization.
```

The positive survivor required by the no-go discipline is the quantitative, reusable Euler-source
certificate `completedEulerMoment_two_ten_lt`. It bounds the exact Euler contribution at the test
point without a parity hypothesis, RH, a new axiom, or empirical numerical input. The terminal
module build and `#print axioms` audit pass; the latter reports only `propext`,
`Classical.choice`, and `Quot.sound`.
