# A finite commuting prime coupling preserves the continuous dilation spectrum

- **ID:** `finite-prime-commuting-dilation-no-point-spectrum`
- **Stage:** 3-formalized
- **Type:** DIRECT HILBERT--PÓLYA SPECTRAL THEOREM / POSITIVE INCIDENCE LAW
- **Scientific status:** `[FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/FinitePrimeCommutingDilationNoPointSpectrum.lean`
- **Statement:** Let the Berry--Keating dilation generator on logarithmic coordinates be coupled to
  finitely many bounded prime translations, with the self-adjoint coefficient pairing. The resulting
  operator is unitarily a multiplication operator by a nonconstant real-analytic function and has
  empty point spectrum. Thus retaining all `pi(N)` prime phases in a commuting finite-prime generator
  does not discretize the clock. A viable Hilbert--Pólya operator must contain a noncommuting
  prime--archimedean incidence or a source-selected boundary/domain mechanism.

## 1. Finite-prime commuting operator

Work on `L2(R,du)`. Let

```text
D=-2i d/du                                                   (1)
```

with its standard self-adjoint domain. For `a in R`, let

```text
(T_a f)(u)=f(u-a).                                           (2)
```

Each `T_a` is unitary and commutes strongly with `D`. Fix a finite prime set `P` and coefficients
`c_p in C`. Define the bounded self-adjoint prime coupling

```text
V_P=sum_(p in P) [c_p T_(log p)+conj(c_p) T_(-log p)],       (3)
H_P=D+V_P.                                                   (4)
```

Since `V_P` is bounded self-adjoint, `H_P` is self-adjoint on `Dom(D)`.

## 2. Exact Fourier diagonalization

Under the unitary Fourier transform,

```text
D -> multiplication by 2t,
T_(log p) -> multiplication by exp(-it log p).              (5)
```

Therefore `H_P` is unitarily equivalent to multiplication by

```text
h_P(t)=2t+sum_(p in P)
  [c_p exp(-it log p)+conj(c_p)exp(it log p)].               (6)
```

The function `h_P` is real-valued and real analytic. Its prime part is bounded:

```text
|h_P(t)-2t|<=2 sum_(p in P)|c_p|.                            (7)
```

Hence `h_P(t)->+infinity` as `t->+infinity` and `h_P(t)->-infinity` as `t->-infinity`; in
particular it is not constant.

## 3. No-point-spectrum theorem

For multiplication by a measurable real function `h` on `L2(R)`, `lambda` is a point eigenvalue
exactly when

```text
measure {t:h(t)=lambda}>0.                                   (8)
```

Indeed, an eigenvector is supported on that level set, and its indicator on a finite-measure part
gives the converse.

For fixed `lambda`, the function `h_P-lambda` is nonzero and real analytic. Its zero set is discrete,
hence countable and Lebesgue-null. By `(8)`,

```text
sigma_point(H_P)=empty.                                      (9)
```

This proves the theorem. The argument uses no smallness assumption on the coefficients and no
genericity assumption on the prime logarithms. Rational independence is relevant to phase rank,
but it is not needed for the spectral exclusion.

## 4. Stronger spectral-type statement

The map `h_P` is proper by `(7)`. Its critical points are discrete unless `h_P'` vanishes
identically, which is impossible because of the linear term. On every interval avoiding those
critical points, change of variables sends Lebesgue measure to an absolutely continuous spectral
measure. The discrete critical set contributes no mass. Thus `H_P` is purely absolutely continuous,
not merely point-spectrum-free.

The no-point conclusion `(9)` is the only part needed for the Hilbert--Pólya verdict.

## 5. Positive Hilbert--Pólya law

At cutoff `N`, the functions

```text
exp(it log p),   p<=N,                                      (10)
```

carry rational phase rank `pi(N)`. The theorem shows that having the correct number of independent
phases is necessary but not sufficient: if those phases enter only through the commuting functional
calculus of the dilation clock, they modify its dispersion relation but do not create states.

Therefore a successful finite-prime approximation must supply at least one of:

1. **Noncommuting incidence:** a source-derived `W_N` with `[D,W_N]!=0` that mixes the dilation and
   prime phase coordinates and gives a discrete operator or determinant.
2. **Boundary/domain discretization:** a closed arithmetic boundary relation not reducible to an
   energy-independent phase condition for the bare first-order derivative.
3. **Singular cofinal limit:** finite operators may use boundary truncations, but their determinants
   must carry zeros at finite stage and converge locally uniformly and zero-preservingly to `Xi`.
4. **Exact global constraint:** an infinite-dimensional self-adjoint realization whose domain
   already contains the prime--archimedean weld and whose secular determinant is `Xi`.

Noncommutativity alone is not a proof; it is the first necessary structural departure from `(3)`.
The operator must additionally cross the compact-resolvent/determinant and logarithmic-boundary gates.

## 6. Completed-connection consequence

The completed `(sigma_p,partial_s)` connection has commuting local generators

```text
[partial_s,sigma_p]=0.                                      (11)
```

Equation `(9)` proves that a standard Hilbert representation in which `partial_s` is the dilation
generator and the `sigma_p` are its commuting translations cannot itself be the point-spectrum
Hilbert--Pólya operator. The positive object must occur one categorical level higher:

```text
not the flat generator sum,
but a noncommuting boundary incidence, holonomy defect,
or source-selected domain of the completed connection.      (12)
```

This sharpens “the object is fixed by a constraint, not propagated by a flow”: the full finite
prime phase module can be present in the flow and the spectrum can still remain purely continuous.

## 7. Boundaries and surviving classes

- An unbounded prime interaction need not be Fourier multiplication and is outside the theorem.
- A nontranslation-invariant potential or boundary condition can create point spectrum.
- A compact interval in `u` has discrete derivative spectrum, but an energy-independent
  self-adjoint boundary phase produces an arithmetic progression, not zeta spacing. An arithmetic
  energy-dependent boundary relation must be realized as a genuine operator extension, not inserted
  as the secular equation.
- Infinite prime sums require separate domain and convergence analysis. If the sum remains a
  measurable function of `D`, the same level-set criterion applies; a point spectrum would require
  positive-measure plateaus, which an analytic finite-stage source does not have.
- CCM, Sonin/prolate, finite-Weil characteristic determinants, and Connes absorption spectra are
  outside the direct point-spectrum claim.

## Scientific status

After Fourier transformation, the result is the elementary spectral theory of multiplication
operators plus the isolated-zero theorem for nonconstant real-analytic functions. It is a useful
Hilbert--Pólya implementation theorem, but it is not new scientific knowledge.

## Gates

- [x] exact finite-prime Fourier symbol computed.
- [x] self-adjointness and nonconstancy proved.
- [x] point spectrum excluded for every finite coefficient system.
- [x] phase rank separated from spectral discretization.
- [x] completed-connection implication stated at the correct representation level.
- [x] exact maximal-domain operator, literal paired translations, Fourier diagonalization,
  properness, pure absolute continuity, and empty point spectrum formalized in Lean 4.
- [x] new declarations checked for axioms and production module passed direct and targeted builds.

## Formalization completion log

Formalization is unconditional for every `P : Finset Nat.Primes` and every coefficient family
`c : Nat.Primes → ℂ`; primality is carried by the index type, and there are no smallness,
genericity, rational-independence, or spectral assumptions.

The production module proves:

- the exact paired exponential symbol and sharp bound
  `|h_P(t) - 2t| ≤ 2 ∑ p ∈ P, ‖c p‖`;
- global real analyticity, two-sided escape, compact-preimage properness, countable critical and
  level sets, and Lebesgue-null level sets;
- exact `L²` translation--modulation diagonalization for the literal operators
  `T_a f(u) = f(u-a)`;
- bounded self-adjointness of `V_P`, maximal self-adjointness of `H_P`, equality of the Hamiltonian
  domain with the standard weak-derivative domain, and
  `H_P = D + V_P` with `D = -2i d/du`;
- the level-set/eigenvalue equivalence for the finite-prime multiplier, empty point spectrum for
  both spectral and physical realizations, and absolute continuity of the direct-integral spectral
  measure;
- exact prime-log linear independence and phase rank `Nat.primeCounting' N`.

Audit results:

- `lake env lean GaloisForLFunctions/RHTower/FinitePrimeCommutingDilationNoPointSpectrum.lean` — pass;
- `lake build GaloisForLFunctions.RHTower.FinitePrimeCommutingDilationNoPointSpectrum` — pass;
- capstone axiom audit — only `propext`, `Classical.choice`, and `Quot.sound`;
- module wired into `GaloisForLFunctions.RHTower` umbrella; umbrella was not built.

## Surviving follow-on problem

- [ ] Construct a source-derived noncommuting prime--archimedean incidence. This is the positive
  successor route exposed by the no-point-spectrum theorem, not an unproved premise or conclusion
  of this card.
