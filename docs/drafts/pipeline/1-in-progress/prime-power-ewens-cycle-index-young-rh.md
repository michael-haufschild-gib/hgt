# Prime-power cycle index, virtual permutations, Young characters, and RH

- **ID:** `prime-power-ewens-cycle-index-young-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [DIRECT CYCLE MODEL RETIRED POSITIVELY]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeCycleDeletionCoherence.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordYoungShapeNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/BornEtaGrading.lean`,
  `formal/GaloisForLFunctions/ExteriorParity.lean`, and
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaAllOrderCumulant.lean`
- **Consumer:** `prime-theta-young-thoma-schur-rh.md`
- **Statement:** `[CONJECTURE]` A colored virtual-permutation process whose cycles are prime-power
  packets completed by theta/Gamma data descends, after the permutation sign twist, to the coherent
  Young system of the Xi square-coordinate coefficients.  The resulting Schur-positive
  specialization proves RH.  The direct uncolored multiplicative cycle-weight model is impossible;
  Lean classifies its maximal coherent survivor exactly as the geometric/Ewens class.

## 1. Why prime powers are cycles

On the Euler half-plane,

```text
log zeta(s)=sum_p sum_(k>=1) p^(-ks)/k.                  (1)
```

The factor `1/k` is the automorphism factor of a labelled cycle of length `k`.  The exponential
formula for permutations gives, for cycle weights `w_k`,

```text
exp(sum_(k>=1) w_k u^k/k)
  =sum_(n>=0) u^n/n! sum_(sigma in S_n)
     product_(C cycle of sigma) w_|C|.                   (2)
```

Thus the raw Euler product is a bosonic permutation cycle index.  Tensoring a representation with
the permutation sign character multiplies a `k`-cycle by `(-1)^(k-1)`, so `(2)` becomes

```text
exp(sum_(k>=1) (-1)^(k-1) w_k u^k/k),                   (3)
```

the row-to-column involution `omega` required by the Young--Thoma route.  The parity and exterior
sign mechanisms already exist in the formal corpus; the missing theorem is to realize the
completed prime--Gamma packet as one coherent colored cycle process before scalarizing its sign.

## 2. Exact Xi cycle weights

For the normalized square-coordinate function `A`, define from the theta source

```text
c_k=(-1)^(k-1) k [u^k] log A(u).                         (4)
```

Then identically near zero,

```text
A(u)=exp(sum_(k>=1)(-1)^(k-1)c_k u^k/k).                 (5)
```

If the completed cycle model has positive effective cycle weights `c_k` and its signed Frobenius
character is coherent and positive on every irreducible character, `(5)` gives the same
Schur-positive specialization as the Young--Thoma route.  Edrei--Thoma and the order bound then
force `A` to have only negative real zeros, hence RH.

Positive scalar values `c_k` are not sufficient.  The central functions at all ranks must be
positive definite and compatible under deleting the last label; otherwise `(5)` is only a formal
cycle-index rewrite of the target.

## 3. Direct deletion coherence and its complete no-go

Suppose an uncolored multiplicative permutation law assigns one nonzero weight `w_k` to every
cycle of length `k`.  Delete the distinguished label `n`.  If it had been inserted into a cycle of
length `k`, there are `k` insertion sites and the relative lift weight is

```text
r_k=w_(k+1)/w_k.                                         (6)
```

For a permutation of cycle shape `lambda`, the total non-fixed lift contribution is

```text
S_r(lambda)=sum_(k in parts(lambda)) k r_k.              (7)
```

Projective deletion can be shape-blind only if `(7)` depends on `|lambda|` and not on its parts.
Lean proves the exact classification

```text
S_r(lambda) depends only on |lambda|
  <-> r_k=r_1 for every k>=1.                            (8)
```

For nonzero cycle weights this forces

```text
w_k=w_1 (w_2/w_1)^(k-1).                                (9)
```

At fixed rank, `(9)` is precisely an Ewens-type weight up to a geometric normalization.  This is
the maximal positive survivor, not merely a counterexample.

The Xi source weights are not geometric.  The first ratios of the numerically certified
logarithmic power sums are

```text
c_2/c_1 = 0.00160885567459714098,
c_3/c_2 = 0.00387850013647296394,
c_4/c_3 = 0.00459883193730066322.
```

Therefore the direct uncolored law with `w_k=c_k` fails the first projective-coherence mechanism.
No normalization depending only on rank can repair it.

## 4. Positive successor: retain the hidden color

The no-go says exactly what was compressed too early.  A prime-power cycle carries at least

```text
(prime p, repetition length k, theta/Gamma termination channel).
```

Deletion need not be shape-blind on this colored state space.  Its lift score may depend on the
retained color and still have a coherent scalar marginal after summing over a fixed latent law.
There are two concrete successors.

1. **Mixture of coherent Ewens fibers.**  Construct a source-defined latent variable `T` from the
   theta/Gamma channel.  Conditional on `T`, use the geometric class `(9)`; mix the resulting
   projective virtual-permutation laws with one aperture-independent positive measure.  The same
   latent measure must work at every rank.
2. **Prime--archimedean colored cycles.**  Keep prime rows and archimedean columns separately.
   Dual RSK then turns binary incidences into a Schur process.  This is the two-alphabet producer in
   `prime-arch-dual-cauchy-rsk-fredholm-rh.md`; the present theorem explains why its second alphabet
   is forced by deletion coherence rather than decorative.

In either successor, the uncolored Xi coefficients are compared only after the colored process is
proved positive and projectively coherent.

## 5. Large two-ended chain

```text
prime-power Euler packets with their 1/k cycle symmetry
  + exterior/sign representation                                  [CORPUS]
  + theta/Gamma latent color                                      [CORPUS]
  -> positive colored cycle weights at every finite aperture       [OPEN A]
  -> deletion-coherent virtual-permutation process                 [OPEN B]
  -> sign-twisted positive central character
  -> Frobenius characteristic / coherent Young measure             [PARENT]
  -> rho(h_n)=a_n/a_1^n from the source cycle index                [OPEN C]
  -> Schur positivity / Edrei--Thoma
  -> negative zeros of A
  -> real zeros of XiC
  -> RH.
```

## 6. Hard attacks and positive successors

1. **Arbitrary-cycle attack.**  Positive `w_k` do not imply projective consistency.
   **Positive successor:** `(8)--(9)` give the complete uncolored coherent class.
2. **Geometric mismatch attack.**  The Xi logarithmic weights are not geometric.
   **Positive successor:** retain a latent theta/Gamma color or a two-alphabet incidence; the first
   ratio mismatch is the exact witness that scalarization occurred too early.
3. **Central-probability attack.**  A positive probability measure on conjugacy classes need not be
   a positive-definite character.
   **Positive successor:** prove nonnegative irreducible-character coefficients before invoking
   Frobenius characteristic; RSK or an explicit representation supplies this automatically.
4. **Sign attack.**  The permutation sign creates alternating scalar coefficients.
   **Positive successor:** positivity lives in the graded representation or in the conjugate Young
   shape, not termwise in the signed class function.
5. **Ewens-mixture attack.**  Choosing a different mixing law at each rank destroys coherence.
   **Positive successor:** one latent measure is constructed before rank truncation and then
   marginalized at every level.
6. **Target-fed cycle attack.**  Setting `w_k=c_k` and declaring the resulting character positive
   assumes the RH-equivalent endpoint.
   **Positive successor:** derive colored cycle weights from prime powers and theta atoms first;
   prove `(5)` only afterward.
7. **Fixed-modulus attack.**  A finite character table or finite latent support yields eventually
   finite-rank Young data.
   **Positive successor:** prove cofinal compatibility and infinite support from the source's
   no-finite-recurrence or hypertranscendence input.

## 7. Parent results

- the exponential formula and cycle index of symmetric groups;
- the Ewens sampling formula and its deletion-consistent virtual-permutation process;
- Betz--Ueltschi--Velenik, *Random permutations with cycle weights*, arXiv:0908.2217;
- Kerov--Olshanski--Vershik, *Harmonic analysis on the infinite symmetric group*,
  arXiv:math/0312270;
- Frobenius characteristic, the sign involution, and the Edrei--Thoma classification.

## Kill conditions

Retire a colored producer if its finite weights are negative, if deletion changes the latent law,
if its scalar marginal is fitted from the Xi coefficients, or if its irreducible-character
expansion has a negative coefficient.  Preserve the largest coherent Ewens fiber, the first failed
shape and ratio, or any positive coherent colored sub-process.

## Gates

- [x] prime-power cycle-index interpretation stated
- [x] sign character identified with the row-to-column involution
- [x] direct uncolored deletion coherence classified completely in Lean
- [x] Xi cycle weights numerically shown nongeometric
- [x] no-go converted into the maximal geometric/Ewens class and a forced latent-color successor
- [ ] source-defined colored cycle law constructed
- [ ] deletion coherence and positive character proved
- [ ] source cycle index identified with A
- [ ] Young--Thoma capstone composed
- [ ] RH formalized
