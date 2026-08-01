# Gamma--Jacobi artanh transport coupling

- **ID:** `gamma-jacobi-artanh-transport-coupling`
- **Stage:** 1 — proof complete; formal/novelty audit in progress
- **Parents:** `SR-38`, `SR-40`, `SR-41`, `SR-43`
- **Type:** source-specific common-coordinate connector / singular reader
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [ADVANCE]`
  `[EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **RH used:** no
- **Computation used:** no

## Collision that killed the first formulation

The initial odd-only claim tried to recover every positive-log power by a linear Jacobi row.  That
is false: odd Gamma modes are odd functions of `t` and cannot linearly recover even powers.  The
edge-integral/Dirac--Krein reformulation was then found already formalized and explicitly classified
as non-new in `VonMangoldtSuccessorDiracKreinEdge.lean`.  Both routes are retired.

The positive survivor is nonlinear in one reconstructed coordinate and couples data that the
existing corpus proves only separately.

## Source theorem

Write

```text
a_k(t)=(-1)^k c_(2k+1) phi(t) tanh(t)^(2k+1)
```

for the actual odd Gamma--Jacobi coefficient.  Define one fixed incidence row and its `K`-mode
head by

```text
B(k)=(-1)^k/((2k+1)c_(2k+1)),
T_K(t)=sum_(k<K) B(k) a_k(t)/phi(t).
```

Phase, normalization, and Gamma characteristic cancel exactly:

```text
T_K(t)=sum_(k<K) tanh(t)^(2k+1)/(2k+1).                 (1)
```

Hence the finite-capacity connection defect has the closed form

```text
T_K'(t)=1-tanh(t)^(2K),                                 (2)
T_K(t) -> t.                                            (3)
```

The error bound used in Lean is explicit:

```text
|t-T_K(t)| <= |tanh t|^(2K+1)/(1-tanh(t)^2).            (4)
```

No target moment, Xi zero, or fitted finite transform enters `(1)`--`(4)`.

## Exact finite-mode current

Define the two-channel transport column

```text
Phi_(K,i)(t)=((i+1)T_K(t)^i T_K'(t), T_K(t)^(i+1))
```

with exchange form `[(a,b),(c,d)]_J=ad+bc`.  Product rule and `(2)` give

```text
integral_[x,y] [Phi_(K,i)(t),Phi_(K,j)(t)]_J dt
  =T_K(y)^(i+j+2)-T_K(x)^(i+j+2).                       (5)
```

For arbitrary source-dependent base capacity `C(n)`, common cofinal increment `L`, source aperture
`M`, and jet aperture `N`, sum `(5)` on the actual edges
`[log n,log(n+1)]` with weight `Lambda(n)/n` and cutoff `L+C(n)`.  Lean proves

```text
GammaJacobiCurrent_(C,L,M,N) -> SR40_(M,N)              (6)
```

in the full finite-dimensional matrix topology.  Thus arbitrary adaptive absolute-mode cutoffs
recover the proved principal-relative successor current, not merely one scalar moment.

## Exact coupling to `SR-38`

At a prime `p`, define the head feature to retain precisely modes
`k<gammaOddJacobiPrimeCapacity(p)`.  The existing coherent residual retains precisely the
complementary modes.  Coordinatewise Lean proves

```text
headFeature(p,k)+SR38ResidualFeature(p,k)=a_k(log p).    (7)
```

The log head at that same source-selected capacity is exactly the `B`-incidence of the head in
`(7)`.  This removes the object-type mismatch “prime kernel after Jacobi contraction versus jet
kernel after prime contraction”: both now arise from one absolute odd-Jacobi label, with the head
feeding the edge current and the tail feeding the coherent residual.

## Required singularity is exposed, not assumed away

Recovering `T_K` from the actual coefficient divides by `phi(log p)`.  Lean proves

```text
phi(log p)^(-2)=(p^2+1)/(2p) >= p/2,                    (8)
```

and therefore for every real `B` some prime has normalization square exceeding `B`.  So the
connector is canonically unbounded across prime labels.  This is positive information forced by
the previous bounded/normal-reader no-gos: the surviving common-coordinate map is singular, while
every bounded diagonal version is impossible.

## Novelty boundary

Parent-known ingredients:

- odd artanh partial sums and their derivative/error bound;
- Meixner--Pollaczek/Gamma Fourier coefficients;
- first-order Dirac--Stokes factorization;
- adaptive Mercer head/tail projections.

New source composition claimed provisionally:

- one fixed Jacobi incidence whose finite heads generate exact successor edge currents;
- arbitrary adaptive cutoff convergence of the full finite `SR-40` matrix;
- exact complementarity with the already source-selected `SR-38` residual;
- exact prime growth law proving the common connector lies in the singular, not bounded, class.

Targeted corpus search found no prior composition.  Literature calibration found classical
Meixner--Pollaczek/tanh generating functions and Xi expansions, but no von-Mangoldt successor
current built from complementary Gamma--Jacobi heads and tails.  External expert audit remains
necessary before publication-level novelty is asserted.

## What remains

This closes common absolute-coordinate incidence, not all of `SR-41`.  Still open:

1. package head current and tail residual as one joint infinite-index Krein object rather than two
   complementary contractions of one coordinate family;
2. construct completed Euler cyclic reader on that object;
3. prove reader carries exact positive jet-opening flux from `SR-43`;
4. derive fibre-pointed Berezin orientation and the RH criterion.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/GammaJacobiArtanhTransportCoupling.lean
```

Capstone declarations:

- `gammaOddJacobiLogIncidence_mul_normalizedCoefficient`;
- `hasDerivAt_gammaOddJacobiLogHead`;
- `tendsto_gammaOddJacobiLogHead`;
- `intervalIntegral_exchangePair_gammaOddJacobiHeadTransportJet`;
- `tendsto_finiteVonMangoldtGammaJacobiHeadKreinGram`;
- `gammaOddJacobiPrimeCoherentHeadFeature_add_residual`;
- `gammaOddJacobiLogHead_primeCapacity_eq`;
- `gammaOddJacobiLogPrimeNormalization_sq_eq`;
- `exists_prime_gammaOddJacobiLogPrimeNormalization_sq_gt`;
- `tendsto_finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram`.

## Gates

- [x] initial parity error killed
- [x] edge-integral rediscovery killed
- [x] exact paper proof `(1)`--`(8)`
- [x] whole-corpus collision search
- [x] targeted primary-literature calibration
- [x] unconditional Lean proof
- [ ] umbrella wiring
- [ ] axiom and lint audit
- [ ] external expert novelty audit
- [ ] completed Euler cyclic reader
- [ ] fibre orientation / RH
