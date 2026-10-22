# Local Pontryagin--Kolchin universality and Weil-crease tomography

- **ID:** `local-pontryagin-kolchin-isodivisorial-universality`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL THEOREM CANDIDATE / HT DIVISOR-FIBRE GEOMETRY / RH SOURCE TOMOGRAPHY
- **Scientific status:** `[CONJECTURE] [PAPER PROOF IN PROGRESS] [NOVELTY UNVERIFIED]`
- **Parents:** `maximal-isodivisorial-ht-free-frame`,
  `isodivisorial-prime-walsh-stone-saturation-law`,
  `isodivisorial-ht-weil-crease-transversal`

## Failure that forces this conjecture

The Boolean Stone-fibre theorem and the relative crease formula do not exclude an off-critical
zero.  Linear averaging over sparse Euler gauges cannot create the missing bound: if `U_omega` is
the zero-free Euler gauge, then

```text
logDeriv Z_(eta omega) - logDeriv Z_eta = logDeriv U_omega
```

coefficient by coefficient.  Thus every linear or differential prime-source fluctuation is absorbed
exactly by the holomorphic completion gauge; no residual Ward mass remains to compare with the
`8 pi` gap.

The stronger replacement must therefore describe the full hidden topology of the divisor fibre and
exhibit a genuinely global inverse.  Cardinal largeness, a Boolean cluster invariant, or a local
coefficient crease alone is insufficient.

## Exact conjecture

Let `H = {s : Re(s) > 0}`.  Let `eta` be a unimodular prime phase whose Helson Euler product has a
meromorphic continuation `Z_eta` to `H`.  Let `D` be its complete signed divisor there.  Fix:

- a finite set of prime coordinates on which phases must equal `eta`;
- a compact subset `C` of `H`;
- a derivative order `r`;
- `epsilon > 0`.

There exist an exponent-zero prime reservoir `S = {q_0,q_1,...}` outside the frozen coordinates and
a continuous family of unimodular phases

```text
x in T^N  |->  eta_x
```

with the following properties.

### A. Local isodivisorial Hilbert-torus universality

1. `eta_1 = eta`, where `1` is the identity of `T^N`.
2. Every `eta_x` agrees with `eta` off `S`, and every `Z_(eta_x)` continues meromorphically to `H`
   with exact divisor `D`.
3. Writing `U_x = Z_(eta_x)/Z_eta`, every `U_x` is holomorphic and zero-free on `H`, and

   ```text
   sup_(x in T^N) sup_(s in C) |d^k/ds^k (U_x(s)-1)| < epsilon
   ```

   for `0 <= k <= r`.
4. The map `x |-> U_x` is a topological embedding of `T^N` into the compact-open holomorphic
   gauge fibre.
5. Every finite set of distinct parameters `x_1,...,x_m` gives a differentially algebraically
   independent finite family of prime-layer sources, including every finite shift--jet rectangle,
   over the finite-prime rational differential field.

Since every pointed compact metrizable space embeds in `T^N` with its base point sent to `1`, every
neighbourhood of every divisor-fibre point contains a pointed copy of every compact metrizable
space whose finite subsets have the same Kolchin-freeness property.  In the Riemann specialization
`eta=1`, this holds in every neighbourhood of zeta while the complete positive-half-plane divisor
is fixed exactly.

### B. Global relative Weil-crease tomography

Take `eta=1`, put `L_2=(log 2)/2`, and choose the reservoir to contain only odd primes.  Enumerate
the character group of `T^N` cofinally as `gamma_m`, and set

```text
eta_x(q_m)=gamma_m(x),        eta_x(p)=1 for p not in S.
```

For the generalized von Mangoldt coefficients

```text
Lambda_x(p^a)=eta_x(p)^a log p
```

let `G_x(a)` be the sharp two-edge prime--Gamma source at width `L_2`, and define the relative
completion defect

```text
Delta_x(a)=G_x(a)-Q_(D_zeta)(a)=G_x(a)-G_1(a).
```

At the prime-entry point `a_m=(log q_m)/2`, the symmetric first-order crease is

```text
Crease_(a_m)(Delta_x)
  = -4 log(q_m) (gamma_m(x)-1) / sqrt(q_m).              (1)
```

Hence the crease current recovers every character value `gamma_m(x)`.  Pontryagin dual separation
then recovers `x` exactly.  The current is a complete global coordinate on the locally invisible
torus, while pushing `S` to infinity makes `Delta_x` identically zero on every prescribed bounded
aperture interval.

## Construction and dependency-closed proof plan

### 1. Pontryagin character code

The compact metrizable group `T^N` has countable discrete dual `Z^(N)`.  Choose a sequence
`gamma_m` in the dual in which every character occurs infinitely often.  For each parameter `x`,
put the value `gamma_m(x)` at `q_m` and `1` away from the reservoir.

For distinct `x_1,...,x_d`, the evaluation maps

```text
ev_(x_j) : Z^(N) -> T,   gamma |-> gamma(x_j)
```

are distinct group characters.  Dedekind--Artin independence of characters implies that

```text
sum_j c_j gamma(x_j)=0 for every gamma in Z^(N)
```

forces every `c_j=0`.  Cofinal repetition converts this into linear independence of the prime
coefficient columns modulo finite prime support.

### 2. Differential independence

Multiplication by the common nowhere-zero base phase `eta(p)` preserves tail rank.  The established
Shapiro--Sparer/Pong shifted prime-derivation transfer therefore makes every finite shift--jet
rectangle differentially algebraically independent over the finite-prime rational differential
field.  In particular every individual carrier is hypertranscendental.

### 3. Exponent-zero continuation and arbitrary local smallness

Choose `q_m` recursively so large that, for every positive `sigma` and every integer `k`,

```text
sum_m (log q_m)^k q_m^(-sigma) < infinity.
```

The reservoir may avoid the frozen finite prime chamber.  Uniformly in `x`,
`|1-gamma_m(x)| <= 2`.  Normal convergence of the local Euler ratios and all their logarithmic
derivatives gives a holomorphic nonvanishing gauge `U_x` on `H`, hence exact preservation of `D`.

Given `C,r,epsilon`, first put `sigma=min_(s in C) Re(s)>0`, then push the first reservoir prime
far enough that the finitely many derivative majorants

```text
sum_m (log q_m)^k q_m^(-sigma),  0 <= k <= r,
```

are uniformly as small as required.  Exponentiation transfers the logarithmic bounds to `U_x-1`.

### 4. Topological embedding

The same uniform majorants make `x |-> U_x` continuous in the compact-open topology.  If `x != y`,
some dual character separates them and occurs at infinitely many reservoir primes, so the prime
phases, Euler products, and gauge units differ.  A continuous injection from compact `T^N` to the
Hausdorff holomorphic-function space is a topological embedding.

Every compact metrizable space embeds in the Hilbert cube, the Hilbert cube embeds coordinatewise
in `T^N`, and translation in `T^N` sends its distinguished point to the identity.

### 5. Crease inverse

For `h>=0`, `0<L<=a`,

```text
R_(L,a)(h)=2 max(L-h,0)+T_L(2a-h),
T_L(u)=max(min(L,u)-max(0,u-L),0).
```

At `L=L_2` and an odd prime `q_m`, a crease at `a_m` could come from another integer `n` only when

```text
log(q_m/n) in {0, (log 2)/2, log 2}.
```

The middle case would make `q_m/n=sqrt(2)`, and the right-end case would make `q_m=2n`; both are
impossible.  The `n=q_m` entry tent has symmetric quotient `2`.  All other finitely many terms are
affine near `a_m`, and the common Gamma term cancels.  This proves `(1)`.  Since every character
occurs, character separation recovers `x`.

If all reservoir primes exceed `exp(2A)`, then no changed prime-power enters the finite source sum
for `a<=A`; hence `Delta_x=0` on `[L_2,A]` for every parameter, even though the global crease
current remains injective.

## Hostile attacks

1. **Pontryagin-wrapper attack.**  Infinite tori and Artin independence are classical.  Novelty can
   only lie in the simultaneous local isodivisorial embedding, finite-subset Kolchin freeness, and
   exact global crease inverse.
2. **Parent free-frame attack.**  The maximal frame theorem proves cardinal saturation inside finite
   prime cylinders but supplies no compact connected parameter space, no local compact-open
   smallness, and no coherent inverse.
3. **Stone-parent attack.**  Stone saturation realizes zero-dimensional recurring-pattern spectra,
   not arbitrary compact metrizable spaces as actual compact subsets of the divisor fibre.
4. **Same-zero folklore attack.**  Grosswald--Schnitzer and Helson constructions supply large
   same-zero families but do not appear to give local Hilbert-torus universality with every finite
   subset differentially free.
5. **Explicit-formula folklore attack.**  Prime-entry kinks recover coefficients in related finite
   paths.  Equation `(1)` alone is not novelty; its role as a complete inverse to a locally
   invisible universal compactum is the candidate-new statement.
6. **RH-decoration attack.**  The theorem does not prove RH and must not be sold as zero exclusion.
   Its RH content is an exact architecture theorem: every compact-local and divisor-only selector
   fails maximally, while one all-scale source--divisor current succeeds.
7. **Nature-significance attack.**  Reject the paper if the combined theorem is judged a routine
   product of sparse Euler gauges, character independence, and a coefficient kink.  Formal
   difficulty, repository novelty, and the RH label do not answer this objection.

## External frontier

- `[LITERATURE]` H. Helson, *Compact groups and Dirichlet series*, Arkiv för Matematik 8
  (1969/70), 139--143: compact-group/Dirichlet-series correspondence and the infinite-dimensional
  prime torus.
- `[LITERATURE]` E. Grosswald and F. J. Schnitzer, *A class of modified zeta and L-functions*,
  Pacific J. Math. 74 (1978), 357--364: modified Euler products with inherited zeros.
- `[LITERATURE]` K. Seip, *Universality and distribution of zeros and poles of some zeta
  functions*, J. Anal. Math. 141 (2020), 331--381; I. Bochkov and R. Romanov, *On zeroes and poles
  of Helson zeta functions*, JFA 282 (2022), 109398; J. Andersson, *Mittag-Leffler type theorems for
  Helson zeta-functions*, arXiv:2408.15713: prescribed-divisor Helson constructions.
- `[LITERATURE]` W. Y. Pong, *Applications of differential algebra to algebraic independence of
  arithmetic functions*, Acta Arith. 172 (2016), 149--173: differential-algebraic transfer from
  arithmetic coefficient independence.
- `[LITERATURE]` Dedekind--Artin independence of distinct characters: the algebraic input for
  finite-subset freeness.

No checked primary source yet states the combined local compact-metrizable universality,
isodivisorial Kolchin-free compactum, or global crease inverse.  This is not a novelty verdict.

## Open core

`[OPEN CORE]` Close the exact analytic topology statement: prove uniform compact-open bounds for all
parameter gauges and derivatives, prove injectivity of the continued Euler products from the
reservoir phase code, and normalize the generic Shapiro--Sparer/Pong transfer from complex circle
phases rather than the corpus's Boolean-sign specialization.

No Lean implementation begins until this proof and the direct primary-literature attack close.

## Gates

- [x] exact stronger conjecture forced by the Stone/averaging failure
- [x] Pontryagin character construction and finite-subset independence mechanism
- [x] exponent-zero/local-smallness proof architecture
- [x] global relative crease inverse architecture
- [ ] dependency-closed paper proof
- [ ] direct primary-source priority audit
- [ ] hostile significance verdict
- [ ] exact Lean theorem
- [ ] publication-ready manuscript and independent antagonist review
