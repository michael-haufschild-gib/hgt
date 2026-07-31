# Reciprocal-period phase reversal and a flat hypertranscendental boundary

- **ID:** `multiple-elliptic-gamma-reciprocal-rank-flat-phase-reversal`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / RECIPROCAL-PERIOD PHASE CLASSIFICATION / SOURCE-PRODUCED FLAT CLASS
- **Source:** `../3-formalized/all-parameter-multiple-elliptic-gamma-dichotomy.md`;
  `../3-formalized/not_new_scientific_knowledge/elliptic-gamma-source-face-fracture.md`;
  `../1-in-progress/hypertranscendental-bornological-krull-radical.md`
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL EXACT-MATCH SEARCH NEGATIVE] [NOT AN RH RESULT]`
- **Statement:** Componentwise reciprocalization of a rank-two period family can change its empty
  hypertranscendence graph into a complete graph of arbitrary size.  Along a rational cofinal
  scaling, the resulting hypertranscendental multiple elliptic Gamma functions differ from their
  differentially algebraic zero-nome face by a nonzero all-orders-flat source section.

## Goal

Produce an actual special-function element in the bornological Krull radical, rather than selecting
the ambient witness `exp(-1/|w|)` after the target algebra is known.  The theorem must also detect
genuine differential phase: every finite fibre on one side is differentially algebraic in `z`,
while every reciprocal fibre of order at least one is hypertranscendental in the same variable.

This is a theorem about a reciprocal-period Cremona transform.  It is **not** asserted to be one
global Narukawa modular transformation.  A Jacobi `S`-move on an individual theta face also
rescales `z`, and the different face normalizations do not assemble into one common modular chart.
That non-gluing boundary is part of the result, not silently removed.

## Exact theorem

Fix `N>=2`, distinct integers `n_1,...,n_N`, and a transcendental
`omega` in the complex upper half-plane; one may take `omega=i*pi`.  Put

```text
tau_j=omega+n_j,
alpha_j(m)=tau_j/m,
beta_j(m)=-1/alpha_j(m)=-m/tau_j,              m>=1.       (1)
```

Both period families lie in the upper half-plane.  Let `G_alpha(m)` and `G_beta(m)` be the
`N`-period multiple elliptic Gamma functions in the parity-correct normalization of the
all-parameter dichotomy paper.  Then:

```text
rank_Q span_Q{1,alpha_1(m),...,alpha_N(m)}=2,               (2)
rank_Q span_Q{1,beta_1(m),...,beta_N(m)}=N+1.               (3)
```

Consequently, for every `m`:

```text
G_alpha(m) and its logarithmic derivative are DA over C(z);
G_beta(m) and its logarithmic derivative are HT over C(z). (4)
```

The face law is exact.  Every nonempty face of the `alpha` family is DA.  In the `beta` family,
every singleton face is DA and every face with at least two surviving periods is HT.  Thus
componentwise reciprocalization changes the empty rank-three graph into the complete graph
`K_N`.

For the flat statement, write

```text
q_j(m)=exp(2*pi*i*beta_j(m)),
x(z)=exp(2*pi*i*z),
Q(m)=product_j q_j(m).                                    (5)
```

Let `K` be the closed disk `|z-i|<=1/4`.  Define the DA zero-nome boundary

```text
B_N(z)=1-x(z)          if N is odd,
B_N(z)=1/(1-x(z))     if N is even.                       (6)
```

There are constants `C>0` and `0<r<1`, depending only on the period packet, such that

```text
sup_(z in K) |G_beta(m)(z)-B_N(z)| <= C r^m               (7)
```

for every sufficiently large `m`.  Put `w_m=1/(m+1)` and

```text
A=ell^infinity({m>=1},C(K)),
D_m=G_beta(m)|_K-B_N|_K.                                  (8)
```

After changing finitely many harmless constants in `(7)`, `D` is a bounded sequence and

```text
D != 0,
D belongs to intersection_(k>=1) w^k A.                  (9)
```

In fact every coordinate `D_m` is nonzero.  Hence the actual multiple elliptic Gamma source
supplies a nonzero flat section whose fibres are the difference between an HT function and its
DA boundary.  Every finite inverse-power boundary jet is identical to that of `B_N`, although the
exact fibre remains hypertranscendental.

## Paper proof

### Reciprocal rank

Equation `(2)` is immediate from

```text
alpha_j(m)=omega/m+n_j/m in span_Q{1,omega}.
```

The span has dimension two because `alpha_j(m)` is nonreal.

For `(3)`, suppose

```text
c_0+sum_j c_j/(omega+n_j)=0,                 c_j in Q.    (10)
```

Multiplying by `P(omega)`, where

```text
P(X)=product_j (X+n_j),
```

gives the value at `omega` of a polynomial over `Q`:

```text
c_0 P(X)+sum_j c_j P(X)/(X+n_j).                         (11)
```

Transcendence of `omega` forces this polynomial to vanish identically.  Evaluation at
`X=-n_k` gives

```text
c_k product_(j!=k)(n_j-n_k)=0,
```

so every `c_k` is zero, and then `c_0=0`.  Multiplication by the nonzero rational `-m` does not
change rational rank.  This proves `(3)`, including the same statement for every subpacket.
The exact all-parameter period-rank dichotomy gives `(4)` and the graph classification.

### Exponentially flat zero-nome degeneration

Since

```text
Im(-1/tau_j)>0,
|q_j(m)|=exp(-2*pi*m*Im(-1/tau_j)),
```

there is an `r<1` with `|q_j(m)|<=r^m` for every `j,m`.  Put `t_m=r^m`.  The multi-index tail obeys

```text
S_m=sum_(nu in N^N,nu!=0) |q(m)^nu|
   =product_j (1-|q_j(m)|)^(-1)-1
   <= (1-t_m)^(-N)-1
   =O(t_m).                                                (12)
```

On `K`, `x` is bounded and bounded away from zero, while `|x|<1`.  The denominator-side product
therefore splits as

```text
(x;q(m))_infinity^(N)
  =(1-x) product_(nu!=0)(1-x q(m)^nu)
  =(1-x)(1+O(t_m))                                        (13)
```

uniformly on `K`.  The standard infinite-product estimate

```text
|product_a (1+u_a)-1| <= exp(sum_a |u_a|)-1
```

applies because `(12)` is summable.

For the numerator-side product,

```text
sum_nu |Q(m)q(m)^nu/x|
 <= |Q(m)| inf_K|x|^(-1) product_j(1-|q_j(m)|)^(-1)
 =O(t_m^N),
```

so

```text
(Q(m)/x;q(m))_infinity^(N)=1+O(t_m)                       (14)
```

uniformly on `K`.  Substitution of `(13)`--`(14)` into the parity-correct product gives `(6)`--`(7)`.

For every `k`,

```text
sup_m (m+1)^k r^m < infinity,
```

so `(7)` proves `D in w^k A`.  This holds for all `k`.

Finally, if `D_m` vanished on `K`, the identity theorem would make `G_beta(m)=B_N` as meromorphic
functions.  The right side is DA, contradicting `(4)`.  Thus every `D_m` is nonzero, proving `(9)`.
`QED`

## What is new and what is parent mathematics

Parent inputs:

- componentwise inversion and partial-fraction independence are elementary;
- trigonometric/zero-nome degeneration of elliptic Gamma products is classical;
- exponentially small nome tails and flat functions are standard asymptotic analysis;
- modular/resurgent `q`-Pochhammer sectors are already studied in the literature;
- failure of Krull intersection in bounded function algebras is parent function-algebra theory.

The candidate-new theorem is their coupling through the exact all-parameter multiple elliptic Gamma
dichotomy:

```text
empty DA graph
  --componentwise reciprocal period transform-->
complete HT graph of arbitrary size
  --zero-nome completion-->
nonzero all-orders-flat deformation of one DA boundary.   (15)
```

No located paper states `(15)`, classifies its face graph, or exhibits the difference between the
named HT fibre and its DA degeneration as an element of the bornological Krull radical.  Exact,
stronger, equivalent, and mechanism searches through July 2026 found only the parent modularity,
degeneration, resurgence, and function-algebra results.

Primary adjacent sources:

- A. Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, <https://arxiv.org/abs/math/0306164>.
- G. Felder and A. Varchenko, *The elliptic gamma function and `SL(3,Z) x Z^3`*,
  <https://arxiv.org/abs/math/9907061>.
- V. Fantini and C. Rella, *Modular resurgence, q-Pochhammer symbols, and quantum operators from
  mirror curves*, <https://arxiv.org/abs/2506.08265>.
- R. Mortini, R. Rupp, and A. Sasane, *On the Krull Intersection Theorem in Function Algebras*,
  <https://arxiv.org/abs/1605.08204>.

## Hostile significance audit

- **Not one modular symmetry.** The reciprocal transform acts componentwise on period labels.
  Genuine Narukawa projective charts divide all periods and `z` by one common period and preserve
  augmented rational rank.  Calling `(15)` a global modular phase change would be false.
- **Same differential axis.** Statements `(2)`--`(4)` all concern differential algebraicity in
  `z`; the theorem does not compare `z`-differential rank with parameter-space algebraic rank.
- **Family statement.** Flatness concerns the cofinal source family indexed by `m`, not one fixed
  function becoming DA.
- **Actual source class.** `D` is obtained from the named multiple elliptic Gamma product and its
  exact zero-nome face.  It is not the ambient witness `exp(-1/|w|)` inserted after choosing the
  receiver.
- **No `BCDef_F` overclaim.** The theorem provides the explicit source-produced element demanded
  by the completion programme, but it does not construct the comparison functor
  `L chi_F^*(Comp_F C_F) -> Comp_F(L chi_F^* C_F)` or compute its cofiber.
- **No RH claim.** Flat HT capacity supplies neither divisor orientation nor Pick-kernel
  domination.  It only proves that finite boundary jets cannot certify that the completed source
  stayed in the DA phase.

## RH pressure test

The Xi completion architecture already excludes every finite reporter and reduces the live core to
a source-pure all-aperture Pick comparison.  The theorem adds one exact necessity:

```text
a comparison built only from finite inverse-aperture jets cannot distinguish
an HT reciprocal-period completion from its DA zero-nome boundary.          (16)
```

The direct Xi sewing does not satisfy that antecedent.  The multiple-Gamma theorem differentiates
in the additive/fugacity variable with fixed nomes, whereas the Xi spectral derivative moves every
nome \(q_p=p^{-s}\).  Diagonal Dedekind-eta specialization also inserts partition multiplicities
not present in one Euler ray.  Taking the first fugacity coefficient recovers the Euler packet but
throws away the full HT carrier.  Plethystic Möbius inversion repairs the coefficient sequence, but
its Mellin multiplier is the existing \(1/\zeta(s)\) continuation wall; analytic-unit twists do not
make that wall easier.

The strongest positive survivor is now proved separately in
`prime-completion-annihilates-hypertranscendence-at-even-temperature.md`.  It retains every
occupation mode: finite prime packets are HT, their complete logarithmic normal jets are the finite
Euler packets, yet all-prime completion at every even integer exponent is DA by Gamma reflection.
Therefore even source purity plus convergence of the entire boundary germ does not conserve the HT
phase.  A valid RH bridge must transport a completion-stable polarized invariant, not HT status
alone.  Until such an invariant is constructed, `(16)` remains a constraint rather than progress on
the Xi Pick inequality.

## Gates

- [x] 0 → 1 in-progress: exact reciprocal family and flat receiver stated
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] internal corpus collision audit
- [x] external primary-literature exact/stronger/equivalent/mechanism search
- [x] hostile modularity, source-naturality, differential-axis, and RH audits
- [ ] independent specialist priority audit
- [ ] 2 → 3 formalized: unconditional Lean rank reversal and flat-product capstone
- [x] direct eta/Möbius Xi reciprocal-face sewing falsified
- [x] strongest source-pure positive survivor extracted and paper-proved
- [ ] construct a completion-stable polarized Xi survivor
- [ ] 3 → 4 publication-ready

## Log

- 2026-07-27 — eta modular-dual flat witness found, then demoted as parent resurgence plus an
  elementary Krull-radical embedding.
- 2026-07-27 — naive claim that global modularity changes period rank falsified: genuine projective
  modular charts preserve augmented rational rank.
- 2026-07-27 — extracted the positive survivor: componentwise reciprocalization reverses the exact
  face graph, and rational cusp scaling makes the resulting HT-minus-DA source difference a nonzero
  all-orders-flat section.
- 2026-07-27 — direct eta sewing failed the source and differential-axis audit; Möbius repair
  returned the already formalized RH-equivalent continuation wall.
- 2026-07-27 — source-pure replacement proved: finite prime occupation products are HT, but
  all-prime completion at even temperature is DA while the complete Euler/zeta boundary jet
  survives.
