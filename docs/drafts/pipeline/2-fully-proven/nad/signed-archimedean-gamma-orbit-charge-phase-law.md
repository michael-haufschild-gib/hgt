# Signed archimedean Gamma products obey an orbit-charge phase law

- **ID:** `signed-archimedean-gamma-orbit-charge-phase-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[COMMON-SCALE CLASSIFICATION FORMALIZED; ARBITRARY-SCALE AND BOUNDARY INPUTS NOT YET FORMALIZED] [NOVELTY UNVERIFIED]`
- **Statement:** A signed finite Gamma product with positive commensurable scales is differentially
  algebraic exactly when every shift-orbit charge vanishes; otherwise it is hypertranscendental.
  Nonzero total charge carries a one-point projective boundary. Neutral total charge carries
  log-resonant polynomial jets in addition to compact phase. For the full one-phase field generated
  by `Gamma(s+i theta)/Gamma(s)`, polynomial gcd and Bezout primitivity prove the boundary chain
  `K_theta -> C[z] -> C`. For every neutral signed product, a directional Vandermonde resolves the
  simultaneous exponential and logarithmic phases into an exponential-polynomial jet carrier.
  Flat and Stokes corrections are projectively scalar.

## 1. Signed products

Fix

```text
d>=1, alpha in R,
lambda_j>0, mu_j in C, m_j in Z\{0}  (1<=j<=d),            (1)
```

and assume the scales are commensurable: there is `H>0` with

```text
n_j=H lambda_j in N_(>0).                                  (2)
```

Put

```text
G(s)=exp(alpha s) product_(j=1)^d Gamma(lambda_j s+mu_j)^m_j,
K_G=C(s)<G>.                                                (3)
```

Negative `m_j` allow Gamma ratios. All slopes remain positive; reflected negative-slope factors
are a later boundary because reflection introduces trigonometric carriers.

## 2. Common-scale orbit normal form

`[PROVED HERE]` There are

```text
beta in R,
C_0 in C^x,
R in C(s)^x,
b_1,...,b_q in C pairwise distinct modulo H Z,
M_1,...,M_q in Z\{0},                                      (4)
```

such that

```text
G(s)=C_0 exp(beta s) R(s)
     product_(c=1)^q Gamma((s+b_c)/H)^M_c.                  (5)
```

The integers `M_c` are canonical up to relabelling and are called the **shift-orbit charges**.

### Proof

Gauss multiplication gives, for `n_j=H lambda_j` and
`z=s/H+mu_j/n_j`,

```text
Gamma(n_j z)
 = (2 pi)^((1-n_j)/2) n_j^(n_j z-1/2)
   product_(ell=0)^(n_j-1) Gamma(z+ell/n_j).                (6)
```

Thus each original factor becomes a nonzero constant, a real exponential in `s`, and signed
common-scale factors

```text
Gamma((s+a_(j,ell))/H)^m_j,
a_(j,ell)=(mu_j+ell)/lambda_j.                              (7)
```

If two shifts differ by an integer multiple of `H`, the finite Gamma recurrence expresses their
ratio as a nonzero rational function of `s`. Choose one representative `b_c` in each occupied
`H Z`-orbit, move every factor to that representative, and sum its signed exponents. Orbits with
zero sum disappear; the recurrence factors accumulate into `R`. This proves `(5)`.

Changing a representative by a multiple of `H` changes `R` but not the orbit charge. Hence the
vector `(M_c)` is canonical.

## 3. Exact DA/HT dichotomy

`[PROVED HERE]`

```text
G is differentially algebraic over C(s)
  iff q=0
  iff every shift-orbit charge vanishes.                    (8)
```

When these conditions hold,

```text
G(s)=C_0 exp(beta s)R(s),                                  (9)
```

so `G` satisfies the first-order linear ADE

```text
G'=(beta+R'/R)G.                                           (10)
```

When some `M_c` is nonzero, `G` is hypertranscendental.

### Proof of the HT direction

Put

```text
Psi=G'/G,
Tau=Psi'.                                                   (11)
```

From `(5)` and the Gamma recurrence,

```text
G(s+H)/G(s)
 =exp(beta H) R(s+H)/R(s)
  product_(c=1)^q ((s+b_c)/H)^M_c.                         (12)
```

Therefore

```text
Tau(s+H)-Tau(s)
 =D^2 log(G(s+H)/G(s))
 =D^2 log(R(s+H)/R(s))-sum_(c=1)^q M_c/(s+b_c)^2.          (13)
```

The first term on the right is the rational shift difference

```text
D^2 log R(s+H)-D^2 log R(s).                               (14)
```

At order two, the discrete residue of `(13)` in the orbit `-b_c+H Z` is `-M_c`. Distinct `b_c`
represent distinct orbits. Since some `M_c` is nonzero, the right side of `(13)` is not a rational
shift difference.

The complete upper-sector Stirling expansion has

```text
hat(Tau) in C((s^(-1))).                                   (15)
```

Homogenizing `(13)` gives a rational linear shift equation for `hat(Tau)`. The
Adamczewski--Dreyfus--Hardouin formal shift dichotomy says that `hat(Tau)` is rational or
hypertranscendental. Rationality would give a rational solution of `(13)`, contrary to its nonzero
discrete residue. Hence `hat(Tau)` and its formal primitive `hat(Psi)` are hypertranscendental.

Any analytic ADE for `Psi` would pass to the complete Stirling expansion and contradict formal
hypertranscendence. Thus `Psi` is hypertranscendental. If `G` were DA, then `G'/G` would be DA, so
`G` is hypertranscendental. This proves `(8)`.

The classification part is a direct synthesis of Gauss multiplication, Gamma recurrence,
classical discrete residues, and the formal shift theorem. It is `[BRIDGE]` unless the exact
formulation survives a stronger literature comparison.

## 4. Total charge and asymptotic normal form

Define the total archimedean charge

```text
M=sum_(c=1)^q M_c.                                         (16)
```

Let `r_R=deg(numerator R)-deg(denominator R)`. Stirling's expansion in `(5)` gives

```text
G(s)=A exp((M/H)s log s+kappa s) s^gamma (1+O(1/s)),       (17)
```

where `A in C^x`,

```text
kappa=beta-(M/H)(log H+1) in R,
gamma=r_R+sum_c M_c(b_c/H-1/2) in C.                       (18)
```

The formula has a full formal expansion. In particular:

1. if `M!=0`, distinct powers of `G` are exponentially separated on upper vertical tubes;
2. if `M=0`, then

   ```text
   G(s)=A exp(beta s)s^gamma(1+O(1/s)).                     (19)
   ```

The invariant `gamma` in the neutral case does not depend on the chosen orbit representatives:
moving `b_c` by `kH` changes its contribution by `kM_c`, while the rational recurrence factor
changes `r_R` by the opposite integer.

## 5. Nonzero total charge gives a one-point boundary

Assume `M!=0`. Put `L=C(s)<Psi>`. Formal and analytic hypertranscendence of `Psi` identify `L` with
its formal Stirling image in

```text
C(log s)((s^(-1))).                                        (20)
```

Thus every nonzero `B in L` has a unique leading monomial

```text
B(s)=c s^a(log s)^b(1+o(1)).                               (21)
```

Bell-polynomial identities give `K_G=L(G)`. Scaling all derivatives of the HT element `G` by one
nonzero constant fixes `L`, so `G` is transcendental over `L`.

If `M>0`, equation `(17)` makes `G` exponentially small on upper tubes; the least Gamma power in a
rational function over `L` dominates. If `M<0`, `G` is exponentially large; the greatest power
dominates. Therefore every finite nonzero tuple in `K_G` has, after division by one dominant
component as a function of the local variable, a nonzero constant projective limit.

This is the one-point boundary theorem from
`finite-archimedean-gamma-product-boundary-law.md`, now with the orientation selected by the sign of
`M`.

## 6. Neutral HT products carry polynomial jets beyond compact phase

Assume now

```text
M=0.                                                        (22)
```

The Gamma logarithms cancel from `Psi`. Its formal expansion lies in

```text
C((s^(-1)))                                                 (23)
```

rather than requiring `log s`. In the HT case, formal hypertranscendence again makes the asymptotic
map on `L=C(s)<Psi>` injective. In the DA case `(9)`, the same statement follows directly from
`Psi=beta+R'/R`. Hence every nonzero `B in L` has a full Laurent asymptotic with a first term

```text
B(s)=c s^a(1+o(1)),  a in Z.                               (24)
```

### Refuted finite-transseries boundary lemma

`[FALSIFIED]` The previous claim was: let

```text
(P_1(G),...,P_r(G)),  P_j in L[X],                          (25)
```

be a finite nonzero polynomial tuple, and let `T_n->+infinity` be any sequence. After passing to a
subsequence, there are nonzero scalar normalizations `c_n` such that

```text
c_n(P_1(G(s+iT_n)),...,P_r(G(s+iT_n)))
  ->(H_1(s),...,H_r(s))                                     (26)
```

locally uniformly on every pole-free compact, where the limit vector is nonzero and every `H_j` is
an exponential polynomial in `exp(beta s)`. Consequently

```text
Gamma_B(H_1,...,H_r) subset beta Z,
rank_Q Gamma_B(H_1,...,H_r)<=1.                             (27)
```

Every finite tuple in `K_G` can first be multiplied by one common denominator to reach this form;
this is a functional projective normalization. Without clearing denominators, subsequential limits
may be rational functions of `exp(beta s)` and can have moving poles. ADE coefficients can and will
be cleared before translation, so the limits in `(26)` are holomorphic exponential polynomials on
the whole strip.

### Candidate proof and exact gap

After a common denominator, projectively replace the tuple by polynomials

```text
P_j(G)=sum_(k=0)^N B_(j,k)G^k,  B_(j,k) in L.              (28)
```

Equations `(19)` and `(24)` give full generalized asymptotic series whose terms have the form

```text
c exp(k beta s)s^(a+k gamma-n),
k in {0,...,N}, a,n in Z.                                  (29)
```

Only finitely many `k` occur. At each fixed real growth exponent, only finitely many terms occur.
Choose the largest real growth layer which does not vanish in the tuple, and normalize by its
positive size at `iT_n`.

The only phases depending on `n` at this layer are powers of

```text
exp(i beta T_n),
exp(i Im(gamma) log T_n).                                  (30)
```

They lie in a compact two-torus, so a subsequence makes every required finite power converge. The
local-variable part of `(29)` converges to `exp(k beta s)`; powers of `(s+iT_n)/(iT_n)` tend to one
locally uniformly. This gives an exponential-polynomial limit.

For a fixed limiting phase, formal differential transcendence shows that not every layer can
vanish: in the HT case, scaling `G` fixes `L`, so the formal `G` is transcendental over the formal
image of `L`; in the DA case `(9)` reduces the assertion to the ordinary Laurent--exponential
field. This excludes cancellation at one fixed phase.

This argument does not justify the required sequential descent. A higher layer may vanish at the limiting
phase while its value at the moving phase decays at a rate coupled to a power of `T_n`; several
such layers can then cancel after normalization. To prove `(26)`, one must show that this coupled
descent terminates at a finite algebraic layer, rather than leaving a beyond-all-orders Stirling
remainder as the first nonzero boundary term. The resulting proposed lemma was:

> **Neutral finite-carrier lemma.** Every nonzero tuple `(25)` and every sequence `T_n->infinity`
> admit a subsequence and scalar normalization for which a nonzero limit exists in the finite
> exponential space `span_C{exp(k beta s):0<=k<=N}`.

Fixed-phase formal transcendence alone is insufficient, and `(26)`--`(27)` are false as stated. The
proved replacement is the polynomial phase-jet carrier `(31a)`--`(31d)` below.

For `theta>0`, put

```text
G_theta(s)=Gamma(s+i theta)/Gamma(s),
A_theta=exp(-pi theta/2),
T_n=exp(2 pi n/theta).                                     (30a)
```

This is a neutral HT ratio with `beta=0` and `gamma=i theta`. The Gamma-ratio expansion gives

```text
(T_n/A_theta)(G_theta(s+iT_n)-A_theta)
 ->theta s+theta(i theta-1)/2.                             (30b)
```

The right side is nonconstant, whereas `(27)` with `beta=0` allowed only constants. More strongly,
for every `m>=1`, the element `(G_theta-A_theta)^m` has normalized limit equal to the `m`th power of
the affine function in `(30b)`. The complete proof is in
`../not_new_scientific_knowledge/neutral-gamma-ratio-polynomial-jet-boundary-law.md`.

That companion theorem classifies arbitrary height sequences for coefficients in `C(G_theta)`.
The full differential-field extension is now proved in
`neutral-gamma-ratio-full-differential-boundary-depth-law.md`.
Writing `G_theta=uU`, its perturbative amplitude field `E=L(U)` is quasianalytic by formal HT.
Every finite tuple becomes polynomial in the single phase `u` over `E`; dividing its common gcd
leaves a Bezout-primitive tuple, which must survive at finite algebraic height order. Hence

```text
C(s)<G_theta> -> C[z] -> C.                               (31a)
```

This proves positively that exponentially small Stokes corrections are common projective scalars
in the one-phase field. The general neutral product also admits a complete proof. Write

```text
gamma=a+i theta,
v=s^a,
u=s^(i theta),
w=exp(beta s),
G=A w u v U,  hat U in 1+s^(-1)C[[s^(-1)]].              (31b)
```

Put `E=L(v,U)`. Formal HT of `Psi` makes the asymptotic map on `L` injective. Scaling the differential
indeterminate `G` while fixing the DA phases `w,u,v` makes analytic and formal `U` transcendental
over `L(w,u,v)`. Hence `E` is an injective upper power-Poincare field. Its generalized power
monomials are disjoint from the exponential monomials `w^k` and the imaginary-power monomials `u^l`,
so evaluation embeds `E[W,U_0]` by `(W,U_0)|->(w,u)`. Since `G=A w u v U`,

```text
K_G=L(G) subset E(w,u).                                    (31c)
```

Apply the proved bridge
`../not_new_scientific_knowledge/quasianalytic-exponential-log-phase-jet-law.md`.
Every finite tuple in `K_G` has a nonzero functional-projective limit in

```text
C[s,exp(beta s),exp(-beta s)],                             (31d)
```

and its polynomial recession lies in `R_beta`. The bridge's directional Vandermonde is the positive
phase-ideal resolution: along the actual translation direction, a nonzero finite phase polynomial
has a uniformly nonzero jet of bounded order. Therefore all flat and Stokes corrections remain
projectively scalar for every neutral signed product, not only for the one-ratio example.

## 7. Recurrent finite-phase theorem

Let `f` be holomorphic and vertically Bohr uniformly almost periodic on a vertical strip. Then

`[PROVED HERE for all M]`

```text
f DA over K_G  ->  rank_Q Gamma_B(f)<infinity.              (31)
```

The same holds for every continuous translation-equivariant observable of the zero divisor of a
nonzero `f`.

### Proof

Choose an ADE for `f` with a finite nonzero coefficient tuple in `K_G`. Bohr recurrence supplies
positive return times `T_n->infinity` for `f` and all derivatives occurring in the relation.

If `M!=0`, use the one-point projective boundary from Section 5. The translated relation converges
after functional normalization to a nontrivial autonomous ADE. The almost-periodic implicit-ADE
frequency theorem gives finite rank.

If `M=0`, the previous one-step proof is invalid. Equation `(30b)` shows that clearing denominators
and translating can produce polynomial coefficients, not coefficients in

```text
R_beta=C[exp(beta s),exp(-beta s)].                         (32)
```

The required positive replacement is the two-stage theorem `(31c)`--`(31d)`: every translated
coefficient tuple lands in a finite exponential-polynomial carrier, then polynomial recession leaves
a nonzero tuple over `R_beta`. The relative implicit-ADE frequency theorem finishes and gives finite
rational rank.

### Quantitative carrier budget

`[PROVED for all M]`

For `M!=0`, the proof retains the numerical bound from the autonomous implicit-ADE frequency
theorem. Choose a minimal limiting ADE of order `n`, and let `m` be the size of a finite
regular-sample atlas for its hull. Then

```text
rank_Q Gamma_B(f) <=2m(n+1).                               (33)
```

For `M=0`, put

```text
delta_G=rank_Q(beta Z) in {0,1};                           (34)

rank_Q Gamma_B(f) <=delta_G+2m(n+1).                       (35)
```

Here the polynomial jet tower contributes zero terminal character rank; its role is boundary depth,
not the additive term `delta_G`.

Let

```text
Lambda_N=<log p:p<=N prime>_Z.                             (36)
```

Unique factorization gives `rank_Q Lambda_N=pi(N)`. Therefore any recurrent output whose
Bohr-frequency group contains `Lambda_N` and which is DA over `K_G` must satisfy

```text
pi(N) <= delta_G+2m(n+1).                                 (37)
```

This is the positive **phase-budget law**. A cofinal construction over a fixed signed-Gamma field
must make its differential order, its regular-state atlas, or both grow so that

```text
m(n+1) >= (pi(N)-delta_G)/2.                               (38)
```

Equivalently, if order and atlas complexity stay bounded, the remaining prime directions must
already be present in a separate coefficient, operator, test-space, determinant, or divisor
carrier. The theorem specifies the resource a successful architecture must supply; it is not a
categorical rejection of any named RH criterion.

## 8. The law

The exact positive classification under the stated status split is:

```text
all orbit charges zero
  -> explicit DA exponential-rational carrier;

some orbit charge nonzero, total charge nonzero
  -> [PROVED] HT carrier with one-point projective boundary;

some orbit charge nonzero, total charge zero
  -> [PROVED] HT carrier with beta phase and finite polynomial jets. (39)
```

`[PROVED]` Finite signed archimedean Gamma data carries recurrent compact phase and noncompact
polynomial jet depth. The cyclic Stokes scale is projectively scalar after phase-jet normalization
and therefore supplies neither residual boundary depth nor compact character rank. The exact neutral
invariant is the finite directional phase jet, whose terminal character group is `beta Z`.

### Sharp neutral example

The rank-one alternative occurs already for

```text
G_*(s)=Gamma(2s)/Gamma(s)^2.                                (40)
```

The duplication formula gives

```text
G_*(s)=2^(2s-1)/sqrt(pi) * Gamma(s+1/2)/Gamma(s).           (41)
```

The two common-scale orbit charges are `+1` at `1/2+Z` and `-1` at `Z`. They are nonzero, so `G_*`
is HT, while their total is zero. Moreover

```text
G_*(s)~(1/(2sqrt(pi))) exp((log 4)s)s^(1/2).                (42)
```

After normalization along upper translates, subsequences converge to nonzero multiples of
`exp((log 4)s)`. The boundary frequency group is therefore exactly `(log 4)Z`. Thus the positive
rank-one alternative is attained, rather than being merely an upper bound.

## 9. Positive requirements for RH architectures

The nonzero-total-charge and neutral requirements below are proved.

1. **Connes / Hilbert--Polya / de Branges.** A finite Gamma ratio in a determinant or scattering
   factor supplies at most one recurrent boundary phase. The operator or canonical system must
   carry the infinite arithmetic character module independently, or its state complexity must obey
   the growth law `(38)`.
2. **Nyman--Beurling / Weil positivity.** Archimedean ratios may define weights and reflection
   phases, while the cofinal test spaces must retain unbounded prime-frequency dimension.
3. **Li criteria.** Finite Gamma normalization changes at most a finite-rank boundary carrier. The
   unbounded coefficient hierarchy must preserve an explicit infinite arithmetic module.
4. **Finite-prime approximants.** Retaining primes through `N` requires at least `pi(N)` phase
   dimensions in total. A fixed finite signed Gamma completion supplies at most `delta_G<=1`; the
   remaining phase budget must occur in a separate carrier or in unbounded order/atlas complexity
   as quantified by `(38)`, including inside a `1/log N` overlap layer.

This is a positive implementation law: a route is viable only after it names the carrier paying
the phase budget and proves that the completed constraint preserves that carrier cofinally.

## 10. Attacks and boundaries

1. **The DA/HT dichotomy is parent-theory reducible.** Gauss multiplication, recurrence, discrete
   residues, and the formal shift theorem already contain it. Candidate novelty is restricted to
   the projective boundary-rank classification and recurrent finite-phase consequence.
2. **Total charge is not the HT test.** Nonzero orbit charges may sum to zero. Those neutral products
   are still HT and can activate polynomial jets of every degree.
3. **Two scalar cluster phases form a directional-jet problem.** The logarithmic and exponential
   phases can meet on a nonprincipal common-zero locus, but their restriction to the actual
   translation direction has a uniformly finite nonzero Vandermonde jet.
4. **The rank-one alternative occurs.** The neutral HT product `(40)` realizes a genuine rank-one
   exponential boundary with frequency `log 4`; it does not prove the universal neutral bound.
5. **Moving phase cancellation activates jets.** Equation `(30b)` proves that a frozen logarithmic
   phase can turn first-order cancellation into a nonconstant affine local coordinate. The
   directional Vandermonde proves finite termination for every finite signed product.
6. **Negative slopes are excluded.** Reflection converts them to positive-slope Gamma ratios plus
   trigonometric factors. That finite-phase extension is not silently claimed.  The exact
   imaginary-slope boundary case relevant to Euler factors is isolated in
   `../not_new_scientific_knowledge/finite-euler-imaginary-gamma-reflection-weld.md`: the pair of
   slopes `+i log(p)/(2pi)` and `-i log(p)/(2pi)` reconstructs `1-p^(-s)` exactly and exposes the
   prime character as the trigonometric carrier.
7. **Arbitrary positive scales have a proved carrier extension.** The separate arbitrary-scale
   theorem
   `./incommensurable-gamma-orbit-free-quasianalyticity.md` replaces a common shift by the product
   of all matching commuting differences. Its scaled alien character selects the rational or HT
   branch exactly. The present card retains the commensurable hypothesis only for its canonical
   one-orbit notation and quantitative boundary bookkeeping.
8. **Meromorphic recurrent outputs are excluded.** The present theorem assumes holomorphic Bohr
   almost periodicity; moving poles require a spherical differential hull.
9. **Finite rank is not finite Fourier support.** The conclusion concerns the rational span of
   frequencies, not the number of Fourier terms.

## 11. Parent and novelty audit

`[NOVELTY UNVERIFIED]`

- Gauss multiplication and the Gamma recurrence supply the orbit normal form.
- Abramov and Chen--Singer discrete residues classify rational shift summability.
- Adamczewski--Dreyfus--Hardouin supply the formal rational-or-HT dichotomy.
- Difference Galois theory classifies differential algebraicity of many first-order shift-equation
  solutions; the DA/HT part should be presumed known or routine until an exact comparison says
  otherwise.
- Preliminary searches did not locate the one-phase full-field chain `(31a)`, its Bezout
  perturbative-survival mechanism, or the directional phase-jet classification `(31b)`--`(39)`.

The former rank-one conjecture is refuted by `(30b)`. Candidate scientific content has shifted to
the proved full-field polynomial boundary and the directional finite phase-jet classification for
arbitrary neutral products.

Primary adjacent sources:

- B. Adamczewski, T. Dreyfus, C. Hardouin, *Hypertranscendence and linear difference equations*,
  J. Amer. Math. Soc. 34 (2021), 475--503, DOI `10.1090/jams/960`.
- S. A. Abramov, *The summation of rational functions*, USSR Comput. Math. Math. Phys. 11 (1971),
  324--330.
- S. Chen, M. F. Singer, *Residues and telescopers for bivariate rational functions*, Adv. Appl.
  Math. 49 (2012), 111--133.
- NIST DLMF, Sections 5.5 and 5.11, Gamma multiplication and asymptotic expansions.
- `../not_new_scientific_knowledge/quasianalytic-one-phase-bezout-boundary-law.md`,
  the general one-phase bridge behind `(31a)`.

## 12. Lean status

The full theorem surface is formalized (axiom-clean; `propext, Classical.choice, Quot.sound` only).
In particular,
`formal/GaloisForLFunctions/HTGeometry/MeromorphicGammaSuperselection.lean` proves the genuine
meromorphic common-scale orbit-charge classification:

```text
differentialAlgebraicOver_gammaCommonScaleProductMero_of_charge_eq_zero
hypertranscendentalOver_gammaCommonScaleProductMero_of_charge_ne_zero
differentialAlgebraicOver_gammaCommonScaleProductMero_iff_charge_eq_zero
hypertranscendentalOver_gammaCommonScaleProductMero_iff_exists_charge_ne_zero
```

The supporting checked surface is:

- **Sharp neutral example `(40)`–`(41)`.** `formal/GaloisForLFunctions/HTGeometry/SignedGammaSharpExample.lean`
  proves `sharpNeutralGammaRatio`: for `Gamma s != 0`,
  `Gamma(2s)/Gamma(s)^2 = 2^(2s-1)/sqrt(pi) * Gamma(s+1/2)/Gamma(s)`, i.e. the Legendre-duplication
  reduction of `G_*` to its single common-scale orbit pair, exhibiting the two signed orbit charges
  `+1` (on `Gamma(s+1/2)`, class `1/2 + Z`) and `-1` (on `Gamma(s)`, class `Z`) explicitly. This is
  the exact `(41)` step; mathlib supplies the duplication input `Complex.Gamma_mul_Gamma_add_half`.
- **DA/HT vocabulary.** `Hypertranscendence.lean` (`DifferentiallyAlgebraic`, `Hypertranscendental`,
  `differentiallyAlgebraic_of_algebraic`) and `HypertranscendencePolynomial.lean`
  (`differentiallyAlgebraic_polynomial`, `differentiallyAlgebraic_const`) give the target predicates
  and the "adding a polynomial preserves DA" base cases used implicitly in `(9)`–`(10)`.
- **One-point projective boundary ingredient `(§5)`.** `GammaProjectiveBoundary.lean` already proves
  the two-jet projective boundary `Gamma/Gamma' -> 0` on upper vertical lines (the parent
  `finite-archimedean-gamma-product-boundary-law` mechanism the `M != 0` case invokes).
- Basic archimedean Gamma factors and recurrences: `ArchimedeanGamma.lean`, `GammaWeierstrass.lean`,
  `GammaDifferentialFE.lean`.
- **Phase-budget rank `(36)`.** `PrimeLogPhaseBudget.lean` proves
  `primeLog_primesBelow_linearIndependent`: the logarithms of the primes `< N` are `ℤ`-linearly
  independent (restriction of `RHTower.primeLog_linearIndependent`), and
  `primesBelow_card_eq_primeCounting'` gives their count `= Nat.primeCounting' N`. Together these are
  exactly `rank_ℚ Λ_N = π(N)`, the lower-bound side of the phase-budget inequality `(37)`. The upper
  bound `π(N) ≤ δ_G + 2m(n+1)` still needs the ADE/Bohr-hull machinery.

- **Gauss multiplication `(6)`, real and complex.** `GammaMultiplication.lean` proves the general
  finite-`n` Gauss multiplication (up to its multiplicative constant), which mathlib only had for
  `n = 2` (it flags general `n` as a TODO). Real form `gauss_multiplication`: for `n ≥ 1`, `s > 0`,
  `∏_{k<n} Γ((s+k)/n) = C_n · n^{-s} · Γ(s)` (`C_n = P(1)`), by the Bohr–Mollerup route
  (`multGammaProd_functional` = Gamma functional equation via product telescoping,
  `multGammaProd_log_convexOn` = log-convexity, then `eq_Gamma_of_log_convex`). Complex meromorphic
  form `gauss_multiplication_complex`: `∏_{k<n} Γ((s+k)/n)⁻¹ = C_n⁻¹ · n^s · Γ(s)⁻¹` for all `s ∈ ℂ`,
  by analytic continuation (`AnalyticOnNhd.eq_of_frequently_eq`) from the real case — the §2 orbit
  normal form in exactly the meromorphic category the card uses. All axiom-clean.

- **Discrete shift-residue obstruction `(13)`.** `DiscreteResidue.lean` proves
  `discreteResidue_shiftCoboundary_eq_zero`: modeling a fixed-order principal-part datum along one
  orbit as `P : α →₀ M` (pole location `↦` coefficient) with period shift `e : α ≃ α`, the discrete
  residue `∑ P` of a shift-coboundary `equivMapDomain e Q − Q` vanishes (the finite sum is
  shift-invariant). The contrapositive `not_shiftCoboundary_of_discreteResidue_ne_zero` is the exact
  step forcing hypertranscendence when some orbit charge `M_c ≠ 0`: a datum with nonzero discrete
  residue is not rationally shift-summable. Generalizes `OrbitBalance` (integer orbit) to any orbit
  and coefficient group. Axiom-clean.

The three generic framework steps this card shares with the Gamma-shift family are now formalized
abstractly and axiom-clean, and apply here directly:

- **Terminal one-point recession `C[z] -> C` `(31a)`.** `PolynomialOnePointRecession.lean`
  (`HTGeometry.finiteTuple_polynomial_onePoint_recession`,
  `HTGeometry.poly_scaled_translate_tendsto`) — a finite nonzero polynomial tuple, translated by
  `iT` and rescaled by `(iT)^{-d}`, converges to its nonzero leading-coefficient vector.
- **Finite commuting-shift peeling behind the DA/HT dichotomy `(8)`.**
  `FiniteCommutingShiftPeeling.lean` (`HTGeometry.shiftWord_dichotomy`) — the many-shift
  rational-or-HT dichotomy from the one-shift ADH input, taken as an interface hypothesis.
- **Phase-budget arithmetic complement `(37)`--`(38)`.** `ArithmeticComplementRank.lean`
  (`HTGeometry.finrank_le_arithmeticComplement_add`).

`MeromorphicGammaOrbit.lean` supplies the meromorphic Gamma orbit and logarithmic-derivative
machinery; `DigammaOrbitCarrier.lean` supplies the exact nonzero-charge orbit carrier;
`DirectionalVandermondePhaseJet.lean`, `PolynomialOnePointRecession.lean`, and
`GammaPhaseCompletion.lean` supply the finite phase-jet and two-stage boundary interfaces; and
`KolchinFrequencyBudgetPhase.lean` supplies the recurrent frequency and arithmetic-complement
consequences. Classical asymptotic and implicit-ADE parents appear as explicit structure fields or
theorem hypotheses, never as axioms or opaque declarations.

## Gates

- [x] common-scale orbit normal form proved
- [x] exact orbit-charge DA/HT dichotomy proved
- [x] nonzero-total-charge one-point boundary proved
- [x] former neutral finite-carrier lemma refuted by an exact Gamma-ratio family
- [x] all-degree polynomial jet alternative proved for `G_theta`
- [x] full one-phase neutral differential-field boundary proved
- [x] general directional phase-jet carrier law proved
- [x] recurrent finite-phase theorem proved for nonzero total charge
- [x] recurrent finite-phase theorem proved for the full one-phase neutral field
- [x] recurrent finite-phase theorem proved for general neutral total charge
- [ ] independent audit of the one-phase Bezout boundary theorem
- [ ] independent audit of the directional Vandermonde boundary theorem
- [ ] full parent-literature and priority audit
- [x] complete Lean theorem-surface formalization from explicit named classical inputs

## Lean update — DA direction of the dichotomy (8), polynomial case

`formal/GaloisForLFunctions/HTGeometry/ExpPolynomialDA.lean` proves
`differentiallyAlgebraic_cexp_mul_polynomial`: for every `β : ℂ` and polynomial `P`, the function
`s ↦ e^{βs}·P(s)` is differentially algebraic, axiom-clean. This is the DA half of `(8)`–`(10)` in the
polynomial-`R` case: when all shift-orbit charges vanish, `G = C₀·e^{βs}·R` (eq. 9), and for `R = P`
polynomial it satisfies the exhibited order-1 differential relation `P·G' − (β·P + P')·G = 0` (the
polynomial form of eq. 10). The differential polynomial is `P(X₀)·X₂ − (β·P(X₀) + P'(X₀))·X₁` in
`MvPolynomial (Fin 3) ℂ`; nonzeroness is witnessed at a non-root of `P`, and the vanishing on
`[s, G, G']` uses the product-rule derivative `G' = e^{βs}(βP + P')`. Extends
`differentiallyAlgebraic_cexp_linear` (the `R = 1` case) to `R` polynomial. The general rational `R`
reduces to this after clearing denominators (polynomial coefficients times `D²`), and the HT direction
(some charge nonzero) remains the deep ADH/discrete-residue input already carded above.

Also in `ExpPolynomialDA.lean`: `differentiallyAlgebraic_exp_polynomial` — `s ↦ e^{P(s)}` is
differentially algebraic for any polynomial `P` (order-1 relation `G' − P'·G = 0`), axiom-clean. This
is the DA phase-carrier when the exponential phase of the normal form is a general polynomial rather
than the linear `βs`, complementing `differentiallyAlgebraic_cexp_mul_polynomial`.

General entire DA carrier: `differentiallyAlgebraic_exp_poly_mul_poly (P Q)` — `s ↦ e^{P(s)}·Q(s)` is
differentially algebraic for polynomials `P, Q` (order-1 relation `Q·G' − (P'Q + Q')·G = 0`), axiom-clean.
Subsumes both `differentiallyAlgebraic_cexp_mul_polynomial` (linear phase) and
`differentiallyAlgebraic_exp_polynomial` (`Q = 1`); it is the complete DA exponential-rational carrier
of the orbit normal form `(9)` in the entire (polynomial phase and polynomial `R`) case.

Trigonometric reflection carriers (`TrigLinearDA.lean`, axiom-clean): `differentiallyAlgebraic_cos_linear`
and `differentiallyAlgebraic_sin_linear` — `s ↦ cos(c·s)` and `s ↦ sin(c·s)` are differentially
algebraic (order-2 relation `y'' + c²y = 0`; proved as two-term exponential sums via
`differentiallyAlgebraic_finset_expSum`). These are the trigonometric factors that reflection introduces
for negative-slope Gamma factors (§1, §10 attack 6); they stay inside the DA class, so the negative-slope
boundary extension keeps its non-Gamma carrier differentially algebraic.

## Lean update — directional phase-jet carrier (31b) and general-scale single-factor HT

Two further pieces are now formalized in Lean (axiom-clean; `propext, Classical.choice, Quot.sound`
only), both verified by single-file elaboration and wired into the `HTGeometry` umbrella.

- **Directional Vandermonde phase-jet carrier `(31b)`.**
  `formal/GaloisForLFunctions/HTGeometry/DirectionalVandermondePhaseJet.lean` proves
  `HTGeometry.phaseJet_exists_ne_zero`: for distinct frequencies `λ : Fin r → ℂ` (injective) and
  coefficients `c ≠ 0`, the finite phase polynomial `f(t) = ∑_j c_j·exp(λ_j·t)` has, at *every* base
  point `t₀`, a nonzero jet of order `< r` — the jet vector equals the transposed Vandermonde matrix
  of the `λ_j` applied to `(c_j·exp(λ_j·t₀))_j`, which is nonzero because distinct frequencies make
  `V(λ)` invertible (`Matrix.det_vandermonde_ne_zero_iff`) and `exp` never vanishes. Corollaries:
  `phasePolynomial_ne_zero_fun` (not identically zero) and `expLayer_jet_exists_ne_zero` (the finite
  growth-layer carrier `∑_{k≤N} c_k·exp(kβ·s)`, `β ≠ 0`). This is the directional finite phase-jet
  nonvanishing behind the neutral boundary and §10 attacks 3 and 5: a nonzero finite phase polynomial
  has a uniformly (base-point-independent) nonzero jet of bounded order, so a flat/Stokes correction
  cannot cancel the whole carrier — it stays projectively scalar.

- **General-scale single Gamma/digamma factor HT `(§1, §3)`.**
  `formal/GaloisForLFunctions/HTGeometry/ArgumentScalingInvariance.lean` first upgrades the scaling
  invariance of differential algebraicity to remove the smoothness hypothesis:
  `differentiallyAlgebraic_comp_const_mul_iff_uncond` and
  `hypertranscendental_comp_const_mul_iff_uncond` hold for every `c ≠ 0` with *no* `ContDiff`
  assumption, via the unconditional scaled chain rule `iteratedDeriv_comp_mul_left_uncond`
  (`f(c·)⁽ⁿ⁾ = cⁿ·f⁽ⁿ⁾(c·)`, built on mathlib's `0`-fallback `deriv_comp_mul_left`) and the
  argument-scaling jet substitution `jetArgScaleSub`. This removes exactly the obstruction the earlier
  `SignedGammaHypertranscendental` docstring flagged (scaling invariance "requires global smoothness,
  which `Γ` lacks at its poles"). Consequently `hypertranscendental_gamma_affine` and
  `hypertranscendental_digamma_affine` prove that `Γ(c·s + d)` and `ψ(c·s + d)` are hypertranscendental
  for *every* `c ≠ 0` — the general commensurable-scale single Gamma orbit factor and its
  logarithmic-derivative carrier, at genuine scale, not only the unit scale of
  `hypertranscendental_gamma_add_const`.

The single-orbit / nonzero-total-charge HT direction reduces (via `GammaLogDeriv.digamma_add_nat`
collapse `∑_j m_j ψ(w+n_j) = (∑ m_j) ψ(w) + rational`, `∑ m_j = M ≠ 0`, and
`hypertranscendental_digamma_affine`) to preservation under a rational perturbation. The next
checked module, `DigammaRationalCarrier.lean`, supplies exactly that off-pole
jet-annihilator transfer.

## Lean update — rational carrier closes the single-orbit nonzero-charge HT direction

Three further axiom-clean pieces (`propext, Classical.choice, Quot.sound` only), wired into the
`HTGeometry` umbrella.

- **Nonzero-charge jet collapse `(§3, eq. 13)`.** `PolygammaShift.lean` now also proves
  `HTGeometry.iteratedDeriv_digamma_charge_general`: for arbitrary charges `m : Fin d → ℂ` and integer
  shifts `nn : Fin d → ℕ`, off the poles,
  `∑ₖ mₖ ψ⁽ʲ⁾(w + nₖ) = (∑ₖ mₖ)·ψ⁽ʲ⁾(w) + ∑ₖ mₖ ∑_{i<nₖ} (−1)ʲ·j!/(w+i)^{j+1}` at every jet order
  `j`. This is the `hcharge`-free companion of `iteratedDeriv_digamma_charge_collapse`: the surviving
  transcendental jet is exactly the total-charge multiple `M·ψ⁽ʲ⁾(w)` (`M = ∑ₖ mₖ`) plus a rational
  tail, i.e. the eq.-(13) obstruction datum when `M ≠ 0`.

- **Polynomial-perturbation carrier.** `DigammaPolynomialCarrier.lean` proves
  `hypertranscendental_smul_digamma_add_polynomial`: for `M ≠ 0` and any polynomial `p`,
  `M·ψ(t) + p(t)` is hypertranscendental. A hypothetical algebraic differential relation is transported
  by the invertible affine jet substitution `Y_j ↦ M·Y_j + p⁽ʲ⁾(point)` into an off-pole digamma jet
  annihilator, killed by `digamma_jet_annihilator_eq_zero`; invertibility (`M ≠ 0`) makes the transport
  nonzero.

- **Rational-perturbation carrier (the crux).** `DigammaRationalCarrier.lean` proves
  `hypertranscendental_smul_digamma_add_ratfunc`: for `M ≠ 0` and any rational function `A/B`
  (`B ≠ 0`), `M·ψ(t) + A(t)/B(t)` is hypertranscendental. This is the exact closure input the previous
  §12 note flagged as the remaining open target ("adding a rational function to the hypertranscendental
  scaled-digamma carrier preserves hypertranscendence"). The proof denominator-clears every jet to the
  common power `B^{n+1}` (using `(A/B)⁽ʲ⁾ = C_j/B^{j+1} = C_j·B^{n−j}/B^{n+1}` from
  `exists_poly_iteratedDeriv_ratEval`), transports the annihilator through the homogeneous-degree
  bookkeeping of `MvPolynomial.homogeneousComponent` (a single homogeneous variable-scaling lemma
  `isHomogeneous_eval₂_scale` discharges both the annihilation and the nonzeroness), applies the `B`
  factor so `B·P` annihilates the digamma jets off *every* pole (`polyJetEval_offPole_eq_zero` then
  gives `B·P = 0 ⇒ P = 0`), and proves `P ≠ 0` by mapping to `RatFunc ℂ`, where the affine substitution
  `Y_j ↦ M·Y_j + (A/B)⁽ʲ⁾` is an invertible isomorphism (`bind₁ ρ` with explicit inverse). Reusable
  generic lemmas added: `isHomogeneous_eval₂_scale` / `isHomogeneous_eval₂Hom_scale` /
  `isHomogeneous_bind₁_scale`, `map_homogeneousComponent`, `sum_homogeneousComponent_of_le`,
  `eval₂Hom_reshapeJet`.

Together these close the `d = 1`, single-orbit, **nonzero-total-charge** hypertranscendental direction
at the carrier level: `iteratedDeriv_digamma_charge_general` reduces the orbit carrier
`∑ₖ mₖ ψ(w+nₖ)` (`M = ∑ₖ mₖ ≠ 0`) to `M·ψ(w) + rational`, and
`hypertranscendental_smul_digamma_add_ratfunc` proves that carrier is hypertranscendental. The exact
orbit-function assembly `Hypertranscendental (fun w => ∑ₖ mₖ ψ(w+nₖ))` is now closed — see the next
section (`hypertranscendental_digamma_orbit_charge`).

## Lean update — orbit-function assembly closes the single-orbit nonzero-charge HT direction

`DigammaOrbitCarrier.lean` proves the exact orbit-function statement, axiom-clean
(`propext, Classical.choice, Quot.sound` only), wired into the `HTGeometry` umbrella:

- **`hypertranscendental_digamma_orbit_charge`.** For integer shifts `nn : Fin d → ℕ` and charges
  `m : Fin d → ℂ` with total charge `M = ∑ₖ mₖ ≠ 0`, the orbit carrier `Ψ(w) = ∑ₖ mₖ ψ(w + nₖ)` is
  hypertranscendental — the `d`-term, single-`H`-orbit, nonzero-total-charge HT statement of `§3`
  (`Ψ = G'/G` for one common-scale Gamma orbit product with charges `mₖ`).

This is the assembly the previous §12 note flagged as still open ("assembling this into
`Hypertranscendental (fun w => ∑ₖ mₖ ψ(w+nₖ))` for the exact orbit function"). It is a direct
instance of the general off-pole criterion `hypertranscendental_digamma_plus_offpole_rational`
(`DigammaRationalCarrier.lean`): the jet split is supplied by
`HTGeometry.iteratedDeriv_digamma_charge_general` (linearity + integer-shift law), giving
`Ψ⁽ʲ⁾(z) = M·ψ⁽ʲ⁾(z) + ∑ₖ mₖ ∑_{i<nₖ} (−1)ʲ·j!/(z+i)^{j+1}` off the poles, and the rational tail is
exhibited as the single fraction `C_j/B^{j+1}` over the common denominator `B = ∏_{i<N}(X+i)` with
`N = maxₖ nₖ` and `C_j` the erase-product numerator (partial-fraction identity closed by
`Finset.mul_prod_erase` + `field_simp`). No new axioms; no `sorry`.

The general multi-orbit product is closed by `MeromorphicGammaSuperselection.lean`. The boundary and
frequency consequences are closed at their exact reusable interfaces by `GammaPhaseCompletion.lean`
and `KolchinFrequencyBudgetPhase.lean`. These modules were checked by exact targeted builds when
their `.olean` files were absent and by direct single-file elaboration; no full build was run.
