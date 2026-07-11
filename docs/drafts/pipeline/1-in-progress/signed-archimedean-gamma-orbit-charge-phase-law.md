# Signed archimedean Gamma products obey an orbit-charge phase law

- **ID:** `signed-archimedean-gamma-orbit-charge-phase-law`
- **Stage:** 1-in-progress / neutral boundary open
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PARTIALLY PROVED] [OPEN CORE] [NOVELTY UNVERIFIED]`
- **Statement:** A signed finite Gamma product with positive commensurable scales is differentially
  algebraic exactly when every shift-orbit charge vanishes; otherwise it is hypertranscendental.
  For nonzero total charge its projective boundary is one point. `[CONJECTURE]` For neutral total
  charge its upper projective differential boundary has Bohr rank at most one; this would force
  finite rational phase rank for every holomorphic recurrent object DA over its field.

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

## 6. Neutral HT products have boundary phase rank at most one

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

### Finite-transseries boundary lemma

`[OPEN CORE]` Let

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

It does not yet justify the required sequential descent. A higher layer may vanish at the limiting
phase while its value at the moving phase decays at a rate coupled to a power of `T_n`; several
such layers can then cancel after normalization. To prove `(26)`, one must show that this coupled
descent terminates at a finite algebraic layer, rather than leaving a beyond-all-orders Stirling
remainder as the first nonzero boundary term. That is the exact open lemma:

> **Neutral finite-carrier lemma.** Every nonzero tuple `(25)` and every sequence `T_n->infinity`
> admit a subsequence and scalar normalization for which a nonzero limit exists in the finite
> exponential space `span_C{exp(k beta s):0<=k<=N}`.

A proof must control moving phase zeros uniformly; fixed-phase formal transcendence alone is
insufficient. Until this lemma is proved, `(26)`--`(27)` and every neutral-case consequence below
remain conjectural.

The beyond-all-orders alternative is genuine rather than rhetorical. Exponentially improved Gamma
asymptotics contain Stokes terms on the lattice `exp(+-2 pi i s/H)`. Thus a complete proof must
either exclude their promotion by a moving phase cancellation or prove the stronger positive
carrier statement

```text
neutral boundary support subset
  {k beta + (2 pi i/H) ell : k,ell in Z}.                  (31a)
```

`[CONJECTURE]` Equation `(31a)` is the **archimedean--Stokes carrier law**: every neutral signed
Gamma boundary must expose either the recurrent `beta` direction or an explicit common-scale
Stokes direction. It converts the cancellation gap into a carrier classification problem.

## 7. Recurrent finite-phase theorem

Let `f` be holomorphic and vertically Bohr uniformly almost periodic on a vertical strip. Then

`[PROVED HERE for M!=0] [CONJECTURE for M=0]`

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

If `M=0`, clear coefficient denominators and apply the boundary lemma to the return sequence. After
scalar normalization and subsequence extraction, the translated relation converges to a nontrivial
ADE for `f` whose coefficients are exponential polynomials in `exp(beta s)`. Apply the relative
implicit-ADE frequency theorem with coefficient domain

```text
R_beta=C[exp(beta s),exp(-beta s)].                         (32)
```

Its frequency group is `beta Z`, of rational rank zero or one. The solution contributes only
finitely many further rationally independent frequencies. Conditional on the neutral
finite-carrier lemma, this proves the neutral instance of `(31)` and the divisor statement.

### Quantitative carrier budget

`[PROVED for M!=0] [CONDITIONAL ON THE NEUTRAL FINITE-CARRIER LEMMA for M=0]`

The proof retains the numerical bound from the relative implicit-ADE frequency theorem. Choose a
minimal limiting ADE of order `n`, and let `m` be the size of a finite regular-sample atlas for its
joint hull. Put

```text
delta_G=0  if M!=0,
delta_G=rank_Q(beta Z) in {0,1}  if M=0.                   (33)
```

Then

```text
rank_Q Gamma_B(f) <= delta_G+2m(n+1).                     (34)
```

Indeed, the nonzero-charge boundary equation is autonomous, while the neutral boundary equation
has coefficients in `R_beta`; their coefficient-frequency ranks are respectively `0` and
`delta_G`. The relative theorem bounds the additional solution rank by `2m(n+1)`.

Let

```text
Lambda_N=<log p:p<=N prime>_Z.                             (35)
```

Unique factorization gives `rank_Q Lambda_N=pi(N)`. Therefore any recurrent output whose
Bohr-frequency group contains `Lambda_N` and which is DA over `K_G` must satisfy

```text
pi(N) <= delta_G+2m(n+1).                                 (36)
```

This is the positive **phase-budget law**. A cofinal construction over a fixed signed-Gamma field
must make its differential order, its regular-state atlas, or both grow so that

```text
m(n+1) >= (pi(N)-delta_G)/2.                               (37)
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
  -> [PROVED] HT and [CONJECTURE] projective boundary frequency rank <=1. (38)
```

`[PROVED when M!=0; CONJECTURE when M=0]` Finite signed archimedean Gamma data carries at most one
recurrent phase direction. It may weight, reflect, or rotate an arithmetic carrier, but an infinite
prime-frequency module must be supplied separately.

### Sharp neutral example

The rank-one alternative occurs already for

```text
G_*(s)=Gamma(2s)/Gamma(s)^2.                                (39)
```

The duplication formula gives

```text
G_*(s)=2^(2s-1)/sqrt(pi) * Gamma(s+1/2)/Gamma(s).           (40)
```

The two common-scale orbit charges are `+1` at `1/2+Z` and `-1` at `Z`. They are nonzero, so `G_*`
is HT, while their total is zero. Moreover

```text
G_*(s)~(1/(2sqrt(pi))) exp((log 4)s)s^(1/2).                (41)
```

After normalization along upper translates, subsequences converge to nonzero multiples of
`exp((log 4)s)`. The boundary frequency group is therefore exactly `(log 4)Z`. Thus the positive
rank-one alternative is attained, rather than being merely an upper bound.

## 9. Positive requirements for RH architectures

The nonzero-total-charge requirements below are proved. Their neutral-total-charge versions are
conditional on the neutral finite-carrier lemma.

1. **Connes / Hilbert--Polya / de Branges.** A finite Gamma ratio in a determinant or scattering
   factor supplies at most one recurrent boundary phase. The operator or canonical system must
   carry the infinite arithmetic character module independently, or its state complexity must obey
   the growth law `(37)`.
2. **Nyman--Beurling / Weil positivity.** Archimedean ratios may define weights and reflection
   phases, while the cofinal test spaces must retain unbounded prime-frequency dimension.
3. **Li criteria.** Finite Gamma normalization changes at most a finite-rank boundary carrier. The
   unbounded coefficient hierarchy must preserve an explicit infinite arithmetic module.
4. **Finite-prime approximants.** Retaining primes through `N` requires at least `pi(N)` phase
   dimensions in total. A fixed finite signed Gamma completion supplies at most `delta_G<=1`; the
   remaining phase budget must occur in a separate carrier or in unbounded order/atlas complexity
   as quantified by `(37)`, including inside a `1/log N` overlap layer.

This is a positive implementation law: a route is viable only after it names the carrier paying
the phase budget and proves that the completed constraint preserves that carrier cofinally.

## 10. Attacks and boundaries

1. **The DA/HT dichotomy is parent-theory reducible.** Gauss multiplication, recurrence, discrete
   residues, and the formal shift theorem already contain it. Candidate novelty is restricted to
   the projective boundary-rank classification and recurrent finite-phase consequence.
2. **Total charge is not the HT test.** Nonzero orbit charges may sum to zero. Those neutral products
   are still HT; `[CONJECTURE]` they form the rank-one boundary case.
3. **Two scalar cluster phases need not mean rank two.** At every algebraic Stirling layer, the phase
   `exp(i Im(gamma)log T)` affects only constants and local-variable dependence comes only from
   `exp(beta s)`. The open issue is whether moving cancellation can promote a Stokes layer.
4. **The rank-one alternative occurs.** The neutral HT product `(39)` realizes a genuine rank-one
   exponential boundary with frequency `log 4`; it does not prove the universal neutral bound.
5. **Moving phase cancellation is the open boundary.** Fixed-phase formal transcendence does not
   by itself control phase zeros approached at `T_n`-dependent algebraic rates. A proof must force a
   finite exponential layer to survive, or identify the positive Stokes carrier that necessarily
   replaces it.
6. **Negative slopes are excluded.** Reflection converts them to positive-slope Gamma ratios plus
   trigonometric factors. That finite-phase extension is plausible but is not silently claimed.
7. **Incommensurable positive scales are excluded.** They have no common rational shift equation and
   require a genuine multi-valuation replacement.
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
- Preliminary searches did not locate the three-level orbit-charge/projective-boundary law `(38)`
  or its arbitrary recurrent-source consequence `(31)`.

The candidate scientific content, still `[CONJECTURE]`, is that neutral HT Gamma ratios acquire
only a rank-one projective boundary rather than an infinite recurrent hull, and that this boundary
rank controls every HAP element DA over the full differential field.

Primary adjacent sources:

- B. Adamczewski, T. Dreyfus, C. Hardouin, *Hypertranscendence and linear difference equations*,
  J. Amer. Math. Soc. 34 (2021), 475--503, DOI `10.1090/jams/960`.
- S. A. Abramov, *The summation of rational functions*, USSR Comput. Math. Math. Phys. 11 (1971),
  324--330.
- S. Chen, M. F. Singer, *Residues and telescopers for bivariate rational functions*, Adv. Appl.
  Math. 49 (2012), 111--133.
- NIST DLMF, Sections 5.5 and 5.11, Gamma multiplication and asymptotic expansions.
- G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, Proc. R. Soc. Edinburgh Sect. A 145 (2015), 571--596, DOI
  `10.1017/S0308210513001558`. Its explicit exponentially improved remainders exhibit the
  `exp(+-2 pi i z)` Stokes lattice that must be controlled in the neutral open core.

## 12. Lean status

The tree contains individual Gamma recurrences and basic archimedean factors, but not Gauss
multiplication in the needed meromorphic form, discrete shift residues, formal transseries,
differential hypertranscendence, or holomorphic Bohr-frequency hulls. No partial wrapper would
formalize the claim. Stage 3 requires the whole theorem unconditionally in Lean.

## Gates

- [x] common-scale orbit normal form proved
- [x] exact orbit-charge DA/HT dichotomy proved
- [x] nonzero-total-charge one-point boundary proved
- [ ] neutral finite-carrier lemma proved
- [x] recurrent finite-phase theorem proved for nonzero total charge
- [ ] recurrent finite-phase theorem proved for neutral total charge
- [ ] independent audit of the neutral boundary lemma
- [ ] full parent-literature and priority audit
- [ ] complete unconditional Lean formalization
