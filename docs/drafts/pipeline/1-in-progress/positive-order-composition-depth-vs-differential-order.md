# Positive-order composition depth versus algebraic-differential order

- **ID:** `positive-order-composition-depth-vs-differential-order`
- **Stage:** 1-in-progress
- **Type:** THEOREM + `[CONJECTURE]`
- **Scientific status:** `[NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; excludes divisor interpolation, DA translation spectra, elliptic-gamma modules, and cross-curve residue reciprocity
- **Source:** the entire-composition OR law; Polya's maximum-modulus estimate for entire compositions; Steinmetz's second-order homogeneous growth bound; Hayman's iterated-growth conjecture.

## Medalist lens

Finite composition does not change the DA/HT bit except by Boolean OR. The nontrivial quantity is therefore not whether a finite composite is DA, but how much finite algebraic-differential order is required to encode its global compositional depth.

The constraint-side question is:

> Can differential order be a finite budget for genuinely transcendental compositional layers?

This asks for a static obstruction. It does not evolve a function along an iteration flow.

## Definition

For a transcendental entire function `F`, define its **positive-lower-order composition depth** `cd_+(F)` to be the supremum of integers `d` for which

`F = f_1 o f_2 o ... o f_d`,

with every `f_j` transcendental entire and of positive Nevanlinna lower order. Affine and polynomial factors do not count.

For a DA entire function `F`, let `ord_DA(F)` be the least derivative order of a nonzero algebraic differential equation over `C(z)` satisfied by `F`.

## Candidate law

`[CONJECTURE]` For every DA entire function,

`cd_+(F) <= ord_DA(F)`.

Consequently, an entire function admitting positive-lower-order decompositions of arbitrarily large finite depth would be HT.

The positive-lower-order hypothesis is load-bearing. Polya's exceptional finite-order composition case uses a zero-order outer factor. Third-order ADEs can have zero-order transcendental entire solutions (Valiron--Strelitz), but those solutions do not themselves supply positive-lower-order composition layers.

## Proved growth-depth law

`[PROVED]` If

`F = f_1 o ... o f_d`

with every factor transcendental entire of positive lower order, then there are `a,c>0` such that, for all sufficiently large `r`,

`T(Cr,F) >= exp_(d-1)(a r^c)`

for a fixed dilation constant `C>1`; here `exp_k` is the `k`-fold exponential and `exp_0(x)=x`.

### Proof

Polya's composition estimate gives, for nonconstant entire `u` and transcendental entire `v`,

`M(r,u o v) >= M(c_u M(r/2,v),u)`

for all sufficiently large `r` and some `c_u>0`.

Positive lower order of `u` gives `log M(R,u) >= R^alpha` eventually for some `alpha>0`. Hence

`log M(r,u o v) >= c M(r/2,v)^alpha`.

Iterating this inequality through the `d` factors and using positive lower order of the innermost factor produces an `(d-1)`-fold exponential lower bound for `log M(r,F)`, after harmless rescaling of `r`. The standard comparison

`log M(r,F) <= 3 T(2r,F)`

transfers the bound to the Nevanlinna characteristic. No numerical experiment enters.

## First sharp differential-order case

`[NOVELTY UNVERIFIED] [PROVED]` Let `F` be an entire solution of a homogeneous second-order algebraic differential equation with polynomial coefficients. Then

`cd_+(F) <= 2`.

### Proof

Steinmetz's homogeneous second-order growth theorem gives

`T(r,F) = O(exp(r^b))`

for some `b>1`. A factorization into three positive-lower-order transcendental entire factors would give, by the proved growth-depth law,

`T(Cr,F) >= exp(exp(a r^c))`,

contradicting the Steinmetz bound. Any deeper factorization contains the same three-layer growth obstruction. Therefore `cd_+(F)<=2`.

The bound is sharp: `F(z)=exp(exp z)` has `cd_+(F)>=2` and satisfies the homogeneous second-order ADE

`F F'' - (F')^2 - F F' = 0`.

## Exact all-order affine-exponential law

Write `E_1(z)=exp z` and `E_(k+1)(z)=exp(E_k(z))`.

`[NOVELTY UNVERIFIED] [PROVED]` More generally, if `f_j(w)=a_j+b_j exp(c_j w)` with real `a_j` and `b_j,c_j>0`, then

`ord_DA(f_n o ... o f_1)=cd_+(f_n o ... o f_1)=n`.

In particular, for every `n>=1`,

`cd_+(E_n)=ord_DA(E_n)=n`.

Thus every affine-exponential covering layer costs exactly one unit of minimal algebraic-differential order throughout a nontrivial parameter family. In particular, the candidate inequality, if true, is sharp in every order.

The full parameter-family proof is separated in `2-fully-proven/needs-audit/exponential-tower-exact-differential-order.md`. The lemmas below record the normalized tower core used there.

### Algebraic-independence lemma

For every `n`, the functions `E_1,...,E_n` are algebraically independent over `C(z)`.

Indeed, restrict a putative polynomial relation to the positive real axis and order its monomials lexicographically from the highest tower variable downward. A larger power of `E_k=exp(E_(k-1))` dominates every fixed product of powers of `z,E_1,...,E_(k-1)`. The lexicographically largest monomial therefore strictly dominates the finite sum of all remaining monomials, after clearing rational denominators. Cancellation is impossible.

### Triangular observability lemma

Let `R_m=C[p_1,...,p_m]` carry the derivation

`delta_m(p_k)=p_k(1+p_1+...+p_(k-1))`,

and put `q_m=p_1+...+p_m`. Then

`q_m, delta_m(q_m), ..., delta_m^(m-1)(q_m)`

are algebraically independent.

Let `J_m` be their Jacobian determinant with respect to `p_1,...,p_m`. Write `s_m=1+q_(m-1)` and regard `delta_m` as

`delta_(m-1) + p_m s_m partial_(p_m)`.

For `f_r^(m)=delta_m^r(q_m)`, induction on `r` gives

`f_r^(m)=f_r^(m-1)+p_m B_r`,

where `B_0=1` and

`B_(r+1)=(delta_(m-1)+s_m)B_r`.

Every row of `J_m` is therefore affine in `p_m`. The coefficient of `p_m^(m-1)` in `J_m` is, up to sign,

`det partial(B_1,...,B_(m-1))/partial(p_1,...,p_(m-1))`.

The recurrence for `B_r` is triangular in the jets of `s_m`:

`B_r=delta_(m-1)^(r-1)(s_m) + polynomial(s_m,...,delta_(m-1)^(r-2)(s_m))`.

Hence this last determinant is exactly `J_(m-1)`. Since `J_1=1`, induction shows that the leading coefficient of `J_m` is nonzero, and therefore `J_m!=0` for every `m`.

### Minimal differential order

Fix `n>=3`, put `y=E_n`, and set

`p_k=E_1...E_k`, for `1<=k<=n-1`.

These prefix products satisfy the triangular derivation above. Moreover,

`p_(n-1)=y'/y`,

`p_(n-1)'/p_(n-1)=1+p_1+...+p_(n-2)`.

Thus the field generated by `y,y',...,y^(n-1)` contains `p_(n-1)` and the first `n-2` jets, counting the function itself, of `q_(n-2)`. By the observability lemma those jets are algebraically independent, so `p_1,...,p_(n-2)` are algebraic over their field. The identities

`E_1=p_1`, `E_k=p_k/p_(k-1)`

then show that the tower field `C(z)(E_1,...,E_n)` is algebraic over `C(z)(y,y',...,y^(n-1))`.

The tower field has transcendence degree `n` by the algebraic-independence lemma. Therefore `y,y',...,y^(n-1)` are algebraically independent, and no ADE of order below `n` exists. All derivatives of `y` lie in the differential field `C(z)(E_1,...,E_n)` of transcendence degree `n`, so `y,y',...,y^(n)` are algebraically dependent. Hence `ord_DA(E_n)=n`. The cases `n=1,2` follow directly, with the order-two lower bound also implied by first-order pseudo-primality.

Finally, the displayed composition of `E_n` into `n` exponential factors gives `cd_+(E_n)>=n`. Since every `E_n` has nonnegative Taylor coefficients, `M(r,E_n)=E_n(r)` on positive radii, so `T(r,E_n)<=log M(r,E_n)=E_(n-1)(r)` has exponential height `n-1`. The proved growth-depth law therefore rules out `n+1` positive-lower-order factors. Thus `cd_+(E_n)=n`.

## Attack

1. `[SEARCH]` Order one is classical: entire solutions of first-order ADEs are pseudo-prime, so `cd_+<=1`.
2. `[SEARCH]` Finite-order second-order ADE solutions are pseudo-prime; the new case above concerns the allowed infinite-order stratum and uses the sharp homogeneous growth ceiling.
3. `[PROVED]` Dropping positive lower order invalidates the growth proof. Polya permits finite-order composites with zero-order outer factor. This does not falsify `cd_+`, because a zero-lower-order factor is excluded from the counted decompositions.
4. `[OPEN CORE]` For a general order-`n` ADE, the needed upper bound is essentially Hayman's conjectural `exp_(n-1)(polynomial)` growth ceiling. The depth law cannot simply assume that conjecture under a new name.
5. `[PROVED]` The all-order triangular observability lemma gives exact order for every real positive affine-exponential cascade; this family saturates the candidate bound in every order.
6. `[ANTI-THEATRE]` The Boolean OR law is a source-known bridge and is not the scientific claim. The candidate knowledge is the quantitative order/depth obstruction and its sharp second-order case.

### Valiron boundary: resolved non-falsifier

`[SEARCH] [PROVED]` Strelitz's proof of the Valiron theorem begins with a theta product `theta(u)`, sets `v=u-u^(-1)`, and descends to an entire zero-order function `F(v)` before rationalizing the transformed third-order equation. This is an algebraic coordinate descent, not an entire-function decomposition of `F`.

Moreover, Valiron's function has lower order zero, so even a genuine occurrence of it as an outer composition factor would not be counted by `cd_+`. The earlier proposal to test `V o exp_k` therefore did not test the stated candidate law. The positive-depth boundary is instead represented in every order by `E_n`, whose minimal ADE order is exactly `n`.

## RH pressure test, not research selector

The completed xi function has finite order, so Polya already forces any nontrivial entire compositional factorization into the exceptional zero-order-outer regime. The present theorem does not imply RH and does not constrain zeros. Its possible RH value is negative but useful: a finite positive-order composition model cannot be the missing handle for xi; an RH route would have to use the infinite Euler/archimedean constraint, a zero-order outer factor, or a different non-compositional invariant.

## Novelty and significance gates

- **Proof gate:** growth-depth lemma, homogeneous second-order corollary, triangular observability lemma, and exact all-order affine-exponential cascade law complete on paper.
- **Significance gate:** the cascade law identifies an exact equality between global composition depth and minimal ADE order throughout a parameter family in every finite order. It supplies a stable sharp family for any general depth budget and turns unbounded positive-order depth into a concrete HT obstruction.
- **Parent-theory gate:** open. The result may be judged a short Polya--Steinmetz synthesis.
- **Literature gate:** preliminary searches found factorization/pseudo-primality results and growth estimates, but no explicit `cd_+ <= 2` theorem or general differential-order/composition-depth law. A full factorization and composite-growth audit remains required.
- **Scientific label:** `[NOVELTY UNVERIFIED]`, not candidate new scientific knowledge yet.

## Next move

Complete the literature gate for the separated fully-proven cascade card. Otsubo's minimal Liouville-chain theorem has now been checked in full and does not subsume it. In parallel, attack the general inequality away from affine-exponential cascades: the remaining mathematical obstruction is the absence of a general order-`n` growth ceiling, not the sharpness family.

## Gates

- [x] Competing composition ideas reduced to one invariant.
- [x] Local-germ counterexample and source-known global OR law separated.
- [x] Paper proof of the growth-depth lemma.
- [x] Sharp homogeneous second-order corollary.
- [ ] Full parent-theory and literature audit.
- [x] Valiron zero-order construction classified and removed as a false falsifier.
- [x] All-order exponential-tower observability lemma proved on paper.
- [x] Exact identity `cd_+(E_n)=ord_DA(E_n)=n` proved on paper.
- [ ] Lean only after the mathematical novelty gate and the repository's numerical pre-certification rule can both be satisfied.

## Primary references checked

1. G. Polya, *On an integral function of an integral function*, J. London Math. Soc. 1 (1926), 12--15.
2. N. Steinmetz, *Uber die faktorisierbaren Losungen gewohnlicher Differentialgleichungen*, Math. Z. 170 (1980), 169--180.
3. L.-W. Liao and C.-C. Yang, *On the growth and factorization of entire solutions of algebraic differential equations*, Ann. Acad. Sci. Fenn. Math. 25 (2000), 73--84.
4. W. K. Hayman, iterated-growth conjecture as quoted and scoped in Liao--Yang (2000).
