# Rational-power canonical products have an exact cyclic-norm parity law

- **ID:** `rational-power-canonical-product-cyclic-norm-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HYPERTRANSCENDENCE / COMPLETION LAW
- **Scientific status:** `[PROVED HERE] [PRELIMINARY NOVELTY PASS] [NOT AN RH RESULT]`
- **Source:** Bank's integer-power canonical-product theorem, the publication-ready
  multiple-elliptic-Gamma completion law, and the corpus search for a completion-stable
  hypertranscendence invariant
- **Statement:** For a reduced positive rational exponent `a=p/q`, the `q`-fold
  root-of-unity norm of the canonical product with zeros `-n^a` is exactly the
  integer-power product `W_p((-1)^(q+1)z^q)`.  Consequently the norm is DA exactly when
  `p` is even, and `W_(p/q)` itself is HT whenever `p` is odd.

## Goal

Replace the false heuristic

```text
finite HT stages should remain HT after completion
```

by an exact completion law for one classical parameterized family.  The theorem identifies two
separate pieces of arithmetic:

```text
q = finite monodromy orbit needed to close the completion,
p mod 2 = differential-algebraic phase of the completed orbit.
```

It strictly extends the known odd-integer hypertranscendence theorem to a dense set of
noninteger rational exponents.  It does not constrain a zeta zero and is not advertised as an
RH theorem.

## 1. Canonical products

For `g>=0`, put

```text
E_g(w)=(1-w) exp(sum_(r=1)^g w^r/r).
```

For a positive real `a`, let

```text
g(a)=floor(1/a),
W_a(z)=product_(n>=1) E_(g(a))(-z/n^a).                    (1)
```

The choice `g(a)` is admissible because

```text
a(g(a)+1)>1.
```

Thus `(1)` converges locally uniformly, is entire of order `1/a`, and has simple zeros exactly
at `-n^a`, `n>=1`.

Let `a=p/q` with coprime positive integers `p,q`, and let

```text
omega=exp(2 pi i/q).
```

Define the finite cyclic norm

```text
N_(p/q)(z)=product_(j=0)^(q-1) W_(p/q)(omega^j z).         (2)
```

## 2. Root-of-unity primary-factor identity

Let `g>=0`, `q>=1`, and put `h=floor(g/q)`.  For every complex `u`,

```text
product_(j=0)^(q-1) E_g(-omega^j u)
  =E_h((-1)^q u^q).                                       (3)
```

Indeed,

```text
product_j (1+omega^j u)=1-(-u)^q,
sum_(j=0)^(q-1) omega^(jr)
  = q  if q divides r,
  = 0  otherwise.
```

The exponential part of the left side of `(3)` is therefore

```text
exp(sum_(ell=1)^h (-1)^(q ell)u^(q ell)/ell),
```

which is exactly the exponential part on the right.

For `g=g(p/q)=floor(q/p)`,

```text
floor(g/q)=floor(1/p).                                    (4)
```

If `p=1`, both sides are one.  If `p>=2`, then `g<q`, so both sides are zero.

## 3. Exact cyclic-norm theorem

Apply `(3)` with `u=z/n^(p/q)` and use `(4)`.  Local uniform convergence permits grouping the
finite root-of-unity packet at each `n`, and gives

```text
N_(p/q)(z)
 = product_(n>=1) E_(floor(1/p))((-1)^q z^q/n^p)
 = W_p((-1)^(q+1) z^q).                                  (5)
```

No asymptotic equivalence, regularization, or exponential-polynomial counterterm occurs:
`(5)` is an exact identity for the standard minimal primary factors.

## 4. Algebraic-change lemma

Differential algebraicity over `C(z)` is invariant under the nonconstant algebraic change

```text
z |-> c z^q,   c!=0.                                      (6)
```

The forward direction follows by repeated chain rule.  Conversely, suppose `F(cz^q)` is DA.
On a simply connected punctured sector choose an algebraic branch

```text
phi(w)=(w/c)^(1/q).
```

Substitution `z=phi(w)` in an ADE for `F(cz^q)` and the triangular chain-rule conversion from
`z`-jets to `w`-jets show that `F(w)` is DA over the finite algebraic extension
`C(w,phi)`.  Differential algebraicity is unchanged by a finite algebraic extension of the
coefficient field, so `F` is DA over `C(w)`.  Hence

```text
F is DA  iff  F(cz^q) is DA.                              (7)
```

The same statement can be expressed by taking the field norm of the substituted differential
polynomial from `C(w,phi)` down to `C(w)`.

## 5. Hypertranscendence consequence

Bank's theorem, with the harmless sign change `z |-> -z`, gives

```text
W_p is DA over C(z)   iff p is even,
W_p is HT over C(z)   iff p is odd.                        (8)
```

For `p=1`, the odd branch is Holder's theorem; Bank's theorem includes it by reference to that
case.  For odd `p>1`, Bank proves the stronger conclusion over the Nevanlinna field
`Lambda_p`.

Equations `(5)`, `(7)`, and `(8)` imply the exact norm classification

```text
N_(p/q) is DA  iff p is even,
N_(p/q) is HT  iff p is odd.                              (9)
```

If `p` is odd and `W_(p/q)` were DA, every rotation
`W_(p/q)(omega^j z)` would be DA and their finite product `N_(p/q)` would be DA, contradicting
`(9)`.  Therefore

```text
p odd  ->  W_(p/q) is HT over C(z).                       (10)
```

The reduced positive rationals with odd numerator are dense in `R_(>0)`: use odd numerators
over powers-of-two denominators.  Thus `(10)` supplies a dense rational HT stratum, not merely
isolated integer examples.

## 6. Hostile audit and exact boundary

1. **Even numerator does not classify the factor.**  If `p` is even, `(9)` says only that the
   complete cyclic norm is DA.  For `q=1`, Bank gives that `W_p` is DA.  For `q>1`, no implication
   from a DA product to its individual factors is valid; the DA/HT status of `W_(p/q)` remains
   open here.
2. **Reduced form is load-bearing.**  Numerator parity before cancelling `p/q` is meaningless.
   The monodromy orbit has size the reduced denominator `q`.
3. **No factorization converse is smuggled in.**  The odd branch uses only the valid direction
   “all factors DA implies their product DA.”
4. **Algebraic pullback does not hide HT.**  Lemma `(7)` rules out the possible loophole that an
   HT integer product becomes DA after `z |-> z^q`.
5. **The primary genus is exact at reciprocal integers.**  When `p=1`, `g(1/q)=q`, and the
   root-of-unity filter leaves genus one, exactly matching `W_1`.
6. **The factor identity is elementary parent mathematics.**  Novelty is not claimed for
   root-of-unity filtering of primary factors.  The candidate new content is the resulting
   rational-exponent DA/HT norm classification and the individual odd-numerator consequence.
7. **Real rational exponents do not reach RH zeros.**  For a nonreal exponent, `n^s` lies on a
   logarithmic spiral and the rotation/monodromy orbit is infinite.  No finite norm like `(2)`
   closes it.  Proving HT for that infinite-orbit family is the next mathematical open core;
   connecting it to a source-forced reflection equality is a separate RH open core.

## 7. Completion insight

The theorem exhibits a direction of completion change not covered by the corpus's
stagewise-DA/limit-HT inverse-limit law:

```text
one rational-power factor
  --complete its finite monodromy orbit of size q-->
integer-power canonical product indexed by p
  --central ray pairing-->
DA exactly when p is even.                                 (11)
```

Thus “HT versus DA” is not the stable datum.  The stable finite datum is the monodromy orbit
together with its oriented ray charge.  Denominator records orbit closure; numerator parity
records whether the closed orbit admits complete opposite-ray pairing.

This also sharpens the completion warning from the multiple-elliptic-Gamma paper: a
regularized determinant can change differential phase not only through local counterterms, but
through finite monodromy completion of its entire divisor.

## 8. Literature audit

- S. B. Bank, *On Certain Canonical Products which Cannot Satisfy Algebraic Differential
  Equations*, Funkcial. Ekvac. 23 (1980), 335--349, proves `(8)` for integer `p` by pulling back
  to a finite Gamma-ray product.  It does not state `(5)`, `(9)`, or the noninteger conclusion
  `(10)`.
- C. Miller and P. Speissegger, *Expansions of the Real Field by Canonical Products*, Canad.
  Math. Bull. 63 (2020), 506--521, define the full real family `W_s`, obtain Barnes-type
  asymptotics and model-theoretic definability results, and cite Bank for odd integer members.
  Their paper does not state a rational-exponent DA/HT classification or cyclic-norm law.
- E. W. Barnes' 1905 asymptotic theory and A. A. Yukhimenko's 2010 asymptotics for products with
  zeros `-n^alpha l(n)` are analytic parent theory, not ADE classifications.
- Exact searches for rational powers, odd numerators, root-of-unity norms, and canonical-product
  hypertranscendence found no equivalent theorem.  This is an absence-of-hit result, not a
  priority certificate.

## Lean status

Everything in the paper except Bank's integer theorem `(8)` is now formalized unconditionally and
axiom-clean (`[propext, Classical.choice, Quot.sound]`).

```text
formal/GaloisForLFunctions/HTGeometry/RootOfUnityPacketFilter.lean
formal/GaloisForLFunctions/HTGeometry/RationalPowerCyclicNorm.lean
formal/GaloisForLFunctions/HTGeometry/PowerSubstitutionJet.lean
formal/GaloisForLFunctions/HTGeometry/PowerSubstitutionDifferentialDescent.lean
formal/GaloisForLFunctions/HTGeometry/RationalPowerHypertranscendenceTransfer.lean
formal/GaloisForLFunctions/HTGeometry/EvenPowerCanonicalProductDA.lean
formal/GaloisForLFunctions/HTGeometry/GammaWeierstrassCanonicalProduct.lean
formal/GaloisForLFunctions/HTGeometry/OnePowerCanonicalProductHypertranscendence.lean
formal/GaloisForLFunctions/HTGeometry/PowerSubstitutionForwardJet.lean
formal/GaloisForLFunctions/HTGeometry/PowerSubstitutionForwardDA.lean
formal/GaloisForLFunctions/HTGeometry/RationalPowerNormDichotomy.lean
formal/GaloisForLFunctions/HTGeometry/OddPowerCanonicalProductGammaRay.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicGammaComplexScale.lean
```

Principal declarations:

```text
prod_one_add_primitiveRoot_pow_mul        -- linear half of (3)
sum_primitiveRoot_pow_mul                 -- orthogonality used by (3)
sum_primaryExponent_primitiveRoot         -- exponential half of (3)
prod_primaryFactor_primitiveRoot          -- the packet identity (3)
powerGenus_natCast, powerGenus_ratio,
nat_div_div_self                          -- the genus bookkeeping (4)
powerCanonicalProduct                     -- W_a, on the corpus canonical-product layer
prod_powerCanonicalProduct_primitiveRoot  -- the exact cyclic norm (5)
differentiallyAlgebraic_of_comp_pow       -- the hard half of (7), for z |-> z^q
differentiallyAlgebraic_of_comp_const_mul_pow  -- (7), descent, for z |-> c z^q
differentiallyAlgebraic_comp_pow          -- the forward half of (7)
differentiallyAlgebraic_comp_const_mul_pow_iff -- (7) in full, as an iff
differentiallyAlgebraic_cyclicNorm_of_even     -- the even branch of (9)
hypertranscendental_cyclicNorm_of_hypertranscendental -- the other branch of (9)
hypertranscendental_powerCanonicalProduct_ratio -- (10) modulo (8)
sum_inv_sub_primitiveRoot_mul             -- root-of-unity partial fractions
inv_pow_sub_pow_eq_weighted_sum           -- residue decomposition of 1/(m^p - n^p)
gammaScaleShiftMero, gammaRayProductMero  -- Gamma at arbitrary complex scale
hypertranscendental_powerCanonicalProduct_odd_iff_mero -- the open core, in the mero field
sincProduct, pi_mul_sincProduct, sincProduct_ade,
differentiallyAlgebraic_sincProduct       -- the Euler sine product and its ADE
powerCanonicalProduct_even_eq_prod_sinc   -- W_(2m)(-w^(2m)) = prod_(k<m) sinc(alpha^k w)
differentiallyAlgebraic_powerCanonicalProduct_of_even -- the even half of (8)
```

The even half of Bank's theorem `(8)` is now proved outright, and without any Gamma theory: for
`p=2m` the substitution `z = -w^(2m)` splits the `n`-th factor by the `2m`-th roots of unity into
`m` Euler sine factors, so

```text
W_(2m)(-w^(2m)) = product_(k<m) sinc(alpha^k w),
sinc(c) = product_(n>=1)(1-c^2/n^2) = sin(pi c)/(pi c),
```

with `alpha` a primitive `2m`-th root of unity.  Each `sinc` satisfies the exact algebraic
differential equation `(pi c y)^2 + (y + c y')^2 = 1` obtained from `sin^2 + cos^2 = 1`, so the
right side is DA; the monomial descent `(7)` then makes `W_(2m)` itself DA.

`(5)` is the exact cyclic-norm identity, with no hypothesis beyond `p,q>=1` and `omega` a primitive
`q`-th root of unity: the finite root-of-unity packet is grouped inside the locally uniformly
convergent canonical product through `HasProd`, so no regularization enters.

`(7)` is now proved in **both** directions and is stated as an iff
(`differentiallyAlgebraic_comp_const_mul_pow_iff`).  The forward half inverts the chain rule
division-free: differentiating `s(z)^(2j) f^(j)(z^q) = sum_i n_(j,i)(z) g^(i)(z)` and using
`s f^(j+1)(z^q) = (f^(j)(.^q))'` gives `n_(j+1,i) = (n_(j,i)' + n_(j,i-1)) s - 2j n_(j,i) s'`, and
homogenising the differential polynomial in the jet variables by the common denominator `s^(2n)`
clears every division.  The descent half is proved by elimination rather than by branch selection.  The chain rule for `z |-> z^q`
gives a triangular polynomial-coefficient substitution on jet variables whose matrix has diagonal
`(q z^(q-1))^j`, hence is invertible at every `z != 0`; solving that system shows the substitution
is injective on differential polynomials.  Reducing the substituted relation modulo the monic
`X^q - t`, with the target point adjoined as a new variable `t`, leaves a remainder of degree `<q`
which still annihilates the jets along `t = z^q`; replacing `z` by `omega^i z` fixes `z^q` and lets
the additive root-of-unity filter isolate one coefficient.  This is stronger than the paper's
sectorial-branch argument and needs no simple connectedness.

`(10)` is formalized as the unconditional implication

```text
Hypertranscendental W_p  ->  Hypertranscendental W_(p/q)      for all p,q >= 1.
```

The remaining Lean gap is exactly the **odd** half of Bank's integer theorem `(8)`.  For odd `p`
the `p`-th roots of unity admit no `+/-` pairing, no elementary closed form appears, and the
substitution `z = -w^p` instead produces the Gamma-ray product

```text
W_p(-w^p) = product_(gamma^p=1) 1/Gamma(1-gamma w),
```

equivalently the digamma relation

```text
(d/dw) log W_p(-w^p)
  = -(1/(p w^(p-1))) sum_(gamma^p=1) gamma psi(1-gamma w).
```

Hypertranscendence of that finite *multi-scale* digamma combination is the one open Lean input.
The corpus owns Hoelder (`hypertranscendental_gamma`) and a complete common-scale/natural-scale
Gamma-orbit superselection layer (`MeromorphicGammaOrbit`, `MeromorphicGammaSuperselection`,
`MeromorphicGammaNatScale`); what is missing is the arbitrary-complex-scale form of that layer.

Statement `(9)` is therefore settled relative to `(8)`: the `q`-fold norm is differentially
algebraic for every even numerator, and hypertranscendental for every numerator whose integer
product `W_p` is hypertranscendental.

### Reduction of the odd branch, and the Lean route

The odd branch reduces exactly.  For odd `p` the identity `sum_(gamma^p=1) gamma = 0` gives

```text
product_(gamma^p=1) W_1(gamma w) = product_(n>=1)(1 + w^p/n^p) = W_p(w^p),
```

which is the `p = q` case of the cyclic-norm law `(5)` already formalized
(`prod_powerCanonicalProduct_primitiveRoot` with `p := p`, `q := p`, using `W_(p/p) = W_1`).  Since
`W_1(z) = exp(-gamma_E z)/Gamma(1+z)`, this says

```text
W_p(w^p) = product_(gamma^p=1) Gamma(1+gamma w)^(-1).
```

So `W_p` HT for odd `p >= 3` is *equivalent* to hypertranscendence of a finite reciprocal-Gamma
product at the `p`-th roots of unity — a **multi-scale** Gamma product.  Both the identity and the
equivalence are now formalized (`powerCanonicalProduct_odd_pow_eq`,
`hypertranscendental_powerCanonicalProduct_odd_iff`), so the open core is a single Lean statement:

```text
Hypertranscendental (fun z => prod_(j<p) (Gamma (omega^j * z + 1))^(-1))    for odd p >= 3.
```

The same core is also now stated inside the corpus's global meromorphic differential field.
`MeromorphicGammaComplexScale` adds `Gamma(a z + b)` at an **arbitrary nonzero complex scale** —
obtained by transporting `gammaShiftMero` along the existing scaling automorphism
`complexScaleMeroEquiv` — together with the ray product `gammaRayProductMero` and the analytic
bridge, giving

```text
hypertranscendental_powerCanonicalProduct_odd_iff_mero :
  Hypertranscendental (powerCanonicalProduct p)
    <-> HypertranscendentalOver (RatFunc C) (gammaRayProductMero p omega _)
```

so the gate can be attacked with the corpus's own superselection machinery.  Before this file the
corpus had `Gamma(z+b)` (`MeromorphicGammaOrbit`) and `Gamma(n z + a)` for natural `n`
(`MeromorphicGammaNatScale`) only; arbitrary complex scale was missing.  The corpus owns the
common-scale and natural-scale superselection layers but not the arbitrary-complex-scale one; that
layer is the single mathematical input still missing.

Milestones, in dependency order:

```text
O1  W_1(z) = exp(-gamma_E z) * Gamma(z+1)^(-1)        [DONE: powerCanonicalProduct_one_eq]
O2  W_1 hypertranscendental              [DONE: hypertranscendental_powerCanonicalProduct_one]
O3  W_(1/q) HT for every q >= 1     [DONE: hypertranscendental_powerCanonicalProduct_inv_nat]
O4  multi-scale root-of-unity reciprocal-Gamma product is HT   (OPEN; statement now in Lean as
    the right-hand side of hypertranscendental_powerCanonicalProduct_odd_iff, and in the
    meromorphic field as hypertranscendental_powerCanonicalProduct_odd_iff_mero)
O5  W_p hypertranscendental for every odd p             (O4 + the p=q cyclic norm)
```

### Attack plan for `O4`

Three equivalent forms of the open core (all three equivalences are formalized, via the monomial
invariance of `(7)`):

```text
(a)  W_p is hypertranscendental,                                p odd, p >= 3;
(b)  prod_(j<p) Gamma(omega^j z + 1)^(-1) is hypertranscendental;
(c)  T_p(u) = sum_(n>=1) 1/(n^p + u) is hypertranscendental.
```

Form `(c)` is the sharpest formulation: `T_p` is meromorphic with simple poles exactly at `-n^p`,
all residues `1`.  For even `p` it is elementary in `u^(1/p)` (the `p`-th roots of unity pair off
into sines) and hence DA; parity, not pole spacing, is what decides the dichotomy, so any proof must
see the pairing.

The corpus's several-automorphism Ostrowski layer is the natural engine:

```text
ElementaryOstrowski.differentialIndependent_of_no_constant_simultaneous_jet_telescoping
AutomorphismFamilyOstrowski.automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
SourceLogarithmicBoundary.automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping
```

It reduces hypertranscendence to non-solvability of a coboundary equation, but it requires
*base-field* increments for **every** (automorphism, primitive) pair.  With the single translation
`sigma : z |-> z+1` only the `j = 0` factor has a rational increment, `sigma(psi(z+1)) - psi(z+1) =
1/(z+1)`; for `j != 0` the increment `psi(omega^j z + omega^j + 1) - psi(omega^j z + 1)` is not
rational.  The workable shape is therefore:

```text
base field   K = the sigma-stable differential subfield generated by C(z) and
                 { psi^(r)(omega^j z + m omega^j + 1) : 1 <= j <= p-1, m in Z, r >= 0 },
primitive    u_0 = psi(z+1),   increment  1/(z+1) in C(z) subset K,
conclusion   u_0 differentially independent over K, hence Phi = sum_j omega^j u_j is HT over C(z),
             because Phi - u_0 lies in K.
```

The one genuine obligation is the non-telescoping hypothesis: no nonzero constant-coefficient
combination of the jets of `1/(z+1)` is `sigma(k) - k` for `k in K`.

**Negative finding (2026-08-03).**  The Ostrowski route above cannot be completed in the corpus's
framework as it stands, and neither can the superselection route.  Both engines require *base-field*
increments for **every** (automorphism, primitive) pair, and for a multi-scale Gamma family the
increment `psi(lambda z + a + lambda h) - psi(lambda z + a)` is rational only when `lambda h` is an
integer.  With scales `omega^j` and translations `omega^(-k)` this happens exactly on the diagonal
`j = k`, because `omega^(j-k)` is real only for `j = k` when `p` is odd.  No enlargement of the
automorphism family repairs this: the shift group `Z[omega]` never makes two different scales
integral simultaneously.  So the multi-scale statement is *not* a missing instantiation of existing
machinery — it needs a different mechanism.

**Correction (2026-08-03): the Laurent constant does *not* see the parity.**  An earlier note on
this card claimed a surviving `log N` in the Laurent constant for odd `p`.  That is wrong; the
logarithms cancel for every `p`.  The exact computation, from the residue decomposition
`inv_pow_sub_pow_eq_weighted_sum`, is

```text
h_N := sum_(m>=1, m != N) 1/(m^p - N^p)
     = (1/(p N^(p-1))) [ -H_(N-1) + gamma
                         - sum_(j != 0) omega^(-j) psi(1 - omega^(-j) N)
                         - (1/N) sum_(j != 0) omega^(-j)/(1 - omega^(-j)) ].
```

The `j = 0` branch supplies `-H_(N-1) ~ -log N`; the branches `j != 0` supply
`-sum_(j != 0) omega^(-j) log N = +log N` because `sum_(j != 0) omega^(-j) = -1`.  The two cancel,
leaving

```text
h_N = ( -C_1 + p/(2N) - C_2/N + O(1/N^2) ) / (p N^(p-1)),
C_1 = sum_(j != 0) omega^(-j) log(-omega^(-j)),  C_2 = sum_(j != 0) omega^(-j)/(1 - omega^(-j)).
```

Two independent checks: for `p = 2` the formula gives `h_N = 3/(4 N^2)` exactly, matching a direct
telescoping evaluation; for `p = 4` it gives `h_N * 4 N^3 = (2 - C_2)/N - pi coth(pi N)`, whose
asymptotic constant is `-C_1 = -pi != 0`.  Since `W_4` is differentially algebraic, a nonzero
asymptotic constant is *not* an obstruction, and neither is irrationality of the constant.  So no
purely local pole-data invariant decides the dichotomy: `W_2` and `W_4` are DA with the same kind of
Laurent data as `W_3`.

**Where the parity actually sits.**  It is a property of the *multiset of scales*, not of any single
pole: `prod_(j<p) Gamma(omega^j z + 1)^(-1)` collapses to elementary sine factors exactly when the
scales are closed under negation with matching charges, i.e. exactly when `p` is even, via
`Gamma(1+x) Gamma(1-x) = pi x / sin(pi x)`.  The theorem to prove is therefore a genuine
**multi-scale Gamma superselection**: a finite product `prod_i Gamma(lambda_i z + mu_i)^(m_i)` times
a DA gauge is DA iff the reflection pairing cancels every charge.  The corpus proves this for a
common scale and for natural scales; the root-of-unity scale case is the open gate.

Revised milestones:

```text
O4a  the reflection norm law  W_p(u) W_p(-u) = W_(2p)(-u^2)                 [DONE]
O4b  root-of-unity partial fractions and the residue decomposition          [DONE]
O4c  the reflection collapse at the level of scales, Gamma(1+x)Gamma(1-x)
O4d  multi-scale Gamma superselection at root-of-unity scales               (the open gate)
```

`O3` is proved, so the card's headline consequence `(10)` now holds unconditionally in Lean for the
whole numerator-one subfamily: `W_(1/q)` is hypertranscendental for every `q >= 1`, a set of
exponents dense in `(0,1]`.  `O2` is proved by removing the Euler-Mascheroni gauge from `W_1`,
identifying the result with the entire reciprocal Gamma germ `Gamma(z+1)^(-1)`, and contradicting the
corpus's single-orbit charge theorem `hypertranscendentalOver_gammaOrbitProductMero` in the global
meromorphic differential field.  Only `O4`/`O5` (odd numerators `p >= 3`) remain.

## Gates

- [x] internal corpus audit: no rational-exponent cyclic-norm classification found
- [x] exact conjecture and falsifiers stated
- [x] primary-factor identity proved for every positive rational exponent
- [x] algebraic-change loophole closed
- [x] odd-numerator HT consequence proved
- [x] even-numerator overclaim rejected
- [x] preliminary primary-source novelty audit completed
- [ ] independent full-text priority audit
- [ ] even-numerator noninteger factor classified or counterexample found
- [ ] infinite-monodromy/nonreal exponent theorem proved
- [x] Lean: primary-factor filter, genus bookkeeping, exact cyclic norm `(5)`
- [x] Lean: algebraic-change lemma `(7)` for `z |-> c z^q`, unconditional
- [x] Lean: the odd-numerator transfer `(10)` as an unconditional implication from `(8)`
- [x] Lean: the even half of Bank's theorem `(8)`, `p` even implies `W_p` DA
- [x] Lean: `W_1 = exp(-gamma_E z)/Gamma(z+1)` and `W_1` hypertranscendental (Bank at `p = 1`)
- [x] Lean: `W_(1/q)` hypertranscendental for every `q >= 1` (a dense rational stratum)
- [ ] Lean: the odd half of Bank's theorem `(8)` for `p >= 3` (multi-scale reciprocal-Gamma HT)
- [x] Lean: the forward half of `(7)`, and hence both branches of `(9)` relative to `(8)`

## Log

- 2026-07-27 — Bank's integer parity law was found, killing the proposed integer-temperature
  novelty claim.
- 2026-07-27 — Replaced it by the exact rational cyclic norm `(5)` and proved the
  odd-numerator individual HT theorem `(10)`.
- 2026-07-27 — Hostile audit isolated even-numerator factors and nonreal infinite monodromy as
  the two genuine open cores.
