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
differentiallyAlgebraic_of_comp_const_mul_pow  -- (7) for z |-> c z^q
hypertranscendental_powerCanonicalProduct_ratio -- (10) modulo (8)
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

`(7)` is proved by elimination rather than by branch selection.  The chain rule for `z |-> z^q`
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

Also still open on the Lean side: the *forward* half of `(7)` (`f` DA implies `f(c z^q)` DA), which
`(9)` needs in the even branch.  The hard converse half is proved.

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
product at the `p`-th roots of unity — a **multi-scale** Gamma product.  The corpus owns the
common-scale and natural-scale superselection layers but not the arbitrary-complex-scale one; that
layer is the single mathematical input still missing.

Milestones, in dependency order:

```text
O1  W_1(z) = exp(-gamma_E z) * Gamma(z+1)^(-1)        [DONE: powerCanonicalProduct_one_eq]
O2  W_1 hypertranscendental                            (O1 + Hoelder, in the meromorphic field)
O3  W_(1/q) hypertranscendental for every q >= 1        (O2 + the proved transfer (10))
O4  multi-scale root-of-unity reciprocal-Gamma product is HT   (open layer)
O5  W_p hypertranscendental for every odd p             (O4 + the p=q cyclic norm)
```

`O3` already gives a dense rational stratum of hypertranscendental exponents `1/q`, which is the
card's headline consequence for the numerator-one subfamily.

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
- [ ] Lean: Bank's integer-exponent theorem `(8)` (the only remaining gap)

## Log

- 2026-07-27 — Bank's integer parity law was found, killing the proposed integer-temperature
  novelty claim.
- 2026-07-27 — Replaced it by the exact rational cyclic norm `(5)` and proved the
  odd-numerator individual HT theorem `(10)`.
- 2026-07-27 — Hostile audit isolated even-numerator factors and nonreal infinite monodromy as
  the two genuine open cores.
