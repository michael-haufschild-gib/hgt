# Finite rank-one Hankel Gröbner basis and toric kernel

- **ID:** `deninger-hankel-rank-one-groebner`
- **Stage:** 3-formalized
- **Type:** THEOREM / literature theorem plus coefficient-ring strengthening
- **Route:** L — rational-Witt source foundation
- **Scientific status:** `[LITERATURE-ALIGNED] [NEW FORMAL CONSEQUENCE] [FULLY FORMALIZED] [NOT AN RH PROOF]`
- **Sources:** Nam, *The determinantal ideals of extended Hankel matrices* (2010),
  Lemma 3.6 and Corollary 3.9; Conca, *Straightening law and powers of determinantal
  ideals of Hankel matrices* (1998).

## Statement

For every natural number `N` and every commutative ring `R`, let `B_N(R)` be the finite
family of generic `2 × 2` Hankel minors in `R[X_0,...,X_(N-1)]`, with consecutive rows and
strictly increasing admissible columns. Define

```text
φ_N : R[X_0,...,X_(N-1)] → R[U,T],   X_i ↦ U T^i.
```

Then, without reducedness, domain, characteristic, or non-nilpotence assumptions:

1. `B_N(R)` is monic and is a Gröbner basis for degree-lex order;
2. `span(B_N(R)) = ker(φ_N)`;
3. division by `B_N(R)` has unique zero-detection on reduced remainders.

If `R` is a domain, this kernel is prime. In particular, the statement is closed over `ℤ`.

The arbitrary-ring Gröbner and exact-kernel statements strengthen the field formulation needed
from the literature and remain valid after base change to rings with nilpotents.

## Proof mechanism

The exponent map of `φ_N` records exactly total degree and Hankel weight. An exponent avoiding
all diagonal leading monomials can be supported on at most two consecutive indices. Its minimum
support index is `weight / degree`; total degree and weight then recover both multiplicities.
Thus the exponent map is injective on reduced exponents, and `φ_N` is coefficientwise injective
on every reduced polynomial over an arbitrary commutative ring.

Each `2 × 2` Hankel minor maps to zero symbolically. Monic degree-lex division writes a kernel
element as a generator combination plus reduced remainder. The combination maps to zero, so the
remainder maps to zero; reduced injectivity forces it to vanish. This proves exact kernel equality.

For the Gröbner statement, apply the same division to a nonzero ideal element. Its remainder is
zero. At the polynomial's leading exponent, the finite combination has nonzero coefficient, so
some generator multiple has nonzero coefficient there. Division bounds give equality of its
degree with the input degree. Regularity of the generator's unit leading coefficient makes product
degree additive, hence the generator degree divides the input leading degree componentwise.

Primeness over domains follows from the exact kernel description and the domain target `R[U,T]`.

## Lean realization

- `RHTower/DeningerHankelRankOneGroebner.lean`
  - `hankelRankOneParameterization_finiteHankelMinor_zero`;
  - `hankelRankOneReduced_support_close`;
  - `hankelRankOneReduced_min_weight_div_degree`;
  - `hankelRankOneExponentHom_injective_on_reduced`;
  - `eq_zero_of_hankelRankOneParameterization_eq_zero_of_reduced`;
  - `finiteHankelRankOneIdeal_eq_parameterization_ker`;
  - `finiteHankelRankOne_degLex_isGroebnerBasis`;
  - `finiteHankelRankOneIdeal_isPrime`;
  - `finiteHankelRankOneIdeal_int_isPrime`.

Direct foreground check and exact module build pass. Axiom audit of the reduced-injectivity,
kernel, Gröbner, and integral-prime capstones reports only `propext`, `Classical.choice`, and
`Quot.sound`. Module is wired into `RHTower.lean`.

## Frontier impact

Nam's rank-one Gröbner/prime base case is no longer an external premise. The remaining hard
literature gap is higher rank: formalize the c-chain leading ideal and the maximal-Hankel-minor
Gröbner theorem for arbitrary row size, then transfer homogeneous primeness integrally and bridge
it honestly to Hazewinkel's normalized specialization `a_0 = 1`.

## Gates

- [x] 0 → 1: exact rank-one literature theorem isolated
- [x] 1 → 2: arbitrary-ring normal form, kernel, Gröbner, and prime proof closed
- [x] 2 → 3: unconditional Lean proofs, foreground check, umbrella wiring
- [ ] 3 → 4: publication/novelty audit of arbitrary-ring strengthening not pursued
