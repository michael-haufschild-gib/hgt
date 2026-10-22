# Stark simple-zero order classification

- **ID:** `artin-stark-simple-zero-order-classification`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LEAN-PROVED] [BRIDGE]`
- **Source:** Stark simple-zero mechanism; Foote--Murty order norm

## Exact statement

Let `I` be a finite type.  Let `d : I -> Nat` and `n : I -> Int` satisfy

```text
(D1) 0 < d(i)                                      for every i,
(D2) sum_i d(i) n(i) = 1,
(D3) sum_i n(i)^2 <= 1.
```

Then there is a unique `i0 : I` such that

```text
d(i0) = 1,    n(i0) = 1,
n(i) = 0      for every i != i0.
```

In particular, every `n(i)` is non-negative.

## Literature alignment `[LITERATURE]`

For a finite Galois extension `K/F`, a point `s0 != 1`, and irreducible characters `chi` of
`G = Gal(K/F)`, put

```text
n(chi) = ord_(s=s0) L(s,chi),    d(chi) = chi(1).
```

The Artin--Takagi factorization gives

```text
ord_(s=s0) zeta_K(s) = sum_chi d(chi)n(chi).
```

Foote--Murty prove

```text
sum_chi n(chi)^2 <= ord_(s=s0) zeta_K(s)^2.
```

Consequently a simple zero of `zeta_K` gives (D2)--(D3), and the classification above says that
exactly one degree-one Artin component has a simple zero and every other component has order zero.
This is Stark's simple-zero holomorphy mechanism in its complete integer-order form.

Primary sources:

- R. Foote and V. K. Murty, *Zeros and poles of Artin L-series*, Math. Proc. Cambridge Philos.
  Soc. 105 (1989), 5--11, https://doi.org/10.1017/S0305004100001316.
- G. Harcos and K. Soundararajan, *A supplement to Chebotarev's density theorem*, Sci. China Math.
  66 (2023), https://doi.org/10.1007/s11425-022-2141-1, especially Remark 3.2 for the
  Foote--Murty bound and its restriction-to-cyclic-subgroups mechanism.

## Paper proof

Every square `n(i)^2` is a non-negative integer.  By (D3), each square is at most `1`.

Assume some `n(i0)` is negative.  Then `n(i0) <= -1`, hence `n(i0)^2 >= 1`.  Since the sum of all
non-negative squares is at most `1`, equality holds at `i0` and every other square is zero.  Thus
`n(i0) = -1` and `n(i) = 0` for `i != i0`.  Equation (D2) becomes `-d(i0)=1`, contradicting
`d(i0)>0`.  Therefore every `n(i)` is non-negative.

Equation (D2) now expresses `1` as a finite sum of non-negative integers `d(i)n(i)`.  Hence some
term is positive.  Fix `i0` with `d(i0)n(i0)>0`.  Since both factors are positive integers and the
whole sum is `1`, that term equals `1`; therefore `d(i0)=1` and `n(i0)=1`.  Every other term is
zero, and positivity of every `d(i)` forces `n(i)=0` for `i != i0`.  This also proves uniqueness.

No analytic hypothesis is hidden in the classification: (D1)--(D3) are the exact integer
consequences imported from character degree, Artin--Takagi factorization, and Foote--Murty.

## Significance boundary

This theorem certifies the complete simple-zero frontier.  It does not prove (D2) or (D3) for
Artin L-functions inside Lean, does not address multiple zeros, and does not prove Artin holomorphy.
Any claim beyond simple Dedekind-zeta zeros still needs group/arithmetic information not present in
the three integer constraints.

## Lean certificate `[LEAN-PROVED]`

- Module: `GaloisForLFunctions.RHTower.Artin.ArtinStarkSimpleZero`
- Theorem: `GaloisForLFunctions.artin_stark_simpleZero_order_classifier`
- Exact scope: arbitrary finite `I`, `degree : I -> Nat`, `order : I -> Int`; statement matches the
  paper classifier above.
- Leaf check: `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinStarkSimpleZero.lean` passed.
- Targeted olean: `lake build GaloisForLFunctions.RHTower.Artin.ArtinStarkSimpleZero` passed.
- Axiom audit: only Lean standard axioms `propext`, `Classical.choice`, `Quot.sound`.
- Escape scan: no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.
- Umbrella: imported by `GaloisForLFunctions.RHTower`; umbrella build intentionally not run.

This certifies only integer-order classification. Full Artin/Heilbronn analytic infrastructure remains
mandatory before treating literature frontier as formalized.
